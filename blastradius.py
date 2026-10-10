#!/usr/bin/env python3
"""BlastRadius-AST — static change-impact analyzer for Python (standard library only).

Usage:
  python blastradius.py analyze <project_dir> <file.py:function> [--depth 3] [--json]
  python blastradius.py graph   <project_dir> <file.py:function>
  python blastradius.py symbols <project_dir>
  python blastradius.py demo     # builds a sample project in memory, analyzes and verifies it

Target formats: auth/tokens.py:verify_jwt · auth/tokens.py:Class.method · auth.tokens:verify_jwt
Set the NO_COLOR environment variable to disable colors.
"""
from __future__ import annotations

import argparse
import ast
import difflib
import json
import math
import os
import sys
import textwrap
from collections import defaultdict, deque
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath

DEF_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef)
SKIP_DIRS = {"__pycache__", "venv", "env", "node_modules", "site-packages", "build", "dist"}


def parent(qn: str) -> str:
    return qn.rpartition(".")[0]


# ═══════════════ STAGE 1: Multi-file AST parser and symbol table ═══════════════

@dataclass
class Symbol:
    qualname: str                 # package.module.Class.method
    kind: str                     # module | class | function | method
    module: str
    file: str
    lineno: int
    params: list[str] = field(default_factory=list)
    returns: str | None = None
    bases: list[str] = field(default_factory=list)  # class only: resolved in-project base classes


def module_name(path: str) -> tuple[str, bool]:
    """'pkg/mod.py' -> ('pkg.mod', False); 'pkg/__init__.py' -> ('pkg', True)."""
    parts = list(PurePosixPath(path.replace("\\", "/")).with_suffix("").parts)
    if len(parts) > 1 and parts[0] == "src":  # src/ layout: imports are written without 'src.'
        parts = parts[1:]
    is_pkg = parts[-1] == "__init__"
    if is_pkg and len(parts) > 1:
        parts.pop()
    return ".".join(parts), is_pkg


def _params(a: ast.arguments) -> list[str]:
    def fmt(arg: ast.arg, default=None, prefix=""):
        s = prefix + arg.arg + (f": {ast.unparse(arg.annotation)}" if arg.annotation else "")
        return s + (f" = {ast.unparse(default)}" if default is not None else "")

    pos = a.posonlyargs + a.args
    defaults = [None] * (len(pos) - len(a.defaults)) + a.defaults
    out = [fmt(x, d) for x, d in zip(pos, defaults)]
    if a.posonlyargs:
        out.insert(len(a.posonlyargs), "/")
    if a.vararg:
        out.append(fmt(a.vararg, prefix="*"))
    elif a.kwonlyargs:
        out.append("*")
    out += [fmt(x, d) for x, d in zip(a.kwonlyargs, a.kw_defaults)]
    if a.kwarg:
        out.append(fmt(a.kwarg, prefix="**"))
    return out


def _scope_nodes(owner: ast.AST):
    """Nodes in the owner's own scope, in source order. Does not enter nested def/class bodies;
    their decorators/defaults/bases belong to the enclosing scope (as in Python)."""
    stack = list(reversed(owner.body))
    while stack:
        n = stack.pop()
        if isinstance(n, DEF_TYPES):
            extra = n.decorator_list + n.args.defaults + [d for d in n.args.kw_defaults if d]
        elif isinstance(n, ast.ClassDef):
            extra = n.decorator_list + n.bases + [k.value for k in n.keywords]
        else:
            yield n
            extra = list(ast.iter_child_nodes(n))
        stack.extend(reversed(extra))


class Project:
    """Symbol table + bidirectional call graph + inheritance hierarchy."""

    def __init__(self, sources: dict[str, str | bytes]):
        self.symbols: dict[str, Symbol] = {}
        self.imports: dict[str, dict[str, str]] = {}          # module -> {local name: qualified name}
        self.star: dict[str, list[str]] = defaultdict(list)    # module -> 'from x import *' sources
        self.files: dict[str, str] = {}                         # module -> file path
        self.errors: list[str] = []
        self.subclasses: dict[str, set[str]] = defaultdict(set)
        self.callees: dict[str, dict[str, int]] = defaultdict(dict)  # caller -> {callee: call sites}
        self.callers: dict[str, dict[str, int]] = defaultdict(dict)  # callee -> {caller: call sites}
        self.guessed: set[tuple[str, str]] = set()              # edges guessed by name
        self.refs: set[tuple[str, str]] = set()                 # used as a value without a call (callback)
        self._nodes: dict[str, ast.AST] = {}
        self._mro_cache: dict[str, list[str]] = {}
        for path, src in sorted(sources.items()):
            mod, is_pkg = module_name(path)
            try:
                tree = ast.parse(src, filename=path)
            except (SyntaxError, ValueError) as e:
                self.errors.append(f"{path}: {e}")
                continue
            self._collect(mod, is_pkg, path, tree)
        self._link_inheritance()
        self._infer_types()
        self._build_call_graph()

    @classmethod
    def from_dir(cls, root: str | Path) -> "Project":
        root = Path(root)
        if not root.is_dir():
            raise ValueError(f"Directory not found: {root}")
        sources = {}
        for p in root.rglob("*.py"):
            rel = p.relative_to(root)
            if any(part in SKIP_DIRS or part.startswith(".") for part in rel.parts[:-1]):
                continue
            sources[rel.as_posix()] = p.read_bytes()  # bytes: ast honors the encoding declaration itself
        return cls(sources)

    def _collect(self, mod: str, is_pkg: bool, path: str, tree: ast.Module):
        self.files[mod] = path
        self.symbols[mod] = Symbol(mod, "module", mod, path, 1)
        self._nodes[mod] = tree
        imports = self.imports.setdefault(mod, {})
        pkg_parts = mod.split(".") if is_pkg else mod.split(".")[:-1]
        stack = [(tree, mod, False)]
        while stack:
            node, scope, in_class = stack.pop()
            for ch in ast.iter_child_nodes(node):
                if isinstance(ch, ast.ClassDef):
                    qn = f"{scope}.{ch.name}"
                    self.symbols[qn] = Symbol(qn, "class", mod, path, ch.lineno)
                    self._nodes[qn] = ch
                    stack.append((ch, qn, True))
                elif isinstance(ch, DEF_TYPES):
                    qn = f"{scope}.{ch.name}"
                    self.symbols[qn] = Symbol(qn, "method" if in_class else "function", mod, path, ch.lineno,
                                              _params(ch.args), ast.unparse(ch.returns) if ch.returns else None)
                    self._nodes[qn] = ch
                    stack.append((ch, qn, False))
                # shortcut: function-local imports go into the module-wide table; name shadowing would need per-scope tables
                elif isinstance(ch, ast.Import):
                    for a in ch.names:
                        imports[a.asname or a.name.split(".")[0]] = a.name if a.asname else a.name.split(".")[0]
                elif isinstance(ch, ast.ImportFrom):
                    base = ch.module or ""
                    if ch.level:
                        keep = len(pkg_parts) - (ch.level - 1)
                        base = ".".join((pkg_parts[:keep] if keep >= 0 else []) + ([ch.module] if ch.module else []))
                    for a in ch.names:
                        if a.name == "*":
                            self.star[mod].append(base)
                        else:
                            imports[a.asname or a.name] = f"{base}.{a.name}" if base else a.name
                else:
                    stack.append((ch, scope, in_class))

    # ─── name resolution ───

    def module_of(self, qn: str) -> str:
        while qn and not (qn in self.symbols and self.symbols[qn].kind == "module"):
            qn = parent(qn)
        return qn

    def label(self, qn: str) -> str:
        """'auth.tokens.verify_jwt' -> 'auth.tokens:verify_jwt'"""
        mod = self.module_of(qn)
        return f"{mod}:{qn[len(mod) + 1:]}" if qn != mod else f"{mod}:<module>"

    def mro(self, cls: str) -> list[str]:
        if cls not in self._mro_cache:
            self._mro_cache[cls] = [cls]  # guard against cyclic inheritance
            bases = self.symbols[cls].bases
            seqs = [list(self.mro(b)) for b in bases] + [list(bases)]
            out = [cls]
            while any(seqs):  # C3 linearization (Python's own MRO)
                seqs = [s for s in seqs if s]
                head = next((s[0] for s in seqs if not any(s[0] in t[1:] for t in seqs)), None)
                if head is None:  # inconsistent hierarchy: Python raises TypeError; append the rest in order
                    head = seqs[0][0]
                out.append(head)
                seqs = [s[1:] if s[0] == head else s for s in seqs]
            self._mro_cache[cls] = list(dict.fromkeys(out))
        return self._mro_cache[cls]

    def member(self, cls: str, name: str, start: int = 0) -> str | None:
        for c in self.mro(cls)[start:]:
            if f"{c}.{name}" in self.symbols:
                return f"{c}.{name}"
        return None

    def _lookup(self, qn: str, _depth: int = 0) -> str | None:
        """Reduces a qualified name to a symbol, following re-exports, the MRO and * imports."""
        if qn in self.symbols:
            return qn
        if _depth > 10:
            return None
        parts = qn.split(".")
        for i in range(len(parts) - 1, 0, -1):
            head = ".".join(parts[:i])
            if head not in self.symbols:
                continue
            name, rest, kind = parts[i], parts[i + 1:], self.symbols[head].kind
            if kind == "class":
                nxt = self.member(head, name)
            elif kind == "module":
                nxt = self.imports[head].get(name) or next(
                    (f"{s}.{name}" for s in self.star[head] if self._lookup(f"{s}.{name}", _depth + 1)), None)
            else:
                nxt = None
            return self._lookup(".".join([nxt, *rest]), _depth + 1) if nxt else None
        return None

    def _resolve_name(self, name: str, owner: str) -> str | None:
        mod = self.module_of(owner)
        scope = owner
        while True:  # local -> enclosing functions -> module (class bodies are not a scope for methods)
            if scope == owner or self.symbols[scope].kind != "class":
                if f"{scope}.{name}" in self.symbols:
                    return f"{scope}.{name}"
            if scope == mod:
                break
            scope = parent(scope)
        if name in self.imports.get(mod, {}):
            return self._lookup(self.imports[mod][name])
        return next((r for s in self.star[mod] if (r := self._lookup(f"{s}.{name}"))), None)

    def _enclosing_class(self, owner: str) -> str | None:
        s = parent(owner)
        while s:
            kind = self.symbols[s].kind if s in self.symbols else None
            if kind == "class":
                return s
            if kind == "module":
                return None
            s = parent(s)
        return None

    def _ann_class(self, ann: ast.AST, owner: str) -> str | None:
        if isinstance(ann, ast.Constant) and isinstance(ann.value, str):  # forward reference
            try:
                ann = ast.parse(ann.value, mode="eval").body
            except SyntaxError:
                return None
        if isinstance(ann, ast.Subscript) and getattr(ann.value, "id", getattr(ann.value, "attr", "")) == "Optional":
            return self._ann_class(ann.slice, owner)
        if isinstance(ann, ast.BinOp) and isinstance(ann.op, ast.BitOr):  # X | None
            return self._ann_class(ann.left, owner) or self._ann_class(ann.right, owner)
        t = self._resolve(ann, owner)
        return t if t and self.symbols[t].kind == "class" else None

    def _type_of(self, e: ast.AST, owner: str, types: dict) -> str | None:
        """Project class of the expression's instance type, if known."""
        if isinstance(e, ast.Name):
            if e.id in types:
                return types[e.id]
            if e.id in ("self", "cls"):
                return self._enclosing_class(owner)
        elif isinstance(e, ast.Attribute) and isinstance(e.value, ast.Name) and e.value.id == "self":
            c = self._enclosing_class(owner)
            return next((self.attr_types[k][e.attr] for k in (self.mro(c) if c else ())
                         if e.attr in self.attr_types[k]), None)
        elif isinstance(e, ast.Call):
            t = self._resolve(e.func, owner, types)
            if t and self.symbols[t].kind == "class":
                return t
            if t and isinstance(self._nodes.get(t), DEF_TYPES) and self._nodes[t].returns is not None:
                return self._ann_class(self._nodes[t].returns, parent(t))
        return None

    def _resolve(self, e: ast.AST, owner: str, types: dict | None = None) -> str | None:
        """Resolves an ast.Name / ast.Attribute chain to a project symbol."""
        types = types or {}
        if isinstance(e, ast.Name):
            return self._resolve_name(e.id, owner)
        if isinstance(e, ast.Attribute):
            v = e.value
            if isinstance(v, ast.Call) and isinstance(v.func, ast.Name) and v.func.id == "super":
                c = self._enclosing_class(owner)
                return self.member(c, e.attr, start=1) if c else None
            t = self._type_of(v, owner, types)
            if t:
                return self.member(t, e.attr)
            base = self._resolve(v, owner, types)
            return self._lookup(f"{base}.{e.attr}") if base else None
        return None

    # ═══════════════ STAGE 2: Bidirectional call graph + inheritance ═══════════════

    def _link_inheritance(self):
        for qn, node in self._nodes.items():
            if isinstance(node, ast.ClassDef):
                bases = [b for b in (self._resolve(e, parent(qn)) for e in node.bases)
                         if b and self.symbols[b].kind == "class" and b != qn]
                self.symbols[qn].bases = bases
                for b in bases:
                    self.subclasses[b].add(qn)
        self._mro_cache.clear()  # may have been computed with incomplete bases while linking

    def _infer_types(self):
        # flow-insensitive: chain resolution uses the last assignment, x.m() links to every possible type
        self._types: dict[str, dict[str, str]] = {}
        self._all_types: dict[str, dict[str, set[str]]] = defaultdict(lambda: defaultdict(set))
        self.attr_types: dict[str, dict[str, str]] = defaultdict(dict)  # class -> {self.attr: class}
        for owner, node in self._nodes.items():
            types = self._types[owner] = {}
            if isinstance(node, DEF_TYPES):
                a = node.args
                for arg in a.posonlyargs + a.args + a.kwonlyargs:
                    if arg.annotation is not None and (t := self._ann_class(arg.annotation, parent(owner))):
                        types[arg.arg] = t
            for n in _scope_nodes(node):
                if isinstance(n, ast.Assign) and len(n.targets) == 1:
                    tgt, t = n.targets[0], self._type_of(n.value, owner, types)
                elif isinstance(n, ast.AnnAssign):
                    tgt = n.target
                    t = self._ann_class(n.annotation, owner) or (n.value and self._type_of(n.value, owner, types))
                else:
                    continue
                if not t:
                    continue
                if isinstance(tgt, ast.Name):
                    types[tgt.id] = t
                    self._all_types[owner][tgt.id].add(t)
                elif (isinstance(tgt, ast.Attribute) and isinstance(tgt.value, ast.Name)
                      and tgt.value.id == "self" and (c := self._enclosing_class(owner))):
                    self.attr_types[c][tgt.attr] = t

    def _build_call_graph(self):
        by_name = defaultdict(list)
        for qn, s in self.symbols.items():
            if s.kind == "method" and not qn.rpartition(".")[2].startswith("__"):
                by_name[qn.rpartition(".")[2]].append(qn)
        def add(a, b):
            self.callees[a][b] = self.callees[a].get(b, 0) + 1
            self.callers[b][a] = self.callers[b].get(a, 0) + 1

        called = set()
        for owner, node in self._nodes.items():
            types = self._types[owner]
            nodes = list(_scope_nodes(node))
            skip = {id(n.func) for n in nodes if isinstance(n, ast.Call)}
            skip |= {id(b) for n in nodes if isinstance(n, ast.ClassDef) for b in n.bases}  # inheritance is tracked separately
            skip |= {id(n.value) for n in nodes if isinstance(n, ast.Attribute)}  # only the full chain
            for n in nodes:
                if isinstance(n, (ast.Name, ast.Attribute)) and isinstance(n.ctx, ast.Load) and id(n) not in skip:
                    ref = self._resolve(n, owner, types)
                    if ref and self.symbols[ref].kind in ("function", "method") and ref != owner:
                        add(owner, ref)  # callback / registry entry: ROUTES = {"/x": handler}
                        self.refs.add((owner, ref))
                if not isinstance(n, ast.Call):
                    continue
                tgt, guessed = self._resolve(n.func, owner, types), False
                if tgt is None and isinstance(n.func, ast.Attribute) and len(by_name[n.func.attr]) == 1:
                    # shortcut: obj.method() with unknown type links by name when exactly one candidate exists (marked ~)
                    tgt, guessed = by_name[n.func.attr][0], True
                if not tgt or self.symbols[tgt].kind == "module":
                    continue
                targets = [tgt]
                if isinstance(n.func, ast.Attribute) and isinstance(n.func.value, ast.Name):
                    for c in sorted(self._all_types[owner].get(n.func.value.id, ())):  # if/else branches
                        if (m := self.member(c, n.func.attr)) and m not in targets:
                            targets.append(m)
                if self.symbols[tgt].kind == "class" and (init := self.member(tgt, "__init__")):
                    targets.append(init)  # Class(...) -> the constructor is called too
                for t in targets:
                    add(owner, t)
                    called.add((owner, t))
                    if guessed:
                        self.guessed.add((owner, t))
        self.refs -= called

    def dependents(self, qn: str) -> dict[str, str]:
        """Direct dependents if qn changes: {node: 'call' | 'inherit' | 'dispatch'}."""
        out = {c: "call" for c in self.callers.get(qn, ())}
        sym, cls, name = self.symbols.get(qn), parent(qn), qn.rpartition(".")[2]
        if sym and sym.kind == "class":
            for s in self.subclasses.get(qn, ()):
                out.setdefault(s, "inherit")
        elif cls in self.symbols and self.symbols[cls].kind == "class" and (sym is None or sym.kind == "method"):
            impl = self.member(cls, name)
            for s in self.subclasses.get(cls, ()):  # a subclass that doesn't override inherits the method
                if self.member(s, name) == impl:
                    out.setdefault(f"{s}.{name}", "inherit")  # virtual node: Sub.method (inherited)
            if sym is not None and (base := self.member(cls, name, start=1)):
                for c in self.callers.get(base, ()):  # a call to Base.method may land here via dynamic dispatch
                    out.setdefault(c, "dispatch")
        out.pop(qn, None)
        return out

    def resolve_target(self, spec: str) -> str:
        left, sep, func = spec.rpartition(":")
        if not sep or not left or not func:
            raise ValueError(f"Target must look like 'file.py:function': {spec!r}")
        norm = PurePosixPath(left.replace("\\", "/")).as_posix()
        if norm.endswith(".py"):
            mod = next((m for m, f in self.files.items() if norm == f or norm.endswith("/" + f)), None)
            if mod is None:
                raise ValueError(f"File not in project: {left}")
        else:
            mod = norm
        qn = f"{mod}.{func}"
        if qn not in self.symbols or self.symbols[qn].kind == "module":
            near = difflib.get_close_matches(qn, self.symbols, n=3)
            raise ValueError(f"Symbol not found: {qn}" + (f" — did you mean: {', '.join(near)}" if near else ""))
        return qn

    # ═══════════════ STAGE 3: Blast radius (BFS) + risk score ═══════════════

    def blast_radius(self, target: str, max_depth: int | None = 3) -> "Impact":
        depth, via, kind = {target: 0}, {}, {}
        queue = deque([target])
        while queue:
            node = queue.popleft()
            if max_depth and depth[node] >= max_depth:
                continue
            for dep, k in sorted(self.dependents(node).items()):
                if dep not in depth:  # BFS: first reach = shortest path; cycles stop here
                    depth[dep], via[dep], kind[dep] = depth[node] + 1, node, k
                    queue.append(dep)
        del depth[target]
        score, level, breakdown = risk_score(self, target, depth)
        return Impact(target, depth, via, kind, score, level, breakdown)


@dataclass
class Impact:
    target: str
    depth: dict[str, int]   # impacted node -> degree (1 = direct)
    via: dict[str, str]     # parent in the BFS tree (which node it was reached through)
    kind: dict[str, str]    # call | inherit | dispatch
    score: int
    level: str
    breakdown: dict


CRITICAL_KEYWORDS = ("auth", "login", "logout", "token", "jwt", "password", "secret", "crypt", "payment",
                     "billing", "charge", "db", "database", "query", "sql", "transaction", "commit", "session",
                     "security", "admin", "permission", "api", "route", "handler", "endpoint", "main", "server")
DEPTH_WEIGHT = {1: 1.0, 2: 0.6, 3: 0.35}  # degree 4 and beyond: 0.2


def is_critical(qn: str) -> bool:
    tokens = qn.lower().replace("_", ".").split(".")
    return any(t.startswith(k) for t in tokens if t for k in CRITICAL_KEYWORDS)


def risk_score(p: Project, target: str, depth: dict[str, int]) -> tuple[int, str, dict]:
    """
    raw   = Σ W(degree) · (2 if critical else 1)      for each impacted node; W = 1.0 / 0.6 / 0.35 / 0.2
          + 0.25 · direct call sites of the target
          + 0.5  · number of distinct impacted modules (excluding the target's)
          + 2    · (target itself is on a critical path)
    score = round(100 · (1 − e^(−raw / 6)))           saturation curve -> 0..100
    """
    nodes = sum(DEPTH_WEIGHT.get(d, 0.2) * (2 if is_critical(n) else 1) for n, d in depth.items())
    sites = sum(p.callers.get(target, {}).values())
    modules = {p.module_of(n) for n in depth} - {p.module_of(target)}
    raw = nodes + 0.25 * sites + 0.5 * len(modules) + (2 if is_critical(target) else 0)
    score = round(100 * (1 - math.exp(-raw / 6)))
    level = "CRITICAL" if score >= 75 else "HIGH" if score >= 50 else "MEDIUM" if score >= 25 else "LOW"
    return score, level, {"node_weight": round(nodes, 2), "call_sites": sites,
                          "impacted_modules": len(modules), "target_critical": is_critical(target), "raw": round(raw, 2)}


# ═══════════════ STAGE 4: Colored ASCII blast tree ═══════════════

ANSI = {"bred": "\033[1;31m", "red": "\033[31m", "yellow": "\033[33m", "green": "\033[32m",
        "cyan": "\033[36m", "dim": "\033[2m", "bold": "\033[1m"}
LEVEL_COLOR = {"CRITICAL": "bred", "HIGH": "red", "MEDIUM": "yellow", "LOW": "green"}
KIND_LABEL = {"inherit": "inherited", "dispatch": "override/dispatch"}


def render(p: Project, imp: Impact, color: bool = False) -> str:
    paint = (lambda s, c: f"{ANSI[c]}{s}\033[0m") if color else (lambda s, c: s)
    children = defaultdict(list)
    for n, par in imp.via.items():
        children[par].append(n)
    kids = lambda n: sorted(children[n], key=p.label)

    def line(n: str) -> str:
        d = imp.depth[n]
        tag = "Direct" if d == 1 else f"Transitive, degree {d}"
        if imp.kind[n] != "call":
            tag += f" · {KIND_LABEL[imp.kind[n]]}"
        elif (n, imp.via[n]) in p.refs:
            tag += " · reference"
        s = f"{paint(p.label(n), 'yellow' if d == 1 else 'cyan')} ({tag})"
        if (n, imp.via[n]) in p.guessed:
            s += paint(" ~guessed", "dim")
        return s + (paint(" ⚠ critical", "red") if is_critical(n) else "")

    out = [paint(f"[{imp.level} RISK - Score: {imp.score}/100]", LEVEL_COLOR[imp.level]),
           f"└─ {paint(p.label(imp.target), 'bold')}"]
    ks = kids(imp.target)
    stack = [(k, "   ", i == len(ks) - 1) for i, k in reversed(list(enumerate(ks)))]
    while stack:  # iterative pre-order walk (no stack overflow on deep chains)
        n, prefix, last = stack.pop()
        out.append(prefix + ("└─ " if last else "├─ ") + line(n))
        ks, sub = kids(n), prefix + ("   " if last else "│  ")
        stack += [(k, sub, i == len(ks) - 1) for i, k in reversed(list(enumerate(ks)))]
    direct = sum(1 for d in imp.depth.values() if d == 1)
    b = imp.breakdown
    out.append(paint(f"\nDirect: {direct} · Transitive: {len(imp.depth) - direct} · "
                     f"Impacted modules: {b['impacted_modules']} · Call sites: {b['call_sites']} · "
                     f"Raw score: {b['raw']}", "dim"))
    return "\n".join(out)


def impact_json(p: Project, imp: Impact) -> str:
    rows = [{"node": n, "label": p.label(n), "depth": d, "via": imp.via[n], "kind": imp.kind[n],
             "critical": is_critical(n), "guessed": (n, imp.via[n]) in p.guessed}
            for n, d in sorted(imp.depth.items(), key=lambda x: (x[1], x[0]))]
    return json.dumps({"target": imp.target, "score": imp.score, "level": imp.level,
                       "breakdown": imp.breakdown, "impacted": rows}, ensure_ascii=False, indent=2)


def describe(p: Project, qn: str) -> str:
    s = p.symbols[qn]
    sig = f"({', '.join(s.params)})" + (f" -> {s.returns}" if s.returns else "") if s.kind in ("function", "method") else ""
    bases = f"  bases={[p.label(b) for b in s.bases]}" if s.bases else ""
    return f"{s.kind:<8} {p.label(qn)}{sig}{bases}   [{s.file}:{s.lineno}]"


# ═══════════════ STAGE 5: In-memory simulation project + verification ═══════════════

DEMO_SOURCES = {k: textwrap.dedent(v) for k, v in {
    "myapp/__init__.py": "",
    "myapp/db/__init__.py": "",
    "myapp/utils/__init__.py": "",
    "myapp/services/__init__.py": "",
    "myapp/api/__init__.py": "",
    # 1) Database layer — the core
    "myapp/db/connection.py": '''
        class Connection:
            def __init__(self, dsn: str) -> None:
                self.dsn = dsn

            def cursor(self):
                return self

        def get_connection(dsn: str = "sqlite://") -> Connection:
            return Connection(dsn)

        def execute_query(sql: str, params: tuple = ()) -> list[dict]:
            conn = get_connection()
            return [{"sql": sql, "params": params, "cursor": conn.cursor()}]
    ''',
    # 2) Utilities — aliased absolute import + function-local relative import
    "myapp/utils/helpers.py": '''
        from myapp.db.connection import execute_query as run_sql

        def fetch_one(sql: str, *params) -> dict | None:
            rows = run_sql(sql, params)
            return rows[0] if rows else None

        def slugify(text: str) -> str:
            return text.lower().replace(" ", "-")

        def audit_log(event: str) -> None:
            from ..db import connection
            connection.execute_query("INSERT INTO audit VALUES (?)", (event,))
    ''',
    # 3) Service layer — inheritance, self calls, super(), instance attribute types
    "myapp/services/user_service.py": '''
        from myapp.utils import helpers
        from myapp.utils.helpers import slugify

        class BaseRepository:
            table = ""

            def find(self, key):
                return helpers.fetch_one(f"SELECT * FROM {self.table} WHERE id=?", key)

        class UserRepository(BaseRepository):
            table = "users"

            def find_by_email(self, email: str):
                return self.find(email)

        class AdminRepository(UserRepository):
            def find(self, key):
                return super().find(key)

        class UserService:
            def __init__(self) -> None:
                self.repo = UserRepository()

            def authenticate(self, email: str, password: str) -> bool:
                user = self.repo.find_by_email(email)
                helpers.audit_log("login")
                return bool(user)

            def display_name(self, name: str) -> str:
                return slugify(name)
    ''',
    # 4) API layer — relative import, call via constructor, annotated local variable
    "myapp/api/routes.py": '''
        from typing import Optional
        from ..services.user_service import UserService, UserRepository

        def login_handler(email: str, password: str) -> dict:
            ok = UserService().authenticate(email, password)
            return {"ok": ok}

        def profile_handler(user_id: int) -> dict:
            repo: UserRepository = UserRepository()
            return repo.find(user_id) or {}

        def name_handler(name: str) -> str:
            return UserService().display_name(name)

        def handle_request(path: str, payload: dict) -> dict:
            if path == "/login":
                return login_handler(**payload)
            return profile_handler(payload["id"])

        def lookup(repo: Optional[UserRepository], key) -> dict:
            return repo.find(key)

        ROUTES = {"/login": login_handler, "/name": name_handler}
    ''',
}.items()}


def run_demo(color: bool) -> int:
    p = Project(DEMO_SOURCES)
    h = lambda t: print(f"\n{'═' * 8} {t} {'═' * max(4, 60 - len(t))}")
    failures = []

    def check(cond: bool, msg: str):
        print(("  ✔ " if cond else "  ✘ ") + msg)
        if not cond:
            failures.append(msg)

    h("STAGE 1 · Symbol table")
    for qn, s in p.symbols.items():
        if s.kind != "module":
            print("  " + describe(p, qn))
    check(p.symbols["myapp.db.connection.execute_query"].params == ["sql: str", "params: tuple = ()"],
          "parameters (types + defaults) extracted")
    check(p.symbols["myapp.db.connection.execute_query"].returns == "list[dict]", "return type extracted")
    check(p.symbols["myapp.services.user_service.AdminRepository"].bases == ["myapp.services.user_service.UserRepository"],
          "base class resolved")
    dia = Project({"d.py": "class O: pass\nclass A(O): pass\nclass B(O): pass\nclass C(A, B): pass\n"
                           "class X(Y): pass\nclass Y(X): pass\n"})
    check([q[2:] for q in dia.mro("d.C")] == ["C", "A", "B", "O"], "C3 MRO on diamond inheritance (same as Python)")
    check(dia.mro("d.X") == ["d.X", "d.Y"], "no infinite loop on cyclic inheritance")
    br = Project({"b.py": "class P:\n    def run(self): pass\nclass Q:\n    def run(self): pass\n"
                          "def f(flag):\n    x = P() if flag else None\n    if flag:\n        x = P()\n"
                          "    else:\n        x = Q()\n    x.run()\n"})
    check({"b.P.run", "b.Q.run"} <= br.callees["b.f"].keys(), "all types from if/else branches linked")

    h("STAGE 2 · Bidirectional call graph")
    for qn in ("myapp.db.connection.execute_query", "myapp.utils.helpers.fetch_one",
               "myapp.services.user_service.UserService.authenticate"):
        print(f"  {p.label(qn)}")
        print(f"     callees → {sorted(map(p.label, p.callees.get(qn, ())))}")
        print(f"     callers ← {sorted(map(p.label, p.callers.get(qn, ())))}")
    S, A = "myapp.services.user_service.", "myapp.api.routes."
    edges = [
        ("myapp.db.connection.execute_query", "myapp.db.connection.Connection.cursor", "inferred from return type"),
        ("myapp.utils.helpers.fetch_one", "myapp.db.connection.execute_query", "aliased import"),
        ("myapp.utils.helpers.audit_log", "myapp.db.connection.execute_query", "function-local relative import"),
        (S + "UserRepository.find_by_email", S + "BaseRepository.find", "self.method → MRO"),
        (S + "AdminRepository.find", S + "BaseRepository.find", "super()"),
        (S + "UserService.authenticate", S + "UserRepository.find_by_email", "self.repo instance attribute"),
        (A + "login_handler", S + "UserService.authenticate", "Class().method"),
        (A + "profile_handler", S + "BaseRepository.find", "annotated local + inheritance"),
        (A + "lookup", S + "BaseRepository.find", "Optional[...] parameter type"),
        ("myapp.api.routes", A + "login_handler", "callback reference (ROUTES dict)"),
    ]
    for a, b, why in edges:
        check(b in p.callees.get(a, {}) and a in p.callers.get(b, {}), f"{p.label(a)} → {p.label(b)}  ({why})")
    check(not p.guessed, "no edge relied on name guessing")

    h("STAGE 3+4 · Blast radius: db.connection:execute_query (depth 3)")
    target = p.resolve_target("myapp/db/connection.py:execute_query")
    imp = p.blast_radius(target, max_depth=3)
    print(render(p, imp, color))

    h("STAGE 5 · Verification")
    U = "myapp.utils.helpers."
    expected = {
        1: {U + "fetch_one", U + "audit_log"},
        2: {S + "BaseRepository.find", S + "UserService.authenticate"},
        3: {S + "UserRepository.find_by_email", S + "UserRepository.find", S + "AdminRepository.find",
            A + "profile_handler", A + "login_handler", A + "lookup"},
    }
    for d, want in expected.items():
        got = {n for n, nd in imp.depth.items() if nd == d}
        check(got == want, f"degree {d} exact (nothing missing, nothing extra): {sorted(map(p.label, got))}"
                           + ("" if got == want else f"  — expected {sorted(map(p.label, want))}"))
    check(imp.kind[S + "UserRepository.find"] == "inherit", "UserRepository.find impacted through inheritance")
    unaffected = {U + "slugify", S + "UserService.display_name", A + "name_handler",
                  "myapp.db.connection.get_connection", "myapp.db.connection.Connection.cursor"}
    check(not unaffected & imp.depth.keys(), "unrelated symbols (slugify, display_name, name_handler, ...) excluded")
    check(A + "handle_request" not in imp.depth, "depth limit: handle_request cut off after degree 3")
    full = p.blast_radius(target, max_depth=None)
    check(full.depth.get(A + "handle_request") == 4, "unlimited depth: handle_request found at degree 4")
    check(full.depth.get("myapp.api.routes") == 4, "ROUTES registry (module-level reference) found at degree 4")
    check((S + "UserRepository", S + "BaseRepository") not in p.refs and
          "myapp.services.user_service" not in p.callees, "class bases produced no reference edges")
    check(imp.level == "CRITICAL" and 0 <= imp.score <= 100, f"risk score {imp.score}/100 → {imp.level}")

    h("Inheritance impact: services.user_service:BaseRepository (class change)")
    cls_imp = p.blast_radius(p.resolve_target("myapp.services.user_service:BaseRepository"), max_depth=3)
    print(render(p, cls_imp, color))
    check({S + "UserRepository", S + "AdminRepository"} <= cls_imp.depth.keys(),
          "base class change propagated to all subclasses")

    print(f"\n{'✘ ' + str(len(failures)) + ' check(s) FAILED' if failures else '✔ All checks passed'}")
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser(prog="blastradius", description="Static change-impact (blast radius) analyzer for Python")
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("analyze", help="show the blast radius and risk score of a target")
    a.add_argument("root")
    a.add_argument("target", help="file.py:function  or  file.py:Class.method")
    a.add_argument("--depth", type=int, default=3, help="maximum degree (0 = unlimited)")
    a.add_argument("--json", action="store_true")
    g = sub.add_parser("graph", help="list callees/callers of a target")
    g.add_argument("root")
    g.add_argument("target")
    sub.add_parser("symbols", help="print the global symbol table").add_argument("root")
    sub.add_parser("demo", help="build a sample project in memory, analyze and verify it")
    args = ap.parse_args(argv)

    color = sys.stdout.isatty() and "NO_COLOR" not in os.environ
    if color and os.name == "nt":
        os.system("")  # enables ANSI (VT) mode in the Windows console
    if args.cmd == "demo":
        return run_demo(color)
    try:
        p = Project.from_dir(args.root)
        for e in p.errors:
            print(f"warning: could not parse — {e}", file=sys.stderr)
        if args.cmd == "symbols":
            for qn, s in p.symbols.items():
                if s.kind != "module":
                    print(describe(p, qn))
            return 0
        target = p.resolve_target(args.target)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    if args.cmd == "graph":
        print(describe(p, target))
        for title, edges in (("callees →", p.callees.get(target, {})), ("callers ←", p.callers.get(target, {}))):
            print(f"  {title}")
            for n, cnt in sorted(edges.items()):
                print(f"     {p.label(n)}  ×{cnt}" + ("  ~guessed" if (target, n) in p.guessed or (n, target) in p.guessed else ""))
        return 0
    imp = p.blast_radius(target, max_depth=args.depth or None)
    print(impact_json(p, imp) if args.json else render(p, imp, color))
    return 0


if __name__ == "__main__":
    sys.exit(main())
