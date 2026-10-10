# BlastRadius-AST

Static change-impact analyzer for Python projects. Point it at a function and it tells you
everything upstream that can break if you change it, with a 0–100 risk score and a colored
terminal tree.

Single file, pure Python 3.10+ standard library, no dependencies.

```
[CRITICAL RISK - Score: 85/100]
└─ myapp.db.connection:execute_query
   ├─ myapp.utils.helpers:audit_log (Direct)
   │  └─ myapp.services.user_service:UserService.authenticate (Transitive, degree 2) ⚠ critical
   │     └─ myapp.api.routes:login_handler (Transitive, degree 3) ⚠ critical
   └─ myapp.utils.helpers:fetch_one (Direct)
      └─ myapp.services.user_service:BaseRepository.find (Transitive, degree 2)
         ├─ myapp.api.routes:lookup (Transitive, degree 3) ⚠ critical
         ├─ myapp.api.routes:profile_handler (Transitive, degree 3) ⚠ critical
         ├─ myapp.services.user_service:AdminRepository.find (Transitive, degree 3) ⚠ critical
         ├─ myapp.services.user_service:UserRepository.find (Transitive, degree 3 · inherited)
         └─ myapp.services.user_service:UserRepository.find_by_email (Transitive, degree 3)
```

## Usage

```bash
python blastradius.py analyze <project_dir> auth/tokens.py:verify_jwt [--depth 3] [--json]
python blastradius.py analyze <project_dir> services/user.py:UserService.login
python blastradius.py graph   <project_dir> auth/tokens.py:verify_jwt   # callees / callers
python blastradius.py symbols <project_dir>                             # global symbol table
python blastradius.py demo                                              # self-check
```

`--depth 0` means unlimited. Targets can also be given as dotted modules (`auth.tokens:verify_jwt`).
Set `NO_COLOR` to disable colors.

## How it works

1. **Multi-file AST parser & symbol table** — every function, method and class gets a fully
   qualified name (`pkg.module.Class.method`) with its parameters (types, defaults) and return type.
   Handles aliased, relative, function-local, re-exported and `*` imports.
2. **Bidirectional call graph** — `callees` and `callers` with call-site counts. Resolves
   `self.method()`, `super()`, `Class().method()`, `self.attr.method()`, annotated locals and
   parameters (including `Optional[X]` / `X | None`), return-type annotations, and variables
   assigned different classes in different branches. Functions passed as values
   (callbacks, route tables) count as dependencies.
3. **Inheritance** — C3 MRO. Changing a base class affects its subclasses; an inherited method
   affects subclasses that don't override it; an override affects callers of the base method
   (dynamic dispatch).
4. **Blast radius** — BFS over reverse dependencies (cycle-safe), grouped by degree:
   direct (1) and transitive (2, 3, …).
5. **Risk score**

   ```
   raw   = Σ W(depth) · (2 if critical else 1)    W = 1.0, 0.6, 0.35, then 0.2
         + 0.25 · direct call sites of the target
         + 0.5  · number of other modules affected
         + 2    · (target itself is on a critical path)
   score = round(100 · (1 − e^(−raw / 6)))
   ```

   "Critical" means a name segment starts with a keyword such as `auth`, `token`, `db`, `query`,
   `payment`, `session`, `api`, `handler`. Levels: ≥75 CRITICAL, ≥50 HIGH, ≥25 MEDIUM, else LOW.

## Demo / verification

`python blastradius.py demo` builds a four-layer sample project in memory (database, utils,
service, API) with cross-module calls and inheritance, runs the analysis on a deep core function,
and asserts that every dependent is found at the right degree and nothing unrelated is included.
Exit code is non-zero if any check fails.

## Limitations

- Static only: calls coming from outside Python (JS bridges, framework decorators, `getattr`,
  string dispatch) are invisible, so the radius can be smaller than reality.
- When an object's type can't be inferred, `obj.method()` is linked by name only if exactly one
  method with that name exists in the project; such edges are marked `~guessed`.
- The "critical" flag is a naming heuristic.
