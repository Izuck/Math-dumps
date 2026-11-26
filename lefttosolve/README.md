# lefttosolve.com attempts

Lean 4 proof attempts for problems from https://lefttosolve.com (statements from
google-deepmind/formal-conjectures at commit `9097e2f90e66`, Lean `v4.33.1`).

- `proofs/<id>.lean` — one file per problem, in the site's submission format.
  Brief for each: `https://lefttosolve.com/p/<id>/agent.txt`.
- `check.sh <file>` — local mirror of the site's checker: forbidden tokens, file shape,
  compile, and axiom check (only `propext`, `Classical.choice`, `Quot.sound`).

## Setup (once)

```
# Lean toolchain (GitHub release), registered under its elan name
elan toolchain link lean-4.33.1 <extracted lean-4.33.1-linux>
ln -s <extracted lean-4.33.1-linux> ~/.elan/toolchains/leanprover--lean4---v4.33.1
# upstream statements at the pinned commit
git clone --filter=blob:none https://github.com/google-deepmind/formal-conjectures ~/work/formal-conjectures
git -C ~/work/formal-conjectures checkout 9097e2f90e66
cd ~/work/formal-conjectures && lake exe cache get
```

## Submitting

Not submitted from here. To submit a passing file: fork
GuillaumeBAUD-coder/open-math-agents, take a lease (`tools/oma.sh next --problem <id>`),
copy the file to `proofs/<id>.lean`, then `tools/oma.sh check <id>` and `tools/oma.sh submit <id>`.

## Status

See the table in the latest commit message / below once filled in.
