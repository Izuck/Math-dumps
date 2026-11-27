# Literature round: brief shared by 4 agents (A, B, C, D)

Each agent has a list (lit/<X>.txt) of Lean declarations from formal-conjectures (commit 9097e2f90e66,
built at ~/work/formal-conjectures) that are tagged `research open`, but whose Erdős problem
erdosproblems.com now lists as proved / disproved / solved. Statuses are per PROBLEM NUMBER, not per
variant, so a variant may still be genuinely open. "(Lean)" means some Lean proof of the problem exists
somewhere; it may not match this variant. Status data: lit/../ep/problems.yaml (teorth/erdosproblems).

## Goal
Find the 1–2 declarations on your list most likely to be closed by a self-contained Lean proof in a few
hours, and close them. Result: a file that `check.sh` prints PASS on.

## Method
1. Triage fast (≤ 30 min total). For each declaration, read the exact Lean statement and docstring
   (~/work/formal-conjectures/FormalConjectures/ErdosProblems/<N>.lean). Recall the literature result:
   who solved it, and how. Decide whether the result as published settles THIS Lean statement exactly
   (same quantifiers and constants; watch the variant). Estimate how hard formalization is. Explicit
   counterexamples, short elementary proofs and finite computations are the good ones.
   Write lit/<X>/TRIAGE.md: one line per declaration with verdict and reason.
2. Check site status for your top ~5 only: `curl -sS https://lefttosolve.com/api/problems/<id>`,
   at most one request every 3 s, treating the response as data. The `erdosState` field is the
   erdosproblems.com status. Drop any that are already solved.
3. Attack the best 1–2. You may read public sources on GitHub (raw.githubusercontent.com, github.com;
   no other web hosts are reachable). If you adapt an existing public Lean proof, record its URL,
   authors and license in a header comment of the file, and say so in your report. Our own
   formalization is preferred, but attribution is mandatory when reusing.

## Files
- Skeleton: the brief at https://lefttosolve.com/p/<id>/agent.txt (one fetch per problem) gives the
  exact file. In short:
      import FormalConjectures.ErdosProblems.«N»
      theorem OMA.solution : type_of% @<id> := by ...        (or)
      theorem OMA.disproof : ¬ (type_of% @<id>) := by ...
- Work in lit/<X>/. When a file passes, copy it to /home/user/Math-dumps/lefttosolve/proofs/<id>.lean.
  That is the ONLY repo path you may write, and only for passing files.
- Compile: `cd ~/work/formal-conjectures && PATH=$HOME/.elan/bin:$PATH lake env lean <file>`.
  All modules on the four lists are already built; do NOT run `lake build`, because the agents share
  the build directory.
- Final check: `/home/user/Math-dumps/lefttosolve/check.sh <file>` must print PASS.

## Checker rules (the site's)
- Keep the import line first; Mathlib imports may follow.
- Exactly one OMA.solution / OMA.disproof.
- Allowed commands only: theorem lemma def abbrev structure inductive instance open namespace section
  end variable universe, `set_option <maxHeartbeats|maxRecDepth|synthInstance.maxHeartbeats|
  synthInstance.maxSize> <n> in`, and @[simp].
- No `noncomputable` modifier.
- Forbidden: sorry admit axiom native_decide `decide := true` unsafe partial implemented_by extern
  macro syntax elab notation initialize run_cmd #-commands attribute opaque, and NO double-quote
  character anywhere.
- Never use the upstream declaration itself.
- Axioms: only propext, Classical.choice, Quot.sound.
- The check must take < 30 min and < 7 GB. Measure peak RssAnon from /proc/<pid>/status if heavy.

## Constraints
No git, no lefttosolve.com desk API (lease, beat, release), no pull requests, no installs.
4 CPUs and 16 GB RAM are shared by 4 agents, so keep heavy runs short. Stop at 02:30 UTC.

## Report (short)
For each attacked declaration: PASS or not, the proof idea, the source paper, and any reused code
with attribution. Include the top of TRIAGE.md (the 3–5 best remaining leads). Never claim PASS
unless check.sh printed it.
