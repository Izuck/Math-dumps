#!/usr/bin/env bash
# Local mirror of the lefttosolve.com checker rules.
# Usage: lefttosolve/check.sh <proof.lean>
# Needs: formal-conjectures at the pinned commit in $FC (default ~/work/formal-conjectures),
# with `lake exe cache get` already run.
set -uo pipefail
f=$(realpath "$1")
FC=${FC:-$HOME/work/formal-conjectures}
export PATH=$HOME/.elan/bin:$PATH
fail=0

# (d) forbidden tokens, outside comments
code=$(python3 -I - "$f" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
s=re.sub(r'/-.*?-/','',s,flags=re.S)
s=re.sub(r'--[^\n]*','',s)
print(s)
PY
)
if grep -q '"' "$f"; then echo "FAIL: double-quote character present"; fail=1; fi
for w in sorry admit axiom native_decide unsafe partial implemented_by extern macro syntax elab notation initialize run_cmd attribute opaque; do
  if grep -qE "(^|[^A-Za-z0-9_.'])$w([^A-Za-z0-9_']|$)" <<<"$code"; then echo "FAIL: forbidden token: $w"; fail=1; fi
done
grep -qE 'decide[[:space:]]*:=[[:space:]]*true' <<<"$code" && { echo "FAIL: decide := true"; fail=1; }
grep -qE '(^|[[:space:]])#[a-z]' <<<"$code" && { echo "FAIL: #-command"; fail=1; }
# (a) import line first
imp=$(head -1 "$f")
[[ $imp == import\ FormalConjectures.* ]] || { echo "FAIL: first line must be the given import"; fail=1; }
# (b) exactly one OMA.solution / OMA.disproof
n=$(grep -cE '^theorem OMA\.(solution|disproof) : ' "$f")
[[ $n == 1 ]] || { echo "FAIL: need exactly one OMA.solution or OMA.disproof (found $n)"; fail=1; }

# build the imported upstream module, then compile + axiom check
mod=${imp#import }
(cd "$FC" && lake build "$mod" 2>&1 | tail -3) || true
tmp=$(mktemp -d); name=$(grep -oE 'OMA\.(solution|disproof)' "$f" | head -1)
cp "$f" "$tmp/P.lean"; printf '\n#print axioms %s\n' "$name" >> "$tmp/P.lean"
out=$(cd "$FC" && timeout 1800 lake env lean "$tmp/P.lean" 2>&1); rc=$?
echo "$out" | tail -40
rm -rf "$tmp"
[[ $rc == 0 ]] || { echo "FAIL: lean exited $rc"; fail=1; }
echo "$out" | grep -qE 'error' && { echo "FAIL: errors"; fail=1; }
echo "$out" | grep -q 'sorryAx' && { echo "FAIL: uses sorry"; fail=1; }
ax=$(echo "$out" | grep -oE "depends on axioms: \[[^]]*\]" | sed 's/.*\[//;s/\]//;s/,/ /g')
for a in $ax; do case $a in propext|Classical.choice|Quot.sound) ;; *) echo "FAIL: axiom $a"; fail=1;; esac; done
[[ $fail == 0 ]] && echo "PASS: $f" || echo "NOT ACCEPTED: $f"
exit $fail
