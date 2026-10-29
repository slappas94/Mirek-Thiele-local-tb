module

public import MirekThiele

/-!
# Proved solution

This module imports the full proof development (`MirekThiele`, four modules) and restates the
three advertised declarations of `Challenge.lean` with the same names and types. Comparator
checks that the statements agree with `Challenge.lean` and that the proofs use only the
permitted axioms (`propext`, `Quot.sound`, `Classical.choice`).

* `theorem_1_3` is Theorem 1.3 (perfect multilinear local `T(1)` theorem), `MirekThiele.localT1`.
* `theorem_1_4` is Theorem 1.4 (perfect multilinear local `T(b)` theorem),
  `MirekThiele.localTb_all`.
* `theorem_1_11` is Theorem 1.11 (perfect multilinear global `T(b)` theorem),
  `MirekThiele.globalTb_all`.
-/

@[expose] public section

namespace MirekThiele

/-- **Theorem 1.3** (perfect multilinear local `T(1)` theorem). -/
theorem theorem_1_3 {d n : ℕ} (p : HolderTuple n) : LocalT1 d n p :=
  localT1 p

/-- **Theorem 1.4** (perfect multilinear local `T(b)` theorem), for every `n` and `k`. -/
theorem theorem_1_4 {d n : ℕ} (p : HolderTuple n) (k : ℕ) : LocalTb d n k p :=
  localTb_all p k

/-- **Theorem 1.11** (perfect multilinear global `T(b)` theorem). -/
theorem theorem_1_11 {d n : ℕ} (p : HolderTuple n) : GlobalTb d n p :=
  globalTb_all p

end MirekThiele
