module

public import Mathlib

/-!
# Challenge: the main theorems of Mirek–Thiele, *A local T(b) theorem for perfect multilinear
Calderón–Zygmund operators*, Proc. London Math. Soc. (3) 114 (2017) 35–59

This module is the small statement surface to audit. Following §1 of the paper it defines
dyadic cubes and dyadic test functions on `ℝ^d`, perfect `n`-linear Calderón–Zygmund forms
(conditions (i)–(iii), p. 35–36), Hölder tuples of exponents, paths in `I_n` and admissible
collections of paths (p. 37), `σ`-nested tuples of cubes, the hypotheses of the three main
theorems, and it states **Theorem 1.3** (local `T(1)`), **Theorem 1.4** (local `T(b)`) and
**Theorem 1.11** (global `T(b)`) with `sorry`, together with
`theorem_1_11_hypotheses_satisfiable`, which shows that the hypotheses of Theorem 1.11 hold for the
zero form with `b_j = 1`. The proofs are supplied by `Solution.lean` through the library
`MirekThiele`.

Conventions and modelling choices (also recorded in `formalization.yaml`):

* `I_n = {1, …, n}` is indexed by `Fin n`; a path of length `k` is an injective map `Fin k ↪ Fin n`.
  The testing functions of Theorem 1.4 for paths of length `k+1` are indexed by the position
  `l < k` in the path (`TestingFamily`); since paths are injective this is the paper's index
  `j = σ(l) ∈ σ(I_k)`.
* Theorem 1.4 is stated for all `k` and `n`: the hypotheses `1 ≤ k ≤ n` are part of `LocalTb`
  (for `k > n` there are no paths of length `k`, so the paper's hypotheses are vacuous), and a
  Hölder tuple of finite exponents forces `n ≥ 2`, so the paper's range `k ≥ 1`, `n ≥ min(k, 2)`
  is covered and the case `n = 1` is void. Like Theorems 1.3 and 1.11 it assumes `d ≥ 1`, which
  the paper does not repeat for Theorem 1.4 (`d = 0` is degenerate).
* The testing functions `b_{σ,𝐐,j}` are required to be dyadic test functions
  (`LocalTbHypotheses.testFun`); the paper leaves this implicit, since `Λ` is only defined on
  dyadic test functions.
* The weak boundedness condition (1.14) of Theorem 1.11 is taken in its scale-invariant form
  `|Λ(b₁𝟙_Q, …, b_n𝟙_Q)| ≤ B |Q|`; the paper writes `≤ B`.
* The functions `b_j` of Theorem 1.11 are *locally dyadic test functions* (`LocTestFun`): their
  truncation `b_j 𝟙_Q` to every dyadic cube is a dyadic test function. This admits `b_j = 1` and
  other functions without bounded support, as pseudo-accretivity on every dyadic cube requires.
  In the BMO condition (1.15) the entries `b_j` are not dyadic test functions, so
  `Λ(b_1, …, g, …, b_n)` is evaluated through a kernel of `Λ` as in the qualitative truncation
  (iii); kernels of `Λ` agree almost everywhere.
* The dyadic Hardy norm `‖·‖_{H¹}` in (1.15) is the `L¹` norm of the dyadic square function;
  `‖·‖_∞` is the essential supremum. The bound (1.15) is required for the `g` with integrable
  square function, i.e. `‖g‖_{H¹} < ∞`; for the other `g` (for instance `g = 𝟙_Q`) the paper's
  right-hand side is `+∞`, while Lean's integral of a non-integrable function is `0`.
-/

@[expose] public section

open MeasureTheory

namespace MirekThiele

/-! ## Dyadic cubes in `ℝ^d` (paper, p. 35) -/

/-- A dyadic cube in `ℝ^d`: the product `∏ᵢ [2^m lᵢ, 2^m (lᵢ + 1))` with `m ∈ ℤ`,
`l ∈ ℤ^d`. -/
@[ext]
structure DyadicCube (d : ℕ) where
  /-- the scale: the side length is `2^m` -/
  m : ℤ
  /-- the integer position -/
  l : Fin d → ℤ

deriving instance DecidableEq for DyadicCube

namespace DyadicCube

variable {d : ℕ}

/-- The side length `ℓ(P) = 2^m`. -/
noncomputable def side (P : DyadicCube d) : ℝ := (2 : ℝ) ^ P.m

/-- The cube as a subset of `ℝ^d = (Fin d → ℝ)`. -/
def toSet (P : DyadicCube d) : Set (Fin d → ℝ) :=
  {x | ∀ i, (2 : ℝ) ^ P.m * P.l i ≤ x i ∧ x i < (2 : ℝ) ^ P.m * (P.l i + 1)}

/-- The Lebesgue measure `|P| = 2^{md}`. -/
noncomputable def vol (P : DyadicCube d) : ℝ := (2 : ℝ) ^ (P.m * d)

/-- The dyadic child of `P` selected by `ε ∈ {0,1}^d`. -/
def child (P : DyadicCube d) (ε : Fin d → Bool) : DyadicCube d :=
  ⟨P.m - 1, fun i => 2 * P.l i + if ε i then 1 else 0⟩

/-- The child of `P` containing `x` (meaningful for `x ∈ P`). -/
noncomputable def childAt (P : DyadicCube d) (x : Fin d → ℝ) : DyadicCube d :=
  P.child fun i => decide ((2 : ℝ) ^ (P.m - 1) * (2 * P.l i + 1) ≤ x i)

/-- The characteristic function `𝟙_P`. -/
noncomputable def indicator (P : DyadicCube d) : (Fin d → ℝ) → ℝ := P.toSet.indicator 1

end DyadicCube

/-! ## Dyadic test functions, norms, averages -/

variable {d : ℕ}

/-- Dyadic test functions on `ℝ^d`: finite linear combinations of characteristic functions
of dyadic cubes. -/
noncomputable def TestFun (d : ℕ) : Submodule ℝ ((Fin d → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (DyadicCube.indicator (d := d)))

/-- `g` is supported on the cube `P`. -/
def SupportedOn (g : (Fin d → ℝ) → ℝ) (P : DyadicCube d) : Prop :=
  ∀ x, x ∉ P.toSet → g x = 0

/-- `g` vanishes on the cube `P`. -/
def VanishesOn (g : (Fin d → ℝ) → ℝ) (P : DyadicCube d) : Prop :=
  ∀ x ∈ P.toSet, g x = 0

/-- `g` has mean zero. -/
def MeanZero (g : (Fin d → ℝ) → ℝ) : Prop := ∫ x, g x = 0

/-- The average `[g]_P = |P|⁻¹ ∫_P g`. -/
noncomputable def avg (P : DyadicCube d) (g : (Fin d → ℝ) → ℝ) : ℝ :=
  (∫ x in P.toSet, g x) / P.vol

/-- The truncation `g_P = g 𝟙_P`. -/
noncomputable def truncate (P : DyadicCube d) (g : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  P.toSet.indicator g

/-- The `L^p` norm `‖g‖_p` (as a real number). -/
noncomputable def lpNorm (g : (Fin d → ℝ) → ℝ) (p : ℝ) : ℝ :=
  (eLpNorm g (ENNReal.ofReal p) volume).toReal

/-- The `L^∞` norm `‖g‖_∞` (as a real number). -/
noncomputable def supNorm (g : (Fin d → ℝ) → ℝ) : ℝ :=
  (eLpNorm g ⊤ volume).toReal

/-- A Hölder tuple of finite exponents: `1 < p_j < ∞` and `∑ 1/p_j = 1`. -/
structure HolderTuple (n : ℕ) where
  /-- the exponents -/
  p : Fin n → ℝ
  one_lt : ∀ j, 1 < p j
  sum_inv : ∑ j, (p j)⁻¹ = 1

/-- The product `∏_j ‖f_j‖_{p_j}`. -/
noncomputable def prodNorm {n : ℕ} (p : HolderTuple n) (f : Fin n → TestFun d) : ℝ :=
  ∏ j, lpNorm (f j : (Fin d → ℝ) → ℝ) (p.p j)

/-- Products of `n` dyadic cubes in `ℝ^d` with a common side length, i.e. dyadic cubes in
`ℝ^{dn}`. -/
def DyadicCube.prodSet {n : ℕ} (P : Fin n → DyadicCube d) : Set (Fin n → Fin d → ℝ) :=
  {x | ∀ j, x j ∈ (P j).toSet}

/-- Dyadic test functions on `ℝ^{dn}`. -/
noncomputable def TestFunProd (d n : ℕ) : Submodule ℝ ((Fin n → Fin d → ℝ) → ℝ) :=
  Submodule.span ℝ {K | ∃ P : Fin n → DyadicCube d,
    (∀ i j, (P i).m = (P j).m) ∧ K = (DyadicCube.prodSet P).indicator 1}

/-! ## Perfect Calderón–Zygmund forms (paper, p. 35–36, conditions (i)–(iii)) -/

/-- A perfect `n`-linear Calderón–Zygmund form on `ℝ^d`. -/
structure PerfectCZForm (d n : ℕ) where
  /-- the `n`-linear form `Λ` on dyadic test functions -/
  form : MultilinearMap ℝ (fun _ : Fin n => TestFun d) ℝ
  /-- (i) dyadic decay (1.1): for every Hölder tuple, if all `f_j` are supported on `P` and two
  of them on different children of `P`, then `|Λ(f)| ≤ ∏ ‖f_j‖_{p_j}`. -/
  decay : ∀ (p : HolderTuple n) (P : DyadicCube d) (f : Fin n → TestFun d),
    (∀ j, SupportedOn (f j) P) →
    (∃ i j : Fin n, i ≠ j ∧ ∃ ε ε' : Fin d → Bool, ε ≠ ε' ∧
      SupportedOn (f i) (P.child ε) ∧ SupportedOn (f j) (P.child ε')) →
    |form f| ≤ prodNorm p f
  /-- (ii) perfect smoothness (1.2): if `f_i` is supported on `P` with mean zero and `f_j`
  (`j ≠ i`) vanishes on `P`, then `Λ(f) = 0`. -/
  smooth : ∀ (P : DyadicCube d) (f : Fin n → TestFun d) (i j : Fin n), i ≠ j →
    SupportedOn (f i) P → MeanZero (f i : (Fin d → ℝ) → ℝ) → VanishesOn (f j) P →
    form f = 0
  /-- (iii) qualitative truncation: `Λ` is given by a kernel which is a dyadic test function on
  `ℝ^{dn}`. -/
  truncation : ∃ K : (Fin n → Fin d → ℝ) → ℝ, K ∈ TestFunProd d n ∧
    ∀ f : Fin n → TestFun d, form f = ∫ x, K x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)

/-! ## Paths in `I_n` and admissible collections (paper, p. 37–38)

We index `I_n = {1, …, n}` by `Fin n = {0, …, n-1}`; a path of length `k` is an injective map
`Fin k ↪ Fin n`. -/

/-- A path of length `k` in `I_n`: an injective map `I_k → I_n`. -/
abbrev IPath (n k : ℕ) := Fin k ↪ Fin n

namespace IPath

variable {n k : ℕ}

/-- Restriction of a path of length `k+1` to `I_k`. -/
def restrict (σ : IPath n (k + 1)) : IPath n k :=
  ⟨fun i => σ i.castSucc, fun _ _ h => Fin.castSucc_injective k (σ.injective h)⟩

/-- The path obtained by interchanging the last two steps of a path of length `k+2`
(condition (3), p. 37). -/
def swapLast (σ : IPath n (k + 2)) : IPath n (k + 2) :=
  (Equiv.swap (Fin.last (k + 1)) (Fin.castSucc (Fin.last k))).toEmbedding.trans σ

/-- A collection of paths in `I_n`, one set of paths for each length. -/
abbrev Collection (n : ℕ) := ∀ k : ℕ, Set (IPath n k)

/-- Admissibility of a collection of paths (conditions (1)–(3), p. 37). -/
structure Admissible (C : Collection n) : Prop where
  /-- (1) for each `j ∈ I_n` there is a path of length 1 with `σ(1) = j` -/
  singletons : ∀ j : Fin n, ∃ σ ∈ C 1, σ 0 = j
  /-- (2) every path of length `k < n` extends to a path of length `k+1` in the collection -/
  extension : ∀ k, k < n → ∀ σ ∈ C k, ∃ τ ∈ C (k + 1), τ.restrict = σ
  /-- (3) the collection is closed under interchanging the last two steps -/
  swap : ∀ k, ∀ σ ∈ C (k + 2), σ.swapLast ∈ C (k + 2)

/-- An `n`-tuple `𝐐` of dyadic cubes is `σ`-nested for a path `σ` of length `k+1` (p. 37):
`Q_{σ(i)} ⊇ Q_{σ(j)}` for `i < j`, `Q_s = Q_{σ(k)}` for `s` outside the range, and, if the
path has full length `n`, `Q_{σ(n-1)} = Q_{σ(n)}`. -/
structure Nested (σ : IPath n (k + 1)) (Q : Fin n → DyadicCube d) : Prop where
  mono : ∀ i j : Fin (k + 1), i < j → (Q (σ j)).toSet ⊆ (Q (σ i)).toSet
  outside : ∀ s : Fin n, s ∉ Set.range σ → Q s = Q (σ (Fin.last k))
  top : k + 1 = n → ∀ _ : 1 ≤ k, Q (σ ⟨k - 1, Nat.lt_of_le_of_lt (Nat.sub_le k 1) (Nat.lt_add_one k)⟩) = Q (σ (Fin.last k))

end IPath

/-! ## The main theorems -/

/-- The testing hypothesis of Theorem 1.3: all but one entry are `𝟙_P`, the remaining entry is an
arbitrary dyadic test function supported on `P`. -/
def T1Testing {n : ℕ} (T : PerfectCZForm d n) (p : HolderTuple n) (B : ℝ) : Prop :=
  ∀ (P : DyadicCube d) (j₀ : Fin n) (f : Fin n → TestFun d),
    (∀ j, j ≠ j₀ → (f j : (Fin d → ℝ) → ℝ) = P.indicator) → SupportedOn (f j₀) P →
    |T.form f| ≤ B * prodNorm p f

/-- **Theorem 1.3** (perfect multilinear local `T(1)` theorem): for `d ≥ 1`, `n ≥ 2` and `B ≥ 1`
there is a constant `C`, depending only on `d`, `n`, `B` and the Hölder tuple, such that every
perfect Calderón–Zygmund form satisfying the testing hypothesis with constant `B` satisfies
`|Λ(f)| ≤ C ∏ ‖f_j‖_{p_j}` for all tuples of dyadic test functions. -/
def LocalT1 (d n : ℕ) (p : HolderTuple n) : Prop :=
  1 ≤ d → 2 ≤ n → ∀ B : ℝ, 1 ≤ B → ∃ C : ℝ, ∀ T : PerfectCZForm d n,
    T1Testing T p B → ∀ f : Fin n → TestFun d, |T.form f| ≤ C * prodNorm p f

/-- The testing functions `b_{σ,𝐐,·}` of Theorem 1.4 for paths of length `k+1`: for each path
`σ`, each tuple `𝐐` and each position `l < k` in the path (so that `σ(l) ∈ σ(I_{k})`) a
function on `ℝ^d`. -/
abbrev TestingFamily (d n k : ℕ) :=
  IPath n (k + 1) → (Fin n → DyadicCube d) → Fin k → (Fin d → ℝ) → ℝ

/-- The testing condition (1.9) of Theorem 1.4 for a family `b` of testing functions on paths of
length `k+1`, with constant `B`: for every admissible `σ`, every `σ`-nested `𝐐` and every dyadic
test function `g` supported on `Q_{σ(k)}`, `|Λ(f)| ≤ B ∏ ‖f_j‖_{p_j}` where `f_{σ(k)} = g`,
`f_{σ(l)} = 𝟙_{Q_{σ(k)}} b_{σ,𝐐,σ(l)}` for `l < k` and `f_s = 𝟙_{Q_{σ(k)}}` outside the range. -/
abbrev TestingCondition {n : ℕ} (T : PerfectCZForm d n) (p : HolderTuple n)
    (C : IPath.Collection n) {k : ℕ} (b : TestingFamily d n k) (B : ℝ) : Prop :=
  ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q →
    ∀ g : TestFun d, SupportedOn g (Q (σ (Fin.last k))) →
    ∀ f : Fin n → TestFun d, f (σ (Fin.last k)) = g →
    (∀ l : Fin k, (f (σ l.castSucc) : (Fin d → ℝ) → ℝ) =
      truncate (Q (σ (Fin.last k))) (b σ Q l)) →
    (∀ s, s ∉ Set.range σ → (f s : (Fin d → ℝ) → ℝ) = (Q (σ (Fin.last k))).indicator) →
    |T.form f| ≤ B * prodNorm p f

/-- Hypotheses (1.5)–(1.9) of Theorem 1.4 for paths of length `k+1`, with constant `B`. -/
structure LocalTbHypotheses {n : ℕ} (T : PerfectCZForm d n) (p : HolderTuple n)
    (C : IPath.Collection n) {k : ℕ} (b : TestingFamily d n k) (B : ℝ) : Prop where
  /-- support condition (1.5) -/
  support : ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q → ∀ l : Fin k,
    SupportedOn (b σ Q l) (Q (σ l.castSucc))
  /-- the testing functions are dyadic test functions (implicit in the paper, where the form
  `Λ` is only defined on dyadic test functions) -/
  testFun : ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q → ∀ l : Fin k, b σ Q l ∈ TestFun d
  /-- mean condition (1.6) -/
  mean : ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q → ∀ l : Fin k,
    ∫ x, b σ Q l x = (Q (σ l.castSucc)).vol
  /-- norm bound condition (1.7) -/
  norm : ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q → ∀ l : Fin k,
    ∫ x, |b σ Q l x| ^ p.p (σ l.castSucc) ≤ B * (Q (σ l.castSucc)).vol
  /-- interdependence condition (1.8) -/
  interdep : ∀ σ ∈ C (k + 1), ∀ σ' ∈ C (k + 1), ∀ Q Q', IPath.Nested σ Q → IPath.Nested σ' Q' →
    ∀ l : Fin k,
    (∀ l' : Fin k, l' ≤ l →
      σ l'.castSucc = σ' l'.castSucc ∧ Q (σ l'.castSucc) = Q' (σ' l'.castSucc)) →
    b σ Q l = b σ' Q' l
  /-- testing condition (1.9) -/
  testing : TestingCondition T p C b B

/-- **Theorem 1.4** (perfect multilinear local `T(b)` theorem), for paths of length `k` with
`1 ≤ k ≤ n`: for `B ≥ 1` there is a constant `C`, depending only on `d`, `n`, `B` and the Hölder
tuple, such that for every perfect Calderón–Zygmund form, every admissible collection of paths
and every family of testing functions satisfying (1.5)–(1.9) with constant `B`,
`|Λ(f)| ≤ C ∏ ‖f_j‖_{p_j}` for all tuples of dyadic test functions. (The paper writes
`n ≥ min(k, 2)`; the hypotheses concern paths of length `k` in `I_n`, which exist only for
`k ≤ n`, and `n ≥ 2` is automatic for a Hölder tuple of finite exponents.) -/
def LocalTb (d n k : ℕ) (p : HolderTuple n) : Prop :=
  1 ≤ d → 1 ≤ k → k ≤ n → ∀ B : ℝ, 1 ≤ B → ∃ C : ℝ,
    ∀ (T : PerfectCZForm d n) (𝒞 : IPath.Collection n), IPath.Admissible 𝒞 →
    ∀ b : TestingFamily d n (k - 1), LocalTbHypotheses T p 𝒞 b B →
    ∀ f : Fin n → TestFun d, |T.form f| ≤ C * prodNorm p f

/-- The dyadic square function `S g(x) = (∑_{P ∋ x} |[g]_{P_x} − [g]_P|²)^{1/2}`, the sum running
over the dyadic cubes `P` containing `x`, with `P_x` the child of `P` containing `x`. For a dyadic
test function `g` the series converges at every point: the terms of the cubes on which `g` is
constant vanish, and the others decay geometrically with the side length. -/
noncomputable def dyadicSquareFun (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑' P : DyadicCube d,
    P.toSet.indicator (fun y => (avg (P.childAt y) g - avg P g) ^ 2) x)

/-- The dyadic Hardy-space norm `‖g‖_{H¹} = ∫ S g` (pre-dual of dyadic BMO). It is the norm of `g`
when `S g` is integrable, that is, when `‖g‖_{H¹} < ∞`; otherwise the integral takes Lean's default
value `0`, so the BMO condition (1.15) below assumes that `S g` is integrable. -/
noncomputable def hardyNorm (g : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ x, dyadicSquareFun g x

/-- A *locally dyadic test function*: a function `b` on `ℝ^d` whose truncation `b 𝟙_Q` to every
dyadic cube `Q` is a dyadic test function. Constant functions, in particular `b = 1`, are of this
kind, so a locally dyadic test function need not have bounded support. -/
def LocTestFun (d : ℕ) : Set ((Fin d → ℝ) → ℝ) :=
  {b | ∀ Q : DyadicCube d, truncate Q b ∈ TestFun d}

/-- Hypotheses (1.12)–(1.15) of Theorem 1.11, for locally dyadic test functions `b_1, …, b_n` (for
example `b_j = 1`). The weak boundedness condition (1.14) is taken in its standard scale-invariant
form `|Λ(b₁𝟙_Q, …, b_n𝟙_Q)| ≤ B |Q|` (the paper writes `≤ B`, which is not dimensionally consistent
with (1.16): a bounded form satisfies `|Λ(b₁𝟙_Q, …, b_n𝟙_Q)| ≤ C B^n |Q|`, and the factor `|Q|` is
needed in the global/local reduction). In the BMO condition (1.15) the entries `b_j` need not be
dyadic test functions, so `Λ(b_1, …, g, …, b_n)` is evaluated through a kernel `K` of `Λ` as in the
qualitative truncation (iii), `∫ K(x) ∏_j f_j(x_j) dx`; the bound is required for every such kernel
(two kernels of `Λ` agree almost everywhere) and for every dyadic test function `g` with
`‖g‖_{H¹} < ∞`, i.e. with integrable square function (for the other `g` the paper's bound is
`+∞` and says nothing). -/
structure GlobalTbHypotheses {n : ℕ} (T : PerfectCZForm d n) (b : Fin n → (Fin d → ℝ) → ℝ)
    (B : ℝ) : Prop where
  /-- the functions `b_j` are locally dyadic test functions -/
  loc : ∀ j, b j ∈ LocTestFun d
  /-- pseudo-accretivity (1.12) -/
  accretive : ∀ (Q : DyadicCube d) (j : Fin n), 1 ≤ |avg Q (b j)|
  /-- norm bound (1.13): `‖b_j‖_∞ ≤ B` -/
  bound : ∀ j, eLpNorm (b j) ⊤ volume ≤ ENNReal.ofReal B
  /-- weak boundedness (1.14) -/
  weak : ∀ (Q : DyadicCube d) (f : Fin n → TestFun d),
    (∀ j, (f j : (Fin d → ℝ) → ℝ) = truncate Q (b j)) → |T.form f| ≤ B * Q.vol
  /-- BMO condition (1.15) for every `g` with `‖g‖_{H¹} < ∞`, with `Λ(b_1, …, g, …, b_n)`
  evaluated through a kernel of `Λ` -/
  bmo : ∀ K ∈ TestFunProd d n,
    (∀ f : Fin n → TestFun d, T.form f = ∫ x, K x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)) →
    ∀ (j₀ : Fin n) (g : TestFun d), Integrable (dyadicSquareFun (g : (Fin d → ℝ) → ℝ)) →
      |∫ x, K x * ∏ j, (Function.update b j₀ (g : (Fin d → ℝ) → ℝ)) j (x j)| ≤
        B * hardyNorm (g : (Fin d → ℝ) → ℝ)

/-- **Theorem 1.11** (perfect multilinear global `T(b)` theorem): for `d ≥ 1`, `n ≥ 2` and
`B ≥ 1` there is a constant `C`, depending only on `d`, `n`, `B` and the Hölder tuple, such that
for every perfect Calderón–Zygmund form and all locally dyadic test functions `b_1, …, b_n`
satisfying (1.12)–(1.15) with constant `B`, `|Λ(f)| ≤ C ∏ ‖f_j‖_{p_j}` for all tuples of dyadic
test functions. -/
def GlobalTb (d n : ℕ) (p : HolderTuple n) : Prop :=
  1 ≤ d → 2 ≤ n → ∀ B : ℝ, 1 ≤ B → ∃ C : ℝ,
    ∀ (T : PerfectCZForm d n) (b : Fin n → (Fin d → ℝ) → ℝ), GlobalTbHypotheses T b B →
    ∀ f : Fin n → TestFun d, |T.form f| ≤ C * prodNorm p f

/-! ## The advertised statements -/

/-- **Theorem 1.3** (perfect multilinear local `T(1)` theorem). -/
theorem theorem_1_3 {n : ℕ} (p : HolderTuple n) : LocalT1 d n p := by
  sorry

/-- **Theorem 1.4** (perfect multilinear local `T(b)` theorem), for every `n` and `k`; the
hypotheses `1 ≤ k ≤ n` are part of `LocalTb`. -/
theorem theorem_1_4 {n : ℕ} (p : HolderTuple n) (k : ℕ) : LocalTb d n k p := by
  sorry

/-- **Theorem 1.11** (perfect multilinear global `T(b)` theorem). -/
theorem theorem_1_11 {n : ℕ} (p : HolderTuple n) : GlobalTb d n p := by
  sorry

/-- **The hypotheses of Theorem 1.11 are satisfiable, with `b_j = 1`**: for every `B ≥ 1` some
perfect Calderón–Zygmund form (the zero form) satisfies (1.12)–(1.15) with the constant functions
`b_1 = ⋯ = b_n = 1`, which do not have bounded support. So Theorem 1.11 is not vacuous, and with
`b_j = 1` its hypotheses are those of a global `T(1)` theorem. -/
theorem theorem_1_11_hypotheses_satisfiable {n : ℕ} {B : ℝ} (hB : 1 ≤ B) :
    ∃ T : PerfectCZForm d n, GlobalTbHypotheses T (fun _ _ => (1 : ℝ)) B := by
  sorry

end MirekThiele
