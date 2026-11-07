# A local T(b) theorem for perfect multilinear Calderón–Zygmund operators, formalized

A Lean 4 + Mathlib formalization of the three main theorems of

> M. Mirek and C. Thiele, *A local T(b) theorem for perfect multilinear Calderón–Zygmund
> operators*, Proc. London Math. Soc. (3) 114 (2017), 35–59,
> [doi:10.1112/plms.12000](https://doi.org/10.1112/plms.12000).

All three theorems are proved without `sorry` and depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Main results

### Setting

Let $`d\ge 1`$ and $`n\ge 2`$. A *dyadic cube* in $`\mathbb R^d`$ is a product
$`P=\prod_{i=1}^d\,[2^m l_i,\,2^m(l_i+1))`$ with $`m\in\mathbb Z`$ and $`l\in\mathbb Z^d`$; its
$`2^d`$ *children* are the dyadic cubes of half its side length contained in it. A *dyadic test
function* is a finite linear combination of indicator functions $`\mathbb 1_P`$ of dyadic cubes,
and $`[g]_Q=|Q|^{-1}\int_Q g`$ denotes the average of $`g`$ over $`Q`$. A *Hölder tuple* is a
tuple $`(p_j)_{j=1}^n`$ with $`1<p_j<\infty`$ and $`\sum_{j=1}^n 1/p_j=1`$.

A *perfect Calderón–Zygmund form* is an $`n`$-linear form $`\Lambda`$ on $`n`$-tuples of dyadic
test functions on $`\mathbb R^d`$ with the following three properties.

**(i) Dyadic decay.** If all $`f_j`$ are supported on a dyadic cube $`P`$ and two of them are
supported on different children of $`P`$, then, for every Hölder tuple,

```math
|\Lambda(f_1,\dots,f_n)|\le\prod_{j=1}^n\|f_j\|_{p_j}.
```

**(ii) Perfect smoothness.** If some $`f_i`$ is supported on a dyadic cube $`P`$ and has mean
zero, and some $`f_j`$ with $`j\ne i`$ vanishes on $`P`$, then $`\Lambda(f_1,\dots,f_n)=0`$.

**(iii) Qualitative truncation.** For a kernel $`K`$ that is a dyadic test function on
$`\mathbb R^{dn}`$,

```math
\Lambda(f_1,\dots,f_n)=\int_{\mathbb R^{dn}}K(x)\prod_{j=1}^n f_j(x_j)\,dx .
```

Fix a Hölder tuple $`(p_j)`$. In all three theorems the constant $`C`$ depends only on $`d`$,
$`n`$, $`B`$ and $`(p_j)`$, and not on the form $`\Lambda`$ or on the testing functions.

### Theorem 1.3 (perfect multilinear local T(1) theorem)

Let $`B\ge 1`$ and let $`\Lambda`$ be a perfect Calderón–Zygmund form such that

```math
|\Lambda(f_1,\dots,f_n)|\le B\prod_{j=1}^n\|f_j\|_{p_j}
```

whenever, for some dyadic cube $`P`$ and some index $`j_0`$, $`f_j=\mathbb 1_P`$ for all
$`j\ne j_0`$ and $`f_{j_0}`$ is a dyadic test function supported on $`P`$. Then

```math
|\Lambda(f_1,\dots,f_n)|\le C\prod_{j=1}^n\|f_j\|_{p_j}
```

for all $`n`$-tuples of dyadic test functions.

The paper states this theorem without proof, as folklore. The formalization proves it by a
dyadic paraproduct argument, with a dyadic John–Nirenberg inequality for the paraproduct
symbols.

### Theorem 1.4 (perfect multilinear local T(b) theorem)

A *path* of length $`k`$ in $`I_n=\{1,\dots,n\}`$ is an injective map $`\sigma:I_k\to I_n`$. A
collection $`\Sigma`$ of paths is *admissible* if

1. for each $`j\in I_n`$ there is a path $`\sigma\in\Sigma`$ of length $`1`$ with
   $`\sigma(1)=j`$;
2. every path in $`\Sigma`$ of length $`k<n`$ extends to a path in $`\Sigma`$ of length $`k+1`$;
3. for every path $`\sigma\in\Sigma`$ of length $`k\ge 2`$, the path obtained by interchanging
   the values $`\sigma(k-1)`$ and $`\sigma(k)`$ also lies in $`\Sigma`$.

For a path $`\sigma`$ of length $`k`$, an $`n`$-tuple $`\mathbf Q=(Q_1,\dots,Q_n)`$ of dyadic
cubes is *$`\sigma`$-nested* if $`Q_{\sigma(i)}\supseteq Q_{\sigma(j)}`$ for $`i<j\le k`$,
$`Q_s=Q_{\sigma(k)}`$ for every $`s`$ outside the range of $`\sigma`$, and, when $`k=n`$,
$`Q_{\sigma(n-1)}=Q_{\sigma(n)}`$.

Let $`1\le k\le n`$, $`B\ge 1`$, let $`\Lambda`$ be a perfect Calderón–Zygmund form and
$`\Sigma`$ an admissible collection. Suppose that for each path $`\sigma\in\Sigma`$ of length
$`k`$, each $`\sigma`$-nested tuple $`\mathbf Q`$ and each $`j\in\sigma(I_{k-1})`$ a dyadic test
function $`b_{\sigma,\mathbf Q,j}`$ is given such that

* **(1.5) support:** $`\mathrm{supp}\,b_{\sigma,\mathbf Q,j}\subseteq Q_j`$;
* **(1.6) mean:** $`\int b_{\sigma,\mathbf Q,j}=|Q_j|`$;
* **(1.7) norm bound:** $`\int|b_{\sigma,\mathbf Q,j}|^{p_j}\le B\,|Q_j|`$;
* **(1.8) interdependence:** for paths $`\sigma,\sigma'\in\Sigma`$ of length $`k`$, a
  $`\sigma`$-nested $`\mathbf Q`$, a $`\sigma'`$-nested $`\mathbf Q'`$ and $`l<k`$, if
  $`\sigma(i)=\sigma'(i)`$ and $`Q_{\sigma(i)}=Q'_{\sigma'(i)}`$ for all $`i\le l`$, then
  $`b_{\sigma,\mathbf Q,\sigma(l)}=b_{\sigma',\mathbf Q',\sigma'(l)}`$;

**(1.9) testing:** for every dyadic test function $`g`$ supported on $`Q_{\sigma(k)}`$,

```math
|\Lambda(f_1,\dots,f_n)|\le B\prod_{j=1}^n\|f_j\|_{p_j},
\qquad
f_{\sigma(k)}=g,\quad
f_{\sigma(l)}=\mathbb 1_{Q_{\sigma(k)}}\,b_{\sigma,\mathbf Q,\sigma(l)}\ (l<k),\quad
f_s=\mathbb 1_{Q_{\sigma(k)}}\ (s\notin\sigma(I_k)).
```

Then

```math
|\Lambda(f_1,\dots,f_n)|\le C\prod_{j=1}^n\|f_j\|_{p_j}
```

for all $`n`$-tuples of dyadic test functions.

The paper allows $`k\ge 1`$ and $`n\ge\min(k,2)`$. The formal statement covers this range: a
Hölder tuple of finite exponents forces $`n\ge 2`$, and for $`k>n`$ there are no paths of length
$`k`$, so the hypotheses are vacuous. The case $`k=1`$ is Theorem 1.3.

### Theorem 1.11 (perfect multilinear global T(b) theorem)

Let $`B\ge 1`$, let $`\Lambda`$ be a perfect Calderón–Zygmund form, and let
$`b_1,\dots,b_n`$ be dyadic test functions such that, for all dyadic cubes $`Q`$ and all
$`j`$,

```math
\begin{aligned}
&|[b_j]_Q|\ge 1, &&\text{(1.12) pseudo-accretivity}\\
&\|b_j\|_{L^\infty}\le B, &&\text{(1.13) norm bound}\\
&|\Lambda(b_1\mathbb 1_Q,\dots,b_n\mathbb 1_Q)|\le B\,|Q|, &&\text{(1.14) weak boundedness}\\
&|\Lambda(b_1,\dots,b_{j-1},g,b_{j+1},\dots,b_n)|\le B\,\|g\|_{H^1}\ \text{for all dyadic test functions } g, &&\text{(1.15) BMO condition}
\end{aligned}
```

where $`\|g\|_{H^1}=\int_{\mathbb R^d}Sg`$ is the dyadic Hardy norm, defined by the dyadic square
function

```math
Sg(x)=\Bigl(\sum_{P\ni x}\bigl|[g]_{P_x}-[g]_P\bigr|^2\Bigr)^{1/2},
```

the sum running over the dyadic cubes $`P`$ containing $`x`$, and $`P_x`$ denoting the child of
$`P`$ containing $`x`$. Then

```math
|\Lambda(f_1,\dots,f_n)|\le C\prod_{j=1}^n\|f_j\|_{p_j}
```

for all $`n`$-tuples of dyadic test functions.

Condition (1.14) is taken in its scale-invariant form with the factor $`|Q|`$; the paper writes
$`\le B`$. See the modelling choices below.

## Main Lean declarations

The statements are in [`Challenge.lean`](Challenge.lean), which a reader audits, and the proofs
are exported through [`Solution.lean`](Solution.lean). Comparator checks, with
[`comparator.json`](comparator.json), that both files declare the same statements and that the
proofs use only the permitted axioms.

| Paper | Lean statement | Proved by |
|---|---|---|
| Theorem 1.3 | `MirekThiele.theorem_1_3 : LocalT1 d n p` | `MirekThiele.localT1` |
| Theorem 1.4 | `MirekThiele.theorem_1_4 : LocalTb d n k p` | `MirekThiele.localTb_all` |
| Theorem 1.11 | `MirekThiele.theorem_1_11 : GlobalTb d n p` | `MirekThiele.globalTb_all` |

The hypotheses are the Lean structures `PerfectCZForm` (fields `decay`, `smooth`,
`truncation`), `T1Testing`, `LocalTbHypotheses` (fields `support`, `testFun`, `mean`, `norm`,
`interdep`, `testing`) and `GlobalTbHypotheses` (fields `accretive`, `bound`, `weak`, `bmo`),
all defined in `Challenge.lean`. The proofs are in
[`MirekThiele/T1Theorem.lean`](MirekThiele/T1Theorem.lean).

The supporting results of Section 2 of the paper are also formalized and proved:

* Theorem 2.68, the discrete Carleson embedding: `MirekThiele.carlesonEmbedding` in
  [`MirekThiele/Estimates.lean`](MirekThiele/Estimates.lean);
* Lemmas 2.71 and 2.72: `MirekThiele.lemma271`, `MirekThiele.lemma272` and the endpoint variant
  `MirekThiele.lemma272one`, in the same module;
* the main estimate of Sections 2.2–2.8, the contraction step $`A\le A\theta+C`$:
  `MirekThiele.contractionStep` and its iteration `MirekThiele.restrictedTesting` in
  [`MirekThiele/T1Theorem.lean`](MirekThiele/T1Theorem.lean).

## Modelling choices

These are also listed in the module docstring of `Challenge.lean` and in
[`formalization.yaml`](formalization.yaml).

* The weak boundedness condition (1.14) is required in the scale-invariant form
  $`|\Lambda(b_1\mathbb 1_Q,\dots,b_n\mathbb 1_Q)|\le B\,|Q|`$. The paper writes $`\le B`$, which
  is not dimensionally consistent with the conclusion; the factor $`|Q|`$ is also what the
  global/local reduction uses.
* The dyadic Hardy norm in (1.15) is the $`L^1`$ norm of the dyadic square function, one of the
  standard equivalent norms; $`\|\cdot\|_{L^\infty}`$ is the essential supremum.
* The testing functions $`b_{\sigma,\mathbf Q,j}`$ of Theorem 1.4 and the functions $`b_j`$ of
  Theorem 1.11 are dyadic test functions. The paper leaves this implicit, since $`\Lambda`$ is
  only defined on dyadic test functions.
* $`I_n`$ is indexed by `Fin n`, and the testing functions are indexed by their position in the
  path; since paths are injective, this is equivalent to the paper's index
  $`j\in\sigma(I_{k-1})`$.

## Repository map (Palomar layout)

* `Challenge.lean` — the statement surface to audit: the definitions of §1 of the paper (dyadic
  cubes and test functions, perfect Calderón–Zygmund forms, Hölder tuples, paths and admissible
  collections, σ-nested tuples, the hypotheses (1.5)–(1.9) and (1.12)–(1.15)) and the three
  theorems with `sorry`. Its module docstring lists every modelling choice.
* `Solution.lean` — the same three declarations, proved, importing the development.
* `MirekThiele.lean` and `MirekThiele/` — the full development, in four modules read in order:
  `Foundations` (definitions, stopping times, pruning, the first half of the main estimate),
  `Estimates` (the second stopping time, the Carleson embedding Theorem 2.68, Lemmas 2.71 and
  2.72, Marcinkiewicz interpolation for outer measures), `Contraction` (the bound on `‖Θ‖_r`, the
  contraction `A ≤ A θ + C`, the bridge from the hypotheses of Theorem 1.4 to the stopping data),
  `T1Theorem` (the contraction step and Theorem 1.4 from Theorem 1.3, the global/local reduction
  and Theorem 1.11, the atom estimate, the proof of Theorem 1.3 by the dyadic paraproduct
  argument with a dyadic John–Nirenberg inequality). The module docstring of `Foundations`
  describes the whole development.
* `comparator.json` — the declarations Comparator compares between `Challenge` and `Solution`.
* `formalization.yaml` — project metadata, sources, automation, fidelity and review information.
* `scripts/check-lean-sources.py` — the Palomar module-header and file-length check (from the
  starter repository).
* `LICENSE` — Apache License 2.0.

## Building

```
lake exe cache get
lake build
```

The toolchain is `leanprover/lean4:v4.36.0-rc2` with Mathlib pinned to the master commit
`237c53b714060dd21b54c29e7e3256ec0c65f132` of 29 October 2026 (`lake-manifest.json` is
committed). Budget several GiB for the Mathlib cache. On Windows, clone into a short path; the
build directory nests deeply.

## Status of this snapshot

The development was written and checked as a single file against the live Lean web editor
(Lean 4.36.0-rc2, Mathlib master of 29 October 2026), where it compiles with no errors and no
warnings. For this repository it was split into four modules under the 10,000-line cap and ported
to the module system (`module`, `public import`, `@[expose] public section`); the split was done
mechanically at section boundaries, re-declaring the enclosing `namespace`, `section`, `open` and
`variable` context at the top of each module. The resulting project was built locally with the
pinned toolchain and Mathlib (`lake exe cache get`, `lake build`): all modules compile, the only
warnings are the three deliberate `sorry`s of `Challenge.lean`, and `#print axioms` on the three
theorems of `Solution.lean` reports exactly `propext`, `Classical.choice` and `Quot.sound`.
`lake comparator` has not been run locally (it needs the Linux `bwrap` sandbox); Palomar runs it
during verification.
