# A local T(b) theorem for perfect multilinear Calderón–Zygmund operators, formalized

A Lean 4 / Mathlib formalization of the three main theorems of

> M. Mirek and C. Thiele, *A local T(b) theorem for perfect multilinear Calderón–Zygmund
> operators*, Proc. London Math. Soc. (3) 114 (2017), 35–59, doi:10.1112/plms.12000.

* **Theorem 1.3** — the perfect multilinear local T(1) theorem (`MirekThiele.theorem_1_3`).
* **Theorem 1.4** — the perfect multilinear local T(b) theorem with general testing functions on
  admissible collections of paths (`MirekThiele.theorem_1_4`).
* **Theorem 1.11** — the perfect multilinear global T(b) theorem (`MirekThiele.theorem_1_11`).

All three are proved without `sorry` and without additional axioms (only `propext`,
`Classical.choice`, `Quot.sound`).

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
`variable` context at the top of each module. The split files have not yet been built locally;
the first local `lake build` should be treated as the acceptance test of the port, and any issue
it reports is expected to be a module-visibility or a Mathlib-pin detail, not a mathematical one.
`Challenge.lean` alone and the three `Solution.lean` statements against the full development were
checked on the web editor.

## Submitting to Palomar

1. Build locally and run `./scripts/verify-comparator.sh` style checks as described in the
   Palomar starter repository (`lake comparator`).
2. Push to a public GitHub repository and copy the full 40-character commit SHA.
3. Open the Palomar submission form, enter the repository and commit, leave the path fields
   blank (root layout), and state your relationship to the formalization.
