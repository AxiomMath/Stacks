module

public import StacksFrontier.AlgebraicGeometry.CommonDegreeTwist.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleTwistIso.Multiplication

/-!
# The twist comparison maps on an open of `Proj` with a common-degree cover

Let `S` be a graded ring, `X = Proj(S)` and `Y ⊆ X` an open admitting a finite cover by standard
opens `D₊(f_i)` with the `f_i` homogeneous of one common positive degree `d`. For a graded
`S`-module `M` and an integer `n` the canonical comparison

`M̃(nd)|_Y = M̃|_Y ⊗_{𝒪_Y} 𝒪_Y(nd) ⟶ M(nd)~|_Y`

is an isomorphism, and so is every multiplication map
`𝒪_Y(nd) ⊗_{𝒪_Y} 𝒪_Y(m) ⟶ 𝒪_Y(nd + m)` — for an *arbitrary* integer `m`, not only a multiple
of `d`.

## Main results

* `Stacks.AlgebraicGeometry.CommonDegreeTwist.le_ratioLocus`: such a `Y` lies in the union of the
  standard opens `D₊(fg)` with `deg f = deg g + d`, which is Tag 01MU's second description of
  `W_d`.
* `Stacks.AlgebraicGeometry.CommonDegreeTwist.isIso_restrict_moduleTwistMap_mul_degree`:
  **Stacks Tag 01MW (4)**, the comparison for an arbitrary graded module.
* `Stacks.AlgebraicGeometry.CommonDegreeTwist.isIso_restrict_twistMultiplication_mul_degree`:
  **Stacks Tag 01MW (3)**, the multiplication maps of Equation 01MO between the twists.

## The route

Both clauses are the Tag 01MU material read at `Y` instead of at `W_d`. The inputs are
the general forms
`Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_restrictFunctor_moduleTwistMap` and
`Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_restrictFunctor_twistMultiplicationMap_left`,
which are stated for every open contained in the ratio locus, so the only thing to supply is the
containment `le_ratioLocus`: a common-degree cover puts `Y` inside `W_d` by
`Stacks.AlgebraicGeometry.CommonDegreeTwist.le_whereInvertible`, and `W_d` inside the ratio locus
by `Stacks.AlgebraicGeometry.GoodOpenClose.whereInvertible_le_ratioLocus`.

Clause (3) is stated on Equation 01MO's own multiplication map
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap`, which is what the source
names, with the second index arbitrary. The multiplication clause of
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.IsGoodOpen` would only give the maps whose *both*
indices are multiples of `d`, and that is weaker than what Tag 01MW (3) asserts; the arbitrary
second index comes from the trivialization of the left factor alone.

## Implementation notes

The positivity of the common degree is not used, as it is not used by the Tag 01MU results
either; it is carried in the bundled cover because Tag 01MW's statement carries it.

## References

* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShifted
open Stacks.GradedLocalization
open Stacks.GradedModule (shiftedGrading)

namespace Stacks.AlgebraicGeometry.CommonDegreeTwist

universe u w t

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- An open of `Proj(S)` with a finite cover by standard opens of one common degree `d` lies in
the union of the standard opens `D₊(fg)` with `deg f = deg g + d`, which is Tag 01MU's second
description of the invertible locus `W_d`. -/
theorem le_ratioLocus (Y : (AlgebraicGeometry.Proj 𝒮).Opens)
    (C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒮 Y) :
    Y ≤ ProjShared.ratioLocus 𝒮 C.degree :=
  (le_whereInvertible 𝒮 Y C).trans (GoodOpenClose.whereInvertible_le_ratioLocus 𝒮 C.degree)

/-! ### Stacks Tag 01MW (4) -/

section Module

variable {M : Type u} [AddCommGroup M] [Module S M] {τ : Type t} [SetLike τ M]
  [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]

/-- **Stacks Tag 01MW (4).** Let `Y` be an open of `Proj(S)` admitting a finite cover by standard
opens defined by homogeneous elements of one common positive degree `d`. Then for every graded
`S`-module `M` and every integer `n` the canonical comparison
`M̃|_Y ⊗_{𝒪_Y} 𝒪_Y(nd) ⟶ M(nd)~|_Y` is an isomorphism. -/
theorem isIso_restrict_moduleTwistMap_mul_degree (Y : (AlgebraicGeometry.Proj 𝒮).Opens)
    (C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒮 Y) (n : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor Y.ι).map
      (moduleTwistMap 𝒮 𝒨 ((C.degree : ℤ) * n))) :=
  ModuleTwistIso.isIso_restrictFunctor_moduleTwistMap 𝒮 𝒨 (le_ratioLocus 𝒮 Y C) n

end Module

/-! ### Stacks Tag 01MW (3) -/

/-- **Stacks Tag 01MW (3).** Let `Y` be an open of `Proj(S)` admitting a finite cover by standard
opens defined by homogeneous elements of one common positive degree `d`. Then for every integer
`n` and every integer `m` — not only for `m` a multiple of `d` — the multiplication map of
Equation 01MO,

`𝒪_Y(nd) ⊗_{𝒪_Y} 𝒪_Y(m) ⟶ 𝒪_Y(nd + m)`,

is an isomorphism. -/
theorem isIso_restrict_twistMultiplication_mul_degree
    (Y : (AlgebraicGeometry.Proj 𝒮).Opens)
    (C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒮 Y) (n m : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor Y.ι).map
      (ProjInvertibleLocus.twistMultiplicationMap 𝒮 ((C.degree : ℤ) * n) m)) :=
  ModuleTwistIso.isIso_restrictFunctor_twistMultiplicationMap_left 𝒮
    (le_ratioLocus 𝒮 Y C) n m

end Stacks.AlgebraicGeometry.CommonDegreeTwist

end
