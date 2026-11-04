module

public import StacksFrontier.AlgebraicGeometry.Modules.CartesianQuasicoherent

/-!
# A quasi-coherent module is cartesian on affine opens

Let `S` be a scheme and `F` an `𝒪_S`-module. For opens `U ≤ V` of `S` the restriction map of `F`
has a base-change comparison `Γ(S, U) ⊗_{Γ(S, V)} Γ(F, V) ⟶ Γ(F, U)`, namely
`Stacks.PresheafOfModules.restrictionBaseChange`.
`StacksFrontier/AlgebraicGeometry/Modules/CartesianQuasicoherent.lean` proves that `F` is
quasi-coherent as soon as that comparison is bijective for every pair of *affine* opens `U ≤ V`.
This file proves the **converse**: for a quasi-coherent `F` the comparison is bijective on every
such pair.

## Main results

In the namespace `Stacks.AlgebraicGeometry.CartesianQuasicoherent`:

* `bijective_restrictionBaseChange_of_isQuasicoherent`
* `isIso_restrictionBaseChange_of_isQuasicoherent`

Together with `isQuasicoherent_of_bijective_restriction` and
`isQuasicoherent_of_isIso_restriction` these say that a sheaf of `𝒪_S`-modules is quasi-coherent
**exactly** when it is cartesian on the affine opens of `S`.

## Why this is not already there

The mathematical content is
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isBaseChange_restrictₗ`, which is Descent,
Proposition 03DX in the form that says the sections of a quasi-coherent module over a smaller
affine open are the base change of the sections over a larger one. What is added
here is only the identification of the comparison map underlying `IsBaseChange` with
`Stacks.PresheafOfModules.restrictionBaseChange` — both are `Γ(S, U)`-linear out of the same
tensor product and both send `1 ⊗ₜ x` to the restriction of `x` — which is the same bridge
`CartesianQuasicoherent.lean` performs in the opposite direction, there by
`CategoryTheory.IsBaseChange.of_equiv`.

The coverage note of
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentModulesAndAffines.lean` lists the converse
implications of [Stacks, Tag 0GZX] among what the development does not have, "those rest on
Descent, Proposition 03DX, which this development does not have". For a plain scheme it does
have it, through `isBaseChange_restrictₗ`, and this file is that half of the note discharged.
The other half — that a cartesian presheaf of modules on the affine opens satisfies the Zariski
sheaf condition — is
`AlgebraicGeometry.Scheme.isSheaf_affineOpensTopology_of_cartesian` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensZariskiDescent.lean`, built on the
machinery `Stacks.Sites.isSheafFor_of_cartesian` of
`StacksFrontier/CategoryTheory/Sites/Modules/CartesianSheafCondition.lean`.

## Implementation notes

The two maps are compared pointwise and the comparison is run through
`CategoryTheory.Limits.TensorProduct.induction_on` rather than through a `rw`: the two rings
`Γ(S, U)` and `Γ(S, V)` enter the statement through different coercions, so the goal is not
type-correct at `implicit` transparency and `rw` refuses it. Every step is therefore an explicit
`Eq.trans` or `congrArg`, as in
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isBaseChange_of_span`.

## References

* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.CartesianQuasicoherent

variable {X : Scheme.{u}}

/-- **A quasi-coherent module is cartesian on affine opens.** For affine opens `U ≤ V` of a
scheme `X` and a quasi-coherent `𝒪_X`-module `F`, the base-change comparison
`Γ(X, U) ⊗_{Γ(X, V)} Γ(F, V) ⟶ Γ(F, U)` is bijective.

This is the converse of
`Stacks.AlgebraicGeometry.CartesianQuasicoherent.isQuasicoherent_of_bijective_restriction`. Its
content is `Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isBaseChange_restrictₗ`; what is
done here is the identification of the two comparison maps, both of which are `Γ(X, U)`-linear
and send `1 ⊗ₜ x` to the restriction of `x`. -/
theorem bijective_restrictionBaseChange_of_isQuasicoherent (F : X.Modules) [F.IsQuasicoherent]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange
      (R := X.presheaf) F.val (homOfLE h).op) := by
  let := algebraOfLE X h
  let := moduleOfLE F h
  let := isScalarTowerOfLE F h
  have hbc := isBaseChange_restrictₗ F hU hV h
  have key : ∀ x, (Stacks.PresheafOfModules.restrictionBaseChange
      (R := X.presheaf) F.val (homOfLE h).op).hom x = hbc.equiv x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul a m =>
        exact (Stacks.PresheafOfModules.restrictionBaseChange_tmul (R := X.presheaf) F.val
          (homOfLE h).op a m).trans (IsBaseChange.equiv_tmul hbc a m).symm
    | add z w h1 h2 =>
        refine (map_add _ z w).trans (Eq.trans ?_ (map_add hbc.equiv z w).symm)
        exact congrArg₂ (· + ·) h1 h2
  refine ⟨fun x y hxy ↦ hbc.equiv.injective ((key x).symm.trans (hxy.trans (key y))),
    fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hbc.equiv.surjective y
  exact ⟨x, (key x).trans hx⟩

/-- **A quasi-coherent module is cartesian on affine opens**, in the form in which the cartesian
condition is stated in `Stacks.PresheafOfModules`: the base-change comparison is an isomorphism
of modules. This is the converse of
`Stacks.AlgebraicGeometry.CartesianQuasicoherent.isQuasicoherent_of_isIso_restriction`. -/
theorem isIso_restrictionBaseChange_of_isQuasicoherent (F : X.Modules) [F.IsQuasicoherent]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := X.presheaf) F.val (homOfLE h).op) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_restrictionBaseChange_of_isQuasicoherent F hU hV h)

end Stacks.AlgebraicGeometry.CartesianQuasicoherent

end
