module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local

/-!
# Quasi-coherence from the cartesian condition on affine opens

Let `S` be a scheme and let `F` be an `𝒪_S`-module.  For opens `V' ≤ V` of `S` the restriction
map of `F` has a base-change comparison `Γ(S, V') ⊗_{Γ(S, V)} Γ(F, V) ⟶ Γ(F, V')`, namely
`Stacks.PresheafOfModules.restrictionBaseChange`.  This file proves that `F` is quasi-coherent as
soon as that comparison is bijective for every pair of *affine* opens `V' ≤ V`.

Only the basic opens of an affine open are needed: for `a : Γ(S, V)` the open `S.basicOpen a` is
affine and `Γ(S, S.basicOpen a)` is the localization of `Γ(S, V)` away from `a`, so bijectivity of
the comparison says exactly that `Γ(F, S.basicOpen a)` is the localization of `Γ(F, V)` away from
`a`, which is the criterion
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`.

## Main results

* `Stacks.AlgebraicGeometry.CartesianQuasicoherent.isQuasicoherent_of_bijective_restriction`:
  **a module whose base-change comparison is bijective on every pair of nested affine opens is
  quasi-coherent.**
* `Stacks.AlgebraicGeometry.CartesianQuasicoherent.isQuasicoherent_of_isIso_restriction`: the
  same criterion with the comparison assumed to be an isomorphism, which is the form the
  cartesian condition takes in `Stacks.PresheafOfModules`.

## Implementation notes

`Stacks.PresheafOfModules.restrictionBaseChange` and the comparison map underlying
`IsBaseChange` are the same map: both are `Γ(S, V')`-linear and both send `1 ⊗ₜ x` to the
restriction of `x`, the first by
`Stacks.PresheafOfModules.restrictionBaseChange_one_tmul`.  So the bijectivity hypothesis is fed
to `IsBaseChange.of_equiv` directly, with no induction over the tensor product, and
`isLocalizedModule_iff_isBaseChange` converts the conclusion into the localization statement.

## References

* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.TorsionQuasicoherent

universe u

namespace Stacks.AlgebraicGeometry.CartesianQuasicoherent

variable {S : Scheme.{u}}

/-- **A module whose restriction maps are base-change bijections between affine opens is
quasi-coherent.**  Applied to a basic open `S.basicOpen a` of an affine open `V`, the hypothesis
says that the sections over `S.basicOpen a` are the localization away from `a` of the sections
over `V`. -/
theorem isQuasicoherent_of_bijective_restriction (F : S.Modules)
    (h : ∀ V V' : S.Opens, IsAffineOpen V → IsAffineOpen V' → ∀ hle : V' ≤ V,
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange
        (R := S.presheaf) F.val (homOfLE hle).op)) :
    F.IsQuasicoherent := by
  refine isQuasicoherent_of_isLocalizedModule_restrictₗ F fun U hU a ↦ ?_
  let := moduleOfLE F (S.basicOpen_le a)
  have hloc : IsLocalization.Away a Γ(S, S.basicOpen a) := hU.isLocalization_basicOpen a
  have htow : IsScalarTower Γ(S, U) Γ(S, S.basicOpen a) Γ(F, S.basicOpen a) :=
    isScalarTowerOfLE F (S.basicOpen_le a)
  refine (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) Γ(S, S.basicOpen a)
    (restrictₗ F (S.basicOpen_le a))).mpr
    (IsBaseChange.of_equiv (LinearEquiv.ofBijective
      (Stacks.PresheafOfModules.restrictionBaseChange (R := S.presheaf) F.val
        (homOfLE (S.basicOpen_le a)).op).hom
      (h U (S.basicOpen a) hU (hU.basicOpen a) (S.basicOpen_le a))) fun x ↦ ?_)
  exact Stacks.PresheafOfModules.restrictionBaseChange_one_tmul (R := S.presheaf) F.val _ x

/-- **A module which is cartesian on affine opens is quasi-coherent**: the form of
`Stacks.AlgebraicGeometry.CartesianQuasicoherent.isQuasicoherent_of_bijective_restriction` in
which the base-change comparison is an isomorphism of modules. -/
theorem isQuasicoherent_of_isIso_restriction (F : S.Modules)
    (h : ∀ V V' : S.Opens, IsAffineOpen V → IsAffineOpen V' → ∀ hle : V' ≤ V,
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := S.presheaf) F.val (homOfLE hle).op)) :
    F.IsQuasicoherent := by
  refine isQuasicoherent_of_bijective_restriction F fun V V' hV hV' hle ↦ ?_
  have := h V V' hV hV' hle
  exact ConcreteCategory.bijective_of_isIso _

end Stacks.AlgebraicGeometry.CartesianQuasicoherent

end
