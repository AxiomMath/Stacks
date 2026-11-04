module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.SectionsInfinitesimalDiff
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceInjective

/-!
# Two sections of `Γ₀` which do not differ have one and the same comorphism

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a scheme `S`, let `U₀ ⊆ U` be a
first order thickening, let `R₀ = s^{-1}(U₀) ⊆ R` and let `δ₁, δ₂` be two elements of the set
`Γ₀` of [Stacks Project, Tag 0CKB].
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionDiff` is the `𝒪_{U₀}`-linear
map `e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` by which the two differ, and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionDiff_self` says that it
vanishes when `δ₁ = δ₂`.

This file proves that it vanishes *only* when the two comorphisms of `δ₁` and `δ₂`, read
through the thickening, are one and the same morphism of sheaves of rings on the small étale
site of `R₀`.  That is the injectivity half of [Stacks Project, Tag 0618] in the groupoid
situation of Equation [Stacks Project, Tag 0CKE], at the level of comorphisms.

## Main results

* `restrictedSharpThroughThickening_eq_of_infinitesimalSectionDiff_eq_zero`: if the difference
  of two elements of `Γ₀` is zero then their two transported comorphisms are equal.
* `infinitesimalSectionDiff_eq_zero_iff`: the difference is zero exactly when the two
  transported comorphisms are equal.

## Implementation notes

Both directions are the general statements of
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceInjective.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDescent.lean` read at the datum
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionLiftDifferenceData`, whose two
maps are the two transported comorphisms by the `rfl` equations
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionLiftDifferenceData_f` and
`.infinitesimalSectionLiftDifferenceData_g`.

The local surjectivity of `j^♯` is introduced by name with `letI`, never left to instance
search: as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsInfinitesimalDiff.lean` record, a
property of a morphism of sheaves of rings on the small étale site is found by instance
resolution in the file which declares it and not in a file which imports it.  The definitional
equation `AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionDiff_eq` is used to
cross from the difference to the general descent rather than letting the kernel unfold the
definition.

## What this does not give

The conclusion is an equality of *comorphisms*, not of the two sections `δ₁` and `δ₂`.
The conclusion is an equality of *comorphisms*, not of the two sections `δ₁` and `δ₂`.  The step
from one to the other is
`AlgebraicGeometry.Space.eq_of_restrictedSharpThroughThickening_eq`, and it is taken in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsInfinitesimalUnique.lean`:
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.eq_of_infinitesimalSectionDiff_eq_zero` is the
uniqueness clause of the field `existsUnique_diff` of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference`, unconditionally.

Recovering an *arbitrary* morphism of algebraic spaces from its comorphism is the faithfulness
half of Properties of Spaces, Theorem [Stacks Project, Tag 04KL], which this development has as
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` — a theorem for a base scheme whose
canonical morphism `S ⟶ Spec Γ(S, ⊤)` is a monomorphism, so for an affine or quasi-affine base,
and open for a general one; nothing here uses, proves or weakens it.  But two morphisms
agreeing on a first order thickening factor through **one** affine
étale chart diagram of the target, so recovering one of *those* from its comorphism needs no part
of that theorem — which is why the uniqueness clause does not need it either.

## References

* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
* [Stacks Project, Tag 0CKB](https://stacks.math.columbia.edu/tag/0CKB)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bas : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS Bas)
  (U₀ : ClosedSubspaces C S hS G.objects.1)
  (hU₀ : IsFirstOrderThickening C S hS G.objects U₀.1)

include hU₀ in
/-- **Two sections of `Γ₀` with zero difference have one and the same transported
comorphism.**  The difference is the descent of the difference of the two comorphisms, and that
descent is injective: Equation [Stacks Project, Tag 0619] is a bijection and the conormal
module is included in the ambient sheaf of rings injectively. -/
theorem restrictedSharpThroughThickening_eq_of_infinitesimalSectionDiff_eq_zero
    (δ₁ δ₂ : InfinitesimalSections G U₀)
    (h : infinitesimalSectionDiff G U₀ hU₀ δ₁ δ₂ = 0) :
    restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
        δ₁.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ₁.2) =
      restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
        δ₂.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ₂.2) := by
  let := isLocallySurjective_restrictedArrowsSharp G U₀
  refine (infinitesimalSectionLiftDifferenceData_f G U₀ hU₀ δ₁ δ₂).symm.trans
    (Eq.trans ?_ (infinitesimalSectionLiftDifferenceData_g G U₀ hU₀ δ₁ δ₂))
  exact Space.eq_of_liftDifferenceDifferentialsHom_eq_zero C S hS
    (preimageProjection C S hS G.source U₀) (restrictedUnit G U₀)
    (conormalModule C S hS G.objects U₀)
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ δ₁ δ₂)
    (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ δ₁ δ₂)
    ((infinitesimalSectionDiff_eq G U₀ hU₀ δ₁ δ₂).symm.trans h)

include hU₀ in
/-- **The difference of two sections of `Γ₀` is zero exactly when their two transported
comorphisms agree.** -/
theorem infinitesimalSectionDiff_eq_zero_iff (δ₁ δ₂ : InfinitesimalSections G U₀) :
    infinitesimalSectionDiff G U₀ hU₀ δ₁ δ₂ = 0 ↔
      restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
          δ₁.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ₁.2) =
        restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
          δ₂.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ₂.2) := by
  refine ⟨restrictedSharpThroughThickening_eq_of_infinitesimalSectionDiff_eq_zero G U₀ hU₀ δ₁ δ₂,
    fun h => ?_⟩
  let := isLocallySurjective_restrictedArrowsSharp G U₀
  refine (infinitesimalSectionDiff_eq G U₀ hU₀ δ₁ δ₂).trans ?_
  exact Space.liftDifferenceDifferentialsHom_eq_zero C S hS
    (preimageProjection C S hS G.source U₀) (restrictedUnit G U₀)
    (conormalModule C S hS G.objects U₀)
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ δ₁ δ₂)
    (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ δ₁ δ₂)
    ((infinitesimalSectionLiftDifferenceData_f G U₀ hU₀ δ₁ δ₂).trans
      (h.trans (infinitesimalSectionLiftDifferenceData_g G U₀ hU₀ δ₁ δ₂).symm))

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
