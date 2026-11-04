module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackTransitionCocycle

/-!
# The functor of Stacks 06WT and its full faithfulness

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces and `𝒳 = [U/R]` its quotient stack.
The forward functor of Stacks 06WT sends a quasi-coherent `𝒪_𝒳`-module `ℱ` to the quasi-coherent
module `(𝒢, α)` on `G` (Stacks 0441) with `𝒢 = x^*ℱ|_{U_étale}` and `α` the transition morphism
`AlgebraicGeometry.Stack.quotientStackTransition` (the comparison maps of equation 076R of the two
triangles of Stacks 044S); the cocycle and unit conditions are
`AlgebraicGeometry.Stack.groupoidPullbackTransition_quotientStackTransition_comp` (from Stacks
044T) and
`AlgebraicGeometry.Stack.groupoidPullbackTransition_quotientStackTransition_identityArrow`.

The functor is fully faithful: a morphism of `𝒪_𝒳`-modules out of a quasi-coherent module is
determined by its restriction to `U`, and a morphism `φ` on `U` comes from one on `𝒳` as soon as
it is compatible with the comparison maps over `R` (Stacks 076S); compatibility with `α` is that
condition.

## Main definitions

* `AlgebraicGeometry.Stack.quotientStackToGroupoid`: the functor
  `QCoh(𝒪_{[U/R]}) ⥤ QCoh(U, R, s, t, c)`.

## Main results

* `AlgebraicGeometry.Stack.fullyFaithfulQuotientStackToGroupoid`: it is fully faithful.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 076S](https://stacks.math.columbia.edu/tag/076S)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- The quasi-coherent module `(x^*ℱ|_{U_étale}, α)` on `G` attached to a quasi-coherent module
`ℱ` on `[U/R]`. -/
noncomputable def quotientStackToGroupoidObj
    (F : FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G)) :
    Space.QuasicoherentModule C S hS G where
  F := ⟨_, isQuasicoherentOnSite_quotientStackObjectRestriction G F.obj F.property⟩
  alpha := quotientStackTransition G F.obj F.property
  cocycle := groupoidPullbackTransition_quotientStackTransition_comp G F.obj F.property
  unit := groupoidPullbackTransition_quotientStackTransition_identityArrow G F.obj F.property

/-- **The forward functor of Stacks 06WT**: `ℱ ↦ (x^*ℱ|_{U_étale}, α)`, on morphisms
`ψ ↦ x^*ψ|_{U_étale}`. -/
noncomputable def quotientStackToGroupoid :
    FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G) ⥤ Space.QuasicoherentModule C S hS G where
  obj F := quotientStackToGroupoidObj G F
  map {F H} ψ :=
    { hom := quotientStackObjectRestrictionMap G ψ.hom
      comm := quotientStackTransition_naturality G F.property H.property ψ.hom }
  map_id F := by
    refine Space.QuasicoherentModule.Hom.ext ?_
    change Space.etaleRestrictedModuleInverseImageMap C S hS _ _ _ _ _ _ _
      ((quotientStackToEtale G).map (𝟙 F.obj)) = 𝟙 _
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ?_)
    rfl
  map_comp ψ ψ' := by
    refine Space.QuasicoherentModule.Hom.ext ?_
    change Space.etaleRestrictedModuleInverseImageMap C S hS _ _ _ _ _ _ _
      ((quotientStackToEtale G).map (ψ.hom ≫ ψ'.hom)) = _
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ?_)
    rfl

variable {G}

/-- **Faithfulness**: a morphism of quasi-coherent modules on `[U/R]` is determined by its
image (Stacks 076S, injectivity). -/
theorem quotientStackToGroupoid_map_injective
    {F H : FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G)} {ψ₁ ψ₂ : F ⟶ H}
    (h : (quotientStackToGroupoid G).map ψ₁ = (quotientStackToGroupoid G).map ψ₂) : ψ₁ = ψ₂ :=
  ObjectProperty.hom_ext _
    (quotientStackObjectRestrictionMap_injective F.property
      (congrArg Space.QuasicoherentModule.Hom.hom h))

/-- The morphism `χ := c_s(ℱ)⁻¹ ≫ s^*φ ≫ c_s(ℋ)` over `R` attached to a morphism `φ` of the
images: it makes the square through the source commute by construction, and the square through
the target commute because `φ` commutes with the transition morphisms. -/
theorem quotientStackToGroupoid_squares
    {F H : FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G)}
    (f : (quotientStackToGroupoid G).obj F ⟶ (quotientStackToGroupoid G).obj H) :
    haveI := isIso_quotientStackSourceComparison G F.obj F.property
    quotientStackSourceComparison G F.obj ≫ (inv (quotientStackSourceComparison G F.obj) ≫
        (Space.modulePullback C S hS G.source).map f.hom ≫
          quotientStackSourceComparison G H.obj) =
        (Space.modulePullback C S hS G.source).map f.hom ≫
          quotientStackSourceComparison G H.obj ∧
      quotientStackTargetComparison G F.obj ≫ (inv (quotientStackSourceComparison G F.obj) ≫
        (Space.modulePullback C S hS G.source).map f.hom ≫
          quotientStackSourceComparison G H.obj) =
        (Space.modulePullback C S hS G.target).map f.hom ≫
          quotientStackTargetComparison G H.obj := by
  have := isIso_quotientStackSourceComparison G F.obj F.property
  refine ⟨IsIso.hom_inv_id_assoc _ _, ?_⟩
  have hc := f.comm
  have e := quotientStackTransition_comp_sourceComparison G H.obj H.property
  change quotientStackTransition G F.obj F.property ≫ _ = _ ≫ quotientStackTransition G H.obj
    H.property at hc
  refine (Category.assoc _ _ _).symm.trans ?_
  show quotientStackTransition G F.obj F.property ≫
      ((Space.modulePullback C S hS G.source).map f.hom ≫ quotientStackSourceComparison G H.obj) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ quotientStackSourceComparison G H.obj) hc).trans
      ((Category.assoc _ _ _).trans (congrArg _ e)))

/-- **Fullness**: every morphism of the images comes from a morphism of quasi-coherent modules
on `[U/R]` (Stacks 076S, the description of the image). -/
noncomputable def quotientStackToGroupoidPreimage
    {F H : FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G)}
    (f : (quotientStackToGroupoid G).obj F ⟶ (quotientStackToGroupoid G).obj H) : F ⟶ H :=
  ObjectProperty.homMk (chartedGluedHom f.hom _ F.property
    (quotientStackToGroupoid_squares f).1 (quotientStackToGroupoid_squares f).2)

/-- The preimage of a morphism of the images is mapped back to it. -/
theorem quotientStackToGroupoid_map_preimage
    {F H : FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G)}
    (f : (quotientStackToGroupoid G).obj F ⟶ (quotientStackToGroupoid G).obj H) :
    (quotientStackToGroupoid G).map (quotientStackToGroupoidPreimage f) = f :=
  Space.QuasicoherentModule.Hom.ext
    (quotientStackObjectRestrictionMap_chartedGluedHom f.hom _ F.property
      (quotientStackToGroupoid_squares f).1 (quotientStackToGroupoid_squares f).2)

variable (G) in
/-- **The forward functor of Stacks 06WT is fully faithful.** -/
noncomputable def fullyFaithfulQuotientStackToGroupoid :
    (quotientStackToGroupoid G).FullyFaithful where
  preimage := quotientStackToGroupoidPreimage
  map_preimage := quotientStackToGroupoid_map_preimage
  preimage_map ψ := quotientStackToGroupoid_map_injective
    (quotientStackToGroupoid_map_preimage ((quotientStackToGroupoid G).map ψ))

end AlgebraicGeometry.Stack

end
