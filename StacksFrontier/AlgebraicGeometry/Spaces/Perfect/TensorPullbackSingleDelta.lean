module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDualTowerData

/-!
# The boundary of `𝒢^• ⊗ f^*(-)` on a short exact sequence of modules

For `f : X ⟶ Y` and a complex `𝒢^•` as in Stacks 08JR, a short exact sequence
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of `𝒪_Y`-modules gives a short exact sequence of complexes
`0 → 𝒢^• ⊗ f^*ℱ₁ → 𝒢^• ⊗ f^*ℱ₂ → 𝒢^• ⊗ f^*ℱ₃ → 0`, hence a boundary morphism
`𝒢^• ⊗ f^*ℱ₃ ⟶ (𝒢^• ⊗ f^*ℱ₁)[1]` in `D(𝒪_X)`. This file names it: it is the boundary map of
part (B) of Stacks 08JR, whose statement
(`AlgebraicGeometry.Space.exists_isPseudoCoherent_extAddEquiv_tensorPullbackComplex`) spells out
the same term.

## Main definitions

* `AlgebraicGeometry.Space.tensorPullbackSingleDelta`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **The boundary `𝒢^• ⊗ f^*ℱ₃ ⟶ (𝒢^• ⊗ f^*ℱ₁)[1]`** of a short exact sequence
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of `𝒪_Y`-modules, for `𝒢^•` as in Stacks 08JR. -/
def tensorPullbackSingleDelta (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hG : FlatProperSupportComplex B S hS f hf G) (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2))
    (hT : T.ShortExact) :=
  DerivedCategory.triangleOfSESδ (S := (ShortComplex.mk ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.f)
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).map T.g) (single_map_comp_map_eq_zero B S hS T)).map
      (tensorPullbackComplex f G))
    (shortExact_tensorPullbackComplex_map_single
      (FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG) hT)

end AlgebraicGeometry.Space

end
