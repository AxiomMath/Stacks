module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexShortExact

/-!
# `ℱ ↦ 𝒢^• ⊗ f^*ℱ` and the boundary maps of short exact sequences

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `𝒢^•` a complex of `𝒪_X`-modules flat over
`Y`.  The comparison `𝒢^• ⊗^L Lf^*(-) ⟶ 𝒢^• ⊗ f^*(-)` carries the boundary map of the image under
`𝒢^• ⊗^L Lf^*(-)` of the triangle of a short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of
`𝒪_Y`-modules to the boundary map of the triangle of the short exact sequence of complexes
`0 → 𝒢^• ⊗ f^*ℱ₁ → 𝒢^• ⊗ f^*ℱ₂ → 𝒢^• ⊗ f^*ℱ₃ → 0` (the compatibility with boundary maps in the
proof of Stacks 0A1M).

## Main results

* `AlgebraicGeometry.Space.tensorPullbackComplexNatTrans_triangleOfSESδ`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleRingedTopos

variable (f : X ⟶ Y)
  (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)

/-- `𝒢^• ⊗ f^*(-)`, written as the composite of the degreewise pullback and `Tot(𝒢^• ⊗ -)`. -/
abbrev tensorPullbackComplexComp : CochainComplex (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS Y)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ :=
  (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
      (ComplexShape.up ℤ)) ⋙ Stacks.SheafOfModules.Tensor.Reduction.bifunctorTotLeft
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS X).O) G)

/-- The functor `𝒢^• ⊗ f^*(-)`, in its composite form, is additive. -/
instance tensorPullbackComplexComp_additive : (tensorPullbackComplexComp f G).Additive := by
  have := Stacks.SheafOfModules.Tensor.Reduction.map₂HomologicalComplex_obj_additive
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS X).O) G
  infer_instance

/-- The comparison `𝒢^• ⊗^L Lf^*(-) ⟶ 𝒢^• ⊗ f^*(-)` commutes with the shifts, read with the
composite form of `𝒢^• ⊗ f^*(-)`. -/
instance tensorPullbackComplexNatTrans_commShift_comp :
    NatTrans.CommShift (F₂ := tensorPullbackComplexComp f G ⋙ DerivedCategory.Q)
      (tensorPullbackComplexNatTrans f G) ℤ :=
  (inferInstance : NatTrans.CommShift (tensorPullbackComplexNatTrans f G) ℤ)

variable {f G} in
/-- If every term of `𝒢^•` is flat over `Y`, then for a short exact sequence
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of `𝒪_Y`-modules, the sequence of complexes
`0 → 𝒢^• ⊗ f^*ℱ₁ → 𝒢^• ⊗ f^*ℱ₂ → 𝒢^• ⊗ f^*ℱ₃ → 0`, with `𝒢^• ⊗ f^*(-)` in its composite form, is
short exact. -/
theorem shortExact_tensorPullbackComplexComp_map_single
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    {T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hT : T.ShortExact) :
    ((T.map (HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0)).map (tensorPullbackComplexComp f G)).ShortExact :=
  shortExact_tensorPullbackComplex_map_single hG hT

variable {f G} in
/-- The comparison `𝒢^• ⊗^L Lf^*(-) ⟶ 𝒢^• ⊗ f^*(-)` carries the boundary map of the image of the
triangle of a short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of `𝒪_Y`-modules to the boundary map of
the triangle of the short exact sequence of complexes
`0 → 𝒢^• ⊗ f^*ℱ₁ → 𝒢^• ⊗ f^*ℱ₂ → 𝒢^• ⊗ f^*ℱ₃ → 0`, with `𝒢^• ⊗ f^*(-)` in its composite form. -/
theorem tensorPullbackComplexNatTrans_triangleOfSESδ_comp
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    {T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hT : T.ShortExact) :
    (smallEtaleDerivedModulePullback B S hS f ⋙
      (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)).map
        (DerivedCategory.triangleOfSESδ (hT.map_of_exact (HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0))) ≫
      ((smallEtaleDerivedModulePullback B S hS f ⋙
      (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)).commShiftIso
        (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj ((HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj T.X₁)) ≫
      ((tensorPullbackComplexNatTrans f G).app ((HomologicalComplex.single
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj T.X₁))⟦(1 : ℤ)⟧' =
    (tensorPullbackComplexNatTrans f G).app ((HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj T.X₃) ≫
      DerivedCategory.triangleOfSESδ (shortExact_tensorPullbackComplexComp_map_single hG hT) :=
  Stacks.SheafOfModules.Tensor.Reduction.compBifunctor_map_triangleOfSESδ_comp_natTrans
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS X).O) G
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules
    (smallEtaleDerivedModulePullback B S hS f ⋙
      (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G))
    (tensorPullbackComplexNatTrans f G) (hT.map_of_exact (HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0))
    (shortExact_tensorPullbackComplexComp_map_single hG hT)

variable {f G} in
/-- **The boundary maps** (Stacks 0A1M, proof): the comparison
`𝒢^• ⊗^L Lf^*(-) ⟶ 𝒢^• ⊗ f^*(-)` carries the boundary map of the image of the triangle of a short
exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of `𝒪_Y`-modules to the boundary map of the triangle of the
short exact sequence of complexes `0 → 𝒢^• ⊗ f^*ℱ₁ → 𝒢^• ⊗ f^*ℱ₂ → 𝒢^• ⊗ f^*ℱ₃ → 0`. -/
theorem tensorPullbackComplexNatTrans_triangleOfSESδ
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    {T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hT : T.ShortExact) :
    (smallEtaleDerivedModulePullback B S hS f ⋙
      (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)).map
        (DerivedCategory.triangleOfSESδ (hT.map_of_exact (HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0))) ≫
      ((smallEtaleDerivedModulePullback B S hS f ⋙
      (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)).commShiftIso
        (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj ((HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj T.X₁)) ≫
      ((tensorPullbackComplexNatTrans f G).app ((HomologicalComplex.single
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj T.X₁))⟦(1 : ℤ)⟧' =
    (tensorPullbackComplexNatTrans f G).app ((HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj T.X₃) ≫
      DerivedCategory.triangleOfSESδ (shortExact_tensorPullbackComplex_map_single hG hT) :=
  tensorPullbackComplexNatTrans_triangleOfSESδ_comp hG hT

end AlgebraicGeometry.Space

end
