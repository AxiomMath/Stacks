module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDirectImage

/-!
# The groups `H^i(Y, K ⊗^L ℱ)` and their boundary maps

For an object `K` of `D(𝒪_Y)` (the small étale site of an algebraic space `Y`) and an
`𝒪_Y`-module `ℱ`, the group `H^i(Y, K ⊗^L ℱ)` is the `i`-th cohomology of derived global
sections of `K ⊗^L ℱ[0]`.  This file names it, its functoriality in `ℱ` and the boundary maps of
short exact sequences `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0`, for an arbitrary `K`; at
`K = Rf_* RSheafHom(E, 𝒢^•)` these are `AlgebraicGeometry.Space.extPerfectBaseCohomology` and
`AlgebraicGeometry.Space.extPerfectBaseDelta` of Stacks 08JN.  It also names the boundary maps of
`Ext^i(E, 𝒢^• ⊗ f^*ℱ)` in the spelling of `AlgebraicGeometry.Space.extPerfectExtGroup`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleTensorCohomology`: `H^i(Y, K ⊗^L ℱ)`.
* `AlgebraicGeometry.Space.smallEtaleTensorCohomologyMap`: its functoriality in `ℱ`.
* `AlgebraicGeometry.Space.smallEtaleTensorCohomologyDelta`: its boundary maps.
* `AlgebraicGeometry.Space.extPerfectExtGroupDelta`: the boundary maps of `Ext^i(E, 𝒢^• ⊗ f^*ℱ)`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology
attribute [local instance 20000] ModuleCat.hasDerivedCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **The group `H^i(Y, K ⊗^L ℱ)`**: the `i`-th cohomology of the derived global sections of
`K ⊗^L ℱ[0]`, read in abelian groups. -/
abbrev smallEtaleTensorCohomology
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (i : ℤ) :
    AddCommGrpCat.{u + 1} :=
  (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
      AddCommGrpCat.{u + 1}).obj (((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) 0).shift i).obj
      ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).obj
        (((smallEtaleDerivedTensor B S hS Y).obj K).obj (extPerfectSingle B S hS F))))

/-- **The map `H^i(Y, K ⊗^L ℱ) ⟶ H^i(Y, K ⊗^L ℱ')` induced by `ℱ ⟶ ℱ'`.** -/
abbrev smallEtaleTensorCohomologyMap
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    {F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (q : F ⟶ F') (i : ℤ) :
    smallEtaleTensorCohomology B S hS K F i ⟶ smallEtaleTensorCohomology B S hS K F' i :=
  (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
    AddCommGrpCat.{u + 1}).map (((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) 0).shift i).map
    ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).map
      (((smallEtaleDerivedTensor B S hS Y).obj K).map (extPerfectSingleMap B S hS q))))

/-- **The boundary map `H^i(Y, K ⊗^L ℱ₃) ⟶ H^{i+1}(Y, K ⊗^L ℱ₁)`** of a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of `𝒪_Y`-modules: the connecting morphism of the cohomology of the
derived global sections of `K ⊗^L` the distinguished triangle of `ℱ₁[0] ⟶ ℱ₂[0] ⟶ ℱ₃[0]`. -/
abbrev smallEtaleTensorCohomologyDelta
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hT : T.ShortExact) (i j : ℤ) (h : i + 1 = j) :
    smallEtaleTensorCohomology B S hS K T.X₃ i ⟶ smallEtaleTensorCohomology B S hS K T.X₁ j :=
  (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
    AddCommGrpCat.{u + 1}).map ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) 0).homologySequenceδ
    ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).mapTriangle.obj
      (((smallEtaleDerivedTensor B S hS Y).obj K).mapTriangle.obj
        (DerivedCategory.triangleOfSES (hT.map_of_exact (HomologicalComplex.single
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ)
            0))))) i j h)

/-- The boundary map `Ext^i(E, 𝒢^• ⊗ f^*ℱ₃) ⟶ Ext^{i+1}(E, 𝒢^• ⊗ f^*ℱ₁)` of a short exact
sequence `0 ⟶ 𝒢^• ⊗ f^*ℱ₁ ⟶ 𝒢^• ⊗ f^*ℱ₂ ⟶ 𝒢^• ⊗ f^*ℱ₃ ⟶ 0` of complexes, in the spelling of
`AlgebraicGeometry.Space.extPerfectExtGroup`. -/
abbrev extPerfectExtGroupDelta (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hT : ((T.map (HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
          (tensorPullbackComplex f G)).ShortExact)
    (i j : ℤ) (h : i + 1 = j) :
    extPerfectExtGroup B S hS f E G T.X₃ i ⟶ extPerfectExtGroup B S hS f E G T.X₁ j :=
  (preadditiveCoyoneda.obj (op E)).map ((DerivedCategory.triangleOfSESδ hT)⟦i⟧' ≫
    (shiftFunctorAdd' _ 1 i j (by omega)).inv.app (extPerfectCoefficientObj B S hS f G T.X₁))

/-- `AlgebraicGeometry.Space.extPerfectBaseDelta` is
`AlgebraicGeometry.Space.smallEtaleTensorCohomologyDelta` at `K = Rf_* RSheafHom(E, 𝒢^•)`. -/
theorem extPerfectBaseDelta_eq_smallEtaleTensorCohomologyDelta (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hT : T.ShortExact) (i j : ℤ) (h : i + 1 = j) :
    extPerfectBaseDelta B S hS f E G T hT i j h =
      smallEtaleTensorCohomologyDelta B S hS (extPerfectDirectImageObj B S hS f E G) T hT i j h :=
  rfl

end AlgebraicGeometry.Space

end
