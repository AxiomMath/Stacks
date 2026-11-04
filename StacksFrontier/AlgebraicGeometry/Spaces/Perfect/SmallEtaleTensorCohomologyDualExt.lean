module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDualExtAddEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleTensorCohomology

/-!
# `H^i(Y, K ⊗^L ℱ) = Ext^i(K^∨, ℱ)` for a perfect `K`, with the boundary maps

Let `Y` be an algebraic space, `K` a perfect object of `D(𝒪_Y)` with dual `K^∨`, and `ℱ` an
`𝒪_Y`-module. Then

`H^i(Y, K ⊗^L ℱ) ≅ Hom(𝒪_Y, (K ⊗^L ℱ)[i]) ≅ Hom(K^∨, ℱ[i]) = Ext^i(K^∨, ℱ)`,

naturally in `ℱ`, and the boundary map `H^i(Y, K ⊗^L ℱ₃) ⟶ H^{i+1}(Y, K ⊗^L ℱ₁)` of a short exact
sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` corresponds to composition with its boundary morphism
`ℱ₃[0] ⟶ ℱ₁[0][1]`, shifted by `i`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleTensorCohomologyDualExtAddEquiv`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleTensorCohomologyDualExtAddEquiv_naturality`: naturality in
  `ℱ`.
* `AlgebraicGeometry.Space.smallEtaleTensorCohomologyDualExtAddEquiv_delta`: the boundary maps.

## Implementation notes

The first identification is `AlgebraicGeometry.Space.cohomologyIsoUnitHomShift` (global sections
are corepresented by `𝒪_Y`), the second `AlgebraicGeometry.Space.smallEtaleDualExtAddEquiv`
(Stacks 08J8, 08JJ). Both are natural in the argument and carry boundary maps to composition with
the shifted third morphism of a triangle, so their composite does.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
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
-- One standard-model line, scoped to this file: the base declarations
-- `AlgebraicGeometry.Space.smallEtaleTensorCohomology` and
-- `AlgebraicGeometry.Space.smallEtaleDualExtAddEquiv` are stated in the model
-- `HasDerivedCategory.standard`.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology
attribute [local instance 20000] ModuleCat.hasDerivedCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {Y : AlgebraicSpaces B S hS}

/-- **`H^i(Y, K ⊗^L ℱ) ≃+ Ext^i(K^∨, ℱ)` for a perfect `K`**: the cohomology of `RΓ(Y, -)` is
corepresented by `𝒪_Y` (`AlgebraicGeometry.Space.cohomologyIsoUnitHomShift`), and
`Hom(𝒪_Y, (K ⊗^L ℱ)[i]) ≅ Hom(K^∨, ℱ[i])` (`AlgebraicGeometry.Space.smallEtaleDualExtAddEquiv`). -/
def smallEtaleTensorCohomologyDualExtAddEquiv
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (i : ℤ) :
    smallEtaleTensorCohomology B S hS K F i ≃+
      (smallEtaleDerivedDual B S hS Y K ⟶
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0).obj F)⟦i⟧) :=
  AddEquiv.ulift.symm.trans
    ((((cohomologyIsoUnitHomShift Y i).app
        (((smallEtaleDerivedTensor B S hS Y).obj K).obj
          (extPerfectSingle B S hS F))).addCommGroupIsoToAddEquiv).trans
      (AddEquiv.ulift.trans (smallEtaleDualExtAddEquiv B S hS Y K hK
        (extPerfectSingle B S hS F) i).symm))

/-- `AlgebraicGeometry.Space.smallEtaleTensorCohomologyDualExtAddEquiv` sends `y` to the inverse
image under `AlgebraicGeometry.Space.smallEtaleDualExtAddEquiv` of the morphism
`𝒪_Y ⟶ (K ⊗^L ℱ)[i]` corresponding to `y` under
`AlgebraicGeometry.Space.cohomologyIsoUnitHomShift`. -/
theorem smallEtaleTensorCohomologyDualExtAddEquiv_apply
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (i : ℤ)
    (y : smallEtaleTensorCohomology B S hS K F i) :
    smallEtaleTensorCohomologyDualExtAddEquiv B S hS K hK F i y =
      (smallEtaleDualExtAddEquiv B S hS Y K hK (extPerfectSingle B S hS F) i).symm
        (ULift.down (((cohomologyIsoUnitHomShift Y i).hom.app
          (((smallEtaleDerivedTensor B S hS Y).obj K).obj (extPerfectSingle B S hS F))) ⟨y⟩)) :=
  rfl

/-- **`AlgebraicGeometry.Space.smallEtaleTensorCohomologyDualExtAddEquiv` is natural in `ℱ`.** -/
theorem smallEtaleTensorCohomologyDualExtAddEquiv_naturality
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K)
    {F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (q : F ⟶ F') (i : ℤ)
    (y : smallEtaleTensorCohomology B S hS K F i) :
    smallEtaleTensorCohomologyDualExtAddEquiv B S hS K hK F' i
        (smallEtaleTensorCohomologyMap B S hS K q i y) =
      smallEtaleTensorCohomologyDualExtAddEquiv B S hS K hK F i y ≫
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0).map q)⟦i⟧' := by
  have hc := ConcreteCategory.congr_hom ((cohomologyIsoUnitHomShift Y i).hom.naturality
    (((smallEtaleDerivedTensor B S hS Y).obj K).map (extPerfectSingleMap B S hS q))) ⟨y⟩
  have hc' : ULift.down (((cohomologyIsoUnitHomShift Y i).hom.app
        (((smallEtaleDerivedTensor B S hS Y).obj K).obj (extPerfectSingle B S hS F'))) ⟨
          smallEtaleTensorCohomologyMap B S hS K q i y⟩) =
      (ULift.down (((cohomologyIsoUnitHomShift Y i).hom.app
          (((smallEtaleDerivedTensor B S hS Y).obj K).obj (extPerfectSingle B S hS F))) ⟨y⟩) :
          structureDerived Y ⟶ (((smallEtaleDerivedTensor B S hS Y).obj K).obj
            (extPerfectSingle B S hS F))⟦i⟧) ≫
        (((smallEtaleDerivedTensor B S hS Y).obj K).map (extPerfectSingleMap B S hS q))⟦i⟧' :=
    congrArg ULift.down hc
  have h2 : smallEtaleDualExtAddEquiv B S hS Y K hK (extPerfectSingle B S hS F) i
      (smallEtaleTensorCohomologyDualExtAddEquiv B S hS K hK F i y) =
        ULift.down (((cohomologyIsoUnitHomShift Y i).hom.app
          (((smallEtaleDerivedTensor B S hS Y).obj K).obj (extPerfectSingle B S hS F))) ⟨y⟩) :=
    AddEquiv.apply_symm_apply _ _
  have hn := smallEtaleDualExtAddEquiv_naturality B S hS Y K hK (extPerfectSingleMap B S hS q) i
    (smallEtaleTensorCohomologyDualExtAddEquiv B S hS K hK F i y)
  rw [h2] at hn
  rw [smallEtaleTensorCohomologyDualExtAddEquiv_apply B S hS K hK F', hc',
    AddEquiv.symm_apply_eq]
  exact hn.symm

/-- **`AlgebraicGeometry.Space.smallEtaleTensorCohomologyDualExtAddEquiv` is compatible with the
boundary maps**: the boundary map `H^1(Y, K ⊗^L ℱ₃) ⟶ H^2(Y, K ⊗^L ℱ₁)` of a short exact sequence
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` is composition with its boundary morphism `ℱ₃[0] ⟶ ℱ₁[0][1]`, shifted by
one. -/
theorem smallEtaleTensorCohomologyDualExtAddEquiv_delta
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K)
    {T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hT : T.ShortExact) (y : smallEtaleTensorCohomology B S hS K T.X₃ 1) :
    smallEtaleTensorCohomologyDualExtAddEquiv B S hS K hK T.X₁ 2
        (smallEtaleTensorCohomologyDelta B S hS K T hT 1 2 rfl y) =
      smallEtaleTensorCohomologyDualExtAddEquiv B S hS K hK T.X₃ 1 y ≫
        hT.singleδ⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y))) 1 1 2 (by norm_num)).inv.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0).obj T.X₁) := by
  have hδ := ConcreteCategory.congr_hom (cohomologyIsoUnitHomShift_homologySequenceδ Y
    (((smallEtaleDerivedTensor B S hS Y).obj K).mapTriangle.obj
      (DerivedCategory.triangleOfSES (hT.map_of_exact (HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0))))
    1 2 rfl) ⟨y⟩
  have hδ' : ULift.down (((cohomologyIsoUnitHomShift Y 2).hom.app
        (((smallEtaleDerivedTensor B S hS Y).obj K).obj (extPerfectSingle B S hS T.X₁))) ⟨
          smallEtaleTensorCohomologyDelta B S hS K T hT 1 2 rfl y⟩) =
      (ULift.down (((cohomologyIsoUnitHomShift Y 1).hom.app
          (((smallEtaleDerivedTensor B S hS Y).obj K).obj (extPerfectSingle B S hS T.X₃))) ⟨y⟩) :
          structureDerived Y ⟶ (((smallEtaleDerivedTensor B S hS Y).obj K).obj
            (extPerfectSingle B S hS T.X₃))⟦(1 : ℤ)⟧) ≫
        (((smallEtaleDerivedTensor B S hS Y).obj K).map hT.singleδ ≫
          (((smallEtaleDerivedTensor B S hS Y).obj K).commShiftIso (1 : ℤ)).hom.app
            (extPerfectSingle B S hS T.X₁))⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y))) 1 1 2 (by norm_num)).inv.app
            (((smallEtaleDerivedTensor B S hS Y).obj K).obj (extPerfectSingle B S hS T.X₁)) :=
    congrArg ULift.down hδ
  have h2 : smallEtaleDualExtAddEquiv B S hS Y K hK (extPerfectSingle B S hS T.X₃) 1
      (smallEtaleTensorCohomologyDualExtAddEquiv B S hS K hK T.X₃ 1 y) =
        ULift.down (((cohomologyIsoUnitHomShift Y 1).hom.app
          (((smallEtaleDerivedTensor B S hS Y).obj K).obj (extPerfectSingle B S hS T.X₃))) ⟨y⟩) :=
    AddEquiv.apply_symm_apply _ _
  have hs := smallEtaleDualExtAddEquiv_shift B S hS Y K hK (M := extPerfectSingle B S hS T.X₃)
    (N := extPerfectSingle B S hS T.X₁) hT.singleδ 1 2 (by norm_num)
    (smallEtaleTensorCohomologyDualExtAddEquiv B S hS K hK T.X₃ 1 y)
  rw [h2] at hs
  rw [smallEtaleTensorCohomologyDualExtAddEquiv_apply B S hS K hK T.X₁, hδ',
    AddEquiv.symm_apply_eq]
  exact hs.symm

/-- **`H^i(Y, K ⊗^L ℱ) ≃+ Ext^i(K^∨, ℱ)` for a perfect `K`, naturally in `ℱ` and compatibly with
the boundary maps**, as an existence statement:
`AlgebraicGeometry.Space.smallEtaleTensorCohomologyDualExtAddEquiv` with its naturality and its
compatibility with the boundary maps. -/
theorem exists_smallEtaleTensorCohomology_addEquiv_dualExt
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K) :
    ∃ E : ∀ (F : (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (i : ℤ),
        smallEtaleTensorCohomology B S hS K F i ≃+
          (smallEtaleDerivedDual B S hS Y K ⟶
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0).obj F)⟦i⟧),
      (∀ {F F' : (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))} (q : F ⟶ F') (i : ℤ)
          (y : smallEtaleTensorCohomology B S hS K F i),
        E F' i (smallEtaleTensorCohomologyMap B S hS K q i y) =
          E F i y ≫ ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0).map q)⟦i⟧') ∧
      (∀ {T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
          (hT : T.ShortExact) (y : smallEtaleTensorCohomology B S hS K T.X₃ 1),
        E T.X₁ 2 (smallEtaleTensorCohomologyDelta B S hS K T hT 1 2 rfl y) =
          E T.X₃ 1 y ≫ hT.singleδ⟦(1 : ℤ)⟧' ≫
            (shiftFunctorAdd' (DerivedCategory (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS Y))) 1 1 2 (by norm_num)).inv.app
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0).obj T.X₁)) :=
  ⟨smallEtaleTensorCohomologyDualExtAddEquiv B S hS K hK,
    fun q i y => smallEtaleTensorCohomologyDualExtAddEquiv_naturality B S hS K hK q i y,
    fun hT y => smallEtaleTensorCohomologyDualExtAddEquiv_delta B S hS K hK hT y⟩

end AlgebraicGeometry.Space

end
