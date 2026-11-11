module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceEtaleSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.BaseObjectAtAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GlobalDerivedHomBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperFlatSingleDegreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceComp
public import StacksFrontier.Homology.DerivedCategory.MapDerivedCategoryIsZero
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Braiding
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategoryPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated

/-!
# The comparison map of Stacks 0DIP and its reduction to a vanishing

In Situation [Stacks, Tag 0DIK] let `j : U ⟶ X` be étale and `Uₙ = Xₙ ×_X U`, with projections
`pₙ : Xₙ ⟶ X`, `jₙ : Uₙ ⟶ Xₙ` and `qₙ : Uₙ ⟶ U`. Write `RΓ_A(V, -)` and `RΓ_{Aₙ}(V, -)` for
derived global sections of a space over `Spec A`, respectively over `Spec Aₙ`.

## Main definitions

* `…etaleSectionsBaseChangeMap`: **the canonical map `RΓ_A(U, K) ⊗^L_A Aₙ ⟶ RΓ_{Aₙ}(Uₙ, Kₙ)`
  of Stacks 0DIP**, the base change map of `RΓ` along `Spec Aₙ ⟶ Spec A` at `K|_U`, followed by
  `RΓ_{Aₙ}(Uₙ, -)` of the restriction to `Uₙ` of `τₙ : K|_{Xₙ} ⟶ Kₙ`.

## Main results

* `…torIndependent_etaleStage_base`, `…torIndependent_etaleStage`: `U` and `Spec Aₙ` are Tor
  independent over `Spec A`, and `Xₙ` and `U` over `X`, since `U` is flat over `X` and over `A`.
* `…isIso_affineBaseDerivedSectionsBaseChangeMap_etaleStage`: for `U` quasi-compact and
  quasi-separated, the base change map `RΓ_A(U, H) ⊗^L_A Aₙ ⟶ RΓ_{Aₙ}(Uₙ, H|_{Uₙ})` is invertible
  on `D_QCoh(𝒪_U)` (Stacks 08IR over the affine base).
* `…isZero_etaleStageSections_of_isZero`: for `C ∈ D_QCoh(𝒪_{Xₙ})`, if
  `RΓ_A(U, (Rpₙ,* C)|_U) = 0` then `RΓ_{Aₙ}(Uₙ, C|_{Uₙ}) = 0`, by flat base change (Stacks 08IR)
  for `Uₙ = Xₙ ×_X U` and the faithfulness of restriction of scalars along `A ⟶ Aₙ`.
* `…isZero_sections_tensor_stagePushforward_of_isZero`: for `E ∈ D_QCoh(𝒪_X)` and
  `C ∈ D_QCoh(𝒪_{Xₙ})`, if `RΓ_{Aₙ}(Xₙ, Lpₙ^*E ⊗^L C) = 0` then `RΓ_A(X, E ⊗^L Rpₙ,* C) = 0`, by
  the projection formula (Stacks 08IN) and `RΓ_A(X, Rpₙ,* -) = RΓ_{Aₙ}(Xₙ, -)` over `A`.
* `…isIso_etaleStageSections_map_coheratorLimitPullbackMap`: `RΓ_{Aₙ}(Uₙ, -)` of `τₙ|_{Uₙ}` is
  invertible as soon as `RΓ_A(U, (Rpₙ,* Cₙ)|_U) = 0` for the cone `Cₙ` of `τₙ`.
* `…isIso_etaleSectionsBaseChangeMap_of_forall`: the canonical map is invertible given the two
  inputs of the source's proof, [Stacks, Tag 0CRW] for `j` (vanishing of every
  `RΓ_A(X, E ⊗^L M)` with `E` perfect forces `RΓ_A(U, M|_U) = 0`) and [Stacks, Tag 0DIM] (every
  `RΓ_{Aₙ}(Xₙ, Lpₙ^*E ⊗^L τₙ)` with `E` perfect is invertible). Both inputs are proved in the
  library, downstream of this file (0DIM as
  `…isPseudoCoherent_and_isIso_stageTensorSectionsBaseChange`, the form used here as
  `…isIso_stageSections_map_tensor_coheratorLimitPullbackMap`), and the unconditional canonical
  map statement is `…isIso_etaleSectionsBaseChangeMap` ([Stacks, Tag 0DIP]).
* `…isIso_etaleSectionsBaseChangeMap_of_isZero`: the canonical map is invertible as soon as
  `RΓ_A(U, (Rpₙ,* Cₙ)|_U) = 0` for the cone `Cₙ` of `τₙ`.

## References

* [Stacks Project, Tag 0DIP](https://stacks.math.columbia.edu/tag/0DIP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

/-- The underlying scheme of the inverse-limit base `Spec A`, as an object over itself, is
affine. -/
instance isAffine_toScheme_limitBaseObject (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (B : BigFppfSite.{u})
    (hS : B.Contains (limitBase F)) :
    IsAffine ((BigFppfOver.toScheme B (limitBase F) hS).obj (limitBaseObject F B hS)) :=
  inferInstanceAs (IsAffine (limitBase F))

namespace SeparatedDerivedExistenceSystem

variable {D : SeparatedDerivedExistenceSystem.{u}}
  {U : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase} {j : U ⟶ D.X.left}

/-! ### Tor independence -/

/-- **`U` and `Spec Aₙ` are Tor independent over `Spec A`** for `j : U ⟶ X` étale: `U` is flat
over `A`. -/
theorem torIndependent_etaleStage_base
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom) (n : ℕ) :
    TorIndependent U.2 (schemeSpace (baseObjectAt D.system D.B D.containsLimitBase
        D.containsBaseAt n)).2
      (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 (j ≫ D.X.hom).hom
      (baseSpaceProjection D.system D.B D.containsLimitBase D.containsBaseAt n).hom :=
  torIndependent_of_isFlat_left _ _ (D.isFlat_structure_of_isEtale hj)

/-- **`Xₙ` and `U` are Tor independent over `X`** for `j : U ⟶ X` étale: `j` is flat. -/
theorem torIndependent_etaleStage
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom) (n : ℕ) :
    TorIndependent (D.stage n).2 U.2 D.X.left.2
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom j.hom :=
  (torIndependent_of_isFlat_left j _
    (isFlat_of_isEtale D.B (limitBase D.system) D.containsLimitBase hj)).symm

/-! ### The base change map of `RΓ` along `Spec Aₙ ⟶ Spec A` -/

variable (j) in
/-- The base change map `RΓ_A(U, H) ⊗^L_A Aₙ ⟶ RΓ_{Aₙ}(Uₙ, H|_{Uₙ})` of `RΓ` along
`Spec Aₙ ⟶ Spec A`, for the square `Uₙ = U ×_{Spec A} Spec Aₙ`. -/
abbrev etaleStageSectionsBaseChangeMap (n : ℕ)
    (H : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf D.B (limitBase D.system) D.containsLimitBase U))) :=
  affineBaseDerivedSectionsBaseChangeMap D.B (limitBase D.system) D.containsLimitBase
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) (j ≫ D.X.hom)
    (D.etaleStageBaseProjection j n) (D.etaleStageToSpace j n)
    (D.isPullback_etaleStage_base j n).w H

/-- **The base change map of `RΓ` along `Spec Aₙ ⟶ Spec A` is invertible on `D_QCoh(𝒪_U)`** for
`U` étale, quasi-compact and quasi-separated over `X`: `U ⟶ Spec A` is then quasi-compact and
quasi-separated, and `U` is Tor independent of `Spec Aₙ` over `Spec A` (Stacks 08IR). -/
theorem isIso_etaleStageSectionsBaseChangeMap
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B (limitBase D.system) D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B (limitBase D.system) D.containsLimitBase
      D.B.contains_terminal U.1) (n : ℕ)
    (H : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf D.B (limitBase D.system) D.containsLimitBase U)))
    (hH : QcohDerived D.B (limitBase D.system) D.containsLimitBase U H) :
    IsIso (D.etaleStageSectionsBaseChangeMap j n H) :=
  have hfp := D.isFinitePresentation_structure_of_isEtale hj hUqc hUqs
  isIso_affineBaseDerivedSectionsBaseChangeMap D.B (limitBase D.system) D.containsLimitBase
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) (j ≫ D.X.hom)
    (D.etaleStageBaseProjection j n) (D.etaleStageToSpace j n)
    (D.isPullback_etaleStage_base j n) hfp.2.1 hfp.2.2 (D.torIndependent_etaleStage_base hj n)
    H hH

/-! ### Vanishing on `Uₙ` from vanishing on `U` -/

/-- **`RΓ_{Aₙ}(Uₙ, C|_{Uₙ})` vanishes when `RΓ_A(U, (Rpₙ,* C)|_U)` does**, for
`C ∈ D_QCoh(𝒪_{Xₙ})`: by flat base change (Stacks 08IR) `(Rpₙ,* C)|_U = Rqₙ,*(C|_{Uₙ})`, so
`RΓ_A(U, (Rpₙ,* C)|_U)` is `RΓ_{Aₙ}(Uₙ, C|_{Uₙ})` with scalars restricted to `A`, and restriction
of scalars reflects zero objects. -/
theorem isZero_etaleStageSections_of_isZero
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom) (n : ℕ)
    (C : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf D.B (limitBase D.system) D.containsLimitBase (D.stage n))))
    (hC : QcohDerived D.B (limitBase D.system) D.containsLimitBase (D.stage n) C)
    (h : IsZero ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).obj
        ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (j ≫ D.X.hom)).obj
          ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase j).obj
            ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
              (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
                C))))) :
    IsZero ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).obj
        ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (D.etaleStageBaseProjection j n)).obj
          ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
            (D.etaleStageToStage j n)).obj C))) := by
  have hbc := isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent D.B (limitBase D.system)
    D.containsLimitBase
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) j
    (D.etaleStageToSpace j n) (D.etaleStageToStage j n) (D.isPullback_etaleStage j n)
    (D.isQuasiCompact_spaceProjection n) (D.isQuasiSeparated_spaceProjection n)
    (D.torIndependent_etaleStage hj n) C hC
  refine StacksDraft.DerivedCategoryHomology.isZero_of_isZero_mapDerivedCategory_obj
    (ModuleCat.restrictScalars (representedAffineCommRingCatHom D.B (limitBase D.system)
      D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom) ?_
  refine h.of_iso (((affineBaseDerivedSectionsPushforwardIso D.B (limitBase D.system)
      D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) (j ≫ D.X.hom)
      (D.etaleStageBaseProjection j n) (D.etaleStageToSpace j n)
      (D.isPullback_etaleStage_base j n).w).app _).symm ≪≫
    (derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase (j ≫ D.X.hom) ⋙
      representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
        (limitBaseObject D.system D.B D.containsLimitBase)).mapIso
      (asIso (smallEtaleDerivedModuleBaseChangeMap D.B (limitBase D.system) D.containsLimitBase
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) j
        (D.etaleStageToSpace j n) (D.etaleStageToStage j n)
        (D.isPullback_etaleStage j n).w C)).symm)

/-! ### Vanishing on `X` from vanishing on `Xₙ` -/

/-- **`RΓ_A(X, E ⊗^L Rpₙ,* C)` vanishes when `RΓ_{Aₙ}(Xₙ, Lpₙ^*E ⊗^L C)` does**, for
`E ∈ D_QCoh(𝒪_X)` and `C ∈ D_QCoh(𝒪_{Xₙ})`: by the projection formula (Stacks 08IN) for the
quasi-compact quasi-separated `pₙ`, `E ⊗^L Rpₙ,* C = Rpₙ,*(Lpₙ^*E ⊗^L C)`, and `RΓ_A(X, Rpₙ,* -)`
is `RΓ_{Aₙ}(Xₙ, -)` with scalars restricted to `A`. -/
theorem isZero_sections_tensor_stagePushforward_of_isZero (D : SeparatedDerivedExistenceSystem.{u})
    (n : ℕ) (E : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left)))
    (hE : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left E)
    (C : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf D.B (limitBase D.system) D.containsLimitBase (D.stage n))))
    (hC : QcohDerived D.B (limitBase D.system) D.containsLimitBase (D.stage n) C)
    (h : IsZero ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).obj
        ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
          (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase (D.stage n)).obj
            ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
              (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
                E)).obj C)))) :
    IsZero ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).obj
        ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase D.X.hom).obj
          (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase D.X.left).obj
            E).obj ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
              (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
                C)))) := by
  have hpf := isIso_smallEtaleProjectionFormulaMap D.B (limitBase D.system) D.containsLimitBase
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (D.isQuasiCompact_spaceProjection n) (D.isQuasiSeparated_spaceProjection n) C hC E hE
  have h' : IsZero ((ModuleCat.restrictScalars (representedAffineCommRingCatHom D.B
      (limitBase D.system) D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase
        D.containsBaseAt n)).hom).mapDerivedCategory.obj
        ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
          (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).obj
          ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
            (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
            (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
              (D.stage n)).obj C).obj
              ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
                (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
                  E))))) :=
    Functor.map_isZero _ (h.of_iso ((derivedModulePushforward D.B (limitBase D.system)
      D.containsLimitBase
      (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) ⋙
        representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
          (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).mapIso
      ((smallEtaleDerivedTensorProduct D.B (limitBase D.system) D.containsLimitBase
        (D.stage n)).braiding _ _)))
  refine h'.of_iso (((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
      D.X.hom ⋙
        representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
          (limitBaseObject D.system D.B D.containsLimitBase)).mapIso
      ((smallEtaleDerivedTensorProduct D.B (limitBase D.system) D.containsLimitBase
        D.X.left).braiding _ _ ≪≫
        @asIso _ _ _ _ (smallEtaleProjectionFormulaMap D.B (limitBase D.system)
          D.containsLimitBase
          (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) C E) hpf)) ≪≫
    (affineBaseDerivedSectionsPushforwardIso D.B (limitBase D.system) D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) D.X.hom
      (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).w.symm).app _)


/-! ### The canonical map of Stacks 0DIP -/

section Coherator

variable (D) (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).FullSubcategory)
  (adj : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)

variable (j) in
/-- `RΓ_{Aₙ}(Uₙ, -) : D(𝒪_{Uₙ}) ⥤ D(Aₙ)`. -/
abbrev etaleStageSections (n : ℕ) :=
  derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
      (D.etaleStageBaseProjection j n) ⋙
    representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)

variable (j) in
/-- The identification `qₙ^*(K|_U) ≅ jₙ^*(K|_{Xₙ})` of the two restrictions to `Uₙ`, around the
square `Uₙ = Xₙ ×_X U`. -/
def etaleStagePullbackIso (n : ℕ) :
    smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase j ⋙
        smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
          (D.etaleStageToSpace j n) ≅
      smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
          (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) ⋙
        smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
          (D.etaleStageToStage j n) :=
  smallEtaleDerivedModulePullbackSquareIso D.B (limitBase D.system) D.containsLimitBase j
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (D.etaleStageToStage j n) (D.etaleStageToSpace j n) (D.isPullback_etaleStage j n).w.symm ≪≫
    (smallEtaleDerivedModulePullbackCompIso D.B (limitBase D.system) D.containsLimitBase
      (D.etaleStageToStage j n)
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).symm

variable (j) in
/-- **The canonical map `RΓ_A(U, K) ⊗^L_A Aₙ ⟶ RΓ_{Aₙ}(Uₙ, Kₙ)` of Stacks 0DIP**: the base change
map of `RΓ` along `Spec Aₙ ⟶ Spec A` at `K|_U`, followed by `RΓ_{Aₙ}(Uₙ, -)` of the restriction
to `Uₙ` of `τₙ : K|_{Xₙ} ⟶ Kₙ`. Here `RΓ_{Aₙ}(Uₙ, Kₙ)` means `RΓ_{Aₙ}(Uₙ, Kₙ|_{Uₙ})`. -/
def etaleSectionsBaseChangeMap (n : ℕ) :
    (representedAffineDerivedExtension D.B (limitBase D.system) D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).functor.obj
      ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
        (limitBaseObject D.system D.B D.containsLimitBase)).obj
        ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (j ≫ D.X.hom)).obj
          ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase j).obj
            ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
              D.X.left).ι.obj (D.coheratorLimit DQ))))) ⟶
      (representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
        (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).obj
        ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (D.etaleStageBaseProjection j n)).obj
          ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
            (D.etaleStageToStage j n)).obj (D.K n))) :=
  D.etaleStageSectionsBaseChangeMap j n _ ≫
    (D.etaleStageSections j n).map ((D.etaleStagePullbackIso j n).hom.app _) ≫
    (smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
      (D.etaleStageToStage j n) ⋙ D.etaleStageSections j n).map
        (D.coheratorLimitPullbackMap DQ adj n)

/-- **`RΓ_{Aₙ}(Uₙ, -)` of `τₙ|_{Uₙ}` is invertible once `RΓ_A(U, (Rpₙ,* Cₙ)|_U) = 0`** for the
third vertex `Cₙ` of a distinguished triangle on `τₙ`. -/
theorem isIso_etaleStageSections_map_coheratorLimitPullbackMap
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom) (n : ℕ)
    {Z : derivedCategoryAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n}
    (g : D.K n ⟶ Z) (δ : Z ⟶ ((D.stageDerivedPullback n).obj
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
        (D.coheratorLimit DQ)))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (D.coheratorLimitPullbackMap DQ adj n) g δ ∈ distTriang _)
    (hZ : IsZero ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).obj
        ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (j ≫ D.X.hom)).obj
          ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase j).obj
            ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
              (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
                Z))))) :
    IsIso ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
      (D.etaleStageToStage j n) ⋙ D.etaleStageSections j n).map
        (D.coheratorLimitPullbackMap DQ adj n)) := by
  have hZq : QcohDerived D.B (limitBase D.system) D.containsLimitBase (D.stage n) Z :=
    D.isQuasicoherent_cone_coheratorLimitPullbackMap DQ n _ hT rfl rfl
  have hT₁ := (smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
    (D.etaleStageToStage j n)).map_distinguished _ hT
  have hT₂ := (derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
    (D.etaleStageBaseProjection j n)).map_distinguished _ hT₁
  have hz := isZero_etaleStageSections_of_isZero hj n Z hZq hZ
  have h := Functor.isIso_map_mor₁_of_isZero_map_obj₃
    (representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)) _ hT₂ hz
  exact h

/-- **The canonical map of Stacks 0DIP is invertible once a vanishing holds**: if, for a
distinguished triangle `K|_{Xₙ} ⟶ Kₙ ⟶ Cₙ ⟶` on `τₙ`, `RΓ_A(U, (Rpₙ,* Cₙ)|_U) = 0`, then
`RΓ_A(U, K) ⊗^L_A Aₙ ⟶ RΓ_{Aₙ}(Uₙ, Kₙ)` is an isomorphism. The base change map of `RΓ` is
invertible since `U` is flat over `A`, and `RΓ_{Aₙ}(Uₙ, -)` of `τₙ|_{Uₙ}` is invertible since
`RΓ_{Aₙ}(Uₙ, Cₙ|_{Uₙ}) = 0`. -/
theorem isIso_etaleSectionsBaseChangeMap_of_isZero
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B (limitBase D.system) D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B (limitBase D.system) D.containsLimitBase
      D.B.contains_terminal U.1) (n : ℕ)
    {Z : derivedCategoryAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n}
    (g : D.K n ⟶ Z) (δ : Z ⟶ ((D.stageDerivedPullback n).obj
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
        (D.coheratorLimit DQ)))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (D.coheratorLimitPullbackMap DQ adj n) g δ ∈ distTriang _)
    (hZ : IsZero ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).obj
        ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (j ≫ D.X.hom)).obj
          ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase j).obj
            ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
              (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
                Z))))) :
    IsIso (D.etaleSectionsBaseChangeMap j DQ adj n) := by
  have hK := (D.coheratorLimit DQ).property
  have h₁ := isIso_etaleStageSectionsBaseChangeMap hj hUqc hUqs n _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback D.B (limitBase D.system)
      D.containsLimitBase j _ hK)
  have h₂ := D.isIso_etaleStageSections_map_coheratorLimitPullbackMap DQ adj hj n g δ hT hZ
  exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso'
    (@Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_hom ((D.etaleStagePullbackIso j n).app _))) h₂)

/-- **The canonical map of Stacks 0DIP is invertible, given 0CRW and 0DIM.** Let `hCRW` be the
consequence of [Stacks, Tag 0CRW] for `j`: for `M ∈ D_QCoh(𝒪_X)`, if `RΓ_A(X, E ⊗^L M) = 0` for
every perfect `E` then `RΓ_A(U, M|_U) = 0`. Let `h0DIM` be [Stacks, Tag 0DIM]: for every perfect
`E` on `X`, `RΓ_{Aₙ}(Xₙ, Lpₙ^*E ⊗^L τₙ)` is invertible, stated with
`RΓ_{Aₙ}(Xₙ, -) = R(Xₙ ⟶ Spec Aₙ)_* ⋙ RΓ(Spec Aₙ, -)`. Then
`RΓ_A(U, K) ⊗^L_A Aₙ ⟶ RΓ_{Aₙ}(Uₙ, Kₙ)` is an isomorphism.

This is the source's proof. For the cone `Cₙ` of `τₙ`, `h0DIM` gives
`RΓ_{Aₙ}(Xₙ, Lpₙ^*E ⊗^L Cₙ) = 0`, hence `RΓ_A(X, E ⊗^L Rpₙ,* Cₙ) = 0` by the projection formula,
for every perfect `E`; so `RΓ_A(U, (Rpₙ,* Cₙ)|_U) = 0` by `hCRW`, and
`AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.isIso_etaleSectionsBaseChangeMap_of_isZero`
applies.

Both hypotheses are proved in the library, in files importing this one: `h0DIM` is
`isIso_stageSections_map_tensor_coheratorLimitPullbackMap` (part of [Stacks, Tag 0DIM],
`isPseudoCoherent_and_isIso_stageTensorSectionsBaseChange`), and `hCRW` is
`isZero_etaleSections_of_forall_isPerfect`; the unconditional form is
`isIso_etaleSectionsBaseChangeMap` ([Stacks, Tag 0DIP]); for `SeparatedDerivedExistenceSystem`
`h0DIM` holds given the pseudo-coherence of the `Mₙ`. -/
theorem isIso_etaleSectionsBaseChangeMap_of_forall
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B (limitBase D.system) D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B (limitBase D.system) D.containsLimitBase
      D.B.contains_terminal U.1) (n : ℕ)
    (hCRW : ∀ M : DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left)),
      QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left M →
      (∀ E : DerivedCategory (SheafOfModules.{u}
          (ringedToposStructureRingSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left)),
        (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
          D.X.left.2).IsPerfect E →
        IsZero ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
          (limitBaseObject D.system D.B D.containsLimitBase)).obj
            ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase D.X.hom).obj
              (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
                D.X.left).obj E).obj M)))) →
      IsZero ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
        (limitBaseObject D.system D.B D.containsLimitBase)).obj
          ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
            (j ≫ D.X.hom)).obj
            ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase j).obj
              M))))
    (h0DIM : ∀ E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left,
      spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E →
      IsIso ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) ⋙
        representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
          (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).map
        (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase (D.stage n)).obj
          ((D.stageDerivedPullback n).obj E)).map (D.coheratorLimitPullbackMap DQ adj n)))) :
    IsIso (D.etaleSectionsBaseChangeMap j DQ adj n) := by
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle (D.coheratorLimitPullbackMap DQ adj n)
  have hZq : QcohDerived D.B (limitBase D.system) D.containsLimitBase (D.stage n) Z :=
    D.isQuasicoherent_cone_coheratorLimitPullbackMap DQ n _ hT rfl rfl
  refine D.isIso_etaleSectionsBaseChangeMap_of_isZero DQ adj hj hUqc hUqs n g δ hT ?_
  refine hCRW _ (qcohDerived_derivedModulePushforward_obj D.B (limitBase D.system)
    D.containsLimitBase
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (D.isQuasiCompact_spaceProjection n) (D.isQuasiSeparated_spaceProjection n) Z hZq) ?_
  intro E hE
  refine isZero_sections_tensor_stagePushforward_of_isZero D n E
    (qcohDerived_of_isPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E hE) Z hZq ?_
  let : ((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase (D.stage n)).obj
      ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
          E)).CommShift ℤ :=
    (smallEtaleDerivedTensorProduct D.B (limitBase D.system) D.containsLimitBase
      (D.stage n)).commShift_right _
  have : ((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase (D.stage n)).obj
      ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
          E)).IsTriangulated :=
    (smallEtaleDerivedTensorProduct D.B (limitBase D.system) D.containsLimitBase
      (D.stage n)).exact_right _
  have hT₁ := ((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
    (D.stage n)).obj ((smallEtaleDerivedModulePullback D.B (limitBase D.system)
      D.containsLimitBase
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
        E)).map_distinguished _ hT
  have hT₂ := (derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
    (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).map_distinguished
      _ hT₁
  have hT₃ := (representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
    (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).map_distinguished _ hT₂
  have hiso := h0DIM E hE
  exact (Triangle.isZero₃_iff_isIso₁ _ hT₃).2 hiso

end Coherator

end SeparatedDerivedExistenceSystem

end AlgebraicGeometry.Space
