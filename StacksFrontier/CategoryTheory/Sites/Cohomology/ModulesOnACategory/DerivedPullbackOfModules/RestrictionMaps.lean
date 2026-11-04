module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedPullbackOfModules.DerivedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedPullbackOfModules.CoevaluationMates
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedPullbackOfModules.DerivedSections
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedPullbackOfModules.CoevaluationMates

/-!
# The restriction maps of the derived pullback of modules on a chaotic site

The derived restriction square for the coevaluations is deduced from its chain-level
counterpart, and from it the computations of the derived sections of the derived extension of
scalars and of the derived pullback are shown to be compatible with the canonical derived
restriction maps. The derived pullback is then packaged as a `DerivedPullbackData`, and it
carries cartesian objects to cartesian objects (Stacks 0GZ1).

## Main definitions

* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.derivedPullbackData`: the derived
  pullback and its sections computation packaged as a
  `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.DerivedPullbackData`.

## Main results

* `dCoevRestrictionMate_restrictScalarsSquare`: the derived restriction square for the
  coevaluations.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.restrictionMap_dExtendScalars`: the
  computation `dExtendScalarsCompRGamma` of the derived sections of the derived extension of
  scalars is compatible with the canonical derived restriction maps.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.restrictionMap_of_dExtendScalars`:
  `derivedPullbackCompRGamma` carries the canonical derived restriction maps of `Lg^*K` to those
  of `K`.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.isQC_derivedPullback`: Stacks 0GZ1 for
  the derived pullback constructed here — it carries cartesian objects to cartesian objects.

## References

* [Stacks Project, Tag 0GZ1](https://stacks.math.columbia.edu/tag/0GZ1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.DerivedCategoryComparisons (mapDerivedCategoryCompIso
  mapDerivedCategoryCompIso_inv_app_Q mapDerivedCategoryIsoOfNatIso)

universe r v u v' u' w

namespace Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C' ⥤ C)
  (O : Cᵒᵖ ⥤ RingCat.{r}) (O' : C'ᵒᵖ ⥤ RingCat.{r}) (φ : F.op ⋙ O ⟶ O')
  (hO : ∀ (U : Cᵒᵖ) (x y : O.obj U), x * y = y * x)
  (hO' : ∀ (U' : C'ᵒᵖ) (x y : O'.obj U'), x * y = y * x)

attribute [local instance] HasDerivedCategory.standard

/-! ### The derived restriction square for the coevaluations -/

section DerivedRestrictionSquare

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

-- The module universe of a restriction of scalars along a restriction map of `O'` is not pinned
-- by `rsPreservesFiniteLimits`, whose free module universe stalls on `max u' v' ?w =?= max u v u'
-- v'`; the instance that does not mention a presheaf of rings is given priority instead.
attribute [local instance 10000] restrictScalarsPreservesFiniteLimits
  restrictScalarsPreservesFiniteColimits

/-- The derived coevaluation/restriction-of-scalars square, at the image of a cochain complex:
it is the image under `Q` of the chain-level square, conjugated by the canonical factorizations
of the four descents involved. -/
private theorem dCoevaluationRestrictScalarsSquare_hom_app_Q (W' : C'ᵒᵖ)
    (M : CochainComplex (ModuleCat.{max u v u' v' r} (O'.obj W')) ℤ) :
    (dCoevaluationRestrictScalarsSquare F O O' φ W').hom.app (DerivedCategory.Q.obj M) =
      (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory.map
          ((coevaluation.{r, v', u', max u v} O' W').mapDerivedCategoryFactors.hom.app M) ≫
        (PresheafOfModules.restrictScalars.{max u v u' v' r}
            φ).mapDerivedCategoryFactors.hom.app
          (((coevaluation.{r, v', u', max u v} O' W').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (coevaluationRestrictScalarsSquare F O O' φ W') (ComplexShape.up ℤ)).hom.app M) ≫
        (coevaluation.{r, v', u', max u v} (F.op ⋙ O) W').mapDerivedCategoryFactors.inv.app
          (((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app W').hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) W').map
          ((ModuleCat.restrictScalars.{max u v u' v' r}
            (φ.app W').hom).mapDerivedCategoryFactors.inv.app M) := by
  have h : (dCoevaluationRestrictScalarsSquare F O O' φ W').hom.app (DerivedCategory.Q.obj M) =
      (mapDerivedCategoryCompIso (coevaluation.{r, v', u', max u v} O' W')
            (PresheafOfModules.restrictScalars.{max u v u' v' r} φ)).inv.app
          (DerivedCategory.Q.obj M) ≫
        (mapDerivedCategoryIsoOfNatIso
            (coevaluation.{r, v', u', max u v} O' W' ⋙
              PresheafOfModules.restrictScalars.{max u v u' v' r} φ)
            (ModuleCat.restrictScalars.{max u v u' v' r} (φ.app W').hom ⋙
              coevaluation.{r, v', u', max u v} (F.op ⋙ O) W')
            (coevaluationRestrictScalarsSquare F O O' φ W')).hom.app
          (DerivedCategory.Q.obj M) ≫
        (mapDerivedCategoryCompIso
            (ModuleCat.restrictScalars.{max u v u' v' r} (φ.app W').hom)
            (coevaluation.{r, v', u', max u v} (F.op ⋙ O) W')).hom.app
          (DerivedCategory.Q.obj M) := rfl
  rw [h, mapDerivedCategoryCompIso_inv_app_Q, mapDerivedCategoryIsoOfNatIso_hom_app_Q,
    mapDerivedCategoryCompIso_hom_app_Q]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc]
  rfl

/-- The derived square of restrictions of scalars, at the image of a cochain complex: it is the
image under `Q` of the chain-level square `restrictScalarsStructureSquare`, conjugated by the
canonical factorizations of the descents involved. -/
private theorem structureSquare_inv_app_Q {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (M : CochainComplex (ModuleCat.{max u v u' v' r} (O'.obj U')) ℤ) :
    (structureSquare F O O' φ a').inv.app (DerivedCategory.Q.obj M) =
      (DRestrict.{max u v} (F.op ⋙ O) a').map
          ((ModuleCat.restrictScalars.{max u v u' v' r}
            (φ.app U').hom).mapDerivedCategoryFactors.hom.app M) ≫
        (ModuleCat.restrictScalars.{max u v u' v' r}
            ((F.op ⋙ O).map a').hom).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (restrictScalarsStructureSquare F O O' φ a') (ComplexShape.up ℤ)).hom.app M) ≫
        (ModuleCat.restrictScalars.{max u v u' v' r}
            (φ.app V').hom).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.restrictScalars.{max u v u' v' r} (O'.map a').hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        (dStructure F O O' φ V').map
          ((ModuleCat.restrictScalars.{max u v u' v' r}
            (O'.map a').hom).mapDerivedCategoryFactors.inv.app M) := by
  have h : (structureSquare F O O' φ a').inv.app (DerivedCategory.Q.obj M) =
      (((mapDerivedCategoryCompIso
              (ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom)
              (ModuleCat.restrictScalars.{max u v u' v' r}
                ((F.op ⋙ O).map a').hom)).inv.app (DerivedCategory.Q.obj M) ≫
          (mapDerivedCategoryIsoOfNatIso
              (ModuleCat.restrictScalars.{max u v u' v' r} (φ.app V' ≫ O'.map a').hom)
              (ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom ⋙
                ModuleCat.restrictScalars.{max u v u' v' r} ((F.op ⋙ O).map a').hom)
              (ModuleCat.restrictScalarsComp'.{max u v u' v' r} ((F.op ⋙ O).map a').hom
                (φ.app U').hom (φ.app V' ≫ O'.map a').hom
                (by rw [(φ.naturality a').symm]; rfl))).inv.app (DerivedCategory.Q.obj M)) ≫
          (mapDerivedCategoryIsoOfNatIso
              (ModuleCat.restrictScalars.{max u v u' v' r} (φ.app V' ≫ O'.map a').hom)
              (ModuleCat.restrictScalars.{max u v u' v' r} (O'.map a').hom ⋙
                ModuleCat.restrictScalars.{max u v u' v' r} (φ.app V').hom)
              (ModuleCat.restrictScalarsComp'.{max u v u' v' r} (φ.app V').hom
                (O'.map a').hom (φ.app V' ≫ O'.map a').hom rfl)).hom.app
            (DerivedCategory.Q.obj M)) ≫
        (mapDerivedCategoryCompIso
            (ModuleCat.restrictScalars.{max u v u' v' r} (O'.map a').hom)
            (ModuleCat.restrictScalars.{max u v u' v' r} (φ.app V').hom)).hom.app
          (DerivedCategory.Q.obj M) := rfl
  rw [h, mapDerivedCategoryCompIso_inv_app_Q, mapDerivedCategoryIsoOfNatIso_inv_app_Q,
    mapDerivedCategoryIsoOfNatIso_hom_app_Q, mapDerivedCategoryCompIso_hom_app_Q]
  have hg : DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (ModuleCat.restrictScalarsComp'.{max u v u' v' r} ((F.op ⋙ O).map a').hom
            (φ.app U').hom (φ.app V' ≫ O'.map a').hom
            (by rw [(φ.naturality a').symm]; rfl)) (ComplexShape.up ℤ)).inv.app M) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (ModuleCat.restrictScalarsComp'.{max u v u' v' r} (φ.app V').hom (O'.map a').hom
            (φ.app V' ≫ O'.map a').hom rfl) (ComplexShape.up ℤ)).hom.app M) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (restrictScalarsStructureSquare F O O' φ a') (ComplexShape.up ℤ)).hom.app M) := by
    rw [← Functor.map_comp]
    rfl
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc, ← hg]
  simp only [Category.assoc]

/-- The derived restriction square, at the image of a cochain complex: both sides descend from
the chain-level square `coevRestrictionMate_restrictScalarsSquare`, conjugated by the same
canonical factorizations. -/
private theorem dCoevRestrictionMate_restrictScalarsSquare_app_Q {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (M : CochainComplex (ModuleCat.{max u v u' v' r} (O'.obj U')) ℤ) :
    ((PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory).map
          ((dCoevRestrictionMate.{r, v', u', max u v} O' a').app (DerivedCategory.Q.obj M)) ≫
        (dCoevaluationRestrictScalarsSquare F O O' φ V').hom.app
          ((DRestrict.{max u v} O' a').obj (DerivedCategory.Q.obj M)) =
      (dCoevaluationRestrictScalarsSquare F O O' φ U').hom.app (DerivedCategory.Q.obj M) ≫
        (dCoevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a').app
          ((dStructure F O O' φ U').obj (DerivedCategory.Q.obj M)) ≫
        (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) V').map
          ((structureSquare F O O' φ a').inv.app (DerivedCategory.Q.obj M)) := by
  -- The derived category of presheaves of `F⁻¹O`-modules and of `O'`-modules do not have their
  -- module universe pinned by `(restrictScalars φ).mapDerivedCategory` alone, so they are named
  -- with their universes written out.
  let : HasDerivedCategory.{max u v u' v' r}
      (PresheafOfModules.{max u v u' v' r} (F.op ⋙ O)) :=
    derivedPresheafCategory.{max u v, u', v', r} (F.op ⋙ O)
  let : HasDerivedCategory.{max u v u' v' r} (PresheafOfModules.{max u v u' v' r} O') :=
    derivedPresheafCategory.{max u v, u', v', r} O'
  have h₁ : ((PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory).map
      (((dCoevaluation.{r, v', u', max u v} O' V').map
          ((ModuleCat.restrictScalars.{max u v u' v' r} (O'.map
              a').hom).mapDerivedCategoryFactors.inv.app M))) ≫
        (dCoevaluationRestrictScalarsSquare F O O' φ V').hom.app ((DRestrict.{max u v} O' a').obj
            (DerivedCategory.Q.obj M)) =
      (dCoevaluationRestrictScalarsSquare F O O' φ V').hom.app (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars.{max u v u' v' r} (O'.map a').hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) ≫
        (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) V').map ((dStructure F O O' φ V').map
          ((ModuleCat.restrictScalars.{max u v u' v' r} (O'.map
              a').hom).mapDerivedCategoryFactors.inv.app M)) :=
    (dCoevaluationRestrictScalarsSquare F O O' φ V').hom.naturality _
  have h₃ : ((PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory).map
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coevRestrictionMate.{r, v', u', max u
      v} O' a') (ComplexShape.up ℤ)).app M)) ≫
        (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategoryFactors.hom.app
            (((coevaluation.{r, v', u', max u v} O' V').mapHomologicalComplex (ComplexShape.up
            ℤ)).obj (((ModuleCat.restrictScalars.{max u v u' v' r} (O'.map
            a').hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) =
      (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategoryFactors.hom.app
          (((coevaluation.{r, v', u', max u v} O' U').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          M) ≫
        DerivedCategory.Q.map (((PresheafOfModules.restrictScalars.{max u v u' v' r}
            φ).mapHomologicalComplex (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex
            (coevRestrictionMate.{r, v', u', max u v} O' a') (ComplexShape.up ℤ)).app M)) :=
    (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategoryFactors.hom.naturality
        _
  have g₂ : ((dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) U').map ((ModuleCat.restrictScalars.{max
      u v u' v' r} (φ.app U').hom).mapDerivedCategoryFactors.inv.app M)) ≫
        (dCoevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a').app ((dStructure F O O' φ U').obj
            (DerivedCategory.Q.obj M)) =
      (dCoevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a').app (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) ≫
        (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) V').map ((DRestrict.{max u v} (F.op ⋙ O)
            a').map
          ((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app
              U').hom).mapDerivedCategoryFactors.inv.app M)) :=
    (dCoevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a').naturality _
  have g₅ : (DRestrict.{max u v} (F.op ⋙ O) a').map ((ModuleCat.restrictScalars.{max u v u' v' r}
      (φ.app U').hom).mapDerivedCategoryFactors.inv.app M) ≫
        (DRestrict.{max u v} (F.op ⋙ O) a').map ((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app
            U').hom).mapDerivedCategoryFactors.hom.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have g₇ : ((coevaluation.{r, v', u', max u v} (F.op ⋙ O) V').mapDerivedCategoryFactors.inv.app
          (((ModuleCat.restrictScalars.{max u v u' v' r} ((F.op ⋙ O).map
              a').hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M))) ≫
        (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) V').map (DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (restrictScalarsStructureSquare F O O' φ a')
            (ComplexShape.up ℤ)).hom.app M)) =
      DerivedCategory.Q.map (((coevaluation.{r, v', u', max u v} (F.op ⋙ O)
          V').mapHomologicalComplex (ComplexShape.up ℤ)).map ((NatIso.mapHomologicalComplex
          (restrictScalarsStructureSquare F O O' φ a') (ComplexShape.up ℤ)).hom.app M)) ≫
        ((coevaluation.{r, v', u', max u v} (F.op ⋙ O) V').mapDerivedCategoryFactors.inv.app
          (((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app V').hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (((ModuleCat.restrictScalars.{max u v u' v' r} (O'.map
              a').hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) :=
    (((coevaluation.{r, v', u', max u v} (F.op ⋙ O) V').mapDerivedCategoryFactors.inv.naturality
        _)).symm
  have g₈ : DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (coevaluationRestrictScalarsSquare
      F O O' φ U') (ComplexShape.up ℤ)).hom.app M) ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (coevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a')
      (ComplexShape.up ℤ)).app (((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app
      U').hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫ DerivedCategory.Q.map
      (((coevaluation.{r, v', u', max u v} (F.op ⋙ O) V').mapHomologicalComplex (ComplexShape.up
      ℤ)).map ((NatIso.mapHomologicalComplex (restrictScalarsStructureSquare F O O' φ a')
      (ComplexShape.up ℤ)).hom.app M)) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (coevaluationRestrictScalarsSquare F O O'
          φ U') (ComplexShape.up ℤ)).hom.app M ≫ (NatTrans.mapHomologicalComplex
          (coevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a') (ComplexShape.up ℤ)).app
          (((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≫ ((coevaluation.{r, v', u', max u v} (F.op ⋙ O)
          V').mapHomologicalComplex (ComplexShape.up ℤ)).map ((NatIso.mapHomologicalComplex
          (restrictScalarsStructureSquare F O O' φ a') (ComplexShape.up ℤ)).hom.app M)) := by
    rw [Functor.map_comp, Functor.map_comp]
  have hmid : DerivedCategory.Q.map (((PresheafOfModules.restrictScalars.{max u v u' v' r}
      φ).mapHomologicalComplex (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex
      (coevRestrictionMate.{r, v', u', max u v} O' a') (ComplexShape.up ℤ)).app M) ≫
      (NatIso.mapHomologicalComplex (coevaluationRestrictScalarsSquare F O O' φ V') (ComplexShape.up
      ℤ)).hom.app (((ModuleCat.restrictScalars.{max u v u' v' r} (O'.map
      a').hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) = DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (coevaluationRestrictScalarsSquare F O O' φ U')
      (ComplexShape.up ℤ)).hom.app M ≫ (NatTrans.mapHomologicalComplex (coevRestrictionMate.{r, v',
      u', max u v} (F.op ⋙ O) a') (ComplexShape.up ℤ)).app (((ModuleCat.restrictScalars.{max u v u'
      v' r} (φ.app U').hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫ ((coevaluation.{r,
      v', u', max u v} (F.op ⋙ O) V').mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((NatIso.mapHomologicalComplex (restrictScalarsStructureSquare F O O' φ a') (ComplexShape.up
      ℤ)).hom.app M)) := by
    rw [coevRestrictionMate_restrictScalarsSquare_mapHomologicalComplex F O O' φ a' M]
  have hL := bookL ((PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory)
      (dCoevRestrictionMate_app_Q.{r, v', u', max u v} O' a' M) h₁
    (cancel_head_map ((PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory)
        (Iso.inv_hom_id_app _ _)
      (dCoevaluationRestrictScalarsSquare_hom_app_Q F O O' φ V' (((ModuleCat.restrictScalars.{max u
          v u' v' r} (O'.map a').hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) h₃
    (DerivedCategory.Q.map_comp (((PresheafOfModules.restrictScalars.{max u v u' v' r}
        φ).mapHomologicalComplex (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex
        (coevRestrictionMate.{r, v', u', max u v} O' a') (ComplexShape.up ℤ)).app M))
        ((NatIso.mapHomologicalComplex (coevaluationRestrictScalarsSquare F O O' φ V')
        (ComplexShape.up ℤ)).hom.app (((ModuleCat.restrictScalars.{max u v u' v' r} (O'.map
        a').hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))).symm
  have hR := bookR (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) V')
    (dCoevaluationRestrictScalarsSquare_hom_app_Q F O O' φ U' M) g₂
    (cancel_head (Iso.inv_hom_id_app _ _)
      (dCoevRestrictionMate_app_Q.{r, v', u', max u v} (F.op ⋙ O) a'
          (((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)))
    (structureSquare_inv_app_Q F O O' φ a' M) g₅ (Iso.inv_hom_id_app _ _) g₇ g₈
  exact hL.trans ((congr_mid _ _ hmid _).trans hR.symm)

/-- **The derived restriction square for the coevaluations.** The mate of the canonical derived
restriction transformation commutes with the derived coevaluation/restriction-of-scalars squares,
through the derived square of restrictions of scalars attached to `a'`. -/
theorem dCoevRestrictionMate_restrictScalarsSquare {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (Y : DerivedCategory (ModuleCat.{max u v u' v' r} (O'.obj U'))) :
    ((PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory).map
          ((dCoevRestrictionMate.{r, v', u', max u v} O' a').app Y) ≫
        (dCoevaluationRestrictScalarsSquare F O O' φ V').hom.app
          ((DRestrict.{max u v} O' a').obj Y) =
      (dCoevaluationRestrictScalarsSquare F O O' φ U').hom.app Y ≫
        (dCoevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a').app
          ((dStructure F O O' φ U').obj Y) ≫
        (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) V').map
          ((structureSquare F O O' φ a').inv.app Y) := by
  have key : Functor.whiskerRight (dCoevRestrictionMate.{r, v', u', max u v} O' a')
          ((PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory) ≫
        Functor.whiskerLeft (DRestrict.{max u v} O' a')
          (dCoevaluationRestrictScalarsSquare F O O' φ V').hom =
      (dCoevaluationRestrictScalarsSquare F O O' φ U').hom ≫
        Functor.whiskerLeft (dStructure F O O' φ U')
          (dCoevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a') ≫
        Functor.whiskerRight (structureSquare F O O' φ a').inv
          (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) V') := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{max u v u' v' r} (O'.obj U'))
        (ComplexShape.up ℤ)) fun M => ?_
    exact dCoevRestrictionMate_restrictScalarsSquare_app_Q F O O' φ a' M
  exact NatTrans.congr_app key Y

end DerivedRestrictionSquare

/-! ### The restriction maps of the derived extension of scalars -/

/-- **Two morphisms out of a value of a left adjoint agree as soon as their adjoint transposes
do**, the adjoint transpose being a bijection. -/
theorem eq_of_unit_map_eq {A : Type*} [Category A] {B : Type*} [Category B] {Lf : A ⥤ B}
    {Rf : B ⥤ A} (adj : Lf ⊣ Rf) {X : A} {Y : B} (f g : Lf.obj X ⟶ Y)
    (h : adj.unit.app X ≫ Rf.map f = adj.unit.app X ≫ Rf.map g) : f = g :=
  (adj.homEquiv X Y).injective (by simpa only [Adjunction.homEquiv_unit] using h)

/-- **The inverse of the sections computation of the derived extension of scalars is the
conjugate of the derived coevaluation square.** -/
theorem dExtendScalarsCompRGamma_inv_eq (W' : C'ᵒᵖ) :
    (conjugateEquiv (dExtendScalarsSectionsAdjunction F O O' φ W')
        (dBaseChangeSectionsAdjunction F O O' φ hO hO' W')).symm
        (dCoevaluationRestrictScalarsSquare F O O' φ W').hom =
      (dExtendScalarsCompRGamma F O O' φ hO hO' W').inv := rfl

/-- **The sections computation of the derived extension of scalars is the conjugate, the other
way round, of the inverse of the derived coevaluation square.** -/
theorem dExtendScalarsCompRGamma_hom_eq (W' : C'ᵒᵖ) :
    (conjugateEquiv (dBaseChangeSectionsAdjunction F O O' φ hO hO' W')
        (dExtendScalarsSectionsAdjunction F O O' φ W')).symm
        (dCoevaluationRestrictScalarsSquare F O O' φ W').inv =
      (dExtendScalarsCompRGamma F O O' φ hO hO' W').hom := rfl

/-- **The computation `dExtendScalarsCompRGamma` of the derived sections of the derived extension
of scalars is compatible with the canonical derived restriction maps.** Over a morphism `a'` of
`C'ᵒᵖ` it carries the restriction map of the derived extension of scalars of `L` to the restriction
map of `L`, followed by the mate of the restriction transformation of the base changes. -/
theorem restrictionMap_dExtendScalars {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (L : DMod.{max u v} (F.op ⋙ O)) :
    restrictionMap.{max u v} O' a' ((dExtendScalars F O O' φ).obj L) ≫
        (DRestrict.{max u v} O' a').map
          ((dExtendScalarsCompRGamma F O O' φ hO hO' U').hom.app L) =
      (dExtendScalarsCompRGamma F O O' φ hO hO' V').hom.app L ≫
        ((PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO').baseChange
            V').map (restrictionMap.{max u v} (F.op ⋙ O) a' L) ≫
        (restrictionMate
          (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO')
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO')
          a').app ((RGamma.{max u v} (F.op ⋙ O) U').obj L) := by
  have key : (dExtendScalarsCompRGamma F O O' φ hO hO' V').inv.app L ≫
      restrictionMap.{max u v} O' a' ((dExtendScalars F O O' φ).obj L) ≫
        (DRestrict.{max u v} O' a').map
          ((dExtendScalarsCompRGamma F O O' φ hO hO' U').hom.app L) =
      ((PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO').baseChange V').map
          (restrictionMap.{max u v} (F.op ⋙ O) a' L) ≫
        (restrictionMate
          (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO')
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO')
          a').app ((RGamma.{max u v} (F.op ⋙ O) U').obj L) := by
    refine eq_of_unit_map_eq (dBaseChangeSectionsAdjunction F O O' φ hO hO' V') _ _ ?_
    have hmate := unit_mateEquiv
        ((PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO').adj U')
        ((PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO').adj V')
        (restrictionMate (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO')
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO') a')
        ((RGamma.{max u v} (F.op ⋙ O) U').obj L)
    rw [NatTrans.congr_app (mate_restrictionMate
      (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO')
      (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
      (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO') a')
      (((PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO').baseChange U').obj
        ((RGamma.{max u v} (F.op ⋙ O) U').obj L))] at hmate
    have hra : (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory.map
          ((dCoevRestrictionMate.{r, v', u', max u v} O' a').app
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L))) ≫
        (dCoevaluationRestrictScalarsSquare F O O' φ V').hom.app ((DRestrict.{max u v} O' a').obj
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L))) =
        (dCoevaluationRestrictScalarsSquare F O O' φ U').hom.app
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) ≫
          (dCoevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a').app
            ((dRestrictScalars.{r, max u v u' v' r} (φ.app U')).obj
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L))) ≫
          (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) V').map ((structureSquare F O O' φ
            a').inv.app
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L))) :=
      dCoevRestrictionMate_restrictScalarsSquare F O O' φ a' _
    have e2 : (PullbackQuasiCoherentBaseChange.dBaseChangeAdj.{r, max u v u' v'} (φ.app V')
          (hO _) (hO' _)).unit.app ((RGamma.{max u v} (F.op ⋙ O) V').obj L) ≫
        (dRestrictScalars.{r, max u v u' v' r} (φ.app V')).map
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app V')
          (hO _) (hO' _)).map (restrictionMap.{max u v} (F.op ⋙ O) a' L)) =
        restrictionMap.{max u v} (F.op ⋙ O) a' L ≫
          (PullbackQuasiCoherentBaseChange.dBaseChangeAdj.{r, max u v u' v'} (φ.app V')
          (hO _) (hO' _)).unit.app ((DRestrict.{max u v} (F.op ⋙ O) a').obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) := Adjunction.unit_naturality _ _
    have e3 : (PullbackQuasiCoherentBaseChange.dBaseChangeAdj.{r, max u v u' v'} (φ.app V')
          (hO _) (hO' _)).unit.app ((DRestrict.{max u v} (F.op ⋙ O) a').obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) ≫ (dRestrictScalars.{r, max u v u' v' r} (φ.app
            V')).map ((restrictionMate
          (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO')
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO')
          a').app
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) =
        (DRestrict.{max u v} (F.op ⋙ O) a').map
          ((PullbackQuasiCoherentBaseChange.dBaseChangeAdj.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).unit.app
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) ≫ (structureSquare F O O' φ a').inv.app
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) := hmate.symm
    have hinner : restrictionMap.{max u v} (F.op ⋙ O) a' L ≫ (DRestrict.{max u v} (F.op ⋙ O) a').map
          ((PullbackQuasiCoherentBaseChange.dBaseChangeAdj.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).unit.app
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) ≫ (structureSquare F O O' φ a').inv.app
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) =
        (PullbackQuasiCoherentBaseChange.dBaseChangeAdj.{r, max u v u' v'} (φ.app V')
          (hO _) (hO' _)).unit.app ((RGamma.{max u v} (F.op ⋙ O) V').obj L) ≫
          (dRestrictScalars.{r, max u v u' v' r} (φ.app V')).map
            ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app V')
          (hO _) (hO' _)).map (restrictionMap.{max u v} (F.op ⋙ O) a' L) ≫ (restrictionMate
          (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO')
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO')
          a').app
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) := by
      rw [(dRestrictScalars.{r, max u v u' v' r} (φ.app V')).map_comp
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app V')
          (hO _) (hO' _)).map (restrictionMap.{max u v} (F.op ⋙ O) a' L)) ((restrictionMate
          (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO')
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO')
          a').app
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)), reassoc_of% e2, e3]
      rfl
    have t3 : (dCoevaluationAdjunction.{r, v', u', max u v} (F.op ⋙ O) U').unit.app L ≫
          (dCoevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a').app
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L) =
        (dCoevaluationAdjunction.{r, v', u', max u v} (F.op ⋙ O) V').unit.app L ≫
          (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) V').map (restrictionMap.{max u v} (F.op ⋙
          O) a' L) :=
      unit_dCoevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a' L
    have t4 : (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) U').map
          ((PullbackQuasiCoherentBaseChange.dBaseChangeAdj.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).unit.app
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) ≫ (dCoevRestrictionMate.{r, v', u', max u v}
            (F.op ⋙ O) a').app ((dRestrictScalars.{r, max u v u' v' r} (φ.app U')).obj
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L))) =
        (dCoevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a').app
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L) ≫ (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O)
            V').map ((DRestrict.{max u v} (F.op ⋙ O) a').map
            ((PullbackQuasiCoherentBaseChange.dBaseChangeAdj.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).unit.app
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L))) := (dCoevRestrictionMate.{r, v', u', max u v}
            (F.op ⋙ O) a').naturality _
    have t1 : (dCoevaluationAdjunction.{r, v', u', max u v} O' U').unit.app ((dExtendScalars F O O'
          φ).obj L) ≫ (dCoevRestrictionMate.{r, v', u', max u v} O' a').app ((RGamma.{max u v} O'
          U').obj ((dExtendScalars F O O' φ).obj L)) =
        (dCoevaluationAdjunction.{r, v', u', max u v} O' V').unit.app ((dExtendScalars F O O' φ).obj
          L) ≫ (dCoevaluation.{r, v', u', max u v} O' V').map (restrictionMap.{max u v} O' a'
          ((dExtendScalars F O O' φ).obj L)) :=
      unit_dCoevRestrictionMate.{r, v', u', max u v} O' a' ((dExtendScalars F O O' φ).obj L)
    have t2 : (dCoevaluation.{r, v', u', max u v} O' U').map ((dExtendScalarsCompRGamma F O O' φ hO
          hO' U').hom.app L) ≫ (dCoevRestrictionMate.{r, v', u', max u v} O' a').app
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) =
        (dCoevRestrictionMate.{r, v', u', max u v} O' a').app ((RGamma.{max u v} O' U').obj
          ((dExtendScalars F O O' φ).obj L)) ≫ (dCoevaluation.{r, v', u', max u v} O' V').map
          ((DRestrict.{max u v} O' a').map ((dExtendScalarsCompRGamma F O O' φ hO hO' U').hom.app
          L)) :=
      (dCoevRestrictionMate.{r, v', u', max u v} O' a').naturality _
    have hinner' : (dCoevaluationAdjunction.{r, v', u', max u v} O' V').unit.app ((dExtendScalars F
          O O' φ).obj L) ≫ (dCoevaluation.{r, v', u', max u v} O' V').map (restrictionMap.{max u v}
          O' a' ((dExtendScalars F O O' φ).obj L) ≫
          (DRestrict.{max u v} O' a').map ((dExtendScalarsCompRGamma F O O' φ hO hO' U').hom.app L))
            =
        (dCoevaluationAdjunction.{r, v', u', max u v} O' U').unit.app ((dExtendScalars F O O' φ).obj
          L) ≫ (dCoevaluation.{r, v', u', max u v} O' U').map ((dExtendScalarsCompRGamma F O O' φ hO
          hO' U').hom.app L) ≫ (dCoevRestrictionMate.{r, v', u', max u v} O' a').app
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) := by
      rw [Functor.map_comp, ← reassoc_of% t1, t2]
    have s1 : (dExtendScalarsSectionsAdjunction F O O' φ V').unit.app L ≫
          (dCoevaluationRestrictScalarsSquare F O O' φ V').hom.app ((RGamma.{max u v} O' V').obj
          ((dExtendScalars F O O' φ).obj L)) =
        (dBaseChangeSectionsAdjunction F O O' φ hO hO' V').unit.app L ≫
          (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) V').map
          ((dRestrictScalars.{r, max u v u' v' r} (φ.app V')).map ((dExtendScalarsCompRGamma F O O'
          φ hO hO' V').inv.app L)) := by
      exact unit_conjugateEquiv_symm _ _ (dCoevaluationRestrictScalarsSquare F O O' φ V').hom L
    have s2 : (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory.map
          ((dCoevaluation.{r, v', u', max u v} O' V').map
          (restrictionMap.{max u v} O' a' ((dExtendScalars F O O' φ).obj L) ≫
          (DRestrict.{max u v} O' a').map ((dExtendScalarsCompRGamma F O O' φ hO hO' U').hom.app
            L))) ≫ (dCoevaluationRestrictScalarsSquare F O O' φ V').hom.app ((DRestrict.{max u v} O'
            a').obj
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L))) =
        (dCoevaluationRestrictScalarsSquare F O O' φ V').hom.app ((RGamma.{max u v} O' V').obj
          ((dExtendScalars F O O' φ).obj L)) ≫ (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O)
          V').map ((dRestrictScalars.{r, max u v u' v' r} (φ.app V')).map
          (restrictionMap.{max u v} O' a' ((dExtendScalars F O O' φ).obj L) ≫
          (DRestrict.{max u v} O' a').map ((dExtendScalarsCompRGamma F O O' φ hO hO' U').hom.app
            L))) := (dCoevaluationRestrictScalarsSquare F O O' φ V').hom.naturality _
    have s7 : (dBaseChangeSectionsAdjunction F O O' φ hO hO' U').unit.app L ≫
          (dCoevaluationRestrictScalarsSquare F O O' φ U').inv.app
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) =
        (dExtendScalarsSectionsAdjunction F O O' φ U').unit.app L ≫
          (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory.map
          ((dCoevaluation.{r, v', u', max u v} O' U').map ((dExtendScalarsCompRGamma F O O' φ hO hO'
          U').hom.app L)) := by
      exact unit_conjugateEquiv_symm _ _ (dCoevaluationRestrictScalarsSquare F O O' φ U').inv L
    have mid : (dExtendScalarsSectionsAdjunction F O O' φ V').unit.app L ≫
          (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory.map
          ((dCoevaluation.{r, v', u', max u v} O' V').map
          (restrictionMap.{max u v} O' a' ((dExtendScalars F O O' φ).obj L) ≫
          (DRestrict.{max u v} O' a').map ((dExtendScalarsCompRGamma F O O' φ hO hO' U').hom.app
            L))) =
        (dBaseChangeSectionsAdjunction F O O' φ hO hO' U').unit.app L ≫
          (dCoevaluationRestrictScalarsSquare F O O' φ U').inv.app
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) ≫
            (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapDerivedCategory.map
            ((dCoevRestrictionMate.{r, v', u', max u v} O' a').app
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L))) := by
      rw [reassoc_of% s7]
      simp only [dExtendScalarsSectionsAdjunction, Adjunction.comp_unit_app, Functor.comp_obj,
        Category.assoc]
      simp only [← Functor.map_comp]
      rw [hinner']
    have hL : (dBaseChangeSectionsAdjunction F O O' φ hO hO' V').unit.app L ≫
          ((dRestrictScalars.{r, max u v u' v' r} (φ.app V')) ⋙ (dCoevaluation.{r, v', u', max u v}
          (F.op ⋙ O) V')).map ((dExtendScalarsCompRGamma F O O' φ hO hO' V').inv.app L ≫
          restrictionMap.{max u v} O' a' ((dExtendScalars F O O' φ).obj L) ≫
          (DRestrict.{max u v} O' a').map ((dExtendScalarsCompRGamma F O O' φ hO hO' U').hom.app L))
            =
        (dBaseChangeSectionsAdjunction F O O' φ hO hO' U').unit.app L ≫
          (dCoevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a').app
            ((dRestrictScalars.{r, max u v u' v' r} (φ.app U')).obj
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L))) ≫
          (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) V').map ((structureSquare F O O' φ
            a').inv.app
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L))) := by
      rw [Functor.map_comp]
      simp only [Functor.comp_map]
      rw [← reassoc_of% s1, ← s2, reassoc_of% mid, hra, Iso.inv_hom_id_app_assoc]
    have hR : (dBaseChangeSectionsAdjunction F O O' φ hO hO' U').unit.app L ≫
          (dCoevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a').app
            ((dRestrictScalars.{r, max u v u' v' r} (φ.app U')).obj
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L))) ≫
          (dCoevaluation.{r, v', u', max u v} (F.op ⋙ O) V').map ((structureSquare F O O' φ
            a').inv.app
          ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'} (φ.app U')
          (hO _) (hO' _)).obj
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L))) =
        (dBaseChangeSectionsAdjunction F O O' φ hO hO' V').unit.app L ≫
          ((dRestrictScalars.{r, max u v u' v' r} (φ.app V')) ⋙ (dCoevaluation.{r, v', u', max u v}
          (F.op ⋙ O) V')).map ((PullbackQuasiCoherentBaseChange.dBaseChange.{r, max u v u' v'}
          (φ.app V')
          (hO _) (hO' _)).map (restrictionMap.{max u v} (F.op ⋙ O) a' L) ≫ (restrictionMate
          (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO')
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO')
          a').app
          ((RGamma.{max u v} (F.op ⋙ O) U').obj L)) := by
      simp only [dBaseChangeSectionsAdjunction, Adjunction.comp_unit_app, Functor.comp_map,
        Functor.comp_obj, Category.assoc]
      rw [reassoc_of% t4, reassoc_of% t3]
      simp only [← Functor.map_comp]
      rw [hinner]
      rfl
    exact hL.trans hR
  have h2 := congrArg (fun f => (dExtendScalarsCompRGamma F O O' φ hO hO' V').hom.app L ≫ f) key
  simp only [Iso.hom_inv_id_app_assoc] at h2
  exact h2

/-! ### The restriction maps of the derived pullback -/

/-- **The computation `derivedPullbackCompRGamma` of the derived sections of `Lg^*` is compatible
with the canonical derived restriction maps.** Over a morphism `a'` of `C'ᵒᵖ` it carries the
restriction map of `Lg^*K` along `a'` to the restriction map of `K` along `F a'`, followed by the
mate of the restriction transformation of the base changes. -/
theorem restrictionMap_of_dExtendScalars {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (K : DMod.{max u' v'} O) :
    restrictionMap.{max u v} O' a' ((derivedPullback F O O' φ).obj K) ≫
        (DRestrict.{max u v} O' a').map
          ((derivedPullbackCompRGamma F O O' φ hO hO' U').hom.app K) =
      (derivedPullbackCompRGamma F O O' φ hO hO' V').hom.app K ≫
        ((PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO').baseChange V').map
          (restrictionMap.{max u' v'} O (F.op.map a') K) ≫
        (restrictionMate (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO')
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO')
          a').app ((RGamma.{max u' v'} O (F.op.obj U')).obj K) := by
  have hmate : ((PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO').baseChange
            V').map
          ((DRestrict.{max u' v'} O (F.op.map a')).map
            ((dInverseImageCompRGamma.{r, v, u, v', u'} F O U').hom.app K)) ≫
        (restrictionMate (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO')
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO')
          a').app ((RGamma.{max u' v'} O (F.op.obj U')).obj K) =
      (restrictionMate (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO')
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
          (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO')
          a').app
          ((RGamma.{max u v} (F.op ⋙ O) U').obj ((dInverseImage.{r, v, u, v', u'} F O).obj K)) ≫
        (DRestrict.{max u v} O' a').map
          (((PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO').baseChange
            U').map ((dInverseImageCompRGamma.{r, v, u, v', u'} F O U').hom.app K)) :=
    (restrictionMate (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO')
      (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
      (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO')
      a').naturality _
  exact comp_map_eq_of_mate (R := DRestrict.{max u v} O' a')
    (T := (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO').baseChange V')
    (S := DRestrict.{max u' v'} O (F.op.map a'))
    (restrictionMap_dExtendScalars F O O' φ hO hO' a'
      ((dInverseImage.{r, v, u, v', u'} F O).obj K)) hmate
    (restrictionMap_dInverseImage F O a' K)

/-! ### The derived pullback as a `DerivedPullbackData` -/

/-- **The canonical `DerivedPullbackData` of this situation**: the derived pullback
`derivedPullback`, with the sections computation `derivedPullbackCompRGamma` and its compatibility
`restrictionMap_of_dExtendScalars` with the canonical derived restriction maps. -/
noncomputable def derivedPullbackData :
    DerivedPullbackData (PullbackQuasiCoherentBaseChange.structureBaseChange F O O' φ hO hO')
      (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO)
      (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO') where
  Lpullback := derivedPullback F O O' φ
  sectionsIso := derivedPullbackCompRGamma F O O' φ hO hO'
  sectionsIso_restrictionMap a' K := restrictionMap_of_dExtendScalars F O O' φ hO hO' a' K

/-! ### Stacks 0GZ1 for the derived pullback constructed here -/

/-- **Derived pullback along a morphism of ringed topoi on chaotic sites carries cartesian
objects to cartesian objects.** If the derived sections of `K` are cartesian then so are the
derived sections of `Lg^*K`, the cartesian condition on either side being taken with respect to
the derived base changes along the restriction homomorphisms of the structure sheaf there. -/
@[stacks 0GZ1 "Lg^* carries QC(O) into QC(O'), for the derived pullback constructed here"]
theorem isQC_derivedPullback (K : DMod.{max u' v'} O)
    (hK : IsQC.{max u' v'}
      (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v, u, max u' v'} O hO) K) :
    IsQC.{max u v}
      (PullbackQuasiCoherentBaseChange.baseChangeDataOfComm.{r, v', u', max u v} O' hO')
      ((derivedPullback F O O' φ).obj K) :=
  PullbackQuasiCoherentBaseChange.isQC_Lpullback_of_comm F O O' φ hO hO'
    (derivedPullbackData F O O' φ hO hO') K hK

end Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

end
