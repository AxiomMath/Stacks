module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitCohomologyQcqsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationStalkCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafEffacement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleCohomologyForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.InjectiveSheafSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldBaseChangeInjectiveAcyclic

/-!
# Restrictions to `Y_K` of sheaves acyclic at every finite stage

Let `k` be a field, `K/k` a separable algebraic extension and `Y` a quasi-compact and
quasi-separated `k`-scheme. If a sheaf `G` of `Λ`-modules on `Y_étale` has no higher cohomology on
every finite stage `Y_E`, `E ⊆ K` finite, then its restriction to `Y_K` has none either: every
class of `H^q(Y_K, G|_{Y_K})` comes from some stage (Stacks 09YQ). This generalizes
`Stacks.EtaleCohomology.subsingleton_H_fieldBaseChange_of_injective`, whose stages are injective.

## Main results

* `Stacks.EtaleCohomology.subsingleton_H_fieldBaseChange_of_stage`.
* `Stacks.EtaleCohomology.isZero_rightDerived_fieldBaseChange_of_stage`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- `Ext` of abelian sheaves on the small étale site at its object universe, pinned. -/
local instance (priority := 3000) hasExt_smallEtale_objectUniverse_fieldBaseChangeStage
    (Y : Scheme.{u}) : HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  CategoryTheory.IsGrothendieckAbelian.hasExt _

attribute [local instance] fextOrderBot fextIsDirected etale_spectrumMap_fext

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar]

/-- **A sheaf without higher cohomology at every finite stage `Y_E` has none on `Y_K`**, at the
level of the underlying abelian sheaves: every class comes from a finite stage (Stacks 09YQ). -/
theorem subsingleton_H_fieldBaseChange_of_stage (I : EtaleModules.{u, 0} Λ Y.left)
    (hI : ∀ (i : FExt k kbar) (q : ℕ), 0 < q → Subsingleton (Sheaf.H.{u + 1}
      ((etaleModuleUnderlyingAbelian _ Λ).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldStageSystem Y kbar |>.obj (op i)).hom).obj I)) q))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (fieldBaseChangeProj Y
        kbar)).obj
      ((etaleModuleUnderlyingAbelian Y.left Λ).obj I)) q) := by
  let W := fieldStageSystem Y kbar
  let D := W ⋙ Scheme.Etale.forget Y.left ⋙ Over.forget Y.left
  let c := fieldStageCone Y kbar
  have : ∀ {i j : (FExt k kbar)ᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) :=
    fun a => isAffineHom_fieldStageMap Y kbar a
  have : CompactSpace (D.obj (op ⊥)) := compactSpace_fieldStage Y kbar ⊥
  have : QuasiSeparatedSpace (D.obj (op ⊥)) := quasiSeparatedSpace_fieldStage Y kbar ⊥
  let UI := (etaleModuleUnderlyingAbelian Y.left Λ).obj I
  let G₀ := (etaleAbelianInverseImage.{u, 0} (W.obj (op ⊥)).hom).obj UI
  -- the inverse image to `Y_K` through the bottom stage
  have e₀ := (etaleAbelianInverseImageCompIso'.{u, 0} (c.π.app (op ⊥)) (W.obj (op ⊥)).hom
    (fieldBaseChangeProj Y kbar) (fieldStageCone_π_comp_hom Y kbar (op ⊥)).symm).app UI
  refine (subsingleton_H_iff_of_iso e₀ q).2 ⟨fun x x' => ?_⟩
  suffices h : ∀ z : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (c.π.app (op ⊥))).obj G₀) q,
      z = 0 from (h x).trans (h x').symm
  intro z
  obtain ⟨i, h, y, hy⟩ :=
    LimitExt.exists_le_restriction_eq_of_qcqs D c (fieldStageConeIsLimit Y kbar) ⊥ G₀ q z
  -- the stage `Y_E` is étale over `Y`, so the class `y` lives on an injective sheaf
  have hW : D.map (homOfLE h).op ≫ (W.obj (op ⊥)).hom = (W.obj (op i)).hom :=
    MorphismProperty.Over.w (W.map (homOfLE h).op)
  have e₁ := (etaleAbelianInverseImageCompIso'.{u, 0} (D.map (homOfLE h).op) (W.obj (op ⊥)).hom
    (W.obj (op i)).hom hW.symm).app UI
  have e₂ := (etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ (W.obj (op i)).hom).app I
  have : Etale (W.obj (op i)).hom := (W.obj (op i)).prop
  have : Subsingleton (Sheaf.H.{u + 1}
      ((etaleAbelianInverseImage.{u, 0} (D.map (homOfLE h).op)).obj G₀) q) :=
    (subsingleton_H_iff_of_iso (e₁.symm ≪≫ e₂) q).2 (hI i q hq)
  rw [← hy, Subsingleton.elim y 0, map_zero, Ext.zero_comp]


/-- **`H^q(Y_K, G|_{Y_K}) = 0` for `q > 0`** as soon as `H^q(Y_E, G|_{Y_E}) = 0` for every finite
stage `Y_E` and `q > 0`. -/
theorem isZero_rightDerived_fieldBaseChange_of_stage (I : EtaleModules.{u, 0} Λ Y.left)
    (hI : ∀ (i : FExt k kbar) (q : ℕ), 0 < q → Subsingleton (Sheaf.H.{u + 1}
      ((etaleModuleUnderlyingAbelian _ Λ).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldStageSystem Y kbar |>.obj (op i)).hom).obj I)) q))
    (q : ℕ) (hq : 0 < q) :
    IsZero (((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerived q).obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj I)) := by
  let H := (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj I
  have hH : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian _ Λ).obj H) q) :=
    (subsingleton_H_iff_of_iso ((etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ
      (fieldBaseChangeProj Y kbar)).app I) q).1
        (subsingleton_H_fieldBaseChange_of_stage Λ Y kbar I hI q hq)
  have : Subsingleton ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
      (((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerived q).obj H)) :=
    AddCommGrpCat.isZero_iff_subsingleton.1
      ((AddCommGrpCat.isZero_iff_subsingleton.2 hH).of_iso
        ((etaleModuleCohomologyIsoFunctorH Λ q).app H))
  exact ModuleCat.isZero_of_subsingleton _

end Stacks.EtaleCohomology

end
