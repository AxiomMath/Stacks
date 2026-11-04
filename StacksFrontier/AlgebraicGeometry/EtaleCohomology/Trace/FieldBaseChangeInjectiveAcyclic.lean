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

/-!
# Restrictions of injective sheaves to `Y_K` are acyclic

Let `k` be a field, `K/k` a separable algebraic extension, `Y` a quasi-compact and
quasi-separated `k`-scheme and `I` an injective sheaf of `Λ`-modules on `Y_étale`. Then the
restriction `I|_{Y_K}` has no higher cohomology: `H^q(Y_K, I|_{Y_K}) = 0` for `q > 0`.

## Main results

* `Stacks.EtaleCohomology.subsingleton_H_etaleModuleUnderlyingAbelian_of_injective`: the
  underlying abelian sheaf of an injective sheaf of `Λ`-modules has no higher cohomology.
* `Stacks.EtaleCohomology.isZero_rightDerived_fieldBaseChange_of_injective`:
  `H^q(Y_K, I|_{Y_K}) = 0` for `q > 0` and `I` injective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- `Ext` of abelian sheaves on the small étale site at its object universe, pinned. -/
local instance (priority := 3000) hasExt_smallEtale_objectUniverse_fieldBaseChange
    (Y : Scheme.{u}) : HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  CategoryTheory.IsGrothendieckAbelian.hasExt _

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned at the object
universe. -/
local instance (priority := 3000) etaleModules_enoughInjectives_fieldBaseChange (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

section Underlying

variable (Λ : Type) [Ring Λ]

/-- **The underlying abelian sheaf of an injective sheaf of `Λ`-modules has no higher
cohomology** (Stacks 03FD). -/
theorem subsingleton_H_etaleModuleUnderlyingAbelian_of_injective {Z : Scheme.{u}}
    (J : EtaleModules.{u, 0} Λ Z) [Injective J] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian Z Λ).obj J) q) := by
  let := HasDerivedCategory.standard (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  have h := (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived
    (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}) ((etaleModuleForgetAb.{u, 0} Λ Z).obj J)).1
    (rightAcyclic_Γ_etaleModuleForgetAb_obj.{u, 0} Λ Z J) q hq
  exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0, u, u + 1}
    (F := (etaleModuleUnderlyingAbelian Z Λ).obj J) (n := q)).2 h

/-- Inverse image along an étale morphism preserves injective sheaves of `Λ`-modules. -/
theorem injective_etaleModuleInverseImage_of_etale {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (I : EtaleModules.{u, 0} Λ X) [Injective I] :
    Injective ((etaleModuleInverseImage.{u, 0} Λ j).obj I) :=
  have := injective_etaleModuleRestriction.{u, 0} Λ j I
  Injective.of_iso ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).app I).symm inferInstance

end Underlying

section Acyclic

attribute [local instance] fextOrderBot fextIsDirected etale_spectrumMap_fext

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar]

/-- **The restriction of an injective sheaf to `Y_K` has no higher cohomology**, at the level of
the underlying abelian sheaves. -/
theorem subsingleton_H_fieldBaseChange_of_injective (I : EtaleModules.{u, 0} Λ Y.left)
    [Injective I] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (fieldBaseChangeProj Y
        kbar)).obj
      ((etaleModuleUnderlyingAbelian Y.left Λ).obj I)) q) := by
  let W := fieldStageSystem Y kbar
  let D := W ⋙ Scheme.Etale.forget Y.left ⋙ Over.forget Y.left
  let c := fieldStageCone Y kbar
  have hc : IsLimit c := fieldStageConeIsLimit Y kbar
  have : ∀ {i j : (FExt k kbar)ᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) :=
    fun a => isAffineHom_fieldStageMap Y kbar a
  have : CompactSpace (D.obj (op ⊥)) := compactSpace_fieldStage Y kbar ⊥
  have : QuasiSeparatedSpace (D.obj (op ⊥)) := quasiSeparatedSpace_fieldStage Y kbar ⊥
  let UI := (etaleModuleUnderlyingAbelian Y.left Λ).obj I
  let G₀ := (etaleAbelianInverseImage.{u, 0} (W.obj (op ⊥)).hom).obj UI
  have e₀ := (etaleAbelianInverseImageCompIso'.{u, 0} (c.π.app (op ⊥)) (W.obj (op ⊥)).hom
    (fieldBaseChangeProj Y kbar) (fieldStageCone_π_comp_hom Y kbar (op ⊥)).symm).app UI
  refine (subsingleton_H_iff_of_iso e₀ q).2 ⟨fun x x' => ?_⟩
  suffices h : ∀ z : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (c.π.app (op ⊥))).obj G₀) q,
      z = 0 from (h x).trans (h x').symm
  intro z
  obtain ⟨i, h, y, hy⟩ := LimitExt.exists_le_restriction_eq_of_qcqs D c hc ⊥ G₀ q z
  have hW : D.map (homOfLE h).op ≫ (W.obj (op ⊥)).hom = (W.obj (op i)).hom :=
    MorphismProperty.Over.w (W.map (homOfLE h).op)
  have e₁ := (etaleAbelianInverseImageCompIso'.{u, 0} (D.map (homOfLE h).op) (W.obj (op ⊥)).hom
    (W.obj (op i)).hom hW.symm).app UI
  have e₂ := (etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ (W.obj (op i)).hom).app I
  have : Etale (W.obj (op i)).hom := (W.obj (op i)).prop
  have := injective_etaleModuleInverseImage_of_etale Λ (W.obj (op i)).hom I
  have hsub : Subsingleton (Sheaf.H.{u + 1}
      ((etaleAbelianInverseImage.{u, 0} (D.map (homOfLE h).op)).obj G₀) q) :=
    (subsingleton_H_iff_of_iso (e₁.symm ≪≫ e₂) q).2
      (subsingleton_H_etaleModuleUnderlyingAbelian_of_injective Λ _ q hq)
  rw [← hy, Subsingleton.elim y 0, map_zero, Ext.zero_comp]

/-- **`H^q(Y_K, I|_{Y_K}) = 0` for `q > 0` and `I` injective on `Y`**, for `Y` quasi-compact and
quasi-separated over `k` and `K/k` separable algebraic. -/
theorem isZero_rightDerived_fieldBaseChange_of_injective (I : EtaleModules.{u, 0} Λ Y.left)
    [Injective I] (q : ℕ) (hq : 0 < q) :
    IsZero (((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerived q).obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj I)) := by
  let H := (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj I
  have hH : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian _ Λ).obj H) q) :=
    (subsingleton_H_iff_of_iso ((etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ
      (fieldBaseChangeProj Y kbar)).app I) q).1
      (subsingleton_H_fieldBaseChange_of_injective Λ Y kbar I q hq)
  have : Subsingleton ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
      (((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerived q).obj H)) :=
    AddCommGrpCat.isZero_iff_subsingleton.1 ((AddCommGrpCat.isZero_iff_subsingleton.2 hH).of_iso
      ((etaleModuleCohomologyIsoFunctorH Λ q).app H))
  exact ModuleCat.isZero_of_subsingleton _

end Acyclic

end Stacks.EtaleCohomology

end
