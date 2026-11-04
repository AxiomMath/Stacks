module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SetAbelianBaseChangeTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedBaseFieldSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction in degree zero along an extension of a separably closed field

For a morphism of schemes `p : Y ⟶ X` and an abelian sheaf `F` on `X_étale`, restriction
`H⁰(X, F) → H⁰(Y, p⁻¹F)` is, under `H⁰ = Hom(ℤ, -)`, the map of global sections induced by the
unit `F ⟶ p_* p⁻¹ F` of the inverse-image adjunction. When `X` lies over a separably closed field
`k` and `p` is the projection from the scalar extension along an extension `K/k`, this map is
bijective by Stacks Tag 0A3I. So restriction is bijective in degree zero for every abelian sheaf.

## Main results

* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_zero_of_bijective_unit`: the
  reduction of degree-zero restriction to the unit at the final object.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_zero_of_isSepClosed`: the
  bijectivity over a separably closed field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- If the unit of the inverse-image adjunction at `F` is bijective on sections over the final
object, postcomposition with it is bijective on maps out of the constant sheaf `ℤ`. -/
theorem bijective_comp_unit_of_bijective_unit {X Y : Scheme.{u}} (p : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : Function.Bijective (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} p).unit.app
      F).hom.app (op (etaleSiteTerminal X)))) :
    Function.Bijective (fun ψ : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F =>
      ψ ≫ (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} p).unit.app F) := by
  set A := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  set ZX := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A
  set L := etaleAbelianInverseImage.{u, u + 1} p
  set θ := (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} p).unit.app F
  set hT := etaleSiteTerminalIsTerminal X
  let e₁ := (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT).homEquiv A F
  let e₂ := (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT).homEquiv A
    ((etaleAbelianDirectImage.{u, u + 1} p).obj (L.obj F))
  let g : (A ⟶ F.obj.obj (op (etaleSiteTerminal X))) →
      (A ⟶ ((etaleAbelianDirectImage.{u, u + 1} p).obj (L.obj F)).obj.obj
        (op (etaleSiteTerminal X))) := fun a => a ≫ θ.hom.app (op (etaleSiteTerminal X))
  have hg : Function.Bijective g := by
    let u₁ := AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj.obj (op (etaleSiteTerminal X)))
    let u₂ := AddCommGrpCat.uliftZMultiplesAddEquiv
      (((etaleAbelianDirectImage.{u, u + 1} p).obj (L.obj F)).obj.obj
        (op (etaleSiteTerminal X)))
    have : g = u₂.symm ∘ θ.hom.app (op (etaleSiteTerminal X)) ∘ u₁ := by
      funext a
      apply u₂.injective
      simp only [Function.comp_apply, AddEquiv.apply_symm_apply]
      rfl
    rw [this]
    exact u₂.symm.bijective.comp (h.comp u₁.bijective)
  have : (fun ψ : ZX ⟶ F => ψ ≫ θ) = e₂.symm ∘ g ∘ e₁ := by
    funext ψ
    apply e₂.injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply, g, e₁, e₂]
    exact Adjunction.homEquiv_naturality_right _ _ _
  rw [this]
  exact e₂.symm.bijective.comp (hg.comp e₁.bijective)

section Unit

variable {X Y : Scheme.{u}} (p : Y ⟶ X)
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **Degree-zero restriction is the unit on global sections.** If the unit of the inverse-image
adjunction at `F` is bijective on sections over the final object, restriction along `p` is
bijective on `H⁰`. -/
theorem bijective_etaleCohomologyRestrictionMap_zero_of_bijective_unit
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : Function.Bijective (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} p).unit.app
      F).hom.app (op (etaleSiteTerminal X)))) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} p F 0) := by
  set A := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  set ZX := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A
  set L := etaleAbelianInverseImage.{u, u + 1} p
  set adj := etaleAbelianInverseImageDirectImageAdj.{u, u + 1} p
  set c := (etaleAbelianInverseImageConstantIso.{u, u + 1} p).app A
  set θ := adj.unit.app F
  have h4 := bijective_comp_unit_of_bijective_unit p F h
  have h3 : Function.Bijective (fun φ : ZX ⟶ F => L.map φ) := by
    have : (adj.homEquiv ZX (L.obj F)) ∘ (fun φ : ZX ⟶ F => L.map φ) =
        fun ψ : ZX ⟶ F => ψ ≫ θ := by
      funext φ
      simp only [Function.comp_apply, Adjunction.homEquiv_unit, θ]
      exact (adj.unit.naturality φ).symm
    rw [← (adj.homEquiv ZX (L.obj F)).bijective.of_comp_iff', this]
    exact h4
  have h2 : Function.Bijective (fun φ : ZX ⟶ F => c.inv ≫ L.map φ) := by
    have : (fun φ : ZX ⟶ F => c.inv ≫ L.map φ) =
        (fun ψ : L.obj ZX ⟶ L.obj F => c.inv ≫ ψ) ∘ (fun φ : ZX ⟶ F => L.map φ) := rfl
    rw [this]
    refine Function.Bijective.comp ⟨fun a b hab => ?_, fun b => ⟨c.hom ≫ b, by simp⟩⟩ h3
    simpa using congrArg (fun t => c.hom ≫ t) hab
  have h1 : etaleCohomologyRestrictionMap.{u, u + 1, u + 1} p F 0 =
      (fun φ => Ext.mk₀ φ) ∘ (fun φ : ZX ⟶ F => c.inv ≫ L.map φ) ∘ Ext.homEquiv₀ := by
    funext x
    obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjective x
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Ext.homEquiv₀_symm_apply]
    rw [etaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀,
      show Ext.homEquiv₀ (Ext.mk₀ φ) = φ from Ext.homEquiv₀.apply_symm_apply φ]
  rw [show (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} p F 0 : Sheaf.H.{u + 1} F 0 → _) =
    (fun φ => Ext.mk₀ φ) ∘ (fun φ : ZX ⟶ F => c.inv ≫ L.map φ) ∘ Ext.homEquiv₀ from h1]
  exact (Ext.mk₀_bijective _ _).comp (h2.comp Ext.homEquiv₀.bijective)

end Unit

section Comparison

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- The comparison `p⁻¹(F as a set sheaf) ⟶ (p⁻¹F) as a set sheaf`: the adjoint transpose of the
unit of the abelian inverse-image adjunction. -/
def inverseImageForgetComparison (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (smallEtaleInverseImage.{u, 0} p).obj ((etaleForget X).obj F) ⟶
      (etaleForget Y).obj ((etaleAbelianInverseImage.{u, u + 1} p).obj F) :=
  ((smallEtaleInverseImageAdjunction.{u, 0} p).homEquiv _ _).symm
    ((etaleForget X).map ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} p).unit.app F))

/-- The unit of the set-level inverse-image adjunction at the underlying set sheaf of `F`,
followed by the pushforward of `inverseImageForgetComparison p F`, is the underlying map of the
unit `F ⟶ p_* p⁻¹ F` of the abelian inverse-image adjunction. -/
theorem unit_comp_inverseImageForgetComparison
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (smallEtaleInverseImageAdjunction.{u, 0} p).unit.app ((etaleForget X).obj F) ≫
        ((smallEtaleBaseChange p).sheafPushforwardContinuous (Type (u + 1)) X.smallEtaleTopology
          Y.smallEtaleTopology).map (inverseImageForgetComparison p F) =
      (etaleForget X).map ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} p).unit.app F) := by
  have := ((smallEtaleInverseImageAdjunction.{u, 0} p).homEquiv ((etaleForget X).obj F)
    ((etaleForget Y).obj ((etaleAbelianInverseImage.{u, u + 1} p).obj F))).apply_symm_apply
    ((etaleForget X).map ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} p).unit.app F))
  rwa [Adjunction.homEquiv_unit] at this

/-- **Inverse image commutes with passing to underlying sets** (Stacks Tag 00YT on Mathlib's
small étale site): the comparison is an isomorphism. -/
theorem isIso_inverseImageForgetComparison
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (inverseImageForgetComparison p F) := by
  let Φ := smallEtaleBaseChange p
  let _ : ∀ (H : Type (u + 1 + 1)) [Category.{u + 1} H] [HasColimitsOfSize.{u + 1, u + 1} H]
      (P : X.Etaleᵒᵖ ⥤ H), Φ.op.HasPointwiseLeftKanExtension P := fun H _ _ P Y => by
    let _ := hasColimitsOfShape_of_essentiallySmall.{u + 1} (CostructuredArrow Φ.op Y) H
    infer_instance
  let _ : ∀ Y : Y.Etaleᵒᵖ, PreservesColimitsOfShape (CostructuredArrow Φ.op Y)
      (forget AddCommGrpCat.{u + 1}) := fun Y => by
    let _ : IsFiltered (CostructuredArrow Φ.op Y) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence Φ Y.unop)
    let _ : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1}
        (forget AddCommGrpCat.{u + 1})
    exact PreservesFilteredColimitsOfSize.preserves_filtered_colimits
      (CostructuredArrow Φ.op Y)
  let adjMA := Φ.sheafAdjunctionContinuous AddCommGrpCat.{u + 1} X.smallEtaleTopology
    Y.smallEtaleTopology
  let adjMS := Φ.sheafAdjunctionContinuous (Type (u + 1)) X.smallEtaleTopology
    Y.smallEtaleTopology
  let adjA := etaleAbelianInverseImageDirectImageAdj.{u, u + 1} p
  let adjS := smallEtaleInverseImageAdjunction.{u, 0} p
  let eA := adjMA.leftAdjointUniq adjA
  let eS := adjMS.leftAdjointUniq adjS
  have hm := Φ.isIso_sheafPullbackSheafComposeHom AddCommGrpCat.{u + 1} X.smallEtaleTopology
    Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F
  have key : inverseImageForgetComparison p F = eS.inv.app _ ≫
      Φ.sheafPullbackSheafComposeHom AddCommGrpCat.{u + 1} X.smallEtaleTopology
        Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F ≫
      (etaleForget Y).map (eA.hom.app F) := by
    apply (adjS.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      unit_comp_inverseImageForgetComparison, Functor.map_comp, Functor.map_comp,
      ← Category.assoc, ← Category.assoc]
    symm
    have h1 : adjS.unit.app ((etaleForget X).obj F) ≫
        ((smallEtaleBaseChange p).sheafPushforwardContinuous (Type (u + 1)) X.smallEtaleTopology
          Y.smallEtaleTopology).map (eS.inv.app _) = adjMS.unit.app _ := by
      rw [← Adjunction.unit_leftAdjointUniq_hom_app adjMS adjS, Category.assoc,
        ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
      exact Category.comp_id _
    rw [h1, Φ.unit_comp_pushforward_map_sheafPullbackSheafComposeHom]
    have h2 : adjMA.unit.app F ≫ (etaleAbelianDirectImage.{u, u + 1} p).map (eA.hom.app F) =
        adjA.unit.app F := Adjunction.unit_leftAdjointUniq_hom_app adjMA adjA F
    rw [← h2, Functor.map_comp]
    rfl
  rw [key]
  infer_instance

end Comparison

section SepClosed

/-- Restriction of global sections to a final object is an isomorphism. -/
theorem isIso_ΓRes_of_isTerminal {Z : Scheme.{u}} (G : Sheaf Z.smallEtaleTopology (Type (u + 1)))
    {V : Z.Etale} (hV : IsTerminal V) : IsIso (G.ΓRes (op V)) := by
  let hI : IsInitial (op V) := hV.op
  have h := G.isLimitConeΓ.conePointUniqueUpToIso_hom_comp (limitOfDiagramInitial hI G.obj)
    (op V)
  have h' : (coneOfDiagramInitial hI G.obj).π.app (op V) = 𝟙 _ := by
    simp [coneOfDiagramInitial, hI.hom_ext (hI.to (op V)) (𝟙 _)]
  rw [h'] at h
  have h'' : G.ΓRes (op V) =
      (G.isLimitConeΓ.conePointUniqueUpToIso (limitOfDiagramInitial hI G.obj)).hom := by
    rw [← Sheaf.coneΓ_π_app, ← h]
    exact (Category.comp_id _).symm
  rw [h'']
  exact Iso.isIso_hom _

/-- **Degree-zero restriction along an extension of a separably closed field is bijective**, for
every abelian sheaf (Stacks Tag 0A3I). -/
@[sga "4 XII 5.4" "(i), special case"]
theorem bijective_etaleCohomologyRestrictionMap_zero_of_isSepClosed
    (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (scalarExtension k K f).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
      (scalarExtensionFst k K f) F 0) := by
  set p := scalarExtensionFst k K f
  have : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    (AlgebraicGeometry.geometricallyConnected_spec_iff k K).2
      ((Algebra.isGeometricallyConnected_iff_connectedSpace_primeSpectrum k K).2 inferInstance)
  have hiso := isIso_globalSectionsSmallEtaleInverseImage.{u, 0} p
    (universally_isQuotientMap_of_flat_quasiCompact _)
  apply bijective_etaleCohomologyRestrictionMap_zero_of_bijective_unit
  set V := etaleSiteTerminal X
  have hV := etaleSiteTerminalIsTerminal X
  have hset : Function.Bijective (smallEtaleUnitApp.{u, 0} p ((etaleForget X).obj F) V) := by
    have e := globalSectionsSmallEtaleInverseImage_app_comp_ΓRes.{u, 0} p
      ((etaleForget X).obj F) V
    have h1 := isIso_ΓRes_of_isTerminal ((etaleForget X).obj F) hV
    have h2 := isIso_ΓRes_of_isTerminal
      ((smallEtaleInverseImage.{u, 0} p).obj ((etaleForget X).obj F))
      (isTerminalSmallEtaleBaseChangeObj p hV)
    have : smallEtaleUnitApp.{u, 0} p ((etaleForget X).obj F) V =
        inv (((etaleForget X).obj F).ΓRes (op V)) ≫
          (globalSectionsSmallEtaleInverseImage.{u, 0} p).app ((etaleForget X).obj F) ≫
          ((smallEtaleInverseImage.{u, 0} p).obj ((etaleForget X).obj F)).ΓRes
            (op ((smallEtaleBaseChange p).obj V)) := by
      rw [e, IsIso.inv_hom_id_assoc]
    rw [this]
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hcmp := isIso_inverseImageForgetComparison p F
  let R := (smallEtaleBaseChange p).sheafPushforwardContinuous (Type (u + 1))
    X.smallEtaleTopology (scalarExtension k K f).smallEtaleTopology
  have hR : IsIso ((R.map (inverseImageForgetComparison p F)).hom.app (op V)) := by
    have : IsIso (R.map (inverseImageForgetComparison p F)) := inferInstance
    exact (inferInstance : IsIso (((sheafToPresheaf _ _).map
      (R.map (inverseImageForgetComparison p F))).app (op V)))
  have hfun : ⇑(((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} p).unit.app F).hom.app
      (op V)) = ⇑((R.map (inverseImageForgetComparison p F)).hom.app (op V)) ∘
        smallEtaleUnitApp.{u, 0} p ((etaleForget X).obj F) V := by
    funext x
    exact (congrFun (congrArg (fun φ => φ.hom.app (op V))
      (unit_comp_inverseImageForgetComparison p F)) x).symm
  rw [hfun]
  exact ((ConcreteCategory.isIso_iff_bijective _).mp hR).comp hset

end SepClosed

end Stacks.EtaleCohomology

end
