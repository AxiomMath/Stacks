module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ComplexSystemResidual
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ComplexSystemColimitSupport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.OpenToOpenExtensionAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.WellOrderedCoverSystem
public import StacksFrontier.CategoryTheory.TransfiniteCoherentSystem
import StacksCore.Tactic.StacksAttribute

/-!
# The transfinite recursion of Tag 0D6B

Let `(X, 𝒪_X)` be a ringed space, let `E` be a well ordered set, let `W : E → Opens X` be an
increasing family of opens, let `K_α` be objects of `D(𝒪_{W_α})` without negative self-Ext and
let `ρ^α_β : K_α|_{W_β} ≅ K_β` be isomorphisms satisfying the cocycle condition.  This file
carries out the proof of [Stacks, Tag 0D6B]: choose K-injective representatives `I_α` of the
`K_α`, and construct by transfinite recursion maps of complexes
`τ_{β,α} : (j_β)_! I_β ⟶ (j_α)_! I_α` which compose strictly, restrict to quasi-isomorphisms on
`W_β`, and represent the inverses of the `ρ^α_β`.  At a stage `α` the colimit of the earlier
stages, restricted to their union `⋃_{β < α} W_β`, is a second solution there of the datum
displayed on the earlier stages; uniqueness of a solution ([Stacks, Tag 0D68]) identifies it
with the restriction of `K_α`, and K-injectivity of `I_α` realises that identification by a map
of complexes out of the colimit.  The colimit of the whole system represents the glued object.

## Main results

* `Stacks.DerivedGlueing.exists_iso_of_isCompatibleBelow`: two objects over the union of the
  stages below `α`, each with compatible identifications of its restrictions with the `K_β`, are
  identified compatibly.
* `Stacks.DerivedGlueing.hasStep`: the step of the recursion.
* `Stacks.DerivedGlueing.producesComplexSystem`: the system of complexes exists.
* `Stacks.DerivedGlueing.gluesAlongWellOrderedCover`: the glueing property over a well ordered
  increasing cover, for index sets in any universe; an index set in a larger universe is reduced
  to the range of the family of opens, reindexed by the least stage attaining each open.
* `Stacks.DerivedGlueing.exists_glueing_of_wellOrderedCover`: **[Stacks, Tag 0D6B]**.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules

namespace Stacks.DerivedGlueing

universe v u

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### Complex-level identities -/

/-- The unit of extension by zero and restriction, on complexes, is the identification
`Stacks.DerivedGlueing.jShriekJStarIso`. -/
theorem jShriekComplexAdjunction_unit_app (U : Opens X.carrier)
    (M : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) :
    (Adjunction.mapHomologicalComplexAdjunction (jShriekAdjunction U (underlyingRingSheaf X))
      (ComplexShape.up ℤ)).unit.app M = (jShriekJStarIso X U).hom.app M := by
  ext n
  rw [jShriekJStarIso_hom_app_f]
  rfl

/-- The comparison of restriction with extension by zero followed by restriction is the
identity. -/
theorem openModuleRestrictionMapIso_inv_app_eq_id (V U : Opens X.carrier) (hVU : V ≤ U)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) :
    (openModuleRestrictionMapIso X V U hVU).inv.app C = 𝟙 _ := by
  ext n : 1
  rw [HomologicalComplex.id_f]
  exact openModuleRestrictionMapIso_inv_app_f X V U hVU C n

/-- The comparison of restriction with extension by zero followed by restriction is the
identity. -/
theorem openModuleRestrictionMapIso_hom_app_eq_id (V U : Opens X.carrier) (hVU : V ≤ U)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) :
    (openModuleRestrictionMapIso X V U hVU).hom.app C = 𝟙 _ := by
  ext n : 1
  rw [HomologicalComplex.id_f]
  exact openModuleRestrictionMapIso_hom_app_f X V U hVU C n

/-- Composing with the comparison of restriction with extension by zero followed by
restriction does nothing. -/
@[simp]
theorem comp_openModuleRestrictionMapIso_inv_app (V U : Opens X.carrier) (hVU : V ≤ U)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ)
    {Z : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X V)) ℤ}
    (f : Z ⟶ ((jStar V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) :
    f ≫ (openModuleRestrictionMapIso X V U hVU).inv.app C = f := by
  rw [openModuleRestrictionMapIso_inv_app_eq_id]
  exact Category.comp_id f

/-- Composing with the comparison of restriction with extension by zero followed by
restriction does nothing. -/
@[simp]
theorem openModuleRestrictionMapIso_hom_app_comp (V U : Opens X.carrier) (hVU : V ≤ U)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ)
    {Z : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X V)) ℤ}
    (f : ((jStar V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ⟶ Z) :
    (openModuleRestrictionMapIso X V U hVU).hom.app C ≫ f = f := by
  rw [openModuleRestrictionMapIso_hom_app_eq_id]
  exact Category.id_comp f

/-- **Restricting a map out of an extension by zero is restricting its transpose.** For opens
`B ≤ V ≤ U` and a map of complexes `s : (j_V)_! C ⟶ (j_U)_! J`, the restriction of `s` to `B`
is the restriction from `V` to `B` of its transpose along `j_{V,!} ⊣ j_V^*`, followed by the
comparison of restriction in two steps with direct restriction. -/
theorem jStar_map_eq_restriction_map_homEquiv (B V U : Opens X.carrier) (hBV : B ≤ V)
    (hVU : V ≤ U) (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X V)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ)
    (s : ((jShriek V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ⟶
      ((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :
    ((jStar B (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map s =
      ((openModuleRestriction X B V hBV).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Adjunction.mapHomologicalComplexAdjunction
            (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv C _ s) ≫
        (NatTrans.mapHomologicalComplex (openModuleRestrictionComparison X B V U hBV hVU)
          (ComplexShape.up ℤ)).app J := by
  ext n : 1
  calc _ = (jStar B (underlyingRingSheaf X)).map (s.f n) := rfl
    _ = (jStar B (underlyingRingSheaf X)).map
          (((jShriekAdjunction V (underlyingRingSheaf X)).homEquiv _ _).symm
            ((jShriekAdjunction V (underlyingRingSheaf X)).homEquiv _ _ (s.f n))) := by
        rw [Equiv.symm_apply_apply]
    _ = _ := by
        rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_unit, Functor.map_comp]
        rfl


/-- If `p ≫ q ≫ e.hom = l.hom` for isomorphisms `e` and `l`, then `e.inv = l.inv ≫ p ≫ q`. -/
private theorem inv_eq_of_comp_comp_hom_eq {C : Type*} [Category C] {A B M N : C} {p : A ⟶ B}
    {q : B ⟶ M} {e : M ≅ N} (l : A ≅ N) (h : p ≫ q ≫ e.hom = l.hom) :
    e.inv = l.inv ≫ p ≫ q := by
  rw [← cancel_mono e.hom]
  simp [h]

/-! ### The glued identification, through forward maps -/

section Leg

variable {E : Type u} [LinearOrder E] [Nonempty E] (V : Opens X.carrier)
  (W : E → Opens X.carrier)
  (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
  (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
  (hsupp : ∀ α : E, F.obj α ≅
    ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (I α))
  (sIso : ((jShriek V (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (glueingComplexOver V F) ≅ colimit F)
  (hqi : ∀ (β α : E) (h : β ≤ α),
    QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (F.map h.hom)))
  (hWV : ∀ α : E, W α ≤ V)

/-- **The inverse of the glued identification at a stage is the transpose of the colimit leg.**
The inverse of `Stacks.DerivedGlueing.glueingComplexRestrictionIsoOver` at `α` is the class of
the composite of the unit of extension by zero along `W α` with the restriction to `W α` of the
colimit inclusion at `α`, read through the support isomorphism of the colimit on `V`. -/
theorem glueingComplexRestrictionIsoOver_inv (α : E) :
    (glueingComplexRestrictionIsoOver V W F I hsupp sIso hqi hWV α).inv =
      DerivedCategory.Q.map ((jShriekJStarIso X (W α)).hom.app (I α) ≫
          ((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((hsupp α).inv ≫ colimit.ι F α ≫ sIso.inv)) := by
  have h := Q_map_colimit_ι_comp_glueingComplexRestrictionIsoOver V W F I hsupp sIso hqi hWV α
  have hinv := inv_eq_of_comp_comp_hom_eq (DerivedCategory.Q.mapIso
    (glueingComplexLocalIso W F I hsupp α)) h
  rw [hinv]
  simp only [glueingComplexLocalIso, glueingComplexRestrictIsoOver, Iso.trans_inv,
    Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv, Functor.map_comp, Category.assoc,
    comp_openModuleRestrictionMapIso_inv_app]
  rfl

end Leg

/-! ### Comparison of two solutions below a stage, indexed by the stages -/

section BelowStage

variable (S : LocallyGiven X) {E : Type v} [LinearOrder E] [WellFoundedLT E]
  (W : E → Opens X.carrier) (hmono : ∀ β α : E, β < α → W β ≤ W α)
  (K : ∀ α : E, OpenDerivedCategory X (W α))
  (rho : ∀ (β α : E) (h : β < α),
    (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β)
  (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
    (rho γ α (hγβ.trans hβα)).hom =
      (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ)
          (hmono β α hβα)).hom.app (K α) ≫
        (S.restriction (W γ) (W β) (hmono γ β hγβ)).map (rho β α hβα).hom ≫
          (rho γ β hγβ).hom)

/-- The union of the stages strictly below a stage. -/
def stageSup (α : E) : Opens X.carrier :=
  ⨆ (β : E) (_ : β < α), W β

omit [WellFoundedLT E] in
/-- Every stage strictly below `α` is contained in the union of the stages below `α`. -/
theorem le_stageSup {β α : E} (h : β < α) : W β ≤ stageSup W α :=
  le_iSup₂ (f := fun (γ : E) (_ : γ < α) => W γ) β h

/-- **Identifications of the restrictions of an object over the stages below `α` with the
prescribed objects, compatible with the prescribed transitions.** -/
def IsCompatibleBelow (α : E) (G : OpenDerivedCategory X (stageSup W α))
    (σ : ∀ (β : E) (hβ : β < α),
      (S.restriction (W β) (stageSup W α) (le_stageSup W hβ)).obj G ≅ K β) : Prop :=
  ∀ (γ β : E) (hγβ : γ < β) (hβ : β < α),
    (S.restrictionComp (W γ) (W β) (stageSup W α) (hmono γ β hγβ)
        (le_stageSup W hβ)).hom.app G ≫
      (S.restriction (W γ) (W β) (hmono γ β hγβ)).map (σ β hβ).hom ≫ (rho γ β hγβ).hom =
    (σ γ (hγβ.trans hβ)).hom

/-- The least index attaining an open which is a stage strictly below `α` is itself strictly
below `α`. -/
theorem coverIndex_lt_of_mem_image_Iio {α : E} {U : Opens X.carrier}
    (hU : U ∈ W '' Set.Iio α) :
    coverIndex W U (image_Iio_subset_range W α hU) < α := by
  obtain ⟨b, hb, hbU⟩ := hU
  exact lt_of_le_of_lt (leastIndex_le W _ hbU) hb

omit [WellFoundedLT E] in
/-- The core of the compatibility of `Stacks.DerivedGlueing.solutionOverBelowOfCompatible`,
with every stage and open a variable. -/
theorem solutionOverBelow_compatibility_aux (α : E) (G : OpenDerivedCategory X (stageSup W α))
    (σ : ∀ (β : E) (hβ : β < α),
      (S.restriction (W β) (stageSup W α) (le_stageSup W hβ)).obj G ≅ K β)
    (hσ : IsCompatibleBelow S W hmono K rho α G σ)
    (T V : Opens X.carrier) (hTV : T ≤ V) (c c' : E) (hcc' : c ≤ c') (hc' : c' < α)
    (hVc' : V ≤ W c') (hTc : T ≤ W c) (hVO : V ≤ stageSup W α) :
    (S.restrictionComp T V (stageSup W α) hTV hVO).hom.app G ≫
        (S.restriction T V hTV).map
          ((S.restrictionComp V (W c') (stageSup W α) hVc' (le_stageSup W hc')).hom.app G ≫
            (S.restriction V (W c') hVc').map (σ c' hc').hom) ≫
        (S.restrictionComp T V (W c') hTV hVc').inv.app (K c') ≫
        (coverTransferIso S W hmono K rho T hcc' hTc).hom =
      (S.restrictionComp T (W c) (stageSup W α) hTc
          (le_stageSup W (lt_of_le_of_lt hcc' hc'))).hom.app G ≫
        (S.restriction T (W c) hTc).map (σ c (lt_of_le_of_lt hcc' hc')).hom := by
  have hpent := S.restrictionComp_pentagon T V (W c') (stageSup W α) hTV hVc'
    (le_stageSup W hc') G
  have hnat := (S.restrictionComp T V (W c') hTV hVc').inv.naturality (σ c' hc').hom
  simp only [Functor.comp_map] at hnat
  have hstep : (S.restrictionComp T V (stageSup W α) hTV hVO).hom.app G ≫
        (S.restriction T V hTV).map
          ((S.restrictionComp V (W c') (stageSup W α) hVc' (le_stageSup W hc')).hom.app G ≫
            (S.restriction V (W c') hVc').map (σ c' hc').hom) ≫
        (S.restrictionComp T V (W c') hTV hVc').inv.app (K c') =
      (S.restrictionComp T (W c') (stageSup W α) (hTV.trans hVc')
          (le_stageSup W hc')).hom.app G ≫
        (S.restriction T (W c') (hTV.trans hVc')).map (σ c' hc').hom := by
    rw [Functor.map_comp, Category.assoc, hnat, ← Category.assoc, ← Category.assoc, ← hpent,
      Category.assoc]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hstep]
  rcases eq_or_lt_of_le hcc' with rfl | hlt
  · rw [coverTransferIso_self, Category.comp_id]
  · rw [coverTransferIso_hom_of_lt S W hmono K rho T hcc' hTc hlt]
    have hnat' := (S.restrictionComp T (W c) (W c') hTc (hmono c c' hlt)).hom.naturality
      (σ c' hc').hom
    simp only [Functor.comp_map] at hnat'
    have hpent' := S.restrictionComp_pentagon T (W c) (W c') (stageSup W α) hTc
      (hmono c c' hlt) (le_stageSup W hc') G
    rw [← hσ c c' hlt hc', reassoc_of% hnat', reassoc_of% hpent']
    simp only [Functor.map_comp]

/-- **A family of compatible identifications below `α` is a solution over the union of the stages
below `α`**, of the datum displayed on those stages. -/
def solutionOverBelowOfCompatible (α : E) (G : OpenDerivedCategory X (stageSup W α))
    (σ : ∀ (β : E) (hβ : β < α),
      (S.restriction (W β) (stageSup W α) (le_stageSup W hβ)).obj G ≅ K β)
    (hσ : IsCompatibleBelow S W hmono K rho α G σ) :
    SolutionOver (belowStageSystem S W hmono K rho hcocycle α) (stageSup W α) where
  obj := G
  rho U hU hUO :=
    (S.restrictionComp U (W (coverIndex W U (image_Iio_subset_range W α hU))) (stageSup W α)
        (le_coverIndex_apply W U _) (le_stageSup W (coverIndex_lt_of_mem_image_Iio W hU))).app G ≪≫
      (S.restriction U (W (coverIndex W U (image_Iio_subset_range W α hU)))
        (le_coverIndex_apply W U _)).mapIso (σ _ (coverIndex_lt_of_mem_image_Iio W hU))
  compatibility V T hTV hV hT hVO := by
    have := solutionOverBelow_compatibility_aux S W hmono K rho α G σ hσ T V hTV
      (coverIndex W T (image_Iio_subset_range W α hT))
      (coverIndex W V (image_Iio_subset_range W α hV))
      (coverIndex_monotone W hmono _ _ hTV) (coverIndex_lt_of_mem_image_Iio W hV)
      (le_coverIndex_apply W V _) (le_coverIndex_apply W T _) hVO
    exact this

omit [WellFoundedLT E] in
/-- The core of the passage back from an isomorphism of solutions to the stages, with every
stage a variable. -/
theorem compatible_of_solutionOverBelow_aux (α : E)
    {G₁ G₂ : OpenDerivedCategory X (stageSup W α)}
    (σ₁ : ∀ (β : E) (hβ : β < α),
      (S.restriction (W β) (stageSup W α) (le_stageSup W hβ)).obj G₁ ≅ K β)
    (σ₂ : ∀ (β : E) (hβ : β < α),
      (S.restriction (W β) (stageSup W α) (le_stageSup W hβ)).obj G₂ ≅ K β)
    (hσ₁ : IsCompatibleBelow S W hmono K rho α G₁ σ₁)
    (hσ₂ : IsCompatibleBelow S W hmono K rho α G₂ σ₂) (φ : G₁ ⟶ G₂)
    (c β : E) (hcβ : c ≤ β) (hβ : β < α) (hβc : W β ≤ W c)
    (h : (S.restriction (W β) (stageSup W α) (le_stageSup W hβ)).map φ ≫
        (S.restrictionComp (W β) (W c) (stageSup W α) hβc
          (le_stageSup W (lt_of_le_of_lt hcβ hβ))).hom.app G₂ ≫
        (S.restriction (W β) (W c) hβc).map (σ₂ c (lt_of_le_of_lt hcβ hβ)).hom =
      (S.restrictionComp (W β) (W c) (stageSup W α) hβc
          (le_stageSup W (lt_of_le_of_lt hcβ hβ))).hom.app G₁ ≫
        (S.restriction (W β) (W c) hβc).map (σ₁ c (lt_of_le_of_lt hcβ hβ)).hom) :
    (S.restriction (W β) (stageSup W α) (le_stageSup W hβ)).map φ ≫ (σ₂ β hβ).hom =
      (σ₁ β hβ).hom := by
  have hc : c < α := lt_of_le_of_lt hcβ hβ
  have hnat :=
    (S.restrictionComp (W β) (W c) (stageSup W α) hβc (le_stageSup W hc)).hom.naturality φ
  simp only [Functor.comp_map] at hnat
  rw [reassoc_of% hnat, cancel_epi, ← Functor.map_comp] at h
  have hc' : (S.restriction (W c) (stageSup W α) (le_stageSup W hc)).map φ ≫ (σ₂ c hc).hom =
      (σ₁ c hc).hom :=
    restriction_map_injective_of_antisymm S hβc (apply_le_apply_of_le hmono hcβ) h
  rcases eq_or_lt_of_le hcβ with rfl | hlt
  · exact hc'
  · have e₁ := hσ₁ c β hlt hβ
    have e₂ := hσ₂ c β hlt hβ
    have hnat2 := (S.restrictionComp (W c) (W β) (stageSup W α) (hmono c β hlt)
      (le_stageSup W hβ)).hom.naturality φ
    simp only [Functor.comp_map] at hnat2
    apply restriction_map_injective_of_antisymm S (hmono c β hlt) hβc
    rw [← cancel_epi ((S.restrictionComp (W c) (W β) (stageSup W α) (hmono c β hlt)
        (le_stageSup W hβ)).hom.app G₁), ← cancel_mono (rho c β hlt).hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% hnat2, e₂, e₁, hc']

include hcocycle in
/-- **Two compatible families of identifications below a stage are related by an isomorphism.**
Let `W` be a well ordered increasing family of opens, `K β` objects without negative self-Ext
and `ρ` transitions satisfying the cocycle condition.  Two objects over the union of the stages
strictly below `α`, each with identifications of its restrictions to those stages with the `K β`
compatible with the `ρ`, are related by an isomorphism compatible with the identifications.

This is the uniqueness clause of [Stacks, Tag 0D68] read on the stages below `α` —
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_covers` for
`Stacks.DerivedGlueing.belowStageSystem` — transported from the opens back to the stages. -/
theorem exists_iso_of_isCompatibleBelow
    (hExt : ∀ (α : E) (i : ℤ), i < 0 → Subsingleton (ShiftedHom (K α) (K α) i)) (α : E)
    (G₁ G₂ : OpenDerivedCategory X (stageSup W α))
    (σ₁ : ∀ (β : E) (hβ : β < α),
      (S.restriction (W β) (stageSup W α) (le_stageSup W hβ)).obj G₁ ≅ K β)
    (σ₂ : ∀ (β : E) (hβ : β < α),
      (S.restriction (W β) (stageSup W α) (le_stageSup W hβ)).obj G₂ ≅ K β)
    (hσ₁ : IsCompatibleBelow S W hmono K rho α G₁ σ₁)
    (hσ₂ : IsCompatibleBelow S W hmono K rho α G₂ σ₂) :
    ∃ φ : G₁ ≅ G₂, ∀ (β : E) (hβ : β < α),
      (S.restriction (W β) (stageSup W α) (le_stageSup W hβ)).map φ.hom ≫ (σ₂ β hβ).hom =
        (σ₁ β hβ).hom := by
  have hcov : stageSup W α = sSup {T | T ∈ W '' Set.Iio α ∧ T ≤ stageSup W α} :=
    le_antisymm (iSup₂_le fun β hβ => le_sSup ⟨⟨β, hβ, rfl⟩, le_stageSup W hβ⟩)
      (sSup_le fun _ hT => hT.2)
  obtain ⟨φ, hφ, -⟩ := hasUniqueSolutionOverIso_of_covers
    (belowStageSystem S W hmono K rho hcocycle α) (inf_eq_sSup_image_Iio W hmono α)
    (stageSup W α) hcov (inf_eq_sSup_image_Iio W hmono α)
    (fun V hV i hi => subsingleton_shiftedHom_coverSystemObj S W K hExt V
      (image_Iio_subset_range W α hV) i hi)
    (solutionOverBelowOfCompatible S W hmono K rho hcocycle α G₁ σ₁ hσ₁)
    (solutionOverBelowOfCompatible S W hmono K rho hcocycle α G₂ σ₂ hσ₂)
  refine ⟨φ, fun β hβ => ?_⟩
  exact compatible_of_solutionOverBelow_aux S W hmono K rho α σ₁ σ₂ hσ₁ hσ₂ φ.hom
    (coverIndex W (W β) (image_Iio_subset_range W α ⟨β, hβ, rfl⟩)) β
    (leastIndex_le W _ rfl) hβ (le_coverIndex_apply W (W β) _)
    (hφ (W β) ⟨β, hβ, rfl⟩ (le_stageSup W hβ))

end BelowStage

/-! ### The comparison of the displayed restriction with restriction of complexes -/

/-- The field `restrictionFactors` of a system at a complex, with its source written as a
displayed restriction and its target as the class of the restriction of the extension by zero. -/
def restrictionFactorsIso (S : LocallyGiven X) (V U : Opens X.carrier) (hVU : V ≤ U)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) :
    (S.restriction V U hVU).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj (((jStar V (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)) :=
  (S.restrictionFactors V U hVU).app C

/-- `restrictionFactorsIso` is natural in the complex. -/
theorem restrictionFactorsIso_naturality (S : LocallyGiven X) (V U : Opens X.carrier)
    (hVU : V ≤ U) {C D : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ}
    (f : C ⟶ D) :
    (S.restriction V U hVU).map (DerivedCategory.Q.map f) ≫
        (restrictionFactorsIso S V U hVU D).hom =
      (restrictionFactorsIso S V U hVU C).hom ≫ DerivedCategory.Q.map
        (((jStar V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)) :=
  (S.restrictionFactors V U hVU).hom.naturality f

/-- The comparison of restriction in two steps with direct restriction, on complexes: the
counit of extension by zero along the middle open. -/
abbrev restrictionComparisonC (B V U : Opens X.carrier)
    (J : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) :
    ((jStar B (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((jShriek V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((jStar V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj J))) ⟶
      ((jStar B (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
  ((jStar B (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((Adjunction.mapHomologicalComplexAdjunction (jShriekAdjunction V (underlyingRingSheaf X))
      (ComplexShape.up ℤ)).counit.app
        (((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J))

/-- For opens `B ≤ V ≤ U`, `restrictionFactorsIso` for `B ≤ U` is the composite of those for
`V ≤ U` and `B ≤ V`, read through the composition isomorphism of restrictions and the
comparison `restrictionComparisonC` of restrictions of complexes. -/
theorem restrictionFactorsIso_comp (S : LocallyGiven X) (B V U : Opens X.carrier)
    (hBV : B ≤ V) (hVU : V ≤ U)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) :
    (S.restrictionComp B V U hBV hVU).hom.app (DerivedCategory.Q.obj C) ≫
        (S.restriction B V hBV).map (restrictionFactorsIso S V U hVU C).hom ≫
        (restrictionFactorsIso S B V hBV
          (((jStar V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj C))).hom ≫
        DerivedCategory.Q.map (restrictionComparisonC B V U C) =
      (restrictionFactorsIso S B U (hBV.trans hVU) C).hom :=
  S.restrictionCompFactors' B V U hBV hVU C

/-- **Restricting a map out of an extension by zero is restricting its transpose.** -/
theorem jStar_map_eq_jStar_map_homEquiv (B V U : Opens X.carrier)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X V)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ)
    (s : ((jShriek V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ⟶
      ((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :
    ((jStar B (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map s =
      ((jStar B (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((jShriek V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((Adjunction.mapHomologicalComplexAdjunction
              (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv C _ s)) ≫
        restrictionComparisonC B V U J := by
  rw [restrictionComparisonC, ← Functor.map_comp, ← Adjunction.homEquiv_counit,
    Equiv.symm_apply_apply]

/-! ### The transpose of a map out of the colimit of the earlier stages -/

section Transpose

variable {E : Type u} [LinearOrder E] [Nonempty E] (V U : Opens X.carrier) (hVU : V ≤ U)
  (W : E → Opens X.carrier)
  (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
  (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
  (hsupp : ∀ α : E, F.obj α ≅
    ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (I α))
  (sIso : ((jShriek V (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (glueingComplexOver V F) ≅ colimit F)
  (hqi : ∀ (β α : E) (h : β ≤ α),
    QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (F.map h.hom)))
  (hWV : ∀ α : E, W α ≤ V)
  (J : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ)

/-- The glued identification over `V` at a stage, on complexes, with its source written as the
class of the restriction of the extension by zero. -/
def glueingLegIso (α : E) :
    DerivedCategory.Q.obj (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((jShriek V (underlyingRingSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (glueingComplexOver V F))) ≅
      DerivedCategory.Q.obj (I α) :=
  glueingComplexRestrictionIsoOver V W F I hsupp sIso hqi hWV α

/-- The inverse of `glueingLegIso` is the class of the unit of the adjunction between extension
by zero and restriction, followed by the restriction of the colimit leg at `α`. -/
theorem glueingLegIso_inv (α : E) :
    (glueingLegIso V W F I hsupp sIso hqi hWV α).inv =
      DerivedCategory.Q.map ((Adjunction.mapHomologicalComplexAdjunction
          (jShriekAdjunction (W α) (underlyingRingSheaf X)) (ComplexShape.up ℤ)).unit.app (I α) ≫
        ((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((hsupp α).inv ≫ colimit.ι F α ≫ sIso.inv)) := by
  rw [jShriekComplexAdjunction_unit_app]
  exact glueingComplexRestrictionIsoOver_inv V W F I hsupp sIso hqi hWV α

/-- **The transpose of a map out of the colimit, read at a stage.** Let `s` be a map of complexes
from the extension by zero of the glued complex over `V` to the extension by zero of a complex
`J` on `U ⊇ V`.  The class of the transpose, along extension by zero from `W β`, of the colimit
inclusion at `β` followed by `s` is the inverse of the glued identification at `β` followed by
the restriction to `W β` of the class of the transpose of `s`. -/
theorem Q_map_homEquiv_colimit_ι_comp (S : LocallyGiven X)
    (s : ((jShriek V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (glueingComplexOver V F) ⟶
      ((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
    (β : E) :
    DerivedCategory.Q.map ((Adjunction.mapHomologicalComplexAdjunction
        (jShriekAdjunction (W β) (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv (I β) _
          (((hsupp β).inv ≫ colimit.ι F β ≫ sIso.inv) ≫ s)) =
      (glueingLegIso V W F I hsupp sIso hqi hWV β).inv ≫
        (restrictionFactorsIso S (W β) V (hWV β) (glueingComplexOver V F)).inv ≫
        (S.restriction (W β) V (hWV β)).map
          (DerivedCategory.Q.map ((Adjunction.mapHomologicalComplexAdjunction
              (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv _ _ s) ≫
            (restrictionFactorsIso S V U hVU J).inv) ≫
        (S.restrictionComp (W β) V U (hWV β) hVU).inv.app (DerivedCategory.Q.obj J) ≫
        (restrictionFactorsIso S (W β) U ((hWV β).trans hVU) J).hom := by
  have hA := glueingLegIso_inv V W F I hsupp sIso hqi hWV β
  have hB := jStar_map_eq_jStar_map_homEquiv (W β) V U (glueingComplexOver V F) J s
  have hC := restrictionFactorsIso_comp S (W β) V U (hWV β) hVU J
  have hN := restrictionFactorsIso_naturality S (W β) V (hWV β)
    ((Adjunction.mapHomologicalComplexAdjunction
      (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv _ _ s)
  have hD : (restrictionFactorsIso S (W β) V (hWV β)
        (((jStar V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((jShriek U (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J))).hom ≫
        DerivedCategory.Q.map (restrictionComparisonC (W β) V U J) =
      (S.restriction (W β) V (hWV β)).map (restrictionFactorsIso S V U hVU J).inv ≫
        (S.restrictionComp (W β) V U (hWV β) hVU).inv.app (DerivedCategory.Q.obj J) ≫
        (restrictionFactorsIso S (W β) U ((hWV β).trans hVU) J).hom := by
    rw [← hC]
    simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have e1 : (Adjunction.mapHomologicalComplexAdjunction
        (jShriekAdjunction (W β) (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv (I β) _
          (((hsupp β).inv ≫ colimit.ι F β ≫ sIso.inv) ≫ s) =
      ((Adjunction.mapHomologicalComplexAdjunction
          (jShriekAdjunction (W β) (underlyingRingSheaf X)) (ComplexShape.up ℤ)).unit.app (I β) ≫
        ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((hsupp β).inv ≫ colimit.ι F β ≫ sIso.inv)) ≫
        ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map s := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [e1, Functor.map_comp, ← hA, hB, Functor.map_comp, Iso.cancel_iso_inv_left]
  rw [Functor.map_comp, Category.assoc]
  refine ((Iso.inv_hom_id_assoc
    (restrictionFactorsIso S (W β) V (hWV β) (glueingComplexOver V F)) _).symm.trans ?_).trans
    (congrArg (fun k => (restrictionFactorsIso S (W β) V (hWV β) (glueingComplexOver V F)).inv ≫
      (S.restriction (W β) V (hWV β)).map (DerivedCategory.Q.map
        ((Adjunction.mapHomologicalComplexAdjunction (jShriekAdjunction V (underlyingRingSheaf X))
          (ComplexShape.up ℤ)).homEquiv _ _ s)) ≫ k) hD)
  exact congrArg (fun k => (restrictionFactorsIso S (W β) V (hWV β)
    (glueingComplexOver V F)).inv ≫ k) ((reassoc_of% hN) _).symm

/-- The transition the system of complexes determines, on complexes, with its source written as
the class of the restriction of the extension by zero. -/
def transitionLegIso {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    DerivedCategory.Q.obj (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (I α))) ≅
      DerivedCategory.Q.obj (I β) :=
  glueingComplexTransitionIso W F I hsupp hqi hβα h

/-- The inverse of `transitionLegIso` is the class of the transpose, along extension by zero,
of the transition map `F.map h.hom` of the system. -/
theorem transitionLegIso_inv {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    (transitionLegIso W F I hsupp hqi hβα h).inv =
      DerivedCategory.Q.map ((Adjunction.mapHomologicalComplexAdjunction
          (jShriekAdjunction (W β) (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv (I β) _
        ((hsupp β).inv ≫ F.map h.hom ≫ (hsupp α).hom)) := by
  have hc := Q_map_comp_glueingComplexTransitionIso W F I hsupp hqi hβα h
  have hinv := inv_eq_of_comp_comp_hom_eq (DerivedCategory.Q.mapIso
    (glueingComplexLocalIso W F I hsupp β)) hc
  have hinv' : (glueingComplexTransitionIso W F I hsupp hqi hβα h).inv =
      DerivedCategory.Q.map ((jShriekJStarIso X (W β)).hom.app (I β) ≫
        ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((hsupp β).inv ≫ F.map h.hom ≫ (hsupp α).hom)) := by
    rw [hinv]
    simp only [glueingComplexLocalIso, glueingComplexTransitionSourceIso, Iso.trans_inv,
      Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv, Functor.map_comp, Category.assoc,
      comp_openModuleRestrictionMapIso_inv_app]
    rfl
  rw [Adjunction.homEquiv_unit, jShriekComplexAdjunction_unit_app]
  exact hinv'

omit [Nonempty E] in
/-- `glueingTransitionIso` is `restrictionFactorsIso` followed by `transitionLegIso`. -/
theorem glueingTransitionIso_eq (S : LocallyGiven X) {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    glueingTransitionIso S W F I hsupp hqi hβα h =
      restrictionFactorsIso S (W β) (W α) hβα (I α) ≪≫ transitionLegIso W F I hsupp hqi hβα h :=
  rfl

end Transpose

/-- **A map out of an extension by zero whose transpose is invertible in the derived category
restricts to a quasi-isomorphism.** -/
theorem quasiIso_jStar_map_of_isIso (V : Opens X.carrier)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X V)) ℤ)
    (M : CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
    (t : ((jShriek V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ⟶ M)
    (ht : IsIso (DerivedCategory.Q.map ((Adjunction.mapHomologicalComplexAdjunction
      (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv C M t))) :
    QuasiIso (((jStar V (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map t) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp] at ht
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact IsIso.of_isIso_comp_left (DerivedCategory.Q.map
    ((Adjunction.mapHomologicalComplexAdjunction
      (jShriekAdjunction V (underlyingRingSheaf X)) (ComplexShape.up ℤ)).unit.app C)) _


/-! ### The recursion -/

section Recursion

variable (S : LocallyGiven X) {E : Type u} [LinearOrder E] [WellFoundedLT E]
  (W : E → Opens X.carrier) (hmono : ∀ β α : E, β ≤ α → W β ≤ W α)
  (K : ∀ α : E, OpenDerivedCategory X (W α))
  (rho : ∀ (β α : E) (h : β < α),
    (S.restriction (W β) (W α) (hmono β α h.le)).obj (K α) ≅ K β)
  (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
  (hK : ∀ α : E, DerivedCategory.Q.obj (I α) ≅ K α)

/-- The extension by zero of the complex chosen at a stage. -/
abbrev stageComplex (α : E) : CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ :=
  ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (I α)

/-- The transpose of a map between two stages along extension by zero from the smaller one. -/
abbrev stageTranspose {β α : E} (t : stageComplex W I β ⟶ stageComplex W I α) :
    I β ⟶ ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (stageComplex W I α) :=
  (Adjunction.mapHomologicalComplexAdjunction (jShriekAdjunction (W β) (underlyingRingSheaf X))
    (ComplexShape.up ℤ)).homEquiv (I β) _ t

/-- The morphism of the derived category on `W β` which the transpose of the transition from `β`
to `α` represents: the inverse of the prescribed `ρ^α_β`, read through the chosen complexes. -/
def stageTarget {β α : E} (h : β < α) :
    DerivedCategory.Q.obj (I β) ⟶ DerivedCategory.Q.obj
      (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (stageComplex W I α)) :=
  (hK β).hom ≫ (rho β α h).inv ≫ (S.restriction (W β) (W α) (hmono β α h.le)).map (hK α).inv ≫
    (restrictionFactorsIso S (W β) (W α) (hmono β α h.le) (I α)).hom

/-- **The property of a transition of the recursion**: its restriction to the smaller stage is a
quasi-isomorphism, and its transpose represents the inverse of the prescribed transition. -/
def IsStageTransition (β α : E) (_ : β ≤ α)
    (t : stageComplex W I β ⟶ stageComplex W I α) : Prop :=
  QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map t) ∧
    ∀ h : β < α, DerivedCategory.Q.map (stageTranspose W I t) = stageTarget S W hmono K rho I hK h

omit [WellFoundedLT E] in
/-- `stageTarget` is an isomorphism. -/
theorem isIso_stageTarget {β α : E} (h : β < α) :
    IsIso (stageTarget S W hmono K rho I hK h) := by
  unfold stageTarget
  infer_instance

omit [WellFoundedLT E] in
/-- **The transition isomorphism a system of complexes determines is the prescribed one** as soon
as the transpose of its transition map represents the inverse of the prescribed one. -/
theorem glueingTransitionIso_eq_rho
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
    (hsupp : ∀ α : E, F.obj α ≅ stageComplex W I α)
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
    {β α : E} (h : β < α)
    (ht : DerivedCategory.Q.map (stageTranspose W I ((hsupp β).inv ≫ F.map h.le.hom ≫
      (hsupp α).hom)) = stageTarget S W hmono K rho I hK h) :
    (S.restriction (W β) (W α) (hmono β α h.le)).mapIso (hK α).symm ≪≫
        glueingTransitionIso S W F I hsupp hqi (hmono β α h.le) h.le ≪≫ hK β = rho β α h := by
  have : Nonempty E := ⟨β⟩
  have key := transitionLegIso_inv W F I hsupp hqi (hmono β α h.le) h.le
  rw [ht] at key
  apply Iso.ext
  rw [← Iso.inv_eq_inv, glueingTransitionIso_eq]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, key, stageTarget, Category.assoc,
    Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.hom_inv_id, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

end Recursion

/-! ### The step of the recursion -/

section Step

variable (S : LocallyGiven X) {E : Type u} [LinearOrder E] [WellFoundedLT E]
  (W : E → Opens X.carrier) (hmono : ∀ β α : E, β ≤ α → W β ≤ W α)
  (K : ∀ α : E, OpenDerivedCategory X (W α))
  (rho : ∀ (β α : E) (h : β < α),
    (S.restriction (W β) (W α) (hmono β α h.le)).obj (K α) ≅ K β)
  (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
    (rho γ α (hγβ.trans hβα)).hom =
      (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ.le)
          (hmono β α hβα.le)).hom.app (K α) ≫
        (S.restriction (W γ) (W β) (hmono γ β hγβ.le)).map (rho β α hβα).hom ≫
          (rho γ β hγβ).hom)
  (hExt : ∀ (α : E) (i : ℤ), i < 0 → Subsingleton (ShiftedHom (K α) (K α) i))
  (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
  (hK : ∀ α : E, DerivedCategory.Q.obj (I α) ≅ K α)

/-- **The system of the stages strictly below `α`**, as a functor out of the initial segment. -/
def belowSystem (α : E)
    (r : ∀ γ : E, γ < α → ∀ β : E, β ≤ γ → (stageComplex W I β ⟶ stageComplex W I γ))
    (hr : Transfinite.IsGoodBelow (IsStageTransition S W hmono K rho I hK) r) :
    Set.Iio α ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ :=
  Transfinite.ofSystem (fun b : Set.Iio α => stageComplex W I b.1)
    (fun b c h => r c.1 c.2 b.1 h) (fun b => hr.2.1 b.1 b.2)
    (fun b c d h₁ h₂ => hr.2.2 b.1 c.1 d.1 h₁ h₂ d.2)

omit [WellFoundedLT E] in
/-- Each transition map of `belowSystem` restricts to a quasi-isomorphism on the smaller stage. -/
theorem belowSystem_quasiIso (α : E)
    (r : ∀ γ : E, γ < α → ∀ β : E, β ≤ γ → (stageComplex W I β ⟶ stageComplex W I γ))
    (hr : Transfinite.IsGoodBelow (IsStageTransition S W hmono K rho I hK) r)
    (b c : Set.Iio α) (h : b ≤ c) :
    QuasiIso (((jStar (W b.1) (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ((belowSystem S W hmono K rho I hK α r hr).map h.hom)) :=
  (hr.1 b.1 c.1 h c.2).1

/-- The prescribed object at `α`, restricted to the union of the stages below `α`, with its
identifications with the earlier prescribed objects. -/
def restrictedStageIso (α : E) (b : E) (hb : b < α) :
    (S.restriction (W b) (stageSup W α) (le_stageSup W hb)).obj
        ((S.restriction (stageSup W α) (W α) (iSup₂_le fun β hβ => hmono β α hβ.le)).obj (K α)) ≅
      K b :=
  ((S.restrictionComp (W b) (stageSup W α) (W α) (le_stageSup W hb)
    (iSup₂_le fun β hβ => hmono β α hβ.le)).app (K α)).symm ≪≫ rho b α hb

include hcocycle in
omit [WellFoundedLT E] in
/-- The identifications `restrictedStageIso` of the restriction of `K α` to the union of the
stages below `α` are compatible with the prescribed transitions. -/
theorem isCompatibleBelow_restrictedStageIso (α : E) :
    IsCompatibleBelow S W (fun β α h => hmono β α h.le) K rho α
      ((S.restriction (stageSup W α) (W α) (iSup₂_le fun β hβ => hmono β α hβ.le)).obj (K α))
      (restrictedStageIso S W hmono K rho α) := by
  intro γ β hγβ hβ
  have hp := S.restrictionComp_pentagon (W γ) (W β) (stageSup W α) (W α) (hmono γ β hγβ.le)
    (le_stageSup W hβ) (iSup₂_le fun β hβ => hmono β α hβ.le) (K α)
  have h2 : (S.restrictionComp (W γ) (W β) (stageSup W α) (hmono γ β hγβ.le)
        (le_stageSup W hβ)).hom.app ((S.restriction (stageSup W α) (W α)
          (iSup₂_le fun β hβ => hmono β α hβ.le)).obj (K α)) ≫
      (S.restriction (W γ) (W β) (hmono γ β hγβ.le)).map
        ((S.restrictionComp (W β) (stageSup W α) (W α) (le_stageSup W hβ)
          (iSup₂_le fun β hβ => hmono β α hβ.le)).inv.app (K α)) =
      (S.restrictionComp (W γ) (stageSup W α) (W α) (le_stageSup W (hγβ.trans hβ))
          (iSup₂_le fun β hβ => hmono β α hβ.le)).inv.app (K α) ≫
        (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ.le)
          (hmono β α hβ.le)).hom.app (K α) := by
    rw [← cancel_epi ((S.restrictionComp (W γ) (stageSup W α) (W α)
      (le_stageSup W (hγβ.trans hβ)) (iSup₂_le fun β hβ => hmono β α hβ.le)).hom.app (K α)),
      reassoc_of% hp, Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [restrictedStageIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc]
  rw [hcocycle γ β α hγβ hβ, reassoc_of% h2]


/-- The glued complex of the stages strictly below `α`, over the union of those stages. -/
abbrev belowComplex (α : E)
    (r : ∀ γ : E, γ < α → ∀ β : E, β ≤ γ → (stageComplex W I β ⟶ stageComplex W I γ))
    (hr : Transfinite.IsGoodBelow (IsStageTransition S W hmono K rho I hK) r) :
    CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (stageSup W α))) ℤ :=
  glueingComplexOver (stageSup W α) (belowSystem S W hmono K rho I hK α r hr)

/-- The support of the colimit of the stages below `α` on their union. -/
def belowSupportIso (α : E) [Nonempty (Set.Iio α)]
    (r : ∀ γ : E, γ < α → ∀ β : E, β ≤ γ → (stageComplex W I β ⟶ stageComplex W I γ))
    (hr : Transfinite.IsGoodBelow (IsStageTransition S W hmono K rho I hK) r) :
    ((jShriek (stageSup W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (belowComplex S W hmono K rho I hK α r hr) ≅
      colimit (belowSystem S W hmono K rho I hK α r hr) :=
  glueingComplexSupportIso (stageSup W α) (fun b : Set.Iio α => W b.1)
    (belowSystem S W hmono K rho I hK α r hr) (fun b => I b.1) (fun _ => Iso.refl _)
    (fun b => le_stageSup W b.2)

/-- The identifications of the restrictions of the glued complex of the stages below `α` with
the prescribed objects. -/
def belowLegIso (α : E) [Nonempty (Set.Iio α)]
    (r : ∀ γ : E, γ < α → ∀ β : E, β ≤ γ → (stageComplex W I β ⟶ stageComplex W I γ))
    (hr : Transfinite.IsGoodBelow (IsStageTransition S W hmono K rho I hK) r)
    (b : E) (hb : b < α) :
    (S.restriction (W b) (stageSup W α) (le_stageSup W hb)).obj
        (DerivedCategory.Q.obj (belowComplex S W hmono K rho I hK α r hr)) ≅ K b :=
  (restrictionFactorsIso S (W b) (stageSup W α) (le_stageSup W hb)
      (belowComplex S W hmono K rho I hK α r hr) ≪≫
    glueingLegIso (stageSup W α) (fun b : Set.Iio α => W b.1)
      (belowSystem S W hmono K rho I hK α r hr) (fun b => I b.1) (fun _ => Iso.refl _)
      (belowSupportIso S W hmono K rho I hK α r hr)
      (belowSystem_quasiIso S W hmono K rho I hK α r hr) (fun b => le_stageSup W b.2)
        ⟨b, Set.mem_Iio.mpr hb⟩) ≪≫
    hK b

omit [WellFoundedLT E] in
/-- The identifications `belowLegIso` of the glued complex of the stages below `α` are compatible
with the prescribed transitions. -/
theorem isCompatibleBelow_belowLegIso (α : E) [Nonempty (Set.Iio α)]
    (r : ∀ γ : E, γ < α → ∀ β : E, β ≤ γ → (stageComplex W I β ⟶ stageComplex W I γ))
    (hr : Transfinite.IsGoodBelow (IsStageTransition S W hmono K rho I hK) r) :
    IsCompatibleBelow S W (fun β α h => hmono β α h.le) K rho α
      (DerivedCategory.Q.obj (belowComplex S W hmono K rho I hK α r hr))
      (belowLegIso S W hmono K rho I hK α r hr) := by
  intro γ β hγβ hβ
  have hc := glueing_compatibility_of_iso_over (stageSup W α) (fun b : Set.Iio α => W b.1)
    (belowSystem S W hmono K rho I hK α r hr) (fun b => I b.1) (fun b => Iso.refl _)
    (belowSupportIso S W hmono K rho I hK α r hr)
    (belowSystem_quasiIso S W hmono K rho I hK α r hr) (fun b => le_stageSup W b.2) S
    (fun b => K b.1) (fun b => hK b.1) (hmono γ β hγβ.le)
    (show (⟨γ, Set.mem_Iio.mpr (hγβ.trans hβ)⟩ : Set.Iio α) ≤ ⟨β, Set.mem_Iio.mpr hβ⟩ from hγβ.le)
  have hrho := glueingTransitionIso_eq_rho S (fun b : Set.Iio α => W b.1)
    (fun b c h => hmono b.1 c.1 h) (fun b => K b.1) (fun b c h => rho b.1 c.1 h)
    (fun b => I b.1) (fun b => hK b.1) (belowSystem S W hmono K rho I hK α r hr)
    (fun b => Iso.refl _) (belowSystem_quasiIso S W hmono K rho I hK α r hr)
    (show (⟨γ, Set.mem_Iio.mpr (hγβ.trans hβ)⟩ : Set.Iio α) < ⟨β, Set.mem_Iio.mpr hβ⟩ from hγβ) (by
      simp only [Iso.refl_inv, Iso.refl_hom]
      exact (hr.1 γ β hγβ.le hβ).2 hγβ)
  rw [hrho] at hc
  exact hc

/-- The algebra closing the step of the recursion, in an arbitrary pair of categories. -/
theorem step_algebra {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (Φ : 𝒞 ⥤ 𝒟)
    {G₁ G₂ Y Y' : 𝒞} {P' QI Kb N N' T : 𝒟} (φ : G₁ ⟶ G₂) (x : G₂ ⟶ Y) (g : Y ≅ Y')
    (gl : P' ≅ QI) (rf : Φ.obj G₁ ≅ P') (hk : QI ≅ Kb) (r : N ≅ Kb) (c : Φ.obj Y ⟶ N')
    (c₀ : Φ.obj G₂ ⟶ N) (a' : N ⟶ N') (e : N' ⟶ T)
    (hn : Φ.map x ≫ c = c₀ ≫ a')
    (hφ : Φ.map φ ≫ c₀ ≫ r.hom = (rf.hom ≫ gl.hom) ≫ hk.hom) :
    gl.inv ≫ rf.inv ≫ Φ.map ((φ ≫ x ≫ g.hom) ≫ g.inv) ≫ c ≫ e =
      hk.hom ≫ r.inv ≫ a' ≫ e := by
  have hφ' : Φ.map φ ≫ c₀ = rf.hom ≫ gl.hom ≫ hk.hom ≫ r.inv := by
    rw [← cancel_mono r.hom]
    simpa using hφ
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Functor.map_comp]
  rw [reassoc_of% hn, reassoc_of% hφ']
  simp

omit [WellFoundedLT E] in
/-- Let `φ` identify the glued complex of the stages below `α` with the restriction of `K α`,
compatibly with the identifications at each earlier stage, and let `s` be a map of complexes
whose transpose represents `φ`. Then for every `b < α` the transpose of the colimit leg at `b`
followed by `s` represents `stageTarget`. -/
theorem stageTranspose_below_eq (α : E) [Nonempty (Set.Iio α)]
    (r : ∀ γ : E, γ < α → ∀ β : E, β ≤ γ → (stageComplex W I β ⟶ stageComplex W I γ))
    (hr : Transfinite.IsGoodBelow (IsStageTransition S W hmono K rho I hK) r)
    (φ : DerivedCategory.Q.obj (belowComplex S W hmono K rho I hK α r hr) ≅
      (S.restriction (stageSup W α) (W α) (iSup₂_le fun β hβ => hmono β α hβ.le)).obj (K α))
    (hφ : ∀ (b : E) (hb : b < α),
      (S.restriction (W b) (stageSup W α) (le_stageSup W hb)).map φ.hom ≫
          (restrictedStageIso S W hmono K rho α b hb).hom =
        (belowLegIso S W hmono K rho I hK α r hr b hb).hom)
    (s : ((jShriek (stageSup W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (belowComplex S W hmono K rho I hK α r hr) ⟶ stageComplex W I α)
    (hs : DerivedCategory.Q.map ((Adjunction.mapHomologicalComplexAdjunction
        (jShriekAdjunction (stageSup W α) (underlyingRingSheaf X)) (ComplexShape.up ℤ)).homEquiv
          _ _ s) =
      φ.hom ≫ (S.restriction (stageSup W α) (W α)
          (iSup₂_le fun β hβ => hmono β α hβ.le)).map (hK α).inv ≫
        (restrictionFactorsIso S (stageSup W α) (W α) (iSup₂_le fun β hβ => hmono β α hβ.le)
          (I α)).hom)
    (b : E) (hb : b < α) :
    DerivedCategory.Q.map (stageTranspose W I
      (colimit.ι (belowSystem S W hmono K rho I hK α r hr) ⟨b, Set.mem_Iio.mpr hb⟩ ≫
        (belowSupportIso S W hmono K rho I hK α r hr).inv ≫ s)) =
      stageTarget S W hmono K rho I hK hb := by
  have hOα : stageSup W α ≤ W α := iSup₂_le fun β hβ => hmono β α hβ.le
  have h1 := Q_map_homEquiv_colimit_ι_comp (stageSup W α) (W α) hOα (fun b : Set.Iio α => W b.1)
    (belowSystem S W hmono K rho I hK α r hr) (fun b => I b.1) (fun b => Iso.refl _)
    (belowSupportIso S W hmono K rho I hK α r hr)
    (belowSystem_quasiIso S W hmono K rho I hK α r hr) (fun b => le_stageSup W b.2) (I α) S s
    ⟨b, Set.mem_Iio.mpr hb⟩
  simp only [Iso.refl_inv] at h1
  rw [hs] at h1
  refine h1.trans ?_
  have hn := (S.restrictionComp (W b) (stageSup W α) (W α) (le_stageSup W hb) hOα).inv.naturality
    (hK α).inv
  simp only [Functor.comp_map] at hn
  exact step_algebra (S.restriction (W b) (stageSup W α) (le_stageSup W hb)) φ.hom _ _ _ _
    (hK b) (rho b α hb) _ _ _ _ hn (hφ b hb)

include hcocycle hExt in
/-- **The step of the transfinite recursion of [Stacks, Tag 0D6B].** Given transitions between the
stages strictly below `α` which compose strictly, restrict to quasi-isomorphisms and represent the
inverses of the prescribed transitions, there are transitions from those stages into `α` with the
same two properties and compatible with the given ones.

The colimit of the earlier stages, read on their union, is a second solution there of the datum
displayed on those stages; uniqueness of a solution identifies it with the restriction of the
prescribed object at `α`, and the K-injectivity of the complex chosen at `α` realises that
identification by a map of complexes out of the colimit. -/
theorem hasStep [∀ α : E, (I α).IsKInjective] :
    Transfinite.HasStep (stageComplex W I) (IsStageTransition S W hmono K rho I hK) := by
  intro α r hr
  by_cases hne : ∃ β : E, β < α
  swap
  · exact ⟨fun β hβ => absurd ⟨β, hβ⟩ hne, fun β hβ => absurd ⟨β, hβ⟩ hne,
      fun β γ _ hγ => absurd ⟨γ, hγ⟩ hne⟩
  obtain ⟨β₀, hβ₀⟩ := hne
  have : Nonempty (Set.Iio α) := ⟨⟨β₀, Set.mem_Iio.mpr hβ₀⟩⟩
  have hOα : stageSup W α ≤ W α := iSup₂_le fun β hβ => hmono β α hβ.le
  obtain ⟨φ, hφ⟩ := exists_iso_of_isCompatibleBelow S W (fun β α h => hmono β α h.le) K rho
    hcocycle hExt α _ _ (belowLegIso S W hmono K rho I hK α r hr)
    (restrictedStageIso S W hmono K rho α)
    (isCompatibleBelow_belowLegIso S W hmono K rho I hK α r hr)
    (isCompatibleBelow_restrictedStageIso S W hmono K rho hcocycle α)
  obtain ⟨s, hs⟩ := exists_jShriek_complexMap (stageSup W α) (W α) hOα
    (belowComplex S W hmono K rho I hK α r hr) (I α)
    (φ.hom ≫ (S.restriction (stageSup W α) (W α) hOα).map (hK α).inv ≫
      (restrictionFactorsIso S (stageSup W α) (W α) hOα (I α)).hom)
  have key := stageTranspose_below_eq S W hmono K rho I hK α r hr φ hφ s hs
  refine ⟨fun b hb => colimit.ι (belowSystem S W hmono K rho I hK α r hr)
      ⟨b, Set.mem_Iio.mpr hb⟩ ≫ (belowSupportIso S W hmono K rho I hK α r hr).inv ≫ s,
    fun b hb => ⟨quasiIso_jStar_map_of_isIso (W b) (I b) _ _ ?_, fun _ => key b hb⟩,
    fun β γ h hγ => colimit.w_assoc (belowSystem S W hmono K rho I hK α r hr)
      (homOfLE h : (⟨β, Set.mem_Iio.mpr (lt_of_le_of_lt h hγ)⟩ : Set.Iio α) ⟶
        ⟨γ, Set.mem_Iio.mpr hγ⟩) _⟩
  rw [key b hb]
  exact isIso_stageTarget S W hmono K rho I hK hb

end Step

/-! ### The production of the system of complexes -/

/-- **The transfinite recursion of [Stacks, Tag 0D6B] produces the system of complexes.** For a
well ordered increasing family of opens, prescribed objects without negative self-Ext and
prescribed transitions satisfying the cocycle condition, there are K-injective representatives
`I α` of the `K α` and strictly composing maps of complexes `(j_β)_! I β ⟶ (j_α)_! I α`, which
restrict to quasi-isomorphisms on `W β` and represent the inverses of the prescribed
transitions. -/
theorem producesComplexSystem (S : LocallyGiven X) : ProducesComplexSystem S := by
  intro E _ _ W hmono K hExt rho hcocycle
  choose I hI hK' using fun α =>
    exists_isKInjective_representative_openDerivedCategory X (W α) (K α)
  have : ∀ α, (I α).IsKInjective := hI
  obtain ⟨τ, hid, hcomp, hP⟩ := Transfinite.exists_coherentSystem_of_step
    (G := stageComplex W I) (P := IsStageTransition S W hmono K rho I (fun α => (hK' α).some))
    (fun _ _ => 0)
    (fun α => ⟨by rw [CategoryTheory.Functor.map_id]; infer_instance,
      fun h => absurd h (lt_irrefl α)⟩)
    (hasStep S W hmono K rho hcocycle hExt I (fun α => (hK' α).some))
  refine ⟨Transfinite.ofSystem (stageComplex W I) τ hid hcomp, I, fun α => Iso.refl _,
    fun β α h => (hP β α h).1, fun α => (hK' α).some, fun β α h => ?_⟩
  refine glueingTransitionIso_eq_rho S W hmono K rho I (fun α => (hK' α).some)
    (Transfinite.ofSystem (stageComplex W I) τ hid hcomp) (fun α => Iso.refl _)
    (fun β α h => (hP β α h).1) h ?_
  simp only [Iso.refl_inv, Iso.refl_hom]
  exact (hP β α h.le).2 h

/-- **The glueing property over a well ordered increasing cover holds for every system**, for
index sets in the universe of the space. -/
theorem gluesAlongWellOrderedCover_sameUniverse (S : LocallyGiven X) :
    GluesAlongWellOrderedCover.{u} S :=
  gluesAlongWellOrderedCover_of_producesComplexSystem S (producesComplexSystem S)

/-! ### Indices in an arbitrary universe -/

section IndexUniverse

variable (S : LocallyGiven X) {E : Type v} [LinearOrder E] [WellFoundedLT E]
  (W : E → Opens X.carrier) (hmono : ∀ β α : E, β < α → W β ≤ W α)
  (K : ∀ α : E, OpenDerivedCategory X (W α))
  (rho : ∀ (β α : E) (h : β < α),
    (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β)
  (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
    (rho γ α (hγβ.trans hβα)).hom =
      (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ)
          (hmono β α hβα)).hom.app (K α) ≫
        (S.restriction (W γ) (W β) (hmono γ β hγβ)).map (rho β α hβα).hom ≫
          (rho γ β hγβ).hom)
  (G : OpenDerivedCategory X ⊤)

/-- Compatibility of two identifications of restrictions of `G` with the prescribed transition
between their stages. -/
def IsCompatiblePair {x y : E} (h : x < y)
    (sx : (S.restriction (W x) ⊤ le_top).obj G ≅ K x)
    (sy : (S.restriction (W y) ⊤ le_top).obj G ≅ K y) : Prop :=
  (S.restrictionComp (W x) (W y) ⊤ (hmono x y h) le_top).hom.app G ≫
      (S.restriction (W x) (W y) (hmono x y h)).map sy.hom ≫ (rho x y h).hom = sx.hom

include hcocycle in
omit [WellFoundedLT E] in
/-- For `x < y < z`, transporting an identification at `z` to `x` directly agrees with
transporting it first to `y` and then to `x`, by the cocycle condition. -/
theorem isCompatiblePair_key {x y z : E} (h₁ : x < y) (h₂ : y < z)
    (sz : (S.restriction (W z) ⊤ le_top).obj G ≅ K z) :
    (S.restrictionComp (W x) (W z) ⊤ (hmono x z (h₁.trans h₂)) le_top).hom.app G ≫
        (S.restriction (W x) (W z) (hmono x z (h₁.trans h₂))).map sz.hom ≫
          (rho x z (h₁.trans h₂)).hom =
      (S.restrictionComp (W x) (W y) ⊤ (hmono x y h₁) le_top).hom.app G ≫
        (S.restriction (W x) (W y) (hmono x y h₁)).map
          ((S.restrictionComp (W y) (W z) ⊤ (hmono y z h₂) le_top).hom.app G ≫
            (S.restriction (W y) (W z) (hmono y z h₂)).map sz.hom ≫ (rho y z h₂).hom) ≫
          (rho x y h₁).hom := by
  have hp := S.restrictionComp_pentagon (W x) (W y) (W z) ⊤ (hmono x y h₁) (hmono y z h₂) le_top G
  have hn := (S.restrictionComp (W x) (W y) (W z) (hmono x y h₁) (hmono y z h₂)).hom.naturality
    sz.hom
  simp only [Functor.comp_map] at hn
  rw [hcocycle x y z h₁ h₂, reassoc_of% hn, reassoc_of% hp]
  simp only [Functor.map_comp, Category.assoc]

include hcocycle in
omit [WellFoundedLT E] in
/-- Compatibility of identifications is transitive along `x < y < z`. -/
theorem IsCompatiblePair.trans {x y z : E} {h₁ : x < y} {h₂ : y < z}
    {sx : (S.restriction (W x) ⊤ le_top).obj G ≅ K x}
    {sy : (S.restriction (W y) ⊤ le_top).obj G ≅ K y}
    {sz : (S.restriction (W z) ⊤ le_top).obj G ≅ K z}
    (hxy : IsCompatiblePair S W hmono K rho G h₁ sx sy)
    (hyz : IsCompatiblePair S W hmono K rho G h₂ sy sz) :
    IsCompatiblePair S W hmono K rho G (h₁.trans h₂) sx sz := by
  unfold IsCompatiblePair at hxy hyz ⊢
  rw [isCompatiblePair_key S W hmono K rho hcocycle G h₁ h₂, hyz, hxy]

include hcocycle in
omit [WellFoundedLT E] in
/-- For `x < y < z` with `W y ≤ W x`, compatibility at `(x, y)` and at `(x, z)` implies
compatibility at `(y, z)`. -/
theorem IsCompatiblePair.of_trans {x y z : E} {h₁ : x < y} {h₂ : y < z}
    {sx : (S.restriction (W x) ⊤ le_top).obj G ≅ K x}
    {sy : (S.restriction (W y) ⊤ le_top).obj G ≅ K y}
    {sz : (S.restriction (W z) ⊤ le_top).obj G ≅ K z}
    (hxy : IsCompatiblePair S W hmono K rho G h₁ sx sy)
    (hxz : IsCompatiblePair S W hmono K rho G (h₁.trans h₂) sx sz) (hyx : W y ≤ W x) :
    IsCompatiblePair S W hmono K rho G h₂ sy sz := by
  unfold IsCompatiblePair at hxy hxz ⊢
  rw [isCompatiblePair_key S W hmono K rho hcocycle G h₁ h₂, ← hxy, cancel_epi,
    cancel_mono] at hxz
  exact restriction_map_injective_of_antisymm S (hmono x y h₁) hyx hxz

/-- **An identification at a stage, carried to a later stage attaining the same open.** -/
def extendIso {a α : E} (ha : a ≤ α) (h₂ : W α ≤ W a)
    (σa : (S.restriction (W a) ⊤ le_top).obj G ≅ K a) :
    (S.restriction (W α) ⊤ le_top).obj G ≅ K α :=
  if h : a = α then by subst h; exact σa
  else isoOfRestrictionObjIso S (hmono a α (lt_of_le_of_ne ha h)) h₂
    (((S.restrictionComp (W a) (W α) ⊤ (hmono a α (lt_of_le_of_ne ha h)) le_top).app G).symm ≪≫
      σa ≪≫ (rho a α (lt_of_le_of_ne ha h)).symm)

/-- The restriction of `isoOfRestrictionObjIso e` is `e`. -/
theorem restriction_map_isoOfRestrictionObjIso_hom {U V : Opens X.carrier} (hUV : U ≤ V)
    (hVU : V ≤ U) {P Q : OpenDerivedCategory X V}
    (e : (S.restriction U V hUV).obj P ≅ (S.restriction U V hUV).obj Q) :
    (S.restriction U V hUV).map (isoOfRestrictionObjIso S hUV hVU e).hom = e.hom := by
  obtain rfl : U = V := le_antisymm hUV hVU
  rw [← cancel_mono ((restrictionSelfIso S U hUV).app Q).hom, restrictionSelfIso_naturality]
  simp [isoOfRestrictionObjIso]

omit [WellFoundedLT E] in
/-- For `a < α`, an identification at `a` is compatible with its extension `extendIso` to `α`. -/
theorem isCompatiblePair_extendIso {a α : E} (ha : a ≤ α) (h₂ : W α ≤ W a)
    (σa : (S.restriction (W a) ⊤ le_top).obj G ≅ K a) (hlt : a < α) :
    IsCompatiblePair S W hmono K rho G hlt σa (extendIso S W hmono K rho G ha h₂ σa) := by
  unfold IsCompatiblePair
  rw [extendIso, dif_neg hlt.ne, restriction_map_isoOfRestrictionObjIso_hom]
  simp

omit [WellFoundedLT E] in
/-- When `a = α`, an identification at `x` is compatible with `extendIso` of `σa` if and only if
it is compatible with `σa`. -/
theorem isCompatiblePair_extendIso_right_iff {x a α : E} (ha : a ≤ α) (h₂ : W α ≤ W a)
    (σa : (S.restriction (W a) ⊤ le_top).obj G ≅ K a) (heq : a = α)
    (sx : (S.restriction (W x) ⊤ le_top).obj G ≅ K x) (hx : x < a) :
    IsCompatiblePair S W hmono K rho G (heq ▸ hx) sx (extendIso S W hmono K rho G ha h₂ σa) ↔
      IsCompatiblePair S W hmono K rho G hx sx σa := by
  subst heq
  rw [extendIso, dif_pos rfl]

omit [WellFoundedLT E] in
/-- When `a = β`, `extendIso` of `σa` is compatible with an identification at `z` if and only if
`σa` is. -/
theorem isCompatiblePair_extendIso_left_iff {a β z : E} (ha : a ≤ β) (h₂ : W β ≤ W a)
    (σa : (S.restriction (W a) ⊤ le_top).obj G ≅ K a) (heq : a = β)
    (sz : (S.restriction (W z) ⊤ le_top).obj G ≅ K z) (hz : a < z) :
    IsCompatiblePair S W hmono K rho G (heq ▸ hz) (extendIso S W hmono K rho G ha h₂ σa) sz ↔
      IsCompatiblePair S W hmono K rho G hz σa sz := by
  subst heq
  rw [extendIso, dif_pos rfl]

end IndexUniverse

section RangeReduction

variable (S : LocallyGiven X) {E : Type v} [LinearOrder E] [WellFoundedLT E]
  (W : E → Opens X.carrier) (hmono : ∀ β α : E, β < α → W β ≤ W α)
  (K : ∀ α : E, OpenDerivedCategory X (W α))
  (rho : ∀ (β α : E) (h : β < α),
    (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β)
  (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
    (rho γ α (hγβ.trans hβα)).hom =
      (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ)
          (hmono β α hβα)).hom.app (K α) ≫
        (S.restriction (W γ) (W β) (hmono γ β hγβ)).map (rho β α hβα).hom ≫
          (rho γ β hγβ).hom)
  (G : OpenDerivedCategory X ⊤)
  (σ₀ : ∀ V : ↥(Set.range W),
    (S.restriction (W (leastIndex W V)) ⊤ le_top).obj G ≅ K (leastIndex W V))

/-- The identifications at the least stages attaining each open, carried to every stage. -/
def rangeExtendIso (α : E) : (S.restriction (W α) ⊤ le_top).obj G ≅ K α :=
  extendIso S W hmono K rho G (leastIndex_self_le W α)
    (apply_leastIndex W ⟨W α, α, rfl⟩).ge (σ₀ ⟨W α, α, rfl⟩)

include hcocycle in
/-- If the identifications `σ₀` at the least stages are pairwise compatible, then the
identification at the least stage attaining an open `V ≤ W α` is compatible with
`rangeExtendIso` at `α`. -/
theorem isCompatiblePair_range_rangeExtendIso
    (h0 : ∀ (V' V : ↥(Set.range W)) (h : V'.1 < V.1),
      IsCompatiblePair S W hmono K rho G (leastIndex_strictMono hmono h) (σ₀ V') (σ₀ V))
    (α : E) (V : ↥(Set.range W)) (hV : V.1 ≤ W α) (hl : leastIndex W V < α) :
    IsCompatiblePair S W hmono K rho G hl (σ₀ V) (rangeExtendIso S W hmono K rho G σ₀ α) := by
  have hle : leastIndex W V ≤ leastIndex W ⟨W α, α, rfl⟩ :=
    leastIndex_monotone hmono (V := V) (U := ⟨W α, α, rfl⟩) hV
  rcases eq_or_lt_of_le hle with heq | hlt
  · have hV' : V = ⟨W α, α, rfl⟩ := Subtype.ext (by
      rw [← apply_leastIndex W V, heq, apply_leastIndex W ⟨W α, α, rfl⟩])
    subst hV'
    exact isCompatiblePair_extendIso S W hmono K rho G _ _ _ hl
  · have hVlt : V.1 < (⟨W α, α, rfl⟩ : ↥(Set.range W)).1 := by
      have := apply_lt_of_lt_leastIndex hmono ⟨W α, α, rfl⟩ hlt
      rwa [apply_leastIndex W V] at this
    have h01 := h0 V ⟨W α, α, rfl⟩ hVlt
    rcases eq_or_lt_of_le (leastIndex_self_le W α) with heq' | hlt'
    · exact (isCompatiblePair_extendIso_right_iff S W hmono K rho G (leastIndex_self_le W α)
        (apply_leastIndex W ⟨W α, α, rfl⟩).ge (σ₀ ⟨W α, α, rfl⟩) heq' (σ₀ V) hlt).2 h01
    · exact IsCompatiblePair.trans S W hmono K rho hcocycle G h01
        (isCompatiblePair_extendIso S W hmono K rho G _ _ _ hlt')

include hcocycle in
/-- If the identifications `σ₀` at the least stages are pairwise compatible, then the
identifications `rangeExtendIso` at any two stages `β < α` are compatible. -/
theorem isCompatiblePair_rangeExtendIso
    (h0 : ∀ (V' V : ↥(Set.range W)) (h : V'.1 < V.1),
      IsCompatiblePair S W hmono K rho G (leastIndex_strictMono hmono h) (σ₀ V') (σ₀ V))
    {β α : E} (h : β < α) :
    IsCompatiblePair S W hmono K rho G h (rangeExtendIso S W hmono K rho G σ₀ β)
      (rangeExtendIso S W hmono K rho G σ₀ α) := by
  have hb : leastIndex W ⟨W β, β, rfl⟩ ≤ β := leastIndex_self_le W β
  have hinner := isCompatiblePair_range_rangeExtendIso S W hmono K rho hcocycle G σ₀ h0 α
    ⟨W β, β, rfl⟩ (hmono β α h) (lt_of_le_of_lt hb h)
  rcases eq_or_lt_of_le hb with heq | hlt
  · exact (isCompatiblePair_extendIso_left_iff S W hmono K rho G hb
      (apply_leastIndex W ⟨W β, β, rfl⟩).ge (σ₀ ⟨W β, β, rfl⟩) heq
      (rangeExtendIso S W hmono K rho G σ₀ α) (lt_of_le_of_lt hb h)).2 hinner
  · exact IsCompatiblePair.of_trans S W hmono K rho hcocycle G
      (isCompatiblePair_extendIso S W hmono K rho G hb _ (σ₀ ⟨W β, β, rfl⟩) hlt) hinner
      (apply_leastIndex W ⟨W β, β, rfl⟩).ge

end RangeReduction

/-- **The glueing step over a well ordered increasing cover holds for every system**, for index
sets in an arbitrary universe. -/
theorem gluesAlongWellOrderedCover (S : LocallyGiven X) : GluesAlongWellOrderedCover.{v} S := by
  intro E _ _ W hmono hlimit hcover K hExt rho hcocycle
  let : LinearOrder ↥(Set.range W) := rangeLinearOrder hmono
  have : WellFoundedLT ↥(Set.range W) := wellFounded_lt_range hmono
  obtain ⟨G, σ₀, hσ₀⟩ := exists_glueing_of_wellOrderedCover_of_gluesAlong S
    (gluesAlongWellOrderedCover_sameUniverse S) ↥(Set.range W) (fun V => W (leastIndex W V))
    (fun V V' h _ => hmono _ _ (leastIndex_strictMono hmono h))
    (fun V hV => leastIndex_eq_iSup_of_not_isPred hmono hlimit hV)
    (by rw [iSup_apply_leastIndex]; exact hcover) (fun V => K (leastIndex W V)) (fun V => hExt _)
    (fun V V' h => rho _ _ (leastIndex_strictMono hmono h))
    (fun T V U h₁ h₂ => hcocycle _ _ _ _ _)
  exact ⟨G, rangeExtendIso S W hmono K rho G σ₀, Set.univ, fun α => ⟨α, Set.mem_univ α, le_rfl⟩,
    fun β γ h _ => isCompatiblePair_rangeExtendIso S W hmono K rho hcocycle G σ₀
      (fun V' V h => hσ₀ V' V h) h⟩

/-! ### Tag 0D6B -/

/-- **[Stacks, Tag 0D6B].** Let `X` be a ringed space, let `E` be a well ordered set and let
`X = ⋃_{α ∈ E} W_α` be an open covering with `W_α ⊆ W_{α+1}` and `W_α = ⋃_{β < α} W_β` when `α`
is not a successor.  Let `K_α` be an object of `D(𝒪_{W_α})` with `Ext^i(K_α, K_α) = 0` for
`i < 0`, and let `ρ^α_β : K_α|_{W_β} ≅ K_β` for `β < α` satisfy
`ρ^α_γ = ρ^β_γ ∘ ρ^α_β|_{W_γ}` for `γ < β < α`.  Then there is an object `K` of `D(𝒪_X)` and
isomorphisms `K|_{W_α} ≅ K_α` compatible with the `ρ^α_β`.

"`β` is the immediate predecessor of `α`" is rendered as "`β < α` and every `γ < α` satisfies
`γ ≤ β`", so `hsucc` is the inclusion `W_α ⊆ W_{α+1}` and `hlimit` the continuity at the stages
that are not successors; `Stacks.DerivedGlueing.le_of_succ_of_limit` derives from them the
inclusion `W_β ⊆ W_α` for every `β < α` along which the transitions are stated.

The system `S : Stacks.DerivedGlueing.LocallyGiven X` (the structure of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedCategory/LocallyGivenObjects.lean`, not
`RingedSite.LocallyGiven`) is exactly Situation 0D67 and carries no further data: its restriction
functors `S.restriction V U` are the canonical derived restrictions `j^*` along the inclusions
`V ⊆ U`, since the field `restrictionFactors` identifies each with the derived functor of the
restriction of complexes `openModuleRestriction` through the localization, and its comparisons
`S.restrictionComp` are the canonical ones, by the field `restrictionCompFactors`. -/
@[stacks 0D6B "the glued object `G` over `⊤` with identifications `sigma α` of its restrictions
  with the `K α`, compatible with the prescribed `ρ^α_β` for every `β < α`, for a well ordered
  covering with `hsucc` (`W_α ⊆ W_{α+1}`), `hlimit` (continuity at the stages that are not
  successors), `hcover`, `hExt` (no negative self-Ext) and the cocycle condition `hcocycle`"]
theorem exists_glueing_of_wellOrderedCover (S : Stacks.DerivedGlueing.LocallyGiven X)
    (E : Type v) [LinearOrder E] [WellFoundedLT E]
    (W : E → Opens X.carrier)
    (hsucc : ∀ β α : E, β < α → (∀ γ : E, γ < α → γ ≤ β) → W β ≤ W α)
    (hlimit : ∀ α : E, (¬ ∃ β : E, β < α ∧ ∀ γ : E, γ < α → γ ≤ β) →
      W α = ⨆ (β : E) (_ : β < α), W β)
    (hcover : (⨆ α : E, W α) = ⊤) (K : ∀ α : E, OpenDerivedCategory X (W α))
    (hExt : ∀ (α : E) (i : ℤ), i < 0 → Subsingleton (ShiftedHom (K α) (K α) i))
    (rho : ∀ (β α : E) (h : β < α),
      (S.restriction (W β) (W α) (le_of_succ_of_limit W hsucc hlimit β α h)).obj (K α) ≅ K β)
    (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
      (rho γ α (hγβ.trans hβα)).hom =
        (S.restrictionComp (W γ) (W β) (W α) (le_of_succ_of_limit W hsucc hlimit γ β hγβ)
            (le_of_succ_of_limit W hsucc hlimit β α hβα)).hom.app (K α) ≫
          (S.restriction (W γ) (W β)
            (le_of_succ_of_limit W hsucc hlimit γ β hγβ)).map (rho β α hβα).hom ≫
            (rho γ β hγβ).hom) :
    ∃ (G : OpenDerivedCategory X ⊤)
      (sigma : ∀ α : E, (S.restriction (W α) ⊤ le_top).obj G ≅ K α),
      ∀ (β α : E) (h : β < α),
        (S.restrictionComp (W β) (W α) ⊤
              (le_of_succ_of_limit W hsucc hlimit β α h) le_top).hom.app G ≫
            (S.restriction (W β) (W α)
              (le_of_succ_of_limit W hsucc hlimit β α h)).map (sigma α).hom ≫ (rho β α h).hom =
          (sigma β).hom :=
  exists_glueing_of_wellOrderedCover_of_gluesAlong S (gluesAlongWellOrderedCover.{v} S) E W hsucc
    hlimit hcover K hExt rho hcocycle

end Stacks.DerivedGlueing

end
