module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.TildeCartesian
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionExactness

/-!
# The direct image of `M~` along an affine morphism commutes with colimits in `M`

Let `g : U ⟶ 𝒳` be an affine 1-morphism from a scheme `U` (with ring of global functions `A`) to
an algebraic stack, with right adjoint `r : x ↦ U ×_𝒳 x` on the sites.  For an `A`-module `M`
the direct image `g_* M~` is the sheafification of the presheaf `x ↦ 𝒪(r x) ⊗_A M`: the
comparison map is bijective on sections over the affine objects of `𝒳`, since `r x` is affine
when `x` is and `𝒪(T) ⊗_A M = M~(T)` for affine `T`.  The functor
`M ↦ (x ↦ 𝒪(r x) ⊗_A M)^#` preserves colimits, being a composite of three colimit-preserving
functors, so `M ↦ g_* M~` preserves colimits.

## Main definitions

* `AlgebraicGeometry.Stack.tildePushforwardModel`: `M ↦ (x ↦ 𝒪(r x) ⊗_A M)^#`.
* `AlgebraicGeometry.Stack.tildePushforwardModelIso`: its identification with `M ↦ g_* M~`.

## Main results

* `AlgebraicGeometry.Stack.preservesColimits_tildeFunctor_comp_affinePushforward`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace CategoryTheory.Adjunction

/-- The unit followed by the transpose of `f` is `f`. -/
lemma unit_app_comp_map_map_comp_counit_app {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A : C} {B : D} (f : A ⟶ R.obj B) :
    adj.unit.app A ≫ R.map (L.map f ≫ adj.counit.app B) = f := by
  have h := adj.unit.naturality f
  simp only [Functor.id_map, Functor.comp_map] at h
  rw [Functor.map_comp, ← Category.assoc, ← h, Category.assoc, adj.right_triangle_components]
  simp

end CategoryTheory.Adjunction

namespace PresheafOfModules

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {Φ : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{u}} {R₀ : Cᵒᵖ ⥤ RingCat.{u}} (φ : R₀ ⟶ Φ.op ⋙ R)

/-- **Pushforward of presheaves of modules preserves colimits**, being computed on sections by
restriction of scalars. -/
theorem pushforward_preservesColimitsOfSize :
    PreservesColimitsOfSize.{u, u} (PresheafOfModules.pushforward.{u} φ) := by
  refine ⟨fun {K} _ => ⟨fun {F} => ⟨fun {c} hc => ⟨?_⟩⟩⟩⟩
  refine PresheafOfModules.evaluationJointlyReflectsColimits
    (F ⋙ PresheafOfModules.pushforward φ) _ fun X => ?_
  refine IsColimit.ofIsoColimit (isColimitOfPreserves
    (PresheafOfModules.evaluation R (Φ.op.obj X) ⋙
      ModuleCat.restrictScalars (φ.app X).hom) hc) ?_
  exact (Cocone.ext (Iso.refl _) (fun j => Category.comp_id _)).symm

end PresheafOfModules

namespace AlgebraicGeometry.Stack

attribute [local instance] FibredSite.hasWeakSheafify_associatedTopology
  FibredSite.wEqualsLocallyBijective_associatedTopology

local notation "𝒪[" Y "]" => AlgebraicStacks.fppfStructureRingSheaf _ _ _ Y
local notation "𝒪c[" Y "]" => AlgebraicStacks.fppfStructureSheaf _ _ _ Y
local notation "J[" Y "]" => AlgebraicStacks.fppfSiteTopology _ _ _ Y

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : AlgebraicStacks.IsAffineHom B S hS g)

/-- The direct image of presheaves of modules along `g`: restriction along `r`. -/
noncomputable abbrev affinePresheafPushforward :
    PresheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U].obj ⥤
      PresheafOfModules.{u} 𝒪[𝒳].obj :=
  letI := isContinuous_affineRightAdjoint g hg
  PresheafOfModules.pushforward (pushforwardRingHom g hg).hom

/-- The direct image of presheaves of modules along `g` preserves colimits of size `u`. -/
instance : PreservesColimitsOfSize.{u, u} (affinePresheafPushforward g hg) :=
  letI := isContinuous_affineRightAdjoint g hg
  PresheafOfModules.pushforward_preservesColimitsOfSize _

/-- **The model `M ↦ (x ↦ 𝒪(r x) ⊗_A M)^#` of `M ↦ g_* M~`.** -/
noncomputable def tildePushforwardModel :
    ModuleCat.{u} (schemeGlobalRing U) ⥤ SheafOfModules.{u} 𝒪[𝒳] :=
  tildePresheafFunctor.{u, w} U ⋙ affinePresheafPushforward g hg ⋙
    Stacks.SheafOfModules.sheafifyFunctor (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)

/-- The functor `M ↦ (x ↦ 𝒪(r x) ⊗_A M)^#` preserves colimits. -/
instance : PreservesColimitsOfSize.{u, u} (tildePushforwardModel g hg) := by
  have : PreservesColimitsOfSize.{u, u} (Stacks.SheafOfModules.sheafifyFunctor (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)) :=
    (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u}
      (affinePresheafPushforward g hg ⋙ Stacks.SheafOfModules.sheafifyFunctor (𝒪c[𝒳]).obj
        (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)) :=
    @Limits.comp_preservesColimits _ _ _ _ _ _ _ _ inferInstance this
  exact @Limits.comp_preservesColimits _ _ _ _ _ _ (tildePresheafFunctor.{u, w} U) _
    inferInstance this

/-- The direct image of the sheafification map `(T ↦ 𝒪(T) ⊗_A M) ⟶ M~`, at one module. -/
noncomputable def tildePushforwardUnitApp (M : ModuleCat.{u} (schemeGlobalRing U)) :
    (affinePresheafPushforward g hg).obj ((tildePresheafFunctor.{u, w} U).obj M) ⟶
      (SheafOfModules.forget 𝒪[𝒳] ⋙ PresheafOfModules.restrictScalars (𝟙 𝒪[𝒳].obj)).obj
        ((affinePushforward.{u, w, u} g hg).obj ((tildeFunctor.{u, w} U).obj M)) :=
  (affinePresheafPushforward g hg).map (tildeUnit.{u, w} U M)

/-- The direct image of the sheafification maps `(T ↦ 𝒪(T) ⊗_A M) ⟶ M~`, natural in `M`. -/
noncomputable def tildePushforwardUnit :
    tildePresheafFunctor.{u, w} U ⋙ affinePresheafPushforward g hg ⟶
      tildeFunctor.{u, w} U ⋙ affinePushforward.{u, w, u} g hg ⋙
        SheafOfModules.forget 𝒪[𝒳] ⋙ PresheafOfModules.restrictScalars (𝟙 𝒪[𝒳].obj) where
  app M := tildePushforwardUnitApp g hg M
  naturality M N f := by
    ext x m
    exact congrArg (fun φ => (PresheafOfModules.Hom.app φ
      (op ((affineRightAdjoint g hg).obj x.unop))).hom m)
      ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction
        (𝒪c[schemeStack.{u, w} B S hS U]).obj
        (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS
          (schemeStack.{u, w} B S hS U))).unit.naturality ((tildePresheafFunctor.{u, w} U).map f))

/-- **The comparison `(x ↦ 𝒪(r x) ⊗_A M)^# ⟶ g_* M~`**, the transpose of
`AlgebraicGeometry.Stack.tildePushforwardUnit`. -/
noncomputable def tildePushforwardComparison :
    tildePushforwardModel g hg ⟶ tildeFunctor.{u, w} U ⋙ affinePushforward.{u, w, u} g hg :=
  Functor.whiskerRight (tildePushforwardUnit g hg)
      (Stacks.SheafOfModules.sheafifyFunctor (𝒪c[𝒳]).obj
        (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)) ≫
    Functor.whiskerLeft (tildeFunctor.{u, w} U ⋙ affinePushforward.{u, w, u} g hg)
      (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction (𝒪c[𝒳]).obj
        (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)).counit

/-- The sheafification map of `x ↦ 𝒪(r x) ⊗_A M`, read as a map of presheaves of abelian groups. -/
noncomputable abbrev tildePushforwardSheafifyUnit (M : ModuleCat.{u} (schemeGlobalRing U)) :=
  (PresheafOfModules.toPresheaf 𝒪[𝒳].obj).map
    ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)).unit.app
        ((affinePresheafPushforward g hg).obj ((tildePresheafFunctor.{u, w} U).obj M)))

/-- The sheafification map, followed by the comparison, is the direct image of the sheafification
map of `T ↦ 𝒪(T) ⊗_A M`. -/
theorem tildePushforwardSheafifyUnit_comp (M : ModuleCat.{u} (schemeGlobalRing U)) :
    tildePushforwardSheafifyUnit g hg M ≫
      (PresheafOfModules.toPresheaf 𝒪[𝒳].obj).map ((tildePushforwardComparison g hg).app M).val =
      (PresheafOfModules.toPresheaf 𝒪[𝒳].obj).map (tildePushforwardUnitApp g hg M) := by
  have h := Adjunction.unit_app_comp_map_map_comp_counit_app
    (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳))
    (A := (affinePresheafPushforward g hg).obj ((tildePresheafFunctor.{u, w} U).obj M))
    (B := (affinePushforward.{u, w, u} g hg).obj ((tildeFunctor.{u, w} U).obj M))
    (tildePushforwardUnitApp g hg M)
  have h' := congrArg (PresheafOfModules.toPresheaf
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)).obj).map h
  rw [Functor.map_comp] at h'
  exact h'

/-- The direct image of the sheafification map `(T ↦ 𝒪(T) ⊗_A M) ⟶ M~` is locally injective. -/
theorem isLocallyInjective_tildePushforwardUnitApp (M : ModuleCat.{u} (schemeGlobalRing U)) :
    Presheaf.IsLocallyInjective J[𝒳]
      ((PresheafOfModules.toPresheaf 𝒪[𝒳].obj).map (tildePushforwardUnitApp g hg M)) :=
  FibredSite.isLocallyInjective_of_injective_affine 𝒳.val.isFiberedInGroupoids _ fun y hy =>
    (bijective_tildeUnit_app.{u, w} U M (isAffineOver_affineRightAdjoint_obj g hg y hy)).1

/-- The direct image of the sheafification map `(T ↦ 𝒪(T) ⊗_A M) ⟶ M~` is locally surjective. -/
theorem isLocallySurjective_tildePushforwardUnitApp (M : ModuleCat.{u} (schemeGlobalRing U)) :
    Presheaf.IsLocallySurjective J[𝒳]
      ((PresheafOfModules.toPresheaf 𝒪[𝒳].obj).map (tildePushforwardUnitApp g hg M)) :=
  FibredSite.isLocallySurjective_of_surjective_affine 𝒳.val.isFiberedInGroupoids _ fun y hy =>
    (bijective_tildeUnit_app.{u, w} U M (isAffineOver_affineRightAdjoint_obj g hg y hy)).2

/-- The sheafification map of `x ↦ 𝒪(r x) ⊗_A M` is locally surjective. -/
theorem isLocallySurjective_tildePushforwardSheafifyUnit (M : ModuleCat.{u} (schemeGlobalRing U)) :
    Presheaf.IsLocallySurjective J[𝒳] (tildePushforwardSheafifyUnit g hg M) :=
  (GrothendieckTopology.W_toSheafify J[𝒳]
    ((affinePresheafPushforward g hg).obj ((tildePresheafFunctor.{u, w} U).obj M)).presheaf
      ).isLocallySurjective

/-- The comparison `(x ↦ 𝒪(r x) ⊗_A M)^# ⟶ g_* M~` is locally injective. -/
theorem isLocallyInjective_tildePushforwardComparison_app_val
    (M : ModuleCat.{u} (schemeGlobalRing U)) :
    Presheaf.IsLocallyInjective J[𝒳]
      ((PresheafOfModules.toPresheaf 𝒪[𝒳].obj).map ((tildePushforwardComparison g hg).app M).val) :=
  @Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _ _ J[𝒳]
    _ _ _ _ _ _ _ _ _ _ _ _ (tildePushforwardSheafifyUnit_comp g hg M)
    (isLocallyInjective_tildePushforwardUnitApp g hg M)
    (isLocallySurjective_tildePushforwardSheafifyUnit g hg M)

/-- The comparison `(x ↦ 𝒪(r x) ⊗_A M)^# ⟶ g_* M~` is locally surjective. -/
theorem isLocallySurjective_tildePushforwardComparison_app_val
    (M : ModuleCat.{u} (schemeGlobalRing U)) :
    Presheaf.IsLocallySurjective J[𝒳]
      ((PresheafOfModules.toPresheaf 𝒪[𝒳].obj).map ((tildePushforwardComparison g hg).app M).val) :=
  @Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ _ J[𝒳]
    _ _ _ _ _ _ _ _ _ _ _ _ (tildePushforwardSheafifyUnit_comp g hg M)
    (isLocallySurjective_tildePushforwardUnitApp g hg M)

/-- **The comparison `(x ↦ 𝒪(r x) ⊗_A M)^# ⟶ g_* M~` is an isomorphism.**  Composed with the
sheafification map it is the direct image of `(T ↦ 𝒪(T) ⊗_A M) ⟶ M~`, which is bijective over
the affine objects of `𝒳` (their images under `r` are affine), hence locally bijective; so the
comparison, a morphism of sheaves, is locally bijective. -/
instance isIso_tildePushforwardComparison_app (M : ModuleCat.{u} (schemeGlobalRing U)) :
    IsIso ((tildePushforwardComparison g hg).app M) :=
  haveI := isLocallyInjective_tildePushforwardComparison_app_val g hg M
  haveI := isLocallySurjective_tildePushforwardComparison_app_val g hg M
  Stacks.SheafOfModules.isIso_of_isLocallyBijective _

/-- **`g_* M~ ≅ (x ↦ 𝒪(r x) ⊗_A M)^#`**, naturally in `M`. -/
noncomputable def tildePushforwardModelIso :
    tildePushforwardModel g hg ≅ tildeFunctor.{u, w} U ⋙ affinePushforward.{u, w, u} g hg :=
  haveI : IsIso (tildePushforwardComparison g hg) := NatIso.isIso_of_isIso_app _
  asIso (tildePushforwardComparison g hg)

/-- **`M ↦ g_* M~` preserves colimits.** -/
instance preservesColimits_tildeFunctor_comp_affinePushforward :
    PreservesColimitsOfSize.{u, u} (tildeFunctor.{u, w} U ⋙ affinePushforward.{u, w, u} g hg) :=
  preservesColimits_of_natIso (tildePushforwardModelIso g hg)

end AlgebraicGeometry.Stack
