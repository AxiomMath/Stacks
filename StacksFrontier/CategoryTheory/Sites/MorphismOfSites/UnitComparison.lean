module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Limits.Final.Type
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites

/-!
# The comparison `f^*𝒪_Y ⟶ 𝒪_X` along a morphism of sites is invertible

Let `v : C ⥤ D` be a continuous functor presenting a morphism of topoi `f : Sh(D) ⟶ Sh(C)`, let
`S` be a sheaf of rings on `(C, J)` and `R` one on `(D, K)`, and let `φ : S ⟶ f_*R` be a morphism
of sheaves of rings, so that `(C, S)` and `(D, R)` are ringed sites and `f` is a morphism of
ringed topoi. Mathlib's `SheafOfModules.pullbackObjUnitToUnit φ : f^*S ⟶ R` is the comparison of
the pullback of the structure sheaf with the structure sheaf, where `f^*` is the left adjoint of
the pushforward. If `v` defines a morphism of sites in the sense of [Stacks, Tag 00X1], that is,
if the induced functor `v_s = f^{-1}` on sheaves of sets is exact, then
`pullbackObjUnitToUnit φ` is invertible.

## Main results

All in the namespace `Stacks.Sites.UnitComparison`.

* `isIso_counit_app_terminal`: the counit of `v_s ⊣ v^s` at the terminal sheaf of sets is
  invertible when `v_s` preserves finite limits.
* `bijective_sectionsPrecomp`: for a sheaf of sets `P` on `(D, K)`, restricting a global section
  along `v` is a bijection `Γ(D, P) ≃ Γ(C, v^sP)`.
* `bijective_pushforwardSections`: the same for the global sections of a sheaf of `R`-modules.
* `isIso_pullbackObjUnitToUnit`: **the comparison `f^*S ⟶ R` is invertible**, under exactness of
  `v_s`.
* `isIso_pullbackObjUnitToUnit_of_isMorphismOfSites`: the same, with the hypothesis packaged as
  `CategoryTheory.Functor.IsMorphismOfSites` ([Stacks, Tag 00X1]).

## References

* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 03A4](https://stacks.math.columbia.edu/tag/03A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites.UnitComparison

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] (v : C ⥤ D)

/-- **The pushforward of the terminal sheaf of sets is the terminal sheaf of sets**, as an
equality of sheaves. -/
theorem sheafPushforwardContinuous_obj_terminal (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [v.IsContinuous J K] :
    (v.sheafPushforwardContinuous (Type u) J K).obj (Sheaf.terminal K Types.isTerminalPUnit) =
      Sheaf.terminal J Types.isTerminalPUnit :=
  rfl

/-- **The counit of `v_s ⊣ v^s` at the terminal sheaf of sets is invertible** when `v_s` preserves
finite limits. -/
theorem isIso_counit_app_terminal (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [v.IsContinuous J K] [PreservesFiniteLimits (v.sheafPullback (Type u) J K)] :
    IsIso ((v.sheafAdjunctionContinuous (Type u) J K).counit.app
      (Sheaf.terminal K Types.isTerminalPUnit)) := by
  have hsrc : IsTerminal ((v.sheafPullback (Type u) J K).obj
      ((v.sheafPushforwardContinuous (Type u) J K).obj
        (Sheaf.terminal K Types.isTerminalPUnit))) := by
    rw [sheafPushforwardContinuous_obj_terminal]
    exact (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).isTerminalObj _
  exact ⟨hsrc.from _, hsrc.hom_ext _ _,
    (Sheaf.isTerminalTerminal K Types.isTerminalPUnit).hom_ext _ _⟩

/-- **The action of `v^s` on the morphisms out of the terminal sheaf of sets is bijective** when
`v_s` preserves finite limits. -/
theorem bijective_map_of_terminal (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [v.IsContinuous J K] [PreservesFiniteLimits (v.sheafPullback (Type u) J K)]
    (PP : Sheaf K (Type u)) :
    Function.Bijective (fun α : Sheaf.terminal K (A := Type u) Types.isTerminalPUnit ⟶ PP =>
      (v.sheafPushforwardContinuous (Type u) J K).map α) := by
  have := isIso_counit_app_terminal v J K
  have hmap : ∀ α : Sheaf.terminal K (A := Type u) Types.isTerminalPUnit ⟶ PP,
      (v.sheafPushforwardContinuous (Type u) J K).map α =
        (v.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _
          ((v.sheafAdjunctionContinuous (Type u) J K).counit.app
            (Sheaf.terminal K (A := Type u) Types.isTerminalPUnit) ≫ α) := by
    intro α
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      Adjunction.right_triangle_components, Category.id_comp]
  refine ⟨fun a b h ↦ ?_, fun β ↦ ?_⟩
  · dsimp only at h
    rw [hmap a, hmap b] at h
    exact (cancel_epi _).mp
      (((v.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _).injective h)
  · refine ⟨inv ((v.sheafAdjunctionContinuous (Type u) J K).counit.app
      (Sheaf.terminal K (A := Type u) Types.isTerminalPUnit)) ≫
        ((v.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _).symm β, ?_⟩
    dsimp only
    rw [hmap, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp, Equiv.apply_symm_apply]

/-- **Restricting a global section of a sheaf of sets along a morphism of sites is a bijection.**
For `P` a sheaf of sets on `(D, K)`, the map `Γ(D, P) ⟶ Γ(C, v^sP)` reading a compatible family
over the objects of `D` as a compatible family over their images is bijective, provided `v_s`
preserves finite limits. -/
theorem bijective_sectionsPrecomp (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [v.IsContinuous J K] [PreservesFiniteLimits (v.sheafPullback (Type u) J K)]
    (P : Dᵒᵖ ⥤ Type u) (hP : Presheaf.IsSheaf K P) :
    Function.Bijective (v.op.sectionsPrecomp (P := P)) := by
  let e₁ : (Sheaf.terminal K (A := Type u) Types.isTerminalPUnit ⟶
      (⟨P, hP⟩ : Sheaf K (Type u))) ≃ P.sections :=
    Sheaf.homEquiv.trans (P.sectionsEquivHom PUnit).symm
  let e₂ : ((v.sheafPushforwardContinuous (Type u) J K).obj
        (Sheaf.terminal K (A := Type u) Types.isTerminalPUnit) ⟶
      (v.sheafPushforwardContinuous (Type u) J K).obj (⟨P, hP⟩ : Sheaf K (Type u))) ≃
        (v.op ⋙ P).sections :=
    Sheaf.homEquiv.trans ((v.op ⋙ P).sectionsEquivHom PUnit).symm
  exact e₂.bijective.comp
    ((bijective_map_of_terminal v J K ⟨P, hP⟩).comp e₁.symm.bijective)

section Modules

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) [v.IsContinuous J K]
  [PreservesFiniteLimits (v.sheafPullback (Type u) J K)]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (v.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- **Restricting a global section of a sheaf of modules along a morphism of sites is a
bijection**, provided `v_s` preserves finite limits. -/
theorem bijective_pushforwardSections (M : SheafOfModules.{u} R) :
    Function.Bijective (SheafOfModules.pushforwardSections φ (M := M)) :=
  bijective_sectionsPrecomp v J K (M.val.presheaf ⋙ forget AddCommGrpCat.{u})
    ((Presheaf.isSheaf_iff_isSheaf_forget K M.val.presheaf
      (forget AddCommGrpCat.{u})).1 M.isSheaf)

variable [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- **The comparison `f^*S ⟶ R` of a morphism of ringed sites is invertible.**  For a continuous
functor `v : C ⥤ D` whose induced functor `v_s` on sheaves of sets is left exact, and a morphism
of sheaves of rings `φ : S ⟶ f_*R`, Mathlib's `SheafOfModules.pullbackObjUnitToUnit φ` is an
isomorphism. -/
theorem isIso_pullbackObjUnitToUnit :
    IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} φ) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← ((SheafOfModules.pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).bijective.of_comp_iff',
    ← (SheafOfModules.unitHomEquiv _).bijective.of_comp_iff']
  convert! (bijective_pushforwardSections v J K φ M).comp
    (SheafOfModules.unitHomEquiv _).bijective
  ext f : 1
  dsimp
  rw [SheafOfModules.pushforwardSections_unitHomEquiv, EmbeddingLike.apply_eq_iff_eq,
    Adjunction.homEquiv_naturality_right,
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

end Modules

/-- **The comparison `f^*S ⟶ R` is invertible along a morphism of sites**, in the sense of
`CategoryTheory.Functor.IsMorphismOfSites` ([Stacks, Tag 00X1]). -/
theorem isIso_pullbackObjUnitToUnit_of_isMorphismOfSites
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [v.IsContinuous J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (v.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint]
    (h : v.IsMorphismOfSites J K) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} φ) :=
  let := h.preservesFiniteLimits
  isIso_pullbackObjUnitToUnit v J K φ

end Stacks.Sites.UnitComparison

end
