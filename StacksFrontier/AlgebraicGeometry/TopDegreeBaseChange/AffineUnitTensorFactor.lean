module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineUnitTensorCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.PullbackTildeUnitFactor
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TildeUnitIdentity

/-!
# The Eilenberg-Watts unit of (b) is the canonical map of structure sheaves, tensored into `F'`

Over a compatible pair of affine opens — `V` of `Y'` and `W` of `Y''` with `W ≤ h⁻¹(V)` — the
Eilenberg-Watts presentation of [Stacks, Tag 0EX3] (b) produces one map
`F'| ⟶ F'| ⊗ (f' ∣_ V)^* (Γ((h ∣_ V^W)_* 𝒪_W))~` out of the restriction of `F'`: the identification
of the value of its geometric factor at the base ring with `F'|`, inverted, followed by the image
under that factor of the ring unit `r ↦ r • 1` and by the comparison of the two tilde functors.

**This file identifies that map** with the right unitor, inverted, followed by tensoring in the
canonical map of structure sheaves of [Stacks, Tag 01I7] — which is the map the sheaf-level
pure-tensor identity `…TopDegreeBaseChange.tensorSheafUnitRightIso_inv_comp_tensorSheaf_map`
consumes. So the Eilenberg-Watts side of conclusion (c) is in the shape the geometric side is
stated at.

## Main results

* `…TopDegreeBaseChange.tensorSheaf_map_pullbackTildeUnit_comp`: the identity. Neither base
  carries a hypothesis; only the two opens are affine.
* `…TopDegreeBaseChange.bifunctor_map_id_comp₄` and `…TopDegreeBaseChange.comp_assoc_rewrite_two`:
  the two rearrangements it needs, at variables of abstract categories.

## Implementation notes

*Two facts do the work.* `…TopDegreeBaseChange.pullbackTildeUnitIso_hom_eq` says the
Eilenberg-Watts unitor of the geometric factor — which is the pullback of
`AlgebraicGeometry.tildeSelf` followed by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` — is
`…TopDegreeBaseChange.pullbackTildeUnitIso`; and
`…TopDegreeBaseChange.pullbackTildeUnitIso_inv_comp_pullbackTildeSectionsIso`, at the ring unit,
says that composing it with the tilde of the unit and the tilde crossing gives the pullback of the
canonical map of structure sheaves. The hypothesis the second needs is
`…TopDegreeBaseChange.toSpanSingleton_comp_sectionsIsoPushforwardUnitSections`.

*The rearrangements are hoisted onto variables*, as the directory does for the same shape in
`…TopDegreeBaseChange.comp_assoc_cancel_middle`: splitting `𝟙 ⊗ -` across a composite and
reassociating are free at variables of abstract categories and do not fire at the concrete
spelling, where the goal is not type-correct at `implicit` transparency.

*No `@[stacks 0EX3]` attribute is placed.* This is one step of the computation of conclusion (c).

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped CategoryTheory.Prod
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **A bifunctor applied to the identity in the first variable splits a four-fold composite in
the second.** Stated at variables of abstract categories, where it is free. -/
theorem bifunctor_map_id_comp₄ {C D E : Type*} [Category C] [Category D] [Category E]
    (B : C × D ⥤ E) (A : C) {X₁ X₂ X₃ X₄ X₅ : D}
    (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄) (d : X₄ ⟶ X₅) {e : X₁ ⟶ X₅}
    (he : a ≫ b ≫ c ≫ d = e) :
    B.map ((𝟙 A ×ₘ a : ((A, X₁) : C × D) ⟶ (A, X₂))) ≫
        B.map ((𝟙 A ×ₘ b : ((A, X₂) : C × D) ⟶ (A, X₃))) ≫
        B.map ((𝟙 A ×ₘ c : ((A, X₃) : C × D) ⟶ (A, X₄))) ≫
        B.map ((𝟙 A ×ₘ d : ((A, X₄) : C × D) ⟶ (A, X₅))) =
      B.map ((𝟙 A ×ₘ e : ((A, X₁) : C × D) ⟶ (A, X₅))) := by
  rw [← he, bifunctor_map_id_comp, bifunctor_map_id_comp, bifunctor_map_id_comp]

/-- **Rewriting the first two factors of a three-fold composite.** Stated at variables of an
abstract category, where the reassociation is free. -/
theorem comp_assoc_rewrite_two {C : Type*} [Category C] {A₀ A₁ A₂ A₃ : C}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) {u : A₀ ⟶ A₂} (hu : a ≫ b = u)
    {e : A₀ ⟶ A₃} (he : u ≫ c = e) : a ≫ b ≫ c = e := by
  rw [← he, ← hu, Category.assoc]

variable {Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h : Y'' ⟶ S.Y')
  {V : S.Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
  (hWV : W ≤ h ⁻¹ᵁ V)

omit [SheafOfModules.IsQuasicoherent F'] in
/-- **The Eilenberg-Watts unit of [Stacks, Tag 0EX3] (b) over a pair of affine opens, tensored
into `F'`.** The identification of the value at the base ring of the geometric factor of
conclusion (b) with the restriction of `F'`, inverted, followed by that factor applied to the ring
unit `r ↦ r • 1` and by the comparison of the two tilde functors, is the right unitor inverted
followed by tensoring in the pullback of the canonical map
`𝒪_V ⟶ (h ∣_ V^W)_* 𝒪_W` of [Stacks, Tag 01I7], read through the identification of that direct
image with the module associated to its sections.

Neither `Y'` nor `Y''` carries a hypothesis; only the two opens are affine. -/
theorem tensorSheaf_map_pullbackTildeUnit_comp
    (ψ : ModuleCat.of Γ((V : Scheme), ⊤) Γ((V : Scheme), ⊤) ⟶
      (ModuleCat.restrictScalars
        ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom)).obj
          (ModuleCat.of Γ(Y'', W) Γ(Y'', W)))
    (hψ : ψ ≫ (sectionsIsoPushforwardUnitSections S h hWV).hom =
      (_root_.SheafOfModules.evaluation (V : Scheme).ringCatSheaf (op ⊤)).map
        (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV))) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
          (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
          (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
            (Scheme.Modules.pullbackUnitIso
              ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).inv) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
              (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
          (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
            (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
              (AlgebraicGeometry.tildeSelf
                (R := CommRingCat.of Γ((V : Scheme), ⊤))).inv) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
              (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
          (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
            (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
              ((AlgebraicGeometry.tilde.functor
                (CommRingCat.of Γ((V : Scheme), ⊤))).map ψ)) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
              (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
          (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
            (pullbackTildeSectionsIso S h hWV).hom) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
            (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
        (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
          ((Scheme.Modules.pullbackUnitIso (S.f' ∣_ V)).inv ≫
            (Scheme.Modules.pullback (S.f' ∣_ V)).map
              (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV) ≫
                (pushforwardUnitIsoAffineTilde (h.resLE V W hWV)).inv))) := by
  have hiso : pullbackTildeUnitIso S.f' V =
      (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).mapIso
          (AlgebraicGeometry.tildeSelf (R := CommRingCat.of Γ((V : Scheme), ⊤))) ≪≫
        Scheme.Modules.pullbackUnitIso ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom) :=
    Iso.ext (pullbackTildeUnitIso_hom_eq S.f' V)
  have hinv : (Scheme.Modules.pullbackUnitIso
          ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).inv ≫
        (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
          (AlgebraicGeometry.tildeSelf (R := CommRingCat.of Γ((V : Scheme), ⊤))).inv =
      (pullbackTildeUnitIso S.f' V).inv :=
    (congrArg Iso.inv hiso).symm
  have hsheaf : (Scheme.Modules.pullbackUnitIso
            ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).inv ≫
        (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
          (AlgebraicGeometry.tildeSelf (R := CommRingCat.of Γ((V : Scheme), ⊤))).inv ≫
        (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
          ((AlgebraicGeometry.tilde.functor (CommRingCat.of Γ((V : Scheme), ⊤))).map ψ) ≫
        (pullbackTildeSectionsIso S h hWV).hom =
      (Scheme.Modules.pullbackUnitIso (S.f' ∣_ V)).inv ≫
        (Scheme.Modules.pullback (S.f' ∣_ V)).map
          (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV) ≫
            (pushforwardUnitIsoAffineTilde (h.resLE V W hWV)).inv) :=
    comp_assoc_rewrite_two _ _ _ hinv
      (pullbackTildeUnitIso_inv_comp_pullbackTildeSectionsIso S h hWV ψ hψ)
  exact bifunctor_map_id_comp₄ (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf, (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩))
    ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') _ _ _ _ hsheaf

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
