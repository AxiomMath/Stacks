module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineOpenTensorCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineUnitCoherence
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TildeUnitIdentity

/-!
# The unit of a restricted base-change square, read through the projection formula

Let `h' : X'' ⟶ X'`, `f'' : X'' ⟶ Y''` and `h : Y'' ⟶ Y'` complete `f' : X' ⟶ Y'` to a cartesian
square, let `F'` be a quasi-coherent `𝒪_{X'}`-module, and let `V ⊆ Y'` and `W ⊆ Y''` be affine
opens with `W ≤ h⁻¹(V)`. This file identifies two maps of `𝒪_{f'⁻¹(V)}`-modules out of the
restriction of `F'`: the inverse right unitor followed by `F'` tensored with the pullback of the
canonical map `𝒪_V ⟶ (h ∣_ V^W)_* 𝒪_W`, and the unit of `(h' ∣)^* ⊣ (h' ∣)_*` followed by the
inverse of the projection formula of the restricted square. This is the sheaf-level form of the
pure-tensor identity in conclusion (c) of [Stacks, Tag 0EX3].

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorSheafUnitRightIso_inv_comp_tensorSheaf_map`:
  the identity above.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.bifunctor_map_id_comp`: a bifunctor applied to
  `𝟙 A ×ₘ (x ≫ y)` is the composite of its values at `𝟙 A ×ₘ x` and `𝟙 A ×ₘ y`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.comp_insert_iso`: an isomorphism inserted against
  its inverse in the middle of a composite.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- A bifunctor applied to the identity in the first variable splits a composite in the
second: `B (𝟙 A ×ₘ (x ≫ y)) = B (𝟙 A ×ₘ x) ≫ B (𝟙 A ×ₘ y)`. -/
theorem bifunctor_map_id_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (B : C × D ⥤ E) (A : C) {X Y Z : D} (x : X ⟶ Y) (y : Y ⟶ Z) :
    B.map ((𝟙 A ×ₘ (x ≫ y) : ((A, X) : C × D) ⟶ (A, Z))) =
      B.map ((𝟙 A ×ₘ x : ((A, X) : C × D) ⟶ (A, Y))) ≫
        B.map ((𝟙 A ×ₘ y : ((A, Y) : C × D) ⟶ (A, Z))) := by
  rw [← B.map_comp]
  simp

/-- Inserting an isomorphism against its inverse in the middle of a composite: if
`a ≫ b ≫ i.hom = e`, then `a ≫ b ≫ c = e ≫ i.inv ≫ c`. -/
theorem comp_insert_iso {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ : C}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (i : A₂ ≅ A₃) (c : A₂ ⟶ A₄) {e : A₀ ⟶ A₃}
    (he : a ≫ b ≫ i.hom = e) : a ≫ b ≫ c = e ≫ i.inv ≫ c := by
  subst he
  simp

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (hsq : IsPullback h' f'' S.f' h)
  {V : S.Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
  (hWV : W ≤ h ⁻¹ᵁ V)

/-- **The unit of `(h' ∣)^* ⊣ (h' ∣)_*` over a compatible pair of affine opens, read through the
projection formula.** For any map `m` out of the structure sheaf of `f'⁻¹(V)` which is the
pullback of the canonical `𝒪_V ⟶ (h ∣_ V^W)_* 𝒪_W` of [Stacks, Tag 01I7] followed by the
identification of that direct image with the module associated to its sections, tensoring `m`
into the restriction of `F'` against the right unitor gives the unit of `(h' ∣)^* ⊣ (h' ∣)_*`,
followed by the inverse of the projection formula of the restricted square and by that same
identification. -/
theorem tensorSheafUnitRightIso_inv_comp_tensorSheaf_map
    (m : Scheme.unitModule (S.f' ⁻¹ᵁ V : Scheme) ⟶
      (Scheme.Modules.pullback (S.f' ∣_ V)).obj
        ((Stacks.Coherent.affineTilde (V : Scheme)).obj
          ((_root_.SheafOfModules.evaluation (V : Scheme).ringCatSheaf (op ⊤)).obj
            ((Scheme.Modules.pushforward (h.resLE V W hWV)).obj
              (Scheme.unitModule (W : Scheme))))))
    (hm : m = ((Scheme.Modules.pullbackUnitIso (S.f' ∣_ V)).inv ≫
        (Scheme.Modules.pullback (S.f' ∣_ V)).map
          (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV))) ≫
      (Scheme.Modules.pullback (S.f' ∣_ V)).map
        (pushforwardUnitIsoAffineTilde (h.resLE V W hWV)).inv) :
    (tensorSheafUnitRightIso (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace
          ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')).inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
              (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
          (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ m) =
      (Scheme.Modules.pullbackPushforwardAdjunction
            (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
              (preimage_le_preimage_of_isPullback hsq hWV))).unit.app
          ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ≫
        (pushforwardPullbackTensorIsoRight (S.f' ∣_ V)
            (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
              (preimage_le_preimage_of_isPullback hsq hWV))
            (f'' ∣_ W) (h.resLE V W hWV) (isPullback_resLE_of_isPullback hsq hWV)
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
            (Scheme.Modules.isQuasicoherent_restrictFunctor (S.f' ⁻¹ᵁ V).ι F')).inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
              (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
          (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
            (Scheme.Modules.pullback (S.f' ∣_ V)).map
              (pushforwardUnitIsoAffineTilde (h.resLE V W hWV)).inv) := by
  subst hm
  exact Eq.trans
    (congrArg (fun z => (tensorSheafUnitRightIso (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace
        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')).inv ≫ z)
      (bifunctor_map_id_comp (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
            (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩))
        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
        ((Scheme.Modules.pullbackUnitIso (S.f' ∣_ V)).inv ≫
          (Scheme.Modules.pullback (S.f' ∣_ V)).map
            (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV)))
        ((Scheme.Modules.pullback (S.f' ∣_ V)).map
          (pushforwardUnitIsoAffineTilde (h.resLE V W hWV)).inv)))
    (comp_insert_iso _ _ _ _
      (unit_eq_pushforwardPullbackTensorIsoRight (S.f' ∣_ V)
        (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) (preimage_le_preimage_of_isPullback hsq hWV))
        (f'' ∣_ W) (h.resLE V W hWV) (isPullback_resLE_of_isPullback hsq hWV)
        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
        (Scheme.Modules.isQuasicoherent_restrictFunctor (S.f' ⁻¹ᵁ V).ι F')))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
