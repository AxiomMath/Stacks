module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.RelativeHodgePairing

/-!
# When the map determined by a pairing is an isomorphism

Let `T ⊣ H` be a tensor–internal-Hom adjunction on a category `C`, so that a pairing
`φ : A ⊗ B ⟶ M` determines a map `A ⟶ H(B, M)`. That map is an isomorphism exactly when every
morphism `Z ⊗ B ⟶ M` is `(v ⊗ 1) ≫ φ` for a unique `v : Z ⟶ A`: the map determined by
`(v ⊗ 1) ≫ φ` is `v` followed by the map determined by `φ`, and the Yoneda lemma applies. In
particular this property survives composing the pairing with an isomorphism `M ≅ M'`.

## Main results

In the namespace `Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction`:

* `isIso_homEquiv_symm_iff`: the criterion.
* `isIso_homEquiv_symm_comp_of_isIso`: composing with an isomorphism of the target.
* `isZero_obj_obj_of_isZero`: the internal Hom out of a zero object is zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction

variable {C : Type*} {_ : Category* C} {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C}
  (DY : TensorHomAdjunction T H)

/-- **The map determined by a pairing is an isomorphism iff the pairing is universal**: for
`φ : A ⊗ B ⟶ M`, the map `A ⟶ H(B, M)` it determines is an isomorphism iff for every `Z` the
map `(Z ⟶ A) ⟶ (Z ⊗ B ⟶ M)`, `v ↦ (v ⊗ 1) ≫ φ`, is bijective. -/
theorem isIso_homEquiv_symm_iff {A B M : C} (φ : (T.obj A).obj B ⟶ M) :
    IsIso ((DY.homEquiv A B M).symm φ) ↔
      ∀ Z : C, Function.Bijective (fun v : Z ⟶ A => (T.map v).app B ≫ φ) := by
  have e : ∀ Z : C, (fun v : Z ⟶ A => (T.map v).app B ≫ φ) =
      (DY.homEquiv Z B M) ∘ (fun v : Z ⟶ A => v ≫ (DY.homEquiv A B M).symm φ) := fun Z =>
    funext fun v => ((Equiv.symm_apply_eq _).1 (homEquiv_symm_map_app_comp DY v φ))
  refine ⟨fun h Z => ?_, fun h => ?_⟩
  · rw [e Z]
    exact (DY.homEquiv Z B M).bijective.comp
      ⟨fun x y hxy => (cancel_mono _).1 hxy,
        fun y => ⟨y ≫ inv ((DY.homEquiv A B M).symm φ), by simp⟩⟩
  · refine isIso_of_yoneda_map_bijective _ fun Z => ?_
    have := h Z
    rw [e Z] at this
    exact (Function.Bijective.of_comp_iff' (DY.homEquiv Z B M).bijective _).1 this

/-- **Composing a pairing with an isomorphism of the target**: if `φ : A ⊗ B ⟶ M` determines an
isomorphism `A ≅ H(B, M)` and `e : M ⟶ M'` is an isomorphism, then `φ ≫ e` determines an
isomorphism `A ≅ H(B, M')`. -/
theorem isIso_homEquiv_symm_comp_of_isIso {A B M M' : C} (φ : (T.obj A).obj B ⟶ M) (e : M ⟶ M')
    (hφ : IsIso ((DY.homEquiv A B M).symm φ)) (he : IsIso e) :
    IsIso ((DY.homEquiv A B M').symm (φ ≫ e)) := by
  refine (isIso_homEquiv_symm_iff DY _).2 fun Z => ?_
  have h := (isIso_homEquiv_symm_iff DY _).1 hφ Z
  have : (fun v : Z ⟶ A => (T.map v).app B ≫ φ ≫ e) =
      (fun k => k ≫ e) ∘ (fun v : Z ⟶ A => (T.map v).app B ≫ φ) :=
    funext fun v => (Category.assoc _ _ _).symm
  rw [this]
  exact Function.Bijective.comp (asIso e).homToEquiv.bijective h

section Zero

variable {C : Type*} {_ : Category* C} [HasZeroMorphisms C] {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C}

/-- **Pairing against a zero object**: for a tensor product preserving zero morphisms in each
variable, `H(L, M)` is a zero object when `L` is, since then `W ⊗ L` is for every `W`. -/
theorem isZero_obj_obj_of_isZero (DY : TensorHomAdjunction T H)
    [∀ W : C, (T.obj W).PreservesZeroMorphisms] {L : C}
    (hL : IsZero L) (M : C) : IsZero ((H.obj (op L)).obj M) := by
  rw [IsZero.iff_id_eq_zero]
  refine (DY.homEquiv _ L M).injective ?_
  exact (Functor.map_isZero (T.obj _) hL).eq_of_src _ _

end Zero

end Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction

end
