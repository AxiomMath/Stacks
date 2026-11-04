module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.Over

/-! # The pushforward of the localization of a topos at a sheaf

Let `E` be a topos (in this file: any cartesian monoidal category, braided so that the two
factors of a product may be interchanged) and let `F` be an object of `E`.  The localization
morphism `j_F : E/F ⟶ E` has `j_{F!} = Over.forget F` and `j_F⁻¹ = toOver F`, the two being
adjoint by `CategoryTheory.forgetAdjToOver`; its pushforward `j_{F,*}` is by definition a right
adjoint of `toOver F`.  (`toOver F : A ↦ (A ⊗ F ⟶ F)` is Mathlib's computable form of
`Over.star F`, the functor used for `j_F⁻¹` in Stacks 04IP.)

Stacks 04H0 computes that pushforward: `j_{F,*}` sends an object `φ : G ⟶ F` of `E/F` to the
sheaf whose sections over `U` are the right inverses of the restriction `φ|_U`.  Since
`Γ(U, H) = Hom(h_U^#, H)` and restriction to `U` is `j_U⁻¹`, this is the statement proved
below, with the representable sheaf `h_U^#` replaced by an arbitrary object `A` of `E`.

## Main results

* `homPushforwardEquivRightInverse` (Stacks 04H0): for every object `A` of `E`, the maps
  `A ⟶ j_{F,*}(G/F)` correspond bijectively to the right inverses of `φ|_A` in `E/A`.

Tags covered: 04H0.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory

universe v u

variable {E : Type u} [Category.{v} E]

/-- A morphism `(Y ⟶ X) ⟶ (Z ⟶ X)` of `E/X` is a morphism `Y ⟶ Z` of `E` over `X`. -/
def Over.mkHomEquiv {X Y Z : E} (f : Y ⟶ X) (g : Z ⟶ X) :
    (Over.mk f ⟶ Over.mk g) ≃ { u : Y ⟶ Z // u ≫ g = f } where
  toFun u := ⟨u.left, Over.w u⟩
  invFun u := Over.homMk u.1 u.2
  left_inv _ := rfl
  right_inv _ := rfl

variable [CartesianMonoidalCategory E] {A F G : E}

/-- A morphism `w : F ⊗ A ⟶ G ⊗ A` of `E/A` is right inverse to `φ|_A = φ ▷ A` exactly when its
first component `w ≫ fst G A` is a morphism `F ⊗ A ⟶ G` over `F`. -/
lemma comp_whiskerRight_eq_id_iff (φ : G ⟶ F) (w : F ⊗ A ⟶ G ⊗ A)
    (hw : w ≫ snd G A = snd F A) :
    w ≫ φ ▷ A = 𝟙 (F ⊗ A) ↔ (w ≫ fst G A) ≫ φ = fst F A := by
  refine ⟨fun h => ?_, fun h => hom_ext _ _ ?_ ?_⟩
  · rw [Category.assoc, ← whiskerRight_fst φ A, reassoc_of% h]
  · rw [Category.assoc, whiskerRight_fst, Category.id_comp, ← Category.assoc, h]
  · rw [Category.assoc, whiskerRight_snd, Category.id_comp, hw]

/-- A morphism `w : F ⊗ A ⟶ G ⊗ A` of `E/A` is determined by its first component. -/
lemma eq_lift_comp_fst (w : F ⊗ A ⟶ G ⊗ A) (hw : w ≫ snd G A = snd F A) :
    w = lift (w ≫ fst G A) (snd F A) := hom_ext _ _ (by simp) (by simp [hw])

/-- The right inverses of the restriction `φ|_A = (toOver A).map φ` in `E/A` are exactly the
morphisms `a : F ⊗ A ⟶ G` with `a ≫ φ = fst F A`, the bijection sending a right inverse to its
first component. -/
def toOverRightInverseEquiv (φ : G ⟶ F) (A : E) :
    { α : (toOver A).obj F ⟶ (toOver A).obj G // α ≫ (toOver A).map φ = 𝟙 _ } ≃
      { a : F ⊗ A ⟶ G // a ≫ φ = fst F A } where
  toFun α := ⟨α.1.left ≫ fst G A,
    (comp_whiskerRight_eq_id_iff φ _ (Over.w α.1)).1 (congrArg Over.Hom.left α.2)⟩
  invFun a := ⟨Over.homMk (lift a.1 (snd F A)) (lift_snd _ _),
    Over.OverMorphism.ext
      ((comp_whiskerRight_eq_id_iff φ _ (lift_snd _ _)).2 (by rw [lift_fst]; exact a.2))⟩
  left_inv α := Subtype.ext (Over.OverMorphism.ext (eq_lift_comp_fst _ (Over.w α.1)).symm)
  right_inv _ := Subtype.ext (lift_fst _ _)

/-- **Stacks 04H0.** Let `E` be a topos, `F` an object of `E` and `j_{F,*} = p` a pushforward
for the localization `j_F : E/F ⟶ E`, i.e. a right adjoint of `j_F⁻¹ = toOver F`.  For an object
`φ : G ⟶ F` of `E/F` and any object `A` of `E`, the maps `A ⟶ j_{F,*}(G/F)` are in bijection
with the morphisms `α : F|_A ⟶ G|_A` of `E/A` that are right inverse to `φ|_A`, restriction to
`A` being `(-)|_A = j_A⁻¹ = toOver A`.

Taking `A = h_U^#` and using `Γ(U, -) = Hom(h_U^#, -)` this is Stacks 04H0: the sections of
`j_{F,*}(G/F)` over `U` are the right inverses of `φ|_U`.  The proof follows the Stacks one: the
adjunction defining `p` identifies `Hom(A, j_{F,*}(G/F))` with the fibre of `φ ∘ (-)` over the
projection `A ⊗ F ⟶ F`, and interchanging the two factors turns that fibre into the set of right
inverses of `φ|_A`.

Two things are *not* covered: the bijection is stated pointwise in `A`, its naturality in `A`
(which is what makes the right-inverse description a description of the sheaf rather than of its
individual section sets) being left implicit; and `F|_A` is read in the slice `E/A`, whereas
Stacks reads it in `Sh(C/U)` via the equivalence `Sh(C/U) ≃ Sh(C)/h_U^#` of Stacks 00Y1, which
is not yet available. -/
@[stacks 04H0]
def homPushforwardEquivRightInverse [BraidedCategory E] {p : Over F ⥤ E} (adj : toOver F ⊣ p)
    (φ : G ⟶ F) (A : E) :
    (A ⟶ p.obj (Over.mk φ)) ≃
      { α : (toOver A).obj F ⟶ (toOver A).obj G // α ≫ (toOver A).map φ = 𝟙 _ } :=
  ((adj.homEquiv A (Over.mk φ)).symm.trans (Over.mkHomEquiv (snd A F) φ)).trans
    (((toOverRightInverseEquiv φ A).trans
      (Equiv.subtypeEquiv (Iso.homCongr (β_ F A) (Iso.refl G)) fun a => by
        simp only [Iso.homCongr, Equiv.coe_fn_mk, Iso.refl_hom, Category.comp_id, Category.assoc]
        refine ⟨fun h => by rw [h]; simp, fun h => ?_⟩
        rw [← cancel_epi (β_ F A).inv]
        simpa using h)).symm)

end CategoryTheory
