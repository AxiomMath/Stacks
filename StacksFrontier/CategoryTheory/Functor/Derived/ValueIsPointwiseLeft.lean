module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksFrontier.CategoryTheory.Functor.Derived.ValueIsPointwise

/-!
# A Deligne value of `LF` at `X` is a pointwise left derived functor at `X`

This is the dual of `StacksFrontier.CategoryTheory.Functor.Derived.ValueIsPointwise`. Let
`F : 𝒞 ⥤ ℋ` be a functor, let `W` be a class of morphisms of `𝒞` and let `X` be an object of
`𝒞`. If the pro-object `W/X ⟶ ℋ`, `(s : X' ⟶ X) ↦ F(X')` is essentially constant
(`CategoryTheory.Functor.IsLeftDerivedValueAt`, Stacks 05S9(2)) and `W` has a right calculus of
fractions, then `F` has a pointwise left derived functor at `X` in Mathlib's sense
(`CategoryTheory.Functor.HasPointwiseLeftDerivedFunctorAt`): a pointwise right Kan extension
along a localization functor `L` for `W` at `L(X)`.

## Main results

* `CategoryTheory.MorphismProperty.overToStructuredArrow`: the comparison functor
  `Ψ : W/X ⥤ StructuredArrow (L.obj X) L` sending `(s : X' ⟶ X)` in `W` to `X'` equipped with
  the inverse of `L(s)`.
* `CategoryTheory.MorphismProperty.initial_overToStructuredArrow`: `Ψ` is an initial functor,
  when `W` has a right calculus of fractions.
* `CategoryTheory.Functor.hasPointwiseLeftDerivedFunctorAt_of_isLeftDerivedValueAt` and
  `CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_isLeftDerivable`.

## Hypotheses used, and why

The right calculus of fractions is used, dually to the left calculus in the right-hand file, to
prove that `Ψ` is initial: every morphism `g : L(X) ⟶ L(Y)` is a right fraction `L(s)⁻¹ ∘ L(f)`
with `s : X' ⟶ X` in `W` (`CategoryTheory.Localization.exists_rightFraction`), and two right
fractions with the same image are related by `RightFractionRel`
(`CategoryTheory.MorphismProperty.RightFraction.map_eq_iff`). Nothing else is assumed. The
converse is not claimed.

## References

* [Stacks, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9) (Deligne's condition)
* [Stacks, Tag 05Q4](https://stacks.math.columbia.edu/tag/05Q4) (the index category `W/X`)
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace MorphismProperty

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W] (X : C)

/-- The isomorphism `L(X') ≅ L(X)` attached to an object `(s : X' ⟶ X)` of the index category
`W/X` of Stacks 05S9, available because a localization functor inverts `W`.

This is `CategoryTheory.Localization.isoOfHom` at `s.hom`, with target `L.obj X`. -/
noncomputable def overIso (s : W.Over ⊤ X) : L.obj s.left ≅ L.obj X :=
  Localization.isoOfHom L W s.hom s.prop

/-- The forward map of `W.overIso L X s` is `L.map s.hom`. -/
@[simp]
lemma overIso_hom (s : W.Over ⊤ X) : (W.overIso L X s).hom = L.map s.hom :=
  rfl

/-- The comparison functor `Ψ : W/X ⥤ StructuredArrow (L.obj X) L` between Deligne's index
category of Stacks 05S9 and the index category of the pointwise right Kan extension of a functor
along a localization functor `L` for `W` at `L(X)`.

An object `(s : X' ⟶ X)` of `W/X` is sent to `X'` equipped with the arrow
`L(s)⁻¹ : L(X) ⟶ L(X')`, and a morphism `u` of `W/X` to the underlying morphism `u.left` of
`𝒞`; the commutation condition in the comma category is `L(s)⁻¹ ≫ L(u.left) = L(t)⁻¹`, which
follows from `u.left ≫ t = s`. -/
noncomputable def overToStructuredArrow :
    W.Over ⊤ X ⥤ CategoryTheory.StructuredArrow (L.obj X) L where
  obj s := CategoryTheory.StructuredArrow.mk (W.overIso L X s).inv
  map {s t} u := CategoryTheory.StructuredArrow.homMk u.left (by
    have hw : (u.left ≫ t.hom : s.left ⟶ X) = s.hom := MorphismProperty.Over.w u
    have hL : L.map u.left ≫ (W.overIso L X t).hom = (W.overIso L X s).hom := by
      simp only [overIso_hom, ← Functor.map_comp, hw]
    change (W.overIso L X s).inv ≫ L.map u.left = (W.overIso L X t).inv
    rw [Iso.inv_comp_eq, Iso.eq_comp_inv]
    exact hL)
  map_id s := by ext; simp
  map_comp u v := by ext; simp

/-- The underlying object of the image of `s` under `W.overToStructuredArrow L X` is
`s.left`. -/
@[simp]
lemma overToStructuredArrow_obj_right (s : W.Over ⊤ X) :
    ((W.overToStructuredArrow L X).obj s).right = s.left :=
  rfl

/-- The underlying morphism of the image of `u` under `W.overToStructuredArrow L X` is
`u.left`. -/
@[simp]
lemma overToStructuredArrow_map_right {s t : W.Over ⊤ X} (u : s ⟶ t) :
    ((W.overToStructuredArrow L X).map u).right = u.left :=
  rfl

/-- The image in the localization of the right fraction `s⁻¹ f`, computed by its defining
property: it is `g` as soon as `L(f) = L(s) ≫ g`. -/
lemma rightFraction_map_eq {Y A : C} (g : L.obj X ⟶ L.obj Y) (f : A ⟶ Y) (s : A ⟶ X) (hs : W s)
    (w : L.map f = L.map s ≫ g) :
    (RightFraction.mk s hs f).map L (Localization.inverts L W) = g := by
  have := Localization.inverts L W s hs
  rw [← cancel_epi (L.map s), ← w]
  exact RightFraction.map_s_comp_map (RightFraction.mk s hs f) L (Localization.inverts L W)

/-- An object of `CostructuredArrow Ψ d`, for `d` an object of `StructuredArrow (L.obj X) L`,
out of a right fraction: an arrow `s : A ⟶ X` in `W`, an arrow `f : A ⟶ d.right` and the identity
`L(f) = L(s) ≫ d.hom`, which says that `d.hom` is the fraction `s⁻¹ f`. -/
noncomputable def costructuredArrowMk (d : CategoryTheory.StructuredArrow (L.obj X) L) {A : C}
    (f : A ⟶ d.right) (s : A ⟶ X) (hs : W s) (w : L.map f = L.map s ≫ d.hom) :
    CategoryTheory.CostructuredArrow (W.overToStructuredArrow L X) d :=
  CategoryTheory.CostructuredArrow.mk (Y := MorphismProperty.Over.mk ⊤ s hs)
    (CategoryTheory.StructuredArrow.homMk f
      ((Iso.inv_comp_eq (W.overIso L X (MorphismProperty.Over.mk ⊤ s hs))).2 w))

/-- Every object of `CostructuredArrow Ψ d` is of the form
`CategoryTheory.MorphismProperty.costructuredArrowMk`: it is a factorization of `d.hom` as a
right fraction. -/
lemma exists_eq_costructuredArrowMk (d : CategoryTheory.StructuredArrow (L.obj X) L)
    (A : CategoryTheory.CostructuredArrow (W.overToStructuredArrow L X) d) :
    ∃ (A' : C) (f : A' ⟶ d.right) (s : A' ⟶ X) (hs : W s) (w : L.map f = L.map s ≫ d.hom),
      A = W.costructuredArrowMk L X d f s hs w :=
  ⟨A.left.left, A.hom.right, A.left.hom, A.left.prop,
    (Iso.inv_comp_eq (W.overIso L X A.left)).1 (CategoryTheory.StructuredArrow.w A.hom), rfl⟩

/-- **The dual comparison functor is initial.** For `W` with a right calculus of fractions, the
functor `Ψ : W/X ⥤ StructuredArrow (L.obj X) L` of
`CategoryTheory.MorphismProperty.overToStructuredArrow` is initial.

Fix `d = (Y, g : L(X) ⟶ L(Y))`. The category `CostructuredArrow Ψ d` is the category of
factorizations of `g` as a right fraction: an object is an arrow `s : X' ⟶ X` of `W` together
with `f : X' ⟶ Y` satisfying `L(f) = L(s) ≫ g`. It is nonempty because `g` is a right fraction
(`CategoryTheory.Localization.exists_rightFraction`), and connected because two right fractions
with the same image in the localization are related by `RightFractionRel`
(`CategoryTheory.MorphismProperty.RightFraction.map_eq_iff`), whose witnessing object maps to
both, giving a zigzag of length two. -/
theorem initial_overToStructuredArrow [W.HasRightCalculusOfFractions] :
    (W.overToStructuredArrow L X).Initial where
  out d := by
    have hne : Nonempty (CategoryTheory.CostructuredArrow (W.overToStructuredArrow L X) d) := by
      obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L W d.hom
      refine ⟨W.costructuredArrowMk L X d φ.f φ.s φ.hs ?_⟩
      rw [hφ, RightFraction.map_s_comp_map]
    have hzz : ∀ A B : CategoryTheory.CostructuredArrow (W.overToStructuredArrow L X) d,
        Zigzag A B := by
      intro A B
      obtain ⟨A', fA, sA, hsA, wA, rfl⟩ := W.exists_eq_costructuredArrowMk L X d A
      obtain ⟨B', fB, sB, hsB, wB, rfl⟩ := W.exists_eq_costructuredArrowMk L X d B
      have key : (RightFraction.mk sA hsA fA).map L (Localization.inverts L W)
          = (RightFraction.mk sB hsB fB).map L (Localization.inverts L W) := by
        rw [W.rightFraction_map_eq L X _ _ _ _ wA, W.rightFraction_map_eq L X _ _ _ _ wB]
      obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := (RightFraction.map_eq_iff L W _ _).1 key
      have wT : L.map (t₁ ≫ fA) = L.map (t₁ ≫ sA) ≫ d.hom := by
        simp only [Functor.map_comp, wA, Category.assoc]
      exact Zigzag.of_inv_hom
        (CategoryTheory.CostructuredArrow.homMk
          (f := W.costructuredArrowMk L X d (t₁ ≫ fA) (t₁ ≫ sA) ht wT)
          (MorphismProperty.Over.homMk t₁ rfl)
          (CategoryTheory.StructuredArrow.hom_ext _ _ rfl))
        (CategoryTheory.CostructuredArrow.homMk
          (f := W.costructuredArrowMk L X d (t₁ ≫ fA) (t₁ ≫ sA) ht wT)
          (MorphismProperty.Over.homMk t₂ hst.symm)
          (CategoryTheory.StructuredArrow.hom_ext _ _ hft.symm))
    exact @zigzag_isConnected _ _ hne hzz

end MorphismProperty

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

/-- Deligne's pro-object `W/X ⟶ ℋ`, `(s : X' ⟶ X) ↦ F(X')` of Stacks 05S9 is the comparison
functor `CategoryTheory.MorphismProperty.overToStructuredArrow` followed by the diagram whose
limit is the pointwise right Kan extension of `F` along `L` at `L(X)`. The two functors agree on
objects and on morphisms, so the isomorphism has identity components. -/
noncomputable def overToStructuredArrowCompProjCompIso (F : C ⥤ H) (W : MorphismProperty C)
    (L : C ⥤ D) [L.IsLocalization W] (X : C) :
    W.overToStructuredArrow L X ⋙ StructuredArrow.proj (L.obj X) L ⋙ F ≅
      MorphismProperty.Over.forget W ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ F :=
  NatIso.ofComponents (fun s => Iso.refl (F.obj s.left)) (fun u => by simp)

/-- If `W` has a right calculus of fractions and some cone on the pro-object
`W/X ⟶ ℋ`, `(s : X' ⟶ X) ↦ F(X')` is a value of the left derived functor of `F` at `X` in
Deligne's sense (Stacks 05S9, `CategoryTheory.Functor.IsLeftDerivedValueAt`), then `F` has a
pointwise left derived functor at `X` in Mathlib's sense, i.e. `F` has a pointwise right Kan
extension along any localization functor for `W` at the image of `X`.

A Deligne value is a limit cone (`IsLeftDerivedValueAt.isLimit`), and the pro-object is the
initial comparison functor `Ψ` (`MorphismProperty.initial_overToStructuredArrow`) followed by the
Kan-extension diagram, so the Kan-extension diagram has a limit too. -/
theorem hasPointwiseLeftDerivedFunctorAt_of_isLeftDerivedValueAt (F : C ⥤ H)
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] (X : C)
    {c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ F)}
    (hc : F.IsLeftDerivedValueAt W X c) :
    F.HasPointwiseLeftDerivedFunctorAt W X := by
  have : HasLimit
      (MorphismProperty.Over.forget W ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ F) :=
    HasLimit.mk ⟨c, hc.isLimit⟩
  have : (W.overToStructuredArrow W.Q X).Initial :=
    W.initial_overToStructuredArrow W.Q X
  have : HasLimit (W.overToStructuredArrow W.Q X ⋙
      StructuredArrow.proj (W.Q.obj X) W.Q ⋙ F) :=
    hasLimit_of_iso (F.overToStructuredArrowCompProjCompIso W W.Q X).symm
  rw [F.hasPointwiseLeftDerivedFunctorAt_iff W.Q W X]
  exact Initial.hasLimit_of_comp (W.overToStructuredArrow W.Q X)

/-- A functor that is left derivable relative to a class of
morphisms with a right calculus of fractions has a pointwise left derived functor. -/
theorem hasPointwiseLeftDerivedFunctor_of_isLeftDerivable (F : C ⥤ H)
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] (hF : F.IsLeftDerivable W) :
    F.HasPointwiseLeftDerivedFunctor W := fun X =>
  (hF X).elim fun _ hc =>
    F.hasPointwiseLeftDerivedFunctorAt_of_isLeftDerivedValueAt W X hc

end Functor

end CategoryTheory

end
