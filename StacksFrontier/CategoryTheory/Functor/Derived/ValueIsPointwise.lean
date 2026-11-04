module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt

/-!
# A Deligne value of `RF` at `X` is a pointwise right derived functor at `X`

Let `F : 𝒞 ⥤ ℋ` be a functor, let `W` be a class of morphisms of `𝒞` and let `X` be an object
of `𝒞`. Two conditions say that the right derived functor of `F` relative to `W` "exists at `X`":

* Deligne's, formalized in `StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt` as
  `CategoryTheory.Functor.IsRightDerivedValueAt` (Stacks 05S9): the ind-object
  `X/W ⟶ ℋ`, `(s : X ⟶ X') ↦ F(X')` is essentially constant, i.e. a prescribed cocone on it
  carries a retraction and a cofinal factorization;
* Mathlib's `CategoryTheory.Functor.HasPointwiseRightDerivedFunctorAt`: the functor `F` has a
  pointwise left Kan extension along a localization functor `L` for `W` at `L(X)`, i.e. the
  diagram indexed by `CostructuredArrow L (L.obj X)`, the arrows `L(Y) ⟶ L(X)` of the
  localization, has a colimit.

This file proves that the first implies the second.

## Main results

* `CategoryTheory.MorphismProperty.underToCostructuredArrow`: the comparison functor
  `Φ : X/W ⥤ CostructuredArrow L (L.obj X)` sending `(s : X ⟶ X')` in `W` to `X'` equipped with
  the inverse of `L(s)`, and a morphism under `X` to itself.
* `CategoryTheory.MorphismProperty.final_underToCostructuredArrow`: `Φ` is a final functor, when
  `W` has a left calculus of fractions.
* `CategoryTheory.Functor.hasPointwiseRightDerivedFunctorAt_of_isRightDerivedValueAt`: if `W`
  has a left calculus of fractions and some cocone is a Deligne value of `RF` at `X`, then `F` has
  a pointwise right derived functor at `X`.
* `CategoryTheory.Functor.hasPointwiseRightDerivedFunctor_of_isRightDerivable`: a functor that is
  right derivable relative to `W` with a left calculus of fractions has a pointwise right derived
  functor.

## Hypotheses used, and why

The only hypothesis beyond the data `F`, `W`, `X` and the value cocone is
`[W.HasLeftCalculusOfFractions]`, and it is used exactly twice, both times to prove that the
comparison functor `Φ` is final, i.e. that `StructuredArrow d Φ` is connected for every
`d = (Y, g : L(Y) ⟶ L(X))`:

* *nonemptiness* needs every morphism `g : L(Y) ⟶ L(X)` of the localization to be a left fraction
  `L(f) ∘ L(s)⁻¹` with `s : X ⟶ X'` in `W` (`CategoryTheory.Localization.exists_leftFraction`);
  without a calculus of fractions the morphisms of `W⁻¹𝒞` are arbitrary zigzags and such a
  factorization need not exist, so `StructuredArrow d Φ` can be empty and `Φ` is then not final;
* *connectedness* needs two left fractions with the same image in the localization to admit a
  common amplification (`CategoryTheory.MorphismProperty.LeftFraction.map_eq_iff`, whose
  conclusion `LeftFractionRel` supplies exactly the object of `X/W` dominating the two given
  ones, hence the zigzag).

Nothing else is assumed: `F` is an arbitrary functor, no exactness, no triangulated structure, no
saturation of `W` — in particular none of Stacks 05S8's standing hypotheses beyond the left
calculus of fractions, which 05S8 does supply, a multiplicative system having one. The
localization functor is arbitrary: finality of `Φ` is proved for every `L` with
`[L.IsLocalization W]`, and `Functor.hasPointwiseRightDerivedFunctorAt_iff` transfers the
conclusion from `W.Q` to any such `L`.

The converse implication is *not* proved here, and is false in general: a pointwise left Kan
extension at `L(X)` is a colimit of a larger diagram, and it does not make the value a retract of
some `F(X')`, which is the extra content of essential constancy.

## Implementation notes

The identification of the two diagrams is on the nose:
`Φ ⋙ CostructuredArrow.proj L (L.obj X) ⋙ F` and `X/W ⟶ ℋ`, `(s : X ⟶ X') ↦ F(X')` agree on
objects and on morphisms by `rfl`, so
`CategoryTheory.Functor.underToCostructuredArrowCompProjCompIso` has identity components; it is
stated as an isomorphism rather than an equality only to feed
`CategoryTheory.Limits.hasColimit_of_iso`.

The structure morphism `s.hom` of an object of `X/W` has type
`(Functor.fromPUnit X).obj s.left ⟶ (𝟭 𝒞).obj s.right`, which is only unfoldably equal to
`X ⟶ s.right`; the auxiliary definition `CategoryTheory.MorphismProperty.underIso` pins the clean
type once and for all, and `CategoryTheory.MorphismProperty.exists_eq_structuredArrowMk`
presents an arbitrary object of `StructuredArrow d Φ` through data of the clean types, so that
the connectedness argument never has to rewrite under such a coercion.

Inside `namespace CategoryTheory.MorphismProperty` the name `CostructuredArrow` refers to
`MorphismProperty.CostructuredArrow`, so Mathlib's comma category is spelled
`CategoryTheory.CostructuredArrow` throughout that section, as elsewhere in this library.

## References

* [Stacks, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9) (Deligne's condition)
* [Stacks, Tag 05Q0](https://stacks.math.columbia.edu/tag/05Q0) (the index category `X/W`)
* [Stacks, Tag 04E6](https://stacks.math.columbia.edu/tag/04E6) (cofinal, i.e. final, functors)
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace MorphismProperty

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W] (X : C)

/-- The isomorphism `L(X) ≅ L(X')` attached to an object `(s : X ⟶ X')` of the index category
`X/W` of Stacks 05S9, available because a localization functor inverts `W`.

This is `CategoryTheory.Localization.isoOfHom` at `s.hom`, with source `L.obj X`. -/
noncomputable def underIso (s : W.Under ⊤ X) : L.obj X ≅ L.obj s.right :=
  Localization.isoOfHom L W s.hom s.prop

/-- The forward map of `W.underIso L X s` is `L.map s.hom`. -/
@[simp]
lemma underIso_hom (s : W.Under ⊤ X) : (W.underIso L X s).hom = L.map s.hom :=
  rfl

/-- The comparison functor `Φ : X/W ⥤ CostructuredArrow L (L.obj X)` between Deligne's index
category of Stacks 05S9 and the index category of the pointwise left Kan extension of a functor
along a localization functor `L` for `W` at `L(X)`.

An object `(s : X ⟶ X')` of `X/W` is sent to `X'` equipped with the arrow
`L(s)⁻¹ : L(X') ⟶ L(X)`, which exists because `L` inverts `W`, and a morphism `u` of `X/W` is
sent to the underlying morphism `u.right` of `𝒞`; the commutation condition in the comma
category is `L(u.right) ≫ L(t)⁻¹ = L(s)⁻¹`, which follows from `s ≫ u.right = t`. -/
noncomputable def underToCostructuredArrow :
    W.Under ⊤ X ⥤ CategoryTheory.CostructuredArrow L (L.obj X) where
  obj s := CategoryTheory.CostructuredArrow.mk (W.underIso L X s).inv
  map {s t} u := CategoryTheory.CostructuredArrow.homMk u.right (by
    have hw : (s.hom ≫ u.right : X ⟶ t.right) = t.hom := MorphismProperty.Under.w u
    have hL : (W.underIso L X s).hom ≫ L.map u.right = (W.underIso L X t).hom := by
      simp only [underIso_hom, ← Functor.map_comp, hw]
    change L.map u.right ≫ (W.underIso L X t).inv = (W.underIso L X s).inv
    rw [Iso.comp_inv_eq, Iso.eq_inv_comp]
    exact hL)
  map_id s := by ext; simp
  map_comp u v := by ext; simp

/-- The underlying object of the image of `s` under `W.underToCostructuredArrow L X` is
`s.right`. -/
@[simp]
lemma underToCostructuredArrow_obj_left (s : W.Under ⊤ X) :
    ((W.underToCostructuredArrow L X).obj s).left = s.right :=
  rfl

/-- The underlying morphism of the image of `u` under `W.underToCostructuredArrow L X` is
`u.right`. -/
@[simp]
lemma underToCostructuredArrow_map_left {s t : W.Under ⊤ X} (u : s ⟶ t) :
    ((W.underToCostructuredArrow L X).map u).left = u.right :=
  rfl

/-- The image in the localization of the left fraction `f s⁻¹`, computed by its defining
property: it is `g` as soon as `L(f) = g ≫ L(s)`. -/
lemma leftFraction_map_eq {Y A : C} (g : L.obj Y ⟶ L.obj X) (f : Y ⟶ A) (s : X ⟶ A) (hs : W s)
    (w : L.map f = g ≫ L.map s) :
    (LeftFraction.mk f s hs).map L (Localization.inverts L W) = g := by
  have := Localization.inverts L W s hs
  rw [← cancel_mono (L.map s), LeftFraction.map_comp_map_s]
  exact w

/-- An object of `StructuredArrow d Φ`, for `d` an object of `CostructuredArrow L (L.obj X)`,
out of a left fraction: an arrow `s : X ⟶ A` in `W`, an arrow `f : d.left ⟶ A` and the identity
`L(f) = d.hom ≫ L(s)`, which says that `d.hom` is the fraction `f s⁻¹`. -/
noncomputable def structuredArrowMk (d : CategoryTheory.CostructuredArrow L (L.obj X)) {A : C}
    (f : d.left ⟶ A) (s : X ⟶ A) (hs : W s) (w : L.map f = d.hom ≫ L.map s) :
    StructuredArrow d (W.underToCostructuredArrow L X) :=
  StructuredArrow.mk (Y := MorphismProperty.Under.mk ⊤ s hs)
    (CategoryTheory.CostructuredArrow.homMk f
      ((Iso.comp_inv_eq (W.underIso L X (MorphismProperty.Under.mk ⊤ s hs))).2 w))

/-- Every object of `StructuredArrow d Φ` is of the form
`CategoryTheory.MorphismProperty.structuredArrowMk`: it is a factorization of `d.hom` as a left
fraction. -/
lemma exists_eq_structuredArrowMk (d : CategoryTheory.CostructuredArrow L (L.obj X))
    (A : StructuredArrow d (W.underToCostructuredArrow L X)) :
    ∃ (A' : C) (f : d.left ⟶ A') (s : X ⟶ A') (hs : W s) (w : L.map f = d.hom ≫ L.map s),
      A = W.structuredArrowMk L X d f s hs w :=
  ⟨A.right.right, A.hom.left, A.right.hom, A.right.prop,
    (Iso.comp_inv_eq (W.underIso L X A.right)).1 (CategoryTheory.CostructuredArrow.w A.hom), rfl⟩

/-- **The comparison functor is final.** For `W` with a left calculus of fractions, the functor
`Φ : X/W ⥤ CostructuredArrow L (L.obj X)` of
`CategoryTheory.MorphismProperty.underToCostructuredArrow` is final.

Fix `d = (Y, g : L(Y) ⟶ L(X))`. The category `StructuredArrow d Φ` is the category of
factorizations of `g` as a left fraction: an object is an arrow `s : X ⟶ X'` of `W` together with
`f : Y ⟶ X'` satisfying `L(f) = g ≫ L(s)`. It is nonempty because `g` is a left fraction
(`CategoryTheory.Localization.exists_leftFraction`), and connected because two left fractions
with the same image in the localization are related by `LeftFractionRel`
(`CategoryTheory.MorphismProperty.LeftFraction.map_eq_iff`), whose witnessing object receives
morphisms from both, giving a zigzag of length two. -/
theorem final_underToCostructuredArrow [W.HasLeftCalculusOfFractions] :
    (W.underToCostructuredArrow L X).Final where
  out d := by
    have hne : Nonempty (StructuredArrow d (W.underToCostructuredArrow L X)) := by
      obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L W d.hom
      refine ⟨W.structuredArrowMk L X d φ.f φ.s φ.hs ?_⟩
      rw [hφ, LeftFraction.map_comp_map_s]
    have hzz : ∀ A B : StructuredArrow d (W.underToCostructuredArrow L X), Zigzag A B := by
      intro A B
      obtain ⟨A', fA, sA, hsA, wA, rfl⟩ := W.exists_eq_structuredArrowMk L X d A
      obtain ⟨B', fB, sB, hsB, wB, rfl⟩ := W.exists_eq_structuredArrowMk L X d B
      have key : (LeftFraction.mk fA sA hsA).map L (Localization.inverts L W)
          = (LeftFraction.mk fB sB hsB).map L (Localization.inverts L W) := by
        rw [W.leftFraction_map_eq L X _ _ _ _ wA, W.leftFraction_map_eq L X _ _ _ _ wB]
      obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := (LeftFraction.map_eq_iff L W _ _).1 key
      have wT : L.map (fA ≫ t₁) = d.hom ≫ L.map (sA ≫ t₁) := by
        simp only [Functor.map_comp, wA, Category.assoc]
      exact Zigzag.of_hom_inv
        (StructuredArrow.homMk (f' := W.structuredArrowMk L X d (fA ≫ t₁) (sA ≫ t₁) ht wT)
          (MorphismProperty.Under.homMk t₁ rfl)
          (CategoryTheory.CostructuredArrow.hom_ext _ _ rfl))
        (StructuredArrow.homMk (f' := W.structuredArrowMk L X d (fA ≫ t₁) (sA ≫ t₁) ht wT)
          (MorphismProperty.Under.homMk t₂ hst.symm)
          (CategoryTheory.CostructuredArrow.hom_ext _ _ hft.symm))
    exact @zigzag_isConnected _ _ hne hzz

end MorphismProperty

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

/-- Deligne's ind-object `X/W ⟶ ℋ`, `(s : X ⟶ X') ↦ F(X')` of Stacks 05S9 is the comparison
functor `CategoryTheory.MorphismProperty.underToCostructuredArrow` followed by the diagram whose
colimit is the pointwise left Kan extension of `F` along `L` at `L(X)`. The two functors agree on
objects and on morphisms, so the isomorphism has identity components. -/
noncomputable def underToCostructuredArrowCompProjCompIso (F : C ⥤ H) (W : MorphismProperty C)
    (L : C ⥤ D) [L.IsLocalization W] (X : C) :
    W.underToCostructuredArrow L X ⋙ CostructuredArrow.proj L (L.obj X) ⋙ F ≅
      MorphismProperty.Under.forget W ⊤ X ⋙ CategoryTheory.Under.forget X ⋙ F :=
  NatIso.ofComponents (fun s => Iso.refl (F.obj s.right)) (fun u => by simp)

/-- If `W` has a left calculus of fractions and some cocone on the ind-object
`X/W ⟶ ℋ`, `(s : X ⟶ X') ↦ F(X')` is a value of the right derived functor of `F` at `X` in
Deligne's sense (Stacks 05S9, `CategoryTheory.Functor.IsRightDerivedValueAt`), then `F` has a
pointwise right derived functor at `X` in Mathlib's sense, i.e. `F` has a pointwise left Kan
extension along any localization functor for `W` at the image of `X`.

A Deligne value is a colimit cocone (`IsRightDerivedValueAt.isColimit`), so the ind-object has a
colimit; the ind-object is the comparison functor `Φ` followed by the Kan-extension diagram, and
`Φ` is final (`MorphismProperty.final_underToCostructuredArrow`, which is where the calculus of
fractions is used), so the Kan-extension diagram has a colimit too. -/
theorem hasPointwiseRightDerivedFunctorAt_of_isRightDerivedValueAt (F : C ⥤ H)
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X : C)
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ CategoryTheory.Under.forget X ⋙ F)}
    (hc : F.IsRightDerivedValueAt W X c) :
    F.HasPointwiseRightDerivedFunctorAt W X := by
  have : HasColimit
      (MorphismProperty.Under.forget W ⊤ X ⋙ CategoryTheory.Under.forget X ⋙ F) :=
    HasColimit.mk ⟨c, hc.isColimit⟩
  have : (W.underToCostructuredArrow W.Q X).Final :=
    W.final_underToCostructuredArrow W.Q X
  have : HasColimit (W.underToCostructuredArrow W.Q X ⋙
      CostructuredArrow.proj W.Q (W.Q.obj X) ⋙ F) :=
    hasColimit_of_iso (F.underToCostructuredArrowCompProjCompIso W W.Q X)
  rw [F.hasPointwiseRightDerivedFunctorAt_iff W.Q W X]
  exact Final.hasColimit_of_comp (W.underToCostructuredArrow W.Q X)

/-- A functor that is right derivable relative to a class of
morphisms with a left calculus of fractions has a pointwise right derived functor. -/
theorem hasPointwiseRightDerivedFunctor_of_isRightDerivable (F : C ⥤ H)
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (hF : F.IsRightDerivable W) :
    F.HasPointwiseRightDerivedFunctor W := fun X =>
  (hF X).elim fun _ hc =>
    F.hasPointwiseRightDerivedFunctorAt_of_isRightDerivedValueAt W X hc

end Functor

end CategoryTheory

end
