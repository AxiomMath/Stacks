module

public import StacksFrontier.CategoryTheory.Localization.LeftFraction.HomAsColimit
public import Mathlib.CategoryTheory.Shift.Localization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms of `S⁻¹𝒞` into a shifted object as a colimit over `X/S`

Let `W` be a left multiplicative system on a category `C` and let `L : C ⥤ D` be a localization
functor of `C` at `W`. Stacks 05Q0 computes the morphisms `L.obj K ⟶ L.obj Y` of `W⁻¹C` as the
colimit of the sets `Mor_C(K, Y')` over the category `Y/S` of the morphisms `s : Y ⟶ Y'` of `W`
out of `Y`; this is `MorphismProperty.isColimitUnderHomCocone` of
`StacksFrontier/CategoryTheory/Localization/LeftFraction/HomAsColimit.lean`. This file records the
form of that computation which is needed when the second variable is a shift `X⟦n⟧` and the
morphisms of the localization are not assumed to live in the universe of the morphisms of `C`.

Two changes are made. The first is a matter of universes: `isColimitUnderHomCocone` takes the
diagram `underHomDiagram W K Y` with values in `Type v`, the universe of the morphisms of `C`,
and therefore forces the localization to satisfy `Category.{v} D`. Here the diagram is composed
with `uliftFunctor` so that it takes values in `Type (max v v₂)`, which is also the universe of
the set of morphisms `L.obj K ⟶ L.obj Y` once it has been lifted, and `D` is an arbitrary
category with morphisms in `Type v₂`. The second is a reindexing: for a `W` compatible with a
shift by `M` in the sense of `MorphismProperty.IsCompatibleWithShift`, shifting by `n : M` is an
equivalence `X/S ≌ X⟦n⟧/S` of index categories, so that the colimit over `X⟦n⟧/S` computing the
morphisms `L.obj K ⟶ L.obj (X⟦n⟧)` may be rewritten as a colimit over `X/S`. When moreover `L`
commutes with the shift, postcomposing with the comparison isomorphism
`L.obj (X⟦n⟧) ≅ (L.obj X)⟦n⟧` identifies that colimit with the set of morphisms
`L.obj K ⟶ (L.obj X)⟦n⟧`, and the leg of the colimit cocone at an object `s : X ⟶ Y` of `X/S`
becomes the map sending `f : K ⟶ Y⟦n⟧` to the left fraction `L(s)⟦n⟧⁻¹ ∘ L(f)`, which is the
displayed formula of Stacks 05Q1 for the shifted hom-set.

## Main definitions

`MorphismProperty.underHomCoconeULift` is the universe-general form of the tautological cocone of
Stacks 05Q0, on the diagram `underHomDiagram W K Y ⋙ uliftFunctor` and with vertex the lift of
`L.obj K ⟶ L.obj Y`. `MorphismProperty.underShiftFunctor` is the functor `X/S ⥤ X⟦n⟧/S` given by
shifting both the object `Y` and the structural morphism `s : X ⟶ Y` by `n`, and
`MorphismProperty.underShiftEquivalence` is the equivalence of categories it induces.
`MorphismProperty.shiftedUnderHomCocone` is the resulting cocone over `X/S` with vertex the lift
of `L.obj K ⟶ L.obj (X⟦n⟧)`, and `MorphismProperty.shiftedUnderHomCoconeCommShift` is its
transport, along postcomposition with `(L.commShiftIso n).hom.app X`, to the vertex given by the
lift of `L.obj K ⟶ (L.obj X)⟦n⟧`. That postcomposition is `Functor.commShiftVertexIso`.

## Main results

`MorphismProperty.isColimitUnderHomCoconeULift` is the colimit statement of Stacks 05Q0 in the
universe-general form, and `MorphismProperty.isColimitShiftedUnderHomCocone` and
`MorphismProperty.isColimitShiftedUnderHomCoconeCommShift` are its two reindexed forms. The legs
of all three cocones are pinned down by the simp lemmas `underHomCoconeULift_ι_app_apply`,
`shiftedUnderHomCocone_ι_app_apply` and `shiftedUnderHomCoconeCommShift_ι_app_apply`; the last of
these says that the leg at an object `s : X ⟶ Y` of `X/S` sends `f : K ⟶ Y⟦n⟧` to
`L(f) ≫ (L.commShiftIso n).hom.app Y ≫ inv (L(s)⟦n⟧)`, the morphism of `W⁻¹C` that Stacks writes
`L(s)⟦n⟧⁻¹ ∘ L(f)`. The computation behind it is
`Functor.inv_map_shift_comp_commShiftIso_hom`, which inverts the naturality square of
`L.commShiftIso n` at a morphism that `L` inverts.

## Implementation notes

The proof of `isColimitUnderHomCoconeULift` mirrors, rather than reuses, the proof of
`isColimitUnderHomCocone`: the latter is stated for a localization with `Category.{v} D`, so it
cannot be instantiated when the morphisms of `D` live in a different universe, and the two
auxiliary lemmas of its proof are private. They are therefore proved again here, under the names
`map_leftFraction_comp_right` and `coconeULift_app_eq_of_rel`. All the ingredients of the argument
are universe-polymorphic, so the mirrored proof is the same one: the legs are jointly surjective
because every morphism of `W⁻¹C` is a left fraction, and they identify exactly the left fractions
related by `MorphismProperty.LeftFractionRel`.

The equivalence `underShiftEquivalence` is obtained from `Functor.asEquivalence`, by checking that
`underShiftFunctor` is full, faithful and essentially surjective. All three rest on the shift by
`n` being an equivalence of `C`, which is assumed as the instance
`(CategoryTheory.shiftFunctor C n).IsEquivalence`; it holds automatically when the shift is
indexed by a group, in particular for the shift by `ℤ` of a category of complexes or of a homotopy
category. Compatibility of `W` with the shift is what makes the shifted structural morphism again
belong to `W`, and `W.RespectsIso` is used for essential surjectivity, where the structural
morphism of a given object of `X⟦n⟧/S` must be transported along an isomorphism.

The morphisms `inv (L.map A.hom)` and `inv (L.map (A.hom⟦n⟧'))` occur in the statements, not only
in the proofs, so the instances `isIso_map_under_hom` and `isIso_map_shift_under_hom` are declared:
they record that `L` inverts the structural morphism of an object of `Y/S`, and its shift.

## References

* [Stacks, Tag 05Q0](https://stacks.math.columbia.edu/tag/05Q0), whose displayed formula is
  [Stacks, Tag 05Q1].
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe w v v₂ u u₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D] (L : C ⥤ D)
  {M : Type w} [AddMonoid M] [HasShift C M] [HasShift D M] [L.CommShift M]

/-- The naturality square of `L.commShiftIso n` at a morphism `s : X ⟶ Y`, inverted: if both
`L.map (s⟦n⟧)` and `(L.map s)⟦n⟧` are isomorphisms, then going down the right-hand side of the
square backwards and then across is the same as going across and then up the left-hand side
backwards. -/
lemma Functor.inv_map_shift_comp_commShiftIso_hom {X Y : C} (s : X ⟶ Y) (n : M)
    [IsIso (L.map (s⟦n⟧'))] [IsIso ((L.map s)⟦n⟧')] :
    CategoryTheory.inv (L.map (s⟦n⟧')) ≫ (L.commShiftIso n).hom.app X =
      (L.commShiftIso n).hom.app Y ≫ CategoryTheory.inv ((L.map s)⟦n⟧') := by
  rw [← cancel_epi (L.map (s⟦n⟧')), IsIso.hom_inv_id_assoc, ← Category.assoc,
    L.commShiftIso_hom_naturality s n, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Postcomposition with the comparison isomorphism `L.obj (X⟦n⟧) ≅ (L.obj X)⟦n⟧`, as an
isomorphism between the set of morphisms `L.obj K ⟶ L.obj (X⟦n⟧)` and the set of morphisms
`L.obj K ⟶ (L.obj X)⟦n⟧`, both lifted to `Type (max v v₂)`. -/
noncomputable def Functor.commShiftVertexIso (K X : C) (n : M) :
    ULift.{v} (L.obj K ⟶ L.obj (X⟦n⟧)) ≅ ULift.{v} (L.obj K ⟶ (L.obj X)⟦n⟧) where
  hom := ↾fun g => ULift.up (g.down ≫ (L.commShiftIso n).hom.app X)
  inv := ↾fun g => ULift.up (g.down ≫ (L.commShiftIso n).inv.app X)
  hom_inv_id := by
    ext g
    simp
  inv_hom_id := by
    ext g
    simp

end CategoryTheory

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

section Localization

variable [W.HasLeftCalculusOfFractions] {D : Type u₂} [Category.{v₂} D] (L : C ⥤ D)
  [L.IsLocalization W]

omit [W.HasLeftCalculusOfFractions] in
/-- A localization functor at `W` inverts the structural morphism of an object of `Y/S`, since
that morphism belongs to `W`. -/
instance isIso_map_under_hom {Y : C} (A : W.Under ⊤ Y) : IsIso (L.map A.hom) :=
  Localization.inverts L W _ A.prop

/-- Postcomposing the numerator of a left fraction with a morphism `α : s ⟶ t` of `Y/S` does not
change the morphism of `W⁻¹C` it defines: `t⁻¹ (α ∘ f) = s⁻¹ f`. -/
lemma map_leftFraction_comp_right {K Y : C} (A B : W.Under ⊤ Y) (α : A ⟶ B)
    (f : K ⟶ A.right) :
    (LeftFraction.mk (W := W) (X := K) (Y := Y) (f ≫ α.right) B.hom B.prop).map L
        (Localization.inverts L W) =
      (LeftFraction.mk (W := W) (X := K) (Y := Y) f A.hom A.prop).map L
        (Localization.inverts L W) :=
  (LeftFraction.map_eq_iff L W _ _).2
    ⟨B.right, 𝟙 B.right, α.right, by simp [MorphismProperty.Under.w α], by simp,
      by simpa using B.prop⟩

/-- The cocone on `underHomDiagram W K Y ⋙ uliftFunctor` with vertex the lift of
`Mor_{W⁻¹C}(K, Y)` whose leg at an object `s : Y ⟶ Y'` of `Y/S` sends `f : K ⟶ Y'` to the left
fraction `s⁻¹ f`. Unlike `underHomCocone`, this relates the universe of the morphisms of the
localization to the universe of the morphisms of `C` in no way. -/
noncomputable def underHomCoconeULift (K Y : C) :
    Cocone (W.underHomDiagram K Y ⋙ uliftFunctor.{v₂}) where
  pt := ULift.{v} (L.obj K ⟶ L.obj Y)
  ι :=
    { app := fun A => ↾fun f => ULift.up
        ((LeftFraction.mk (W := W) (X := K) (Y := Y) f.down A.hom A.prop).map L
          (Localization.inverts L W))
      naturality := fun A B α => by
        ext f
        exact congrArg ULift.up (W.map_leftFraction_comp_right L A B α f.down) }

/-- The leg of `underHomCoconeULift` at `s : Y ⟶ Y'` sends `f : K ⟶ Y'` to `s⁻¹ f`. -/
@[simp]
lemma underHomCoconeULift_ι_app_apply (K Y : C) (A : W.Under ⊤ Y)
    (f : ULift.{v₂} (K ⟶ A.right)) :
    (W.underHomCoconeULift L K Y).ι.app A f =
      ULift.up ((LeftFraction.mk (W := W) (X := K) (Y := Y) f.down A.hom A.prop).map L
        (Localization.inverts L W)) :=
  rfl

omit [W.HasLeftCalculusOfFractions] in
/-- The legs of any cocone on `underHomDiagram W K Y ⋙ uliftFunctor` identify two left fractions
that are `LeftFractionRel`-related: the relation provides a third object of `Y/S` receiving the
two given ones, and the two cocone relations at it are compared using that the relation also
equalizes the numerators. -/
lemma coconeULift_app_eq_of_rel {K Y : C}
    (c : Cocone (W.underHomDiagram K Y ⋙ uliftFunctor.{v₂}))
    (A B : W.Under ⊤ Y) (f : K ⟶ A.right) (g : K ⟶ B.right)
    (h : LeftFractionRel (LeftFraction.mk (W := W) (X := K) (Y := Y) f A.hom A.prop)
      (LeftFraction.mk (W := W) (X := K) (Y := Y) g B.hom B.prop)) :
    c.ι.app A (ULift.up f) = c.ι.app B (ULift.up g) := by
  obtain ⟨Z, t₁, t₂, hs, hf, hW⟩ := h
  have h₁ := types_congr_hom
    (c.w (Under.homMk (A := A) (B := Under.mk ⊤ (A.hom ≫ t₁) hW) t₁ rfl)) (ULift.up f)
  have h₂ := types_congr_hom
    (c.w (Under.homMk (A := B) (B := Under.mk ⊤ (A.hom ≫ t₁) hW) t₂ hs.symm)) (ULift.up g)
  rw [← h₁, ← h₂]
  exact congrArg _ (congrArg ULift.up hf)

/-- **Stacks 05Q0**, the displayed formula [Stacks, Tag 05Q1], with no constraint relating the
universe of the morphisms of the localization to that of the morphisms of `C`: for a left
multiplicative system `W` on `C`, a localization functor `L : C ⥤ D` of `C` at `W` and objects
`K`, `Y` of `C`, the lift of the set of morphisms `L.obj K ⟶ L.obj Y` of `W⁻¹C` is the colimit
`colim_{(s : Y ⟶ Y') ∈ Y/S} Mor_C(K, Y')` of the lifted sets, at the tautological cocone
`underHomCoconeULift`. -/
@[sga "4 VI 6.5"]
noncomputable def isColimitUnderHomCoconeULift (K Y : C) :
    IsColimit (W.underHomCoconeULift L K Y) where
  desc c := ↾fun g =>
    c.ι.app (Under.mk ⊤ (Localization.exists_leftFraction L W g.down).choose.s
      (Localization.exists_leftFraction L W g.down).choose.hs)
      (ULift.up (Localization.exists_leftFraction L W g.down).choose.f)
  fac c A := by
    ext f
    refine W.coconeULift_app_eq_of_rel c _ A _ f.down ((LeftFraction.map_eq_iff L W _ _).1 ?_)
    exact ((Localization.exists_leftFraction L W _).choose_spec).symm
  uniq c m hm := by
    ext g
    refine (congrArg m (congrArg ULift.up
      (Localization.exists_leftFraction L W g.down).choose_spec)).trans ?_
    exact types_congr_hom
      (hm (Under.mk ⊤ (Localization.exists_leftFraction L W g.down).choose.s
        (Localization.exists_leftFraction L W g.down).choose.hs))
      (ULift.up (Localization.exists_leftFraction L W g.down).choose.f)

end Localization

section Shift

variable {M : Type w} [AddMonoid M] [HasShift C M] [W.IsCompatibleWithShift M] (X : C) (n : M)

/-- Shifting by `n` as a functor `X/S ⥤ X⟦n⟧/S`: it sends an object `s : X ⟶ Y` of `X/S` to the
morphism `s⟦n⟧ : X⟦n⟧ ⟶ Y⟦n⟧`, which again belongs to `W` because `W` is compatible with the
shift, and a morphism `a : Y ⟶ Y'` of `X/S` to `a⟦n⟧`. -/
def underShiftFunctor : W.Under ⊤ X ⥤ W.Under ⊤ (X⟦n⟧) where
  obj A := Under.mk ⊤ (A.hom⟦n⟧') (W.shift A.prop n)
  map {A B} α := Under.homMk (α.right⟦n⟧') (by
    change (CategoryTheory.shiftFunctor C n).map A.hom ≫
        (CategoryTheory.shiftFunctor C n).map α.right =
      (CategoryTheory.shiftFunctor C n).map B.hom
    rw [← Functor.map_comp, MorphismProperty.Under.w α])
  map_id A := MorphismProperty.Under.Hom.ext ((CategoryTheory.shiftFunctor C n).map_id A.right)
  map_comp α β := MorphismProperty.Under.Hom.ext
    ((CategoryTheory.shiftFunctor C n).map_comp α.right β.right)

/-- The object of `X⟦n⟧/S` underlying the image of an object `s : X ⟶ Y` of `X/S` under
`underShiftFunctor` is `Y⟦n⟧`. -/
@[simp]
lemma underShiftFunctor_obj_right (A : W.Under ⊤ X) :
    ((W.underShiftFunctor X n).obj A).right = A.right⟦n⟧ :=
  rfl

/-- The structural morphism of the image of an object `s : X ⟶ Y` of `X/S` under
`underShiftFunctor` is `s⟦n⟧`. -/
@[simp]
lemma underShiftFunctor_obj_hom (A : W.Under ⊤ X) :
    ((W.underShiftFunctor X n).obj A).hom = A.hom⟦n⟧' :=
  rfl

section

variable [(CategoryTheory.shiftFunctor C n).IsEquivalence]

/-- When shifting by `n` is an equivalence of `C`, `underShiftFunctor` is faithful. -/
instance : (W.underShiftFunctor X n).Faithful where
  map_injective {A B} _ _ h := MorphismProperty.Under.Hom.ext
    ((CategoryTheory.shiftFunctor C n).map_injective
      (congrArg (fun γ : (W.underShiftFunctor X n).obj A ⟶ (W.underShiftFunctor X n).obj B =>
        γ.right) h))

/-- When shifting by `n` is an equivalence of `C`, `underShiftFunctor` is full. -/
instance : (W.underShiftFunctor X n).Full where
  map_surjective {A B} g := by
    obtain ⟨b, hb⟩ := (CategoryTheory.shiftFunctor C n).map_surjective
      (show A.right⟦n⟧ ⟶ B.right⟦n⟧ from g.right)
    refine ⟨Under.homMk b ?_, MorphismProperty.Under.Hom.ext hb⟩
    apply (CategoryTheory.shiftFunctor C n).map_injective
    rw [Functor.map_comp, hb]
    exact MorphismProperty.Under.w g

variable [W.RespectsIso]

/-- When shifting by `n` is an equivalence of `C` and `W` respects isomorphisms,
`underShiftFunctor` is essentially surjective. -/
instance : (W.underShiftFunctor X n).EssSurj where
  mem_essImage A := by
    obtain ⟨b, hb⟩ := (CategoryTheory.shiftFunctor C n).map_surjective
      (A.hom ≫ ((CategoryTheory.shiftFunctor C n).objObjPreimageIso A.right).inv)
    have hbW : W b := by
      rw [← MorphismProperty.IsCompatibleWithShift.iff W b n, hb]
      exact (W.cancel_right_of_respectsIso _ _).2 A.prop
    refine ⟨Under.mk ⊤ b hbW, ⟨Under.isoMk
      ((CategoryTheory.shiftFunctor C n).objObjPreimageIso A.right) ?_⟩⟩
    change (CategoryTheory.shiftFunctor C n).map b ≫ _ = A.hom
    rw [hb, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- When shifting by `n` is an equivalence of `C` and `W` respects isomorphisms,
`underShiftFunctor` is an equivalence. -/
instance : (W.underShiftFunctor X n).IsEquivalence where

/-- Shifting by `n` as an equivalence `X/S ≌ X⟦n⟧/S`. It is an equivalence because shifting by `n`
is an equivalence of `C` and `W` is compatible with the shift, so that a morphism of `C` out of
`X` belongs to `W` exactly when its shift by `n` does; `W` is also assumed to respect
isomorphisms. -/
noncomputable def underShiftEquivalence : W.Under ⊤ X ≌ W.Under ⊤ (X⟦n⟧) :=
  (W.underShiftFunctor X n).asEquivalence

/-- The functor underlying `underShiftEquivalence` is `underShiftFunctor`. -/
@[simp]
lemma underShiftEquivalence_functor :
    (W.underShiftEquivalence X n).functor = W.underShiftFunctor X n :=
  rfl

end

end Shift

section Combination

variable [W.HasLeftCalculusOfFractions] {D : Type u₂} [Category.{v₂} D] (L : C ⥤ D)
  [L.IsLocalization W] {M : Type w} [AddMonoid M] [HasShift C M] [W.IsCompatibleWithShift M]
  (K X : C) (n : M)

omit [W.HasLeftCalculusOfFractions] in
/-- A localization functor at `W` inverts the shift by `n` of the structural morphism of an object
of `X/S`, since `W` is compatible with the shift. -/
instance isIso_map_shift_under_hom (A : W.Under ⊤ X) : IsIso (L.map (A.hom⟦n⟧')) :=
  Localization.inverts L W _ (W.shift A.prop n)

variable [W.RespectsIso] [(CategoryTheory.shiftFunctor C n).IsEquivalence]

/-- The cocone over `X/S` computing the morphisms `L.obj K ⟶ L.obj (X⟦n⟧)` of `W⁻¹C`: it is the
cocone `underHomCoconeULift W L K (X⟦n⟧)` reindexed along the equivalence
`underShiftEquivalence W X n`, so its diagram sends an object `s : X ⟶ Y` of `X/S` to the lift of
`Mor_C(K, Y⟦n⟧)` and its leg there sends `f : K ⟶ Y⟦n⟧` to the left fraction `(s⟦n⟧)⁻¹ f`. -/
noncomputable def shiftedUnderHomCocone :
    Cocone (Under.forget W ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
      CategoryTheory.shiftFunctor C n ⋙ coyoneda.obj (Opposite.op K) ⋙ uliftFunctor.{v₂}) :=
  (W.underHomCoconeULift L K (X⟦n⟧)).whisker (W.underShiftEquivalence X n).functor

/-- The leg of `shiftedUnderHomCocone` at an object `s : X ⟶ Y` of `X/S` sends `f : K ⟶ Y⟦n⟧` to
the left fraction `(s⟦n⟧)⁻¹ f`. -/
@[simp]
lemma shiftedUnderHomCocone_ι_app_apply (A : W.Under ⊤ X) (f : ULift.{v₂} (K ⟶ A.right⟦n⟧)) :
    (W.shiftedUnderHomCocone L K X n).ι.app A f =
      ULift.up ((LeftFraction.mk (W := W) (X := K) (Y := X⟦n⟧) f.down (A.hom⟦n⟧')
        (W.shift A.prop n)).map L (Localization.inverts L W)) :=
  rfl

/-- The reindexed form of **Stacks 05Q0**: the lift of the set of morphisms
`L.obj K ⟶ L.obj (X⟦n⟧)` of `W⁻¹C` is the colimit of the lifted sets `Mor_C(K, Y⟦n⟧)` over the
objects `(s : X ⟶ Y)` of `X/S`, at the cocone `shiftedUnderHomCocone` whose leg at `s` sends `f`
to the left fraction `(s⟦n⟧)⁻¹ f`. -/
noncomputable def isColimitShiftedUnderHomCocone :
    IsColimit (W.shiftedUnderHomCocone L K X n) :=
  (W.isColimitUnderHomCoconeULift L K (X⟦n⟧)).whiskerEquivalence
    (W.underShiftEquivalence X n)

variable [HasShift D M] [L.CommShift M]

/-- The cocone over `X/S` computing the morphisms `L.obj K ⟶ (L.obj X)⟦n⟧` of `W⁻¹C`: it is
`shiftedUnderHomCocone` with its vertex transported along postcomposition with
`(L.commShiftIso n).hom.app X`. -/
noncomputable def shiftedUnderHomCoconeCommShift :
    Cocone (Under.forget W ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
      CategoryTheory.shiftFunctor C n ⋙ coyoneda.obj (Opposite.op K) ⋙ uliftFunctor.{v₂}) :=
  (W.shiftedUnderHomCocone L K X n).extend (Functor.commShiftVertexIso L K X n).hom

/-- The vertex of `shiftedUnderHomCoconeCommShift` is the lift of `L.obj K ⟶ (L.obj X)⟦n⟧`. -/
lemma shiftedUnderHomCoconeCommShift_pt :
    (W.shiftedUnderHomCoconeCommShift L K X n).pt = ULift.{v} (L.obj K ⟶ (L.obj X)⟦n⟧) :=
  rfl

/-- The leg of `shiftedUnderHomCoconeCommShift` at an object `s : X ⟶ Y` of `X/S` sends
`f : K ⟶ Y⟦n⟧` to `L(f) ≫ (L.commShiftIso n).hom.app Y ≫ inv (L(s)⟦n⟧)`, the morphism
`L.obj K ⟶ (L.obj X)⟦n⟧` that Stacks 05Q1 writes as the left fraction `L(s)⟦n⟧⁻¹ ∘ L(f)`. -/
@[simp]
lemma shiftedUnderHomCoconeCommShift_ι_app_apply (A : W.Under ⊤ X)
    (f : ULift.{v₂} (K ⟶ A.right⟦n⟧)) :
    (W.shiftedUnderHomCoconeCommShift L K X n).ι.app A f =
      ULift.up (L.map f.down ≫ (L.commShiftIso n).hom.app A.right ≫
        inv ((L.map A.hom)⟦n⟧')) := by
  refine congrArg ULift.up ?_
  change (L.map f.down ≫ inv (L.map (A.hom⟦n⟧'))) ≫ (L.commShiftIso n).hom.app X = _
  rw [Category.assoc,
    L.inv_map_shift_comp_commShiftIso_hom (X := X) (Y := A.right) A.hom n]

/-- The reindexed form of **Stacks 05Q0** in its shifted shape: for a localization functor `L`
commuting with the shift, the lift of the set of morphisms `L.obj K ⟶ (L.obj X)⟦n⟧` of `W⁻¹C` is
the colimit of the lifted sets `Mor_C(K, Y⟦n⟧)` over the objects `(s : X ⟶ Y)` of `X/S`, at the
cocone whose leg at `s` sends `f` to the left fraction `L(s)⟦n⟧⁻¹ ∘ L(f)`. -/
noncomputable def isColimitShiftedUnderHomCoconeCommShift :
    IsColimit (W.shiftedUnderHomCoconeCommShift L K X n) :=
  IsColimit.ofIsoColimit (W.isColimitShiftedUnderHomCocone L K X n)
    (Cocone.ext (Functor.commShiftVertexIso L K X n) fun _ => rfl)

end Combination

end CategoryTheory.MorphismProperty

end
