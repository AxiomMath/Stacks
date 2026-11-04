module

public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection

/-!
# The total presheaf of a presheaf on a category of elements

Let `C` be a category, let `Z` be a presheaf of sets on `C` and let `F` be a presheaf of sets on
the category of elements `El Z` of `Z` (Stacks 02XV applied to `Z ⋙ typeToCat`). The *total
presheaf* `Σ_Z F` of `F` is the presheaf on `C` whose sections over `V` are the pairs
`(z ∈ Z(V), s ∈ F(V, z))`, with the obvious restriction maps, together with its structure
morphism `Σ_Z F ⟶ Z` reading off the first component. This file builds it and identifies its
category of elements with the category of elements of `F`, viewed over `C` through the projection
of `El Z`:

```text
El_{El Z} F ⟶ El Z ⟶ C     is     El_C (Σ_Z F) ⟶ C.
```

This is the general-base form of `CategoryTheory.PresheafOfCategories.relocalizeAsElements`'s
comparison: `CategoryTheory.OverShriek.presheaf` and
`CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver` do the same for `Z` a
*representable* presheaf, where `El Z` is the slice `C/A`. The general case is what turns a
statement about a presheaf on the category of elements of `Z` into a statement about a presheaf
over `Z` on `C` itself; in particular it is what makes a category over `El Z` representable by a
presheaf on `El Z` into a category over `C` representable by a presheaf over `Z`.

## Main definitions

* `CategoryTheory.PresheafOfCategories.elementsPoint`: the object `(V, z)` of `El Z` named by a
  section `z` of `Z` over `V`, and `CategoryTheory.PresheafOfCategories.elementsRestrict` the
  morphism of `El Z` restricting it along a morphism of `C`.
* `CategoryTheory.PresheafOfCategories.elementsTotalPresheaf`: the total presheaf `Σ_Z F`, with
  `CategoryTheory.PresheafOfCategories.elementsTotalProj` its structure morphism to `Z`.
* `CategoryTheory.PresheafOfCategories.elementsToTotal` and
  `CategoryTheory.PresheafOfCategories.totalToElements`: the two comparison functors of
  categories of elements.

## Main results

* `CategoryTheory.PresheafOfCategories.totalElementsEquivalenceOver`: the two are an equivalence
  in the 2-category of categories over `C`.
* `CategoryTheory.PresheafOfCategories.sectionOfObj_totalElementsEquivalenceOver`: the section of
  `Σ_Z F` that an object of the category of elements of `F` names through the equivalence is the
  explicit pair.

## Implementation notes

The sections of `Σ_Z F` over `V` are a `Sigma` type whose second component's *type* depends on
the first, so the two functoriality equations are equalities of dependent pairs.
`CategoryTheory.PresheafOfCategories.totalMk_eq` is the bookkeeping lemma that reduces such an
equality to an equality of the base morphisms of `C`: two morphisms of `El Z` with one and the
same target and one and the same base morphism restrict a section of `F` to the same pair,
because a morphism of a category of elements is determined by its base
(`CategoryTheory.PresheafOfCategories.elements_hom_ext`) and because the element of `Z` a
morphism of `El Z` starts at is determined by its base and its target. It is the exact analogue
of `CategoryTheory.OverShriek.sigmaMk_eq`, and `totalMk_eq_self` and `totalMk_eq_comp` are its
two specialisations that `map_id` and `map_comp` consume.

Both comparison functors are *isomorphisms of categories on objects*, which is why both the unit
and the counit are `CategoryTheory.Iso.refl`: an object of `El_{El Z} F` is a triple
`(V, z, s)` written as `((V, z), s)` and an object of `El_C (Σ_Z F)` is the same triple written
as `(V, (z, s))`, and structure eta for `CategoryTheory.Pseudofunctor.CoGrothendieck`,
`CategoryTheory.Discrete` and `Sigma` makes the two round trips the identity on objects. This is
the one place where the general base is *easier* than the representable base of
`CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver`: there a round trip
replaces the base `P.base` of an object by `Over.mk (P.fiber.as.1.1 ≫ a)`, which agrees with it
only propositionally, so the counit is an `elementsIsoOfBaseIso` and the backward functor is only
propositionally over the base. Here the base of `elementsPoint Z z` for `z ∈ Z(V)` is `V` on the
nose, so both `w` equations are `rfl`.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 03CD](https://stacks.math.columbia.edu/tag/03CD)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.PresheafOfCategories

universe v u

variable {C : Type u} [Category.{v} C] (Z : Cᵒᵖ ⥤ Type v)

/-- The object `(V, z)` of the category of elements of `Z` named by a section `z` of `Z` over
`V`. -/
abbrev elementsPoint {V : C} (z : Z.obj (op V)) :
    (presheafOfCategories (Z ⋙ typeToCat)).obj :=
  ⟨V, Discrete.mk z⟩

/-- The morphism of the category of elements of `Z` that restriction along `f` induces between
the object named by `Z(f)(z)` and the object named by `z`. -/
abbrev elementsRestrict {U V : Cᵒᵖ} (f : U ⟶ V) (z : Z.obj U) :
    elementsPoint Z (Z.map f z) ⟶ elementsPoint Z z :=
  ⟨f.unop, Discrete.eqToHom rfl⟩

variable (F : ((presheafOfCategories (Z ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type v)

/-! ### Bookkeeping for sections of the total presheaf

A section of `Σ_Z F` over `V` is a pair `(z, s)` with `z ∈ Z(V)` and `s ∈ F(V, z)`. Two such
pairs built by restricting one section `s` of `F` along two morphisms of `El Z` with the same
target agree as soon as the two morphisms have the same base morphism of `C`; this is what makes
the restriction maps of `Σ_Z F` functorial. -/

/-- Contravariant functoriality of `F`, in applied form. -/
lemma totalMap_op_comp {P Q R : (presheafOfCategories (Z ⋙ typeToCat)).obj} (a : P ⟶ Q)
    (b : Q ⟶ R) (s : F.obj (op R)) : F.map a.op (F.map b.op s) = F.map (a ≫ b).op s := by
  rw [op_comp, F.map_comp_apply]

/-- Two morphisms of `El Z` with one and the same target and one and the same base morphism of
`C` restrict a section `s` of `F` to the same pair. -/
lemma totalMk_eq {V : C} {Q : (presheafOfCategories (Z ⋙ typeToCat)).obj} (s : F.obj (op Q))
    {y y' : Z.obj (op V)} (e : elementsPoint Z y ⟶ Q) (e' : elementsPoint Z y' ⟶ Q)
    (h : e.base = e'.base) :
    (⟨y, F.map e.op s⟩ : Σ t : Z.obj (op V), F.obj (op (elementsPoint Z t))) =
      ⟨y', F.map e'.op s⟩ := by
  have h1 : y = Z.map (Quiver.Hom.op e.base) Q.fiber.as := Discrete.eq_of_hom e.fiber
  have h2 : y' = Z.map (Quiver.Hom.op e'.base) Q.fiber.as := Discrete.eq_of_hom e'.fiber
  have hy : y = y' := by rw [h1, h2, h]
  subst hy
  rw [elements_hom_ext e e' h]

/-- Restricting along a morphism of `El Z` whose base morphism of `C` is the identity does
nothing. -/
lemma totalMk_eq_self {Q : (presheafOfCategories (Z ⋙ typeToCat)).obj} (s : F.obj (op Q))
    {y : Z.obj (op Q.base)} (e : elementsPoint Z y ⟶ Q) (h : e.base = 𝟙 Q.base) :
    (⟨y, F.map e.op s⟩ : Σ t : Z.obj (op Q.base), F.obj (op (elementsPoint Z t))) =
      ⟨Q.fiber.as, s⟩ := by
  have hid : F.map (Quiver.Hom.op (𝟙 Q)) s = s := by
    change F.map (𝟙 (op Q)) s = s
    rw [Functor.map_id_apply]
  exact (totalMk_eq Z F s e (𝟙 Q) h).trans
    (congrArg (fun t => (⟨Q.fiber.as, t⟩ :
      Σ t' : Z.obj (op Q.base), F.obj (op (elementsPoint Z t')))) hid)

/-- Restricting along a morphism of `El Z` that factors as `e₂ ≫ e₁` is restricting along `e₁`
and then along `e₂`. -/
lemma totalMk_eq_comp {V : C} {Q R : (presheafOfCategories (Z ⋙ typeToCat)).obj}
    (s : F.obj (op Q)) {y y' : Z.obj (op V)} (e : elementsPoint Z y ⟶ Q) (e₁ : R ⟶ Q)
    (e₂ : elementsPoint Z y' ⟶ R) (h : e.base = e₂.base ≫ e₁.base) :
    (⟨y, F.map e.op s⟩ : Σ t : Z.obj (op V), F.obj (op (elementsPoint Z t))) =
      ⟨y', F.map e₂.op (F.map e₁.op s)⟩ := by
  rw [totalMap_op_comp]
  exact totalMk_eq Z F s e (e₂ ≫ e₁) h

/-! ### The total presheaf -/

/-- **The total presheaf of a presheaf on a category of elements.** For a presheaf `F` on the
category of elements of `Z`, the presheaf `V ↦ ∐_{z ∈ Z(V)} F(V, z)` on `C`, with the obvious
restriction maps: `(z, s)` restricts along `f : W ⟶ V` to `(Z(f)(z), s|_{(W, Z(f)(z))})`. -/
def elementsTotalPresheaf : Cᵒᵖ ⥤ Type v where
  obj V := Σ z : Z.obj V, F.obj (op (elementsPoint Z z))
  map {_ _} f := ↾fun p => ⟨Z.map f p.1, F.map (elementsRestrict Z f p.1).op p.2⟩
  map_id V := by
    ext p : 3
    obtain ⟨z, s⟩ := p
    exact totalMk_eq_self Z F s _ (by simp)
  map_comp {_ _ _} f g := by
    ext p : 3
    obtain ⟨z, s⟩ := p
    exact totalMk_eq_comp Z F s _ _ _ (by simp)

/-- The point of `Z` carried by the restriction along `f` of a section of `Σ_Z F` is the
restriction along `f` of the point of `Z` that the section carries. -/
@[simp] lemma elementsTotalPresheaf_map_fst {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (p : (elementsTotalPresheaf Z F).obj X) :
    ((elementsTotalPresheaf Z F).map f p).1 = Z.map f p.1 :=
  rfl

/-- The structure morphism `Σ_Z F ⟶ Z` of the total presheaf, reading off the point of `Z` that a
section carries. -/
def elementsTotalProj : elementsTotalPresheaf Z F ⟶ Z where
  app _ := ↾fun p => p.1
  naturality _ _ _ := rfl

/-- The projection `Σ_Z F ⟶ Z` sends a section to the point of `Z` that it carries. -/
@[simp] lemma elementsTotalProj_app_apply (V : Cᵒᵖ) (p : (elementsTotalPresheaf Z F).obj V) :
    (elementsTotalProj Z F).app V p = p.1 :=
  rfl

/-! ### The category of elements of the total presheaf -/

/-- A morphism of the category of elements of `Σ_Z F` carries the point of `Z` of its target back
to the point of `Z` of its source. -/
lemma totalFactorOf_map
    {P Q : (presheafOfCategories (elementsTotalPresheaf Z F ⋙ typeToCat)).obj} (u : P ⟶ Q) :
    P.fiber.as.1 = Z.map (Quiver.Hom.op u.base) Q.fiber.as.1 :=
  congrArg Sigma.fst (Discrete.eq_of_hom u.fiber)

/-- The morphism of `El Z` between the points of `Z` that the two ends of a morphism of the
category of elements of `Σ_Z F` carry. -/
def totalBaseHom {P Q : (presheafOfCategories (elementsTotalPresheaf Z F ⋙ typeToCat)).obj}
    (u : P ⟶ Q) : elementsPoint Z P.fiber.as.1 ⟶ elementsPoint Z Q.fiber.as.1 :=
  ⟨u.base, Discrete.eqToHom (totalFactorOf_map Z F u)⟩

/-- The underlying morphism of `C` of `totalBaseHom Z F u` is the underlying morphism of `u`. -/
@[simp] lemma totalBaseHom_base
    {P Q : (presheafOfCategories (elementsTotalPresheaf Z F ⋙ typeToCat)).obj} (u : P ⟶ Q) :
    (totalBaseHom Z F u).base = u.base :=
  rfl

/-- A morphism of the category of elements of `Σ_Z F` restricts the section of `F` of its target
to the section of `F` of its source. -/
lemma totalSectionOf_map
    {P Q : (presheafOfCategories (elementsTotalPresheaf Z F ⋙ typeToCat)).obj} (u : P ⟶ Q) :
    P.fiber.as.2 = F.map (totalBaseHom Z F u).op Q.fiber.as.2 := by
  have h : (⟨P.fiber.as.1, P.fiber.as.2⟩ :
      Σ t : Z.obj (op P.base), F.obj (op (elementsPoint Z t))) =
      ⟨P.fiber.as.1, F.map (totalBaseHom Z F u).op Q.fiber.as.2⟩ := by
    refine (Discrete.eq_of_hom u.fiber).trans ?_
    exact totalMk_eq Z F Q.fiber.as.2 (elementsRestrict Z (Quiver.Hom.op u.base) Q.fiber.as.1)
      (totalBaseHom Z F u) rfl
  simpa using h

/-- An object of the category of elements of `F` — a point of `Z` together with a section of `F`
at it — read as an element of the total presheaf `Σ_Z F`. -/
def elementsToTotal :
    (presheafOfCategories (F ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (elementsTotalPresheaf Z F ⋙ typeToCat)).obj where
  obj Y := ⟨Y.base.base, Discrete.mk ⟨Y.base.fiber.as, Y.fiber.as⟩⟩
  map {Y Y'} u := ⟨u.base.base, Discrete.eqToHom (by
    refine (congrArg (fun s => (⟨Y.base.fiber.as, s⟩ :
      Σ t : Z.obj (op Y.base.base), F.obj (op (elementsPoint Z t))))
      (Discrete.eq_of_hom u.fiber)).trans ?_
    exact totalMk_eq Z F Y'.fiber.as u.base
      (elementsRestrict Z (Quiver.Hom.op u.base.base) Y'.base.fiber.as) rfl)⟩
  map_id _ := elements_hom_ext _ _ rfl
  map_comp _ _ := elements_hom_ext _ _ rfl

/-- The forward functor is strictly over `C`. -/
lemma elementsToTotal_comp_eq :
    elementsToTotal Z F ⋙ (presheafOfCategories (elementsTotalPresheaf Z F ⋙ typeToCat)).p =
      (presheafOfCategories (F ⋙ typeToCat)).p ⋙ (presheafOfCategories (Z ⋙ typeToCat)).p :=
  rfl

/-- An element of the total presheaf `Σ_Z F`, read as an object of the category of elements of
`F`: the point of `Z` it carries names an object of `El Z`, and the section of `F` it carries
lives at that object. -/
def totalToElements :
    (presheafOfCategories (elementsTotalPresheaf Z F ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (F ⋙ typeToCat)).obj where
  obj P := ⟨elementsPoint Z P.fiber.as.1, Discrete.mk P.fiber.as.2⟩
  map {_ _} u := ⟨totalBaseHom Z F u, Discrete.eqToHom (totalSectionOf_map Z F u)⟩
  map_id _ := elements_hom_ext _ _ (elements_hom_ext _ _ rfl)
  map_comp _ _ := elements_hom_ext _ _ (elements_hom_ext _ _ rfl)

/-- The backward functor is strictly over `C`: the base of an element of `Σ_Z F` is the base of
the object of `El Z` that its point of `Z` names. -/
lemma totalToElements_comp_eq :
    totalToElements Z F ⋙ (presheafOfCategories (F ⋙ typeToCat)).p ⋙
        (presheafOfCategories (Z ⋙ typeToCat)).p =
      (presheafOfCategories (elementsTotalPresheaf Z F ⋙ typeToCat)).p :=
  rfl

/-- **The category of elements of a total presheaf.** Viewed over `C` through the projection of
the category of elements of `Z`, the category of elements of `F` is the category of elements of
`Σ_Z F`, as an equivalence in the 2-category of categories over `C`. -/
def totalElementsEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver
      ((presheafOfCategories (F ⋙ typeToCat)).p ⋙ (presheafOfCategories (Z ⋙ typeToCat)).p)
      (presheafOfCategories (elementsTotalPresheaf Z F ⋙ typeToCat)).p where
  hom := ⟨elementsToTotal Z F, elementsToTotal_comp_eq Z F⟩
  inv := ⟨totalToElements Z F, totalToElements_comp_eq Z F⟩
  unitIso := NatIso.ofComponents Iso.refl
    (by
      intro Y Y' u
      refine elements_hom_ext _ _ (elements_hom_ext _ _ ?_)
      change u.base.base ≫ 𝟙 Y'.base.base = 𝟙 Y.base.base ≫ u.base.base
      simp)
  counitIso := NatIso.ofComponents Iso.refl
    (by
      intro P Q u
      refine elements_hom_ext _ _ ?_
      change u.base ≫ 𝟙 Q.base = 𝟙 P.base ≫ u.base
      simp)
  unit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl
  counit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl

/-- The section of `Σ_Z F` named by an object `Y` of the category of elements of `F` through
`CategoryTheory.PresheafOfCategories.totalElementsEquivalenceOver` is the explicit pair: the
point of `Z` that the base of `Y` is, together with the section of `F` that `Y` names. -/
@[simp] lemma sectionOfObj_totalElementsEquivalenceOver
    (Y : (presheafOfCategories (F ⋙ typeToCat)).obj) :
    sectionOfObj (totalElementsEquivalenceOver Z F) Y rfl =
      ⟨Y.base.fiber.as, Y.fiber.as⟩ :=
  rfl

end CategoryTheory.PresheafOfCategories

end
