module

public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp

/-!
# A slice of a category is the category of elements of a representable presheaf

Let `𝒞` be a category and `X` an object of it. The slice `𝒞/X`, with its projection
`CategoryTheory.Over.forget X`, is the category of elements (Stacks 02XV applied to the presheaf
of discrete categories `yoneda.obj X ⋙ typeToCat`) of the representable presheaf of `X`: both have
objects the pairs `(V, s : V ⟶ X)`, and both have for morphisms the factorizations. More
generally, for `g : A ⟶ X` the relocalization functor `CategoryTheory.Over.map g : 𝒞/A ⥤ 𝒞/X`
is, as a category over `𝒞/X`, the category of elements of the presheaf on `𝒞/X` represented by
`A/X`.

Both statements are equivalences in the 2-category of categories over the base, in the sense of
`StacksRepresentableCFG.EquivalenceOver`, so they are exactly what the representability
predicates of Stacks 04SV and Stacks 02ZW quantify over: they turn
`StacksRepresentableCFG.RepresentableBy p X`, which compares `p` with `Over.forget X`, into a
comparison of `p` with the category of elements of a presheaf, and they exhibit the big site of
an object over a base as represented by that object.

## Main definitions

* `CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`: `𝒞/X` is the category of
  elements of `yoneda.obj X`, over `𝒞`.
* `CategoryTheory.PresheafOfCategories.overMapElementsEquivalenceOver`: for `g : A ⟶ X`, the
  relocalization functor `Over.map g` is the category of elements of `yoneda.obj (Over.mk g)`,
  over `𝒞/X`.
* `CategoryTheory.PresheafOfCategories.overMapForgetEquivalenceOver`: consequently `Over.map g`
  is the localization functor of `𝒞/X` at `A/X`, as an equivalence over `𝒞/X`.

## Main results

* `CategoryTheory.PresheafOfCategories.elements_hom_ext`: a morphism of a category of elements is
  determined by its base.
* `CategoryTheory.PresheafOfCategories.elementsIsoOfBaseIso`: an isomorphism of categories of
  elements from an isomorphism of the bases carrying one element to the other.

## Implementation notes

The forward functors are isomorphisms of categories on the nose: for `Over.forget X` both
composites are the identity by `rfl`, which is why the unit and the counit there are
`CategoryTheory.Iso.refl`. For `Over.map g` only one composite is, because an object `Z` of the
category of elements has `Z.base.hom` an arbitrary morphism to `X` while the round trip produces
`Over.mk (Z.fiber.as.left ≫ g)`, and `Z.fiber.as.left ≫ g = Z.base.hom` only propositionally
(`CategoryTheory.Over.w`). That is also why `elementsToOverMap_map_eq` — the statement that the
backward functor is strictly over `𝒞/X` — is a `CategoryTheory.Functor.ext` and not an `rfl`.

`over_hom_eq_conj` exists because the `eqToHom`-conjugated equation that
`CategoryTheory.Functor.ext` leaves behind cannot be rewritten with
`CategoryTheory.Over.eqToHom_left` in place: the goal mentions the projections `Z.base` and
`Z.fiber` of an object of the category of elements, and those are not type-correct at the
transparency at which `rw` re-elaborates its motive. Stating the step for abstract objects of
`𝒞/X` removes the projections from the goal and is the structural fix; no `set_option` is needed.

`CategoryTheory.PresheafOfCategories.overMapForgetEquivalenceOver` is the content of Stacks 03EH
that `map_eq_forget_iteratedSlice` in
`StacksFrontier/CategoryTheory/Sites/Localization/RelocalizationTriangle.lean` records as an equality
of functors; it is derived here, rather than imported from there, because that module's import
closure is unrelated to this one.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.PresheafOfCategories

universe v u a

variable {C : Type u} [Category.{v} C]

/-- A morphism of the category of elements of a presheaf of sets is determined by its base: its
second component lives in a discrete category, so it is unique once the base is fixed. -/
lemma elements_hom_ext {G : Cᵒᵖ ⥤ Type a}
    {Z W : (presheafOfCategories (G ⋙ typeToCat)).obj} (u w : Z ⟶ W)
    (h : u.base = w.base) : u = w := by
  obtain ⟨ub, uf⟩ := u
  obtain ⟨wb, wf⟩ := w
  change ub = wb at h
  subst h
  congr 1
  exact Discrete.hom_eq

/-- An isomorphism of the category of elements of a presheaf of sets, from an isomorphism of the
two bases which carries the element named by the target to the element named by the source. -/
def elementsIsoOfBaseIso {G : Cᵒᵖ ⥤ Type a}
    {Z W : (presheafOfCategories (G ⋙ typeToCat)).obj} (e : Z.base ≅ W.base)
    (h : Z.fiber.as = G.map (Quiver.Hom.op e.hom) W.fiber.as) : Z ≅ W where
  hom := ⟨e.hom, Discrete.eqToHom h⟩
  inv := ⟨e.inv, Discrete.eqToHom (by
    change W.fiber.as = G.map (Quiver.Hom.op e.inv) Z.fiber.as
    rw [h, ← Functor.map_comp_apply, ← op_comp, e.inv_hom_id, op_id,
      Functor.map_id_apply])⟩
  hom_inv_id := elements_hom_ext _ _ (show e.hom ≫ e.inv = 𝟙 Z.base from e.hom_inv_id)
  inv_hom_id := elements_hom_ext _ _ (show e.inv ≫ e.hom = 𝟙 W.base from e.inv_hom_id)

/-- An object of a slice is recovered from its structure morphism. -/
lemma over_mk_eq {X : C} (b : Over X) {h : b.left ⟶ X} (e : h = b.hom) : Over.mk h = b := by
  subst e
  rfl

/-- An equation between a morphism of `𝒞/X` and an `eqToHom`-conjugate of another one, reduced to
the underlying morphisms of `𝒞`. This is the shape `CategoryTheory.Functor.ext` asks for, stated
for abstract objects of the slice so that `CategoryTheory.Over.eqToHom_left` applies. -/
lemma over_hom_eq_conj {X : C} {b b' c c' : Over X} (hb : b = c) (hb' : b' = c')
    (hl : b.left = c.left) (hl' : b'.left = c'.left) (φ : b ⟶ b') (ψ : c ⟶ c')
    (h : φ.left = eqToHom hl ≫ ψ.left ≫ eqToHom hl'.symm) :
    φ = eqToHom hb ≫ ψ ≫ eqToHom hb'.symm := by
  ext
  rwa [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left]

section Slice

variable (X : C)

/-- An object of the slice `𝒞/X`, read as an element of the presheaf represented by `X`. -/
def sliceToElements :
    Over X ⥤ (presheafOfCategories (yoneda.obj X ⋙ typeToCat)).obj where
  obj a := ⟨a.left, Discrete.mk a.hom⟩
  map {_ _} h := ⟨h.left, Discrete.eqToHom (Over.w h).symm⟩
  map_id _ := elements_hom_ext _ _ rfl
  map_comp _ _ := elements_hom_ext _ _ rfl

/-- An element of the presheaf represented by `X`, read as an object of the slice `𝒞/X`. -/
def elementsToSlice :
    (presheafOfCategories (yoneda.obj X ⋙ typeToCat)).obj ⥤ Over X where
  obj Z := Over.mk Z.fiber.as
  map {_ _} u := Over.homMk u.base (Discrete.eq_of_hom u.fiber).symm
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The slice `𝒞/X` is the category of elements of the presheaf represented by `X`**, as an
equivalence in the 2-category of categories over `𝒞`. -/
def sliceElementsEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (Over.forget X)
      (presheafOfCategories (yoneda.obj X ⋙ typeToCat)).p where
  hom := ⟨sliceToElements X, rfl⟩
  inv := ⟨elementsToSlice X, rfl⟩
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (by
      intro Z W u
      refine elements_hom_ext _ _ ?_
      change u.base ≫ 𝟙 _ = 𝟙 _ ≫ u.base
      simp)
  unit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ ↦ IsHomLift.id rfl
  counit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ ↦ IsHomLift.id rfl

end Slice

section OverMap

variable {X A : C} (g : A ⟶ X)

/-- An object of `𝒞/A`, read as an element of the presheaf on `𝒞/X` represented by `A/X`: its
structure morphism composed with `g` is the base, and the structure morphism itself is the
element. -/
def overMapToElements :
    Over A ⥤ (presheafOfCategories (yoneda.obj (Over.mk g) ⋙ typeToCat)).obj where
  obj b := ⟨Over.mk (b.hom ≫ g), Discrete.mk (Over.homMk b.hom rfl)⟩
  map {_ _} h :=
    ⟨Over.homMk h.left (by simp), Discrete.eqToHom (Over.OverMorphism.ext (Over.w h).symm)⟩
  map_id _ := elements_hom_ext _ _ (Over.OverMorphism.ext rfl)
  map_comp _ _ := elements_hom_ext _ _ (Over.OverMorphism.ext rfl)

/-- An element of the presheaf on `𝒞/X` represented by `A/X`, read as an object of `𝒞/A`: the
element is a morphism of `𝒞/X` to `A/X`, and its underlying morphism of `𝒞` is the structure
morphism. -/
def elementsToOverMap :
    (presheafOfCategories (yoneda.obj (Over.mk g) ⋙ typeToCat)).obj ⥤ Over A where
  obj Z := Over.mk Z.fiber.as.left
  map {_ _} u := Over.homMk u.base.left (congrArg Over.Hom.left (Discrete.eq_of_hom u.fiber).symm)
  map_id _ := Over.OverMorphism.ext rfl
  map_comp _ _ := Over.OverMorphism.ext rfl

/-- `CategoryTheory.PresheafOfCategories.elementsToOverMap` is strictly over `𝒞/X`: the base of
an element of the presheaf represented by `A/X` is the relocalization of the object of `𝒞/A` it
names. -/
lemma elementsToOverMap_map_eq :
    elementsToOverMap g ⋙ Over.map g
      = (presheafOfCategories (yoneda.obj (Over.mk g) ⋙ typeToCat)).p := by
  fapply CategoryTheory.Functor.ext
  · intro Z
    exact over_mk_eq Z.base (Over.w Z.fiber.as)
  · intro Z W u
    refine over_hom_eq_conj (over_mk_eq Z.base (Over.w Z.fiber.as))
      (over_mk_eq W.base (Over.w W.fiber.as)) rfl rfl _ _ ?_
    show u.base.left = eqToHom rfl ≫ u.base.left ≫ eqToHom rfl
    simp

/-- The identity of the underlying object of `𝒞`, read as an isomorphism between the base of an
element of the presheaf represented by `A/X` and the relocalization of the object of `𝒞/A` that
element names. -/
def overMapBaseIso (Z : (presheafOfCategories (yoneda.obj (Over.mk g) ⋙ typeToCat)).obj) :
    (Over.mk (Z.fiber.as.left ≫ g)) ≅ Z.base where
  hom := Over.homMk (𝟙 Z.base.left) (by simpa using (Over.w Z.fiber.as).symm)
  inv := Over.homMk (𝟙 Z.base.left) (by simpa using Over.w Z.fiber.as)
  hom_inv_id := Over.OverMorphism.ext (by simp)
  inv_hom_id := Over.OverMorphism.ext (by simp)

/-- **The relocalization functor `Over.map g : 𝒞/A ⥤ 𝒞/X` is the category of elements of the
presheaf on `𝒞/X` represented by `A/X`**, as an equivalence in the 2-category of categories over
`𝒞/X`. -/
def overMapElementsEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (Over.map g)
      (presheafOfCategories (yoneda.obj (Over.mk g) ⋙ typeToCat)).p where
  hom := ⟨overMapToElements g, rfl⟩
  inv := ⟨elementsToOverMap g, elementsToOverMap_map_eq g⟩
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun Z => elementsIsoOfBaseIso (overMapBaseIso g Z) (by
      apply Over.OverMorphism.ext
      change Z.fiber.as.left = 𝟙 Z.base.left ≫ Z.fiber.as.left
      simp))
    (by
      intro Z W u
      refine elements_hom_ext _ _ ?_
      apply Over.OverMorphism.ext
      change u.base.left ≫ 𝟙 W.base.left = 𝟙 Z.base.left ≫ u.base.left
      simp)
  unit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ ↦ IsHomLift.id rfl
  counit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun Z ↦ ?_
    refine IsHomLift.of_fac' _ _ _ rfl (over_mk_eq Z.base (Over.w Z.fiber.as)).symm ?_
    refine over_hom_eq_conj rfl (over_mk_eq Z.base (Over.w Z.fiber.as)).symm rfl rfl _ _ ?_
    change 𝟙 Z.base.left = eqToHom rfl ≫ 𝟙 Z.base.left ≫ eqToHom rfl
    simp

/-- **Stacks 03EH.** The relocalization functor `Over.map g : 𝒞/A ⥤ 𝒞/X` of `g : A ⟶ X` is the
localization functor of `𝒞/X` at its object `A/X`, as an equivalence in the 2-category of
categories over `𝒞/X`. -/
def overMapForgetEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (Over.map g) (Over.forget (Over.mk g)) :=
  (overMapElementsEquivalenceOver g).trans
    (sliceElementsEquivalenceOver (Over.mk g)).symm

end OverMap

end CategoryTheory.PresheafOfCategories

end
