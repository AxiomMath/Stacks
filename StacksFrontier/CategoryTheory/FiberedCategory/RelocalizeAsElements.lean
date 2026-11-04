module

public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict

/-!
# The category of elements of a lower-shriek extension

Let `C` be a category, let `a : A ⟶ X` be a morphism of `C` and let `H` be a presheaf of sets on
`C/A`. The lower-shriek extension `Λ_a H = CategoryTheory.OverShriek.relocalizePresheafFunctor a`
is the presheaf on `C/X` whose sections over `W` are the pairs
`(ψ : W.left ⟶ A, s ∈ H(W.left →ψ A))` with `ψ ≫ a = W.hom`. Its category of elements is the
category of elements of `H`, viewed over `C/X` through the relocalization functor
`CategoryTheory.Over.map a`:

```text
El_{C/A} H  ⟶  C/A  --Over.map a-->  C/X     is     El_{C/X} (Λ_a H)  ⟶  C/X.
```

For `H` the terminal presheaf this is
`CategoryTheory.PresheafOfCategories.overMapElementsEquivalenceOver`.

## Main definitions

* `CategoryTheory.PresheafOfCategories.relocalizeToElements`: a section of `H` over `V : C/A`,
  read as an element of `Λ_a H` over `V` relocalized to `C/X`.
* `CategoryTheory.PresheafOfCategories.elementsToRelocalize`: the inverse construction.

## Main results

* `CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver`: the two are an
  equivalence in the 2-category of categories over `C/X`.
* `CategoryTheory.PresheafOfCategories.sectionOfObj_relocalizeElementsEquivalenceOver`: the
  section of `Λ_a H` that an object of the category of elements of `H` names through the
  equivalence is the explicit pair.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 03CD](https://stacks.math.columbia.edu/tag/03CD)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.PresheafOfCategories

universe v u

variable {C : Type u} [Category.{v} C] {X A : C} (a : A ⟶ X) (H : (Over A)ᵒᵖ ⥤ Type v)

/-- The factorization carried by the section of `Λ_a H` named by an object of the category of
elements of `Λ_a H`. -/
abbrev relocalizeFactorOf
    (P : (presheafOfCategories ((OverShriek.relocalizePresheafFunctor a).obj H ⋙
      typeToCat)).obj) : P.base.left ⟶ A :=
  P.fiber.as.1.1

/-- The section of `H` carried by an object of the category of elements of `Λ_a H`. -/
abbrev relocalizeSectionOf
    (P : (presheafOfCategories ((OverShriek.relocalizePresheafFunctor a).obj H ⋙
      typeToCat)).obj) : H.obj (op (Over.mk (relocalizeFactorOf a H P))) :=
  P.fiber.as.1.2

/-- A morphism of the category of elements of `Λ_a H` carries the factorization of its target
back to the factorization of its source. -/
lemma relocalizeFactorOf_map
    {P Q : (presheafOfCategories ((OverShriek.relocalizePresheafFunctor a).obj H ⋙
      typeToCat)).obj} (u : P ⟶ Q) :
    u.base.left ≫ relocalizeFactorOf a H Q = relocalizeFactorOf a H P :=
  (congrArg (fun p => p.1.1) (Discrete.eq_of_hom u.fiber)).symm

/-- A morphism of the category of elements of `Λ_a H` restricts the section of its target to the
section of its source. -/
lemma relocalizeSectionOf_map
    {P Q : (presheafOfCategories ((OverShriek.relocalizePresheafFunctor a).obj H ⋙
      typeToCat)).obj} (u : P ⟶ Q) :
    relocalizeSectionOf a H P =
      H.map (Over.homMk u.base.left (relocalizeFactorOf_map a H u) :
        Over.mk (relocalizeFactorOf a H P) ⟶ Over.mk (relocalizeFactorOf a H Q)).op
        (relocalizeSectionOf a H Q) := by
  have h : (⟨relocalizeFactorOf a H P, relocalizeSectionOf a H P⟩ :
      Σ χ : P.base.left ⟶ A, H.obj (op (Over.mk χ))) =
      ⟨relocalizeFactorOf a H P,
        H.map (Over.homMk u.base.left (relocalizeFactorOf_map a H u) :
          Over.mk (relocalizeFactorOf a H P) ⟶
            Over.mk (relocalizeFactorOf a H Q)).op (relocalizeSectionOf a H Q)⟩ := by
    refine (congrArg Subtype.val (Discrete.eq_of_hom u.fiber)).trans ?_
    exact (OverShriek.sigmaMk_eq H (relocalizeSectionOf a H Q)
      (ψ := relocalizeFactorOf a H P) (ψ' := u.base.left ≫ relocalizeFactorOf a H Q)
      (Over.homMk u.base.left (relocalizeFactorOf_map a H u))
      (Over.homMk u.base.left rfl) rfl).symm
  simpa using h

/-- A section of `H` over `V : C/A`, read as an element of `Λ_a H` over the relocalization of `V`
to `C/X`: the factorization is the structure morphism of `V` and the section is the given one. -/
def relocalizeToElements :
    (presheafOfCategories (H ⋙ typeToCat)).obj ⥤
      (presheafOfCategories ((OverShriek.relocalizePresheafFunctor a).obj H ⋙
        typeToCat)).obj where
  obj Z := ⟨Over.mk (Z.base.hom ≫ a),
    Discrete.mk (OverShriek.relocalizeMk a H Z.base.hom Z.fiber.as rfl)⟩
  map {Z W} u := ⟨Over.homMk u.base.left (by simp), Discrete.eqToHom (by
    refine Subtype.ext ?_
    refine (congrArg (fun s => (⟨Z.base.hom, s⟩ :
      Σ χ : Z.base.left ⟶ A, H.obj (op (Over.mk χ))))
      (Discrete.eq_of_hom u.fiber)).trans ?_
    exact OverShriek.sigmaMk_eq H W.fiber.as (ψ := Z.base.hom)
      (ψ' := u.base.left ≫ W.base.hom) u.base (Over.homMk u.base.left rfl) rfl)⟩
  map_id _ := elements_hom_ext _ _ (by apply Over.OverMorphism.ext; rfl)
  map_comp _ _ := elements_hom_ext _ _ (by apply Over.OverMorphism.ext; rfl)

/-- The forward functor is strictly over `C/X`. -/
lemma relocalizeToElements_comp_eq :
    relocalizeToElements a H ⋙
        (presheafOfCategories ((OverShriek.relocalizePresheafFunctor a).obj H ⋙
          typeToCat)).p =
      (presheafOfCategories (H ⋙ typeToCat)).p ⋙ Over.map a :=
  rfl

/-- An element of `Λ_a H` over `W : C/X`, read as a section of `H` over `W.left →ψ A` for the
factorization `ψ` it carries. -/
def elementsToRelocalize :
    (presheafOfCategories ((OverShriek.relocalizePresheafFunctor a).obj H ⋙
        typeToCat)).obj ⥤
      (presheafOfCategories (H ⋙ typeToCat)).obj where
  obj P := ⟨Over.mk (relocalizeFactorOf a H P), Discrete.mk (relocalizeSectionOf a H P)⟩
  map {P Q} u := ⟨Over.homMk u.base.left (relocalizeFactorOf_map a H u),
    Discrete.eqToHom (relocalizeSectionOf_map a H u)⟩
  map_id _ := elements_hom_ext _ _ (by apply Over.OverMorphism.ext; rfl)
  map_comp _ _ := elements_hom_ext _ _ (by apply Over.OverMorphism.ext; rfl)

/-- `CategoryTheory.PresheafOfCategories.elementsToRelocalize` is strictly over `C/X`: the base of
an element of `Λ_a H` is the relocalization of the object of `C/A` the factorization names. -/
lemma elementsToRelocalize_comp_eq :
    elementsToRelocalize a H ⋙ (presheafOfCategories (H ⋙ typeToCat)).p ⋙ Over.map a =
      (presheafOfCategories ((OverShriek.relocalizePresheafFunctor a).obj H ⋙
        typeToCat)).p := by
  fapply CategoryTheory.Functor.ext
  · intro P
    exact over_mk_eq P.base (OverShriek.relocalizeFactors a H P.fiber.as)
  · intro P Q u
    refine over_hom_eq_conj (over_mk_eq P.base (OverShriek.relocalizeFactors a H P.fiber.as))
      (over_mk_eq Q.base (OverShriek.relocalizeFactors a H Q.fiber.as)) rfl rfl _ _ ?_
    show u.base.left = eqToHom rfl ≫ u.base.left ≫ eqToHom rfl
    simp

/-- The identity of the underlying object of `C`, read as an isomorphism between the base of an
element of `Λ_a H` and the relocalization of the object of `C/A` its factorization names. -/
def relocalizeBaseIso
    (P : (presheafOfCategories ((OverShriek.relocalizePresheafFunctor a).obj H ⋙
      typeToCat)).obj) :
    Over.mk (relocalizeFactorOf a H P ≫ a) ≅ P.base where
  hom := Over.homMk (𝟙 P.base.left) (by
    simpa using (OverShriek.relocalizeFactors a H P.fiber.as).symm)
  inv := Over.homMk (𝟙 P.base.left) (by
    simpa using OverShriek.relocalizeFactors a H P.fiber.as)
  hom_inv_id := by apply Over.OverMorphism.ext; simp
  inv_hom_id := by apply Over.OverMorphism.ext; simp

/-- **The category of elements of a lower-shriek extension.** Viewed over `C/X` through
`CategoryTheory.Over.map a`, the category of elements of `H` is the category of elements of
`Λ_a H`, as an equivalence in the 2-category of categories over `C/X`. -/
def relocalizeElementsEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver
      ((presheafOfCategories (H ⋙ typeToCat)).p ⋙ Over.map a)
      (presheafOfCategories ((OverShriek.relocalizePresheafFunctor a).obj H ⋙
        typeToCat)).p where
  hom := ⟨relocalizeToElements a H, relocalizeToElements_comp_eq a H⟩
  inv := ⟨elementsToRelocalize a H, elementsToRelocalize_comp_eq a H⟩
  unitIso := NatIso.ofComponents (fun Z => Iso.refl Z)
    (by
      intro Z W u
      refine elements_hom_ext _ _ ?_
      apply Over.OverMorphism.ext
      change u.base.left ≫ 𝟙 W.base.left = 𝟙 Z.base.left ≫ u.base.left
      simp)
  counitIso := NatIso.ofComponents
    (fun P => elementsIsoOfBaseIso (relocalizeBaseIso a H P) (Subtype.ext
      (OverShriek.sigmaMk_eq_self H (relocalizeSectionOf a H P)
        (Over.homMk (𝟙 P.base.left) rfl :
          Over.mk (𝟙 P.base.left ≫ relocalizeFactorOf a H P) ⟶
            Over.mk (relocalizeFactorOf a H P)) rfl).symm))
    (by
      intro P Q u
      refine elements_hom_ext _ _ ?_
      apply Over.OverMorphism.ext
      change u.base.left ≫ 𝟙 Q.base.left = 𝟙 P.base.left ≫ u.base.left
      simp)
  unit_over :=
    StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ ↦ IsHomLift.id rfl
  counit_over := by
    apply StacksRepresentableCFG.whiskerRight_eq_eqToHom
    intro P
    refine IsHomLift.of_fac' _ _ _ rfl
      (over_mk_eq P.base (OverShriek.relocalizeFactors a H P.fiber.as)).symm ?_
    refine over_hom_eq_conj rfl
      (over_mk_eq P.base (OverShriek.relocalizeFactors a H P.fiber.as)).symm rfl rfl _ _ ?_
    change 𝟙 P.base.left = eqToHom rfl ≫ 𝟙 P.base.left ≫ eqToHom rfl
    simp

/-- The section of `Λ_a H` named by an object `Z` of the category of elements of `H` through
`CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver` is the explicit pair: the
structure morphism of the base of `Z` together with the section `Z` names. -/
@[simp] lemma sectionOfObj_relocalizeElementsEquivalenceOver
    (Z : (presheafOfCategories (H ⋙ typeToCat)).obj) :
    sectionOfObj (relocalizeElementsEquivalenceOver a H) Z rfl =
      OverShriek.relocalizeMk a H (W := op (Over.mk (Z.base.hom ≫ a))) Z.base.hom
        Z.fiber.as rfl :=
  rfl

end CategoryTheory.PresheafOfCategories

end
