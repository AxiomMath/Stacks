module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Basic

/-!
# The canonical restriction functor is an equivalence for an empty family of points

For a finite family `s : I → S` of closed points of a scheme `S`, the functor
`AlgebraicGeometry.canonicalRestrictionFunctor` from schemes of finite presentation over `S` to
gluing data near the family is an equivalence of categories when the index type `I` is empty: then
the gluing datum has no local components, and the canonical functor reduces to restriction to the
open complement, which is all of `S`.

## Main results

* `AlgebraicGeometry.canonicalRestrictionFunctor_isEquivalence_of_isEmpty`: for an empty family
  of points, the canonical restriction functor is an equivalence of categories.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe v u w₁ w₂ w₃

namespace AlgebraicGeometry

/-- If every morphism of `C` lies in a `Unique` hom-type, every morphism of `C` is an
isomorphism. -/
theorem isIsoOfUniqueHom {C : Type w₁} [Category.{v} C]
    (huniqHom : ∀ X Y : C, Unique (X ⟶ Y)) {X Y : C} (f : X ⟶ Y) : IsIso f :=
  ⟨(huniqHom Y X).default, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The inclusion of a full subcategory satisfied by every object is essentially surjective. -/
theorem essSurjιOfForall {C : Type w₁} [Category.{v} C] (P : ObjectProperty C)
    (hP : ∀ X, P X) : P.ι.EssSurj where
  mem_essImage Y := ⟨⟨Y, hP Y⟩, ⟨Iso.refl _⟩⟩

/-- The quasi-inverse to `Comma.fst F G` when `B` has a unique object and every hom-type of `C`
is `Unique`: send `a : A` to the unique comma object over it. -/
noncomputable def commaFstInverse {A : Type w₁} {B : Type w₂} {C : Type w₃} [Category.{v} A]
    [Category.{v} B] [Category.{v} C] (F : A ⥤ C) (G : B ⥤ C) [Unique B]
    (huniqHom : ∀ X Y : C, Unique (X ⟶ Y)) : A ⥤ Comma F G where
  obj a := ⟨a, default, (huniqHom _ _).default⟩
  map f := ⟨f, 𝟙 default, Subsingleton.elim _ _⟩
  map_id _ := Comma.hom_ext _ _ rfl rfl
  map_comp _ _ := Comma.hom_ext _ _ rfl (by simp)

/-- If `B` has a unique object, a unique morphism between any two of its objects, and every
hom-type of `C` is `Unique`, then the first projection `Comma.fst F G` of the comma category is
an equivalence of categories. -/
theorem commaFstIsEquivalenceOfUnique {A : Type w₁} {B : Type w₂} {C : Type w₃} [Category.{v} A]
    [Category.{v} B] [Category.{v} C] (F : A ⥤ C) (G : B ⥤ C) [Unique B]
    [∀ X Y : B, Subsingleton (X ⟶ Y)] (huniqHom : ∀ X Y : C, Unique (X ⟶ Y)) :
    (Comma.fst F G).IsEquivalence :=
  Functor.IsEquivalence.mk' (commaFstInverse F G huniqHom)
    (NatIso.ofComponents
      (fun X ↦ Comma.isoMk (Iso.refl X.left) (eqToIso (Subsingleton.elim X.right default))
        (Subsingleton.elim _ _))
      (fun _ ↦ Comma.hom_ext _ _ (by simp [commaFstInverse]) (Subsingleton.elim _ _)))
    (NatIso.ofComponents (fun a ↦ Iso.refl a) (fun _ ↦ by simp [commaFstInverse]))

/-- Over an empty index type, each hom-type of the product category is `Unique`. -/
private instance uniqueHomPiOfIsEmpty {J : Type w₁} [IsEmpty J] {C : J → Type w₂}
    [∀ j, Category.{v} (C j)] (X Y : ∀ j, C j) : Unique (X ⟶ Y) := by
  change Unique (∀ j, X j ⟶ Y j)
  infer_instance

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S) (hs : ∀ i, s i ∈ closedPoints S)

/-- For an empty family of points, the projection of a gluing datum to its component over the
open complement is an equivalence of categories. -/
theorem openComponent_isEquivalence_of_isEmpty [IsEmpty I] :
    (openComponent s hs).IsEquivalence := by
  have huniqHomC := fun X Y : (i : I) → FinitePresentationOver (puncturedLocalScheme s hs i) ↦
    uniqueHomPiOfIsEmpty X Y
  have : ∀ X Y : (i : I) → FinitePresentationOver (Spec (S.presheaf.stalk (s i))),
      Subsingleton (X ⟶ Y) := fun X Y ↦ (uniqueHomPiOfIsEmpty X Y).instSubsingleton
  let P : ObjectProperty (Comma (restrictOpenToPuncturedLocals s hs)
      (restrictLocalsToPuncturedLocals s hs)) := fun X ↦ IsIso X.hom
  have : P.ι.EssSurj := essSurjιOfForall _ fun X ↦ isIsoOfUniqueHom huniqHomC X.hom
  have : P.ι.IsEquivalence := { faithful := inferInstance, full := inferInstance }
  have := commaFstIsEquivalenceOfUnique (restrictOpenToPuncturedLocals s hs)
    (restrictLocalsToPuncturedLocals s hs) huniqHomC
  change (P.ι ⋙ Comma.fst (restrictOpenToPuncturedLocals s hs)
    (restrictLocalsToPuncturedLocals s hs)).IsEquivalence
  infer_instance

/-- For an empty family of points, the open complement of the family is everything. -/
theorem complementOfClosedPoints_eq_top_of_isEmpty [IsEmpty I] :
    complementOfClosedPoints s hs = ⊤ := by
  ext x
  simp [complementOfClosedPoints]

/-- For an empty family of points, restriction to the open complement is an equivalence of
categories. -/
theorem restrictToComplementOfClosedPoints_isEquivalence_of_isEmpty [IsEmpty I] :
    (restrictToComplementOfClosedPoints s hs).IsEquivalence := by
  have : IsIso (complementOfClosedPoints s hs).ι := by
    rw [complementOfClosedPoints_eq_top_of_isEmpty s hs,
      show (⊤ : S.Opens).ι = S.topIso.hom from rfl]
    infer_instance
  exact finitePresentationBaseChange_isEquivalence_of_isIso (complementOfClosedPoints s hs).ι

/-- For an empty family of points, the canonical restriction functor from schemes of finite
presentation over `S` to gluing data is an equivalence of categories. -/
@[stacks 0E8Q "equivalence, special case of an empty family of points"]
theorem canonicalRestrictionFunctor_isEquivalence_of_isEmpty [IsEmpty I] :
    (canonicalRestrictionFunctor s hs).IsEquivalence := by
  have hG : (openComponent s hs).IsEquivalence := openComponent_isEquivalence_of_isEmpty s hs
  have hFG : (canonicalRestrictionFunctor s hs ⋙ openComponent s hs).IsEquivalence := by
    rw [openComponent_comp_canonicalRestrictionFunctor]
    exact restrictToComplementOfClosedPoints_isEquivalence_of_isEmpty s hs
  exact Functor.isEquivalence_of_comp_right (canonicalRestrictionFunctor s hs) (openComponent s hs)

end AlgebraicGeometry

end
