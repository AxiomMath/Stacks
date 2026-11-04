module

public import Mathlib.CategoryTheory.Sites.MorphismProperty
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.FromSimplicialObject
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.MorphismProperty
public import StacksFrontier.CategoryTheory.Sites.HypercoverDescent

/-!
# Levels and faces of a hypercovering for a property of morphisms

Let `P` be a property of morphisms of a category `C` with fibre products which is multiplicative
and stable under base change, and let `U ⟶ X` be a `P`-hypercovering in the sense of Tag 0DER.
Regarding every level of `U` as a one-member family of objects over `X` turns `U ⟶ X` into a
hypercovering of `X` for the pretopology whose covering presieves are those all of whose members
belong to `P`. The permanence properties of coverings therefore apply, and give the two further
assertions of Tag 0DER: every level `Uₙ ⟶ X` belongs to `P`, and so does every face map
`δ i : U_{n+1} ⟶ Uₙ`.

## Main results

* `isHypercovering_pretopology_of_isHypercovering`: a `P`-hypercovering, read levelwise as a
  one-member family, is a hypercovering for `MorphismProperty.pretopology P`.
* `CategoryTheory.MorphismProperty.IsHypercovering.hom_app`: Tag 0DER, `levels_in_p` — every
  level of a `P`-hypercovering maps to the point of its augmentation by a morphism in `P`.
* `CategoryTheory.MorphismProperty.IsHypercovering.face_mem`: Tag 0DER, `faces_in_p` — every
  face map of a `P`-hypercovering in positive degree belongs to `P`.

## Implementation notes

The site used in the proof is Mathlib's `MorphismProperty.pretopology P`, whose covering presieves
of `X` are exactly the presieves all of whose members belong to `P`. The source instead speaks of
the site whose covering families are the one-member families `{f}` with `P f`; the two have the
same one-member coverings, which is all that is used, and the former is already stable under
indexed composition of covering families — the axiom of a site that Tag 0DEQ requires, and which
the one-member version does not satisfy (two different `P`-morphisms over one covering morphism
compose to a two-member family, which is not a one-member family).

The one-member simplicial semi-representable object of a `P`-hypercovering is
`associatedSimplicialObject A.left A.hom` of Tag 0GM9, so the covering conditions of a
hypercovering are available through `isHypercovering_associatedSimplicialObject_iff`, and in this
pretopology each of them is literally the assertion that the corresponding matching morphism
belongs to `P`.

## References

* [Stacks Project, Tag 0DEQ](https://stacks.math.columbia.edu/tag/0DEQ)
* [Stacks Project, Tag 0DER](https://stacks.math.columbia.edu/tag/0DER)
-/

@[expose] public section

universe w u v

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

section Pretopology

variable (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange]

/-- Every presieve of the pretopology of `P` whose members all belong to `P` is covering; in
particular a one-member presieve is covering exactly when its member belongs to `P`. -/
theorem singleton_mem_pretopology {X Y : C} (f : Y ⟶ X) :
    Presieve.singleton f ∈ P.pretopology X ↔ P f :=
  P.singleton_mem_precoverage f

/-- The pretopology of a multiplicative morphism property is stable under indexed composition of
covering families. -/
instance isStableUnderComposition_pretopology :
    Precoverage.IsStableUnderComposition (P.pretopology).toPrecoverage :=
  inferInstanceAs (Precoverage.IsStableUnderComposition P.precoverage)

/-- A `P`-hypercovering, with each of its levels read as a one-member family of objects over the
point of its augmentation, is a hypercovering of that point for the pretopology of `P`. -/
theorem isHypercovering_pretopology_of_isHypercovering
    (A : SimplicialObject.Augmented C) (hA : P.IsHypercovering A) :
    IsHypercovering.{w} P.pretopology (associatedSimplicialObject.{w} A.left A.hom) := by
  rw [isHypercovering_associatedSimplicialObject_iff]
  simp only [singleton_mem_pretopology]
  exact ⟨hA.map_zero, hA.map_one, hA.matching⟩

end Pretopology

end Stacks.CategoryTheory.Hypercovering

namespace CategoryTheory.MorphismProperty.IsHypercovering

open Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

omit [HasPullbacks C] in
/-- A morphism belongs to a property respecting isomorphisms as soon as its composite with a
transport along an equality of objects does. -/
private lemma of_comp_eqToHom {P : MorphismProperty C} [P.RespectsIso] {X Y Z : C} (f : X ⟶ Y)
    (p : Y = Z) (h : P (f ≫ eqToHom p)) : P f :=
  (P.cancel_right_of_respectsIso f (eqToHom p)).1 h

/-- Every face map in positive degree of a `P`-hypercovering belongs to `P`. -/
@[stacks 0DER "faces_in_p"]
lemma face_mem (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    {A : SimplicialObject.Augmented C}
    (hA : MorphismProperty.IsHypercovering P A) (n : ℕ) (i : Fin (n + 2)) :
    P (A.left.δ i) := by
  have h := isCoveringOver_delta P.pretopology
    (associatedSimplicialObject.{u} A.left A.hom)
    (isHypercovering_pretopology_of_isHypercovering.{u} P A hA) n i PUnit.unit
  rw [show ∀ (X : C) (S : Presieve X), (S ∈ P.pretopology X) = (S ∈ P.precoverage X) from
    fun _ _ ↦ rfl, MorphismProperty.ofArrows_mem_precoverage] at h
  have h₀ := h ⟨PUnit.unit, rfl⟩
  simp only [associatedSimplicialObject, FormalCoproduct.incl, SimplicialObject.δ,
    Functor.comp_map] at h₀
  exact of_comp_eqToHom _ _ h₀

variable {P : MorphismProperty C} {A : SimplicialObject.Augmented C}

/-- Every level of a `P`-hypercovering maps to its augmentation point by a morphism in `P`.

This is the `levels_in_p` assertion of **Stacks Project, Tag 0DER**. -/
@[stacks 0DER "levels_in_p"]
lemma hom_app [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    (hA : MorphismProperty.IsHypercovering P A) (n : ℕ) :
    P (A.hom.app (Opposite.op (SimplexCategory.mk n))) := by
  induction n with
  | zero => exact hA.map_zero
  | succ n ih =>
    have hnat : A.left.δ (0 : Fin (n + 2)) ≫ A.hom.app (Opposite.op (SimplexCategory.mk n)) =
        A.hom.app (Opposite.op (SimplexCategory.mk (n + 1))) := by
      simp [SimplicialObject.δ]
    exact hnat ▸ P.comp_mem _ _ (face_mem P hA n 0) ih

end CategoryTheory.MorphismProperty.IsHypercovering

end
