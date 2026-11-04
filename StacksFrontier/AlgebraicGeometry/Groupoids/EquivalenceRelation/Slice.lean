module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An internal equivalence relation in a slice category, read on the underlying morphisms

A pre-relation `j : R ⟶ U ×_S U` of schemes over `S` is an internal equivalence relation as soon
as the pair of *underlying* morphisms `R.left ⟶ U.left` is one in the category of schemes. The
converse is immediate — `CategoryTheory.Over.forget` is faithful and preserves what is needed —
but this direction is the useful one: an equivalence relation is almost always built in the
ambient category, where the relation object is a coproduct or a disjoint union of graphs, and
then has to be read in the slice category, which is where
`Stacks.Groupoids.IsEtaleEquivalenceRelation` lives.

The statement allows the relation object to be presented through an isomorphism `R' ≅ R.left`,
because the ambient-category construction usually produces a coproduct taken in the ambient
category while `R.left` is the underlying object of a coproduct taken in the slice category, and
those two are isomorphic rather than equal.

## Main results

* `Stacks.Groupoids.equivalence_of_equivalenceRelation_hom`: an internal equivalence relation
  induces an equivalence relation on the `T`-valued points of its target, for every `T`.
* `Stacks.Groupoids.isEquivalenceRelation_of_iso_left`: the transfer itself.

## Implementation notes

The proof goes through the pointwise characterisation
`Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation` (Stacks 043C,
parts (2)-(4)) rather than through the structure fields. Transporting the fields directly would
require a limiting pullback cone in the slice category, hence a construction of pullbacks there;
the pointwise route needs only that a morphism of the ambient category between objects of the
slice category which commutes with one of the two projections already lies over `S`, which is
`CategoryTheory.Over.w`.

## References

* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

open AlgebraicGeometry

/-- **An internal equivalence relation induces an equivalence relation on points.** For an
internal equivalence relation `p, q : R ⟶ U` and any object `T`, the relation on `T ⟶ U` which
holds of `x` and `y` when some `T ⟶ R` has images `x` and `y` is an equivalence relation. -/
theorem equivalence_of_equivalenceRelation_hom {C : Type*} [Category C] {R U : C}
    {p q : R ⟶ U} (e : EquivalenceRelation p q) (T : C) :
    Equivalence (fun x y : T ⟶ U => ∃ r : T ⟶ R, r ≫ p = x ∧ r ≫ q = y) := by
  constructor
  · intro x
    exact ⟨x ≫ e.r, by simp, by simp⟩
  · rintro x y ⟨r, hr₁, hr₂⟩
    exact ⟨r ≫ e.s, by rw [Category.assoc, e.symmetry₁, hr₂],
      by rw [Category.assoc, e.symmetry₂, hr₁]⟩
  · rintro x y z ⟨r, hr₁, hr₂⟩ ⟨r', hr₁', hr₂'⟩
    let l := PullbackCone.IsLimit.lift e.isLimit r r' (hr₂.trans hr₁'.symm)
    refine ⟨l ≫ e.t, ?_, ?_⟩
    · rw [Category.assoc, e.transitivity₁, ← Category.assoc,
        PullbackCone.IsLimit.lift_fst, hr₁]
    · rw [Category.assoc, e.transitivity₂, ← Category.assoc,
        PullbackCone.IsLimit.lift_snd, hr₂']

/-- **An internal equivalence relation in a slice category, from one on the underlying
morphisms.** Let `j : R ⟶ U ×_S U` be a pre-relation of schemes over `S`, let `i : R' ≅ R.left`
present the relation object in the category of schemes, and let `p, q : R' ⟶ U.left` be the two
projections read through `i`. If `p, q` is an internal equivalence relation of schemes then `j`
is an internal equivalence relation over `S`. -/
@[sga "3 IV 3.1.3" "special case"]
theorem isEquivalenceRelation_of_iso_left {S : Scheme.{u}} {R U : Over S}
    (j : PreRelation R U) {R' : Scheme.{u}} (i : R' ≅ R.left)
    (p q : R' ⟶ U.left) (hp : i.hom ≫ j.target.left = p)
    (hq : i.hom ≫ j.source.left = q) (h : IsEquivalenceRelation p q) :
    IsEquivalenceRelation j.target j.source := by
  obtain ⟨e⟩ := h.nonempty_equivalenceRelation
  have hl {T : Over S} (f : T ⟶ R) {a : R ⟶ U} {b : R' ⟶ U.left} (hb : i.hom ≫ a.left = b) :
      f.left ≫ i.inv ≫ b = (f ≫ a).left := by
    simp [← hb]
  apply (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mpr
  constructor
  · constructor
    intro T f g hfg
    apply Over.OverMorphism.ext
    apply (cancel_mono i.inv).mp
    apply e.right_cancellation
    · rw [Category.assoc, Category.assoc, hl f hp, hl g hp]
      exact congrArg Over.Hom.left
        (show f ≫ j.target = g ≫ j.target by
          simpa [PreRelation.target, Category.assoc] using
            congrArg (fun v => v ≫ prod.fst) hfg)
    · rw [Category.assoc, Category.assoc, hl f hq, hl g hq]
      exact congrArg Over.Hom.left
        (show f ≫ j.source = g ≫ j.source by
          simpa [PreRelation.source, Category.assoc] using
            congrArg (fun v => v ≫ prod.snd) hfg)
  · intro T
    have hrel (x y : T ⟶ U) : j.Rel x y ↔
        ∃ r : T.left ⟶ R', r ≫ p = x.left ∧ r ≫ q = y.left := by
      constructor
      · rintro ⟨r, h₁, h₂⟩
        exact ⟨r.left ≫ i.inv, by rw [Category.assoc, hl r hp, h₁],
          by rw [Category.assoc, hl r hq, h₂]⟩
      · rintro ⟨r, h₁, h₂⟩
        have ht : (r ≫ i.hom) ≫ j.target.left = x.left := by
          simpa only [Category.assoc, hp] using h₁
        have hs : (r ≫ i.hom) ≫ j.source.left = y.left := by
          simpa only [Category.assoc, hq] using h₂
        have hw : (r ≫ i.hom) ≫ R.hom = T.hom := by
          rw [← Over.w x, ← ht]
          simp
        exact ⟨Over.homMk (r ≫ i.hom) hw, Over.OverMorphism.ext ht, Over.OverMorphism.ext hs⟩
    have he := equivalence_of_equivalenceRelation_hom e T.left
    exact ⟨fun x => (hrel x x).mpr (he.refl x.left),
      fun hxy => (hrel _ _).mpr (he.symm ((hrel _ _).mp hxy)),
      fun hxy hyz => (hrel _ _).mpr (he.trans ((hrel _ _).mp hxy) ((hrel _ _).mp hyz))⟩

end Stacks.Groupoids

end
