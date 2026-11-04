module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties
import StacksCore.Tactic.StacksAttribute

/-!
# Detecting injective objects by a set of monomorphisms

Injectivity of an object `I` of an abelian category is a condition quantified over *all*
monomorphisms, hence over a proper class. In a Grothendieck abelian category it is enough to
test it against the inclusions of the subobjects of a separator, of which there is only a set:
this is [Stacks, Tag 079G](https://stacks.math.columbia.edu/tag/079G).

This file records that criterion in two shapes — indexed by `Subobject G` for a separator `G`,
and as the bare existence of a set-indexed family of monomorphisms detecting injectivity — and
adds the observation that such a family can be transported along an adjunction: an extension
problem posed against `R.obj I` for a right adjoint `R` is the same as the extension problem
posed against `I` for the image of the test monomorphism under the left adjoint.

## Main results

* `CategoryTheory.injective_iff_exists_extension_of_subobject` is **Tag 079G**: an object of a
  Grothendieck abelian category is injective if and only if every morphism to it from a
  subobject of a separator extends to the separator.
* `CategoryTheory.exists_monomorphisms_injective_iff`: a Grothendieck abelian category has a
  set-indexed family of monomorphisms against which injectivity can be tested. This is the form
  in which [Stacks, Tag 0FSN](https://stacks.math.columbia.edu/tag/0FSN) and
  [Stacks, Tag 0FSS](https://stacks.math.columbia.edu/tag/0FSS) use Tag 079G.
* `CategoryTheory.Adjunction.exists_extension_map_iff`: for an adjunction `L ⊣ R`, a morphism
  `i` has the extension property against `R.obj I` if and only if `L.map i` has it against `I`.

## Implementation notes

The right lifting property of Mathlib's `CategoryTheory.IsGrothendieckAbelian` development is
what carries the content: `injective_iff_rlp_monomorphisms_zero` turns injectivity of `I` into
the right lifting property of `I ⟶ 0` against all monomorphisms, and
`IsGrothendieckAbelian.generatingMonomorphisms_rlp` says that this class of maps has the same
right lifting property as the inclusions of subobjects of a separator. The lift and the
factorization of a square whose target is a zero object are the same datum, which is the
translation performed in both directions of the proof.

The index type of the set-indexed family is `Shrink (Subobject G)`, which is a `Type w` for the
auxiliary universe `w` of `IsGrothendieckAbelian.{w}`, because that class implies
`CategoryTheory.WellPowered.{w}`. Neither the object universe `u` nor the hom universe `v` of
the category appears in it.

The adjunction statement is stated for the existence of an extension rather than for
`CategoryTheory.HasLiftingProperty` because the latter is a statement about a square, and the
squares in question have a zero object in a corner only after the ambient category is known to
be abelian; the adjunction transfer needs no additivity at all.

## References

* [Stacks Project, Tag 079G](https://stacks.math.columbia.edu/tag/079G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v' u' v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- **Stacks Tag 079G.** An object `I` of a Grothendieck abelian category is injective if and
only if, for every subobject `M` of a separator `G`, every morphism `M ⟶ I` extends along
`M.arrow` to a morphism `G ⟶ I`.

The forward implication is injectivity applied to the monomorphism `M.arrow`; the converse is
the statement that the inclusions of the subobjects of a separator have the same right lifting
property as all monomorphisms. -/
@[stacks 079G]
theorem injective_iff_exists_extension_of_subobject [Abelian C] [IsGrothendieckAbelian.{w} C]
    {G : C} (hG : IsSeparator G) (I : C) :
    Injective I ↔
      ∀ (M : Subobject G) (f : (M : C) ⟶ I), ∃ g : G ⟶ I, M.arrow ≫ g = f := by
  refine ⟨fun h M f ↦ h.factors f M.arrow, fun h ↦ ?_⟩
  rw [injective_iff_rlp_monomorphisms_zero,
    ← IsGrothendieckAbelian.generatingMonomorphisms_rlp (G := G) hG]
  rintro _ _ _ ⟨M⟩
  constructor
  intro f g sq
  obtain ⟨l, hl⟩ := h M f
  exact ⟨⟨{ l := l, fac_left := hl, fac_right := (isZero_zero C).eq_of_tgt _ _ }⟩⟩

/-- **Tag 079G in set-indexed form.** A Grothendieck abelian category has a set `T` and, for
each `t : T`, a monomorphism `N t ⟶ N' t` such that an object `I` is injective precisely when
every morphism `N t ⟶ I` extends to `N' t`.

The family is the one of `injective_iff_exists_extension_of_subobject`: the inclusions of the
subobjects of `CategoryTheory.separator C`, whose collection is `w`-small because a
Grothendieck abelian category is well-powered. This is the shape in which Tags 0FSN and 0FSS
consume Tag 079G. -/
@[stacks 079G "set-indexed form"]
theorem exists_monomorphisms_injective_iff (C : Type u) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] :
    ∃ (T : Type w) (N N' : T → C) (i : ∀ t, N t ⟶ N' t),
      (∀ t, Mono (i t)) ∧
        ∀ I : C, Injective I ↔ ∀ (t : T) (f : N t ⟶ I), ∃ g : N' t ⟶ I, i t ≫ g = f := by
  classical
  let G := separator C
  let e := (equivShrink.{w} (Subobject G)).symm
  refine ⟨Shrink.{w} (Subobject G), fun t ↦ ((e t : Subobject G) : C), fun _ ↦ G,
    fun t ↦ (e t).arrow, fun _ ↦ inferInstance, fun I ↦ ?_⟩
  rw [injective_iff_exists_extension_of_subobject (isSeparator_separator C)]
  refine ⟨fun h t f ↦ h (e t) f, fun h M f ↦ ?_⟩
  obtain ⟨t, rfl⟩ := e.surjective M
  exact h t f

namespace Adjunction

variable {D : Type u'} [Category.{v'} D]

/-- Extension problems transfer along an adjunction `L ⊣ R`: a morphism `i : N ⟶ N'` of the
source has the property that every morphism `N ⟶ R.obj I` extends along `i` if and only if
`L.map i` has the property that every morphism `L.obj N ⟶ I` extends along it.

Both directions are the hom-bijection of the adjunction together with its naturality in the
contravariant variable. Taking `L` to be the left adjoint of the functor forgetting the
differential of a differential graded module, this is what turns the detecting family of
[Stacks, Tag 0FSN](https://stacks.math.columbia.edu/tag/0FSN) into the detecting family of
[Stacks, Tag 0FSS](https://stacks.math.columbia.edu/tag/0FSS). -/
theorem exists_extension_map_iff {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {N N' : C} (i : N ⟶ N')
    (I : D) :
    (∀ f : L.obj N ⟶ I, ∃ g : L.obj N' ⟶ I, L.map i ≫ g = f) ↔
      ∀ f : N ⟶ R.obj I, ∃ g : N' ⟶ R.obj I, i ≫ g = f := by
  constructor <;> intro h f
  · obtain ⟨g, hg⟩ := h ((adj.homEquiv N I).symm f)
    exact ⟨adj.homEquiv N' I g, by
      simpa [adj.homEquiv_naturality_left] using congrArg (adj.homEquiv N I) hg⟩
  · obtain ⟨g, hg⟩ := h (adj.homEquiv N I f)
    exact ⟨(adj.homEquiv N' I).symm g, (adj.homEquiv N I).injective (by
      simpa [adj.homEquiv_naturality_left] using hg)⟩

end Adjunction

end CategoryTheory

end
