module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack

/-!
# Cutting a category over a site down to one with set-sized fibres (Stacks 03ZZ)

Let `(𝒮, J)` be a site and let `p : 𝒳 ⥤ 𝒮` satisfy the three conditions of Stacks 026F,
`CategoryTheory.Functor.IsStack`, with `𝒳` a category too large to be the source of a stack —
in the source, one whose objects form a proper class. Stacks 03ZZ observes that `p` can
nevertheless be replaced by its restriction to a *full* subcategory with set-sized fibres,
provided

> (4) for every `U : 𝒮` there is a set of objects of the fibre `𝒳_U` such that every object of
> `𝒳_U` is isomorphic, *in `𝒳_U`*, to one of them.

Condition (4) is the hypothesis `EssentiallySmall.{w} (p.Fiber U)`: by
`CategoryTheory.Functor.essentiallySmall_fiber_iff` the two agree whenever the smallness
universe contains the hom universe of `𝒳`, since a fibre's hom types are hom types of `𝒳`.
The full subcategory `CategoryTheory.Functor.fibreRepresentatives` is then cut out by the chosen
representatives `CategoryTheory.Functor.fibreRepresentative` of the isomorphism classes of the
fibres, namely the images under `CategoryTheory.equivSmallModel` of the small models of the
fibres, and the two assertions of the remark hold for it:

* (a) `p` restricted to it satisfies the three conditions of Stacks 026F;
* (b) its inclusion into `𝒳` is fully faithful and essentially surjective.

## Main definitions

* `CategoryTheory.Functor.fibreRepresentative`, the chosen representative attached to an object
  of the small model of a fibre.
* `CategoryTheory.Functor.fibreRepresentatives`, the full subcategory they cut out.

## Main results

* `CategoryTheory.Functor.small_fibreRepresentatives` and
  `CategoryTheory.Functor.small_fiber_restrict_fibreRepresentatives`: the objects of the cutdown
  form a set, and each of its fibres is a set at the universe of condition (4).
* `CategoryTheory.Functor.IsStack.fibreRepresentatives`, assertion (a) of Stacks 03ZZ.
* `CategoryTheory.Functor.isEquivalence_ι_fibreRepresentatives`, assertion (b) of Stacks 03ZZ.

## Implementation notes

The source's hint cuts `𝒳` down to the objects of bounded von Neumann rank, taking the supremum
over `U` of the least ordinal whose stage surjects onto the isomorphism classes of `𝒳_U` (Sets,
Section 000B). Nothing of that is needed here: in Lean the content of condition (4) is precisely
relative essential smallness of the fibres, and the small model `CategoryTheory.SmallModel`
together with the equivalence `CategoryTheory.equivSmallModel` supply the representatives
directly. The index set is `Σ U : 𝒮, SmallModel (p.Fiber U)`, a set because `𝒮` is one, which is
the role the supremum of ordinals plays in the source.

Assertion (a) is Stacks 04TU, `CategoryTheory.Functor.IsStack.fullSubcategory`, rather than a
transport of the stack condition along the equivalence of (b): the cutdown is a full subcategory
on the nose, so no comparison functor has to be inverted. Both hypotheses of 04TU are
consequences of the single statement `CategoryTheory.Functor.isoOverId_fibreRepresentatives` that
every object of `𝒳` is isomorphic *over the identity of its image* to one of the representatives,
which is condition (4) read fibrewise.

`StacksFrontier/CategoryTheory/Sites/Descent/SmallStack.lean` reaches the same conclusion from the
hypotheses that `𝒮` is locally small and `𝒳` essentially small as a whole, rather than from
condition (4). There the representatives are only isomorphic to a given object in `𝒳`, so they
have to be pulled back along the isomorphism of their images before they are isomorphic to it
over an identity; condition (4) hands that fibrewise isomorphism over directly.

## References

* [Stacks Project, Tag 03ZZ](https://stacks.math.columbia.edu/tag/03ZZ)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU)
-/

@[expose] public section

open CategoryTheory

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

variable (p : 𝒳 ⥤ 𝒮) [∀ U : 𝒮, EssentiallySmall.{w} (p.Fiber U)]

/-- The representative of an isomorphism class of the fibre `𝒳_U` attached to an object of the
small model of that fibre: its image under the inverse of `CategoryTheory.equivSmallModel`, read
as an object of `𝒳`. -/
noncomputable def fibreRepresentative (i : Σ U : 𝒮, SmallModel.{w} (p.Fiber U)) : 𝒳 :=
  ((equivSmallModel.{w} (p.Fiber i.1)).inverse.obj i.2).1

/-- A representative attached to an object of the small model of `𝒳_U` lies over `U`. -/
lemma fibreRepresentative_proj (i : Σ U : 𝒮, SmallModel.{w} (p.Fiber U)) :
    p.obj (p.fibreRepresentative i) = i.1 :=
  ((equivSmallModel.{w} (p.Fiber i.1)).inverse.obj i.2).2

/-- The full subcategory `𝒳_small` of Stacks 03ZZ: the objects of `𝒳` that are chosen
representatives of isomorphism classes of the fibres of `p`. -/
noncomputable def fibreRepresentatives : ObjectProperty 𝒳 := .ofObj p.fibreRepresentative

/-- The objects of the cutdown form a set: they are indexed by the pairs of an object `U` of `𝒮`
and an object of the small model of `𝒳_U`. -/
@[stacks 03ZZ "the cutdown: a full subcategory of 𝒳 whose objects form a set"]
instance small_fibreRepresentatives :
    ObjectProperty.Small.{max u₁ w} (p.fibreRepresentatives) := by
  dsimp [fibreRepresentatives]
  infer_instance

/-- Every object of `𝒳` is isomorphic over the identity of its image to a chosen representative:
this is condition (4) of Stacks 03ZZ, whose isomorphisms are isomorphisms of a fibre. -/
lemma isoOverId_fibreRepresentatives (X : 𝒳) : IsoOverId p p.fibreRepresentatives X := by
  refine ⟨p.fibreRepresentative ⟨p.obj X, (equivSmallModel.{w} (p.Fiber (p.obj X))).functor.obj
      ⟨X, rfl⟩⟩, ⟨_⟩, (Fiber.fiberInclusion (p := p) (S := p.obj X)).mapIso
      ((equivSmallModel.{w} (p.Fiber (p.obj X))).unitIso.app ⟨X, rfl⟩), ?_⟩
  exact ((equivSmallModel.{w} (p.Fiber (p.obj X))).unitIso.app ⟨X, rfl⟩).hom.2

/-- Each fibre of the cutdown is a set at the universe of condition (4): the fibre over `U` is
covered by the small model of `𝒳_U`. -/
@[stacks 03ZZ "the cutdown: each of its fibres is a set"]
instance small_fiber_restrict_fibreRepresentatives (U : 𝒮) :
    Small.{w} ((p.restrict p.fibreRepresentatives).Fiber U) := by
  refine small_of_surjective (f := fun s : SmallModel.{w} (p.Fiber U) =>
    (⟨⟨p.fibreRepresentative ⟨U, s⟩, ⟨_⟩⟩, p.fibreRepresentative_proj ⟨U, s⟩⟩ :
      (p.restrict p.fibreRepresentatives).Fiber U)) ?_
  rintro ⟨⟨X, hX⟩, hXU⟩
  obtain ⟨i⟩ := hX
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj] at hXU
  have hi : i.1 = U := (p.fibreRepresentative_proj i).symm.trans hXU
  subst hi
  exact ⟨i.2, rfl⟩

/-- The inclusion of the cutdown is essentially surjective, because every object of `𝒳` is
isomorphic to a chosen representative. -/
instance essSurj_ι_fibreRepresentatives : (p.fibreRepresentatives).ι.EssSurj where
  mem_essImage X := by
    obtain ⟨Y, hY, e, _⟩ := p.isoOverId_fibreRepresentatives X
    exact ⟨⟨Y, hY⟩, ⟨e.symm⟩⟩

/-- **Stacks 03ZZ (b).** The inclusion `𝒳_small ⥤ 𝒳` of the cutdown is fully faithful and
essentially surjective. -/
@[stacks 03ZZ "(b): the inclusion of the cutdown is fully faithful and essentially surjective"]
theorem isEquivalence_ι_fibreRepresentatives : (p.fibreRepresentatives).ι.IsEquivalence := {}

/-- **Stacks 03ZZ (a).** If `p : 𝒳 ⥤ 𝒮` satisfies the three conditions of Stacks 026F over the
site `(𝒮, J)`, then so does its restriction to the cutdown; that is, the cutdown is a stack. -/
@[stacks 03ZZ "(a): the restriction of p to the cutdown satisfies the conditions of 026F"]
theorem IsStack.fibreRepresentatives (J : GrothendieckTopology 𝒮) (hp : p.IsStack J) :
    (p.restrict p.fibreRepresentatives).IsStack J := by
  refine IsStack.fullSubcategory p J hp _ ?_ ?_
  · intro _ _ Y _ _ _ _ _
    exact p.isoOverId_fibreRepresentatives Y
  · intro _ _ _ _ _ X _
    exact p.isoOverId_fibreRepresentatives X.1

end CategoryTheory.Functor

end
