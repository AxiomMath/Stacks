module

public import StacksFrontier.Deformation.Artin.Versality.Openness.Basic
public import StacksFrontier.Deformation.Artin.Versality.Openness.Composition
public import StacksFrontier.Deformation.Artin.Versality.Openness.BaseChange
public import StacksFrontier.Deformation.Artin.Versality.Openness.Comparison

/-!
# Openness of versality (Stacks chapter Artin's Axioms)

*Openness of versality* for a category fibred in groupoids over a scheme `S` says that a
finite-type point at which an object is versal has an open neighbourhood on which the object
is versal at every finite-type point. For a morphism of such categories the property is
imposed on every base change to an object of the target.

The property is approached through the smoothness condition on predeformation categories: a
morphism of categories over the big fppf site is *smooth on predeformation categories* when
the induced map at every finite-type field-valued point of the source is smooth. This
condition is stable under composition, which is the main result of the file.

The file also carries the standard counterexample showing that versality need not be open
without further hypotheses. For a field `k` and `Λ = k[s, t]`, consider the functor which is
a singleton on exactly those `Λ`-algebras `A` in which `s`, `t` and finitely many elements
annihilated by `s` generate the unit ideal, and is empty otherwise. Its nonempty values are
characterized geometrically: the closed subset `V(s, t)` of `Spec A` must have a
quasi-compact open neighbourhood on which `s` vanishes.

## Main definitions

* `Deformation.Artin.IsAdmissible` — the finitary condition on a `k[s, t]`-algebra defining
  the counterexample functor, and `Deformation.Artin.artinAxiomsFunctor` that functor.
* `Deformation.Artin.IsArtinAxiomsObject`, `Deformation.Artin.artinAxiomsCategory` — the
  associated local condition on a scheme over `Spec k[s, t]` and the resulting full
  subcategory of the big fppf category.
* `Deformation.Artin.IsSmoothOnPredeformationCategories` — smoothness of the induced map on
  predeformation categories at every finite-type field-valued point.
* `Deformation.Artin.IsOpenVersality`, `Deformation.Artin.IsOpenVersalityMorphism` — openness
  of versality for a category fibred in groupoids, and the relative property for a morphism.

## Main results

* `Deformation.Artin.nonempty_artinAxiomsFunctor_iff_exists_isCompact_open` — the geometric
  criterion for the counterexample functor to take its unique value.
* `Deformation.Artin.isSmoothOnPredeformationCategories_comp` — the composite of two
  morphisms smooth on predeformation categories is smooth on predeformation categories.
* `Deformation.Artin.isSmoothOnPredeformationCategories_twoFibreProductSnd` — smoothness on
  predeformation categories is stable under base change: if `f : 𝒳 ⟶ 𝒴` has it, so does the
  projection `𝒳 ×_𝒴 𝒵 ⟶ 𝒵`.
* `Deformation.Artin.isSmoothOnPredeformationCategories_of_full_of_surjective_obj` — a
  1-morphism over the site which is full and surjective on objects is smooth on predeformation
  categories. This is the transport along an isomorphism of categories over the site that the
  two results below use.
* `Deformation.Artin.isSmoothOnPredeformationCategories_of_natIso` — the condition is invariant
  under a 2-isomorphism of 1-morphisms: two 1-morphisms over the site related by a natural
  isomorphism with vertical components satisfy it together.
* `Deformation.Artin.isSmoothOnPredeformationCategories_twoFibreProductSwap` — the exchange of
  the two factors of a 2-fibre product is smooth on predeformation categories.
* `Deformation.Artin.isSmoothOnPredeformationCategories_twoFibreProductFst` — the previous
  base-change result for the presentation `𝒵 ×_𝒴 𝒳` of the 2-fibre product, whose projection
  to `𝒵` is the first one. That is the ordering in which
  `AlgebraicGeometry.Stack.HasRelativeProperty` presents a base change along a scheme-valued
  point of the target.

## Implementation notes

For openness of versality the open neighbourhood is an open subset of the original scheme,
and versality at its points is tested on the original object. For the relative property, a
target object over `U` determines a functor from schemes over `U` by chosen pullbacks; the
2-fibre product with the source category is fibred in groupoids over schemes over `U`, and
the absolute property is applied to its first projection. The choice of pullbacks is
immaterial by the 2-Yoneda lemma. Local Noetherianness is not needed to formulate either
predicate.

Finite type of `Spec k ⟶ S` is expressed as local finite type together with
quasi-compactness, and the affine open factorization `Spec k ⟶ Spec Λ ⟶ S` is quantified
over, since it is the input to the predeformation-category construction. The composition
result uses the canonical equality showing that the composite functor lies over the base; the
formal deformation argument works for arbitrary categories over the site, so neither local
Noetherianness nor the fibred-in-groupoids conditions enter.

Base change is proved on the *explicit* presentation of a predeformation category, the
category whose objects are literally `Deformation.Artin.DeformationObject`s. Any
`Deformation.Artin.PredeformationConstruction` is fully faithfully and surjectively presented
on it over `𝒞_Λ`, and smoothness of a morphism of categories over `𝒞_Λ` is unchanged by
composing with such a presentation on either side, so the two formulations agree. On the
explicit presentation a lifting problem for the projection of a 2-fibre product is solved by
solving it for `f` and assembling the answer: the comparison arrow that smoothness of `f`
returns lies over an identity, hence is invertible because the target is fibred in groupoids,
and its inverse is the comparison isomorphism of the new object of `𝒳 ×_𝒴 𝒵`. The base
category is embedded faithfully and injectively on objects in `Over S` by `Over.post`, which
is what lets the `IsHomLift` conditions be read in either category.

For the counterexample, `k[s, t]` is modelled by `MvPolynomial (Fin 2) k` with `s = X 0` and
`t = X 1`. The assertion that `(s, t, f₁, …, fₙ)` is the unit ideal is written as an explicit
finite linear combination, and the value of the functor is `PLift` of that proposition, so
proof irrelevance makes it a singleton when the condition holds and empty otherwise. In the
geometric criterion, vanishing of `s` on an open is expressed stalkwise, and the functor
taking its unique value is expressed by `Nonempty` since every value is a subsingleton.

## References

* [Stacks Project, Tag 07XQ](https://stacks.math.columbia.edu/tag/07XQ)
* [Stacks Project, Tag 07XR](https://stacks.math.columbia.edu/tag/07XR)
* [Stacks Project, Tag 07XS](https://stacks.math.columbia.edu/tag/07XS)
* [Stacks Project, Tag 07XU](https://stacks.math.columbia.edu/tag/07XU)
* [Stacks Project, Tag 07XV](https://stacks.math.columbia.edu/tag/07XV)
-/
