module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact.DescentGluing
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact.SplittingExactness
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact.Surjectivity

/-!
# The Picard sequence of a morphism with a section

Let `f : X ⟶ S` be a morphism of a big fppf site which admits a section `σ : S ⟶ X`. Every
`S`-scheme `T` of the site then has a section `σ_T : T ⟶ X_T` of the projection `X_T ⟶ T`, the
`Stacks.PicardFunctor.baseChangeSection` of the construction of the Picard functor, and pullback
along it is a left inverse of pullback along the projection. So the first arrow of

`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T) ⟶ 0`

is split injective, with splitting `σ_T^*`. Independently of any section, the composite of the
first two arrows is zero, because an invertible module on `T` is trivial on a Zariski covering
of `T` and the Picard functor is an fppf sheaf.

If moreover the comparison map `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` is an isomorphism for every `T`, the
sequence is exact at `Pic(X_T)` and at `Pic_{X/S}(T)` as well, so it is a split exact sequence.
Both rest on the same mechanism. A trivialisation of an invertible module on `X_T` along the
induced section `σ_T` normalises the trivialisations on the base changes of the members of a
covering family of `T`; the overlap of two members is again a base change, so it carries an
induced section, and the normalised trivialisations therefore agree there. Hence a class killed
by `σ_T^*` and killed on a covering family is zero, and the normalised local classes of a
section of `Pic_{X/S}(T)` form a quasi-coherent descent datum for the base-changed covering
family, which is an fpqc covering of `X_T`.

## Main results

* `Stacks.PicardFunctor.schemePullbackClass_baseChangeSection_baseChangeProj` — pullback along
  the induced section is a left inverse of pullback along the projection.
* `Stacks.PicardFunctor.injective_schemePullbackClass_baseChangeProj_of_section` — hence
  pullback from `Pic(T)` is injective, with no hypothesis on structure sheaves.
* `Stacks.PicardFunctor.toPicardFunctorHom_schemePullbackClass_baseChangeProj` — the composite
  `Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T)` is zero, so the image of the first arrow is contained in
  the kernel of the second.
* `Stacks.PicardFunctor.eq_zero_of_schemePullbackClass_baseChangeSection_eq_zero` — a class
  killed by `σ_T^*` and killed on a covering family of `T` is zero.
* `Stacks.PicardFunctor.exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom` — the
  image of pullback from `Pic(T)` is the kernel of the map to the Picard functor.
* `Stacks.PicardFunctor.surjective_toPicardFunctorHom` — the map to the Picard functor is
  surjective.
* `Stacks.Picard.nonempty_iso_of_pullHom_hom_eq` — the gluing principle behind the first of
  these: a family of isomorphisms of the pullbacks of two modules along a family of morphisms
  which agree after every further pullback exhibits the two modules as isomorphic.
* `Stacks.Picard.isInvertible_of_pullback_fpqcCover` — invertibility descends along an fpqc
  covering, which is what makes the module produced by descent invertible.

## References

* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)

This file only re-exports its parts: `DescentGluing`, `SplittingExactness` and `Surjectivity`.
-/
