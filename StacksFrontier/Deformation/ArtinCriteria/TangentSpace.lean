module

public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace.SixTermTransfer
public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace.SiteComparison
public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace.SixTermExact

/-!
# Tangent spaces of a 2-fibre product of categories fibred in groupoids

Let `Φ : 𝒳 ⟶ 𝒴` and `Ψ : 𝒵 ⟶ 𝒴` be `1`-morphisms of categories fibred in groupoids over the
big fppf site of a scheme `S`, all three satisfying the Rim–Schlessinger condition (RS), and let
`w₀` be an object of `𝒲 = 𝒳 ×_𝒴 𝒵` over a field `k` of finite type over `S`, with induced
objects `x₀`, `y₀ = Φ(x₀)`, `z₀` of `𝒳`, `𝒴`, `𝒵`. The tangent spaces of the four associated
predeformation categories then sit in an exact sequence

`T𝓕_{𝒲,k,w₀} ⟶ T𝓕_{𝒳,k,x₀} ⊕ T𝓕_{𝒵,k,z₀} ⟶ T𝓕_{𝒴,k,y₀}`

of `k`-vector spaces. This is the tangent row of the six-term exact sequence of Stacks 07X2.

## Main results

* `Deformation.Artin.sixTermExact_twoFibreProduct` — the full six-term exact sequence of
  Stacks 07X2, with all five of its exactness/injectivity claims proved.
* `Deformation.Artin.exact_tangentRow_twoFibreProduct` — the tangent row and its exactness at
  the middle term, kept as a standalone statement alongside the combined theorem above.
* `Deformation.Artin.isEquivalence_liftPost` — forming the 2-fibre product over the chosen big
  fppf site and forming it over all schemes over `S` give equivalent categories. This is what
  makes Stacks 07WL applicable to a point of a 2-fibre product.
* `Deformation.isEquivalence_lift_congr` — whether the mediating `1`-morphism of
  `CategoryTheory.TwoFibreProductOver.lift` is an equivalence does not depend on which
  (propositionally equal) functor presents each leg of the square; this is what lets the
  square of predeformation categories, whose legs are literally `mF.toFunctor ⋙ D𝒴.projection`
  and `data.rightFunctor ⋙ D𝒴.projection` rather than the separately-named `D𝒳.projection` and
  `D𝒵.projection`, inherit the equivalence Stacks 07WL supplies for the latter presentation.
* `Deformation.injective_infProjPairOfLift`, `Deformation.exact_infProjPairOfLift`,
  `Deformation.exact_infLegDiff_infBoundaryLinearMapOfLift`,
  `Deformation.exact_infBoundaryLinearMapOfLift_tangentProjPairOfLift` and
  `Deformation.exact_tangentPairOfLift_tangentLegDiffOfEq` — each of the five
  exactness/injectivity claims of Stacks 06L5's abstract six-term sequence, transported along
  an arbitrary mediating `CategoryTheory.TwoFibreProductOver.lift`-equivalence rather than only
  along the identity on the literal 2-fibre product.
* `Deformation.tangentMapAt_comp` and `Deformation.tangentMapAt_surjective_of_essSurj` — the
  functoriality of the map induced on tangent modules, and its surjectivity for a `1`-morphism
  that is essentially surjective.

## Implementation notes

*What is covered.* The source states a six-term exact sequence

`0 ⟶ Inf(𝓕_𝒲) ⟶ Inf(𝓕_𝒳) ⊕ Inf(𝓕_𝒵) ⟶ Inf(𝓕_𝒴) ⟶ T𝓕_𝒲 ⟶ T𝓕_𝒳 ⊕ T𝓕_𝒵 ⟶ T𝓕_𝒴.`

`Deformation.Artin.sixTermExact_twoFibreProduct` proves the whole sequence, with all five
exactness/injectivity claims. The square of predeformation categories is identified with the
literal 2-fibre product `CategoryTheory.TwoFibreProductOver` by the equivalence Stacks 07WL
supplies (`Deformation.Artin.fibreProductOfPredeformationCategoriesOfEssSurj`), and each of the
five clauses of the abstract six-term sequence proved for the literal 2-fibre product
(Stacks 06L5, part (2), `Deformation.SixTerm.twoFibreProduct_sixTermExact`) is transported along
that equivalence by the corresponding `...OfLift` lemma above. The standalone
`Deformation.Artin.exact_tangentRow_twoFibreProduct`, covering only the tangent row's exactness
at `T𝓕_𝒳 ⊕ T𝓕_𝒵`, predates the combined theorem and is kept for the clients that already use it;
it is a direct instance of the fifth conjunct of the combined theorem.

*Why the second leg is transported.* The two routes from `𝒲` to `𝒴` agree only up to the
comparison isomorphism `ψ(w₀) : Φ(x₀) ≅ Ψ(z₀)`, so the basepoint in `𝒴` is taken to be `Φ(x₀)`
and the second leg of the square of predeformation categories is the functor induced by `Ψ`
*transported along* `ψ(w₀)`. That transported functor is the `rightFunctor` field of the data
Stacks 07WL supplies, and it is the one appearing in the difference below.

*The two 2-fibre products.* The predeformation category of a point of a category fibred in
groupoids over the big fppf site is formed over the slice of *all* schemes over `S`, so the
square Stacks 07WL is applied to has its base the structure functor of `𝒳 ×_𝒴 𝒵` composed with
the inclusion of the site. That composite is not fibred in groupoids over all schemes over `S`
— the site does not contain every scheme — so the fibredness hypothesis of Stacks 07WL cannot be
met here. It is used there only to make the essential surjectivity of the ambient comparison
functor strict on the base, and for the 2-fibre product that surjectivity holds on the nose:
the base object of an object of the 2-fibre product formed over all schemes over `S` is the
image of the base of its `𝒳`-component, hence comes from the site, and the remaining data is
reflected because the inclusion of the site is fully faithful and injective on objects. The form
of Stacks 07WL taking that surjectivity directly as a hypothesis is
`Deformation.Artin.fibreProductOfPredeformationCategoriesOfEssSurj`.

*How the exactness transports.* Exactness of the tangent row is proved in the library for
`CategoryTheory.TwoFibreProductOver` itself. The square of predeformation categories is
identified with that 2-fibre product by a `1`-morphism which Stacks 07WL asserts to be an
equivalence; the pair of the maps induced by the two projections of the square factors through
the map that equivalence induces on tangent modules, and that map is surjective because the
equivalence is essentially surjective on each fibre. Exactness is inherited by precomposition
with a surjection, so no compatibility beyond that factorization is needed.

*Hypotheses.* Local Noetherianity of `S` is not assumed: the explicit finite-type and
quasi-compactness hypotheses on the field-valued point are what the predeformation machinery
consumes, exactly as in `Deformation.Artin.isDeformationCategory_predeformationCategory`.

## References

* [Stacks Project, Tag 07X2](https://stacks.math.columbia.edu/tag/07X2)
* [Stacks Project, Tag 07WL](https://stacks.math.columbia.edu/tag/07WL)
* [Stacks Project, Tag 07WR](https://stacks.math.columbia.edu/tag/07WR)
* [Stacks Project, Tag 07WU](https://stacks.math.columbia.edu/tag/07WU)
* [Stacks Project, Tag 06L5](https://stacks.math.columbia.edu/tag/06L5)
-/
