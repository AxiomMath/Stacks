module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom.HomSystem
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom.QuasiCompactInduction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom.RestrictToSmaller

/-!
# Morphisms in the derived category along a relative descent situation

In a relative descent situation — a directed inverse limit `S = lim Sᵢ` of
quasi-compact quasi-separated schemes with affine transition maps, and a flat morphism of finite
presentation `X₀ ⟶ S₀` with base changes `Xᵢ` and `X` — the derived pullbacks of two objects
`K₀, L₀` of `D(𝒪_{X₀})` form a system of morphism sets `Hom_{D(𝒪_{Xᵢ})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀)`
over `Hom_{D(𝒪_X)}(Lf₀^*K₀, Lf₀^*L₀)`. This file constructs the transition maps and the
comparison maps of that system and proves that they are compatible.

## Main definitions

* `Stacks.DerivedPullback.factorIso` and `Stacks.DerivedPullback.factorHom`: for a factorisation
  `k = f ≫ g` of morphisms of ringed spaces, the comparison `Lg^* ⋙ Lf^* ≅ Lk^*` and the induced
  map `Hom(Lg^*K, Lg^*L) ⟶ Hom(Lk^*K, Lk^*L)`; `schemeFactorIso` and `schemeFactorHom` are the
  same for morphisms of schemes.
* `AlgebraicGeometry.RelativeDescentSituation.homTransition`: the transition map
  `Hom_{D(𝒪_{Xᵢ})}(Kᵢ, Lᵢ) ⟶ Hom_{D(𝒪_{Xⱼ})}(Kⱼ, Lⱼ)` for `i ≤ j`.
* `AlgebraicGeometry.RelativeDescentSituation.homComparison`: the comparison map
  `Hom_{D(𝒪_{Xᵢ})}(Kᵢ, Lᵢ) ⟶ Hom_{D(𝒪_X)}(K, L)`.
* `AlgebraicGeometry.RelativeDescentSituation.HomDescent`: the statement that
  `colim_i Hom_{D(𝒪_{Xᵢ})}(Kᵢ, Lᵢ) ⟶ Hom_{D(𝒪_X)}(K, L)` is bijective.
* `AlgebraicGeometry.RelativeDescentSituation.homFunctor` and
  `AlgebraicGeometry.RelativeDescentSituation.homCocone`: the same system of morphism sets as a
  functor `D.LaterIndex ⥤ Type (u + 1)`, and the cocone on it given by the comparison maps.
* `AlgebraicGeometry.RelativeDescentSituation.restrict`: the relative descent situation restricted
  to a quasi-compact open `U₀ ⊆ X₀`, together with the inclusions
  `AlgebraicGeometry.RelativeDescentSituation.restrictToAmbient` of `Uᵢ` into `Xᵢ` and
  `AlgebraicGeometry.RelativeDescentSituation.restrictToAmbientLimit` of `U` into `X`.
* `Stacks.DerivedPullback.factorSquareIso` and `Stacks.DerivedPullback.factorSquareHom`: for a
  commutative square `r ≫ g = e ≫ ι` of morphisms of ringed spaces, the comparison
  `Lι^* ⋙ Le^* ≅ Lg^* ⋙ Lr^*` and the induced map `Hom(Lg^*K, Lg^*L) ⟶ Hom(Le^*Lι^*K, Le^*Lι^*L)`;
  `schemeFactorSquareIso` and `schemeFactorSquareHom` are the same for morphisms of schemes.
* `AlgebraicGeometry.RelativeDescentSituation.restrictDerivedPullbackIso` and
  `restrictDerivedPullbackLimitIso`: the derived pullbacks of the restricted situation compared
  with the restrictions of the derived pullbacks, at a stage and at the limit.
* `AlgebraicGeometry.RelativeDescentSituation.homRestrictToOpen`,
  `homRestrictToOpenLimit` and `homFunctorRestrictToOpen`: restriction to `U₀` on derived
  morphism sets at a stage and at the limit, and the resulting morphism of systems.
* `AlgebraicGeometry.RelativeDescentSituation.RestrictHomDescent`: `HomDescent` for the restricted
  situation, as a predicate on the quasi-compact open `U₀`.
* `Stacks.DerivedPullback.factorTowerHom`: for a commutative square `r ≫ g ≫ p = e ≫ q` of
  morphisms of ringed spaces whose two edges to the base are given as composites, the induced map
  `Hom(Lg^*Lp^*K, Lg^*Lp^*L) ⟶ Hom(Le^*Lq^*K, Le^*Lq^*L)`; `schemeFactorTowerHom` is the same for
  morphisms of schemes.
* `AlgebraicGeometry.RelativeDescentSituation.restrictToLarger` and `restrictToLargerLimit`: for
  quasi-compact opens `V₀ ≤ U₀` of `X₀`, the inclusions `Vᵢ ⟶ Uᵢ` and `V ⟶ U` of the restricted
  situations, the base changes of the inclusion `V₀ ⟶ U₀`.
* `AlgebraicGeometry.RelativeDescentSituation.homRestrictToSmaller`, `homRestrictToSmallerLimit`
  and `homFunctorRestrictToSmaller`: restriction from `U₀` to `V₀` on derived morphism sets at a
  stage and at the limit, and the resulting morphism of systems.
* `AlgebraicGeometry.RelativeDescentSituation.restrictTopToAmbientInv` and
  `restrictTopToAmbientLimitInv`: the inverses of the inclusions `Uᵢ ⟶ Xᵢ` and `U ⟶ X` of the
  situation restricted to `U₀ = X₀`, the base changes of the inverse of `X₀ ≅ ⊤`.

## Main results

* `Stacks.DerivedPullback.factorHom_comp`: the cocycle identity for `factorHom` along a
  factorisation `c = p ≫ t ≫ a`.
* `Stacks.DerivedPullback.factorHom_id` and `schemeFactorHom_id`: a factorisation through an
  identity induces the identity map on derived Hom.
* `AlgebraicGeometry.RelativeDescentSituation.homTransition_refl`,
  `homComparison_homTransition` and `homTransition_homTransition`: the transition map at a stage
  to itself is the identity, the transition maps compose, and the comparison maps are compatible
  with them.
* `AlgebraicGeometry.RelativeDescentSituation.transition_comp_toFixedStage`,
  `projection_comp_toFixedStage`, `transition_refl`, `transition_comp_transition`,
  `projection_comp_transition`: the factorisations satisfied by the transition, projection and
  structure morphisms.
* `AlgebraicGeometry.RelativeDescentSituation.nonempty_laterIndex` and `isDirected_laterIndex`:
  the stages at or beyond the fixed stage are nonempty and directed, hence filtered.
* `AlgebraicGeometry.RelativeDescentSituation.homDescent_iff_nonempty_isColimit`: `HomDescent`
  holds exactly when `homCocone` is a colimit cocone.
* `AlgebraicGeometry.RelativeDescentSituation.opensRange_restrictToAmbient` and
  `opensRange_restrictToAmbientLimit`: the stages and the limit of the restricted situation are
  the preimages of `U₀` in `Xᵢ` and in `X`.
* `AlgebraicGeometry.RelativeDescentSituation.restrictToAmbient_transition` and
  `restrictToAmbient_projection`: those inclusions are compatible with the transition morphisms
  and with the projections from the limit.
* `Stacks.DerivedPullback.factorEquiv_factorHom` and
  `Stacks.DerivedPullback.factorHom_factorSquareHom`: the compatibility of `factorEquiv` with
  `factorHom`, and the compatibility of the square comparisons with factorisations of the
  horizontal edges.
* `AlgebraicGeometry.RelativeDescentSituation.homTransition_homRestrictToOpen` and
  `homComparison_homRestrictToOpen`: restriction to `U₀` commutes with the transition maps and
  with the comparison maps, so it is a map of cocones on the systems of derived morphism sets.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomDescent_iff_nonempty_isColimit`:
  `RestrictHomDescent` is the colimit statement for the restricted situation.
* `Stacks.DerivedPullback.factorTowerHom_comp`, `factorTowerHom_id`,
  `factorHom_factorTowerHom` and `factorTowerHom_factorSquareHom`: the maps attached to squares
  with factored horizontal edges compose, are the identity when the vertical edge is an identity,
  commute with factorisations of the vertical edges, and compose with the maps attached to a
  square whose upper edge is unfactored.
* `AlgebraicGeometry.RelativeDescentSituation.opensRange_restrictToLarger` and
  `opensRange_restrictToLargerLimit`: the smaller restricted situation is the preimage of `V₀` in
  the larger one.
* `AlgebraicGeometry.RelativeDescentSituation.restrictToLarger_transition` and
  `restrictToLarger_projection`: the inclusions `Vᵢ ⟶ Uᵢ` are compatible with the transition
  morphisms and with the projections from the limit.
* `AlgebraicGeometry.RelativeDescentSituation.homTransition_homRestrictToSmaller` and
  `homComparison_homRestrictToSmaller`: restriction from `U₀` to `V₀` commutes with the transition
  maps and with the comparison maps, so it is a map of cocones.
* `AlgebraicGeometry.RelativeDescentSituation.homRestrictToSmaller_refl` and
  `homRestrictToSmaller_homRestrictToSmaller`: restriction along `U₀ ≤ U₀` is the identity and
  restriction along `W₀ ≤ V₀ ≤ U₀` composes.
* `AlgebraicGeometry.RelativeDescentSituation.homRestrictToSmaller_homRestrictToOpen` and
  `homRestrictToSmallerLimit_homRestrictToOpenLimit`: restriction to `U₀` followed by restriction
  to `V₀` is restriction to `V₀`.
* `Stacks.DerivedPullback.isEquivalence_derivedPullback` and `bijective_derivedPullback_map`:
  derived pullback along an isomorphism of ringed spaces is an equivalence, hence bijective on
  derived morphism sets; `bijective_schemeFactorSquareHom` is the resulting bijectivity of the
  map attached to a square of schemes whose vertical edge is an isomorphism.
* `AlgebraicGeometry.RelativeDescentSituation.bijective_homRestrictToOpen_top`,
  `bijective_homRestrictToOpenLimit_top` and `homDescent_of_restrictHomDescent_top`: restriction
  to `U₀ = X₀` is bijective at each stage and at the limit, so `HomDescent` follows from
  `RestrictHomDescent` there.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomDescent_of_isAffineOpen_of_sup` and
  `homDescent_of_isAffineOpen_of_sup`: `RestrictHomDescent` on every quasi-compact open of `X₀`,
  and `HomDescent`, follow from `RestrictHomDescent` for the affine opens of `X₀` together with
  its stability under the Mayer--Vietoris union step `U₀, V₀, U₀ ⊓ V₀ ⊢ U₀ ⊔ V₀`.

The content is split into the parts `HomSystem`, `RestrictToSmaller` and `QuasiCompactInduction`.

## References

* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/
