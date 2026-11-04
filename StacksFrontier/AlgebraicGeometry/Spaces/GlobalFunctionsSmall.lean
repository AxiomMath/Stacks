module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FaithfullyFlatSections
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme

/-!
# The ring of global functions of an algebraic space is small

A global regular function on an algebraic space over `S` is a compatible family of regular
functions on its étale scheme charts, so the type `AlgebraicGeometry.Space.globalFunctions` of
such functions is a subtype of a product indexed by the charts and therefore lives, as written,
in `Type (u + 1)`. It is nevertheless `u`-small: restriction to a single *surjective* étale
chart is injective, because a global function is determined by its values on any chart that
covers the space, and the values on one chart form a `u`-type.

This is what makes the spectrum of the ring of global functions available: every construction
that forms `Spec Γ(X, 𝒪_X)` needs the ring to be a `u`-type first.

## Main results

* `AlgebraicGeometry.Space.globalFunctionsChartRestriction_injective`: restriction of global
  functions to the chart carrying a surjective étale atlas is injective.
* `AlgebraicGeometry.Space.small_globalFunctions`: the ring of global functions of an algebraic
  space over `S` is `u`-small.

## Implementation notes

*Why a surjective chart suffices.* Two global functions agreeing on the atlas `U` agree on
every chart `V`: the fibre product `W = V ×_X U` is an étale chart as well, its projection to
`U` carries the agreement to `W`, and its projection to `V` is a surjective flat morphism of
schemes, hence injective on global sections by
`AlgebraicGeometry.Scheme.Hom.appTop_injective_of_flat_of_surjective`. Surjectivity and
étaleness of that projection are the two base-change clauses of
`AlgebraicGeometry.Space.AtlasKernelPairData`, read at the chart `V`.

*The chart `W`.* It is produced by the relative representability of the atlas, which is the
first component of the étaleness clause, rather than as a pullback in the site: the
representing object comes with the two projections and the Cartesian square, which is exactly
what the two restrictions are compared through.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Restriction of global functions to a surjective étale chart is injective.** A global
function on an algebraic space is determined by its values on the chart carrying a surjective
étale atlas: on any other chart `V` the fibre product `W = V ×_X U` is again a chart, the two
functions agree there because they agree on `U`, and `W ⟶ V` is a surjective flat morphism of
schemes and hence injective on global sections. -/
theorem globalFunctionsChartRestriction_injective (X : AlgebraicSpaces B S hS)
    (D : AtlasKernelPairData B S hS X) :
    Function.Injective (globalFunctionsChartRestriction B S hS X
      (chartFromEtaleHom B S hS X D.U D.f D.etale)) := by
  intro a b hab
  apply Subtype.ext
  funext V
  let hrep := D.etale.1
  let W := hrep.pullback V.unop.1.hom
  let i := hrep.fst' V.unop.1.hom
  let j := hrep.snd V.unop.1.hom
  let hp := hrep.isPullback' V.unop.1.hom
  have hjEtale := D.etale.property V.unop.1.hom (yoneda.map i) j hp
  let WC := chartFromEtaleHom B S hS X W (yoneda.map j ≫ V.unop.1.hom)
    (chart_preimage_etale B S hS X V.unop.1.hom V.unop.2 j hjEtale)
  let AC := chartFromEtaleHom B S hS X D.U D.f D.etale
  let iC : WC ⟶ AC := ObjectProperty.homMk (CostructuredArrow.homMk i hp.w)
  let jC : WC ⟶ V.unop := ObjectProperty.homMk (CostructuredArrow.homMk j rfl)
  have hi := globalFunctionsChartRestriction_naturality B S hS X iC
  have hj := globalFunctionsChartRestriction_naturality B S hS X jC
  have hw : globalFunctionsChartRestriction B S hS X WC a =
      globalFunctionsChartRestriction B S hS X WC b := by
    rw [← congrFun hi a, ← congrFun hi b]
    exact congrArg (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map i))) hab
  have _ : Surjective ((BigFppfOver.toScheme B S hS).map j) :=
    D.surjective.property V.unop.1.hom (yoneda.map i) j hp
  have _ : Etale ((BigFppfOver.toScheme B S hS).map j) := hjEtale
  exact Scheme.Hom.appTop_injective_of_flat_of_surjective
    ((BigFppfOver.toScheme B S hS).map j) ((congrFun hj a).trans (hw.trans (congrFun hj b).symm))

/-- **The ring of global functions of an algebraic space over `S` is `u`-small.** Restriction to
the chart carrying a chosen surjective étale atlas is an injection into the ring of global
regular functions of a scheme, which is a `u`-type. -/
instance small_globalFunctions (X : AlgebraicSpaces B S hS) :
    Small.{u} (globalFunctions B S hS X.1) :=
  small_of_injective
    (globalFunctionsChartRestriction_injective B S hS X (chosenAtlasKernelPair B S hS X))

end AlgebraicGeometry.Space

end
