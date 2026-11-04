module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction

/-!
# The comparison of the modules of a represented algebraic space is compatible with pullback

Let `α : W ⟶ V` be a morphism of the big fppf site over `S`, with underlying morphism of
schemes `T_α`, and let `G` be a quasi-coherent `𝒪`-module on the small étale site of the
algebraic space `h_V` represented by `V`. The comparison
`AlgebraicGeometry.Space.representedZariskiRestriction` of the modules of a represented
algebraic space with the sheaves of modules on the representing scheme carries the inverse
image of `G` along `h_α` to the Zariski inverse image along `T_α` of the comparison of `G`.

## Main results

* `AlgebraicGeometry.Space.representedZariskiRestrictionBaseChangeIso`: that compatibility.
* `AlgebraicGeometry.Space.isQuasicoherent_representedZariskiRestriction`: the comparison of a
  quasi-coherent module is quasi-coherent, so the compatibility may be iterated.

## Implementation notes

The comparison is the restriction to the identity chart of a represented algebraic space, so
this is `AlgebraicGeometry.Space.restrictToChartBaseChangeIso` — the base change of Stacks 03M0
along Stacks 03LW — read at the identity charts of `h_W` and `h_V`, joined by `α` itself. The
commutation of the square of charts is the commutation of `h_α` with two identities.

This is the functorial half of the comparison of `AlgebraicGeometry.Scheme.Modules` of a scheme
of the site with `AlgebraicGeometry.Space.Modules` of the algebraic space it represents. The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiRestriction.lean` asked for exactly
this identification and recorded it as unavailable; it became available with
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, which identifies the two parallel chart
restrictions and transports the represented base change across.

Quasi-coherence of `G` is used, once, by that base change; nothing else is assumed, and in
particular `α` is an arbitrary morphism of the site, not an étale or flat one.

The module universe is the universe `u` of the structure rings, which is where
`AlgebraicGeometry.Scheme.Modules` of the representing scheme and
`AlgebraicGeometry.Space.representedZariskiRestriction` both live.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison of the modules of a represented algebraic space with the modules of the
representing scheme is compatible with inverse images.**  For a morphism `α : W ⟶ V` of the big
fppf site and a quasi-coherent `𝒪`-module `G` on the small étale site of `h_V`, the Zariski
inverse image along the morphism of representing schemes of the comparison of `G` is the
comparison of the inverse image of `G` along `h_α`.

This is `AlgebraicGeometry.Space.restrictToChartBaseChangeIso` at the identity charts of the
two represented algebraic spaces. -/
def representedZariskiRestrictionBaseChangeIso {W V : BigFppfOver B S hS} (α : W ⟶ V)
    (G : Modules.{u, u} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V))
    (hG : G.IsQuasicoherentOnSite) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map α)).obj
        (representedZariskiRestriction B S hS V (isAlgebraicSpace_yoneda B S hS V) G) ≅
      representedZariskiRestriction B S hS W (isAlgebraicSpace_yoneda B S hS W)
        ((modulePullback B S hS (schemeSpaceMap α)).obj G) :=
  restrictToChartBaseChangeIso B S hS (X := schemeSpace W) (Z := schemeSpace V)
    (schemeSpaceMap α) G hG (selfChart B S hS V) (selfChart B S hS W) α
    ((Category.comp_id (yoneda.map α)).trans (Category.id_comp (yoneda.map α)).symm)

/-- The comparison of a quasi-coherent `𝒪`-module on a represented algebraic space is a
quasi-coherent sheaf of modules on the representing scheme.

This is `AlgebraicGeometry.Space.isQuasicoherent_restrictToChart` at the identity chart. -/
theorem isQuasicoherent_representedZariskiRestriction (U : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hM : M.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent
      (representedZariskiRestriction B S hS U (isAlgebraicSpace_yoneda B S hS U) M) :=
  isQuasicoherent_restrictToChart B S hS (schemeSpace U) M hM (selfChart B S hS U)

end AlgebraicGeometry.Space

end
