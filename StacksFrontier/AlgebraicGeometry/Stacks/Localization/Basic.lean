module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.Localization.InheritedTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Localization
public import StacksCore.Tactic.StacksAttribute

/-!
# Localizing a category fibred in groupoids over schemes at an object

Let `p : 𝒳 ⥤ (Sch/S)_fppf` be a category fibred in groupoids, let `τ` be one of the Zariski,
étale, smooth, syntomic and fppf topologies, and let `x` be an object of `𝒳` lying over the
scheme `U = p x`. Then `p` induces an equivalence of sites `𝒳_τ/x ⥤ (Sch/U)_τ`: the functor
`Over.post` of the composite of `p` with the forgetful functor to the chosen category of schemes
is an equivalence of categories, and the topology it induces from the localization of the big
`τ`-topology at `U` is the localization at `x` of the topology `𝒳` inherits from `(Sch/S)_τ`.

## Main results

* `AlgebraicGeometry.BigFppfOver.overPost_isEquivalence`: the induced functor `𝒳/x ⥤ Sch/U` is
  an equivalence of categories.
* `AlgebraicGeometry.BigFppfOver.overPost_inducedTopology`: that functor identifies the two
  topologies, so the equivalence of categories is an equivalence of sites.

## Implementation notes

Tag 06W0 is registered in
`StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization`, on
`AlgebraicGeometry.Stack.isEquivalence_overPost` and
`AlgebraicGeometry.Stack.inducedTopology_overPost`, which state the same two results for an
arbitrary topology on the chosen category of schemes rather than for one of the five named
ones. The two results below are the named-topology case and are what this file's consumers
refer to.

The canonical functor is `CategoryTheory.Over.post` applied to the composite of `p` with the
forgetful functor from the big fppf category over `S` to the chosen category of schemes; its
target is the slice over `(p x).left`, with no `eqToHom` transport in the statement. Stating the
identification of topologies as an equality of the topology *induced by this functor* with the
localized inherited topology says that this particular functor, not merely some equivalence, is
an equivalence of sites.

Both results delegate to the general ones. At a `SiteKind` the two spellings of the associated
topology agree definitionally: `AlgebraicGeometry.BigFppfOver.associatedTopology` unfolds to
`p.inheritedTopology (baseOverTopology B S hS τ)` and `baseOverTopology` to
`(B.baseTopology τ).over (B.obj hS)`, which is `AlgebraicGeometry.Stack.associatedTopology` at
`B.baseTopology τ`. So the named-topology case is the general statement instantiated, and needs
no bridging lemma.

## References

* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.BigFppfOver


/-- **Stacks 06W0**, the equivalence of categories: for a category `𝒳` fibred in groupoids over
the big fppf category of schemes over `S` and an object `x` of `𝒳`, the canonical functor
`𝒳/x ⥤ Sch/p x` induced by the structure functor is an equivalence of categories. -/
public theorem overPost_isEquivalence (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (x : 𝒳) :
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
  Stack.isEquivalence_overPost B S hS p hp x

/-- **Stacks 06W0**, the equivalence of sites: the canonical localization functor
`𝒳/x ⥤ Sch/p x` carries the localization at `p x` of any of the five big topologies on the
chosen category of schemes to the localization at `x` of the topology `𝒳` inherits from the
corresponding big site over `S`. -/
public theorem overPost_inducedTopology (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (τ : SiteKind) (x : 𝒳) :
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inducedTopology
        ((B.baseTopology τ).over (p.obj x).left) =
      (associatedTopology B S hS p τ).over x :=
  Stack.inducedTopology_overPost B S hS p hp (B.baseTopology τ) x

end AlgebraicGeometry.BigFppfOver

end
