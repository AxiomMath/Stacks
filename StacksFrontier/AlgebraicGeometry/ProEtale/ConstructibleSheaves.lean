module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Constructible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.Stratification
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructible sheaves of modules on the small pro-étale site

Let `Λ` be a Noetherian ring and `X` a scheme. A sheaf of `Λ`-modules on the small pro-étale
site of `X` is *constructible* when every affine open of `X` admits a finite decomposition into
constructible locally closed subschemes on which the inverse image of the sheaf is locally
constant of finite type.

## Main definitions

* `AlgebraicGeometry.ProEtale.IsConstructibleModuleSheaf'` — constructibility of a sheaf of
  modules on the small pro-étale site, with no instance hypotheses. The stratifications it
  quantifies over are `AlgebraicGeometry.Scheme.ConstructibleStratification`.

## Implementation notes

Constructibility of a stratum is constructibility of its image inside the ambient open, so the
condition is the one of the source: the strata are constructible *in* `U`. Finite type together
with local constancy is `Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf`, the
condition that the sheaf become a constant sheaf on a finitely generated module after
restriction along a covering family; this is the same predicate the étale theory of Stacks 03RW
uses, now on the pro-étale topology.

Restriction to a stratum is inverse image along `AlgebraicGeometry.Scheme.proetaleBaseChange`,
constructed as a left Kan extension followed by sheafification. The module sections live in a
universe `max (u + 1) v w` containing the site and the coefficients and otherwise arbitrary; at
every such universe sheafification and the left Kan extensions exist unconditionally, so the
definition carries no instance hypotheses: the `HasWeakSheafify` and `IsRightAdjoint`
assumptions that a form with a completely free sections universe would need are supplied by
`AlgebraicGeometry.hasSheafify_moduleCat`, which is itself universe-polymorphic.

The site is Mathlib's `AlgebraicGeometry.Scheme.ProEt` with no size cutoff, so neither a choice
of big pro-étale site nor a containment witness enters the statement.

## References

* [Stacks Project, Tag 09AJ](https://stacks.math.columbia.edu/tag/09AJ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

namespace ProEtale

/-- Inverse image of a pro-étale sheaf of modules along a morphism of schemes: the left Kan
extension of its restriction along pro-étale base change, sheafified. -/
public def proetaleModuleInverseImage {Y X : Scheme.{u}} (g : Y ⟶ X) (Λ : Type v) [CommRing Λ] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ) ⥤
      Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{max (u + 1) v w} Λ) :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.proetaleBaseChange g)
    (ModuleCat.{max (u + 1) v w} Λ) (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)

/-- **Stacks 09AJ.** A sheaf of `Λ`-modules on the small pro-étale site of `X` is
*constructible* when every affine open `U` of `X` admits a finite decomposition into
constructible locally closed subschemes on each of which the inverse image of the sheaf is
locally constant of finite type.

This is reducible, so a client can use the witnesses of the stratification directly.

The primed name records the weaker hypotheses: pinning the sections universe to
`max (u + 1) v w` makes sheafification and the left Kan extensions exist unconditionally, so
this form needs none of the `HasWeakSheafify` and `IsRightAdjoint` assumptions that
`AlgebraicGeometry.ProEtale.IsConstructibleModuleSheaf` of
`StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.Defs` carries, at the cost of leaving
that universe no longer free. The two are stated with different local-constancy predicates —
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf` here against
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant` there — and identifying them is not done. -/
@[stacks 09AJ]
public abbrev IsConstructibleModuleSheaf' (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [IsNoetherianRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) : Prop :=
  ∀ U : X.affineOpens, ∃ s : Scheme.ConstructibleStratification X U.1, ∀ i,
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology (s.piece i)) Λ
      ((proetaleModuleInverseImage.{u, v, w} (s.inclusion i) Λ).obj F)

end ProEtale

end AlgebraicGeometry

end
