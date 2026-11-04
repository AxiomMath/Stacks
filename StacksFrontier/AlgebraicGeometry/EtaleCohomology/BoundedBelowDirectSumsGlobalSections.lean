module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedBelowDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectSumsOfEtaleCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# Derived global sections and direct sums bounded below

[Stacks, Tag 0GIS] says that for a quasi-compact and quasi-separated scheme `X` and a family
`K_i`, `i ∈ I`, of objects of `D(X_étale)` admitting a common lower bound `a` — that is,
`H^n(K_i) = 0` for `n < a` and all `i ∈ I` — one has
`RΓ(X, ⨁_i K_i) = ⨁_i RΓ(X, K_i)`.

This is the global sections case of the argument of
`Stacks.EtaleCohomology.preservesColimit_rightDerivedFunctorPlus_of_isGE`, the bounded below
direct sum statement for an arbitrary left exact functor out of a Grothendieck abelian category
with enough injectives, which is what the sibling tag [Stacks, Tag 0GIW] is read through: resolve
each `K_i` by a complex of injectives in degrees `≥ a` ([Stacks, Tag 07D9]), note that the
termwise direct sum of those resolutions is `Γ`-acyclic because each `H^q_étale(X, -)` commutes
with the direct sum, and conclude by Leray's acyclicity lemma, [Stacks, Tag 015E].

## Main results

* `Stacks.EtaleCohomology.preservesColimit_rightDerivedFunctorPlus_Γ_smallEtale_of_isGE` —
  **the tag**.

## Implementation notes

*Nothing is assumed.* Unlike the morphism version [Stacks, Tag 0GIW], whose input that each
`R^q f_*` commutes with direct sums ([Stacks, Tag 09Z1]) is carried as a hypothesis, the input
needed here is on the base of this repository: that each `H^q_étale(X, -)` commutes with
arbitrary direct sums of abelian sheaves on a quasi-compact quasi-separated scheme is
`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale`. It is the
one place the quasi-compactness and quasi-separatedness of `X` are consumed, exactly as in the
source.

*Bounded below.* The source states the lemma in `D(X_étale)`, but its hypothesis
`H^n(K_i) = 0` for `n < a` places every `K_i`, and hence their direct sum, in `D⁺(X_étale)`. The
statement here is therefore read on `D⁺` and for `RΓ⁺`, the bounded below right derived functor
of `CategoryTheory.Sheaf.Γ`.

*Direct sums.* "Commutes with direct sums" is
`CategoryTheory.Limits.PreservesColimit` for a discrete diagram: the image of a coproduct cocone
is a coproduct cocone, which is the source's `RΓ(X, ⨁ K_i) = ⨁ RΓ(X, K_i)` read through the
canonical comparison, and presupposes no existence of either coproduct.

*The index universe.* `I` ranges over `Type (max (u + 1) r)`, the universe controlling the
Grothendieck axioms of the abelian sheaves on the small étale site and of the coefficients. This
is forced rather than an artefact: the termwise direct sum of the injective resolutions is formed
inside the category of sheaves, so the index universe and the Grothendieck universe are the same
one. It is also the universe at which
`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale` is stated,
the coefficients `AddCommGrpCat.{max (u + 1) r}` being large enough for the filtered poset of
finite subsets of `I` to be an index category of the size [Stacks, Tag 03Q5] is available at.

## References

* [Stacks Project, Tag 0GIS](https://stacks.math.columbia.edu/tag/0GIS)
* [Stacks Project, Tag 0GIW](https://stacks.math.columbia.edu/tag/0GIW)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.CompactExtensionByZero.hasRightDerivedFunctorPlus

namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-- **[Stacks, Tag 0GIS].** Let `X` be a quasi-compact and quasi-separated scheme, let
`K : I → D⁺(X_étale)` be a family of objects of the bounded below derived category of abelian
sheaves on the small étale site of `X` and let `a : ℤ` be such that `H^n(K i) = 0` for `n < a`
and all `i`, that is `(K i).IsGE a`. Then `RΓ(X, ⨁ i, K i) = ⨁ i, RΓ(X, K i)`.

Nothing is assumed: the one input of the argument beyond the injective resolutions bounded below
by `a` of [Stacks, Tag 07D9] and Leray's acyclicity lemma [Stacks, Tag 015E] is that each
`H^q_étale(X, -)` commutes with the direct sum, which is
`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale`, and that
is where the quasi-compactness and quasi-separatedness of `X` are used.

The source states the lemma in `D(X_étale)`; its hypothesis places every `K i` in `D⁺`, and the
module docstring records why the statement is read there and why the index universe is
`max (u + 1) v`. -/
@[stacks 0GIS "RΓ(X, ⨁ K_i) = ⨁ RΓ(X, K_i) for a family of D⁺(X_étale) with common lower bound
a, on a quasi-compact quasi-separated scheme. The global sections case of the machinery behind
Tag 0GIW; unlike that tag nothing is carried, the input that H^q_étale(X, -) commutes with direct
sums being `preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale`. The index type lies in
Type (max (u+1) v), the universe at which the abelian sheaves on the small étale site are
Grothendieck abelian: the termwise direct sum of the resolutions is formed inside that category,
so the index universe and the Grothendieck universe are the same."]
theorem preservesColimit_rightDerivedFunctorPlus_Γ_smallEtale_of_isGE
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] {I : Type (max (u + 1) v)}
    (K : I → DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    (a : ℤ) (hK : ∀ i, (K i).IsGE a) :
    PreservesColimit (Discrete.functor K)
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus :=
  preservesColimit_rightDerivedFunctorPlus_of_isGE
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (fun p => preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale.{v} X p I) K a hK

end Stacks.EtaleCohomology

end
