module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# The data of the theorem on formal functions for algebraic spaces

The theorem on formal functions compares the `I`-adic completion of the cohomology of a
coherent module on a proper algebraic space over `Spec A` with the inverse limit of the
cohomologies of its restrictions to the infinitesimal thickenings cut out by `I`.  Stacks 08AV
fixes the data it is stated for: a Noetherian ring `A` with an ideal `I`, a proper algebraic
space over `Spec A`, and a coherent module on it.

## Main definitions

* `AlgebraicGeometry.Space.FormalFunctionsSituation` is the data of Stacks 08AV.

## Implementation notes

The target of the structure morphism is `AlgebraicGeometry.Space.baseObject`, the base `Spec A`
read as the terminal object of the big fppf category over itself; its Yoneda presheaf is the
algebraic space `Spec A` over itself, and the thickenings whose adic fibres the theorem
compares with are the objects `AlgebraicGeometry.Space.adicThickeningObject` of the same
category.  Properness is `AlgebraicGeometry.Space.IsProper` of Stacks 03ZM.

Coherence of the module is `AlgebraicGeometry.Space.IsCoherent` of Stacks 07UA, that is,
quasi-coherence together with coherence as a sheaf of modules on the small étale ringed site,
and not merely the latter: on an algebraic space a coherent sheaf is in particular
quasi-coherent.  The universe of the module sections is independent of the universe of the
schemes, as it is for `AlgebraicGeometry.Space.Modules`.

The ambient big fppf site is only required to contain `Spec A`.  The thickenings are
separately required to belong to it by the statements that mention them, since nothing in this
situation refers to them.

## References

* [Stacks Project, Tag 08AV](https://stacks.math.columbia.edu/tag/08AV)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u m

/-- **Stacks 08AV.** A Noetherian ring `A` with an ideal `I`, a proper algebraic space over
`Spec A`, and a coherent module on that space. -/
@[stacks 08AV]
structure FormalFunctionsSituation where
  /-- The Noetherian base ring. -/
  ring : Type u
  [commRing : CommRing ring]
  [noetherian : IsNoetherianRing ring]
  /-- The ideal along which the completion is taken. -/
  ideal : Ideal ring
  /-- The ambient big fppf site. -/
  site : BigFppfSite.{u}
  /-- The spectrum of the base ring belongs to the ambient big fppf site. -/
  containsBase : site.Contains (Spec (.of ring))
  /-- The algebraic space over the base. -/
  space : AlgebraicSpaces site (Spec (.of ring)) containsBase
  /-- The structure morphism to the base. -/
  structureMorphism : space.1 ⟶ yoneda.obj (baseObject ring site containsBase)
  /-- The structure morphism is proper. -/
  proper : IsProper site (Spec (.of ring)) containsBase structureMorphism
  /-- A module on the space. -/
  coefficients : Modules.{u, m} site (Spec (.of ring)) containsBase space.1 space.2
  /-- The module is coherent. -/
  [coherent :
    IsCoherent site (Spec (.of ring)) containsBase space.1 space.2 coefficients]

attribute [instance] FormalFunctionsSituation.commRing FormalFunctionsSituation.noetherian
  FormalFunctionsSituation.coherent

end AlgebraicGeometry.Space

end
