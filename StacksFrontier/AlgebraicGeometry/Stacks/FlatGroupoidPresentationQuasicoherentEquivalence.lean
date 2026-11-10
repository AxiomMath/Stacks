module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AlgebraicStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackQuasicoherentEquivalence

/-!
# Quasi-coherent modules on an algebraic stack through a flat groupoid presentation

Let `𝒳` be an algebraic stack and `(U, R, s, t, c)` the flat groupoid of a flat groupoid
presentation `[U/_pR] ⟶ 𝒳` (Stacks 04T5). Reading Stacks 06WT through the presentation gives an
equivalence `QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)` (Stacks 06WV (1)), whose functor is the descent
functor of the presentation.

## Main definitions

* `AlgebraicGeometry.Stack.FlatGroupoidPresentation.quasicoherentEquivalenceGroupoid`: the
  equivalence `QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)` of a flat groupoid presentation.

## Main results

* `AlgebraicGeometry.Stack.FlatGroupoidPresentation.quasicoherentEquivalenceGroupoid_functor`: its
  functor is the descent functor.

The abelian structure of Stacks 06WV (2) is `AlgebraicGeometry.Stack.abelianQuasicoherentModules`
in `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AlgebraicStackPresentation`,
imported here.

## References

* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

section AlgebraicStack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The equivalence `QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)` attached to a flat groupoid presentation of
an algebraic stack: Stacks 06WT read through the presentation (Stacks 06WV (1)). -/
def FlatGroupoidPresentation.quasicoherentEquivalenceGroupoid {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (P : FlatGroupoidPresentation 𝒳) :
    FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids ≌ Space.QuasicoherentModule B S hS P.G :=
  haveI := P.full
  haveI := P.faithful
  haveI := isEquivalence_pointwiseQuasicoherentDescentFunctor P.F P.hF 𝒳.val.isFiberedInGroupoids
    P.hloc
  (pointwiseQuasicoherentDescentFunctor P.F P.hF 𝒳.val.isFiberedInGroupoids).asEquivalence

/-- The functor of `FlatGroupoidPresentation.quasicoherentEquivalenceGroupoid` is the descent
functor `pointwiseQuasicoherentDescentFunctor` of the presentation. -/
theorem FlatGroupoidPresentation.quasicoherentEquivalenceGroupoid_functor
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (P : FlatGroupoidPresentation 𝒳) :
    P.quasicoherentEquivalenceGroupoid.functor =
      pointwiseQuasicoherentDescentFunctor P.F P.hF 𝒳.val.isFiberedInGroupoids := rfl

end AlgebraicStack

end AlgebraicGeometry.Stack

end
