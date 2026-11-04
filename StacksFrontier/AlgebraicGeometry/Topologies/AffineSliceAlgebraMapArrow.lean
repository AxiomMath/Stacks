module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechAmitsurComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSliceAlgebraAdjunction

/-!
# The arrow on sections of the terminal object of an affine slice is the algebra map

Let `S` be a scheme, `U` an object of `Over S` whose total space is affine, `R = Γ(U.left, 𝒪)`
and `A` an `R`-algebra. The map on sections `Γ(U) ⟶ Γ(V)` induced by the morphism from the
spectrum `V` of `A` over `U` to the terminal object of the slice at `U` is the algebra map
`R ⟶ A`.

## Main definitions

* `AlgebraicGeometry.overAffineAlgObj`: the `ULift R`-algebra
  `(AlgebraicTopology.algebraMapArrow R A).right`, the universe lift of `A`.

## Main results

* `AlgebraicGeometry.sectionsTerminalArrowIsoAlgebraMapArrow`: the arrow on sections induced by
  the morphism from the spectrum of `AlgebraicGeometry.overAffineAlgObj U A` to the terminal
  object of `Over U` is `AlgebraicTopology.algebraMapArrow R A`.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 023L](https://stacks.math.columbia.edu/tag/023L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology Stacks.CechSite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (U : Over S) [IsAffine U.left] (A : Type u) [CommRing A]
  [Algebra (Γ(U.left, ⊤) : Type u) A]

/-- The universe lift of `A` as a `ULift Γ(U.left, 𝒪)`-algebra, the target of
`AlgebraicTopology.algebraMapArrow Γ(U.left, 𝒪) A`. -/
public abbrev overAffineAlgObj : CommAlgCat.{u} (ULift.{u} (Γ(U.left, ⊤) : Type u)) :=
  (algebraMapArrow (Γ(U.left, ⊤) : Type u) A).right

/-- The arrow on sections induced by the morphism from `Spec A`, over `U`, to the terminal object
of `Over U` is isomorphic to the algebra map `Γ(U.left, 𝒪) ⟶ A`. -/
public def sectionsTerminalArrowIsoAlgebraMapArrow :
    sectionsTerminalArrow ((overAffineAlgSpec U).obj (op (overAffineAlgObj U A)))
        (overAffineAlgΓ U).leftOp ≅
      algebraMapArrow (Γ(U.left, ⊤) : Type u) A :=
  sectionsTerminalArrowIsoOfAdjunction (overAffineAlgAdjunction U) CommAlgCat.isInitialSelf
    (algebraMapArrow (Γ(U.left, ⊤) : Type u) A).hom

end AlgebraicGeometry

end
