module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedHomDisjointUnionProductProof
public import StacksFrontier.AlgebraicGeometry.Quot.RelHomStructureRepresentable

/-!
# Step (S) of Stacks 0DLC, part (3), and the case `W = Y` of part (3)

This file discharges the input `AlgebraicGeometry.Space.DerivedHomDisjointUnionProduct` of step
(S), proved in `StacksFrontier/AlgebraicGeometry/Quot/DerivedHomDisjointUnionProductProof.lean`.
What is left is Stacks 0DL9 itself, carried as the hypothesis of the proposition
`AlgebraicGeometry.Space.RelativeDerivedHomIsSheafOfDescent`.  It then assembles the case `W = Y`
of Stacks 0DLC, part (3), with step (S) discharged, and also with step (L) discharged, which
`AlgebraicGeometry.Space.relHomStructureRepresentableOfIsLE` proves.  Nothing is registered: the
assembly still carries part (2) at `W = Y`, Stacks 0DKY and Stacks 0DL9.

## Main results

* `AlgebraicGeometry.Space.relativeDerivedHomIsSheafOfDescent`: step (S), the proposition
  `AlgebraicGeometry.Space.RelativeDerivedHomIsSheafOfDescent`.
* `AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_steps'`: Stacks 0DLC,
  part (3), at `W = Y`, from part (2), Stacks 0DKY, Stacks 0DL9 and step (L).
* `AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_external`: the same, from
  part (2), Stacks 0DKY and Stacks 0DL9 only.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DL9](https://stacks.math.columbia.edu/tag/0DL9)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Step (S) of the proof of Stacks 0DLC, part (3)**: granted Stacks 0DL9, the functor
`T ↦ Hom(K_T, E_T)` is an fppf sheaf over `Y` whenever the negative extensions of `K_V`, `E_V`
vanish for every `V` over `Y`.  This is
`AlgebraicGeometry.Space.relativeDerivedHomIsSheafOfDescent_of_disjointUnion` with the derived Hom
of a disjoint union, `AlgebraicGeometry.Space.derivedHomDisjointUnionProduct`. -/
theorem relativeDerivedHomIsSheafOfDescent : RelativeDerivedHomIsSheafOfDescent B S hS :=
  relativeDerivedHomIsSheafOfDescent_of_disjointUnion (derivedHomDisjointUnionProduct B S hS)

/-- **Stacks 0DLC, part (3), in the case `W = Y`**, from part (2) in the case `W = Y` (`h2`),
Stacks 0DKY (`h0DKY`), Stacks 0DL9 (`h0DL9`) and step (L) (`hL`): the assembly
`AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_steps` with step (S)
discharged by `AlgebraicGeometry.Space.relativeDerivedHomIsSheafOfDescent`. -/
theorem relativeDerivedHomRepresentableOfFibres_of_steps'
    (h2 : NegativeExtVanishesOfFibres B S hS)
    (h0DKY : RelativeDerivedHomDualExistsNaturalCompatible B S hS)
    (h0DL9 : DerivedHomHypercoveringDescent B S hS)
    (hL : RelHomStructureRepresentableOfIsLE B S hS) :
    RelativeDerivedHomRepresentableOfFibres B S hS :=
  relativeDerivedHomRepresentableOfFibres_of_steps h2 h0DKY h0DL9
    relativeDerivedHomIsSheafOfDescent hL

/-- **Stacks 0DLC, part (3), in the case `W = Y`**, from part (2) in the case `W = Y` (`h2`),
Stacks 0DKY (`h0DKY`) and Stacks 0DL9 (`h0DL9`): both internal steps are discharged, step (S) by
`AlgebraicGeometry.Space.relativeDerivedHomIsSheafOfDescent` and step (L) by
`AlgebraicGeometry.Space.relHomStructureRepresentableOfIsLE`. -/
theorem relativeDerivedHomRepresentableOfFibres_of_external
    (h2 : NegativeExtVanishesOfFibres B S hS)
    (h0DKY : RelativeDerivedHomDualExistsNaturalCompatible B S hS)
    (h0DL9 : DerivedHomHypercoveringDescent B S hS) :
    RelativeDerivedHomRepresentableOfFibres B S hS :=
  relativeDerivedHomRepresentableOfFibres_of_steps' h2 h0DKY h0DL9
    relHomStructureRepresentableOfIsLE

end AlgebraicGeometry.Space

end
