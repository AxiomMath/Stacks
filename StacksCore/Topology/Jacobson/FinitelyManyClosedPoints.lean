module

public import Mathlib.Topology.JacobsonSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Jacobson spaces with finitely many closed points

Stacks 07JU has two parts — a finite Jacobson space is discrete, and a Jacobson space with
finitely many closed points is discrete — and Mathlib states both, as
`instDiscreteTopologyOfFiniteOfJacobsonSpace` and `JacobsonSpace.discreteTopology`.

## References

* [Stacks Project, Tag 07JU](https://stacks.math.columbia.edu/tag/07JU)
-/

@[expose] public section

add_to_stacks 07JU "a finite Jacobson space is discrete" instDiscreteTopologyOfFiniteOfJacobsonSpace
add_to_stacks 07JU "a Jacobson space with finitely many closed points is discrete"
  JacobsonSpace.discreteTopology
