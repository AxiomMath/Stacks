module

public import StacksFrontier.RingTheory.Different.Formula.AnnihilatorOfDiagonal.KoszulResolution
public import StacksFrontier.RingTheory.Different.Formula.AnnihilatorOfDiagonal.ScalarExtensionComparison
public import StacksFrontier.RingTheory.Different.Formula.AnnihilatorOfDiagonal.AnnihilatorCriteria
public import StacksFrontier.RingTheory.Different.Formula.AnnihilatorOfDiagonal.ComparisonQuasiIso

/-!
# The annihilator of the diagonal ideal of a flat complete intersection

This file re-exports the parts of the proof that, for a flat complete intersection
`B = P/(f_1, …, f_n)` over `A`, the annihilator of `I = Ker(B ⊗_A B → B)` is free of rank one over
`B` on the image of `det(g_{ij})` (Stacks Project, Tag 0BWC): Koszul resolutions, the comparison
of Koszul complexes after scalar extension, algebraic criteria for the annihilator, and the
quasi-isomorphism of the comparison together with the main results.
-/
