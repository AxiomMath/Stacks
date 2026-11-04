module

public import StacksFrontier.Deformation.FlatAlgebraLiftHenselizationRelative.ForwardImplication
public import StacksFrontier.Deformation.FlatAlgebraLiftHenselizationRelative.FlatModuleLiftInstance
public import StacksFrontier.Deformation.FlatAlgebraLiftHenselizationRelative.Converse
public import StacksFrontier.Deformation.FlatAlgebraLiftHenselizationRelative.ExtOneSurjectivity

/-!
# Stacks 0DZB with Stacks 0DZ2 taken only where it is used

The development is split into four parts: `ForwardImplication` proves the forward implication of
Stacks 0DZB unconditionally, together with the syntomic, not formally smooth `A[x]/(x²)`;
`FlatModuleLiftInstance` shows that the one instance of Stacks 0DZ2 the converse consumes is
equivalent to the converse itself; `Converse` proves Stacks 0DZB with Stacks 0DZ2 taken only at
the surjection in hand, and unconditionally at a square-zero kernel; and `ExtOneSurjectivity`
treats the `Ext¹` surjectivity a dévissage from nilpotent to square-zero kernels would need, and
shows it is formal smoothness.
-/
