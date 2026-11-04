module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat.CoefficientsExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat.SignDegreeRaising
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat.TensorDifferential
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat.FlatAndKFlat

/-!
# The free graded module on a sheaf of graded sets is flat

The free graded module `A[S]` on a sheaf of graded sets is flat and K-flat: conditions (1) and
(2) of Tag 0FSA for the module of Tag 0FSG. The development is in four parts:
`CoefficientsExact` (the construction `X ↦ X[S]` preserves exactness), `SignDegreeRaising` (the
sign automorphism of `X[S]`, transport along a reindexing of the coefficient degrees, and the
signed degree-raising map of `W[S]`), `TensorDifferential` (the identification
`A[S] ⊗_A N = N[S]` carries the differential to the signed degree-raising map) and
`FlatAndKFlat` (Tag 0FSG, conditions (1) and (2) of Tag 0FSA).
-/
