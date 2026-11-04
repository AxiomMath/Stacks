module

public import Mathlib.Algebra.Homology.BifunctorHomotopy
import StacksCore.Tactic.StacksAttribute

/-! ## Homotopies and the total complex of a bifunctor

The second points of Stacks 0G6A and 0G6B say that `Tot` of homotopic maps of double complexes
are homotopic. Mathlib proves this for the double complexes `F(K₁, K₂)` built from a bifunctor and
two complexes, for homotopies in either variable; the general bicomplex is treated in
`StacksCore.Algebra.Homology.TotalComplexHomotopy`. -/

@[expose] public section

add_to_stacks 0G6B "point 2 for the bicomplexes `F(K₁, K₂)`: a homotopy in the first variable"
  HomologicalComplex.mapBifunctorMapHomotopy₁
add_to_stacks 0G6A "point 2 for the bicomplexes `F(K₁, K₂)`: a homotopy in the second variable"
  HomologicalComplex.mapBifunctorMapHomotopy₂
