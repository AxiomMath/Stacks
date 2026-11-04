module

public import Mathlib.Algebra.Homology.BifunctorAssociator
import StacksCore.Tactic.StacksAttribute

/-! ## The associator for bifunctors on complexes

Stacks 08BI compares the two two-step total complexes of a triple complex. Mathlib proves this
for the triple complexes `G(F₁₂(K₁, K₂), K₃)` and `F(K₁, G₂₃(K₂, K₃))` obtained from three
complexes and compatible bifunctors, under the sign compatibility `ComplexShape.Associative`;
that is the case the remark's citers in the algebra chapters use, e.g. for derived tensor products.
The general triple complex is treated in `StacksCore.Algebra.Homology.HomologicalTricomplex`. -/

@[expose] public section

add_to_stacks 08BI "the bifunctor case: `Tot(Tot(F₁₂(K₁, K₂)) ⊗ K₃) ≅ Tot(K₁ ⊗ Tot(G₂₃(K₂, K₃)))`"
  HomologicalComplex.mapBifunctorAssociator
