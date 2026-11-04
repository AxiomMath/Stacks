module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksCore.Tactic.StacksAttribute

/-! ## Additive functors in preadditive categories. -/

add_to_stacks 0103 CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive

@[expose] public section

open CategoryTheory Limits

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive]

add_to_stacks 0DLP Functor.preservesFiniteBiproductsOfAdditive
add_to_stacks 0DLP preservesBinaryBiproducts_of_preservesBiproducts
add_to_stacks 0DLP "1 => 2 and 1 => 3" Functor.mapBiprod

@[stacks 0DLP "(3) => (1)"]
lemma Functor.additive_of_mono_biprodComparison [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (G : C ⥤ D) [G.PreservesZeroMorphisms] (h : ∀ X Y : C, Mono (G.biprodComparison X Y)) :
    G.Additive :=
  have : PreservesBinaryBiproducts G := ⟨preservesBinaryBiproduct_of_mono_biprodComparison G⟩
  G.additive_of_preservesBinaryBiproducts

@[stacks 0DLP "(2) => (1)"]
lemma Functor.additive_of_epi_biprodComparison' [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (G : C ⥤ D) [G.PreservesZeroMorphisms] (h : ∀ X Y : C, Epi (G.biprodComparison' X Y)) :
    G.Additive :=
  have : PreservesBinaryBiproducts G := ⟨preservesBinaryBiproduct_of_epi_biprodComparison' G⟩
  G.additive_of_preservesBinaryBiproducts

add_to_stacks 010N "part 1 (i)" CategoryTheory.AdditiveFunctor.ofLeftExact
add_to_stacks 010N "part 1 (ii)" CategoryTheory.AdditiveFunctor.ofRightExact
