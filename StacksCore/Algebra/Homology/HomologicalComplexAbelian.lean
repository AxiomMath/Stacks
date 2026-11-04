module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import StacksCore.Tactic.StacksAttribute

/-! # The category of complexes over an abelian category is abelian

Stacks tag 010Y for chain complexes and 0114 for cochain complexes; as everywhere in §12.13 the
two are one statement about an arbitrary `c : ComplexShape ι`, so each part below carries both
tags. See `StacksCore.Algebra.Homology.Homotopy` for the indexing conventions this collapses.

Parts (1) and (4) are already in Mathlib, as the `Abelian (HomologicalComplex C c)` instance and
`HomologicalComplex.exact_iff_degreewise_exact`. Parts (2) and (3) are proved here: Mathlib has
the implications `mono_of_mono_f` and `epi_of_epi_f`, and the converses hold because each
evaluation functor preserves finite limits and colimits. Only that much is needed, so the two
lemmas are stated without `Abelian`, which the Stacks statement assumes.

The Stacks project says *injective* and *surjective* where an abelian category has no elements;
these mean monomorphism and epimorphism, which is how (2) and (3) are read here.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

/-- **Stacks 010Y (2) and 0114 (2).** A morphism of complexes is a monomorphism if and only if it
is one in each degree. -/
@[stacks 010Y "(2)", stacks 0114 "(2)"]
lemma mono_iff_degreewise_mono [HasFiniteLimits C] (φ : K ⟶ L) :
    Mono φ ↔ ∀ i, Mono (φ.f i) :=
  ⟨fun _ i ↦ (eval C c i).map_mono φ, mono_of_mono_f φ⟩

/-- **Stacks 010Y (3) and 0114 (3).** A morphism of complexes is an epimorphism if and only if it
is one in each degree. -/
@[stacks 010Y "(3)", stacks 0114 "(3)"]
lemma epi_iff_degreewise_epi [HasFiniteColimits C] (φ : K ⟶ L) :
    Epi φ ↔ ∀ i, Epi (φ.f i) :=
  ⟨fun _ i ↦ (eval C c i).map_epi φ, epi_of_epi_f φ⟩

end HomologicalComplex

add_to_stacks 010Y "(1)" HomologicalComplex.instAbelian

add_to_stacks 0114 "(1)" HomologicalComplex.instAbelian

add_to_stacks 010Y "(4), for a short complex of complexes: exactness at the middle term is
exactness at the middle term in every degree."
  HomologicalComplex.exact_iff_degreewise_exact

add_to_stacks 0114 "(4)" HomologicalComplex.exact_iff_degreewise_exact
