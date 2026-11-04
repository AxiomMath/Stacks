module

public import Mathlib.Algebra.Homology.QuasiIso
import StacksCore.Tactic.StacksAttribute

/-! # Quasi-isomorphisms

Stacks tags 010Z (1) and 0110 (2) for chain complexes, and 0115 (1) and 0116 (2) for cochain
complexes; as everywhere in §12.13 each pair is one declaration about an arbitrary
`c : ComplexShape ι`.

010Z and 0115 are definitions, so the tag goes on Mathlib's `QuasiIso` itself. That class is
stated degreewise, through `QuasiIsoAt`, rather than through the homology objects the Stacks
project uses, so `quasiIso_iff_isIso_homologyMap` follows as the bridge: it records the tag
against the Stacks wording too, and not merely against a class of the same name.

Part 2 of those definitions, acyclic complexes, is in
`StacksCore.Algebra.Homology.ShortComplex.HomologicalComplex`, where Mathlib defines `Acyclic`.
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

add_to_stacks 010Z "(1), the definition" QuasiIso

add_to_stacks 0115 "(1), the definition; `QuasiIso` is stated for an arbitrary `ComplexShape`, so
the chain- and cochain-complex tags are the same declaration."
  QuasiIso

/-- **Stacks 010Z (1) and 0115 (1).** A morphism of complexes is a quasi-isomorphism exactly when
the induced map `Hᵢ(f) : Hᵢ(K) ⟶ Hᵢ(L)` is an isomorphism for every `i`. -/
@[stacks 010Z "(1), identified with the Stacks wording",
  stacks 0115 "(1), identified with the Stacks wording", sga "4½ Etat_0 3.1.7"]
lemma quasiIso_iff_isIso_homologyMap (f : K ⟶ L)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso f ↔ ∀ i, IsIso (homologyMap f i) :=
  (quasiIso_iff f).trans (forall_congr' fun i ↦ quasiIsoAt_iff_isIso_homologyMap f i)

add_to_stacks 0110 "part 2" HomotopyEquiv.quasiIso_hom

add_to_stacks 0116 "part 2" HomotopyEquiv.quasiIso_hom
