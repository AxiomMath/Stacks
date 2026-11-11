module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericStalkCriterion

/-!
# Isomorphisms of dense opens of irreducible schemes

The library's `AlgebraicGeometry.Scheme.Birational` is the existence of an isomorphism between
dense open subschemes. For irreducible schemes a nonempty open is dense, so this is the same as
an isomorphism between nonempty open subschemes; this file records that reformulation.

## Main results

* `AlgebraicGeometry.birational_iff_exists_nonempty_open_iso`: the reformulation.

## Implementation notes

This reformulation is not [Stacks, Tag 0BAA]: there, birationality is isomorphism in the
category of irreducible schemes and dominant rational maps ([Stacks, Tag 0A20]). That notion is
`AlgebraicGeometry.Scheme.DominantBirational`, and Tag 0BAA is
`AlgebraicGeometry.Scheme.dominantBirational_iff_exists_nonempty_open_iso` together with
`AlgebraicGeometry.Scheme.dominantBirationalOver_iff_exists_nonempty_open_iso`, both in
`StacksFrontier.AlgebraicGeometry.Morphisms.Birational.DominantRationalMaps`, whose proofs use it.
The relative reformulation is `AlgebraicGeometry.birationalOver_iff_exists_nonempty_open_iso`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Two irreducible schemes admit an isomorphism of dense open subschemes
(`Scheme.Birational`) if and only if they have isomorphic nonempty open subschemes. -/
public theorem birational_iff_exists_nonempty_open_iso
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] :
    Scheme.Birational X Y ↔
      ∃ (U : X.Opens) (V : Y.Opens),
        (U : Set X).Nonempty ∧ (V : Set Y).Nonempty ∧
          Nonempty (U.toScheme ≅ V.toScheme) :=
  ⟨fun ⟨f⟩ => ⟨f.source, f.target, f.dense_source.nonempty, f.dense_target.nonempty, ⟨f.iso⟩⟩,
    fun ⟨U, V, h, k, ⟨e⟩⟩ => ⟨⟨U, U.2.dense h, V, V.2.dense k, e⟩⟩⟩

end AlgebraicGeometry

end
