module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericStalkCriterion

/-!
# Birationality of irreducible schemes

Two irreducible schemes are birational precisely when they contain isomorphic nonempty open
subschemes. A nonempty open of an irreducible space is dense, so a partial isomorphism is the
same datum as an isomorphism between nonempty opens.

## Main results

* `AlgebraicGeometry.birational_iff_exists_nonempty_open_iso`: the absolute characterization.

## Implementation notes

The relative characterization, with the isomorphism required to commute with the structure maps,
is `AlgebraicGeometry.birationalOver_iff_exists_nonempty_open_iso`, which takes no
finite-presentation hypotheses; it is registered for the tag with `add_to_stacks`.

## References

* [Stacks Project, Tag 0BAA](https://stacks.math.columbia.edu/tag/0BAA)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Two irreducible schemes are birational if and only if they have isomorphic
nonempty open subschemes. -/
@[stacks 0BAA "part (1)"]
public theorem birational_iff_exists_nonempty_open_iso
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] :
    Scheme.Birational X Y ↔
      ∃ (U : X.Opens) (V : Y.Opens),
        (U : Set X).Nonempty ∧ (V : Set Y).Nonempty ∧
          Nonempty (U.toScheme ≅ V.toScheme) :=
  ⟨fun ⟨f⟩ => ⟨f.source, f.target, f.dense_source.nonempty, f.dense_target.nonempty, ⟨f.iso⟩⟩,
    fun ⟨U, V, h, k, ⟨e⟩⟩ => ⟨⟨U, U.2.dense h, V, V.2.dense k, e⟩⟩⟩

add_to_stacks 0BAA "part (2)" AlgebraicGeometry.birationalOver_iff_exists_nonempty_open_iso

end AlgebraicGeometry

end
