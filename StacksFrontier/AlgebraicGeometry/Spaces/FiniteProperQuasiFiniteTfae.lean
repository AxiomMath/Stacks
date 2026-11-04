module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite

/-!
# The four conditions of Stacks 0A4X collected as a single equivalence

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Stacks 0A4X lists four conditions on `f` and asserts that they are
equivalent:

1. `f` is finite;
2. `f` is proper and locally quasi-finite;
3. `f` is proper and the point space of its fibre over every field-valued point of `Y` is
   discrete;
4. `f` is universally closed, separated and locally of finite type, and the point space of its
   fibre over every field-valued point of `Y` is discrete.

The pairwise comparisons are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteProperQuasiFinite.lean`. This file collects them
into one `List.TFAE` statement, in the source's numbering, so that a consumer can name the
equivalence itself rather than assemble it from the pieces.

## Main results

* `AlgebraicGeometry.Space.isFinite_tfae`: **Stacks 0A4X**, the four conditions collected as a
  `List.TFAE`.

## Implementation notes

The entries of the list are the very propositions the pairwise comparisons in
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteProperQuasiFinite.lean` speak about, so no bridging
is needed: the fibre over a field-valued point `p` is the pullback of `f` along the morphism out
of the field spectrum presented by `p`, taken in the order Stacks 06RW uses, and the
discreteness clause is a quantifier over *all* field-valued points of `Y`.

The cycle is closed by five of the six facts:

* (1) ⇒ (2) is `AlgebraicGeometry.Space.isProper_and_isLocallyQuasiFinite_of_isFinite`;
* (2) ⇒ (1) is `AlgebraicGeometry.Space.isFinite_of_isProper_of_isLocallyQuasiFinite`;
* (2) ⇔ (3) is
  `AlgebraicGeometry.Space.isProper_and_isLocallyQuasiFinite_iff_isProper_and_discreteFibres`;
* (3) ⇔ (4) is
  `AlgebraicGeometry.Space.isProper_iff_universallyClosed_isSeparated_isLocallyOfFiniteType`
  conjoined with the discreteness clause, which the two conditions share.

## References

* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
* [Stacks Project, Tag 06RW](https://stacks.math.columbia.edu/tag/06RW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0A4X**, the four conditions collected as a `List.TFAE`. For a morphism
`f : X ⟶ Y` of algebraic spaces over `S` the following are equivalent: `f` is finite; `f` is
proper and locally quasi-finite; `f` is proper and the point space of its fibre over every
field-valued point of `Y` is discrete; `f` is universally closed, separated and locally of
finite type, and the point space of its fibre over every field-valued point of `Y` is
discrete.

The entries are listed in the source's numbering, and each is the proposition the
corresponding pairwise comparison in
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteProperQuasiFinite.lean` speaks about, from which
this equivalence is assembled. -/
@[stacks 0A4X "the four conditions collected as a TFAE",
  ega "IV 18.12.4",
  ega "III 4.4.11" "proper q-finite ⇒ finite", ega "III 4.4.2" "a) <=> c)"]
theorem isFinite_tfae (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE
      [IsFinite B S hS f,
        IsProper B S hS f ∧ IsLocallyQuasiFinite B S hS f,
        IsProper B S hS f ∧ ∀ p : FieldValuedPoint B S hS Y,
          DiscreteTopology (points B S hS (pullback (yonedaEquiv.symm p.value) f)),
        UniversallyClosed B S hS f ∧ IsSeparated B S hS f ∧ IsLocallyOfFiniteType B S hS f ∧
          ∀ p : FieldValuedPoint B S hS Y,
            DiscreteTopology (points B S hS (pullback (yonedaEquiv.symm p.value) f))] := by
  tfae_have 1 → 2 := isProper_and_isLocallyQuasiFinite_of_isFinite B S hS hX hY f
  tfae_have 2 → 1 := fun h ↦
    isFinite_of_isProper_of_isLocallyQuasiFinite B S hS hX hY f h.1 h.2
  tfae_have 2 ↔ 3 :=
    isProper_and_isLocallyQuasiFinite_iff_isProper_and_discreteFibres B S hS hX hY f
  tfae_have 3 ↔ 4 := by
    rw [isProper_iff_universallyClosed_isSeparated_isLocallyOfFiniteType B S hS hX hY f,
      and_assoc, and_assoc]
  tfae_finish

end AlgebraicGeometry.Space

end
