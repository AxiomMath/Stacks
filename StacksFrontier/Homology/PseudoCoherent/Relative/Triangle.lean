module

public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.PseudoCoherent.Triangle

@[expose] public section

/-!
# Relative pseudo-coherence around a distinguished triangle

Pseudo-coherence relative to a base ring is a two-out-of-three property around a distinguished
triangle, with the shift in the degree bound that the source records.

## Main results

* `PseudoCoherence.isRelativelyPseudoCoherent_of_distinguished` (Stacks 0674).

## Implementation notes

The proof works one polynomial presentation at a time. Relative pseudo-coherence is by
definition a statement about every presentation, so it is enough to fix a surjection
`f : R[x_1,…,x_n] ↠ A` and argue over the polynomial algebra; restriction of scalars along `f` is
exact, so it carries the distinguished triangle to a distinguished triangle and the absolute
statement applies there.

The absolute statement is `PseudoCoherence.isPseudoCoherent_of_distinguished_one` and its two
companions, tag 064R, from `StacksFrontier.Homology.PseudoCoherent.Triangle`. This module
imports it directly.

## References

* [The Stacks Project, Lemma 15.82.6 (0674)](https://stacks.math.columbia.edu/tag/0674)
-/

open CategoryTheory CategoryTheory.Pretriangulated

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0674.** Relative pseudo-coherence is preserved around a distinguished triangle,
with the indicated shift in the degree bound. Without a degree bound it is a two-out-of-three
property. -/
@[stacks 0674]
public theorem isRelativelyPseudoCoherent_of_distinguished
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (m : ℤ)
    (T : Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ distinguishedTriangles) :
    ((IsRelativelyPseudoCoherentFrom (R := R) T.obj₁ (m + 1) →
        IsRelativelyPseudoCoherentFrom (R := R) T.obj₂ m →
        IsRelativelyPseudoCoherentFrom (R := R) T.obj₃ m) ∧
      (IsRelativelyPseudoCoherentFrom (R := R) T.obj₁ m →
        IsRelativelyPseudoCoherentFrom (R := R) T.obj₃ m →
        IsRelativelyPseudoCoherentFrom (R := R) T.obj₂ m) ∧
      (IsRelativelyPseudoCoherentFrom (R := R) T.obj₂ (m + 1) →
        IsRelativelyPseudoCoherentFrom (R := R) T.obj₃ m →
        IsRelativelyPseudoCoherentFrom (R := R) T.obj₁ (m + 1))) ∧
    ((IsRelativelyPseudoCoherent (R := R) T.obj₁ →
        IsRelativelyPseudoCoherent (R := R) T.obj₂ →
        IsRelativelyPseudoCoherent (R := R) T.obj₃) ∧
      (IsRelativelyPseudoCoherent (R := R) T.obj₁ →
        IsRelativelyPseudoCoherent (R := R) T.obj₃ →
        IsRelativelyPseudoCoherent (R := R) T.obj₂) ∧
      (IsRelativelyPseudoCoherent (R := R) T.obj₂ →
        IsRelativelyPseudoCoherent (R := R) T.obj₃ →
        IsRelativelyPseudoCoherent (R := R) T.obj₁)) := by
  have proveOne : ∀ i : ℤ,
      IsRelativelyPseudoCoherentFrom (R := R) T.obj₁ (i + 1) →
      IsRelativelyPseudoCoherentFrom (R := R) T.obj₂ i →
      IsRelativelyPseudoCoherentFrom (R := R) T.obj₃ i := by
    intro i hK hL n f hf
    let F := (ModuleCat.restrictScalars.{u} f.toRingHom).mapDerivedCategory
    exact isPseudoCoherent_of_distinguished_one i
      (F.mapTriangle.obj T) (F.map_distinguished T hT) (hK n f hf) (hL n f hf)
  have proveTwo : ∀ i : ℤ,
      IsRelativelyPseudoCoherentFrom (R := R) T.obj₁ i →
      IsRelativelyPseudoCoherentFrom (R := R) T.obj₃ i →
      IsRelativelyPseudoCoherentFrom (R := R) T.obj₂ i := by
    intro i hK hM n f hf
    let F := (ModuleCat.restrictScalars.{u} f.toRingHom).mapDerivedCategory
    exact isPseudoCoherent_of_distinguished_two i
      (F.mapTriangle.obj T) (F.map_distinguished T hT) (hK n f hf) (hM n f hf)
  have proveThree : ∀ i : ℤ,
      IsRelativelyPseudoCoherentFrom (R := R) T.obj₂ (i + 1) →
      IsRelativelyPseudoCoherentFrom (R := R) T.obj₃ i →
      IsRelativelyPseudoCoherentFrom (R := R) T.obj₁ (i + 1) := by
    intro i hL hM n f hf
    let F := (ModuleCat.restrictScalars.{u} f.toRingHom).mapDerivedCategory
    exact isPseudoCoherent_of_distinguished_three i
      (F.mapTriangle.obj T) (F.map_distinguished T hT) (hL n f hf) (hM n f hf)
  exact ⟨⟨proveOne m, proveTwo m, proveThree m⟩,
    fun hK hL i => proveOne i (hK (i + 1)) (hL i),
    fun hK hM i => proveTwo i (hK i) (hM i),
    fun hL hM i => by simpa using proveThree (i - 1) (by simpa using hL i) (hM (i - 1))⟩

end PseudoCoherence
