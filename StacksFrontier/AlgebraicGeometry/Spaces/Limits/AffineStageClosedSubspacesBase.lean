module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineViewOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspacesViewOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme

/-!
# Stacks 07SQ for closed subspaces over a general base, from the terminal base

Let `Y` be a quasi-compact separated algebraic space over `S` and let `(Z_i)` be a directed,
antitone family of closed subspaces of `Y` whose intersection is affine. Stacks 07SQ then gives an
affine `Z_i`; no bound on the index is needed, because the intersection of closed subspaces of one
space is their honest limit.

This file reduces the statement over `S` to the one over the terminal scheme. It views everything
over `Spec ℤ` (Spaces, Definition 65.16.2): `exists_closedSubspaces_viewOverIntegers` transports
the family, `isAffineSpace_viewOverIntegers_iff` transports affineness, and quasi-compactness and
separatedness transport by `isQuasiCompactSpace_relocalize` and
`isAbsolutelySeparated_viewOverIntegers_iff`. The terminal-base statement is the hypothesis `htm`
here. No `@[stacks]` attribute is attached.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Stacks 07SQ for a directed family of closed subspaces of a quasi-compact separated algebraic
space over `S`, deduced from the same statement over the terminal scheme, `htm`. -/
theorem exists_isAffineSpace_of_closedSubspaces_of_terminal
    (htm : ∀ (Y : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal)
      (_ : IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal Y.1)
      (_ : IsAbsolutelySeparated B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Y.1)
      {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] (i₀ : ι)
      (Z : ι → ClosedSubspaces B (⊤_ Scheme.{u}) B.contains_terminal Y.1)
      (_ : ∀ ⦃i j⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
      (_ : IsAffineSpace B (⊤_ Scheme.{u}) B.contains_terminal (⨅ i, (Z i).1).toFunctor),
      ∃ i, i₀ ≤ i ∧ IsAffineSpace B (⊤_ Scheme.{u}) B.contains_terminal (Z i).1.toFunctor)
    (Y : AlgebraicSpaces B S hS) (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYsep : IsAbsolutelySeparated B S hS B.contains_terminal Y.1)
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] (i₀ : ι)
    (Z : ι → ClosedSubspaces B S hS Y.1) (hZ : ∀ ⦃i j⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
    (haff : IsAffineSpace B S hS (⨅ i, (Z i).1).toFunctor) :
    ∃ i, i₀ ≤ i ∧ IsAffineSpace B S hS (Z i).1.toFunctor := by
  have hT : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  obtain ⟨Z', hZ', hstage, ⟨hinf⟩⟩ :=
    exists_closedSubspaces_viewOverIntegers B S hS hT Y Z hZ
  let Y' : AlgebraicSpaces B (⊤_ Scheme.{u}) hT :=
    ⟨viewOverIntegers B S hS hT Y.1,
      isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hT) ⟨terminal.from S⟩ _ Y.2⟩
  have haff' : IsAffineSpace B (⊤_ Scheme.{u}) hT (⨅ i, (Z' i).1).toFunctor :=
    ((isAffineSpace_viewOverIntegers_iff B S hS hT).2 haff).of_iso hinf.symm
  obtain ⟨i, hi, hiaff⟩ := htm Y' (isQuasiCompactSpace_relocalize B S hS hT _ hYqc)
    ((isAbsolutelySeparated_viewOverIntegers_iff B S hS hT Y.1).2 hYsep) i₀ Z' hZ' haff'
  obtain ⟨e⟩ := hstage i
  exact ⟨i, hi, (isAffineSpace_viewOverIntegers_iff B S hS hT).1 (hiaff.of_iso e)⟩

end AlgebraicGeometry.Space

end
