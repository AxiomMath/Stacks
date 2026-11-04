module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Seminormalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Scheme

/-!
# Seminormality on every affine open, at the library's spelling

`AlgebraicGeometry.IsSeminormal` is defined pointwise: every point has *some* affine open
neighbourhood whose ring of sections is seminormal.  The upgrade to the statement about
*every* affine open, which is the form the geometric arguments need, is already proved as
`Stacks.AlgebraicGeometry.Seminormal.isSeminormal_iff_forall_affineOpens`.  This file restates
it at `AlgebraicGeometry.IsSeminormal` and `IsSeminormalRing`, and records the transport of
seminormality of a scheme along an isomorphism.

## Main results

* `AlgebraicGeometry.isSeminormal_iff_forall_affineOpens` is the equivalence between the
  pointwise definition and the condition on every affine open.
* `AlgebraicGeometry.isSeminormal_of_isIso` transports seminormality of a scheme along an
  isomorphism.

## Implementation notes

The repository carries two unbridged spellings of seminormality with character-for-character
identical bodies: `IsSeminormalRing` (`AlgebraicGeometry/Morphisms/WeakNormalization/Ring.lean`,
which is what the tagged `AlgebraicGeometry.IsSeminormal` and the whole `WeakNormalization`
development use) and `Stacks.RingTheory.Seminormal.IsSeminormalRing`
(`StacksFrontier/AlgebraicGeometry/Seminormalization/Defs.lean`, with its scheme-level
`Stacks.AlgebraicGeometry.Seminormal.IsSeminormal` built on the equally duplicated
`IsLocallyRingProperty`).  Both are plain `def`s, so the two spellings are interchangeable at
default transparency and the restatement below is literally the existing proof: no bridging
argument is needed, only the restatement, which is why it is given as a term.

Transport along an isomorphism is likewise `Stacks.RingTheory.Seminormal.IsSeminormalRing`'s
`of_ringEquiv` applied to the isomorphism of section rings over the preimage of an affine open.

## References

* [Stacks Project, Tag 0EUP](https://stacks.math.columbia.edu/tag/0EUP)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0EUP.** A scheme is seminormal if and only if the ring of sections
of every affine open is seminormal.

This is `Stacks.AlgebraicGeometry.Seminormal.isSeminormal_iff_forall_affineOpens` restated at
the spelling of seminormality that the `WeakNormalization` development uses. -/
theorem isSeminormal_iff_forall_affineOpens (X : Scheme.{u}) :
    IsSeminormal X ↔ ∀ U : X.affineOpens, IsSeminormalRing Γ(X, U.1) :=
  Stacks.AlgebraicGeometry.Seminormal.isSeminormal_iff_forall_affineOpens

/-- Seminormality of a scheme transports along an isomorphism. -/
theorem isSeminormal_of_isIso {P Q : Scheme.{u}} (f : P ⟶ Q) [IsIso f]
    (hP : IsSeminormal P) : IsSeminormal Q := by
  rw [isSeminormal_iff_forall_affineOpens]
  intro U
  have hV : IsSeminormalRing Γ(P, (f ⁻¹ᵁ U.1 : P.Opens)) :=
    (isSeminormal_iff_forall_affineOpens P).mp hP ⟨f ⁻¹ᵁ U.1, IsAffineOpen.preimage U.2 f⟩
  exact Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv
    (RingEquiv.ofBijective (f.app U.1).hom
      ((ConcreteCategory.isIso_iff_bijective (f.app U.1)).mp inferInstance)).symm hV

end AlgebraicGeometry

end
