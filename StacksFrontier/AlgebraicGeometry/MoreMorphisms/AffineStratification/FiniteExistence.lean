module

public import StacksFrontier.AlgebraicGeometry.CompactOpenInduction.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.Union

/-!
# Finite affine stratifications and quasi-compact quasi-separated schemes

A scheme admits an affine stratification indexed by a finite poset exactly when it is
quasi-compact and quasi-separated.

## Main definitions

* `AlgebraicGeometry.HasFiniteAffineStratification`: the existence of an affine stratification
  indexed by a finite partially ordered type.

## Main results

* `AlgebraicGeometry.hasFiniteAffineStratification_iff`: a scheme has a finite affine
  stratification if and only if it is quasi-compact and quasi-separated.

## Implementation notes

Quasi-compactness is `CompactSpace` and quasi-separatedness is `QuasiSeparatedSpace` on the
underlying space. The index type is quantified existentially in a universe independent of the
scheme, so no particular finite enumeration is privileged.

For a scheme with a finite affine stratification, every stratum is affine, hence quasi-compact,
and a finite union of quasi-compact sets is quasi-compact. The intersection of two affine opens
meets each stratum in an affine open of that stratum, because the inclusion of the stratum is
an affine morphism and an affine scheme has affine diagonal; so that intersection is a finite
union of quasi-compact sets as well.

Conversely the construction is by induction on quasi-compact opens: an affine open is a single
stratum, and the union of a quasi-compact open with an affine open is handled by
`AlgebraicGeometry.AffineStratification.ofSup`.

## References

* [Stacks Project, Tag 0F2U](https://stacks.math.columbia.edu/tag/0F2U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u v

namespace AlgebraicGeometry

/-- A scheme *has a finite affine stratification* if it admits an affine stratification indexed
by a finite partially ordered type.

See [Stacks, Tag 0F2U]. -/
def HasFiniteAffineStratification (X : Scheme.{u}) : Prop :=
  ∃ (I : Type v) (_ : Finite I) (order : PartialOrder I),
    Nonempty (@AffineStratification X I order)

private lemma hasFiniteAffineStratification_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (h : HasFiniteAffineStratification.{u, v} X) :
    HasFiniteAffineStratification.{u, v} Y := by
  obtain ⟨I, hI, order, ⟨s⟩⟩ := h
  let : PartialOrder I := order
  exact ⟨I, hI, order, ⟨AffineStratification.ofIso e.symm s⟩⟩

private lemma isCompact_strata {X : Scheme.{u}} {I : Type v} [PartialOrder I]
    (s : AffineStratification X I) (i : I) : IsCompact (s.strata i) := by
  let hLC := s.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i
  have : IsAffine (reducedInducedScheme (s.strata i) hLC) := s.isAffine i
  have hc := isCompact_range (reducedInducedInclusion (s.strata i) hLC).continuous
  rwa [range_reducedInducedInclusion] at hc

/-- On a stratum of an affine stratification, the intersection of two affine opens of the
ambient scheme is quasi-compact. -/
private lemma isCompact_strata_inter_inter {X : Scheme.{u}} {I : Type v} [PartialOrder I]
    (s : AffineStratification X I) (U V : X.affineOpens) (i : I) :
    IsCompact (s.strata i ∩ (U : Set X) ∩ (V : Set X)) := by
  let hLC := s.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i
  let f := reducedInducedInclusion (s.strata i) hLC
  have : IsAffine (reducedInducedScheme (s.strata i) hLC) := s.isAffine i
  have : IsAffineHom f := s.isAffineHom i
  have himage : f.base '' (f.base ⁻¹' ((U : Set X) ∩ V)) = s.strata i ∩ (U : Set X) ∩ V := by
    rw [Set.image_preimage_eq_inter_range, range_reducedInducedInclusion, Set.inter_comm,
      Set.inter_assoc]
  rw [← himage]
  exact ((U.2.preimage f).inf (V.2.preimage f)).isCompact.image f.continuous

/-- A scheme has an affine stratification indexed by a finite poset if and only if it is
quasi-compact and quasi-separated. -/
@[stacks 0F2U]
theorem hasFiniteAffineStratification_iff (X : Scheme.{u}) :
    HasFiniteAffineStratification.{u, v} X ↔ (CompactSpace X ∧ QuasiSeparatedSpace X) := by
  constructor
  · rintro ⟨I, hI, order, ⟨s⟩⟩
    let : PartialOrder I := order
    have hcover : (⋃ i, s.strata i) = Set.univ :=
      s.isLocallyFiniteStratification.isStratification.isPartition.cover
    refine ⟨isCompact_univ_iff.mp (hcover ▸ isCompact_iUnion (isCompact_strata s)),
      quasiSeparatedSpace_iff_forall_affineOpens.2 fun U V => ?_⟩
    have h := isCompact_iUnion (isCompact_strata_inter_inter s U V)
    rwa [← Set.iUnion_inter, ← Set.iUnion_inter, hcover, Set.univ_inter] at h
  · rintro ⟨hcompact, hqs⟩
    let : QuasiSeparatedSpace X := hqs
    let P : X.Opens → Prop := fun W => HasFiniteAffineStratification.{u, v} W.toScheme
    have h₁ : ∀ W : X.Opens, IsAffineOpen W → P W := fun W hW =>
      have : IsAffine W.toScheme := hW
      ⟨ULift.{v} Unit, inferInstance, inferInstance, ⟨AffineStratification.ofIsAffine W.toScheme⟩⟩
    have h₂ : ∀ W₁ W₂ : X.Opens, IsCompact (W₁ : Set X) → IsAffineOpen W₂ →
        P W₁ → P W₂ → P (W₁ ⊓ W₂) → P (W₁ ⊔ W₂) := by
      intro W₁ W₂ _ hW₂ hP₁ _ hP₁₂
      obtain ⟨I, hI, orderI, ⟨sU⟩⟩ := hP₁
      let : PartialOrder I := orderI
      obtain ⟨J, hJ, orderJ, ⟨sUV⟩⟩ := hP₁₂
      let : PartialOrder J := orderJ
      have : Finite (WithBot J) := inferInstanceAs (Finite (Option J))
      have : Finite (WithBot (I × WithBot J)) :=
        inferInstanceAs (Finite (Option (I × WithBot J)))
      exact ⟨WithBot (I × WithBot J), inferInstance, inferInstance,
        ⟨AffineStratification.ofSup W₁ W₂ hW₂ sU sUV⟩⟩
    exact hasFiniteAffineStratification_of_iso (Scheme.topIso X)
      (Stacks.AlgebraicGeometry.CompactOpenInduction.top h₁ h₂)

end AlgebraicGeometry

end
