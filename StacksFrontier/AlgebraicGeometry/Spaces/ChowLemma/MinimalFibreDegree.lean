module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeClosedStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable

/-!
# The minimal fibre degree of a chart, and the open locus on which it is attained

The proof of Stacks 089J, Chow's lemma for algebraic spaces, begins by choosing a surjective
étale chart `W ⟶ X` of the algebraic space with universally bounded fibres, taking the *least*
bound `d` on the fibre degrees, and observing that the locus where the degree equals `d` is a
nonempty open subset `U` of the point set of `X`, over which the chart is finite locally free
of degree exactly `d`.

This file proves that step. The input is the degree stratification of Stacks 07S8,
`AlgebraicGeometry.Space.exists_closedChain_isFiniteLocallyFreeOfRank`, which produces an
increasing chain of closed subsets `∅ = Z 0 ⊆ Z 1 ⊆ ⋯` reaching the whole point set, whose
consecutive difference `Z (r + 1) ∖ Z r` is the locus of fibre degree `r`. Choosing the index
at which the chain first reaches the whole point set makes the top stratum an open set, and
minimality of that index makes it nonempty.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_minimal_closedChain_isFiniteLocallyFreeOfRank`: the degree
  stratification of Stacks 07S8, with the length of the chain chosen least — so that the chain
  reaches the whole point set at index `d + 1` and not before.
* `AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_of_minimal_degree`: the
  nonempty open locus of the minimal degree, with its universal characterization: a morphism
  into `X` from an algebraic space has finite locally free chart base change of degree `d`
  exactly when its image lands in that open locus.

## What is and is not proved

Stacks 089J is **not** proved here, and no declaration in this file carries a Stacks
attribute: choosing the minimal degree bound is an unlabelled step of the proof of Stacks
089J, and the stratification it is applied to is Stacks 07S8, already carried by
`AlgebraicGeometry.Space.exists_closedChain_isFiniteLocallyFreeOfRank`.

Nonemptiness of the open locus needs the point set of `X` to be nonempty: the degree bound `0`
is the least one when `X` has no points, and then the locus of degree `0` is the whole — empty
— point set. That hypothesis is harmless in Stacks 089J, where the empty algebraic space is
covered by the empty scheme.

The open locus is produced as a subset of the point set `AlgebraicGeometry.Space.points`, in
the topology `AlgebraicGeometry.Space.pointTopology` of Stacks 03BX, exactly as in Stacks
07S8; it is not equipped with the reduced induced algebraic space structure of Stacks 047X,
which Stacks 089J introduces only on the *complement*.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The degree stratification of Stacks 07S8, with the degree bound chosen least.** A flat,
locally finitely presented, separated, locally quasi-finite morphism from a scheme to an
algebraic space with universally bounded fibres admits a finite increasing chain of closed
subsets of the point set which reaches the whole point set at index `d + 1` and *not* at index
`d`, and whose strata are the loci over which the base change of the morphism is finite
locally free of a fixed degree.

The index `d` is the least degree bounding all the fibre degrees, which is what the proof of
Stacks 089J picks. -/
theorem exists_minimal_closedChain_isFiniteLocallyFreeOfRank
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : BigFppfOver B S hS)
    (g : yoneda.obj W ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hflat : IsFlat B S hS g) (hlfp : IsLocallyOfFinitePresentation B S hS g)
    (hsep : IsSeparated B S hS g) (hlqf : IsLocallyQuasiFinite B S hS g)
    (hbound : HasUniversallyBoundedFibers B S hS W g) (hne : Nonempty (points B S hS X)) :
    ∃ (d : ℕ) (Z : ℕ → Set (points B S hS X)), Z 0 = ∅ ∧ (∀ r, IsClosed (Z r)) ∧ Monotone Z ∧
      Z (d + 1) = Set.univ ∧ Z d ≠ Set.univ ∧
      ∀ r : ℕ, r ≤ d → ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X),
        IsAlgebraicSpace B S hS T →
        ∀ (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T),
          IsPullback pr₁ pr₂ g hm →
          ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
              (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
            Set.range (pointsMap B S hS T hm) ⊆ Z (r + 1) \ Z r) := by
  obtain ⟨n, Z, hZ0, hZcl, hZmono, hZuniv, hZchar⟩ :=
    exists_closedChain_isFiniteLocallyFreeOfRank B S hS X W g hX hflat hlfp hsep hlqf hbound
  have hex : ∃ m : ℕ, Z (m + 1) = Set.univ := ⟨n, hZuniv⟩
  classical
  refine ⟨Nat.find hex, Z, hZ0, hZcl, hZmono, Nat.find_spec hex, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · obtain ⟨p⟩ := hne
      rw [h0, hZ0]
      intro hcontra
      rw [Set.eq_univ_iff_forall] at hcontra
      exact hcontra p
    · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
      rw [hk]
      exact Nat.find_min hex (by omega)
  · exact fun r hr => hZchar r (le_trans hr (Nat.find_le hZuniv))

/-- **The nonempty open locus of the minimal fibre degree.** For a flat, locally finitely
presented, separated, locally quasi-finite chart `W ⟶ X` with universally bounded fibres of an
algebraic space with at least one point, there is a degree `d` and a nonempty *open* subset
`U` of the point set of `X` such that a morphism into `X` from an algebraic space has chart
base change finite locally free of degree `d` exactly when its image lands in `U`.

The open set is the complement of the closed set `Z d` of
`AlgebraicGeometry.Space.exists_minimal_closedChain_isFiniteLocallyFreeOfRank`, that is, the
top stratum of the degree stratification; it is open because the chain has already reached the
whole point set at the next index, and nonempty because it has not reached it at this one.

This is the choice of `d` and `U` with which the proof of Stacks 089J begins: `U` is the open
over which the chart is finite locally free — hence, the chart being étale, finite étale — of
degree exactly `d`. -/
theorem exists_isOpen_isFiniteLocallyFreeOfRank_of_minimal_degree
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : BigFppfOver B S hS)
    (g : yoneda.obj W ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hflat : IsFlat B S hS g) (hlfp : IsLocallyOfFinitePresentation B S hS g)
    (hsep : IsSeparated B S hS g) (hlqf : IsLocallyQuasiFinite B S hS g)
    (hbound : HasUniversallyBoundedFibers B S hS W g) (hne : Nonempty (points B S hS X)) :
    ∃ (d : ℕ) (U : Set (points B S hS X)), IsOpen U ∧ U.Nonempty ∧
      ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X), IsAlgebraicSpace B S hS T →
        ∀ (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T),
          IsPullback pr₁ pr₂ g hm →
          ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} d)
              (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
            Set.range (pointsMap B S hS T hm) ⊆ U) := by
  obtain ⟨d, Z, -, hZcl, -, hZtop, hZd, hZchar⟩ :=
    exists_minimal_closedChain_isFiniteLocallyFreeOfRank B S hS X W g hX hflat hlfp hsep hlqf
      hbound hne
  refine ⟨d, (Z d)ᶜ, (hZcl d).isOpen_compl, Set.nonempty_compl.2 hZd, ?_⟩
  intro T hm hT Pp pr₁ pr₂ hsq
  have h := hZchar d le_rfl T hm hT Pp pr₁ pr₂ hsq
  rw [hZtop] at h
  rwa [Set.compl_eq_univ_sdiff]

/-- **The minimal fibre degree of a separated étale chart of a reasonable algebraic space.**
This is `AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_of_minimal_degree`
with the hypotheses it is applied with in the proof of Stacks 089J: the chart is an *affine*
étale chart, which is flat by Stacks 0467, locally of finite presentation by Stacks 0468 and
locally quasi-finite by Stacks 03XU, and its fibres are universally bounded because the
algebraic space is reasonable — which is condition (2) of Stacks 03JT, and what the chain of
conditions of Stacks 03JX delivers for a quasi-separated algebraic space.

Separatedness of the chart is kept as a hypothesis: in Stacks 089J it holds because the chart
is an affine scheme separated over the base and the algebraic space is separated over the
base, so that the chart is separated over the algebraic space. -/
theorem exists_isOpen_isFiniteLocallyFreeOfRank_of_minimal_degree_of_isEtale
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : BigFppfOver B S hS)
    (g : yoneda.obj W ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hR : IsReasonableSpace B S hS X)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (hgEt : IsEtale B S hS g) (hsep : IsSeparated B S hS g)
    (hne : Nonempty (points B S hS X)) :
    ∃ (d : ℕ) (U : Set (points B S hS X)), IsOpen U ∧ U.Nonempty ∧
      ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X), IsAlgebraicSpace B S hS T →
        ∀ (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T),
          IsPullback pr₁ pr₂ g hm →
          ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} d)
              (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
            Set.range (pointsMap B S hS T hm) ⊆ U) :=
  exists_isOpen_isFiniteLocallyFreeOfRank_of_minimal_degree B S hS X W g hX
    (isFlat_of_isEtale B S hS hgEt) (isLocallyOfFinitePresentation_of_isEtale B S hS hgEt)
    hsep (isLocallyQuasiFinite_of_isEtale B S hS hX hgEt)
    (hR W hW g ((isEtale_iff_presheaf_of_yoneda B S hS g).1 hgEt)) hne

end AlgebraicGeometry.Space

end
