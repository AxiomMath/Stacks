module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.Basic
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.AffineComplement
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.HighBoundTFAE

/-!
# Bounding the cohomological dimension by an affine cover of the complement

Let `I` be a finitely generated ideal of a commutative ring `A` and let `Y = V(I)` be its zero
locus in `X = Spec A`. If the open complement `U = X ∖ Y` is covered by `c` affine opens, then
the cohomological dimension `cd(A, I)` of Stacks 0DX8 is at most `c`.

An open subscheme of an affine scheme is separated, hence has affine diagonal, and the affine
opens of `U` are the affine opens of `X` contained in `U`; so the vanishing theorem of
Stacks 01XI applies on `U` and gives `H^n(U, ℱ) = 0` for every quasi-coherent `ℱ` and every
`n ≥ c`. That is the third of the equivalent conditions of Stacks 0DX7 for the bound `c`, whose
first condition is the vanishing of `H^i_Y(A)` for `i > c`. The degenerate case `c = 0` is the
empty cover, where `Y` is the whole spectrum and the bound `0` comes from the generator bound of
Stacks 0DX9 (2) for the empty family.

## Main results

* `AlgebraicGeometry.Scheme.Opens.isSeparated_toScheme` — an open subscheme of a separated
  scheme is separated.
* `Stacks.LocalCohomology.isZero_hgroup_complZeroLocusOpen_of_affine_cover` — the cohomology of
  a quasi-coherent module on `Spec A ∖ V(I)` vanishes in every degree at least the size of an
  affine cover of that open.
* `Stacks.LocalCohomology.cohomologicalDimension_le_card_affine_cover` — **part (3) of
  Stacks 0DX9**.

## References

* [Stacks Project, Tag 0DX9](https://stacks.math.columbia.edu/tag/0DX9)
* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Scheme.Opens

/-- An open subscheme of a separated scheme is separated: its structure morphism factors as the
open immersion followed by the structure morphism of the ambient scheme. -/
theorem isSeparated_toScheme {X : Scheme.{u}} [X.IsSeparated] (U : X.Opens) :
    U.toScheme.IsSeparated :=
  ⟨by rw [← terminal.comp_from U.ι]; infer_instance⟩

end AlgebraicGeometry.Scheme.Opens

namespace Stacks.LocalCohomology

/-- Quasi-coherent cohomology on `Spec A ∖ V(I)` vanishes in every degree at least the number of
members of an affine open cover of that open: the complement of a zero locus in an affine scheme
is separated, so the vanishing theorem of Stacks 01XI applies to it. -/
theorem isZero_hgroup_complZeroLocusOpen_of_affine_cover
    (A : Type u) [CommRing A] (I : Ideal A)
    {c : ℕ} (V : Fin c → (Spec (CommRingCat.of A)).Opens)
    (hV : ∀ i, IsAffineOpen (V i))
    (hcov : ⨆ i, V i = complZeroLocusOpen A I)
    (F : ((complZeroLocusOpen A I) : Scheme).Modules) (hF : F.IsQuasicoherent)
    (n : ℕ) (hn : c ≤ n) :
    IsZero (Hgroup ((complZeroLocusOpen A I) : Scheme).ringCatSheaf ⊤ n F) := by
  have hsep : (complZeroLocusOpen A I).toScheme.IsSeparated :=
    Scheme.Opens.isSeparated_toScheme _
  have hqc := hF
  refine Stacks.Cohomology.AffineCover.isZero_cohomology_of_finite_affine_cover
    (complZeroLocusOpen A I).toScheme (fun i => (complZeroLocusOpen A I).ι ⁻¹ᵁ V i)
    (fun i => (hV i).preimage_of_isOpenImmersion _ ?_) ?_ F n hn
  · rw [Scheme.Opens.opensRange_ι]
    exact hcov ▸ le_iSup V i
  · rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Opens.ι_preimage_self]

/-- An ideal whose zero locus has empty complement has zero locus the whole spectrum. -/
theorem zeroLocus_eq_univ_of_isEmpty_affine_cover
    (A : Type u) [CommRing A] (I : Ideal A)
    (V : Fin 0 → (Spec (CommRingCat.of A)).Opens)
    (hcov : ⨆ i, V i = complZeroLocusOpen A I) :
    PrimeSpectrum.zeroLocus (I : Set A) = Set.univ := by
  have h : complZeroLocusOpen A I = ⊥ := by simpa using hcov.symm
  rw [Set.eq_univ_iff_forall]
  intro x
  by_contra hx
  have hmem : x ∈ (complZeroLocusOpen A I).carrier := hx
  rw [h] at hmem
  exact hmem

/-- **Stacks Project, Tag 0DX9 (3).** The cohomological dimension of a finitely generated ideal
`I` of `A` is at most the number of members of an affine open cover of `Spec A ∖ V(I)`. -/
@[stacks 0DX9 "part (3): the bound by an affine cover of the complement"]
theorem cohomologicalDimension_le_card_affine_cover
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    {c : ℕ} (V : Fin c → (Spec (CommRingCat.of A)).Opens)
    (hV : ∀ i, IsAffineOpen (V i))
    (hcov : ⨆ i, V i = complZeroLocusOpen A I) :
    cohomologicalDimension A I hI ≤ (c : ℤ) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simpa using cohomologicalDimension_nonpos_of_zeroLocus_eq_univ A I hI
      (zeroLocus_eq_univ_of_isEmpty_affine_cover A I V hcov)
  · refine cohomologicalDimension_le A I hI (c : ℤ) ⟨by omega, ?_⟩
    have h := (localCohomology_vanishing_tfae.{u, u} A I hI (c : ℤ) (by omega)).out 3 1
    refine h.mp ⟨fun hneg => absurd hneg (by omega), fun hzero => absurd hzero (by omega), ?_⟩
    intro _ _ F hF n hn
    exact isZero_hgroup_complZeroLocusOpen_of_affine_cover A I V hV hcov F hF n
      (by exact_mod_cast hn)

end Stacks.LocalCohomology

end
