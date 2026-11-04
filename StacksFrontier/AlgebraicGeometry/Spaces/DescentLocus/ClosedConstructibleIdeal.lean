module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.DescentTopology
public import StacksFrontier.Topology.Constructible.Homeomorph

/-!
# Closed constructible subsets of an affine scheme are cut out by finitely generated ideals

Let `U` be an affine scheme and `C ⊆ U` a closed constructible subset. Its complement is an
open constructible subset of the spectral space `U`, hence quasi-compact, hence of the form
`D(J)` for a finitely generated ideal `J` of `Γ(U, ⊤)`. A morphism `t : T ⟶ U` from an affine
scheme then misses `C` exactly when `J` generates the unit ideal of `Γ(T, ⊤)`.

## Main results

* `AlgebraicGeometry.Space.exists_fg_zeroLocus_eq_of_isClosed_of_isConstructible`: a closed
  constructible subset of `Spec R` is `V(J)` for a finitely generated ideal `J`.
* `AlgebraicGeometry.Space.range_comap_subset_compl_zeroLocus_iff`: the image of
  `Spec A ⟶ Spec R` misses `V(J)` exactly when `J A = A`.
* `AlgebraicGeometry.Space.exists_fg_ideal_range_subset_compl_iff`: the scheme form, for a
  closed constructible subset of an affine scheme and test morphisms from affine schemes.
-/

@[expose] public section

open CategoryTheory PrimeSpectrum Topology

universe u

namespace AlgebraicGeometry.Space

/-- A closed constructible subset of the spectrum of a ring is the zero locus of a finitely
generated ideal. -/
theorem exists_fg_zeroLocus_eq_of_isClosed_of_isConstructible {R : Type*} [CommRing R]
    {C : Set (PrimeSpectrum R)} (hC : IsClosed C) (hC' : IsConstructible C) :
    ∃ J : Ideal R, J.FG ∧ zeroLocus (J : Set R) = C := by
  have hcomp : IsCompact Cᶜ :=
    ConnectedComponentSection.isCompact_of_isConstructible (isConstructible_compl.2 hC')
  obtain ⟨J, hJ, e⟩ := isCompact_isOpen_iff_ideal.1 ⟨hcomp, hC.isOpen_compl⟩
  exact ⟨J, hJ, compl_injective e⟩

/-- The image of `Spec A ⟶ Spec R` misses the zero locus of an ideal `J` of `R` exactly when the
extension of `J` to `A` is the unit ideal. -/
theorem range_comap_subset_compl_zeroLocus_iff {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (J : Ideal R) :
    Set.range (comap φ) ⊆ (zeroLocus (J : Set R))ᶜ ↔ J.map φ = ⊤ := by
  rw [← zeroLocus_empty_iff_eq_top, Ideal.map, zeroLocus_span, ← preimage_comap_zeroLocus,
    Set.eq_empty_iff_forall_notMem, Set.range_subset_iff]
  rfl

/-- **Closed constructible subsets of an affine scheme are cut out by finitely generated
ideals.** For a closed constructible subset `C` of an affine scheme `U` there is a finitely
generated ideal `J` of `Γ(U, ⊤)` such that a morphism `t : T ⟶ U` from an affine scheme has
image disjoint from `C` exactly when `J` generates the unit ideal of `Γ(T, ⊤)`. -/
theorem exists_fg_ideal_range_subset_compl_iff {U : Scheme.{u}} [IsAffine U] {C : Set U}
    (hC : IsClosed C) (hC' : IsConstructible C) :
    ∃ J : Ideal Γ(U, ⊤), J.FG ∧ ∀ (T : Scheme.{u}) [IsAffine T] (t : T ⟶ U),
      (Set.range t.base ⊆ Cᶜ ↔ J.map t.appTop.hom = ⊤) := by
  let h : U ≃ₜ Spec Γ(U, ⊤) := Scheme.homeoOfIso U.isoSpec
  have hC₁ : IsClosed (h.symm ⁻¹' C) := hC.preimage h.symm.continuous
  have hC₂ : IsConstructible (h.symm ⁻¹' C) :=
    (h.symm.isConstructible_preimage_iff C).2 hC'
  obtain ⟨J, hJ, hJC⟩ := exists_fg_zeroLocus_eq_of_isClosed_of_isConstructible hC₁ hC₂
  refine ⟨J, hJ, fun T _ t => ?_⟩
  rw [← range_comap_subset_compl_zeroLocus_iff, hJC]
  have hrange : Set.range t.base = Set.range (Spec.map t.appTop ≫ U.isoSpec.inv).base := by
    have hs : Function.Surjective T.isoSpec.inv.base :=
      (Scheme.homeoOfIso T.isoSpec.symm).surjective
    rw [Scheme.isoSpec_inv_naturality, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      hs.range_eq, Set.image_univ]
  rw [hrange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  constructor
  · rintro hsub _ ⟨p, rfl⟩ hp
    exact hsub ⟨_, ⟨p, rfl⟩, rfl⟩ hp
  · rintro hsub _ ⟨_, ⟨p, rfl⟩, rfl⟩ hp
    exact hsub ⟨p, rfl⟩ hp

end AlgebraicGeometry.Space
