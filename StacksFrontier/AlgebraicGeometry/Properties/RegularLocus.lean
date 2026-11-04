module

public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension

/-!
# Regularity of a locally Noetherian scheme is emptiness of its singular locus

The two notions of regularity available for a scheme are compared here. One asks that every
point have an affine open neighbourhood whose ring of sections is a regular ring; the other,
pointwise, asks that every local ring be a regular local ring, that is, that the singular
locus be empty. On a locally Noetherian scheme the two agree.

## Main results

* `AlgebraicGeometry.isRegular_iff_singularLocus_eq_empty` — a locally Noetherian scheme is
  regular exactly when its singular locus is empty.
* `AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk` — on any scheme, regularity gives a
  regular local ring at every point.
* `AlgebraicGeometry.isRegular_of_singularLocus_eq_empty` — the converse direction, which is
  where local Noetherianness is used.

## Implementation notes

Each direction passes through the identification of the stalk at a point of an affine open with
a localization of the ring of sections at the corresponding prime. In one direction the prime is
`AlgebraicGeometry.IsAffineOpen.primeIdealOf` of the point, and the transfer of regularity to an
arbitrary model of the localization is
`IsRegularRing.isRegularLocalRing_of_isLocalization`. In the other direction the point is
produced from the prime by `AlgebraicGeometry.IsAffineOpen.fromSpec`, whose range is the affine
open, and the identification is `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk'`; the
affine open itself is supplied by the basis of affine opens, and local Noetherianness is what
makes `Mathlib`'s `isRegularRing_iff` applicable to its ring of sections.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A regular scheme has empty singular locus. -/
public theorem singularLocus_eq_empty_of_isRegular {X : Scheme.{u}} (hX : IsRegular X) :
    singularLocus X = ∅ :=
  Set.eq_empty_of_forall_notMem fun x hx ↦ hx (IsRegular.isRegularLocalRing_stalk hX x)

/-- A locally Noetherian scheme whose local rings are all regular is regular. -/
public theorem isRegular_of_singularLocus_eq_empty (X : Scheme.{u}) [IsLocallyNoetherian X]
    (h : singularLocus X = ∅) : IsRegular X := by
  have hreg : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y) := by
    intro y
    by_contra hy
    have hmem : y ∈ singularLocus X := hy
    rw [h] at hmem
    exact hmem
  intro x
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine ⟨⟨V, hV⟩, hxV, ?_⟩
  have _ : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  rw [isRegularRing_iff]
  intro p hp
  have hmemV : hV.fromSpec (⟨p, hp⟩ : PrimeSpectrum Γ(X, V)) ∈ V := by
    have hmem : hV.fromSpec (⟨p, hp⟩ : PrimeSpectrum Γ(X, V)) ∈ Set.range hV.fromSpec :=
      Set.mem_range_self _
    rwa [hV.range_fromSpec] at hmem
  let _ : Algebra Γ(X, V) (X.presheaf.stalk (hV.fromSpec (⟨p, hp⟩ : PrimeSpectrum Γ(X, V)))) :=
    X.presheaf.algebra_section_stalk ⟨_, hmemV⟩
  let _ : IsLocalization.AtPrime
      (X.presheaf.stalk (hV.fromSpec (⟨p, hp⟩ : PrimeSpectrum Γ(X, V)))) p :=
    hV.isLocalization_stalk' ⟨p, hp⟩ hmemV
  let _ := hreg (hV.fromSpec (⟨p, hp⟩ : PrimeSpectrum Γ(X, V)))
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl
      (X.presheaf.stalk (hV.fromSpec (⟨p, hp⟩ : PrimeSpectrum Γ(X, V))))
      (Localization.AtPrime p)).toRingEquiv

/-- A locally Noetherian scheme is regular exactly when its singular locus is empty. -/
public theorem isRegular_iff_singularLocus_eq_empty (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsRegular X ↔ singularLocus X = ∅ :=
  ⟨singularLocus_eq_empty_of_isRegular, isRegular_of_singularLocus_eq_empty X⟩

end AlgebraicGeometry

end
