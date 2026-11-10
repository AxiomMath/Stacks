module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.TotalFractionRing
public import StacksFrontier.RingTheory.GeometricallyIntegral.NowhereDenseFibreAux
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# The spectrum of the total ring of fractions of an affine scheme

Let `T` be a reduced, locally Noetherian affine scheme and let `A = Γ(T, ⊤)`, a reduced
Noetherian ring. The spectrum of the total ring of fractions `Q(A)` maps to `T`, its image
consists of generic points of irreducible components of `T`, and hence it lies in every dense
open subset of `T`.

## Main definitions

* `AlgebraicGeometry.Scheme.fromSpecTotalFractionRing` is the morphism from the spectrum of the
  total ring of fractions of the global sections of an affine scheme to that scheme.

## Main results

* `exists_mem_minimalPrimes_of_notMem_nonZeroDivisors`: in a reduced ring every element which is
  not a nonzerodivisor lies in a minimal prime.
* `PrimeSpectrum.mem_genericPoints_of_disjoint_nonZeroDivisors`: a prime of a reduced
  Noetherian ring disjoint from the nonzerodivisors is a generic point of the spectrum.
* `AlgebraicGeometry.Scheme.mem_genericPoints_fromSpecTotalFractionRing`: the image of the
  morphism consists of generic points.
* `AlgebraicGeometry.Scheme.fromSpecTotalFractionRing_mem_of_dense`: the image of the morphism
  lies in every dense open subset.
* `AlgebraicGeometry.Scheme.nonZeroDivisors_le_comap_germ_top`: on an affine scheme the germ at
  a point carries nonzerodivisors to nonzerodivisors.

## References

* [Stacks Project, Tag 00EW](https://stacks.math.columbia.edu/tag/00EW)
* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
* [Stacks Project, Tag 02LX](https://stacks.math.columbia.edu/tag/02LX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

/-- In a reduced ring every element which is not a nonzerodivisor lies in a minimal prime. -/
theorem exists_mem_minimalPrimes_of_notMem_nonZeroDivisors (A : Type u) [CommRing A]
    [IsReduced A] {a : A} (ha : a ∉ A⁰) : ∃ q ∈ minimalPrimes A, a ∈ q := by
  rw [mem_nonZeroDivisors_iff_left] at ha
  simp only [not_forall] at ha
  obtain ⟨y, hay, hy0⟩ := ha
  exact zeroDivisor_imp_mem_minimalPrime A a ⟨y, hy0, hay⟩

/-- A prime ideal of a reduced Noetherian ring which is disjoint from the nonzerodivisors is a
generic point of the spectrum. -/
theorem PrimeSpectrum.mem_genericPoints_of_disjoint_nonZeroDivisors {A : Type u} [CommRing A]
    [IsReduced A] [IsNoetherianRing A] {p : PrimeSpectrum A}
    (hp : Disjoint (A⁰ : Set A) (p.asIdeal : Set A)) :
    p ∈ genericPoints (PrimeSpectrum A) := by
  have _ : p.asIdeal.IsPrime := p.isPrime
  have hmin : p.asIdeal ∈ minimalPrimes A :=
    mem_minimalPrimes_of_disjoint_nonZeroDivisors (minimalPrimes.finite_of_isNoetherianRing A)
      (fun _ ha => exists_mem_minimalPrimes_of_notMem_nonZeroDivisors A ha) p.asIdeal hp.symm
  change closure ({p} : Set (PrimeSpectrum A)) ∈ irreducibleComponents (PrimeSpectrum A)
  rw [PrimeSpectrum.closure_singleton]
  exact PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents.mpr
    (by rw [p.isPrime.radical]; exact hmin)

namespace AlgebraicGeometry

/-- The morphism from the spectrum of the total ring of fractions of the global sections of an
affine scheme to that scheme. -/
noncomputable def Scheme.fromSpecTotalFractionRing (T : Scheme.{u}) [IsAffine T] :
    Spec (CommRingCat.of (FractionRing Γ(T, ⊤))) ⟶ T :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤)))) ≫ T.isoSpec.inv

/-- On an affine scheme the germ at a point carries nonzerodivisors of the global sections to
nonzerodivisors of the local ring. -/
theorem Scheme.nonZeroDivisors_le_comap_germ_top (T : Scheme.{u}) [IsAffine T] (t : T) :
    (Γ(T, ⊤))⁰ ≤ ((↥(T.presheaf.stalk t))⁰).comap (T.presheaf.germ ⊤ t trivial).hom := by
  intro a ha
  let : Algebra Γ(T, ⊤) ↥(T.presheaf.stalk t) :=
    TopCat.Presheaf.algebra_section_stalk T.presheaf (⟨t, trivial⟩ : ((⊤ : T.Opens)))
  have : IsLocalization.AtPrime ↥(T.presheaf.stalk t)
      ((isAffineOpen_top T).primeIdealOf (⟨t, trivial⟩ : ((⊤ : T.Opens)))).asIdeal :=
    (isAffineOpen_top T).isLocalization_stalk _
  exact IsLocalization.nonZeroDivisors_le_comap
    (M := ((isAffineOpen_top T).primeIdealOf
      (⟨t, trivial⟩ : ((⊤ : T.Opens)))).asIdeal.primeCompl)
    (S := ↥(T.presheaf.stalk t)) ha

/-- The image of the spectrum of the total ring of fractions of a reduced, locally Noetherian
affine scheme consists of generic points of irreducible components. -/
theorem Scheme.mem_genericPoints_fromSpecTotalFractionRing (T : Scheme.{u}) [IsAffine T]
    [IsReduced T] [IsLocallyNoetherian T]
    (z : Spec (CommRingCat.of (FractionRing Γ(T, ⊤)))) :
    T.fromSpecTotalFractionRing.base z ∈ genericPoints T := by
  have _ : IsNoetherianRing Γ(T, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩
  have hz : (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤))))).base z ∈
      genericPoints (PrimeSpectrum Γ(T, ⊤)) := by
    refine PrimeSpectrum.mem_genericPoints_of_disjoint_nonZeroDivisors ?_
    have hrange := PrimeSpectrum.localization_comap_range
      (S := FractionRing Γ(T, ⊤)) (R := Γ(T, ⊤)) (Γ(T, ⊤))⁰
    have : (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤))))).base z ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤)))) :=
      ⟨z, rfl⟩
    rwa [hrange] at this
  have := (Scheme.homeoOfIso T.isoSpec.symm).mem_genericPoints hz
  rwa [show ((Scheme.homeoOfIso T.isoSpec.symm)
    ((Spec.map (CommRingCat.ofHom
      (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤))))).base z) : T) =
      T.fromSpecTotalFractionRing.base z from rfl] at this

/-- The image of the spectrum of the total ring of fractions of a reduced, locally Noetherian
affine scheme lies in every dense open subset. -/
theorem Scheme.fromSpecTotalFractionRing_mem_of_dense (T : Scheme.{u}) [IsAffine T]
    [IsReduced T] [IsLocallyNoetherian T] {D : Set T} (hD : IsOpen D) (hd : Dense D)
    (z : Spec (CommRingCat.of (FractionRing Γ(T, ⊤)))) :
    T.fromSpecTotalFractionRing.base z ∈ D :=
  T.mem_of_mem_genericPoints_of_dense hD hd (T.mem_genericPoints_fromSpecTotalFractionRing z)

end AlgebraicGeometry

end
