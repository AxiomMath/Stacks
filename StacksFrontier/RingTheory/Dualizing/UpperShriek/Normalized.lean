module

public import Mathlib.RingTheory.KrullDimension.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.MinimalPrimeNonvanishing
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.MvPolynomial.MaximalIdeal
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionSurjective
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Dualizing
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialExtension
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso

import all StacksFrontier.RingTheory.Dualizing.MinimalPrimeNonvanishing

/-!
# Algebraic upper shriek and normalized dualizing complexes

Let `φ : R → A` be a finite type homomorphism of Noetherian rings with `R` local, let `m ⊆ A` be
a maximal ideal lying over the maximal ideal of `R` and let `ω_R` be a normalized dualizing
complex for `R`.  Then `φ^!(ω_R)_m` is a normalized dualizing complex for `A_m`.

Over a Noetherian local ring `A` of dimension `d`, a dualizing complex is normalized exactly when
`-d` is the smallest index in which it has nonvanishing cohomology.

## Main results

* `Dualizing.isZero_homology_of_lt_neg_ringKrullDim` — a normalized dualizing complex has no
  cohomology below degree `-dim(A)`.
* `Dualizing.nontrivial_homology_neg_ringKrullDim` — and it does have cohomology in degree
  `-dim(A)`.
* `Dualizing.isNormalizedDualizingComplex_of_homology_bounds` — the converse: a dualizing
  complex whose cohomology vanishes below `-dim(A)` and is nonzero in degree `-dim(A)` is
  normalized.
* `Dualizing.ringKrullDim_localizationAtPrime_mvPolynomial` — `dim(R[x_1, …, x_n]_m) = dim(R) + n`
  for a maximal ideal `m` lying over the maximal ideal of `R`.
* `Dualizing.PolynomialPresentation.dualizingDimension_derivedExtension` — the polynomial case:
  the dimension function of `ω_R ⊗_R^L P` takes the value `-n` at such an `m`.
* `Dualizing.PolynomialPresentation.upperShriekFunctor_localization_isNormalizedDualizingComplex`
  — for every polynomial presentation of `φ`, `φ^!(ω_R)_m` is a normalized dualizing complex
  for `A_m`.

## Implementation notes

Upper shriek is only defined up to isomorphism, so the main statement is made for an arbitrary
polynomial presentation of `φ`, as in [Stacks, Tag 0BZL]. The module universe is the ring
universe.

## References

* [Stacks Project, Tag 0E9N](https://stacks.math.columbia.edu/tag/0E9N)
* [Stacks Project, Tag 0BZL](https://stacks.math.columbia.edu/tag/0BZL)
* [Stacks Project, Tag 0A7Y](https://stacks.math.columbia.edu/tag/0A7Y)
* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0A7V](https://stacks.math.columbia.edu/tag/0A7V)
* [Stacks Project, Tag 00OP](https://stacks.math.columbia.edu/tag/00OP)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- Shifting reindexes cohomology: `H^i(K⟦n⟧) = H^{n+i}(K)`. -/
noncomputable def homologyShiftIso {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (n i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (K⟦n⟧) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n + i)).obj K :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso n i (n + i) rfl).app K

/-- Nonvanishing of an object of `ModuleCat A` is the negation of being a zero object. -/
private theorem not_isZero_iff_nontrivial {A : Type u} [CommRing A] (M : ModuleCat.{u} A) :
    ¬ Limits.IsZero M ↔ Nontrivial M := by
  rw [ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial]

/-- `H^i(K⟦n⟧)` vanishes if and only if `H^j(K)` does, where `n + i = j`. -/
private theorem isZero_homology_shift_iff {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (n i j : ℤ) (h : n + i = j) :
    Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (K⟦n⟧)) ↔
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K) := by
  subst h
  exact ⟨fun hz => hz.of_iso (homologyShiftIso K n i).symm,
    fun hz => hz.of_iso (homologyShiftIso K n i)⟩

/-- A Noetherian local ring of dimension `d` has maximal ideal of height `d`. -/
private theorem height_maximalIdeal_eq_of_ringKrullDim_eq
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (d : ℕ)
    (hd : ringKrullDim A = (d : WithBot ℕ∞)) :
    (IsLocalRing.maximalIdeal A).height = (d : ℕ∞) := by
  have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [hd] at h
  exact_mod_cast h

/-- A Noetherian local ring of dimension `d` has a minimal prime `p` with `dim(A/p) = d`. -/
theorem exists_minimalPrime_ringKrullDim_quotient_eq
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (d : ℕ)
    (hd : ringKrullDim A = (d : WithBot ℕ∞)) :
    ∃ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal ∧
      ringKrullDim (A ⧸ p.asIdeal) = (d : WithBot ℕ∞) := by
  have hmp : (IsLocalRing.maximalIdeal A).IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  have hheight := height_maximalIdeal_eq_of_ringKrullDim_eq d hd
  obtain ⟨l, hlast, hlen⟩ := (IsLocalRing.maximalIdeal A).exists_ltSeries_length_eq_height
  have hlend : l.length = d := by
    rw [hheight] at hlen
    exact_mod_cast hlen
  have hheight' : Order.height (⟨IsLocalRing.maximalIdeal A, hmp⟩ : PrimeSpectrum A)
      = (d : ℕ∞) := by
    rwa [← PrimeSpectrum.height_eq_orderHeight]
  refine ⟨l.head, ?_, ?_⟩
  · rw [IsMinimalPrime.iff_minimal]
    refine ⟨l.head.isPrime, fun q hq hle => ?_⟩
    by_contra hnot
    have hlt : (⟨q, hq⟩ : PrimeSpectrum A) < l.head :=
      lt_of_le_of_ne hle fun h => hnot (le_of_eq (congrArg PrimeSpectrum.asIdeal h).symm)
    have hbound := Order.length_le_height
      (p := l.cons (⟨q, hq⟩ : PrimeSpectrum A) hlt)
      (x := (⟨IsLocalRing.maximalIdeal A, hmp⟩ : PrimeSpectrum A)) (by
        rw [RelSeries.last_cons, hlast])
    rw [hheight'] at hbound
    have hbound' : ((l.length + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
      simpa [RelSeries.cons_length] using hbound
    have hfin : l.length + 1 ≤ d := by exact_mod_cast hbound'
    omega
  · have hcoh : ringKrullDim (A ⧸ l.head.asIdeal)
        = (Order.coheight l.head : WithBot ℕ∞) := by
      rw [ringKrullDim_quotient,
        show PrimeSpectrum.zeroLocus (R := A) (l.head.asIdeal : Set A) = Set.Ici l.head from rfl,
        Order.coheight_eq_krullDim_Ici]
    have hge : (d : ℕ∞) ≤ Order.coheight l.head := by
      have := Order.length_le_coheight_head (p := l)
      rwa [hlend] at this
    have hle : (Order.coheight l.head : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      rw [← hd]
      exact Order.coheight_le_krullDim l.head
    rw [hcoh]
    exact le_antisymm hle (by exact_mod_cast hge)

/-- A normalized dualizing complex over a Noetherian local ring of dimension `d` has no
cohomology in degrees below `-d`. -/
theorem isZero_homology_of_lt_neg_ringKrullDim
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞)) (i : ℤ) (hi : i < -(d : ℤ)) :
    Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  have hfin : Module.Finite A (ULift.{u} A) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := A) (M := A)).symm
  have hnt : Nontrivial (ULift.{u} A) :=
    (ULift.moduleEquiv (R := A) (M := A)).toEquiv.nontrivial_congr.mpr inferInstance
  have hsupp : Module.supportDim A (ULift.{u} A) = (d : WithBot ℕ∞) := by
    rw [Module.supportDim_eq_of_equiv (ULift.moduleEquiv (R := A) (M := A)),
      Module.supportDim_self_eq_ringKrullDim, hd]
  by_contra hcon
  have hExt : Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (ULift.{u} A))) K i) :=
    (extFromUliftRing.{u, u} K i).toEquiv.nontrivial_congr.mpr
      ((not_isZero_iff_nontrivial _).mp hcon)
  have := ext_degree_mem_Icc_of_nontrivial.{u, u} (A := A) (M := ULift.{u} A) K hK d hsupp i hExt
  exact absurd this.1 (by omega)

/-- A normalized dualizing complex over a Noetherian local ring of dimension `d` has nonzero
cohomology in degree `-d`. -/
theorem nontrivial_homology_neg_ringKrullDim
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞)) :
    Nontrivial
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K) := by
  obtain ⟨p, hp, hpdim⟩ := exists_minimalPrime_ringKrullDim_quotient_eq d hd
  have hloc : Nontrivial (LocalizedModule p.asIdeal.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K)) :=
    (nontrivial_localized_homology_iff_eq_neg_dimension.{u, u} K hK p hp d hpdim
      (-(d : ℤ))).mpr rfl
  by_contra hcon
  have hsub : Subsingleton
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K) :=
    not_nontrivial_iff_subsingleton.mp hcon
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hloc

/-- Shifting by `-0` does not affect being a normalized dualizing complex. -/
private theorem isNormalizedDualizingComplex_of_shift_neg_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (h : IsNormalizedDualizingComplex.{u, u} (K⟦-(0 : ℤ)⟧)) :
    IsNormalizedDualizingComplex.{u, u} K :=
  (isNormalizedDualizingComplex_congr.{u, u} (K := K⟦-(0 : ℤ)⟧) (L := K)
    ((shiftFunctorZero' (DerivedCategory (ModuleCat.{u} A)) (-(0 : ℤ)) (by simp)).app K)).mp h

/-- A dualizing complex over a Noetherian local ring of dimension `d` whose cohomology vanishes
in every degree below `-d` and is nonzero in degree `-d` is normalized. -/
theorem isNormalizedDualizingComplex_of_homology_bounds
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (L : DerivedCategory (ModuleCat.{u} A)) (hL : IsDualizingComplex L)
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞))
    (hvanish : ∀ i : ℤ, i < -(d : ℤ) →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj L))
    (hnonzero : Nontrivial
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj L)) :
    IsNormalizedDualizingComplex.{u, u} L := by
  obtain ⟨n, hn⟩ := exists_isNormalizedDualizingComplex_shift.{u, u} L hL
  have hle : n ≤ 0 := by
    by_contra hgt
    have hnt := nontrivial_homology_neg_ringKrullDim.{u} (L⟦-n⟧) hn d hd
    exact (not_isZero_iff_nontrivial _).mpr hnt
      ((isZero_homology_shift_iff L (-n) (-(d : ℤ)) (-n + -(d : ℤ)) rfl).mpr
        (hvanish _ (by omega)))
  have hge : 0 ≤ n := by
    by_contra hlt
    have hz := isZero_homology_of_lt_neg_ringKrullDim.{u} (L⟦-n⟧) hn d hd
      (n + -(d : ℤ)) (by omega)
    exact (not_isZero_iff_nontrivial _).mpr hnonzero
      ((isZero_homology_shift_iff L (-n) (n + -(d : ℤ)) (-(d : ℤ)) (by omega)).mp hz)
  obtain rfl : n = 0 := le_antisymm hle hge
  exact isNormalizedDualizingComplex_of_shift_neg_zero L hn

/-- Let `R` be a Noetherian local ring of dimension `d` and let `m` be a maximal ideal of
`R[x_1, …, x_n]` lying over the maximal ideal of `R`.  Then `dim(R[x_1, …, x_n]_m) = d + n`. -/
@[ega "IV 5.5.3" "special case", ega "IV 5.6.1" "special case"]
theorem ringKrullDim_localizationAtPrime_mvPolynomial
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) R)) [m.IsMaximal]
    (hlies : m.comap (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)
      = IsLocalRing.maximalIdeal R)
    (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    ringKrullDim (Localization.AtPrime m) = ((d + n : ℕ) : WithBot ℕ∞) := by
  have hImax : (IsLocalRing.maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  have halg : (algebraMap R (MvPolynomial (Fin n) R))
      = (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) := MvPolynomial.algebraMap_eq R (Fin n)
  have hliesover : m.LiesOver (IsLocalRing.maximalIdeal R) := ⟨by
    rw [Ideal.under_def, halg, hlies]⟩
  have hgd : Algebra.HasGoingDown R (MvPolynomial (Fin n) R) := Algebra.HasGoingDown.of_flat
  have hIheight := height_maximalIdeal_eq_of_ringKrullDim_eq d hd
  have hfibre : (m.map (Ideal.Quotient.mk (Ideal.map
      (algebraMap R (MvPolynomial (Fin n) R)) (IsLocalRing.maximalIdeal R)))).height
      = (n : ℕ∞) := by
    rw [halg]
    have hMmax : (m.map (Ideal.Quotient.mk (Ideal.map
        (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)
          (IsLocalRing.maximalIdeal R)))).IsMaximal := by
      refine Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_
      rw [Ideal.mk_ker, Ideal.map_le_iff_le_comap, hlies]
    have he : (MvPolynomial (Fin n) R ⧸ Ideal.map
        (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) (IsLocalRing.maximalIdeal R)) ≃+*
        MvPolynomial (Fin n) (R ⧸ IsLocalRing.maximalIdeal R) :=
      (MvPolynomial.quotientEquivQuotientMvPolynomial
        (IsLocalRing.maximalIdeal R)).symm.toRingEquiv
    have hMemax : (Ideal.map he (m.map (Ideal.Quotient.mk (Ideal.map
        (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)
          (IsLocalRing.maximalIdeal R))))).IsMaximal := inferInstance
    rw [← he.height_map]
    exact @height_maximal_ideal_eq (R ⧸ IsLocalRing.maximalIdeal R)
      (Ideal.Quotient.field _) n _ hMemax
  have hsplit := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (R := R) (S := MvPolynomial (Fin n) R) (IsLocalRing.maximalIdeal R) m
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), hsplit,
    hIheight, hfibre]
  push_cast
  rfl

section BaseChange

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Derived extension of scalars is the total left derived functor of termwise extension of
scalars: the universe lift inside the construction is the identity when the two rings and the
module carrier share a universe. -/
noncomputable def derivedExtensionScalarsObjIso (g : A →+* B)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (StacksDraft.PseudoCoherence.derivedExtensionScalars g).obj K ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        g).functor.obj K := by
  unfold StacksDraft.PseudoCoherence.derivedExtensionScalars
  exact (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    g).functor.mapIso ((uliftSelfIso.{u, u} A).app K)

/-- Derived extension of scalars along a flat ring map commutes with cohomology. -/
noncomputable def derivedExtensionScalarsHomologyObjIso (g : A →+* B) (hg : g.Flat)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars g).obj K) ≅
      (ModuleCat.extendScalars.{u, u, u} g).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso
      (derivedExtensionScalarsObjIso g K) ≪≫
    (CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, u, u} g hg i).app K

/-- Derived extension of scalars commutes with the shift. -/
noncomputable def derivedExtensionScalarsShiftIso (g : A →+* B)
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    (StacksDraft.PseudoCoherence.derivedExtensionScalars g).obj (K⟦n⟧) ≅
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars g).obj K)⟦n⟧ := by
  have hcs : (StacksDraft.PseudoCoherence.derivedExtensionScalars g
      (R := A) (A := B)).CommShift ℤ := by
    unfold StacksDraft.PseudoCoherence.derivedExtensionScalars
    infer_instance
  exact ((StacksDraft.PseudoCoherence.derivedExtensionScalars g).commShiftIso n).app K

end BaseChange

/-- Shifting a dualizing complex by `n` raises its dimension function by `n`. -/
theorem dualizingDimension_shift {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsDualizingComplex K)
    (q : PrimeSpectrum A) (n : ℤ) :
    dualizingDimension.{u, u} (K⟦n⟧) q = dualizingDimension.{u, u} K q + n := by
  refine ((dualizingDimension_eq_iff.{u, u} (K⟦n⟧) (isDualizingComplex_shift K hK n) q
    (dualizingDimension.{u, u} K q + n)).mp ?_).symm
  refine (isNormalizedDualizingComplex_congr.{u, u} ?_).mp (dualizingDimension_spec.{u, u} K hK q)
  refine (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} (Localization.AtPrime q.asIdeal)))
    n (-(dualizingDimension.{u, u} K q + n)) (-dualizingDimension.{u, u} K q)
      (by omega)).app _ ≪≫ ?_
  exact (shiftFunctor _ (-(dualizingDimension.{u, u} K q + n))).mapIso
    (derivedExtensionScalarsShiftIso (algebraMap A (Localization.AtPrime q.asIdeal)) K n).symm

/-- Let `R` be a Noetherian local ring with a normalized dualizing complex `K`, let `p` be a
polynomial presentation with `n` variables and let `m` be a maximal ideal of its polynomial
algebra `P` lying over the maximal ideal of `R`.  Then the dimension function of `K ⊗_R^L P`
takes the value `-n` at `m`; equivalently `(K ⊗_R^L P)_m[n]` is a normalized dualizing complex
over `P_m`. -/
theorem PolynomialPresentation.dualizingDimension_derivedExtension
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsLocalRing R]
    {f : R →+* A} (p : PolynomialPresentation f)
    (m : Ideal p.Poly) [m.IsMaximal]
    (hlies : m.comap (MvPolynomial.C : R →+* p.Poly) = IsLocalRing.maximalIdeal R)
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsNormalizedDualizingComplex.{u, u} K) :
    dualizingDimension.{u, u} (p.derivedExtension.{u, u}.obj K)
        (⟨m, inferInstance⟩ : PrimeSpectrum p.Poly) = -(p.variableCount : ℤ) := by
  obtain ⟨d, hd⟩ := Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim R
  have hgflat : (algebraMap p.Poly (Localization.AtPrime m)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization.AtPrime m) m.primeCompl)
  have hBnoeth : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl (Localization.AtPrime m) inferInstance
  have hL : IsDualizingComplex (p.derivedExtension.{u, u}.obj K) :=
    mvPolynomialBaseChange_isDualizingComplex p.variableCount K hK.1
  have hLB : IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap p.Poly (Localization.AtPrime m))).obj
        (p.derivedExtension.{u, u}.obj K)) :=
    isDualizingComplex_localization m.primeCompl _ hL
  have halgcomp : (algebraMap p.Poly (Localization.AtPrime m)).comp
      (MvPolynomial.C : R →+* p.Poly) = algebraMap R (Localization.AtPrime m) := by
    ext r
    rfl
  have hflatPB : Module.Flat p.Poly (Localization.AtPrime m) :=
    IsLocalization.flat (Localization.AtPrime m) m.primeCompl
  have hflatRB : Module.Flat R (Localization.AtPrime m) :=
    Module.Flat.trans R p.Poly (Localization.AtPrime m)
  have hlocal : IsLocalHom (algebraMap R (Localization.AtPrime m)) := by
    refine ⟨fun r hr => ?_⟩
    by_contra hnu
    have hrm : r ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal r).mpr hnu
    have hCm : (MvPolynomial.C r : p.Poly) ∈ m := by
      rwa [← hlies] at hrm
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime m) m
      (MvPolynomial.C r)).mp hr hCm
  have hff : Module.FaithfullyFlat R (Localization.AtPrime m) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hcomp : ∀ i : ℤ,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.AtPrime m)) i).obj
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars
            (algebraMap p.Poly (Localization.AtPrime m))).obj
            (p.derivedExtension.{u, u}.obj K)) ≅
        (ModuleCat.extendScalars (algebraMap R (Localization.AtPrime m))).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) := by
    intro i
    refine derivedExtensionScalarsHomologyObjIso
      (algebraMap p.Poly (Localization.AtPrime m)) hgflat _ i ≪≫ ?_
    refine (ModuleCat.extendScalars (algebraMap p.Poly (Localization.AtPrime m))).mapIso
      (p.derivedExtensionHomologyIso.{u, u} K i) ≪≫ ?_
    refine ((ModuleCat.extendScalarsComp (MvPolynomial.C : R →+* p.Poly)
      (algebraMap p.Poly (Localization.AtPrime m))).app
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)).symm ≪≫ ?_
    exact eqToIso (by rw [halgcomp])
  have hdim : ringKrullDim (Localization.AtPrime m) = ((d + p.variableCount : ℕ) : WithBot ℕ∞) :=
    ringKrullDim_localizationAtPrime_mvPolynomial p.variableCount m hlies d hd
  have hnorm : IsNormalizedDualizingComplex.{u, u}
      (((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap p.Poly (Localization.AtPrime m))).obj
        (p.derivedExtension.{u, u}.obj K))⟦(p.variableCount : ℤ)⟧) := by
    refine isNormalizedDualizingComplex_of_homology_bounds.{u} _
      (isDualizingComplex_shift _ hLB (p.variableCount : ℤ)) (d + p.variableCount) hdim
      (fun i hi => ?_) ?_
    · refine Limits.IsZero.of_iso ?_ (homologyShiftIso.{u} _ (p.variableCount : ℤ) i)
      refine Limits.IsZero.of_iso ?_ (hcomp ((p.variableCount : ℤ) + i))
      refine Functor.map_isZero _ ?_
      refine isZero_homology_of_lt_neg_ringKrullDim.{u} K hK d hd
        ((p.variableCount : ℤ) + i) ?_
      push_cast at hi ⊢
      omega
    · have hnt := nontrivial_homology_neg_ringKrullDim.{u} K hK d hd
      have htensor : Nontrivial
          (TensorProduct R (Localization.AtPrime m)
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(d : ℤ))).obj K)) :=
        (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right R
          (Localization.AtPrime m)).mpr hnt
      have hext : Nontrivial
          ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime m))).obj
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(d : ℤ))).obj K)) :=
        (extendCarrierEquiv.{u, u} _).toEquiv.nontrivial_congr.mp htensor
      have hLBnt := ((hcomp (-(d : ℤ))).toLinearEquiv.toEquiv.nontrivial_congr).mpr hext
      have hidx : (p.variableCount : ℤ) + (-((d + p.variableCount : ℕ) : ℤ)) = -(d : ℤ) := by
        push_cast
        omega
      refine (not_isZero_iff_nontrivial _).mp fun hz => (not_isZero_iff_nontrivial _).mpr hLBnt
        ((isZero_homology_shift_iff _ _ _ _ hidx).mp hz)
  refine ((dualizingDimension_eq_iff.{u, u} (p.derivedExtension.{u, u}.obj K) hL
    (⟨m, inferInstance⟩ : PrimeSpectrum p.Poly) (-(p.variableCount : ℤ))).mp ?_).symm
  rwa [neg_neg]

/-- Let `φ : R → A` be a finite type homomorphism of Noetherian rings with `R` local, and let
`m ⊆ A` be a maximal ideal lying over the maximal ideal of `R`.  If `ω_R` is a normalized
dualizing complex for `R`, then `φ^!(ω_R)_m` is a normalized dualizing complex for `A_m`, for
every polynomial presentation of `φ`. -/
@[stacks 0E9N]
theorem PolynomialPresentation.upperShriekFunctor_localization_isNormalizedDualizingComplex
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [IsLocalRing R] {f : R →+* A} (p : PolynomialPresentation f)
    (m : Ideal A) [m.IsMaximal] (hlies : m.comap f = IsLocalRing.maximalIdeal R)
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsNormalizedDualizingComplex.{u, u} K) :
    IsNormalizedDualizingComplex.{u, u}
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A (Localization.AtPrime m))).obj (p.upperShriekFunctor.{u, u}.obj K)) := by
  have hPnoeth : IsNoetherianRing p.Poly := inferInstance
  have hm' : (m.comap p.toRingHom).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ p.surjective
  have hlies' : (m.comap p.toRingHom).comap (MvPolynomial.C : R →+* p.Poly)
      = IsLocalRing.maximalIdeal R := by
    rwa [Ideal.comap_comap, p.commutes]
  have hL : IsDualizingComplex (p.derivedExtension.{u, u}.obj K) :=
    mvPolynomialBaseChange_isDualizingComplex p.variableCount K hK.1
  have hZ : IsDualizingComplex
      ((derivedHom.{u, u} p.toRingHom).obj (p.derivedExtension.{u, u}.obj K)) :=
    isDualizingComplex_derivedHom_of_finite.{u, u} p.toRingHom p.finite_toRingHom _ hL
  have hdimZ : dualizingDimension.{u, u}
      ((derivedHom.{u, u} p.toRingHom).obj (p.derivedExtension.{u, u}.obj K))
      (⟨m, inferInstance⟩ : PrimeSpectrum A) = -(p.variableCount : ℤ) := by
    rw [dualizingDimension_derivedHom_of_surjective.{u, u} p.toRingHom p.surjective
      (p.derivedExtension.{u, u}.obj K) hL (⟨m, inferInstance⟩ : PrimeSpectrum A)]
    exact p.dualizingDimension_derivedExtension (m.comap p.toRingHom) hlies' K hK
  have hdimY : dualizingDimension.{u, u} (p.upperShriekFunctor.{u, u}.obj K)
      (⟨m, inferInstance⟩ : PrimeSpectrum A) = 0 := by
    rw [p.upperShriekFunctor_obj.{u, u} K,
      dualizingDimension_shift.{u} _ hZ (⟨m, inferInstance⟩ : PrimeSpectrum A)
        (p.variableCount : ℤ), hdimZ]
    omega
  have hY : IsDualizingComplex (p.upperShriekFunctor.{u, u}.obj K) :=
    p.upperShriekFunctor_isDualizingComplex K hK.1
  have hspec := dualizingDimension_spec.{u, u} (p.upperShriekFunctor.{u, u}.obj K) hY
    (⟨m, inferInstance⟩ : PrimeSpectrum A)
  rw [hdimY] at hspec
  exact isNormalizedDualizingComplex_of_shift_neg_zero _ hspec

end Dualizing

end
