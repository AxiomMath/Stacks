module

public import Mathlib.RingTheory.Support
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionSpecialization
public import StacksFrontier.RingTheory.Dualizing.FiniteDimension
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.FlatBaseChange
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Normalized
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.LocalCohomology.BaseChangeGeneralSupport
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Dimension.DimensionFunctionDifference

/-!
# The canonical module of a Noetherian local ring

Let `A` be a Noetherian local ring with a normalized dualizing complex `ω_A^•`, let `d = dim(A)`
and let `ω_A = H^{-d}(ω_A^•)` be its **canonical module**. The support of `ω_A` is the union of
the irreducible components of `Spec(A)` of dimension `d`.

## Main results

* `Dualizing.dualizingDimension_eq_ringKrullDim_quotient` — for a normalized dualizing complex
  over a Noetherian local ring the dimension function is `δ(p) = dim(A/p)`.
* `Dualizing.isNormalizedDualizingComplex_localizationAtPrime_shift` — equivalently, the
  localization at `p`, shifted by `-dim(A/p)`, is a normalized dualizing complex over `A_p`.
* `Dualizing.subsingleton_localizedHomology_neg_ringKrullDim` — the canonical module vanishes at
  a prime with `dim(A/p) + dim(A_p) < dim(A)`.
* `Dualizing.support_canonicalModule` — the support of the canonical module is the union of the
  irreducible components of `Spec(A)` of dimension `dim(A)`.

## References

* [Stacks Project, Tag 0AWE](https://stacks.math.columbia.edu/tag/0AWE)
* [Stacks Project, Tag 0A7Z](https://stacks.math.columbia.edu/tag/0A7Z)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
* [Stacks Project, Tag 0AWD](https://stacks.math.columbia.edu/tag/0AWD)
-/

@[expose] public section

open CategoryTheory Order PrimeSpectrum TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-! ### The dimension function of a normalized dualizing complex over a local ring -/

/-- Over a Noetherian local ring, derived extension of scalars along the localization at the
maximal ideal preserves normalized dualizing complexes. -/
theorem isNormalizedDualizingComplex_derivedExtensionScalars_maximalIdeal
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsNormalizedDualizingComplex.{u, u} K) :
    IsNormalizedDualizingComplex.{u, u}
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A (Localization.AtPrime (IsLocalRing.maximalIdeal A)))).obj K) := by
  let B := Localization.AtPrime (IsLocalRing.maximalIdeal A)
  have : Module.Flat A B := IsLocalization.flat B (IsLocalRing.maximalIdeal A).primeCompl
  have : IsLocalHom (algebraMap A B) := ⟨fun x hx => IsLocalRing.notMem_maximalIdeal.mp
    ((IsLocalization.AtPrime.isUnit_to_map_iff B (IsLocalRing.maximalIdeal A) x).mp hx)⟩
  have hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B :=
    IsLocalization.AtPrime.map_eq_maximalIdeal (IsLocalRing.maximalIdeal A) B
  have hfl : (algebraMap A B).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat.{u, u, u} _ hfl
  have : Limits.PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    ModuleCat.extendScalars_preservesFiniteColimits.{u, u, u} _
  exact (isNormalizedDualizingComplex_congr
    (derivedExtensionScalarsObjIso (algebraMap A B) K ≪≫
      (Stacks.LocalCohomology.derivedExtensionScalarsIsoMapDerivedCategory.{u, u, u}
        (algebraMap A B)).app K)).mpr
    (isNormalizedDualizingComplex_extendScalars_of_flat.{u, u, u} hmax K hK)

/-- On the spectrum of a Noetherian local ring a dimension function vanishing at the maximal
ideal is `p ↦ dim(A/p)`. -/
private theorem dimensionFunction_eq_ringKrullDim_quotient
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A))
    (hδm : δ ⟨IsLocalRing.maximalIdeal A,
      (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩ = 0)
    (p : Ideal A) [p.IsPrime] (e : ℕ)
    (he : ringKrullDim (A ⧸ p) = e) : δ ⟨p, inferInstance⟩ = (e : ℤ) := by
  have hSober : StacksSober (PrimeSpectrum A) :=
    stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩
  have hδcat : IsDimensionFunctionForCatenary (δ : PrimeSpectrum A → ℤ) :=
    ⟨fun x y hxy hne => δ.strictAnti_specializes hxy hne, fun _ _ himm => δ.step_immediate himm⟩
  have hcat := isCatenary_of_isSober_of_dim hSober δ hδcat
  have hdimFn : ∃ δ' : TopologicalSpace.DimensionFunction (PrimeSpectrum A),
      ∀ q, δ' q = deltaDim q := by
    refine (TopologicalSpace.exists_dimensionFunction_iff deltaDim).2
      ⟨deltaDim_lt_of_specializes, fun x y himm => (deltaDim_eq_iff_coheight x y).2
        (FlatLocalCatenary.coheight_covBy_of_isCatenarySpace hcat x y
          ((immediateSpec_iff_covby x y).mp himm))⟩
  obtain ⟨δ', hδ'⟩ := hdimFn
  let m : PrimeSpectrum A :=
    ⟨IsLocalRing.maximalIdeal A, (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩
  let q : PrimeSpectrum A := ⟨p, inferInstance⟩
  have hspec : q ⤳ m :=
    (PrimeSpectrum.le_iff_specializes q m).mp (IsLocalRing.le_maximalIdeal_of_isPrime p)
  have hdiff := TopologicalSpace.DimensionFunction.sub_eq_of_specializes δ δ' hspec
  have hmmax : IsMax m := fun r _ => IsLocalRing.le_maximalIdeal_of_isPrime r.asIdeal
  have hδ'm : δ' m = 0 := by
    rw [hδ' m, deltaDim, dimQuotient, Order.coheight_eq_zero.mpr hmmax]; rfl
  have hδq : δ q = δ' q := by
    have h0 : δ q - δ' q = 0 := by rw [hdiff, hδm, hδ'm]; ring
    omega
  rw [hδq, hδ' q, deltaDim, dimQuotient]
  have hco : Order.coheight q = (e : ℕ∞) := mod_cast (coheight_eq_ringKrullDim_quotient q).trans he
  rw [hco]
  norm_num

/-- For a Noetherian local ring with a normalized dualizing complex, the shift that normalizes the
localization at `p` is the dimension of `A/p`. -/
theorem dualizingDimension_eq_ringKrullDim_quotient
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (p : Ideal A) [p.IsPrime] (e : ℕ) (he : ringKrullDim (A ⧸ p) = (e : WithBot ℕ∞)) :
    dualizingDimension.{u, u} K ⟨p, inferInstance⟩ = (e : ℤ) :=
  dimensionFunction_eq_ringKrullDim_quotient
    (dualizingDimensionFunction.{u, u} K hK.1)
    (dualizingDimension_maximalIdeal_eq_zero.{u, u} K hK) p e he

/-- Over a Noetherian local ring, the localization at `p` of a normalized dualizing complex,
shifted by `-dim(A/p)`, is a normalized dualizing complex over `A_p`. -/
theorem isNormalizedDualizingComplex_localizationAtPrime_shift
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (p : Ideal A) [p.IsPrime] (e : ℕ) (he : ringKrullDim (A ⧸ p) = (e : WithBot ℕ∞)) :
    IsNormalizedDualizingComplex.{u, u}
      (((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A (Localization.AtPrime p))).obj K)⟦-(e : ℤ)⟧) := by
  have h := dualizingDimension_spec.{u, u} K hK.1 ⟨p, inferInstance⟩
  rwa [dualizingDimension_eq_ringKrullDim_quotient K hK p e he] at h

/-- If `dim(A/p) + dim(A_p) < d` then the localization at `p` of `H^{-d}(K)` is zero. -/
theorem subsingleton_localizedHomology_neg_ringKrullDim
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (p : Ideal A) [p.IsPrime] (d e h : ℕ)
    (he : ringKrullDim (A ⧸ p) = (e : WithBot ℕ∞))
    (hh : ringKrullDim (Localization.AtPrime p) = (h : WithBot ℕ∞)) (hlt : e + h < d) :
    Subsingleton (LocalizedModule p.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K)) := by
  let Kp := (StacksDraft.PseudoCoherence.derivedExtensionScalars
    (algebraMap A (Localization.AtPrime p))).obj K
  have hnorm : IsNormalizedDualizingComplex.{u, u} (Kp⟦-(e : ℤ)⟧) :=
    isNormalizedDualizingComplex_localizationAtPrime_shift K hK p e he
  have hzero := isZero_homology_of_lt_neg_ringKrullDim (Kp⟦-(e : ℤ)⟧) hnorm h hh
    ((e : ℤ) - (d : ℤ)) (by omega)
  have hdeg : -(e : ℤ) + ((e : ℤ) - (d : ℤ)) = -(d : ℤ) := by ring
  have hiso := homologyShiftIso Kp (-(e : ℤ)) ((e : ℤ) - (d : ℤ))
  rw [hdeg] at hiso
  have hsub : Subsingleton ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Localization.AtPrime p)) (-(d : ℤ))).obj Kp) :=
    hiso.toLinearEquiv.toEquiv.subsingleton_congr.mp
      (ModuleCat.isZero_iff_subsingleton.mp hzero)
  exact (localizedHomologyIso p K (-(d : ℤ))).toLinearEquiv.toEquiv.subsingleton_congr.mp hsub

/-! ### The support of the canonical module -/

private lemma catenaryOrder_of_ringCatenary
    {A : Type u} [CommRing A] (hA : Ring.IsCatenary A) :
    Catenary.IsCatenaryOrder (PrimeSpectrum A) := by
  intro p q hpq
  obtain ⟨hbound, n, hn⟩ := hA p q hpq
  refine ⟨hbound, fun s t hs ht hs' ht' => ?_⟩
  exact (hn ⟨s.length, s.toFun, fun i => (s.step i).lt⟩ hs ht s.step).trans
    (hn ⟨t.length, t.toFun, fun i => (t.step i).lt⟩ hs' ht' t.step).symm

private lemma irreducibleCatenary_of_catenaryOrder
    {X : Type*} [TopologicalSpace X]
    (hX : Catenary.IsCatenaryOrder (TopologicalSpace.IrreducibleCloseds X)) :
    IrreducibleClosedsCodim.IsCatenarySpace X := by
  intro Y Z hYZ
  obtain ⟨⟨N, hN⟩, hlen⟩ := hX Y Z hYZ
  have hfin : IrreducibleClosedsCodim.topCodim Y Z ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top N)
    rw [IrreducibleClosedsCodim.topCodim_le_iff]
    intro s hs ht
    exact_mod_cast hN s hs ht
  refine ⟨hfin, fun s hs => ?_⟩
  obtain ⟨t, ht, htdim⟩ := exists_maximalChain_length_eq_topCodim Y Z hYZ hfin
  exact (congrArg (fun n : ℕ => (n : ℕ∞))
    (hlen ⟨s.length, s.toFun, hs.2.2⟩ ⟨t.length, t.toFun, ht.2.2⟩
      hs.1 hs.2.1 ht.1 ht.2.1)).trans htdim

private lemma exists_minimalPrime_coheight_eq_height_add
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hcat : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum A))
    (p : PrimeSpectrum A) :
    ∃ q : PrimeSpectrum A, IsMin q ∧ q ≤ p ∧
      Order.coheight q = Order.coheight p + Order.height p := by
  have : WellFoundedLT (PrimeSpectrum A) := (FlatLocalCatenary.wf_instances).1
  have : WellFoundedGT (PrimeSpectrum A) := (FlatLocalCatenary.wf_instances).2
  have hpfin : Order.height p < ⊤ :=
    lt_top_iff_ne_top.mpr (FlatLocalCatenary.height_ne_top_of_isLocalRing p)
  let n := (Order.height p).toNat
  have hn : Order.height p = (n : ℕ∞) := (ENat.natCast_toNat hpfin.ne).symm
  obtain ⟨s, hslast, hslen⟩ := Order.exists_series_of_height_eq_coe p hn
  obtain ⟨t, i, hti, _, hilast⟩ := LTSeries.exists_relSeries_covBy s
  have htlast : t.last = p := by
    have h := congrFun hti (Fin.last _)
    have h' : t.toFun (Fin.last t.length) = s.toFun (Fin.last s.length) := by
      simpa only [Function.comp_apply, hilast] using h
    have hh : t.last = s.last := by simpa only [RelSeries.last] using h'
    exact hh.trans hslast
  have hge : s.length ≤ t.length := by
    have hcard := Fintype.card_le_of_injective i i.injective
    simp only [Fintype.card_fin] at hcard
    omega
  have hub : (t.length : ℕ∞) ≤ Order.height p := by
    have h := Order.length_le_height_last (p := covToLT t)
    rwa [covToLT_length, show (covToLT t).last = t.last from rfl, htlast] at h
  have htlen : t.length = n := by
    have hnle : n ≤ t.length := hslen ▸ hge
    rw [hn] at hub
    have hcast : (t.length : ℕ∞) = n := le_antisymm hub (by exact_mod_cast hnle)
    exact_mod_cast hcast
  have hqmin : IsMin t.head := by
    have hmax : (covToLT t).length = Order.height (covToLT t).last := by
      rw [covToLT_length, show (covToLT t).last = t.last by rfl, htlast, htlen, hn]
    have hzero := Order.height_eq_index_of_length_eq_height_last hmax (0 : Fin (t.length + 1))
    change Order.height t.head = 0 at hzero
    exact Order.height_eq_zero.mp hzero
  have hqle : t.head ≤ p := by
    simpa [covToLT_head, show (covToLT t).last = t.last by rfl, htlast] using
      (covToLT t).head_le_last
  have htele := FlatLocalCatenary.coheight_head_eq
    (FlatLocalCatenary.coheight_covBy_of_isCatenarySpace hcat) t
  rw [htlast, htlen, ← hn] at htele
  exact ⟨t.head, hqmin, hqle, htele⟩

private lemma height_add_coheight_le_ringKrullDim
    {A : Type u} [CommRing A] (p : PrimeSpectrum A) :
    (Order.height p : WithBot ℕ∞) + (Order.coheight p : WithBot ℕ∞) ≤ ringKrullDim A := by
  have : Nonempty (PrimeSpectrum A) := ⟨p⟩
  change _ ≤ Order.krullDim (PrimeSpectrum A)
  rw [← WithBot.coe_add, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  exact WithBot.coe_le_coe.mpr
    (le_iSup (fun x : PrimeSpectrum A => Order.height x + Order.coheight x) p)

/-- `dim(A/p) = n` iff the coheight of `p` in `Spec A` is `n`. -/
private lemma ringKrullDim_quotient_eq_coe_iff {A : Type u} [CommRing A]
    (p : PrimeSpectrum A) (n : ℕ) :
    ringKrullDim (A ⧸ p.asIdeal) = (n : WithBot ℕ∞) ↔ Order.coheight p = (n : ℕ∞) := by
  rw [← coheight_eq_ringKrullDim_quotient p]
  norm_cast

private lemma mem_topDimensionalComponents_iff
    {A : Type u} [CommRing A] (d : ℕ) (p : PrimeSpectrum A) :
    p ∈ ⋃₀ {C ∈ irreducibleComponents (PrimeSpectrum A) |
        topologicalKrullDim C = (d : WithBot ℕ∞)} ↔
      ∃ q : PrimeSpectrum A, IsMin q ∧ q ≤ p ∧ Order.coheight q = d := by
  constructor
  · intro hp
    obtain ⟨C, ⟨hCcomp, hdimC⟩, hpC⟩ := Set.mem_sUnion.mp hp
    have hCclosed : IsClosed C := isClosed_of_mem_irreducibleComponents C hCcomp
    have hI : vanishingIdeal C ∈ minimalPrimes A := by
      rw [PrimeSpectrum.vanishingIdeal_mem_minimalPrimes, hCclosed.closure_eq]
      exact hCcomp
    let q : PrimeSpectrum A := ⟨vanishingIdeal C, hI.1.1⟩
    have hqI : q.asIdeal = vanishingIdeal C := rfl
    have hCq : C = PrimeSpectrum.zeroLocus (q.asIdeal : Set A) := by
      rw [hqI, zeroLocus_vanishingIdeal_eq_closure, hCclosed.closure_eq]
    have hqmin : IsMin q := isMin_iff.mpr (by rw [hqI]; exact hI)
    have hqp : q ≤ p := (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp
      (SetLike.coe_subset_coe.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp (hCq ▸ hpC)))
    rw [hCq, topologicalKrullDim_zeroLocus] at hdimC
    exact ⟨q, hqmin, hqp, (ringKrullDim_quotient_eq_coe_iff q d).1 hdimC⟩
  · rintro ⟨q, hqmin, hqp, hqd⟩
    have hqideal : q.asIdeal ∈ minimalPrimes A := isMin_iff.mp hqmin
    have hC : PrimeSpectrum.zeroLocus (q.asIdeal : Set A) ∈
        irreducibleComponents (PrimeSpectrum A) := by
      rw [← PrimeSpectrum.zeroLocus_minimalPrimes]
      exact Set.mem_image_of_mem _ hqideal
    have hdimC : topologicalKrullDim (PrimeSpectrum.zeroLocus (q.asIdeal : Set A)) =
        (d : WithBot ℕ∞) := by
      rw [topologicalKrullDim_zeroLocus]
      exact (ringKrullDim_quotient_eq_coe_iff q d).2 hqd
    exact Set.mem_sUnion.mpr ⟨_, ⟨hC, hdimC⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr
      (SetLike.coe_subset_coe.mpr ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hqp))⟩

/-- Let `A` be a Noetherian local ring with a normalized
dualizing complex `K`, let `d = dim(A)` and let `ω_A = H^{-d}(K)`. The support of `ω_A` is the
union of the irreducible components of `Spec(A)` of dimension `d`. -/
@[stacks 0AWE "(1): the support of ω_A is the union of the d-dimensional irreducible components"]
theorem support_canonicalModule
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞)) :
    Module.support A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K) =
      ⋃₀ {C ∈ irreducibleComponents (PrimeSpectrum A) |
        topologicalKrullDim C = (d : WithBot ℕ∞)} := by
  classical
  have hcatU : Ring.IsUniversallyCatenary A :=
    isUniversallyCatenary_of_isDualizingComplex hK.1
  have hcat : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum A) :=
    irreducibleCatenary_of_catenaryOrder
      ((Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum A).mp
        (catenaryOrder_of_ringCatenary (hcatU A)))
  ext p
  rw [mem_topDimensionalComponents_iff d p]
  constructor
  · intro hp
    let e : ℕ := (Order.coheight p).toNat
    let h : ℕ := (Order.height p).toNat
    have hcfin : Order.coheight p < ⊤ := WithBot.coe_lt_coe.mp
      ((Order.coheight_le_krullDim p).trans_lt (ringKrullDim_lt_top_of_isDualizingComplex hK.1))
    have hhfin : Order.height p < ⊤ :=
      lt_top_iff_ne_top.mpr (FlatLocalCatenary.height_ne_top_of_isLocalRing p)
    have hce : Order.coheight p = (e : ℕ∞) := (ENat.natCast_toNat hcfin.ne).symm
    have hhe : Order.height p = (h : ℕ∞) := (ENat.natCast_toNat hhfin.ne).symm
    have hdimE := (ringKrullDim_quotient_eq_coe_iff p e).2 hce
    have hdimH : ringKrullDim (Localization.AtPrime p.asIdeal) = (h : WithBot ℕ∞) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal _,
        PrimeSpectrum.height_eq_orderHeight]
      exact_mod_cast hhe
    have hnotlt : ¬ e + h < d := fun hlt => (not_nontrivial_iff_subsingleton.mpr
      (subsingleton_localizedHomology_neg_ringKrullDim K hK p.asIdeal d e h hdimE hdimH hlt))
      (Module.mem_support_iff.mp hp)
    have hle : e + h ≤ d := by
      have hle := height_add_coheight_le_ringKrullDim p
      rw [show (Order.height p : WithBot ℕ∞) = (h : WithBot ℕ∞) by exact_mod_cast hhe,
        show (Order.coheight p : WithBot ℕ∞) = (e : WithBot ℕ∞) by exact_mod_cast hce, hd] at hle
      have hle' : (h : WithBot ℕ∞) + (e : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
        simpa [add_comm] using hle
      have hleNat : h + e ≤ d := by exact_mod_cast hle'
      omega
    have heq : e + h = d := Nat.le_antisymm hle (Nat.le_of_not_lt hnotlt)
    obtain ⟨q, hqmin, hqp, hqsum⟩ := exists_minimalPrime_coheight_eq_height_add hcat p
    have hqcoheight : Order.coheight q = (d : ℕ∞) := by
      rw [hqsum, hce, hhe]; exact_mod_cast heq
    exact ⟨q, hqmin, hqp, by exact_mod_cast hqcoheight⟩
  · rintro ⟨q, hqmin, hqp, hqd⟩
    have hqideal : q.asIdeal ∈ minimalPrimes A := PrimeSpectrum.isMin_iff.mp hqmin
    have hdimq := (ringKrullDim_quotient_eq_coe_iff q d).2 hqd
    exact Module.mem_support_mono hqp (Module.mem_support_iff.mpr
      ((nontrivial_localized_homology_iff_eq_neg_dimension.{u, u}
        K hK q hqideal d hdimq (-(d : ℤ))).mpr rfl))

end Dualizing

end
