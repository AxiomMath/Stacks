module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GenericPointGluing.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.RingTheory.Branches.Henselization
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
public import StacksFrontier.RingTheory.TensorProduct.LocalAlgebra

/-!
# Geometric unibranchness and connectedness of punctured strict local spectra

A locally Noetherian scheme is geometrically unibranch exactly when, at every point that is not
the generic point of an irreducible component, the punctured spectrum of a strict henselization
of the local ring is connected.

## Main results

* `AlgebraicGeometry.isGeometricallyUnibranch_iff_isConnected_puncturedSpectrum` is the
  equivalence.

## Implementation notes

The source assumes the scheme is Noetherian; local Noetherianity is all the argument uses. A
strict henselization is a henselization whose residue field is a separable closure of the
original residue field, which is `IsLocalRing.IsHenselization` for such a field; the statement
quantifies over every choice of one. The punctured spectrum is the complement of the closed
point in `PrimeSpectrum`.

## References

* [Stacks Project, Tag 0BQ4](https://stacks.math.columbia.edu/tag/0BQ4)
-/

@[expose] public section

universe u

open IsLocalRing
open scoped TensorProduct

private lemma unique_minimalPrimes_of_domain_reduction
    (R : Type u) [CommRing R]
    (hred : IsDomain (R ⧸ nilradical R)) :
    ∃! p : Ideal R, p ∈ minimalPrimes R := by
  let : IsDomain (R ⧸ nilradical R) := hred
  have hnil : (nilradical R).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime (I := nilradical R)).mp inferInstance
  have hmem : nilradical R ∈ minimalPrimes R := by
    rw [minimalPrimes_eq_minimals]
    refine ⟨hnil, ?_⟩
    intro q hq _
    exact nilradical_le_prime q (H := hq)
  refine ⟨nilradical R, hmem, ?_⟩
  intro q hq
  rw [minimalPrimes_eq_minimals] at hq
  have hle : nilradical R ≤ q := nilradical_le_prime q (H := hq.1)
  exact le_antisymm (hq.2 hnil hle) hle

private theorem unique_minimalPrimes_of_isGeometricallyUnibranch_of_normal_tensorProduct
    {R : Type u} {S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Module.Flat R S] (hgeom : IsGeometricallyUnibranch R)
    (hn : ∀ (C : Type u) [CommRing C] [Algebra R C],
      IsNormalRing C → IsNormalRing (S ⊗[R] C)) :
    ∃! p : Ideal S, p ∈ minimalPrimes S := by
  let Rred := R ⧸ nilradical R
  let I : Ideal S := Ideal.map (algebraMap R S) (nilradical R)
  let D := S ⧸ I
  let C := integralClosure Rred (FractionRing Rred)
  have hred : IsDomain Rred := hgeom.1.1
  have hC : IsLocalRing C := hgeom.1.2
  let : IsLocalRing Rred :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap R Rred) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hCint : IsIntegrallyClosed C :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing Rred)
  have hCnormal : IsNormalRing C := fun p _ =>
    ⟨IsLocalization.isDomain_of_local_atPrime ‹p.IsPrime›,
      isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime p)
        p.primeCompl p.primeCompl_le_nonZeroDivisors⟩
  let : Algebra.IsIntegral R C := Algebra.IsIntegral.trans Rred
  have hRredC : IsLocalHom (algebraMap Rred C) := by
    exact ((local_hom_TFAE (algebraMap Rred C)).out 5 1).mp <| (maximal_ideal_unique Rred).unique
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := Rred) (maximalIdeal C)) inferInstance
  have hRC : IsLocalHom (algebraMap R C) := by
    rw [IsScalarTower.algebraMap_eq R Rred C]
    exact RingHom.isLocalHom_comp _ _
  have hins :
      @IsPurelyInseparable (ResidueField R) (ResidueField C) _ _
        (ResidueField.map (algebraMap R C)).toAlgebra ∨
      @IsPurelyInseparable (ResidueField R) (ResidueField S) _ _
        (ResidueField.map (algebraMap R S)).toAlgebra :=
    Or.inl (hgeom.2 hred hC)
  have hTlocal : IsLocalRing (S ⊗[R] C) := (isLocalRing_tensorProduct_of_isIntegral R S C hins).1
  have hTnormal : IsNormalRing (S ⊗[R] C) := hn C hCnormal
  have hTdomain : IsDomain (S ⊗[R] C) :=
    (IsNormalRing.of_isLocalRing hTnormal).1
  have hIlemax : I ≤ maximalIdeal S := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
    exact nilradical_le_prime (maximalIdeal R)
  have hIproper : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hIlemax
  let : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr hIproper
  let : IsLocalRing D :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : Algebra Rred D := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower R Rred C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R Rred D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hflatD : Module.Flat Rred D :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (nilradical R)).toLinearEquiv
  have hRCinj : Function.Injective (algebraMap Rred C) :=
    FaithfulSMul.algebraMap_injective Rred C
  let e : D ⊗[Rred] C ≃+* S ⊗[R] C :=
    (((Algebra.TensorProduct.comm Rred D C).toRingEquiv).trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[C] C)
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (nilradical R))).trans
        (Algebra.TensorProduct.cancelBaseChange R Rred C C S)).toRingEquiv).trans
      (Algebra.TensorProduct.comm R S C).symm.toRingEquiv
  have hDinj : Function.Injective
      (e.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := Rred) (A := D) (B := C))) :=
    e.injective.comp
      (Algebra.TensorProduct.includeLeft_injective (S := Rred) hRCinj)
  let : IsDomain (S ⊗[R] C) := hTdomain
  have hD : IsDomain D := Function.Injective.isDomain _ hDinj
  have hIprime : I.IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime (I := I)).mp hD
  have hIle : I ≤ nilradical S := by
    show Ideal.map (algebraMap R S) (Ideal.radical ⊥) ≤ Ideal.radical ⊥
    simpa only [Ideal.map_bot] using
      (Ideal.map_radical_le (algebraMap R S) (I := (⊥ : Ideal R)))
  have hIeq : I = nilradical S := le_antisymm hIle (nilradical_le_prime I)
  exact unique_minimalPrimes_of_domain_reduction S (hIeq ▸ hD)

private theorem isConnected_puncturedSpectrum_of_unique_minimalPrime
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hmin : ∃! p : Ideal R, p ∈ minimalPrimes R)
    (hne : ({closedPoint R}ᶜ : Set (PrimeSpectrum R)).Nonempty) :
    IsConnected ({closedPoint R}ᶜ : Set (PrimeSpectrum R)) := by
  obtain ⟨p, hp, hpu⟩ := hmin
  have hs : sInf (minimalPrimes R) = p := by
    ext x
    simp only [Ideal.mem_sInf]
    constructor
    · intro hx
      exact hx hp
    · intro hx q hq
      rw [hpu q hq]
      exact hx
  have hn : nilradical R = p := by
    show (⊥ : Ideal R).radical = p
    rw [← Ideal.sInf_minimalPrimes]
    exact hs
  have hi : IrreducibleSpace (PrimeSpectrum R) :=
    (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical (R := R)).2 (hn ▸ hp.1.1)
  have hu : IsPreirreducible (Set.univ : Set (PrimeSpectrum R)) :=
    (irreducibleSpace_def (PrimeSpectrum R)).1 hi |>.2
  have hpunct : IsOpen ({closedPoint R}ᶜ : Set (PrimeSpectrum R)) :=
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2
      (IsLocalRing.maximalIdeal.isMaximal R)).isOpen_compl
  have hirr : IsIrreducible ({closedPoint R}ᶜ : Set (PrimeSpectrum R)) :=
    hu.subset_irreducible hne hpunct (fun _ hx => hx) (fun _ _ => Set.mem_univ _)
  exact hirr.isConnected

private theorem unique_minimal_of_connected_puncture_of_unique_local_minimals
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hconn : IsConnected ({closedPoint R}ᶜ : Set (PrimeSpectrum R)))
    (huniq : ∀ q : PrimeSpectrum R, q ≠ closedPoint R →
      ∃! p : Ideal R, p ∈ minimalPrimes R ∧ p ≤ q.asIdeal) :
    ∃! p : Ideal R, p ∈ minimalPrimes R := by
  classical
  let S := {q : PrimeSpectrum R // q ≠ closedPoint R}
  let P := {p : Ideal R // p ∈ minimalPrimes R}
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp hconn
  let label : S → P := fun q => ⟨Classical.choose (huniq q.1 q.2),
    (Classical.choose_spec (huniq q.1 q.2)).1.1⟩
  have hlabel_le (q : S) : (label q).1 ≤ q.1.asIdeal :=
    (Classical.choose_spec (huniq q.1 q.2)).1.2
  have hlabel_unique (q : S) (p : P) (hp : p.1 ≤ q.1.asIdeal) : label q = p :=
    Subtype.ext ((Classical.choose_spec (huniq q.1 q.2)).2 p ⟨p.2, hp⟩).symm
  have hmin_finite : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  let : Finite P := hmin_finite.to_subtype
  have hfiber (p : P) : {q : S | label q = p} = {q : S | p.1 ≤ q.1.asIdeal} := by
    ext q
    exact ⟨fun h => h ▸ hlabel_le q, hlabel_unique q p⟩
  have hclosed (p : P) : IsClosed {q : S | label q = p} := by
    rw [hfiber p, isClosed_induced_iff]
    refine ⟨PrimeSpectrum.zeroLocus (p.1 : Set R), PrimeSpectrum.isClosed_zeroLocus _, ?_⟩
    ext q
    simp [PrimeSpectrum.mem_zeroLocus]
  have hcompl_eq (p : P) : {q : S | label q ≠ p} =
      ⋃ i : P, if i = p then (∅ : Set S) else {q : S | label q = i} := by
    ext q
    constructor
    · intro h
      refine Set.mem_iUnion.mpr ⟨label q, ?_⟩
      have hne : label q ≠ p := fun heq => h heq
      simp [hne]
    · intro h
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
      by_cases hip : i = p
      · simp [hip] at hi
      · have hqi : label q = i := by simpa [hip] using hi
        intro hqp
        exact hip (hqi.symm.trans hqp)
  have hcompl_closed (p : P) : IsClosed {q : S | label q ≠ p} := by
    rw [hcompl_eq p]
    exact isClosed_iUnion_of_finite fun i => by
      by_cases hi : i = p
      · simp [hi]
      · simpa [hi] using hclosed i
  have hclopen (p : P) : IsClopen {q : S | label q = p} := by
    refine ⟨hclosed p, ?_⟩
    simpa only [Set.compl_ofPred, not_not] using (isOpen_compl_iff.mpr (hcompl_closed p))
  have hmin_ne_max (p : P) : p.1 ≠ maximalIdeal R := by
    intro hpmax
    obtain ⟨r, hr⟩ := hconn.nonempty
    obtain ⟨q, hq, hqr⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R))
      (J := r.asIdeal) bot_le
    have hp' : maximalIdeal R ∈ minimalPrimes R := by simpa [hpmax] using p.2
    have hrle : r.asIdeal ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal r.2.ne_top
    have hqeq : q = maximalIdeal R :=
      (minimalPrimes_eq_minimals (R := R) ▸ hp').eq_of_le hq.isPrime (hqr.trans hrle)
    have hreq : r.asIdeal = maximalIdeal R := le_antisymm hrle (hqeq ▸ hqr)
    exact hr (PrimeSpectrum.ext hreq)
  have hfiber_nonempty (p : P) : ({q : S | label q = p}).Nonempty := by
    let q : S := ⟨⟨p.1, p.2.isPrime⟩, by
      intro h
      exact hmin_ne_max p (congrArg PrimeSpectrum.asIdeal h)⟩
    exact ⟨q, hlabel_unique q p le_rfl⟩
  have hall : ∀ p : P, {q : S | label q = p} = Set.univ := fun p =>
    (isClopen_iff.mp (hclopen p)).resolve_left (hfiber_nonempty p).ne_empty
  obtain ⟨r, hr⟩ := hconn.nonempty
  let rS : S := ⟨r, hr⟩
  let p₀ := label rS
  refine ⟨p₀.1, p₀.2, ?_⟩
  intro p hp
  let pp : P := ⟨p, hp⟩
  have hppne : pp.1 ≠ maximalIdeal R := hmin_ne_max pp
  let q : S := ⟨⟨p, hp.isPrime⟩, by
    intro h
    exact hppne (congrArg PrimeSpectrum.asIdeal h)⟩
  have hqpp : label q = pp := hlabel_unique q pp le_rfl
  have hq0 : label q = p₀ := Set.eq_univ_iff_forall.mp (hall p₀) q
  exact congrArg Subtype.val (hqpp.symm.trans hq0)

private theorem unique_minimalPrime_below_of_unique_localization
    {R : Type u} [CommRing R] (q : Ideal R) [q.IsPrime]
    (h : ∃! p : Ideal (Localization.AtPrime q), p ∈ minimalPrimes (Localization.AtPrime q)) :
    ∃! p : Ideal R, p ∈ minimalPrimes R ∧ p ≤ q := by
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := q) bot_le
  have hm (r : Ideal R) (hr : r ∈ minimalPrimes R) (hrq : r ≤ q) :
      (r.map (algebraMap R (Localization.AtPrime q))) ∈
        minimalPrimes (Localization.AtPrime q) ∧
      (r.map (algebraMap R (Localization.AtPrime q))).under R = r := by
    have he := IsLocalization.under_map_of_isPrime_disjoint q.primeCompl
      (Localization.AtPrime q) hr.isPrime
      (Set.disjoint_left.mpr fun x hx hxr => hx (hrq hxr))
    refine ⟨?_, he⟩
    show _ ∈ (⊥ : Ideal (Localization.AtPrime q)).minimalPrimes
    rw [← Ideal.map_bot (f := algebraMap R (Localization.AtPrime q)),
      IsLocalization.minimalPrimes_map q.primeCompl (Localization.AtPrime q),
      Set.mem_preimage, he]
    exact hr
  refine ⟨p, ⟨hp, hpq⟩, ?_⟩
  rintro r ⟨hr, hrq⟩
  obtain ⟨hpm, hpe⟩ := hm p hp hpq
  obtain ⟨hrm, hre⟩ := hm r hr hrq
  exact hre.symm.trans ((congrArg (Ideal.under R) (h.unique hrm hpm)).trans hpe)

private theorem unique_minimalPrimes_of_ind_etale
    (R S : Type u) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hR : IsGeometricallyUnibranch R)
    (hi : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S)) :
    ∃! p : Ideal S, p ∈ minimalPrimes S := by
  let : Module.Flat R S := CommAlgCat.flat_of_ind_etale hi
  exact unique_minimalPrimes_of_isGeometricallyUnibranch_of_normal_tensorProduct hR
    fun C _ _ hC => IsNormalRing.congr (Algebra.TensorProduct.comm R C S).toRingEquiv
      (isNormalRing_tensorProduct_of_ind_etale C hC hi)

private theorem exists_noetherian_strictHenselization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra (ResidueField R) K)
      (_ : IsSepClosure (ResidueField R) K)
      (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra R S),
      IsHenselization R K S ∧ IsNoetherianRing S := by
  obtain ⟨Rh, _, _, _, _, hh, hi, hm, he⟩ := exists_henselization R
  let : HenselianLocalRing Rh := hh
  let : IsHenselization R (ResidueField R) Rh :=
    IsHenselization.of_ind_etale hh hi
      ⟨RingEquiv.ofBijective _ he, fun x => ResidueField.map_residue _ x⟩
  let K := SeparableClosure (ResidueField R)
  obtain ⟨S, _, _, _, _, _, _, hS, _, hiS, _, e, heS⟩ :=
    exists_strictHenselization R Rh hi he.2 K
  let : IsHenselization R K S := IsHenselization.of_ind_etale hS hiS ⟨e, heS⟩
  exact ⟨K, inferInstance, inferInstance, inferInstance, S, inferInstance, inferInstance,
    inferInstance, inferInstance,
    (isNoetherianRing_iff_henselizations R Rh S K).2.mp inferInstance⟩

private theorem comap_lt_of_ne_closedPoint
    (R A H : Type u) [CommRing R] [CommRing A] [IsLocalRing A]
    [CommRing H] [IsLocalRing H] [Algebra R A] [Algebra A H] [Algebra R H]
    [IsScalarTower R A H] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p]
    [IsLocalHom (algebraMap A H)]
    (hm : (maximalIdeal A).map (algebraMap A H) = maximalIdeal H)
    (q : PrimeSpectrum H) (hq : q ≠ closedPoint H) :
    q.asIdeal.comap (algebraMap R H) < p := by
  have he : (maximalIdeal H).comap (algebraMap R H) = p := by
    rw [IsScalarTower.algebraMap_eq R A H, ← Ideal.comap_comap,
      maximalIdeal_comap]
    exact IsLocalization.AtPrime.under_maximalIdeal A p
  refine lt_of_le_of_ne ?_ ?_
  · rw [← he]
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal q.2.ne_top)
  · intro h
    have hmap : p.map (algebraMap R H) = maximalIdeal H := by
      rw [IsScalarTower.algebraMap_eq R A H, ← Ideal.map_map,
        IsLocalization.AtPrime.map_eq_maximalIdeal p A, hm]
    have hle : maximalIdeal H ≤ q.asIdeal := by
      rw [← hmap, ← h]
      exact Ideal.map_comap_le
    exact hq (PrimeSpectrum.ext (le_antisymm
      (IsLocalRing.le_maximalIdeal q.2.ne_top) hle))

/-- For a prime `q` of `H` whose contraction to `R` is the prime that `B` localizes `R` at, the
localization of `H` at `q` is a local `B`-algebra over `R`. -/
private theorem exists_isLocalHom_to_localizationAtPrime
    (R B H : Type u) [CommRing R] [CommRing B] [IsLocalRing B]
    [CommRing H] [Algebra R B] [Algebra R H] (q : PrimeSpectrum H)
    [IsLocalization.AtPrime B (q.asIdeal.comap (algebraMap R H))] :
    ∃ f : B →+* Localization.AtPrime q.asIdeal,
      (∀ x : R, f (algebraMap R B x) = algebraMap R (Localization.AtPrime q.asIdeal) x) ∧
        IsLocalHom f := by
  let Q := Localization.AtPrime q.asIdeal
  let r := q.asIdeal.comap (algebraMap R H)
  have hu (s : r.primeCompl) : IsUnit (algebraMap R Q s.1) := by
    rw [IsScalarTower.algebraMap_apply R H Q]
    exact IsLocalization.map_units (M := q.asIdeal.primeCompl) Q
      ⟨algebraMap R H s.1, s.2⟩
  let f : B →ₐ[R] Q := IsLocalization.liftAlgHom
    (f := IsScalarTower.toAlgHom R R Q) hu
  let : Algebra B Q := f.toRingHom.toAlgebra
  let : IsScalarTower R B Q := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have hlocal : IsLocalHom (algebraMap B Q) := by
    apply ((local_hom_TFAE (algebraMap B Q)).out 4 1).mp
    intro b hb
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal r B] at hb
    have hle : (r.map (algebraMap R B)).map (algebraMap B Q) ≤ maximalIdeal Q := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R B Q,
        Ideal.map_le_iff_le_comap, IsScalarTower.algebraMap_eq R H Q,
        ← Ideal.comap_comap]
      show r ≤ ((maximalIdeal Q).under H).under R
      rw [IsLocalization.AtPrime.under_maximalIdeal Q q.asIdeal]
    exact hle (Ideal.mem_map_of_mem _ hb)
  exact ⟨f.toRingHom, fun x => f.commutes x, hlocal⟩

namespace AlgebraicGeometry

private theorem puncturedSpectrum_nonempty_of_notMem_genericPoints
    (X : Scheme.{u}) (x : X) (hx : x ∉ genericPoints X)
    (κsep : Type u) [Field κsep]
    [Algebra (ResidueField (X.presheaf.stalk x)) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk x)) κsep]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash]
    [Algebra (X.presheaf.stalk x) Ash]
    [IsHenselization (X.presheaf.stalk x) κsep Ash] :
    ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)).Nonempty := by
  let Z : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let η : genericPoints X := genericPoints.ofComponent Z
  have hηx : η.1 ⤳ x := genericPoints.isGenericPoint_ofComponent Z |>.specializes
    (mem_irreducibleComponent (x := x))
  have hηne : η.1 ≠ x := by
    intro h
    apply hx
    simpa [h] using η.2
  have hηrange : η.1 ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hηx
  obtain ⟨q, hq⟩ := hηrange
  have hqne : q ≠ closedPoint (X.presheaf.stalk x) := by
    intro h
    subst q
    apply hηne
    simpa using hq.symm
  let : Module.Flat (X.presheaf.stalk x) Ash := flat_of_isHenselization κsep
  let : IsLocalHom (algebraMap (X.presheaf.stalk x) Ash) :=
    IsLocalRing.IsHenselization.isLocalHom (R := X.presheaf.stalk x) (L := κsep)
  let : Module.FaithfullyFlat (X.presheaf.stalk x) Ash :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨p, hp⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := X.presheaf.stalk x) (B := Ash) q
  refine ⟨p, ?_⟩
  intro hpclosed
  have hcomap : PrimeSpectrum.comap (algebraMap (X.presheaf.stalk x) Ash)
      (closedPoint Ash) = closedPoint (X.presheaf.stalk x) :=
    PrimeSpectrum.ext (maximalIdeal_comap (algebraMap (X.presheaf.stalk x) Ash))
  exact hqne (hp.symm.trans ((congrArg
    (PrimeSpectrum.comap (algebraMap (X.presheaf.stalk x) Ash)) hpclosed).trans hcomap))

/-- A locally Noetherian scheme is geometrically unibranch exactly when, at every point which is
not the generic point of an irreducible component, the punctured spectrum of a strict
henselization of the local ring is connected. -/
@[stacks 0BQ4]
theorem isGeometricallyUnibranch_iff_isConnected_puncturedSpectrum
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsGeometricallyUnibranch X ↔
      ∀ x : X, x ∉ genericPoints X →
        ∀ (κsep : Type u) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk x)) κsep]
          [IsSepClosure (ResidueField (X.presheaf.stalk x)) κsep]
          (Ash : Type u) [CommRing Ash] [IsLocalRing Ash]
          [Algebra (X.presheaf.stalk x) Ash]
          [IsHenselization (X.presheaf.stalk x) κsep Ash],
          IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)) := by
  constructor
  · intro hgeom x hx κsep _ _ _ Ash _ _ _ _
    have hgeomRing : _root_.IsGeometricallyUnibranch (X.presheaf.stalk x) :=
      (isGeometricallyUnibranch_iff_isGeometricallyUnibranchRing _).2 (hgeom x)
    have hmin := (isGeometricallyUnibranch_iff_strictHenselization_has_unique_minimalPrime
      (X.presheaf.stalk x) Ash κsep).mp hgeomRing
    exact isConnected_puncturedSpectrum_of_unique_minimalPrime Ash hmin
      (puncturedSpectrum_nonempty_of_notMem_genericPoints X x hx κsep Ash)
  · intro hconn x
    classical
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    change IsAffineOpen U at hU
    let R : Type u := Γ(X, U)
    let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hmemU (p : PrimeSpectrum R) : hU.fromSpec p ∈ U := by
      show hU.fromSpec p ∈ (U : Set X)
      rw [← hU.range_fromSpec]
      exact ⟨p, rfl⟩
    have hgoal : ∀ p : PrimeSpectrum R,
        _root_.IsGeometricallyUnibranch (X.presheaf.stalk (hU.fromSpec p)) := by
      intro p
      induction p using
          (InvImage.wf (fun p : PrimeSpectrum R => p.asIdeal.height) wellFounded_lt).induction with
      | h p ih =>
        let y : X := hU.fromSpec p
        let A : Type u := X.presheaf.stalk y
        let : Algebra R A := X.presheaf.algebra_section_stalk ⟨y, hmemU p⟩
        let : IsLocalization.AtPrime A p.asIdeal := hU.isLocalization_stalk' p (hmemU p)
        obtain ⟨K, _, _, _, H, _, _, _, hH, hN⟩ :=
          exists_noetherian_strictHenselization A
        let : IsHenselization A K H := hH
        let : IsNoetherianRing H := hN
        let : IsLocalHom (algebraMap A H) := IsHenselization.isLocalHom (L := K)
        let : Algebra R H := ((algebraMap A H).comp (algebraMap R A)).toAlgebra
        let : IsScalarTower R A H := IsScalarTower.of_algebraMap_eq fun _ => rfl
        have hiAH := IsHenselization.ind_etale_of_universe_le (R := A) K (Rh := H)
        have hiRH := CommAlgCat.ind_etale_comp
          (CommAlgCat.ind_etale_atPrime R A p.asIdeal) hiAH
        have hlt (q : PrimeSpectrum H) (hq : q ≠ closedPoint H) :
            q.asIdeal.comap (algebraMap R H) < p.asIdeal :=
          comap_lt_of_ne_closedPoint R A H p.asIdeal
            (IsHenselization.map_maximalIdeal (R := A) (L := K)) q hq
        apply (isGeometricallyUnibranch_iff_strictHenselization_has_unique_minimalPrime
          A H K).mpr
        by_cases hne : ({closedPoint H}ᶜ : Set (PrimeSpectrum H)).Nonempty
        · have hy : y ∉ genericPoints X := by
            intro hgen
            obtain ⟨q, hq⟩ := hne
            let r := PrimeSpectrum.comap (algebraMap R H) q
            have hrp : r < p := hlt q hq
            have hspec : hU.fromSpec r ⤳ y :=
              ((PrimeSpectrum.le_iff_specializes r p).mp hrp.le).map hU.fromSpec.continuous
            have heq : r = p := hU.fromSpec.isOpenEmbedding.injective
              (Stacks.AlgebraicGeometry.GenericPointGluing.eq_of_specializes_genericPoint
                hgen hspec)
            exact hrp.ne heq
          apply unique_minimal_of_connected_puncture_of_unique_local_minimals H
            (hconn y hy K H)
          intro q hq
          let r := PrimeSpectrum.comap (algebraMap R H) q
          have hrp : r.asIdeal < p.asIdeal := hlt q hq
          have hihr : _root_.IsGeometricallyUnibranch (X.presheaf.stalk (hU.fromSpec r)) :=
            ih r (Ideal.height_strict_mono_of_isPrime hrp)
          let B : Type u := X.presheaf.stalk (hU.fromSpec r)
          let : Algebra R B := X.presheaf.algebra_section_stalk ⟨hU.fromSpec r, hmemU r⟩
          let : IsLocalization.AtPrime B (q.asIdeal.comap (algebraMap R H)) :=
            hU.isLocalization_stalk' r (hmemU r)
          obtain ⟨fBQ, hfBQ, hfBQloc⟩ := exists_isLocalHom_to_localizationAtPrime R B H q
          let : Algebra B (Localization.AtPrime q.asIdeal) := fBQ.toAlgebra
          have : IsScalarTower R B (Localization.AtPrime q.asIdeal) :=
            IsScalarTower.of_algebraMap_eq fun x => (hfBQ x).symm
          have : IsLocalHom (algebraMap B (Localization.AtPrime q.asIdeal)) := hfBQloc
          have hiRQ := CommAlgCat.ind_etale_comp hiRH
            (CommAlgCat.ind_etale_atPrime H (Localization.AtPrime q.asIdeal) q.asIdeal)
          have hiBQ := CommAlgCat.ind_etale_of_comp
            (CommAlgCat.ind_etale_atPrime R B (q.asIdeal.comap (algebraMap R H))) hiRQ
          exact unique_minimalPrime_below_of_unique_localization q.asIdeal
            (unique_minimalPrimes_of_ind_etale B (Localization.AtPrime q.asIdeal) hihr hiBQ)
        · have hall (q : PrimeSpectrum H) : q = closedPoint H := by
            by_contra hq
            exact hne ⟨q, hq⟩
          obtain ⟨m, hm, -⟩ := Ideal.exists_minimalPrimes_le
            (I := (⊥ : Ideal H)) (J := maximalIdeal H) bot_le
          exact ⟨m, hm, fun n hn => congrArg PrimeSpectrum.asIdeal
            ((hall ⟨n, hn.isPrime⟩).trans (hall ⟨m, hm.isPrime⟩).symm)⟩
    apply (isGeometricallyUnibranch_iff_isGeometricallyUnibranchRing _).mp
    exact (congrArg (fun z : X => _root_.IsGeometricallyUnibranch (X.presheaf.stalk z))
      (hU.fromSpec_primeIdealOf ⟨x, hxU⟩)).mp (hgoal (hU.primeIdealOf ⟨x, hxU⟩))

end AlgebraicGeometry

end
