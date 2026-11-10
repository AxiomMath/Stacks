module

public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.Regular.Flat
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.AffineBlowup.ModelComparison
public import StacksFrontier.RingTheory.Blowup.Basic
public import StacksFrontier.RingTheory.Blowup.Defs
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.Kaehler.Defs
public import StacksFrontier.RingTheory.Kaehler.Separable
public import StacksFrontier.RingTheory.Koszul.Blowup
public import StacksFrontier.RingTheory.Koszul.Quasiregular
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.Sequence.Regular.Basic
public import StacksFrontier.RingTheory.Smooth.Basic
public import StacksFrontier.RingTheory.Smooth.Localization
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import StacksFrontier.RingTheory.Smooth.RegularRing
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.RingTheory.Smoothing.NeronDesingularization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regular parameters at the point of a Néron chart

Fix an extension `R → Λ` of discrete valuation rings of ramification index one together with a
factorization `R → A → Λ` in which `A` is flat and of finite type over `R`, let `π` be a
uniformizer of `R`, and let `𝔭 ⊆ A` be the preimage of the maximal ideal of `Λ`. This file shows
that `𝔭` is prime and that, when `A` is smooth over `R` at `𝔭`, the local ring at `𝔭` and its
closed fibre are regular, so that `π` followed by a regular system of parameters of the closed
fibre is a regular sequence generating `𝔭`. These data spread out to a principal neighbourhood
of `𝔭`, and a regular sequence `π, g₁, …, g_c` presents the affine blowup chart `A[𝔭/π]` as the
quotient `A[y₁, …, y_c]/(π y₁ - g₁, …, π y_c - g_c)`, each `yᵢ` corresponding to `gᵢ/π`.
-/

@[expose] public section

namespace Stacks.Smoothing

open Stacks.Smooth.FlatFibreCriterion
open Stacks.Flatness.RegularSequenceQuotient

/-- The ideal `𝔭`, the preimage in `A` of the maximal ideal of `Λ`, is prime. -/
instance NeronSituation.isPrime_maximalIdealPreimage (S : NeronSituation) :
    S.maximalIdealPreimage.IsPrime := by
  have : (IsLocalRing.maximalIdeal S.Λ).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal S.Λ).isPrime
  exact Ideal.comap_isPrime _ _

private lemma maximalIdealPreimage_comap (S : NeronSituation) :
    S.maximalIdealPreimage.comap (algebraMap S.R S.A) =
      IsLocalRing.maximalIdeal S.R := by
  have : IsLocalHom (algebraMap S.R S.Λ) := S.extension.2
  change (Ideal.comap (algebraMap S.A S.Λ) (IsLocalRing.maximalIdeal S.Λ)).comap
    (algebraMap S.R S.A) = _
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq S.R S.A S.Λ]
  exact IsLocalRing.maximalIdeal_comap (algebraMap S.R S.Λ)

private lemma uniformizer_mem_maximalIdealPreimage (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) :
    algebraMap S.R S.A π ∈ S.maximalIdealPreimage := by
  change π ∈ S.maximalIdealPreimage.comap (algebraMap S.R S.A)
  rw [maximalIdealPreimage_comap S, hπ]
  exact Ideal.subset_span (by simp)

private lemma uniformizer_isSMulRegular (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) :
    IsSMulRegular S.A (algebraMap S.R S.A π) := by
  have hπ0 : π ≠ 0 := by
    intro heq
    apply IsDiscreteValuationRing.not_a_field S.R
    rw [hπ, heq, Ideal.span_singleton_eq_bot]
  have hreg : IsSMulRegular S.R π := by
    intro x y hxy
    exact mul_left_cancel₀ hπ0 (by simpa only [smul_eq_mul] using hxy)
  exact hreg.of_flat

private lemma atPrime_isRegularLocalRing_of_smoothAt (S : NeronSituation)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage) :
    IsRegularLocalRing (Localization.AtPrime S.maximalIdealPreimage) := by
  obtain ⟨f, hf, hsmf⟩ := hsm
  have : Algebra.Smooth S.R (Localization.Away f) := hsmf
  have : IsRegularRing (Localization.Away f) :=
    Algebra.isRegularRing_of_smooth S.R (Localization.Away f)
  let : Algebra (Localization.Away f)
      (Localization.AtPrime S.maximalIdealPreimage) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
      S.maximalIdealPreimage.primeCompl (Submonoid.powers_le.mpr hf)
  have : IsScalarTower S.A (Localization.Away f)
      (Localization.AtPrime S.maximalIdealPreimage) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : (S.maximalIdealPreimage.map
      (algebraMap S.A (Localization.Away f))).IsPrime :=
    isPrime_map_algebraMap_of_notMem S.maximalIdealPreimage hf
  have : IsLocalization.AtPrime (Localization.AtPrime S.maximalIdealPreimage)
      (S.maximalIdealPreimage.map (algebraMap S.A (Localization.Away f))) :=
    isLocalization_atPrime_map_of_notMem (B := Localization.Away f)
      (C := Localization.AtPrime S.maximalIdealPreimage) hf
  exact IsRegularRing.isRegularLocalRing_of_isLocalization
    (S.maximalIdealPreimage.map (algebraMap S.A (Localization.Away f)))
    (Localization.AtPrime S.maximalIdealPreimage)

private lemma closedFibre_isRegularRing_of_smooth
    (R B : Type*) [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
    [Algebra.Smooth R B] :
    IsRegularRing (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) := by
  let k := R ⧸ IsLocalRing.maximalIdeal R
  let : Field k := Ideal.Quotient.field _
  have : Algebra.Smooth k (TensorProduct R k B) := Algebra.Smooth.baseChange R B k
  have : IsRegularRing (TensorProduct R k B) :=
    Algebra.isRegularRing_of_smooth k (TensorProduct R k B)
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B
      (IsLocalRing.maximalIdeal R)).symm.toRingEquiv

private lemma closedFibre_atPrime_isRegularLocalRing_of_smooth
    (R B : Type*) [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
    [Algebra.Smooth R B] (p : Ideal B) [p.IsPrime]
    (hp : p.comap (algebraMap R B) = IsLocalRing.maximalIdeal R) :
    IsRegularLocalRing
      ((Localization.AtPrime p) ⧸
        Ideal.map (algebraMap R (Localization.AtPrime p))
          (IsLocalRing.maximalIdeal R)) := by
  let k := (IsLocalRing.maximalIdeal R).ResidueField
  have : (IsLocalRing.maximalIdeal R).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  obtain ⟨Q, hQ, hQp⟩ :=
    Ideal.Fiber.exists_comap_includeRight_eq p (IsLocalRing.maximalIdeal R) hp
  subst p
  have : Q.IsPrime := hQ
  have : Algebra.Smooth k ((IsLocalRing.maximalIdeal R).Fiber B) :=
    Algebra.Smooth.baseChange R B k
  have : IsRegularRing ((IsLocalRing.maximalIdeal R).Fiber B) :=
    Algebra.isRegularRing_of_smooth k ((IsLocalRing.maximalIdeal R).Fiber B)
  have : IsRegularLocalRing (Localization.AtPrime Q) :=
    IsRegularRing.isRegularLocalRing_localization Q
  have e := Ideal.Fiber.algEquivAux₂ (IsLocalRing.maximalIdeal R) Q
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at e
  exact @IsRegularLocalRing.of_ringEquiv (Localization.AtPrime Q) _ inferInstance _ _
    e.toRingEquiv

private lemma closedFibre_atPrime_isRegularLocalRing_of_smoothAt
    (S : NeronSituation)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage) :
    IsRegularLocalRing
      ((Localization.AtPrime S.maximalIdealPreimage) ⧸
        Ideal.map (algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage))
          (IsLocalRing.maximalIdeal S.R)) := by
  obtain ⟨f, hf, hsmf⟩ := hsm
  let B := Localization.Away f
  let p : Ideal B := S.maximalIdealPreimage.map (algebraMap S.A B)
  have : p.IsPrime := isPrime_map_algebraMap_of_notMem S.maximalIdealPreimage hf
  have hpunder : p.comap (algebraMap S.R B) = IsLocalRing.maximalIdeal S.R := by
    change Ideal.comap (algebraMap S.R B)
      (Ideal.map (algebraMap S.A B) S.maximalIdealPreimage) = _
    rw [IsScalarTower.algebraMap_eq S.R S.A B, ← Ideal.comap_comap]
    change Ideal.comap (algebraMap S.R S.A)
      (Ideal.under S.A (Ideal.map (algebraMap S.A B) S.maximalIdealPreimage)) = _
    rw [IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) B
      (I := S.maximalIdealPreimage) inferInstance
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf)]
    exact maximalIdealPreimage_comap S
  have : Algebra.Smooth S.R B := hsmf
  have hreg : IsRegularLocalRing
      ((Localization.AtPrime p) ⧸
        Ideal.map (algebraMap S.R (Localization.AtPrime p))
          (IsLocalRing.maximalIdeal S.R)) :=
    closedFibre_atPrime_isRegularLocalRing_of_smooth S.R B p hpunder
  let : Algebra B (Localization.AtPrime S.maximalIdealPreimage) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
      S.maximalIdealPreimage.primeCompl (Submonoid.powers_le.mpr hf)
  have : IsScalarTower S.A B (Localization.AtPrime S.maximalIdealPreimage) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsLocalization.AtPrime
      (Localization.AtPrime S.maximalIdealPreimage) p :=
    isLocalization_atPrime_map_of_notMem (B := B)
      (C := Localization.AtPrime S.maximalIdealPreimage) hf
  have : IsScalarTower S.R B (Localization.AtPrime S.maximalIdealPreimage) :=
    .to₁₃₄ _ S.A _ _
  let e : Localization.AtPrime p ≃ₐ[B]
      Localization.AtPrime S.maximalIdealPreimage :=
    IsLocalization.algEquiv p.primeCompl _ _
  let eR := e.restrictScalars S.R
  have hmap : Ideal.map (eR : Localization.AtPrime p →+*
      Localization.AtPrime S.maximalIdealPreimage)
      (Ideal.map (algebraMap S.R (Localization.AtPrime p))
        (IsLocalRing.maximalIdeal S.R)) =
      Ideal.map (algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage))
        (IsLocalRing.maximalIdeal S.R) := by
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext fun x => eR.commutes x
  exact @IsRegularLocalRing.of_ringEquiv _ _ hreg _ _
    (Ideal.quotientEquiv _ _ eR.toRingEquiv hmap.symm)

private lemma uniformizer_quotient_atPrime_isRegularLocalRing
    (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage) :
    IsRegularLocalRing
      ((Localization.AtPrime S.maximalIdealPreimage) ⧸
        Ideal.span ({(algebraMap S.R
          (Localization.AtPrime S.maximalIdealPreimage)) π} : Set _)) := by
  have h := closedFibre_atPrime_isRegularLocalRing_of_smoothAt S hsm
  have hJ : Ideal.map (algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage))
      (IsLocalRing.maximalIdeal S.R) =
      Ideal.span ({(algebraMap S.R
        (Localization.AtPrime S.maximalIdealPreimage)) π} : Set _) := by
    rw [hπ, Ideal.map_span]
    simp
  rwa [hJ] at h

private lemma uniformizer_atPrime_isSMulRegular
    (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) :
    IsSMulRegular (Localization.AtPrime S.maximalIdealPreimage)
      (algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π) := by
  have hreg := (uniformizer_isSMulRegular S π hπ).of_flat
    (S := Localization.AtPrime S.maximalIdealPreimage)
  simpa only [IsScalarTower.algebraMap_apply S.R S.A
    (Localization.AtPrime S.maximalIdealPreimage)] using hreg

private lemma exists_regular_generators_of_regular_local_ring
    (T : Type*) [CommRing T] [IsRegularLocalRing T] :
    ∃ xs : List T, Ideal.ofList xs = IsLocalRing.maximalIdeal T ∧
      xs.length = (IsLocalRing.maximalIdeal T).spanFinrank ∧
      RingTheory.Sequence.IsRegular T xs := by
  obtain ⟨s, hcard, hspan⟩ :=
    (IsNoetherian.noetherian
      (IsLocalRing.maximalIdeal T)).exists_span_finset_card_eq_spanFinrank
  have hgen : Ideal.ofList s.toList = IsLocalRing.maximalIdeal T := by
    rw [← hspan]
    simp [Ideal.ofList]
  have hlen : s.toList.length = (IsLocalRing.maximalIdeal T).spanFinrank := by
    simp [hcard]
  exact ⟨s.toList, hgen, hlen,
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      T).1 s.toList hgen hlen |>.1⟩

/-- A regular system of parameters indexed by the dimension of a regular local ring. -/
private lemma exists_regular_parameters_of_regular_local_ring
    (T : Type*) [CommRing T] [IsRegularLocalRing T] :
    ∃ (c : ℕ) (g : Fin c → T),
      ringKrullDim T = c ∧
      Ideal.span (Set.range g) = IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T (List.ofFn g) := by
  obtain ⟨xs, hxs, hlen, hreg⟩ := exists_regular_generators_of_regular_local_ring T
  refine ⟨xs.length, xs.get, ?_, ?_, ?_⟩
  · rw [hlen]
    exact (IsRegularLocalRing.spanFinrank_maximalIdeal (R := T)).symm
  · rw [show Set.range xs.get = {x | x ∈ xs} by
      ext x
      exact (List.mem_iff_get).symm]
    exact hxs
  · simpa using hreg

/-- Lift generators of the maximal ideal of a local quotient to generators of the maximal ideal
upstairs, together with the quotient ideal. -/
private lemma exists_lifts_generating_maximalIdeal
    (T : Type*) [CommRing T] [IsLocalRing T] (I : Ideal T)
    [IsLocalRing (T ⧸ I)] (hI : I ≤ IsLocalRing.maximalIdeal T)
    {c : ℕ} (g : Fin c → T ⧸ I)
    (hg : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (T ⧸ I)) :
    ∃ x : Fin c → T,
      (∀ i, Ideal.Quotient.mk I (x i) = g i) ∧
      I ⊔ Ideal.span (Set.range x) = IsLocalRing.maximalIdeal T := by
  choose x hx using fun i => Ideal.Quotient.mk_surjective (g i)
  have hxmem : ∀ i, x i ∈ IsLocalRing.maximalIdeal T := by
    intro i
    have hgi : g i ∈ IsLocalRing.maximalIdeal (T ⧸ I) := by
      rw [← hg]
      exact Ideal.subset_span ⟨i, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal (x i)).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal (g i)).mp hgi
        ((hx i) ▸ hu.map (Ideal.Quotient.mk I))
  refine ⟨x, hx, ?_⟩
  have hmapeq : Ideal.map (Ideal.Quotient.mk I)
      (I ⊔ Ideal.span (Set.range x)) =
      Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal T) := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_quotient_self, bot_sup_eq,
      ← Set.range_comp, IsLocalRing.map_maximalIdeal_of_surjective _
        Ideal.Quotient.mk_surjective, ← hg]
    exact congrArg (fun v : Fin c → T ⧸ I => Ideal.span (Set.range v))
      (funext hx)
  have h := (Ideal.map_eq_iff_sup_ker_eq_of_surjective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).mp hmapeq
  rwa [Ideal.mk_ker, sup_right_comm, sup_idem,
    sup_eq_left.mpr hI] at h

open scoped Pointwise in
private lemma regular_cons_of_regular_quotient
    (T : Type*) [CommRing T] (π : T)
    (hπ : IsSMulRegular T π) (xs : List T)
    (hxs : RingTheory.Sequence.IsRegular (T ⧸ Ideal.span ({π} : Set T))
      (xs.map (Ideal.Quotient.mk (Ideal.span ({π} : Set T))))) :
    RingTheory.Sequence.IsRegular T (π :: xs) := by
  let I : Ideal T := Ideal.span ({π} : Set T)
  have heq : π • (⊤ : Submodule T T) = (I : Submodule T T) := by
    simp [I, ← Submodule.ideal_span_singleton_smul]
  let e : QuotSMulTop π T ≃ₗ[T] T ⧸ I :=
    Submodule.quotEquivOfEq _ _ heq
  have hregT : RingTheory.Sequence.IsRegular (T ⧸ I) xs := by
    have hcongr : RingTheory.Sequence.IsRegular (T ⧸ I) xs ↔
        RingTheory.Sequence.IsRegular (T ⧸ I) (xs.map (Ideal.Quotient.mk I)) :=
      (AddEquiv.refl (T ⧸ I)).isRegular_congr
        (List.forall₂_map_right_iff.mpr <|
          List.forall₂_same.mpr fun r _ y =>
            (algebraMap_smul (T ⧸ I) r y).symm)
    exact hcongr.mpr hxs
  have hreg := (e.isRegular_congr xs).mpr hregT
  exact (RingTheory.Sequence.isRegular_cons_iff T π xs).mpr ⟨hπ, hreg⟩

/-- A regular parameter sequence for a regular closed fibre lifts across a regular element to a
regular sequence generating the maximal ideal. -/
private lemma exists_regular_parameters_of_regular_quotient
    (T : Type*) [CommRing T] [IsRegularLocalRing T] (π : T)
    (hπmem : π ∈ IsLocalRing.maximalIdeal T)
    (hπreg : IsSMulRegular T π)
    (hquot : IsRegularLocalRing (T ⧸ Ideal.span ({π} : Set T))) :
    ∃ (c : ℕ) (g : Fin c → T),
      ringKrullDim (T ⧸ Ideal.span ({π} : Set T)) = c ∧
      IsLocalRing.maximalIdeal T =
        Ideal.span ({π} : Set T) ⊔ Ideal.span (Set.range g) ∧
      RingTheory.Sequence.IsRegular T (π :: List.ofFn g) := by
  let I : Ideal T := Ideal.span ({π} : Set T)
  have : IsRegularLocalRing (T ⧸ I) := hquot
  obtain ⟨c, q, hdim, hgen, hreg⟩ :=
    exists_regular_parameters_of_regular_local_ring (T ⧸ I)
  have hI : I ≤ IsLocalRing.maximalIdeal T :=
    Ideal.span_le.mpr (by simpa using hπmem)
  obtain ⟨g, hg, hgen'⟩ :=
    exists_lifts_generating_maximalIdeal T I hI q hgen
  refine ⟨c, g, hdim, hgen'.symm, ?_⟩
  have hmap : (List.ofFn g).map (Ideal.Quotient.mk I) = List.ofFn q := by
    simp only [List.map_ofFn]
    congr 1
    exact funext hg
  exact regular_cons_of_regular_quotient T π hπreg (List.ofFn g)
    (hmap.symm ▸ hreg)

/-- Equality of a finitely generated ideal and a subideal at a prime spreads to a principal
neighbourhood of that prime. -/
private lemma exists_away_map_eq_of_map_eq
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I J p : Ideal R) [p.IsPrime] (hJI : J ≤ I)
    (hmap : J.map (algebraMap R (Localization.AtPrime p)) =
      I.map (algebraMap R (Localization.AtPrime p))) :
    ∃ g ∉ p, J.map (algebraMap R (Localization.Away g)) =
      I.map (algebraMap R (Localization.Away g)) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  have hx : ∀ y : {y : R // y ∈ s}, ∃ m : p.primeCompl, (m : R) * (y : R) ∈ J := by
    intro y
    have hy : (algebraMap R (Localization.AtPrime p)) y ∈
        J.map (algebraMap R (Localization.AtPrime p)) := by
      rw [hmap, ← hs]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span y.property)
    obtain ⟨m, hm, hmy⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
        (Localization.AtPrime p) J y).mp hy
    exact ⟨⟨m, hm⟩, hmy⟩
  choose m hm using hx
  let g : p.primeCompl := s.attach.prod m
  refine ⟨g, g.property, ?_⟩
  apply le_antisymm (Ideal.map_mono hJI)
  rw [← hs, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro z ⟨y, hy, rfl⟩
  let yy : {y : R // y ∈ s} := ⟨y, hy⟩
  have hdvd : (m yy : R) ∣ (g : R) := by
    simpa [g, Submonoid.coe_prod] using
      (Finset.dvd_prod_of_mem (fun x : {y : R // y ∈ s} => (m x : R))
        (Finset.mem_attach _ yy))
  obtain ⟨d, hd⟩ := hdvd
  have hgy : (g : R) * y ∈ J := by
    rw [hd]
    convert J.mul_mem_left d (hm yy) using 1
    ring
  have hgy' : (algebraMap R (Localization.Away (g : R))) ((g : R) * y) ∈
      J.map (algebraMap R (Localization.Away (g : R))) :=
    Ideal.mem_map_of_mem _ hgy
  have hunit : IsUnit ((algebraMap R (Localization.Away (g : R))) (g : R)) :=
    IsLocalization.Away.algebraMap_isUnit (g : R)
  apply (Ideal.mul_unit_mem_iff_mem _ hunit).mp
  simpa only [map_mul, mul_comm] using hgy'

/-- A finite family in a localization at a prime is defined on one principal neighbourhood of
the prime. -/
private lemma exists_away_lifts_of_atPrime
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
    {c : ℕ} (g : Fin c → Localization.AtPrime p) :
    ∃ f : A, ∃ (hf : f ∉ p) (g' : Fin c → Localization.Away f),
      letI : Algebra (Localization.Away f) (Localization.AtPrime p) :=
        IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
          p.primeCompl (Submonoid.powers_le.mpr hf)
      ∀ i, algebraMap (Localization.Away f) (Localization.AtPrime p) (g' i) = g i := by
  classical
  choose z hz using fun i => IsLocalization.mk'_surjective p.primeCompl (g i)
  let a : Fin c → A := fun i => (z i).1
  let s : Fin c → p.primeCompl := fun i => (z i).2
  let f : p.primeCompl := ∏ i, s i
  have hf : (f : A) ∉ p := f.property
  let : Algebra (Localization.Away (f : A)) (Localization.AtPrime p) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers (f : A))
      p.primeCompl (Submonoid.powers_le.mpr hf)
  have : IsScalarTower A (Localization.Away (f : A)) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have hdiv (i : Fin c) : (s i : A) ∣ (f : A) := by
    simpa [f, Submonoid.coe_prod] using
      (Finset.dvd_prod_of_mem (fun j : Fin c => (s j : A)) (Finset.mem_univ i))
  let u (i : Fin c) : (Localization.Away (f : A))ˣ :=
    (IsLocalization.Away.isUnit_of_dvd (f : A) (hdiv i)).unit
  let g' (i : Fin c) : Localization.Away (f : A) :=
    algebraMap A (Localization.Away (f : A)) (a i) * (u i)⁻¹
  refine ⟨f, hf, g', ?_⟩
  intro i
  have hlocal : g' i * algebraMap A (Localization.Away (f : A)) (s i : A) =
      algebraMap A (Localization.Away (f : A)) (a i) := by
    simp [g', u, mul_assoc]
  have hlocal' := congrArg
    (algebraMap (Localization.Away (f : A)) (Localization.AtPrime p)) hlocal
  have hspec := IsLocalization.mk'_spec (Localization.AtPrime p) (a i) (s i)
  have hi : IsLocalization.mk' (Localization.AtPrime p) (a i) (s i) = g i := by
    simpa [Function.uncurry, a, s] using hz i
  rw [hi] at hspec
  apply (IsLocalization.map_units (Localization.AtPrime p) (s i)).mul_right_cancel
  have hlocal'' :
      algebraMap (Localization.Away (f : A)) (Localization.AtPrime p) (g' i) *
        algebraMap A (Localization.AtPrime p) (s i : A) =
        algebraMap A (Localization.AtPrime p) (a i) := by
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply] using hlocal'
  exact hlocal''.trans hspec.symm

/-- Regularity of a sequence at a prime spreads to a principal neighbourhood for the ring
itself. -/
private lemma exists_regular_sequence_away_of_atPrime
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (xs : List A)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime p)
      (xs.map (algebraMap A (Localization.AtPrime p)))) :
    ∃ f ∉ p, RingTheory.Sequence.IsRegular (Localization.Away f)
      (xs.map (algebraMap A (Localization.Away f))) := by
  have e (S : Submonoid A) : LocalizedModule S A ≃ₗ[Localization S] Localization S :=
    IsLocalizedModule.mapEquiv S (LocalizedModule.mkLinearMap S A)
      (Algebra.linearMap A (Localization S)) (Localization S) (LinearEquiv.refl A A)
  obtain ⟨f, hf, haway⟩ := regular_sequence_localize_away_of_atPrime p xs
    ((e _).isRegular_congr _ |>.mpr hreg)
  exact ⟨f, hf, ((e _).isRegular_congr _).mp haway⟩

private lemma ideal_map_injective_ringEquiv
    {B C : Type*} [CommRing B] [CommRing C] (e : B ≃+* C) :
    Function.Injective (Ideal.map e) := by
  intro I J h
  have h' := congrArg (Ideal.map e.symm) h
  have hk : Ideal.comap e ⊥ = ⊥ := by
    ext x
    simp
  simpa [Ideal.comap_map_of_surjective e e.surjective, hk] using h'

private lemma isRegular_of_isLocalization_of_mem_prime
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A) [IsLocalization S B]
    (p : Ideal A) [p.IsPrime]
    (hd : Disjoint (S : Set A) (p : Set A)) (xs : List A)
    (hreg : RingTheory.Sequence.IsRegular A xs)
    (hmem : ∀ x ∈ xs, x ∈ p) :
    RingTheory.Sequence.IsRegular B (xs.map (algebraMap A B)) := by
  let q : Ideal B := p.map (algebraMap A B)
  have : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint S B p inferInstance hd
  refine ⟨hreg.toIsWeaklyRegular.of_isLocalization B S, ?_⟩
  have hq : Ideal.ofList (xs.map (algebraMap A B)) ≤ q := by
    apply Ideal.span_le.mpr
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact Ideal.mem_map_of_mem _ (hmem x hx)
  intro heq
  have hq' : Ideal.ofList (xs.map (algebraMap A B)) • (⊤ : Submodule B B) ≤ q := by
    simpa using hq
  exact (inferInstance : q.IsPrime).ne_top (top_le_iff.mp (heq.symm ▸ hq'))

private lemma isH1Regular_of_isRegular_cons {T : Type*} [CommRing T] {c : ℕ}
    (π : T) (g : Fin c → T)
    (hreg : RingTheory.Sequence.IsRegular T (π :: List.ofFn g)) :
    Koszul.IsH1Regular (Fin.cases π g) := by
  have hlist : List.ofFn (Fin.cases π g) = π :: List.ofFn g := by simp
  have hreg' : RingTheory.Sequence.IsRegular T (List.ofFn (Fin.cases π g)) := by
    rwa [hlist]
  exact (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
    (M := T)).2.2 hreg' |>.isH1Regular

/-- A regular sequence `π, g₁, …, g_c` generating an ideal `I` presents the affine blowup
algebra `B[I/π]` as `B[y₁, …, y_c]/(π yᵢ - gᵢ)`. -/
private lemma exists_blowupChart_algEquiv
    {B : Type*} [CommRing B] {c : ℕ} (I : Ideal B) (π : B) (g : Fin c → B)
    (hI : I = Ideal.span ({π} : Set B) ⊔ Ideal.span (Set.range g))
    (hreg : RingTheory.Sequence.IsRegular B (π :: List.ofFn g)) :
    Nonempty (affineBlowupAlgebra I π (Localization.Away π) ≃ₐ[B]
      MvPolynomial (Fin c) B ⧸ Ideal.span (Set.range fun i : Fin c ↦
        MvPolynomial.C π * MvPolynomial.X i - MvPolynomial.C (g i))) := by
  let f : Fin (c + 1) → B := Fin.cases π g
  have hspan : Ideal.span (Set.range f) = I := by
    rw [hI]
    rw [show Set.range f = insert π (Set.range g) from Fin.range_cons π g, Ideal.span_insert]
  obtain ⟨e⟩ := Koszul.exists_affineBlowup_algEquiv_mvPolynomial_quotient_of_isH1Regular
    f (isH1Regular_of_isRegular_cons π g hreg)
  rw [hspan, affineBlowupAlgebraAway_eq_affineBlowupAlgebra] at e
  exact ⟨e⟩

/-- Any presentation of the affine blowup algebra sends the fraction `gᵢ/π` to the displayed
variable, because the denominator is invertible in the ambient localization. -/
private lemma blowupChart_algEquiv_fraction
    {B : Type*} [CommRing B] {c : ℕ} (I : Ideal B) (π : B) (g : Fin c → B)
    (hg : ∀ i, g i ∈ I)
    (e : affineBlowupAlgebra I π (Localization.Away π) ≃ₐ[B]
      MvPolynomial (Fin c) B ⧸ Ideal.span (Set.range fun i : Fin c ↦
        MvPolynomial.C π * MvPolynomial.X i - MvPolynomial.C (g i))) (i : Fin c) :
    e (affineBlowupFraction I π (Localization.Away π) (hg i)) =
      Ideal.Quotient.mk _ (MvPolynomial.X i) := by
  have hleft :
      affineBlowupFraction I π (Localization.Away π) (hg i) *
        algebraMap B (affineBlowupAlgebra I π (Localization.Away π)) π =
      algebraMap B (affineBlowupAlgebra I π (Localization.Away π)) (g i) :=
    (mul_comm _ _).trans
      (algebraMap_mul_affineBlowupFraction I π (Localization.Away π) (hg i))
  have hright :
      e.symm (Ideal.Quotient.mk _ (MvPolynomial.X i)) *
        algebraMap B (affineBlowupAlgebra I π (Localization.Away π)) π =
      algebraMap B (affineBlowupAlgebra I π (Localization.Away π)) (g i) := by
    apply e.injective
    rw [map_mul, e.apply_symm_apply, e.commutes, e.commutes]
    let J : Ideal (MvPolynomial (Fin c) B) :=
      Ideal.span (Set.range fun j : Fin c =>
        MvPolynomial.C π * MvPolynomial.X j - MvPolynomial.C (g j))
    change Ideal.Quotient.mk J (MvPolynomial.X i) *
        Ideal.Quotient.mk J (MvPolynomial.C π) =
      Ideal.Quotient.mk J (MvPolynomial.C (g i))
    rw [← map_mul, mul_comm (MvPolynomial.X i) (MvPolynomial.C π)]
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have hcancel : ∀ x y : affineBlowupAlgebra I π (Localization.Away π),
      x * algebraMap B (affineBlowupAlgebra I π (Localization.Away π)) π =
      y * algebraMap B (affineBlowupAlgebra I π (Localization.Away π)) π → x = y := by
    intro x y hxy
    apply Subtype.ext
    have hxy' := congrArg Subtype.val hxy
    change (x : Localization.Away π) * algebraMap B (Localization.Away π) π =
      (y : Localization.Away π) * algebraMap B (Localization.Away π) π at hxy'
    have := congrArg (fun z : Localization.Away π =>
      z * IsLocalization.Away.invSelf π) hxy'
    simpa [mul_assoc, IsLocalization.Away.mul_invSelf] using this
  exact (congrArg e (hcancel _ _ (hleft.trans hright.symm))).trans (e.apply_symm_apply _)

private lemma exists_blowupChart_algEquiv_fraction
    {B : Type*} [CommRing B] {c : ℕ} (I : Ideal B) (π : B) (g : Fin c → B)
    (hI : I = Ideal.span ({π} : Set B) ⊔ Ideal.span (Set.range g))
    (hreg : RingTheory.Sequence.IsRegular B (π :: List.ofFn g))
    (hg : ∀ i, g i ∈ I) :
    Nonempty {e : affineBlowupAlgebra I π (Localization.Away π) ≃ₐ[B]
      MvPolynomial (Fin c) B ⧸ Ideal.span (Set.range fun i : Fin c ↦
        MvPolynomial.C π * MvPolynomial.X i - MvPolynomial.C (g i)) //
      ∀ i, e (affineBlowupFraction I π (Localization.Away π) (hg i)) =
        Ideal.Quotient.mk _ (MvPolynomial.X i)} := by
  obtain ⟨e⟩ := exists_blowupChart_algEquiv I π g hI hreg
  exact ⟨⟨e, blowupChart_algEquiv_fraction I π g hg e⟩⟩

end Stacks.Smoothing

end
