module

public import StacksFrontier.RingTheory.CohenMacaulay.Module
public import StacksFrontier.RingTheory.SerreIntersection.EqualCharacteristic
public import StacksFrontier.RingTheory.SerreIntersection.QuotientEulerVanishing
public import StacksFrontier.RingTheory.SerreIntersection.UnramifiedDiagonal

/-!
# Serre's dimension inequality over an arbitrary regular local ring

Let `(A, 𝔪)` be a regular local ring and let `M`, `N` be nonzero finite `A`-modules with `M ⊗_A N`
supported in `{𝔪}`. Then `dim Supp M + dim Supp N ≤ dim A` [Serre, *Algèbre locale*, V.B.6].

After completing, `A` either contains a field (`supportDim_add_supportDim_le_of_field`) or has a
Cohen coefficient ring `Λ` (a complete discrete valuation ring with maximal ideal `(p)`). In the
second case `A = S ⧸ (g)` for `S = Λ[[x_1, …, x_n]]`, `n = dim A`, and a nonzerodivisor `g`
(`exists_surjective_mvPowerSeries_ker_eq_span`): send the `x_i` to a regular system of
parameters `y_i` of `A` and take `g = p - ∑ sᵢ xᵢ` for any lift `∑ sᵢ yᵢ` of `p`; `g` belongs to
a minimal system of generators of the maximal ideal of `S`, so `S ⧸ (g)` is regular of
dimension `n` and maps isomorphically onto `A`.

Over `S` the inequality `r + s ≤ n + 1` holds (`supportDim_add_supportDim_le_of_mvPowerSeries`).
If `r + s = n + 1`, choose top-dimensional points `𝔭`, `𝔮` of the two supports: the Euler
characteristic `χ^S(A ⧸ 𝔭, A ⧸ 𝔮)` is positive by Serre's positivity over `S`
(`torEulerCharacteristic_quotient_pos_of_mvPowerSeries`) and zero because both modules are killed
by `g` (`torEulerCharacteristic_eq_zero_of_quotient`). Hence `r + s ≤ n`.

## Main results

* `Stacks.SerreIntersection.exists_surjective_mvPowerSeries_ker_eq_span` — the presentation.
* `Stacks.SerreIntersection.supportDim_add_supportDim_le_of_isCohenRing` — the inequality for a
  complete regular local ring with a Cohen coefficient ring.
* `Stacks.SerreIntersection.supportDim_add_supportDim_le` — **Serre's inequality** for every
  regular local ring.
-/

@[expose] public noncomputable section

open MvPowerSeries IsLocalRing Stacks.CompleteLocalRing.RegularSubring
open scoped TensorProduct

universe u

namespace Stacks.SerreIntersection

/-- The power series ring `Λ[[x_1, …, x_n]]` over a Cohen ring has Krull dimension `n + 1`. -/
private theorem ringKrullDim_mvPowerSeries_fin {Λ : Type u} [CommRing Λ] [IsDomain Λ]
    [IsCohenRing Λ] (n : ℕ) :
    ringKrullDim (MvPowerSeries (Fin n) Λ) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
  rw [MvPowerSeries.ringKrullDim_fin_eq_add, IsDiscreteValuationRing.ringKrullDim_eq_one]
  push_cast
  exact add_comm _ _

section Presentation

variable {A : Type u} [CommRing A] [IsRegularLocalRing A] [IsAdicComplete (maximalIdeal A) A]
  {Λ : Type u} [CommRing Λ] [IsDomain Λ] [IsCohenRing Λ] {p : ℕ}
  (hΛ : maximalIdeal Λ = Ideal.span {(p : Λ)})
  (φ : Λ →+* A) (hφm : ∀ x : Λ, ¬ IsUnit x → φ x ∈ maximalIdeal A)
  (hφs : Function.Surjective ((residue A).comp φ))

include hΛ hφm hφs in
/-- **A complete regular local ring with a Cohen coefficient ring is a power series ring modulo
a nonzerodivisor.** If `dim A = n`, there are a surjection `F : Λ[[x_1, …, x_n]] → A` and a
nonzerodivisor `g` with `ker F = (g)`. -/
theorem exists_surjective_mvPowerSeries_ker_eq_span (n : ℕ) (hn : ringKrullDim A = n) :
    ∃ F : MvPowerSeries (Fin n) Λ →+* A, Function.Surjective F ∧
      ∃ g : MvPowerSeries (Fin n) Λ, IsSMulRegular (MvPowerSeries (Fin n) Λ) g ∧
        RingHom.ker F = Ideal.span {g} := by
  -- a regular system of parameters
  have hsf : (maximalIdeal A).spanFinrank = n := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hn] at h
    exact_mod_cast h
  obtain ⟨s, hcard, hs⟩ :=
    (IsNoetherian.noetherian (maximalIdeal A)).exists_span_finset_card_eq_spanFinrank
  rw [hsf] at hcard
  let y : Fin n → A := fun i => (s.equivFin.symm (Fin.cast hcard.symm i) : A)
  have hy : Ideal.span (Set.range y) = maximalIdeal A := by
    rw [← hs]
    congr 1
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm _).2
    · intro ha
      refine ⟨Fin.cast hcard (s.equivFin ⟨a, ha⟩), ?_⟩
      simp [y]
  obtain ⟨F, hFs, hFX, hFC⟩ := Stacks.CompleteLocalRing.CohenStructure.exists_surjective_eval₂Hom
    (maximalIdeal A) y hy φ hφs
  refine ⟨F, hFs, ?_⟩
  -- the element `g`
  have hpΛ : (p : Λ) ∈ maximalIdeal Λ := hΛ ▸ Ideal.mem_span_singleton_self _
  have hpA : φ p ∈ Ideal.span (Set.range y) := by
    rw [hy]
    exact hφm _ ((mem_maximalIdeal _).mp hpΛ)
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hpA
  choose t ht using fun i => hFs (a i)
  set g : MvPowerSeries (Fin n) Λ := C (p : Λ) - ∑ i, t i * X i with hg
  have hgF : F g = 0 := by
    rw [hg, map_sub, hFC, map_sum, ← ha, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hFX, ht]
  -- `g, x_1, …, x_n` is a minimal system of generators of the maximal ideal
  have : IsRegularLocalRing (MvPowerSeries (Fin n) Λ) := MvPowerSeries.isRegularLocalRing Λ n
  have hdimS := ringKrullDim_mvPowerSeries_fin (Λ := Λ) n
  let xs : List (MvPowerSeries (Fin n) Λ) := g :: List.ofFn X
  have hofFn : Ideal.ofList (List.ofFn (X : Fin n → MvPowerSeries (Fin n) Λ)) =
      Ideal.span (Set.range X) := by
    show Ideal.span _ = _
    congr 1
    ext z
    simp only [Set.mem_setOf_eq, List.mem_ofFn, Set.mem_range]
  have hsumX : ∑ i, t i * X i ∈ Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) Λ)) :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have hxs : Ideal.ofList xs = maximalIdeal (MvPowerSeries (Fin n) Λ) := by
    rw [Ideal.ofList_cons, hofFn, maximalIdeal_mvPowerSeries, hΛ, Ideal.map_span,
      Set.image_singleton]
    apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rw [Ideal.span_singleton_le_iff_mem, hg]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
        (Ideal.mem_sup_right hsumX)
    · refine sup_le ?_ le_sup_right
      rw [Ideal.span_singleton_le_iff_mem]
      have : (C (p : Λ) : MvPowerSeries (Fin n) Λ) = g + ∑ i, t i * X i := by rw [hg]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
        (Ideal.mem_sup_right hsumX)
  have hlen : xs.length = (maximalIdeal (MvPowerSeries (Fin n) Λ)).spanFinrank := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := MvPowerSeries (Fin n) Λ)
    rw [hdimS] at h
    have h' : (maximalIdeal (MvPowerSeries (Fin n) Λ)).spanFinrank = n + 1 := by exact_mod_cast h
    simp [xs, h']
  have hquot :=
    ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      (MvPowerSeries (Fin n) Λ)).1 xs hxs hlen).2 1 (by simp [xs])
  have htake : Ideal.ofList (xs.take 1) = Ideal.span {g} := by
    simp [xs]
  rw [htake] at hquot
  obtain ⟨hDreg, hDdim⟩ := hquot
  -- `S ⧸ (g)` maps isomorphically onto `A`
  let D := MvPowerSeries (Fin n) Λ ⧸ Ideal.span {g}
  have : IsRegularLocalRing D := hDreg
  have : IsDomain D := IsRegularLocalRing.isDomain D
  have hgker : ∀ z ∈ Ideal.span {g}, F z = 0 := fun z hz => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [map_mul, hgF, mul_zero]
  let ψ : D →+* A := Ideal.Quotient.lift (Ideal.span {g}) F hgker
  have hψs : Function.Surjective ψ := fun x => by
    obtain ⟨z, rfl⟩ := hFs x
    exact ⟨Ideal.Quotient.mk _ z, rfl⟩
  have hψ : RingHom.ker ψ = ⊥ := by
    by_contra hne
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hzr : z ∈ nonZeroDivisors D := mem_nonZeroDivisors_of_ne_zero hz0
    have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hzr
    let ψ' : D ⧸ Ideal.span {z} →+* A := Ideal.Quotient.lift (Ideal.span {z}) ψ (fun w hw => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
      rw [map_mul, RingHom.mem_ker.mp hz, mul_zero])
    have hψ's : Function.Surjective ψ' := fun x => by
      obtain ⟨w, rfl⟩ := hψs x
      exact ⟨Ideal.Quotient.mk _ w, rfl⟩
    have h1 := ringKrullDim_le_of_surjective ψ' hψ's
    have hD1 : ringKrullDim D + 1 = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← hdimS, ← hDdim, Nat.cast_one]
    have h4 : ((n : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim D :=
      le_trans (by rw [← hn]; gcongr) hle
    have h5 : ((n : ℕ) : WithBot ℕ∞) + 1 + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← hD1]; gcongr
    have h6 : ((n + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h5
    have : n + 1 + 1 ≤ n + 1 := by exact_mod_cast h6
    omega
  refine ⟨g, ?_, ?_⟩
  · -- `g` is a nonzerodivisor
    have := IsRegularLocalRing.isDomain (MvPowerSeries (Fin n) Λ)
    have hp0 : (p : Λ) ≠ 0 := fun h => by
      have : IsField Λ := by
        rw [IsLocalRing.isField_iff_maximalIdeal_eq, hΛ, h, Ideal.span_singleton_eq_bot]
      exact IsDiscreteValuationRing.not_isField Λ this
    have hg0 : g ≠ 0 := fun h => hp0 (by
      have := congrArg (constantCoeff (σ := Fin n) (R := Λ)) h
      rw [hg, map_sub, constantCoeff_C, map_sum] at this
      simpa using this)
    exact fun a b hab => mul_left_cancel₀ hg0 hab
  · ext z
    constructor
    · intro hz
      have : Ideal.Quotient.mk (Ideal.span {g}) z ∈ RingHom.ker ψ := hz
      rw [hψ, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
      exact this
    · exact hgker z

end Presentation

section Complete

variable {A : Type u} [CommRing A] [IsRegularLocalRing A] [IsAdicComplete (maximalIdeal A) A]
  {Λ : Type u} [CommRing Λ] [IsDomain Λ] [IsCohenRing Λ] {p : ℕ}
  (hΛ : maximalIdeal Λ = Ideal.span {(p : Λ)})
  (φ : Λ →+* A) (hφm : ∀ x : Λ, ¬ IsUnit x → φ x ∈ maximalIdeal A)
  (hφs : Function.Surjective ((residue A).comp φ))

/-- `S ⧸ F⁻¹(𝔭) ≅ A ⧸ 𝔭` for a surjective algebra map `S → A`. -/
def quotientComapAlgEquiv {S : Type u} [CommRing S] [Algebra S A]
    (hT : Function.Surjective (algebraMap S A)) (P : Ideal A) :
    (S ⧸ P.comap (algebraMap S A)) ≃ₐ[S] A ⧸ P :=
  (Ideal.quotientEquivAlgOfEq S (by
      ext x
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply,
        Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem])).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := (Ideal.Quotient.mkₐ S P).comp (Algebra.ofId S A))
      (Ideal.Quotient.mk_surjective.comp hT))

include hΛ hφm hφs in
/-- **Serre's dimension inequality for a complete regular local ring with a Cohen coefficient
ring.** -/
theorem supportDim_add_supportDim_le_of_isCohenRing (M N : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M] [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Nontrivial N] (hMN : Module.support A (M ⊗[A] N) ⊆ {closedPoint A}) :
    Module.supportDim A M + Module.supportDim A N ≤ ringKrullDim A := by
  obtain ⟨n, hn⟩ := Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim A
  obtain ⟨F, hFs, g, hg, hker⟩ := exists_surjective_mvPowerSeries_ker_eq_span hΛ φ hφm hφs n hn
  let : Algebra (MvPowerSeries (Fin n) Λ) A := F.toAlgebra
  have hT : Function.Surjective (algebraMap (MvPowerSeries (Fin n) Λ) A) := hFs
  have hdimΛ : ringKrullDim Λ = 1 := IsDiscreteValuationRing.ringKrullDim_eq_one Λ
  have : IsRegularLocalRing (MvPowerSeries (Fin n) Λ) := MvPowerSeries.isRegularLocalRing Λ n
  -- top-dimensional points of the supports
  obtain ⟨P, hPM, hP⟩ := PowerSeriesDiagonal.exists_mem_support_supportDim_quotient_eq (A := A) M
  obtain ⟨Q, hQN, hQ⟩ := PowerSeriesDiagonal.exists_mem_support_supportDim_quotient_eq (A := A) N
  rw [← hP, ← hQ]
  set P' := P.asIdeal.comap (algebraMap (MvPowerSeries (Fin n) Λ) A)
  set Q' := Q.asIdeal.comap (algebraMap (MvPowerSeries (Fin n) Λ) A)
  let eP := quotientComapAlgEquiv hT P.asIdeal
  let eQ := quotientComapAlgEquiv hT Q.asIdeal
  have hdim : ∀ I : Ideal A,
      Module.supportDim (MvPowerSeries (Fin n) Λ)
          (MvPowerSeries (Fin n) Λ ⧸ I.comap (algebraMap (MvPowerSeries (Fin n) Λ) A)) =
        Module.supportDim A (A ⧸ I) := fun I => by
    rw [Module.supportDim_quotient_eq_ringKrullDim, Module.supportDim_quotient_eq_ringKrullDim]
    exact ringKrullDim_eq_of_ringEquiv (quotientComapAlgEquiv hT I).toRingEquiv
  have hdimP := hdim P.asIdeal
  have hdimQ := hdim Q.asIdeal
  -- the two quotients meet in the closed point, over `A` and over `S`
  have hsuppA : Module.support A ((A ⧸ P.asIdeal) ⊗[A] (A ⧸ Q.asIdeal)) ⊆ {closedPoint A} := by
    rw [Stacks.Intersection.support_tensorProduct_eq_inter]
    refine fun q hq => hMN ?_
    rw [Stacks.Intersection.support_tensorProduct_eq_inter]
    exact ⟨PowerSeriesDiagonal.support_quotient_subset_support M hPM hq.1,
      PowerSeriesDiagonal.support_quotient_subset_support N hQN hq.2⟩
  have hsuppS : Module.support (MvPowerSeries (Fin n) Λ)
      ((MvPowerSeries (Fin n) Λ ⧸ P') ⊗[MvPowerSeries (Fin n) Λ] (MvPowerSeries (Fin n) Λ ⧸ Q'))
        ⊆ {closedPoint (MvPowerSeries (Fin n) Λ)} := by
    rw [Stacks.Intersection.support_tensorProduct_eq_inter]
    rintro q ⟨hqP, hqQ⟩
    rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] at hqP hqQ
    have hkq : RingHom.ker F ≤ q.asIdeal := by
      refine le_trans ?_ hqP
      intro x hx
      show F x ∈ P.asIdeal
      rw [RingHom.mem_ker.mp hx]
      exact Ideal.zero_mem _
    have := Ideal.map_isPrime_of_surjective hFs hkq
    have hcomap : (Ideal.map F q.asIdeal).comap F = q.asIdeal := by
      rw [Ideal.comap_map_of_surjective F hFs, sup_eq_left]
      exact hkq
    have hle : ∀ I : Ideal A, I.comap F ≤ q.asIdeal → I ≤ Ideal.map F q.asIdeal := fun I h => by
      rw [← Ideal.map_comap_of_surjective F hFs I]
      exact Ideal.map_mono h
    have hPq := hle _ hqP
    have hQq := hle _ hqQ
    let q' : PrimeSpectrum A := ⟨Ideal.map F q.asIdeal, inferInstance⟩
    have hmem : q' ∈ ({closedPoint A} : Set (PrimeSpectrum A)) := hsuppA (by
      rw [Stacks.Intersection.support_tensorProduct_eq_inter]
      constructor <;>
        rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] <;> assumption)
    have hmem' : Ideal.map F q.asIdeal = maximalIdeal A :=
      congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hmem)
    rw [Set.mem_singleton_iff, PrimeSpectrum.ext_iff, closedPoint]
    show q.asIdeal = maximalIdeal _
    rw [← hcomap, hmem']
    have := Ideal.comap_isMaximal_of_surjective F hFs (K := maximalIdeal A)
    exact IsLocalRing.eq_maximalIdeal this
  -- over `S`: `r + s ≤ n + 1`
  have hS := PowerSeriesDiagonal.supportDim_add_supportDim_le_of_mvPowerSeries hΛ hdimΛ
    (MvPowerSeries (Fin n) Λ ⧸ P') (MvPowerSeries (Fin n) Λ ⧸ Q') hsuppS
  have : Nontrivial (A ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr P.2.ne_top
  have : Nontrivial (A ⧸ Q.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr Q.2.ne_top
  obtain ⟨r, hr⟩ := exists_supportDim_eq_natCast A (A ⧸ P.asIdeal)
  obtain ⟨s, hs⟩ := exists_supportDim_eq_natCast A (A ⧸ Q.asIdeal)
  have hdimS := ringKrullDim_mvPowerSeries_fin (Λ := Λ) n
  rw [hdimP, hdimQ, hr, hs, hdimS] at hS
  have hrs : r + s ≤ n + 1 := by exact_mod_cast hS
  rw [hr, hs, hn]
  by_contra hlt
  have hlt' : ¬ r + s ≤ n := fun h => hlt (by exact_mod_cast h)
  have heq : r + s = n + 1 := by omega
  -- positivity over `S` against vanishing for modules over `S ⧸ (g)`
  have hpos := PowerSeriesDiagonal.torEulerCharacteristic_quotient_pos_of_mvPowerSeries hΛ hdimΛ
    P' Q' hsuppS (by rw [hdimP, hdimQ, hr, hs, hdimS]; exact_mod_cast heq)
  have hzero := torEulerCharacteristic_eq_zero_of_quotient hT hker hg (A ⧸ P.asIdeal)
    (A ⧸ Q.asIdeal) hsuppA
  rw [torEulerCharacteristic_congr_left eP.toLinearEquiv, torEulerCharacteristic_comm,
    torEulerCharacteristic_congr_left eQ.toLinearEquiv, torEulerCharacteristic_comm, hzero] at hpos
  exact lt_irrefl _ hpos

end Complete

section General

/-- **Serre's dimension inequality** [Serre, *Algèbre locale*, V.B.6]. Let `A` be a regular local
ring and let `M`, `N` be nonzero finite `A`-modules with `M ⊗_A N` supported in the closed point.
Then `dim Supp M + dim Supp N ≤ dim A`.

The statement passes to the completion; a complete regular local ring either contains a field
(`supportDim_add_supportDim_le_of_field`) or has a Cohen coefficient ring
(`supportDim_add_supportDim_le_of_isCohenRing`), by the Cohen structure theorem (Stacks 032A). -/
@[stacks 0B0X "Serre's inequality r + s ≤ dim A"]
theorem supportDim_add_supportDim_le {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Nontrivial N]
    (hMN : Module.support A (M ⊗[A] N) ⊆ {closedPoint A}) :
    Module.supportDim A M + Module.supportDim A N ≤ ringKrullDim A := by
  have hfg : (maximalIdeal A).FG := Ideal.fg_of_isNoetherianRing _
  have : IsAdicComplete (maximalIdeal (Completion A)) (Completion A) :=
    AdicCompletion.isAdicComplete_of_fg hfg
  have hm : Ideal.map (algebraMap A (Completion A)) (maximalIdeal A) =
      maximalIdeal (Completion A) := (AdicCompletion.maximalIdeal_eq_map).symm
  have := nontrivial_baseChange hm M
  have := nontrivial_baseChange hm N
  have hsupp := support_subset_closedPoint_tensor hm M N hMN
  have hM : Module.supportDim (Completion A) (Completion A ⊗[A] M) = Module.supportDim A M :=
    supportDim_baseChange hm M
  have hN : Module.supportDim (Completion A) (Completion A ⊗[A] N) = Module.supportDim A N :=
    supportDim_baseChange hm N
  have hR : ringKrullDim (Completion A) = ringKrullDim A :=
    (ringKrullDim_adicCompletion_maximalIdeal (A := A)).symm
  rw [← hM, ← hN, ← hR]
  obtain ⟨Λ, _, _, _, hcase, -, hmax, f, hfm, hfs⟩ :=
    Stacks.CompleteLocalRing.CohenStructure.hasCoefficientRingHom (Completion A)
  rcases hcase with hfield | hcohen
  · let : Field Λ := hfield.toField
    let : Algebra Λ (Completion A) := f.toAlgebra
    exact supportDim_add_supportDim_le_of_field Λ _ _ hsupp
  · have : IsCohenRing Λ := hcohen
    exact supportDim_add_supportDim_le_of_isCohenRing hmax f hfm hfs _ _ hsupp

end General

end Stacks.SerreIntersection
