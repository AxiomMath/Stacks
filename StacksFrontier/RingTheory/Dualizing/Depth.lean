module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.Dimension
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Depth.ShortExact
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Depth and dimension for Cohen--Macaulay modules (Stacks chapter Dualizing Complexes)

Let `R` be a Noetherian local ring and `M` a finite `R`-module which is Cohen--Macaulay, i.e.
whose depth along the maximal ideal equals the dimension of its support. Then for any proper
ideal `I ⊆ R` the `I`-depth of `M` measures exactly how far quotienting by `I` cuts down the
support of `M`: one has `dim Supp(M / IM) + depth_I(M) = dim Supp(M)`, the additive form of
the source's difference formula (`Module.supportDim` takes values in `WithBot ℕ∞`).

The second result transports this along a flat local homomorphism `R → S` of Noetherian local
rings whose closed fibre `S/𝔪_R S` is Cohen--Macaulay: the `I`-depth of `S` is then at least
the drop in dimension that `I` induces on the closed fibre. The improper case `I = ⊤` must be
recorded separately, since there `depth_I(S) = ⊤` while the Krull dimension of the zero
quotient is `⊥` in `WithBot ℕ∞`.

## Main results

* `Dualizing.supportDim_quotient_add_depth_eq_supportDim` — for a finite Cohen--Macaulay
  module over a Noetherian local ring, the depth along a proper ideal is the drop in the
  dimension of its support on passing to the quotient by that ideal.
* `Dualizing.ringKrullDim_fiber_le_depth_add_ringKrullDim_quotient_of_flat` — the
  depth--dimension inequality for a flat local homomorphism with Cohen--Macaulay closed fibre.

## Implementation notes

The quotient `M / IM` is written `M ⧸ I • (⊤ : Submodule R M)`. The closed fibre of
`R → S` is written as the quotient of `S` by the extension of the maximal ideal of `R`, and
its Cohen--Macaulayness is expressed by `Module.IsCohenMacaulayAtMaximalIdeal` for the fibre
regarded as an `S`-module, which is equivalent to the local-ring condition because regular
sequences over the quotient correspond to regular sequences over `S`.

The three bounds of Tag 0BUV and the two parts of Tag 0BUW are already available in the
library, in forms more general than the source's (they need Noetherianity of the ring and
finiteness of only the middle module); they are recorded by the `add_to_stacks` commands at
the end of the file rather than restated here.

## References

* [Stacks Project, Tag 0BUV](https://stacks.math.columbia.edu/tag/0BUV)
* [Stacks Project, Tag 0BUW](https://stacks.math.columbia.edu/tag/0BUW)
* [Stacks Project, Tag 0BUX](https://stacks.math.columbia.edu/tag/0BUX)
* [Stacks Project, Tag 0BUY](https://stacks.math.columbia.edu/tag/0BUY)
-/

@[expose] public section

namespace Dualizing

section SupportDim

/-- The coheight of a prime in the support of `M` is at most the dimension of that support. -/
theorem coheight_le_supportDim_of_mem_support {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {p : PrimeSpectrum R} (hp : p ∈ Module.support R M) :
    (Order.coheight p : WithBot ℕ∞) ≤ Module.supportDim R M := by
  rw [Module.supportDim, Order.coheight_eq_krullDim_Ici]
  exact Order.krullDim_le_of_strictMono
    (fun q => (⟨q.1, Module.mem_support_mono q.2 hp⟩ : Module.support R M))
    (fun _ _ h => h)

private theorem supportDim_ideal_quotient_quotient_eq {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (I : Ideal R) {x : R} (hx : x ∈ I) :
    Module.supportDim R ((QuotSMulTop x M) ⧸ I • (⊤ : Submodule R (QuotSMulTop x M))) =
      Module.supportDim R (M ⧸ I • (⊤ : Submodule R M)) := by
  have hsupp :
      Module.support R ((QuotSMulTop x M) ⧸ I •
        (⊤ : Submodule R (QuotSMulTop x M))) =
        Module.support R (M ⧸ I • (⊤ : Submodule R M)) := by
    rw [Module.support_quotient, Module.support_quotSMulTop, Module.support_quotient]
    ext p
    simp only [Set.mem_inter_iff, PrimeSpectrum.mem_zeroLocus]
    constructor
    · rintro ⟨⟨hp, _⟩, hI⟩
      exact ⟨hp, hI⟩
    · rintro ⟨hp, hI⟩
      refine ⟨⟨hp, ?_⟩, hI⟩
      exact Set.singleton_subset_iff.mpr (hI hx)
  show Order.krullDim (Module.support R ((QuotSMulTop x M) ⧸ I • ⊤)) =
    Order.krullDim (Module.support R (M ⧸ I • ⊤))
  rw [hsupp]

private theorem depth_formula_of_eq_nat {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : I ≠ ⊤)
    (hCM : (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) =
      Module.supportDim R M) :
    ∀ n : ℕ, Module.depth R I M = (n : ℕ∞) →
      Module.supportDim R (M ⧸ I • (⊤ : Submodule R M)) +
          (n : WithBot ℕ∞) = Module.supportDim R M := by
  intro n
  induction n generalizing M with
  | zero =>
      intro hdepth
      have hnot : ¬ ∀ p ∈ associatedPrimes R M, ¬ I ≤ p := by
        intro hall
        obtain ⟨x, hx, hxreg⟩ :=
          (Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le I M
            (associatedPrimes.finite R M)).2 hall
        have hdrop :=
          (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append I M).1
            x hx hxreg
        rw [hdepth] at hdrop
        simp at hdrop
      push Not at hnot
      obtain ⟨p, hp, hIp⟩ := hnot
      let q : PrimeSpectrum R := ⟨p, hp.isPrime⟩
      have hqass : q.asIdeal ∈ associatedPrimes R M := by
        simpa [q] using hp
      have hbus :=
        Module.ringKrullDim_quotient_eq_supportDim_and_minimal_support_of_mem_associatedPrimes
          hCM hqass
      have hqM : q ∈ Module.support R M := hbus.2.1
      have hqQ : q ∈ Module.support R (M ⧸ I • (⊤ : Submodule R M)) := by
        rw [Module.support_quotient]
        exact ⟨hqM, hIp⟩
      have hlow : Module.supportDim R M ≤
          Module.supportDim R (M ⧸ I • (⊤ : Submodule R M)) :=
        (hbus.1.symm.trans (coheight_eq_ringKrullDim_quotient q).symm).trans_le
          (coheight_le_supportDim_of_mem_support hqQ)
      have hup : Module.supportDim R (M ⧸ I • (⊤ : Submodule R M)) ≤
          Module.supportDim R M :=
        Module.supportDim_le_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
      simp [le_antisymm hup hlow]
  | succ n ih =>
      intro hdepth
      have hIM : I • (⊤ : Submodule R M) ≠ ⊤ := by
        intro htop
        have hfin : (n + 1 : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top _
        exact hfin (by simpa [Module.depth, htop] using hdepth.symm)
      have : Nontrivial M := by
        by_contra h
        have := not_nontrivial_iff_subsingleton.mp h
        exact hIM (Submodule.eq_top_iff'.mpr fun m => by simp [Subsingleton.elim m 0])
      obtain ⟨rs, hmem, hreg, hlen⟩ :=
        (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append I M).2
          hIM [] (by simp) (RingTheory.Sequence.IsRegular.nil R M)
      cases rs with
      | nil =>
          have hne : ((n + 1 : ℕ) : ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
          exact (hne (by simpa [hdepth] using hlen.symm)).elim
      | cons x xs =>
          have hxI : x ∈ I := hmem x (by simp)
          have hxreg : IsSMulRegular M x :=
            (RingTheory.Sequence.isRegular_cons_iff M x xs).mp hreg |>.1
          have hxmax : x ∈ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI hxI
          have hdrop :=
            (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append I M).1
              x hxI hxreg
          have hdepth' : Module.depth R I (QuotSMulTop x M) = (n : ℕ∞) := by
            apply WithTop.add_right_cancel ENat.one_ne_top
            calc
              Module.depth R I (QuotSMulTop x M) + 1 = Module.depth R I M := hdrop
              _ = ((n + 1 : ℕ) : ℕ∞) := hdepth
              _ = (n : ℕ∞) + 1 := by simp
          have hCM' :=
            (Module.depth_eq_supportDim_iff_quotSMulTop hxmax hxreg).mp hCM
          have ih' := ih (M := QuotSMulTop x M) hCM' hdepth'
          have hdim := Module.supportDim_quotSMulTop_succ_eq_supportDim hxreg hxmax
          have hquot := supportDim_ideal_quotient_quotient_eq (M := M) I hxI
          calc
            Module.supportDim R (M ⧸ I • (⊤ : Submodule R M)) +
                (↑(n + 1) : WithBot ℕ∞) =
              (Module.supportDim R
                ((QuotSMulTop x M) ⧸ I •
                  (⊤ : Submodule R (QuotSMulTop x M))) +
                (n : WithBot ℕ∞)) + 1 := by
                  rw [hquot]
                  norm_num [Nat.cast_add, add_assoc]
            _ = Module.supportDim R (QuotSMulTop x M) + 1 := by rw [ih']
            _ = Module.supportDim R M := hdim

/-- **Stacks Project, Tag 0BUX.** The depth of a finite Cohen--Macaulay module
along a proper ideal is the drop in the dimension of its support on passing to
the quotient by that ideal. -/
@[stacks 0BUX, ega "0 16.5.9" "r = depth_p(M)"]
theorem supportDim_quotient_add_depth_eq_supportDim
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : I ≠ ⊤) (hM : Module.IsCohenMacaulayAtMaximalIdeal R M) :
    Module.supportDim R (M ⧸ I • (⊤ : Submodule R M)) +
        (Module.depth R I M : WithBot ℕ∞) =
      Module.supportDim R M := by
  by_cases hsub : Subsingleton M
  · let : Subsingleton M := hsub
    simp [Module.supportDim_eq_bot_of_subsingleton]
  · let : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub
    have hIM : I • (⊤ : Submodule R M) ≠ ⊤ := by
      intro htop
      have hbot : (⊤ : Submodule R M) = ⊥ :=
        Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤ Module.Finite.fg_top
          (by rw [htop]) (by
            rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
            exact IsLocalRing.le_maximalIdeal hI)
      obtain ⟨m, hm⟩ := exists_ne (0 : M)
      exact hm ((Submodule.eq_bot_iff _).mp hbot m Submodule.mem_top)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Module.depth_lt_top R I M hIM).ne
    rw [← hn]
    exact depth_formula_of_eq_nat I hI hM n hn.symm

end SupportDim

section FlatFibre

open IsLocalRing

universe u v

open RingTheory.Sequence

/-- Quotienting `S ⧸ J` by `I` times the top submodule is linearly equivalent to `S ⧸ (J ⊔ I)`. -/
private lemma nonempty_quotient_equiv_quotient_sup {S : Type*} [CommRing S] (J I : Ideal S) :
    Nonempty (((S ⧸ J) ⧸ I • (⊤ : Submodule S (S ⧸ J))) ≃ₗ[S]
      (S ⧸ (J ⊔ I))) := by
  have hmap : I • (⊤ : Submodule S (S ⧸ J)) =
      (I • (⊤ : Submodule S S)).map J.mkQ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  exact ⟨(Submodule.quotEquivOfEq _ _ hmap).trans
    ((Submodule.quotientQuotientEquivQuotientSup J (I • (⊤ : Submodule S S))).trans
      (Submodule.quotEquivOfEq _ _ (by simp)))⟩

private lemma supportDim_fiber_quotient_eq_ringKrullDim
    {S : Type*} [CommRing S]
    (J I : Ideal S) :
    Module.supportDim S
        ((S ⧸ J) ⧸ I • (⊤ : Submodule S (S ⧸ J))) =
      ringKrullDim (S ⧸ (J ⊔ I)) := by
  obtain ⟨e⟩ := nonempty_quotient_equiv_quotient_sup J I
  rw [← Module.supportDim_quotient_eq_ringKrullDim]
  exact Module.supportDim_eq_of_equiv e

private lemma depth_fiber_le_depth_of_flat
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [Module.Flat R S] [IsLocalHom (algebraMap R S)] (I : Ideal S)
    (hI : I ≠ ⊤) :
    Module.depth S I (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) ≤
      Module.depth S I S := by
  let J := Ideal.map (algebraMap R S) (maximalIdeal R)
  have hJ : J ≤ maximalIdeal S := map_maximalIdeal_le (algebraMap R S)
  have hImax : I ≤ maximalIdeal S := le_maximalIdeal hI
  have hsum : J ⊔ I ≠ ⊤ := by
    intro h
    exact (maximalIdeal.isMaximal S).ne_top
      (le_antisymm le_top (h ▸ sup_le hJ hImax))
  have hfiber : Nontrivial ((S ⧸ J) ⧸ I • (⊤ : Submodule S (S ⧸ J))) := by
    obtain ⟨e⟩ := nonempty_quotient_equiv_quotient_sup J I
    exact e.toEquiv.nontrivial_congr.mpr (Ideal.Quotient.nontrivial_iff.mpr hsum)
  have hFsmul : I • (⊤ : Submodule S (S ⧸ J)) ≠ ⊤ :=
    (Submodule.Quotient.nontrivial_iff).mp hfiber
  have hSsmul : I • (⊤ : Submodule S S) ≠ ⊤ := by simpa using hI
  have hRnoeth : IsNoetherianRing R := by
    have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat (A := S)
      (isNoetherian_of_linearEquiv (TensorProduct.AlgebraTensorModule.rid R S S).symm)
  simp only [Module.depth, ite_eq_right hFsmul, ite_eq_right hSsmul]
  refine iSup₂_le fun rs hrs =>
    le_iSup₂_of_le rs ⟨hrs.1, ?_⟩ le_rfl
  let := hRnoeth
  have hreg : IsRegular (S ⧸ J) (rs.map (Ideal.Quotient.mk J)) :=
    (AddEquiv.refl (S ⧸ J)).isRegular_congr
      (List.forall₂_map_right_iff.mpr <|
        List.forall₂_same.mpr fun r _ x => by
          simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]) |>.mp hrs.2
  exact (Module.Flat.isRegular_and_flat_quotient_ofList_take_of_isRegular_maximalIdeal
    (R := R) (S := S) hreg).1

/-- Let `R → S` be a flat local homomorphism with Noetherian local target. If its closed
fibre is Cohen--Macaulay, then the depth of `S` along an ideal `I` is at least the difference
between the dimension of the closed fibre and that of its quotient by `I`. -/
@[stacks 0BUY]
theorem ringKrullDim_fiber_le_depth_add_ringKrullDim_quotient_of_flat
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [Module.Flat R S] [IsLocalHom (algebraMap R S)] (I : Ideal S)
    (hCM : Module.IsCohenMacaulayAtMaximalIdeal S
      (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))) :
    I = ⊤ ∨
      ringKrullDim (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) ≤
        (Module.depth S I S : WithBot ℕ∞) +
        ringKrullDim
            (S ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) ⊔ I)) := by
  by_cases hI : I = ⊤
  · exact Or.inl hI
  · right
    let J := Ideal.map (algebraMap R S) (maximalIdeal R)
    have hdepth := depth_fiber_le_depth_of_flat R S I hI
    have hcm := supportDim_quotient_add_depth_eq_supportDim I hI hCM
    rw [supportDim_fiber_quotient_eq_ringKrullDim J I,
      Module.supportDim_quotient_eq_ringKrullDim J] at hcm
    have hle : (Module.depth S I (S ⧸ J) : WithBot ℕ∞) ≤
        (Module.depth S I S : WithBot ℕ∞) := WithBot.coe_le_coe.mpr hdepth
    rw [← hcm]
    simpa only [add_comm] using add_le_add_right hle (ringKrullDim (S ⧸ (J ⊔ I)))

end FlatFibre

end Dualizing

-- Tag 0BUV: the three depth bounds attached to a short exact sequence are the three
-- conjuncts of the library's `Module.min_depth_le_depth_of_exact`, which assumes only
-- finiteness of the middle module.
add_to_stacks 0BUV "middle_depth_bound, quotient_depth_bound and submodule_depth_bound: the \
  three conjuncts of this inequality" Module.min_depth_le_depth_of_exact

-- Tag 0BUW: part (1) is the depth computation `depth_I(M/xM) + 1 = depth_I(M)` and part (2)
-- is the extension of a regular sequence to one of length the depth.
add_to_stacks 0BUW Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
