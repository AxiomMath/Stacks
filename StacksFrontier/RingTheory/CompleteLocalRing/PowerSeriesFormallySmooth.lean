module

public import Mathlib
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.FieldTheory.Separable.PerfectField
public import StacksFrontier.RingTheory.CohenRing
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.Flat.RegularSequence
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings
public import StacksFrontier.RingTheory.MvPowerSeries.HomExt
public import StacksFrontier.RingTheory.MvPowerSeries.RegularLocal
public import StacksFrontier.RingTheory.Noetherian.ULift
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous
import StacksFrontier.RingTheory.LocalRing.AdicCompleteRingEquiv
import StacksFrontier.Topology.Algebra.AdicTopology.QuotientAdic

@[expose] public section

/-!
# Formal smoothness of power series rings over complete local rings

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

07NL, 07NN, 09Q8.

## Tag 07NL — Formal smoothness of power series rings over fields and Cohen rings

Power series rings over a characteristic-zero field, over a field of positive
characteristic, and over a Cohen ring are formally smooth over their respective
prime rings for the maximal-ideal-adic topology.

### Main definitions

No new definitions are introduced.

### Main results

* `isFormallySmooth_mvPowerSeries`: formal smoothness of the three
  power series rings over their prime rings.

### Implementation notes

The formal power series ring in `n` variables is represented by
`MvPowerSeries (Fin n)`. The prime rings carry their discrete topologies,
expressed as the adic topologies of their zero ideals, while each power series
ring carries the adic topology of its maximal ideal.

### References

* [Stacks Project, Tag 07NL](https://stacks.math.columbia.edu/tag/07NL)

## Tag 07NN — Power series presentations compatible with a local homomorphism

A local homomorphism of Noetherian complete local rings is covered by a commutative square of
surjections whose left-hand map is a flat map between power series rings with regular closed
fibre. In residue characteristic zero the coefficient rings are fields, and in positive residue
characteristic they are Cohen rings. The left-hand map carries a regular system of parameters to
part of a regular system of parameters.

### Main definitions

No new definitions are introduced.

### Main results

* `exists_powerSeries_presentation_of_isLocalHom`: a compatible power series
  presentation of a local homomorphism of Noetherian complete local rings.

### Implementation notes

Power series rings are represented by `MvPowerSeries (Fin n)`. A regular system of parameters is
a minimal list of generators of the maximal ideal. Saying that its image is part of a regular
system upstairs means that the mapped list can be extended to such a minimal generating list.
The closed fibre of `g : R →+* S` is the quotient by the extension of the maximal ideal of `R`.
In positive residue characteristic, the chosen parameter system of `R` starts with the
residue characteristic `p`, which is the uniformizer in both Cohen coefficient rings.

### References

* [Stacks Project, Tag 07NN](https://stacks.math.columbia.edu/tag/07NN)

## Tag 09Q8 — Pullbacks of complete Noetherian local rings

The pullback of two surjections onto a common complete Noetherian local ring is again a
complete Noetherian local ring.

### Main definitions

No new definitions are introduced.

### Main results

* `isNoetherianCompleteLocalRing_pullback`: a pullback of surjective maps of complete
  Noetherian local rings is complete Noetherian local.

### Implementation notes

The fibre product is Mathlib's `RingHom.pullback`. Completeness means adic completeness for the
maximal ideal. The local-ring structure on the pullback is existentially bound so that its
maximal ideal can occur in the completeness assertion.

### References

* [Stacks Project, Tag 09Q8](https://stacks.math.columbia.edu/tag/09Q8)

-/

/-! ### Stacks Tag 07NL -/

section

section

@[expose] public section

open scoped Topology
open Filter IsLocalRing Set
open Stacks.CompleteLocalRing.RegularSubring

open Stacks.FormallySmooth.TopologicalRings

private theorem formallySmooth_field_charZero (K : Type*) [Field K] [CharZero K] :
    Algebra.FormallySmooth ℚ K := by
  have h := Algebra.isSeparableExtension_of_charZero_and_tfae ℚ K
  exact (h.2.out 1 6).mp (h.1 (inferInstance : CharZero ℚ))


private def zmodLiftInt {S : Type*} [CommRing S] (n : ℕ)
    (f : ℤ →+* S) (hn : f (n : ℤ) = 0) : ZMod n →+* S :=
  (Ideal.Quotient.lift (Ideal.span {(n : ℤ)}) f
    ((Ideal.span_singleton_le_iff_mem _).2 (RingHom.mem_ker.mpr hn))).comp
      (Int.quotientSpanNatEquivZMod n).symm

private theorem zmodLiftInt_comp_intCast {S : Type*} [CommRing S] (n : ℕ)
    (f : ℤ →+* S) (hn : f (n : ℤ) = 0) :
    (zmodLiftInt n f hn).comp (Int.castRingHom (ZMod n)) = f := by
  apply RingHom.ext_int

private theorem continuous_C_mvPowerSeries {R : Type*} [CommRing R] [IsLocalRing R]
    (n : ℕ) :
    @Continuous R (MvPowerSeries (Fin n) R)
      (IsLocalRing.maximalIdeal R).adicTopology
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R)).adicTopology
      (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R) := by
  let m := IsLocalRing.maximalIdeal R
  let M := IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R)
  apply (RingHom.continuous_adic_iff
    (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R) m M).2
  refine ⟨1, by omega, ?_⟩
  intro x hx
  have hx' : x ∈ m := by simpa using hx
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_C]
  exact (IsLocalRing.mem_maximalIdeal x).mp hx'

private theorem mvPowerSeries_maximalIdeal_pow_of_finite_coefficients
    {R : Type*} [CommRing R] [IsLocalRing R] (n : ℕ) :
    ∀ N : ℕ, ∃ E : Finset (Fin n →₀ ℕ),
      ∀ f : MvPowerSeries (Fin n) R,
        (∀ e ∈ E, MvPowerSeries.coeff e f ∈ IsLocalRing.maximalIdeal R ^ N) →
          f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R) ^ N := by
  induction n with
  | zero =>
    intro N
    refine ⟨{0}, fun f hf ↦ ?_⟩
    let e : MvPowerSeries (Fin 0) R ≃+* R :=
      (MvPowerSeries.isEmptyEquiv (Fin 0) R).toRingEquiv
    have hemax : Ideal.map e (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 0) R)) =
        IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)
    have hepow : Ideal.map e
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 0) R) ^ N) =
          IsLocalRing.maximalIdeal R ^ N := by rw [Ideal.map_pow, hemax]
    have hcoeff : MvPowerSeries.coeff (0 : Fin 0 →₀ ℕ) f ∈
        IsLocalRing.maximalIdeal R ^ N := hf 0 (by simp)
    have heval : e f = MvPowerSeries.coeff (0 : Fin 0 →₀ ℕ) f := by
      simp [e, MvPowerSeries.coeff_zero_eq_constantCoeff]
    have hfmap : e f ∈ Ideal.map e
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 0) R) ^ N) := by
      rw [hepow]
      simpa [heval] using hcoeff
    obtain ⟨g, hg, hgf⟩ :=
      (Ideal.mem_map_iff_of_surjective e e.surjective).1 hfmap
    have : g = f := e.injective hgf
    simpa [this] using hg
  | succ n ih =>
    intro N
    obtain ⟨E, hE⟩ := ih N
    classical
    let e : MvPowerSeries (Fin (n + 1)) R ≃+* PowerSeries (MvPowerSeries (Fin n) R) :=
      (MvPowerSeries.finSuccEquiv R n).toRingEquiv
    let E' : Finset (Fin (n + 1) →₀ ℕ) :=
      ((Finset.range N).product E).image (fun x => Finsupp.cons x.1 x.2)
    refine ⟨E', ?_⟩
    intro f hf
    let m₀ := IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R)
    let m₁ := IsLocalRing.maximalIdeal (PowerSeries (MvPowerSeries (Fin n) R))
    have hcoeff (j : ℕ) (hj : j < N) : PowerSeries.coeff j (e f) ∈ m₀ ^ N := by
      apply hE (PowerSeries.coeff j (e f))
      intro d hd
      have hmem : Finsupp.cons j d ∈ E' := by
        apply Finset.mem_image.mpr
        refine ⟨(j, d), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, hd⟩, rfl⟩
      have h := hf (Finsupp.cons j d) hmem
      have hc := MvPowerSeries.coeff_coeff_finSuccEquiv (R := R) (n := n) f
        (k := j) (x := d)
      simpa [e] using hc ▸ h
    have hsum : e f ∈ (m₀ ^ N).map (PowerSeries.C : _ →+* _) ⊔
        Ideal.span {(PowerSeries.X : PowerSeries (MvPowerSeries (Fin n) R)) ^ N} :=
      (mem_map_C_sup_span_X_pow_iff (m₀ ^ N) N (e f)).2 hcoeff
    have hle := le_pow_maximalIdeal_powerSeries (MvPowerSeries (Fin n) R) N
    have hmap : Ideal.map e (IsLocalRing.maximalIdeal (MvPowerSeries (Fin (n + 1)) R)) = m₁ :=
      IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)
    have hmapPow : Ideal.map e
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin (n + 1)) R) ^ N) = m₁ ^ N := by
      rw [Ideal.map_pow, hmap]
    have hmem : e f ∈ Ideal.map e
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin (n + 1)) R) ^ N) := by
      rw [hmapPow]
      exact hle hsum
    obtain ⟨g, hg, hgf⟩ :=
      (Ideal.mem_map_iff_of_surjective e e.surjective).1 hmem
    have : g = f := e.injective hgf
    simpa [this] using hg

private theorem mvPowerSeries_maximalIdeal_pow_isOpen_pi
    {R : Type*} [CommRing R] [IsLocalRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (hR : ‹TopologicalSpace R› =
      (IsLocalRing.maximalIdeal R).adicTopology) (n N : ℕ) :
    @IsOpen (MvPowerSeries (Fin n) R)
      (MvPowerSeries.WithPiTopology.instTopologicalSpace R)
      (((IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R) ^ N :
        Ideal (MvPowerSeries (Fin n) R)) : Set (MvPowerSeries (Fin n) R))) := by
  let : TopologicalSpace (MvPowerSeries (Fin n) R) :=
    MvPowerSeries.WithPiTopology.instTopologicalSpace R
  obtain ⟨E, hE⟩ := mvPowerSeries_maximalIdeal_pow_of_finite_coefficients (R := R) n N
  have hcoeffOpen : IsOpen ((IsLocalRing.maximalIdeal R ^ N : Ideal R) : Set R) := by
    have hAdic : @IsOpen R (IsLocalRing.maximalIdeal R).adicTopology
        ((IsLocalRing.maximalIdeal R ^ N : Ideal R) : Set R) := by
      let : TopologicalSpace R := (IsLocalRing.maximalIdeal R).adicTopology
      exact (IsLocalRing.maximalIdeal R).openAddSubgroup N |>.isOpen'
    exact hR.symm ▸ hAdic
  let U : Set (MvPowerSeries (Fin n) R) :=
    ⋂ e ∈ E, (MvPowerSeries.coeff e) ⁻¹' ((IsLocalRing.maximalIdeal R ^ N : Ideal R) : Set R)
  have hU : IsOpen U := isOpen_biInter_finset fun e _ =>
    hcoeffOpen.preimage (MvPowerSeries.WithPiTopology.continuous_coeff R e)
  have hU0 : U ∈ 𝓝 (0 : MvPowerSeries (Fin n) R) := hU.mem_nhds (by simp [U])
  have hUsub : U ⊆
      ((IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R) ^ N : Ideal _) : Set _) :=
    fun f hf => hE f fun e he => by
      simp only [U, Set.mem_iInter] at hf
      exact hf e he
  let : IsTopologicalRing (MvPowerSeries (Fin n) R) :=
    MvPowerSeries.WithPiTopology.instIsTopologicalRing (Fin n) R
  apply isOpen_iff_mem_nhds.2
  intro f hf
  have htrans : (fun x : MvPowerSeries (Fin n) R => f + x) '' U ∈ 𝓝 f := by
    rw [← map_add_left_nhds_zero f]
    exact Filter.mem_map.mpr (Filter.mem_of_superset hU0 fun x hx => ⟨x, hx, rfl⟩)
  refine Filter.mem_of_superset htrans ?_
  rintro g ⟨x, hx, rfl⟩
  exact Ideal.add_mem _ hf (hUsub hx)

private theorem mvPowerSeries_pi_to_adic_continuous
    {R : Type*} [CommRing R] [IsLocalRing R] [TopologicalSpace R]
    [IsTopologicalRing R]
    (hR : ‹TopologicalSpace R› = (IsLocalRing.maximalIdeal R).adicTopology)
    (n : ℕ) :
    @Continuous (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R)
      (MvPowerSeries.WithPiTopology.instTopologicalSpace R)
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R)).adicTopology id := by
  let : TopologicalSpace (MvPowerSeries (Fin n) R) :=
    MvPowerSeries.WithPiTopology.instTopologicalSpace R
  let : IsTopologicalRing (MvPowerSeries (Fin n) R) :=
    MvPowerSeries.WithPiTopology.instIsTopologicalRing (Fin n) R
  apply continuous_iff_le_induced.2
  rw [@induced_id _ (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R)).adicTopology]
  apply TopologicalSpace.le_def.2
  intro s hs
  apply isOpen_iff_mem_nhds.2
  intro f hf
  have hmemAdic : s ∈ @nhds _
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R)).adicTopology f := by
    let : TopologicalSpace (MvPowerSeries (Fin n) R) :=
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R)).adicTopology
    exact hs.mem_nhds hf
  obtain ⟨N, -, hN⟩ :=
    (Ideal.hasBasis_nhds_adic (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R)) f).mem_iff.mp
      hmemAdic
  let V : Set (MvPowerSeries (Fin n) R) :=
    (fun y => y - f) ⁻¹' ((IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R) ^ N :
      Ideal (MvPowerSeries (Fin n) R)) : Set (MvPowerSeries (Fin n) R))
  have hVmem : V ∈ 𝓝 f := ((mvPowerSeries_maximalIdeal_pow_isOpen_pi hR n N).preimage
    (continuous_id.sub continuous_const)).mem_nhds (by simp)
  exact Filter.mem_of_superset hVmem fun y hy => hN ⟨y - f, hy, by simp⟩

private theorem prime_and_maximalIdeal_eq_span_of_residueChar {p : ℕ} {Λ : Type*}
    [CommRing Λ] [IsDomain Λ] [IsCohenRing Λ] [CharP (ResidueField Λ) p] :
    p.Prime ∧ IsLocalRing.maximalIdeal Λ = Ideal.span {(p : Λ)} := by
  obtain ⟨q, hq, hqm⟩ := IsCohenRing.exists_prime_maximalIdeal_eq_span (R := Λ)
  have hdvd : p ∣ q := (CharP.cast_eq_zero_iff (ResidueField Λ) p q).mp <| by
    rw [← map_natCast (residue Λ) q, residue_eq_zero_iff, hqm]
    exact Ideal.mem_span_singleton_self _
  obtain rfl := (hq.eq_one_or_self_of_dvd p hdvd).resolve_left
    (CharP.char_ne_one (ResidueField Λ) p)
  exact ⟨hq, hqm⟩

private theorem formallySmoothTop_int_of_cohenRing.{u, w} (p : ℕ) (Λ : Type w)
    [CommRing Λ] [IsDomain Λ] [IsCohenRing Λ] [CharP (ResidueField Λ) p]
    [TopologicalSpace Λ] [IsTopologicalRing Λ]
    (htΛ : ‹TopologicalSpace Λ› = (IsLocalRing.maximalIdeal Λ).adicTopology)
    : @RingHom.FormallySmoothTop.{u, 0, w} ℤ Λ inferInstance
        (⊥ : Ideal ℤ).adicTopology (⊥ : Ideal ℤ).ringFilterBasis.isTopologicalRing
        inferInstance inferInstance inferInstance (Int.castRingHom Λ) := by
  intro A _ _ _ J hJ f hf gbar hgbar hcomm
  let : DiscreteTopology (A ⧸ J) := discreteTopology_iff_isOpen_singleton.mpr fun x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa using (QuotientRing.isOpenMap_coe J) ({a} : Set A) (isOpen_discrete ({a} : Set A))
  let m := IsLocalRing.maximalIdeal Λ
  obtain ⟨hp, hm⟩ := prime_and_maximalIdeal_eq_span_of_residueChar (p := p) (Λ := Λ)
  have hopen : gbar ⁻¹' {0} ∈ 𝓝 (0 : Λ) := by
    apply hgbar.continuousAt
    simp
  obtain ⟨N, -, hN⟩ := (Ideal.hasBasis_nhds_zero_adic m).mem_iff.mp (htΛ ▸ hopen)
  have hp_mem : (p : Λ) ∈ m := by
    change (p : Λ) ∈ IsLocalRing.maximalIdeal Λ
    rw [hm]
    exact Ideal.mem_span_singleton_self _
  have hNzero : gbar ((p : Λ) ^ N) = 0 := by simpa using hN (Ideal.pow_mem_pow hp_mem N)
  have hmem : f ((p : ℤ) ^ N) ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hcommN' : gbar ((p : Λ) ^ N) = Ideal.Quotient.mk J (f ((p : ℤ) ^ N)) := by
      simp
    rw [← hcommN']
    exact hNzero
  let e := 2 * N
  have hkill : f ((p : ℤ) ^ e) = 0 := by
    rw [show e = N * 2 by simp [e, Nat.mul_comm], map_pow, pow_mul]
    have hsquare : f ((p : ℤ) ^ N) ^ 2 ∈ J ^ 2 := by
      simpa [pow_two] using Ideal.mul_mem_mul hmem hmem
    simpa [hJ] using hsquare
  let q := p ^ e
  have hkillNat : f (q : ℤ) = 0 := by
    simpa [q, Nat.cast_pow] using hkill
  let IΛ : Ideal Λ := Ideal.span {(p : Λ) ^ e}
  let Λq := Λ ⧸ IΛ
  let rho : ZMod q →+* Λq := zmodLiftInt q (Int.castRingHom Λq) (by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change ((q : ℤ) : Λ) ∈ IΛ
    simpa only [q, Int.cast_natCast, Nat.cast_pow, Int.cast_pow, IΛ] using
      (Ideal.mem_span_singleton_self ((p : Λ) ^ e)))
  let fQ : ZMod q →+* A := zmodLiftInt q f hkillNat
  have hkern : IΛ ≤ RingHom.ker gbar := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    have hp2N : (p : Λ) ^ e ∈ m ^ e := Ideal.pow_mem_pow hp_mem e
    have hle : m ^ e ≤ m ^ N := Ideal.pow_le_pow_right (by omega)
    have := hN (hle hp2N)
    simpa using this
  let gbarQ : Λq →+* A ⧸ J := Ideal.Quotient.lift IΛ gbar hkern
  have hcompat : gbarQ.comp rho = (Ideal.Quotient.mk J).comp fQ :=
    RingHom.ext_zmod _ _
  let : Algebra (ZMod q) Λq := rho.toAlgebra
  let : Algebra (ZMod q) A := fQ.toAlgebra
  let : Algebra (ZMod q) (A ⧸ J) := ((Ideal.Quotient.mk J).comp fQ).toAlgebra
  have : Algebra.FormallySmooth (ZMod q) Λq :=
    IsCohenRing.formallySmooth_quotient_span_pow p e Λ
  let gbarAlg : Λq →ₐ[ZMod q] A ⧸ J :=
    { gbarQ with commutes' := fun z => DFunLike.congr_fun hcompat z }
  obtain ⟨gAlg, hgAlg⟩ := Algebra.FormallySmooth.exists_lift J ⟨2, hJ⟩ gbarAlg
  let g : Λ →+* A := gAlg.toRingHom.comp (Ideal.Quotient.mk IΛ)
  have hcont : @Continuous Λ A (m.adicTopology) ‹TopologicalSpace A› g := by
    have hA : ‹TopologicalSpace A› = (⊥ : Ideal A).adicTopology :=
      (is_bot_adic_iff (A := A)).2 (inferInstance : DiscreteTopology A)
    rw [hA]
    apply (RingHom.continuous_adic_iff g m ⊥).2
    refine ⟨max e 1, le_max_right _ _, ?_⟩
    intro x hx
    have hx' : x ∈ m ^ e := (Ideal.pow_le_pow_right (le_max_left _ _)) hx
    have hxI : x ∈ IΛ := by
      have hpow : m ^ e = IΛ := by
        change (IsLocalRing.maximalIdeal Λ) ^ e = Ideal.span {(p : Λ) ^ e}
        rw [hm, Ideal.span_singleton_pow]
      rw [← hpow]
      exact hx'
    apply Ideal.mem_bot.mpr
    apply RingHom.mem_ker.mp
    simp [g, Ideal.Quotient.eq_zero_iff_mem.mpr hxI]
  have hred : (Ideal.Quotient.mk J).comp g = gbar := by
    calc
      (Ideal.Quotient.mk J).comp g =
          ((Ideal.Quotient.mk J).comp gAlg.toRingHom).comp (Ideal.Quotient.mk IΛ) := by
            simp [g, RingHom.comp_assoc]
      _ = gbarQ.comp (Ideal.Quotient.mk IΛ) := by
            rw [show (Ideal.Quotient.mk J).comp gAlg.toRingHom = gbarQ from
              congrArg AlgHom.toRingHom hgAlg]
      _ = gbar := Ideal.Quotient.lift_comp_mk IΛ gbar hkern
  refine ⟨g, ?_, ?_, hred⟩
  · rw [htΛ]
    exact hcont
  · exact RingHom.ext_int _ _

private theorem formallySmoothTop_mvPowerSeries.{u, v, w} {R₀ : Type v} {R : Type w}
    [CommRing R₀] [TopologicalSpace R₀] [IsTopologicalRing R₀]
    [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (n : ℕ)
    [TopologicalSpace (MvPowerSeries (Fin n) R)]
    [IsTopologicalRing (MvPowerSeries (Fin n) R)]
    (φ : R₀ →+* R) (hφ : RingHom.FormallySmoothTop.{u, v, w} φ)
    (htR : ‹TopologicalSpace R› =
      (maximalIdeal R).adicTopology)
    (ht : ‹TopologicalSpace (MvPowerSeries (Fin n) R)› =
      (maximalIdeal (MvPowerSeries (Fin n) R)).adicTopology)
    (hC : Continuous (MvPowerSeries.C : R → MvPowerSeries (Fin n) R)) :
    RingHom.FormallySmoothTop.{u, v, w}
      ((MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R).comp φ) := by
  let m := maximalIdeal (MvPowerSeries (Fin n) R)
  intro A _ _ _ J hJ f hf gbar hgbar hcomm
  let : DiscreteTopology (A ⧸ J) := discreteTopology_iff_isOpen_singleton.mpr fun x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa using
      (QuotientRing.isOpenMap_coe J) ({a} : Set A) (isOpen_discrete ({a} : Set A))
  have hgC : Continuous (gbar.comp (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R)) :=
    hgbar.comp hC
  obtain ⟨c, hc, hcφ, hqc⟩ :=
    hφ A J hJ f hf (gbar.comp MvPowerSeries.C) hgC (by rwa [RingHom.comp_assoc])
  choose a ha using fun i : Fin n ↦ Ideal.Quotient.mk_surjective (gbar (MvPowerSeries.X i))
  have hmX (i : Fin n) : MvPowerSeries.X i ∈ m := by
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hopen : gbar ⁻¹' {0} ∈ 𝓝 (0 : MvPowerSeries (Fin n) R) := by
    apply hgbar.continuousAt
    simp
  obtain ⟨N, -, hN⟩ := (Ideal.hasBasis_nhds_zero_adic m).mem_iff.mp (ht ▸ hopen)
  have ha_nil (i : Fin n) : IsNilpotent (a i) := by
    refine ⟨2 * N, ?_⟩
    have hx : gbar ((MvPowerSeries.X i) ^ N) = 0 := by
      simpa using hN (Ideal.pow_mem_pow (hmX i) N)
    have haj : a i ^ N ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [map_pow, ha i] using hx
    rw [mul_comm, pow_mul]
    exact (show (a i ^ N) ^ 2 ∈ (⊥ : Ideal A) by
      rw [← hJ]
      simpa [pow_two] using Ideal.mul_mem_mul haj haj)
  have ha_eval : MvPowerSeries.HasEval a := by
    refine ⟨fun i ↦ (ha_nil i).isTopologicallyNilpotent, ?_⟩
    rw [Filter.cofinite_eq_bot]
    exact tendsto_bot
  have hbarPi : @Continuous (MvPowerSeries (Fin n) R) (A ⧸ J)
      (MvPowerSeries.WithPiTopology.instTopologicalSpace R)
      (topologicalRingQuotientTopology J) gbar := by
    have hbarAdic : @Continuous (MvPowerSeries (Fin n) R) (A ⧸ J)
        (maximalIdeal (MvPowerSeries (Fin n) R)).adicTopology
        (topologicalRingQuotientTopology J) gbar := by
      rw [← ht]
      exact hgbar
    exact @Continuous.comp
      (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R) (A ⧸ J)
      (MvPowerSeries.WithPiTopology.instTopologicalSpace R)
      (maximalIdeal (MvPowerSeries (Fin n) R)).adicTopology
      (topologicalRingQuotientTopology J) id gbar hbarAdic
      (mvPowerSeries_pi_to_adic_continuous htR n)
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity A := by
    rw [discreteUniformity_iff_eq_principal_setRelId, uniformity_eq_comap_nhds_zero' A,
      nhds_discrete, comap_pure]
    congr 1
    ext x
    change x.2 + -x.1 = 0 ↔ x.1 = x.2
    rw [← sub_eq_add_neg, sub_eq_zero, eq_comm]
  have : CompleteSpace A := by infer_instance
  let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  have hc' : @Continuous R A (IsTopologicalAddGroup.rightUniformSpace R).toTopologicalSpace
      (IsTopologicalAddGroup.rightUniformSpace A).toTopologicalSpace c := hc
  have hqcont : Continuous (Ideal.Quotient.mk J : A →+* A ⧸ J) :=
    continuous_of_discreteTopology
  let cq : R →+* A ⧸ J := (Ideal.Quotient.mk J).comp c
  let aq : Fin n → A ⧸ J := fun i => Ideal.Quotient.mk J (a i)
  have hcq : @Continuous R (A ⧸ J)
      (IsTopologicalAddGroup.rightUniformSpace R).toTopologicalSpace
      (IsTopologicalAddGroup.rightUniformSpace (A ⧸ J)).toTopologicalSpace cq :=
    hqcont.comp hc
  have haq : MvPowerSeries.HasEval aq := ha_eval.map hqcont
  let : UniformSpace (A ⧸ J) := IsTopologicalAddGroup.rightUniformSpace (A ⧸ J)
  let : IsUniformAddGroup (A ⧸ J) := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity (A ⧸ J) := by
    rw [discreteUniformity_iff_eq_principal_setRelId,
      uniformity_eq_comap_nhds_zero' (A ⧸ J), nhds_discrete, comap_pure]
    congr 1
    ext x
    change x.2 + -x.1 = 0 ↔ x.1 = x.2
    rw [← sub_eq_add_neg, sub_eq_zero, eq_comm]
  have : CompleteSpace (A ⧸ J) := by infer_instance
  have : T2Space (A ⧸ J) := by infer_instance
  have hbarEq : gbar = MvPowerSeries.eval₂ cq aq := by
    apply MvPowerSeries.eval₂_unique hcq haq hbarPi
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
        rw [MvPolynomial.coe_C, MvPolynomial.eval₂_C]
        exact (DFunLike.congr_fun hqc r).symm
    | add p q hp hq =>
        change gbar ((p + q : MvPolynomial (Fin n) R) : MvPowerSeries (Fin n) R) =
          MvPolynomial.eval₂ cq aq (p + q)
        rw [MvPolynomial.coe_add, map_add, MvPolynomial.eval₂_add, hp, hq]
    | mul_X p i hp =>
        change gbar ((p * MvPolynomial.X i : MvPolynomial (Fin n) R) :
          MvPowerSeries (Fin n) R) = MvPolynomial.eval₂ cq aq (p * MvPolynomial.X i)
        rw [MvPolynomial.coe_mul, map_mul, MvPolynomial.eval₂_mul, hp, MvPolynomial.coe_X,
          MvPolynomial.eval₂_X, ← ha i]
  let g := MvPowerSeries.eval₂Hom hc' ha_eval
  have hred : (Ideal.Quotient.mk J).comp g = gbar := by
    ext x
    calc
      (Ideal.Quotient.mk J) (g x) = (Ideal.Quotient.mk J) (MvPowerSeries.eval₂ c a x) :=
        congrArg _ (congrFun (MvPowerSeries.coe_eval₂Hom hc' ha_eval) x)
      _ = MvPowerSeries.eval₂ cq aq x :=
        congrFun (MvPowerSeries.comp_eval₂ hc' ha_eval hqcont) x
      _ = gbar x := congrFun hbarEq x |>.symm
  have hcont : @Continuous (MvPowerSeries (Fin n) R) A
      (maximalIdeal (MvPowerSeries (Fin n) R)).adicTopology
      ‹TopologicalSpace A› g := by
    let : TopologicalSpace (MvPowerSeries (Fin n) R) :=
      (maximalIdeal (MvPowerSeries (Fin n) R)).adicTopology
    let : IsTopologicalRing (MvPowerSeries (Fin n) R) :=
      (maximalIdeal (MvPowerSeries (Fin n) R)).ringFilterBasis.isTopologicalRing
    let : DiscreteTopology (A ⧸ J) :=
      discreteTopology_iff_isOpen_singleton.mpr fun x ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        simp
    have hQ : (inferInstance : TopologicalSpace (A ⧸ J)) =
        (⊥ : Ideal (A ⧸ J)).adicTopology :=
      (is_bot_adic_iff (A := A ⧸ J)).2 (inferInstance : DiscreteTopology (A ⧸ J))
    have hA : ‹TopologicalSpace A› = (⊥ : Ideal A).adicTopology :=
      (is_bot_adic_iff (A := A)).2 (inferInstance : DiscreteTopology A)
    rw [hA]
    apply (RingHom.continuous_adic_iff g
      (maximalIdeal (MvPowerSeries (Fin n) R)) ⊥).2
    obtain ⟨k, hk, hkmap⟩ :=
      (RingHom.continuous_adic_iff gbar
        (maximalIdeal (MvPowerSeries (Fin n) R)) ⊥).1 (by
          change @Continuous (MvPowerSeries (Fin n) R) (A ⧸ J)
            (maximalIdeal (MvPowerSeries (Fin n) R)).adicTopology
            (⊥ : Ideal (A ⧸ J)).adicTopology gbar
          rw [← ht, ← hQ]
          exact hgbar)
    refine ⟨k * 2, by omega, ?_⟩
    intro x hx
    have hmap : Ideal.map g
        (maximalIdeal (MvPowerSeries (Fin n) R) ^ k) ≤ J := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      have heq : gbar y = 0 := by simpa using hkmap y hy
      apply (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
      exact (DFunLike.congr_fun hred y).trans heq
    have hxmap : g x ∈ Ideal.map g
        (maximalIdeal (MvPowerSeries (Fin n) R) ^ (k * 2)) :=
      Ideal.mem_map_of_mem g hx
    rw [pow_mul, Ideal.map_pow] at hxmap
    have hsq : g x ∈ J ^ 2 := (Ideal.pow_right_mono hmap 2) hxmap
    simpa [hJ] using hsq
  refine ⟨g, ?_, ?_, hred⟩
  · rw [ht]
    exact hcont
  · ext x
    change g (MvPowerSeries.C (φ x)) = f x
    rw [show g (MvPowerSeries.C (φ x)) = c (φ x) by
      simp only [g, MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C]]
    exact DFunLike.congr_fun hcφ x

private theorem isFormallySmooth_mvPowerSeries_of_coefficient.{u, v, w}
    {R₀ : Type v} {R : Type w} [CommRing R₀] [CommRing R] [IsLocalRing R]
    (n : ℕ) (φ : R₀ →+* R)
    (hφ : @IsFormallySmooth.{u, v, w} R₀ R inferInstance
      (⊥ : Ideal R₀).adicTopology (⊥ : Ideal R₀).ringFilterBasis.isTopologicalRing
      (Ideal.isLinearTopology ⊥) inferInstance
      (maximalIdeal R).adicTopology (maximalIdeal R).ringFilterBasis.isTopologicalRing
      (Ideal.isLinearTopology _) φ) :
    @IsFormallySmooth.{u, v, w} R₀ (MvPowerSeries (Fin n) R) inferInstance
      (⊥ : Ideal R₀).adicTopology (⊥ : Ideal R₀).ringFilterBasis.isTopologicalRing
      (Ideal.isLinearTopology ⊥) inferInstance
      (maximalIdeal (MvPowerSeries (Fin n) R)).adicTopology
      (maximalIdeal (MvPowerSeries (Fin n) R)).ringFilterBasis.isTopologicalRing
      (Ideal.isLinearTopology _)
      ((MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R).comp φ) := by
  let : TopologicalSpace R₀ := (⊥ : Ideal R₀).adicTopology
  let : IsTopologicalRing R₀ := (⊥ : Ideal R₀).ringFilterBasis.isTopologicalRing
  let : TopologicalSpace R := (maximalIdeal R).adicTopology
  let : IsTopologicalRing R := (maximalIdeal R).ringFilterBasis.isTopologicalRing
  let : TopologicalSpace (MvPowerSeries (Fin n) R) :=
    (maximalIdeal (MvPowerSeries (Fin n) R)).adicTopology
  let : IsTopologicalRing (MvPowerSeries (Fin n) R) :=
    (maximalIdeal (MvPowerSeries (Fin n) R)).ringFilterBasis.isTopologicalRing
  change Continuous φ ∧ RingHom.FormallySmoothTop.{u, v, w} φ at hφ
  change Continuous ((MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R).comp φ) ∧
    RingHom.FormallySmoothTop.{u, v, w}
      ((MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R).comp φ)
  have hC : Continuous (MvPowerSeries.C : R → MvPowerSeries (Fin n) R) :=
    continuous_C_mvPowerSeries n
  exact ⟨hC.comp hφ.1,
    formallySmoothTop_mvPowerSeries n φ hφ.2 rfl rfl hC⟩

/-- **Stacks 07NL.** Formal power series rings over a characteristic-zero field,
over a field of characteristic `p`, and over a Cohen ring are formally smooth
over `ℚ`, `𝔽_p`, and `ℤ`, respectively, for their maximal-ideal-adic topologies. -/
@[stacks 07NL]
public theorem isFormallySmooth_mvPowerSeries.{u} (n p : ℕ)
    (K L Λ : Type*) [Field K] [CharZero K] [Field L] [Fact p.Prime] [CharP L p]
    [CommRing Λ] [IsDomain Λ] [IsCohenRing Λ] :
    letI : Algebra (ZMod p) L := ZMod.algebra L p
    @IsFormallySmooth.{u} ℚ (MvPowerSeries (Fin n) K) inferInstance
        (⊥ : Ideal ℚ).adicTopology (⊥ : Ideal ℚ).ringFilterBasis.isTopologicalRing
        (Ideal.isLinearTopology ⊥) inferInstance
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K)).adicTopology
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K)).ringFilterBasis.isTopologicalRing
        (Ideal.isLinearTopology _) (algebraMap ℚ (MvPowerSeries (Fin n) K)) ∧
      @IsFormallySmooth.{u} (ZMod p) (MvPowerSeries (Fin n) L) inferInstance
          (⊥ : Ideal (ZMod p)).adicTopology
          (⊥ : Ideal (ZMod p)).ringFilterBasis.isTopologicalRing
          (Ideal.isLinearTopology ⊥) inferInstance
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) L)).adicTopology
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) L)).ringFilterBasis.isTopologicalRing
          (Ideal.isLinearTopology _) (algebraMap (ZMod p) (MvPowerSeries (Fin n) L)) ∧
        @IsFormallySmooth.{u} ℤ (MvPowerSeries (Fin n) Λ) inferInstance
          (⊥ : Ideal ℤ).adicTopology (⊥ : Ideal ℤ).ringFilterBasis.isTopologicalRing
          (Ideal.isLinearTopology ⊥) inferInstance
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) Λ)).adicTopology
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) Λ)).ringFilterBasis.isTopologicalRing
          (Ideal.isLinearTopology _) (algebraMap ℤ (MvPowerSeries (Fin n) Λ)) := by
  let : Algebra (ZMod p) L := ZMod.algebra L p
  have hK : @IsFormallySmooth.{u} ℚ K inferInstance
      (⊥ : Ideal ℚ).adicTopology (⊥ : Ideal ℚ).ringFilterBasis.isTopologicalRing
      (Ideal.isLinearTopology ⊥) inferInstance
      (maximalIdeal K).adicTopology (maximalIdeal K).ringFilterBasis.isTopologicalRing
      (Ideal.isLinearTopology _) (algebraMap ℚ K) := by
    let : TopologicalSpace ℚ := (⊥ : Ideal ℚ).adicTopology
    let : IsTopologicalRing ℚ := (⊥ : Ideal ℚ).ringFilterBasis.isTopologicalRing
    let : TopologicalSpace K := (maximalIdeal K).adicTopology
    let : IsTopologicalRing K := (maximalIdeal K).ringFilterBasis.isTopologicalRing
    change Continuous (algebraMap ℚ K) ∧ RingHom.FormallySmoothTop.{u} (algebraMap ℚ K)
    constructor
    · have : DiscreteTopology ℚ := (is_bot_adic_iff (A := ℚ)).1 rfl
      exact continuous_of_discreteTopology
    · have hformal : @Algebra.FormallySmooth ℚ K _ _
          (algebraMap ℚ K).toAlgebra := by
        rw [toAlgebra_algebraMap]
        exact formallySmooth_field_charZero K
      exact formallySmoothTop_of_formallySmooth_of_isAdic
        (algebraMap ℚ K) (maximalIdeal K) rfl hformal
  have hL : @IsFormallySmooth.{u} (ZMod p) L inferInstance
      (⊥ : Ideal (ZMod p)).adicTopology
      (⊥ : Ideal (ZMod p)).ringFilterBasis.isTopologicalRing
      (Ideal.isLinearTopology ⊥) inferInstance
      (maximalIdeal L).adicTopology (maximalIdeal L).ringFilterBasis.isTopologicalRing
      (Ideal.isLinearTopology _) (algebraMap (ZMod p) L) := by
    let : TopologicalSpace (ZMod p) := (⊥ : Ideal (ZMod p)).adicTopology
    let : IsTopologicalRing (ZMod p) :=
      (⊥ : Ideal (ZMod p)).ringFilterBasis.isTopologicalRing
    let : TopologicalSpace L := (maximalIdeal L).adicTopology
    let : IsTopologicalRing L := (maximalIdeal L).ringFilterBasis.isTopologicalRing
    change Continuous (algebraMap (ZMod p) L) ∧
      RingHom.FormallySmoothTop.{u} (algebraMap (ZMod p) L)
    constructor
    · have : DiscreteTopology (ZMod p) := (is_bot_adic_iff (A := ZMod p)).1 rfl
      exact continuous_of_discreteTopology
    · exact formallySmoothTop_of_formallySmooth_of_isAdic
        (algebraMap (ZMod p) L) (maximalIdeal L) rfl
        (Algebra.formallySmooth_of_perfectField (ZMod p) L)
  have hΛ : @IsFormallySmooth.{u} ℤ Λ inferInstance
      (⊥ : Ideal ℤ).adicTopology (⊥ : Ideal ℤ).ringFilterBasis.isTopologicalRing
      (Ideal.isLinearTopology ⊥) inferInstance
      (maximalIdeal Λ).adicTopology (maximalIdeal Λ).ringFilterBasis.isTopologicalRing
      (Ideal.isLinearTopology _) (algebraMap ℤ Λ) := by
    let : TopologicalSpace ℤ := (⊥ : Ideal ℤ).adicTopology
    let : IsTopologicalRing ℤ := (⊥ : Ideal ℤ).ringFilterBasis.isTopologicalRing
    let : TopologicalSpace Λ := (maximalIdeal Λ).adicTopology
    let : IsTopologicalRing Λ := (maximalIdeal Λ).ringFilterBasis.isTopologicalRing
    change Continuous (algebraMap ℤ Λ) ∧ RingHom.FormallySmoothTop.{u} (algebraMap ℤ Λ)
    constructor
    · have : DiscreteTopology ℤ := (is_bot_adic_iff (A := ℤ)).1 rfl
      exact continuous_of_discreteTopology
    · simpa only [algebraMap_int_eq] using
        (formallySmoothTop_int_of_cohenRing
          (ringChar (ResidueField Λ)) Λ rfl)
  refine ⟨?_, ?_, ?_⟩
  · have hmap : (MvPowerSeries.C : K →+* MvPowerSeries (Fin n) K).comp
        (algebraMap ℚ K) = algebraMap ℚ (MvPowerSeries (Fin n) K) := by
      ext x
      simp [MvPowerSeries.algebraMap_apply]
    simpa only [hmap] using
      isFormallySmooth_mvPowerSeries_of_coefficient n (algebraMap ℚ K) hK
  · have hmap : (MvPowerSeries.C : L →+* MvPowerSeries (Fin n) L).comp
        (algebraMap (ZMod p) L) = algebraMap (ZMod p) (MvPowerSeries (Fin n) L) := by
      ext x
      simp [MvPowerSeries.algebraMap_apply]
    simpa only [hmap] using
      isFormallySmooth_mvPowerSeries_of_coefficient n (algebraMap (ZMod p) L) hL
  · have hmap : (MvPowerSeries.C : Λ →+* MvPowerSeries (Fin n) Λ).comp
        (algebraMap ℤ Λ) = algebraMap ℤ (MvPowerSeries (Fin n) Λ) := by
      ext x
      simp
    simpa only [hmap] using
      isFormallySmooth_mvPowerSeries_of_coefficient n (algebraMap ℤ Λ) hΛ

end

end

end

/-! ### Stacks Tag 07NN -/

section

section

open IsLocalRing
open Stacks.CompleteLocalRing.CohenStructure
open Stacks.CompleteLocalRing.RegularSubring

universe u v w

/-- Formal power series over a regular local ring are regular, with the expected embedding
dimension. -/
@[ega "0 17.3.8" "special case", sga "1 II 5.6" "(iii)"]
private theorem isRegularLocalRing_and_spanFinrank_mvPowerSeries (R : Type*) [CommRing R]
    [IsRegularLocalRing R] (n : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin n) R) ∧
      (maximalIdeal (MvPowerSeries (Fin n) R)).spanFinrank =
        (maximalIdeal R).spanFinrank + n := by
  obtain ⟨s, hcard, hs⟩ :=
    (IsNoetherian.noetherian (maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  have hle := spanFinrank_maximalIdeal_mvPowerSeries_le R n s hs
  rw [hcard] at hle
  have hdim : ((maximalIdeal R).spanFinrank + n : WithBot ℕ∞) ≤
      ringKrullDim (MvPowerSeries (Fin n) R) := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal]
    exact ringKrullDim_add_le_mvPowerSeries R n
  have hle' : ((maximalIdeal (MvPowerSeries (Fin n) R)).spanFinrank : WithBot ℕ∞) ≤
      (maximalIdeal R).spanFinrank + n := by exact_mod_cast hle
  have hreg : IsRegularLocalRing (MvPowerSeries (Fin n) R) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (hle'.trans hdim)
  refine ⟨hreg, le_antisymm hle ?_⟩
  exact_mod_cast hdim.trans (ringKrullDim_le_spanFinrank_maximalIdeal _)

/-- The old parameters together with the variables generate the maximal ideal. -/
private theorem ofList_map_C_append_X (R : Type*) [CommRing R] [IsLocalRing R]
    (xs : List R) (hxs : Ideal.ofList xs = maximalIdeal R) (n : ℕ) :
    Ideal.ofList (xs.map (MvPowerSeries.C (σ := Fin n)) ++
      List.ofFn (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)) =
        maximalIdeal (MvPowerSeries (Fin n) R) := by
  rw [Ideal.ofList_append, ← Ideal.map_ofList, hxs, maximalIdeal_mvPowerSeries]
  congr 1
  simp [Ideal.ofList, Set.range]

/-- A local map that carries parameters to an initial part of a parameter system is flat
and has regular closed fibre. -/
private theorem flat_and_regular_fibre_of_parameters
    {R S : Type*} [CommRing R] [IsRegularLocalRing R] [CommRing S]
    [IsRegularLocalRing S] (g : R →+* S) [IsLocalHom g]
    (xs : List R) (zs : List S)
    (hxs : Ideal.ofList xs = maximalIdeal R)
    (hxlen : xs.length = (maximalIdeal R).spanFinrank)
    (hys : Ideal.ofList (xs.map g ++ zs) = maximalIdeal S)
    (hylen : (xs.map g ++ zs).length = (maximalIdeal S).spanFinrank) :
    let : Algebra R S := g.toAlgebra
    Module.Flat R S ∧ IsRegularLocalRing (S ⧸ Ideal.map g (maximalIdeal R)) := by
  let : Algebra R S := g.toAlgebra
  have h := (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
    S).1 (xs.map g ++ zs) hys hylen
  have ht : (xs.map g ++ zs).take xs.length = xs.map g := by simp
  have hf := (h.2 xs.length (by simp)).1
  rw [ht, ← Ideal.map_ofList, hxs] at hf
  refine ⟨Module.Flat.of_ofList_eq_maximalIdeal_of_isWeaklyRegular_map S S xs hxs hxlen ?_, hf⟩
  exact ((RingTheory.Sequence.isWeaklyRegular_append_iff S _ _).mp h.1.toIsWeaklyRegular).1

/-- Local homomorphisms are continuous for the maximal-ideal-adic topologies. -/
private theorem continuous_of_isLocalHom {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S]
    (hR : IsAdic (maximalIdeal R)) (hS : IsAdic (maximalIdeal S))
    (f : R →+* S) [IsLocalHom f] : Continuous f := by
  apply continuous_of_continuousAt_zero f
  rw [ContinuousAt, map_zero]
  apply (hR.hasBasis_nhds_zero.tendsto_iff hS.hasBasis_nhds_zero).2
  intro n _
  refine ⟨n, trivial, ?_⟩
  exact Ideal.map_le_iff_le_comap.mp (by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (map_maximalIdeal_le f) n)

/-- The quotient topology of an adic ring is the adic topology for the image ideal. -/
public theorem IsAdic.map_quotient_mk {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (I J : Ideal R) (hI : IsAdic I) :
    IsAdic (Ideal.map (Ideal.Quotient.mk J) I) := by
  rw [isAdic_iff]
  constructor
  · intro n
    rw [← Ideal.map_pow, Ideal.map_eq_image_of_surjective _ Ideal.Quotient.mk_surjective]
    exact (QuotientRing.isOpenMap_coe J) _ ((isAdic_iff.mp hI).1 n)
  · intro s hs
    have hc := (QuotientRing.isOpenQuotientMap_mk J).continuous.continuousAt (x := 0)
    have hs' : (Ideal.Quotient.mk J) ⁻¹' s ∈ nhds (0 : R) :=
      hc.preimage_mem_nhds (by simpa using hs)
    obtain ⟨n, hn⟩ := (isAdic_iff.mp hI).2 _ hs'
    refine ⟨n, ?_⟩
    rw [← Ideal.map_pow, Ideal.map_eq_image_of_surjective _ Ideal.Quotient.mk_surjective]
    exact Set.image_subset_iff.mpr hn

/-- Formal smoothness lifts a compatible local map through a surjection of complete local
rings. -/
private theorem exists_lift_of_formallySmooth
    {P : Type u} {T : Type v} {S : Type w} {B : Type*}
    [CommRing P] [TopologicalSpace P] [IsTopologicalRing P] [IsLinearTopology P P]
    [CommRing T] [IsLocalRing T] [TopologicalSpace T]
    [IsTopologicalRing T] [IsLinearTopology T T]
    [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    [CommRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B]
    (hT : IsAdic (maximalIdeal T)) (a : P →+* T)
    (ha : IsFormallySmooth.{w} a)
    (b : P →+* S) (q : S →+* B) (hq : Function.Surjective q)
    (f : T →+* B) [IsLocalHom f]
    (hb : @Continuous P S _ (maximalIdeal S).adicTopology b)
    (hcomm : f.comp a = q.comp b) :
    ∃ φ : T →+* S, q.comp φ = f := by
  let : WithIdeal S := ⟨maximalIdeal S⟩
  let : WithIdeal B := ⟨maximalIdeal B⟩
  have : IsLocalHom q := IsLocalHom.of_surjective q hq
  have : T2Space B := (IsAdic.isHausdorff_iff (I := maximalIdeal B) rfl).1 inferInstance
  let e : (S ⧸ RingHom.ker q) ≃+* B := RingHom.quotientKerEquivOfSurjective hq
  have : IsLocalRing (S ⧸ RingHom.ker q) := e.symm.isLocalRing
  have : IsLocalHom e.symm.toRingHom := isLocalHom_toRingHom e.symm
  have hQ : IsAdic (maximalIdeal (S ⧸ RingHom.ker q)) := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk (RingHom.ker q))
      Ideal.Quotient.mk_surjective]
    exact isAdic_map_quotient_mk _ _ rfl
  have hcq : Continuous q := continuous_of_isLocalHom rfl rfl q
  have hce : Continuous e.symm.toRingHom := continuous_of_isLocalHom rfl hQ _
  have hcf : Continuous f := continuous_of_isLocalHom hT rfl f
  obtain ⟨φ, _, _, hφ⟩ :=
    exists_continuous_lift_of_isFormallySmooth_of_isAdic a (maximalIdeal T)
      hT ha (maximalIdeal S) rfl (RingHom.ker q)
      (isClosed_singleton.preimage hcq) 1 le_rfl
      (by simpa using le_maximalIdeal (RingHom.ker_ne_top q)) b hb
      (e.symm.toRingHom.comp f) (hce.comp hcf) (by
        ext x
        apply e.injective
        simpa [e] using DFunLike.congr_fun hcomm x)
  refine ⟨φ, ?_⟩
  ext x
  have hx := DFunLike.congr_fun hφ x
  have := congrArg e hx
  simpa [e] using this

/-- A power series presentation over a characteristic-zero field lifts through a surjection
of complete local rational algebras. -/
@[ega "0 19.3.11" "special case"]
private theorem exists_lift_mvPowerSeries_field
    {K S B : Type*} [Field K] [CharZero K] (n : ℕ)
    [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S] [Algebra ℚ S]
    [CommRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B]
    (q : S →+* B) (hq : Function.Surjective q)
    (f : MvPowerSeries (Fin n) K →+* B) [IsLocalHom f] :
    ∃ φ : MvPowerSeries (Fin n) K →+* S, q.comp φ = f := by
  let : WithIdeal S := ⟨maximalIdeal S⟩
  let : WithIdeal ℚ := ⟨⊥⟩
  let : TopologicalSpace ℚ := (⊥ : Ideal ℚ).adicTopology
  let : IsTopologicalRing ℚ := (⊥ : Ideal ℚ).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology ℚ ℚ := Ideal.isLinearTopology ⊥
  have : DiscreteTopology ℚ := is_bot_adic_iff.1 rfl
  let : WithIdeal (MvPowerSeries (Fin n) K) := ⟨maximalIdeal _⟩
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have : IsCohenRing (PadicInt 2) := padicInt_isCohenRing 2
  exact exists_lift_of_formallySmooth rfl (algebraMap ℚ _)
    (isFormallySmooth_mvPowerSeries n 2 K (ZMod 2) (PadicInt 2)).1
    (algebraMap ℚ S) q hq f continuous_of_discreteTopology (RingHom.ext_rat _ _)

/-- A power series presentation over a Cohen ring lifts through a surjection of complete
local rings. -/
@[ega "0 19.3.11" "special case"]
private theorem exists_lift_mvPowerSeries_cohen
    {Λ S B : Type*} [CommRing Λ] [IsDomain Λ] [IsCohenRing Λ] (n : ℕ)
    [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    [CommRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B]
    (q : S →+* B) (hq : Function.Surjective q)
    (f : MvPowerSeries (Fin n) Λ →+* B) [IsLocalHom f] :
    ∃ φ : MvPowerSeries (Fin n) Λ →+* S, q.comp φ = f := by
  let : WithIdeal S := ⟨maximalIdeal S⟩
  let : WithIdeal ℤ := ⟨⊥⟩
  let : TopologicalSpace ℤ := (⊥ : Ideal ℤ).adicTopology
  let : IsTopologicalRing ℤ := (⊥ : Ideal ℤ).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology ℤ ℤ := Ideal.isLinearTopology ⊥
  have : DiscreteTopology ℤ := is_bot_adic_iff.1 rfl
  let : WithIdeal (MvPowerSeries (Fin n) Λ) := ⟨maximalIdeal _⟩
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact exists_lift_of_formallySmooth rfl (algebraMap ℤ _)
    (isFormallySmooth_mvPowerSeries n 2 ℚ (ZMod 2) Λ).2.2
    (algebraMap ℤ S) q hq f continuous_of_discreteTopology (Subsingleton.elim _ _)

/-
`powerSeries_hom_ext` and `mvPowerSeries_hom_ext` lived here. They are now public in
`StacksFrontier/RingTheory/MvPowerSeries/HomExt.lean:32` and `:58`, which this file imports.
-/

/-- Adjoining variables makes a lifted coefficient homomorphism compatible with an arbitrary
local map from a power series ring. -/
private theorem exists_surjective_adjoin_variables
    {Λ S B : Type*} [CommRing Λ] [IsLocalRing Λ]
    [CommRing S] [IsLocalRing S] [CommRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B] (n : ℕ)
    (q : S →+* B) (hq : Function.Surjective q)
    (f : MvPowerSeries (Fin n) Λ →+* B) [IsLocalHom f]
    (φ : MvPowerSeries (Fin n) Λ →+* S) (hφ : q.comp φ = f) :
    ∃ q' : MvPowerSeries (Fin n) S →+* B,
      Function.Surjective q' ∧
      q'.comp (MvPowerSeries.map (φ.comp MvPowerSeries.C)) = f ∧
      IsLocalHom (MvPowerSeries.map (σ := Fin n) (φ.comp MvPowerSeries.C)) := by
  have hx : ∀ i : Fin n, f (MvPowerSeries.X i) ∈ maximalIdeal B := by
    intro i
    apply map_nonunit f
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  obtain ⟨q', hX, hC⟩ := exists_eval₂Hom (maximalIdeal B) _ hx q
  have hsurj : Function.Surjective q' := fun b => by
    obtain ⟨s, rfl⟩ := hq b
    exact ⟨MvPowerSeries.C s, hC s⟩
  have hcomm : q'.comp (MvPowerSeries.map (φ.comp MvPowerSeries.C)) = f := by
    apply mvPowerSeries_hom_ext (maximalIdeal B) n
    · intro r
      simpa [hC] using DFunLike.congr_fun hφ (MvPowerSeries.C r)
    · simpa using hX
    · simpa [hX] using hx
  have : IsLocalHom (q'.comp (MvPowerSeries.map (φ.comp MvPowerSeries.C))) :=
    hcomm.symm ▸ inferInstance
  exact ⟨q', hsurj, hcomm, isLocalHom_of_comp _ q'⟩

/-- A coefficient-ring equivalence induces an equivalence of power series rings. -/
private theorem nonempty_mvPowerSeries_map_equiv {R S : Type*} [CommRing R] [CommRing S]
    (σ : Type*) (e : R ≃+* S) : Nonempty (MvPowerSeries σ R ≃+* MvPowerSeries σ S) := by
  refine ⟨RingEquiv.ofRingHom (MvPowerSeries.map e.toRingHom)
    (MvPowerSeries.map e.symm.toRingHom) ?_ ?_⟩ <;>
    ext a d <;> simp

/-- Iterated power series in finitely many variables are power series in the combined
number of variables. -/
private theorem nonempty_iterated_mvPowerSeries_equiv (R : Type*) [CommRing R] (n m : ℕ) :
    Nonempty (MvPowerSeries (Fin n) (MvPowerSeries (Fin m) R) ≃+*
      MvPowerSeries (Fin (m + n)) R) := by
  induction n with
  | zero => exact ⟨(MvPowerSeries.isEmptyEquiv (Fin 0) _).toRingEquiv⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨e'⟩ := nonempty_mvPowerSeries_map_equiv Unit e
    exact ⟨(MvPowerSeries.finSuccEquiv (MvPowerSeries (Fin m) R) n).toRingEquiv.trans
      (e'.trans (MvPowerSeries.finSuccEquiv R (m + n)).toRingEquiv.symm)⟩

/-- Extending a coefficient map by the same formal variables preserves the property of
carrying a parameter system to part of a parameter system. -/
private theorem parameters_mvPowerSeries_map {R S : Type*} [CommRing R] [IsRegularLocalRing R]
    [CommRing S] [IsRegularLocalRing S] (c : R →+* S) (xs : List R) (zs : List S)
    (hxs : Ideal.ofList xs = maximalIdeal R)
    (hxlen : xs.length = (maximalIdeal R).spanFinrank)
    (hys : Ideal.ofList (xs.map c ++ zs) = maximalIdeal S)
    (hylen : (xs.map c ++ zs).length = (maximalIdeal S).spanFinrank) (n : ℕ) :
    let us := xs.map (MvPowerSeries.C (σ := Fin n)) ++
      List.ofFn (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)
    let vs := zs.map (MvPowerSeries.C (σ := Fin n))
    Ideal.ofList us = maximalIdeal (MvPowerSeries (Fin n) R) ∧
      us.length = (maximalIdeal (MvPowerSeries (Fin n) R)).spanFinrank ∧
      Ideal.ofList (us.map (MvPowerSeries.map c) ++ vs) =
        maximalIdeal (MvPowerSeries (Fin n) S) ∧
      (us.map (MvPowerSeries.map c) ++ vs).length =
        (maximalIdeal (MvPowerSeries (Fin n) S)).spanFinrank := by
  dsimp only
  refine ⟨ofList_map_C_append_X R xs hxs n, ?_, ?_, ?_⟩
  · simp [hxlen, (isRegularLocalRing_and_spanFinrank_mvPowerSeries R n).2]
  · have h := ofList_map_C_append_X S (xs.map c ++ zs) hys n
    simpa [List.map_append, List.map_map, Function.comp_def,
      Ideal.ofList_append, sup_assoc, sup_left_comm, sup_comm] using h
  · simp only [List.length_append, List.length_map, List.length_ofFn] at hylen ⊢
    rw [(isRegularLocalRing_and_spanFinrank_mvPowerSeries S n).2, ← hylen]
    omega

/-- Local homomorphisms preserve residue characteristic. -/
@[ega "0 21.1.3" "more general"]
private theorem ringChar_residueField_eq {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    ringChar (ResidueField A) = ringChar (ResidueField B) := by
  let : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map f).toAlgebra
  exact Algebra.ringChar_eq _ _

/-- The proof of Stacks 032A chooses the coefficient ring according to the residue
characteristic. The power series map extends the chosen coefficient map and sends its
variables into the maximal ideal. -/
private theorem exists_characteristic_refined_mvPowerSeries (R : Type u) [CommRing R]
    [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (hFG : (maximalIdeal R).FG) :
    ∃ (n : ℕ) (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsLocalRing Λ),
      (ringChar (ResidueField R) = 0 → IsField Λ) ∧
      (ringChar (ResidueField R) ≠ 0 → IsCohenRing Λ) ∧
      maximalIdeal Λ = Ideal.span {(ringChar (ResidueField R) : Λ)} ∧
      ∃ (c : Λ →+* R) (F : MvPowerSeries (Fin n) Λ →+* R),
        (∀ a : Λ, ¬ IsUnit a → c a ∈ maximalIdeal R) ∧
        Function.Surjective ((residue R).comp c) ∧
        Function.Surjective F ∧
        (∀ i, F (MvPowerSeries.X i) ∈ maximalIdeal R) ∧
        ∀ a, F (MvPowerSeries.C a) = c a := by
  obtain ⟨Λ, _, _, _, -, hpos, hmax, c, hlocal, hres⟩ := hasCoefficientRingHom R
  obtain ⟨n, y, hy⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hFG
  obtain ⟨F, hFsurj, hFX, hFC⟩ :=
    exists_surjective_eval₂Hom (maximalIdeal R) y hy c hres
  have hfield (hzero : ringChar (ResidueField R) = 0) : IsField Λ := by
    apply isField_iff_maximalIdeal_eq.mpr
    rw [hmax, hzero]
    simp
  refine ⟨n, Λ, inferInstance, inferInstance, inferInstance, hfield, hpos, hmax, c, F,
    hlocal, hres, hFsurj, ?_, hFC⟩
  intro i
  rw [hFX i]
  exact hy ▸ Ideal.subset_span ⟨i, rfl⟩

/-- Cohen presentations may be chosen in any larger universe while retaining the residue
characteristic of the ring being presented. -/
@[ega "0 19.8.8" "more general"]
private theorem exists_refined_presentation (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] :
    ∃ (n : ℕ) (Λ : Type (max u v)) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsLocalRing Λ),
      (ringChar (ResidueField A) = 0 → IsField Λ) ∧
      (ringChar (ResidueField A) ≠ 0 → IsCohenRing Λ) ∧
      maximalIdeal Λ = Ideal.span {(ringChar (ResidueField A) : Λ)} ∧
      ∃ q : MvPowerSeries (Fin n) Λ →+* A, Function.Surjective q := by
  let e : ULift.{v} A ≃+* A := ULift.ringEquiv
  have : IsLocalRing (ULift.{v} A) := e.symm.isLocalRing
  have : IsAdicComplete (maximalIdeal (ULift.{v} A)) (ULift.{v} A) :=
    isAdicComplete_maximalIdeal_of_ringEquiv e.symm
  obtain ⟨n, Λ, hΛ, hd, hl, hzero, hpos, hm, c, q, _, _, hq, _, _⟩ :=
    exists_characteristic_refined_mvPowerSeries (ULift.{v} A)
      (IsNoetherian.noetherian _)
  have hc : ringChar (ResidueField (ULift.{v} A)) = ringChar (ResidueField A) :=
    ringChar_residueField_eq (e : ULift.{v} A →+* A)
  refine ⟨n, Λ, hΛ, hd, hl, hc ▸ hzero, hc ▸ hpos, hc ▸ hm,
    e.toRingHom.comp q, e.surjective.comp hq⟩

/-- Fields and Cohen rings are complete regular local rings with the empty parameter system
or the one-element parameter system consisting of the residue characteristic. -/
private theorem coefficient_parameters {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsLocalRing Λ]
    (p : ℕ) (hfield : p = 0 → IsField Λ) (hcohen : p ≠ 0 → IsCohenRing Λ)
    (hm : maximalIdeal Λ = Ideal.span {(p : Λ)}) :
    IsRegularLocalRing Λ ∧ IsAdicComplete (maximalIdeal Λ) Λ ∧
      Ideal.ofList (if p = 0 then [] else [(p : Λ)]) = maximalIdeal Λ ∧
      (if p = 0 then [] else [(p : Λ)]).length = (maximalIdeal Λ).spanFinrank := by
  by_cases hp : p = 0
  · let : Field Λ := (hfield hp).toField
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · simpa only [maximalIdeal_eq_bot] using IsAdicComplete.bot Λ
    · simp [hp, maximalIdeal_eq_bot]
    · simp [hp, maximalIdeal_eq_bot]
  · have : IsCohenRing Λ := hcohen hp
    have hd : (maximalIdeal Λ).spanFinrank = 1 := by
      exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := Λ)).trans
        (IsDiscreteValuationRing.ringKrullDim_eq_one Λ)
    exact ⟨inferInstance, inferInstance, by simp [hp, hm], by simp [hp, hd]⟩

/-- **Stacks 07NN.** A local homomorphism `A → B` of Noetherian complete local rings admits
a commutative presentation by surjections from power series rings `R` and `S`. According to the
residue characteristic, these are power series rings over fields or over Cohen rings. The map
`R → S` carries a regular system of parameters to part of one, is flat, and has regular closed
fibre. -/
@[stacks 07NN,
  ega "0 19.8.8" "more general",
  sga "2 IV 4.8" "more general",
  sga "2 IX 2.3" "more general"]
public theorem exists_powerSeries_presentation_of_isLocalHom
    {A : Type u} {B : Type v}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f] :
    ∃ (R S : Type (max u v)) (_ : CommRing R) (_ : IsRegularLocalRing R)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
      (_ : CommRing S) (_ : IsRegularLocalRing S)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal S) S)
      (g : R →+* S) (qA : R →+* A) (qB : S →+* B),
      Function.Surjective qA ∧ Function.Surjective qB ∧
      IsLocalHom g ∧ IsLocalHom qA ∧ IsLocalHom qB ∧
      f.comp qA = qB.comp g ∧
      (∃ (xs : List R) (ys : List S) (zs : List S),
        Ideal.ofList xs = IsLocalRing.maximalIdeal R ∧
        xs.length = (IsLocalRing.maximalIdeal R).spanFinrank ∧
        Ideal.ofList ys = IsLocalRing.maximalIdeal S ∧
        ys.length = (IsLocalRing.maximalIdeal S).spanFinrank ∧
        ys = xs.map g ++ zs ∧
        (ringChar (IsLocalRing.ResidueField A) = 0 →
          ∃ (nR nS : ℕ) (kR kS : Type (max u v)) (_ : Field kR) (_ : Field kS),
            Nonempty (R ≃+* MvPowerSeries (Fin nR) kR) ∧
            Nonempty (S ≃+* MvPowerSeries (Fin nS) kS)) ∧
        (∀ p : ℕ, 0 < p → ringChar (IsLocalRing.ResidueField A) = p →
          ∃ (nR nS : ℕ) (ΛR ΛS : Type (max u v))
            (_ : CommRing ΛR) (_ : IsDomain ΛR) (_ : IsCohenRing ΛR)
            (_ : CommRing ΛS) (_ : IsDomain ΛS) (_ : IsCohenRing ΛS),
            Nonempty (R ≃+* MvPowerSeries (Fin nR) ΛR) ∧
            Nonempty (S ≃+* MvPowerSeries (Fin nS) ΛS) ∧
            IsLocalRing.maximalIdeal ΛR = Ideal.span {(p : ΛR)} ∧
            IsLocalRing.maximalIdeal ΛS = Ideal.span {(p : ΛS)} ∧
            ∃ xs', xs = (p : R) :: xs')) ∧
      letI : Algebra R S := g.toAlgebra
      Module.Flat R S ∧
        IsRegularLocalRing (S ⧸ Ideal.map g (IsLocalRing.maximalIdeal R)) := by
  classical
  obtain ⟨nA, ΛA, cA, dA, lA, hFA, hCA, hmA, qA, hqA⟩ :=
    exists_refined_presentation.{u, v} A
  obtain ⟨nB, ΛB, cB, dB, lB, hFB, hCB, hmB, qB, hqB⟩ :=
    exists_refined_presentation.{v, u} B
  have hpB := ringChar_residueField_eq f
  rw [← hpB] at hFB hCB hmB
  let p := ringChar (ResidueField A)
  obtain ⟨hregA, hcompleteA, hspanA, hlenA⟩ := coefficient_parameters p hFA hCA hmA
  obtain ⟨hregB, hcompleteB, hspanB, hlenB⟩ := coefficient_parameters p hFB hCB hmB
  let R := MvPowerSeries (Fin nA) ΛA
  let S₀ := MvPowerSeries (Fin nB) ΛB
  let S := MvPowerSeries (Fin nA) S₀
  have : IsRegularLocalRing R := (isRegularLocalRing_and_spanFinrank_mvPowerSeries ΛA nA).1
  have : IsRegularLocalRing S₀ := (isRegularLocalRing_and_spanFinrank_mvPowerSeries ΛB nB).1
  have : IsRegularLocalRing S := (isRegularLocalRing_and_spanFinrank_mvPowerSeries S₀ nA).1
  have : IsAdicComplete (maximalIdeal R) R := isAdicComplete_maximalIdeal_mvPowerSeries ΛA nA
  have : IsAdicComplete (maximalIdeal S₀) S₀ := isAdicComplete_maximalIdeal_mvPowerSeries ΛB nB
  have : IsAdicComplete (maximalIdeal S) S := isAdicComplete_maximalIdeal_mvPowerSeries S₀ nA
  have : IsLocalHom qA := IsLocalHom.of_surjective qA hqA
  obtain ⟨φ, hφ⟩ : ∃ φ : R →+* S₀, qB.comp φ = f.comp qA := by
    by_cases hp : p = 0
    · let : Field ΛA := (hFA hp).toField
      let : Field ΛB := (hFB hp).toField
      have : CharZero (ResidueField A) :=
        (CharP.ringChar_zero_iff_CharZero (R := ResidueField A)).mp hp
      have : CharZero (ResidueField B) :=
        (CharP.ringChar_zero_iff_CharZero (R := ResidueField B)).mp (hpB.symm.trans hp)
      have : CharZero ΛA := ((residue A).comp (qA.comp MvPowerSeries.C)).charZero
      have : CharZero ΛB := ((residue B).comp (qB.comp MvPowerSeries.C)).charZero
      exact exists_lift_mvPowerSeries_field nA qB hqB (f.comp qA)
    · have : IsCohenRing ΛA := hCA hp
      exact exists_lift_mvPowerSeries_cohen nA qB hqB (f.comp qA)
  obtain ⟨q, hq, hcomm, hlocal⟩ :=
    exists_surjective_adjoin_variables nA qB hqB (f.comp qA) φ hφ
  let c : ΛA →+* S₀ := φ.comp MvPowerSeries.C
  let g : R →+* S := MvPowerSeries.map c
  let ts : List ΛA := if p = 0 then [] else [(p : ΛA)]
  let zs₀ : List S₀ := List.ofFn (MvPowerSeries.X : Fin nB → S₀)
  have hmap : ts.map c =
      (if p = 0 then [] else [(p : ΛB)]).map (MvPowerSeries.C (σ := Fin nB)) := by
    by_cases hp : p = 0 <;> simp [ts, hp]
  have hs₀ : Ideal.ofList (ts.map c ++ zs₀) = maximalIdeal S₀ := by
    rw [hmap]
    exact ofList_map_C_append_X ΛB _ hspanB nB
  have hl₀ : (ts.map c ++ zs₀).length = (maximalIdeal S₀).spanFinrank := by
    rw [hmap]
    simp only [List.length_append, List.length_map, List.length_ofFn, zs₀]
    rw [hlenB, (isRegularLocalRing_and_spanFinrank_mvPowerSeries ΛB nB).2]
  let xs : List R := ts.map MvPowerSeries.C ++ List.ofFn MvPowerSeries.X
  let zs : List S := zs₀.map MvPowerSeries.C
  obtain ⟨hxs, hxlen, hys, hylen⟩ :=
    parameters_mvPowerSeries_map c ts zs₀ hspanA hlenA hs₀ hl₀ nA
  have : IsLocalHom g := hlocal
  refine ⟨R, S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, g, qA, q, hqA, hq, inferInstance, inferInstance,
    IsLocalHom.of_surjective q hq, hcomm.symm, ?_, ?_⟩
  · refine ⟨xs, xs.map g ++ zs, zs, hxs, hxlen, hys, hylen, rfl, ?_, ?_⟩
    · intro hp
      let : Field ΛA := (hFA hp).toField
      let : Field ΛB := (hFB hp).toField
      exact ⟨nA, nB + nA, ΛA, ΛB, inferInstance, inferInstance,
        ⟨RingEquiv.refl _⟩, nonempty_iterated_mvPowerSeries_equiv ΛB nA nB⟩
    · intro p' hpos hp'
      have hp : p ≠ 0 := by dsimp [p]; omega
      have : IsCohenRing ΛA := hCA hp
      have : IsCohenRing ΛB := hCB hp
      refine ⟨nA, nB + nA, ΛA, ΛB, inferInstance, inferInstance, inferInstance,
        inferInstance, inferInstance, inferInstance, ⟨RingEquiv.refl _⟩,
        nonempty_iterated_mvPowerSeries_equiv ΛB nA nB, by simpa [hp'] using hmA,
        by simpa [hp'] using hmB, List.ofFn MvPowerSeries.X, ?_⟩
      simp [xs, ts, p, hp', Nat.ne_of_gt hpos]
  · exact flat_and_regular_fibre_of_parameters g xs zs hxs hxlen hys hylen

end

end

/-! ### Stacks Tag 09Q8 -/

section

section

@[expose] public section

open IsLocalRing

private theorem isNoetherianRing_pullback_of_surjective {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (f : S →+* R) (g : T →+* R)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    IsNoetherianRing (f.pullback g) := by
  let P := f.pullback g
  let α : P →+* S := f.pullbackFst g
  let β : P →+* T := f.pullbackSnd g
  have hα : Function.Surjective α := RingHom.surjective_pullbackFst_of_surjective f g hg
  have hβ : Function.Surjective β := RingHom.surjective_pullbackSnd_of_surjective f g hf
  constructor
  intro I
  have hIα : (Ideal.map α I).FG := IsNoetherian.noetherian _
  have hIβ : (Ideal.map β (I ⊓ RingHom.ker α)).FG := IsNoetherian.noetherian _
  have hker : (I ⊓ RingHom.ker α).FG := by
    let : Algebra P T := β.toAlgebra
    let K : Submodule P P := I ⊓ RingHom.ker α
    let l : P →ₗ[P] T := Module.compHom.toLinearMap β
    let lK : K →ₗ[P] T := l.comp K.subtype
    have hinj : Function.Injective lK := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · have hx : α x = 0 := x.property.2
        have hy : α y = 0 := y.property.2
        exact hx.trans hy.symm
      · exact hxy
    have heq : Submodule.map l K =
        (Ideal.map β (I ⊓ RingHom.ker α)).restrictScalars P := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Ideal.mem_map_of_mem β hy
      · intro hx
        obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective β hβ).mp hx
        exact ⟨y, hy, hxy⟩
    have hmap : (Submodule.map l K).FG := by
      rw [heq]
      exact Submodule.FG.restrictScalars_of_surjective hIβ hβ
    have hmapK : (LinearMap.range lK).FG := by
      simpa [lK, LinearMap.range_comp, K] using hmap
    have htop : (⊤ : Submodule P K).FG :=
      Submodule.fg_of_fg_map_injective (N := ⊤) lK hinj (by rwa [Submodule.map_top])
    exact (Submodule.fg_top K).mp htop
  exact Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective hIα hker hα

universe q

private theorem isAdicComplete_of_exact {A : Type q} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {M N : Type q} {Q : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    [AddCommGroup Q] [Module A Q]
    [IsAdicComplete I N] [IsAdicComplete I Q]
    (f : M →ₗ[A] N) (g : N →ₗ[A] Q)
    (hf : Function.Injective f) (hex : Function.Exact f g) :
    IsAdicComplete I M := by
  apply (AdicCompletion.of_bijective_iff).mp
  constructor
  · intro x y hxy
    apply hf
    apply AdicCompletion.of_injective I N
    simpa only [AdicCompletion.map_of] using
      congrArg (AdicCompletion.map I f) hxy
  · intro x
    have hmapinj := AdicCompletion.map_injective I hf
    obtain ⟨y, hy⟩ := AdicCompletion.of_surjective I N
      (AdicCompletion.map I f x)
    have hgy : g y = 0 := by
      apply AdicCompletion.of_injective I Q
      rw [← AdicCompletion.map_of, hy]
      change (AdicCompletion.map I g ∘ₗ AdicCompletion.map I f) x = _
      rw [AdicCompletion.map_comp, hex.linearMap_comp_eq_zero]
      simp
    obtain ⟨z, hz⟩ := (hex y).mp hgy
    refine ⟨z, ?_⟩
    apply hmapinj
    rw [AdicCompletion.map_of, hz, ← hy]

private theorem ideal_smul_prod {A : Type*} [CommRing A] (I : Ideal A)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (U : Submodule A M) (V : Submodule A N) :
    I • U.prod V = (I • U).prod (I • V) := by
  rw [LinearMap.prod_eq_sup_map, Submodule.smul_sup,
    ← Submodule.map_smul'', ← Submodule.map_smul'', LinearMap.prod_eq_sup_map]

private theorem isAdicComplete_prod {A : Type*} [CommRing A] (I : Ideal A)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [IsAdicComplete I M] [IsAdicComplete I N] :
    IsAdicComplete I (M × N) := by
  have hpow (n : ℕ) :
      (I ^ n • (⊤ : Submodule A (M × N))) =
        (I ^ n • (⊤ : Submodule A M)).prod (I ^ n • (⊤ : Submodule A N)) := by
    rw [← Submodule.prod_top, ideal_smul_prod]
  have hHaus : IsHausdorff I (M × N) := by
    constructor
    intro x hx
    apply Prod.ext
    · apply IsHausdorff.haus' (I := I) x.1
      intro n
      have h := hx n
      rw [SModEq.sub_mem, hpow] at h
      simpa [SModEq.sub_mem] using h.1
    · apply IsHausdorff.haus' (I := I) x.2
      intro n
      have h := hx n
      rw [SModEq.sub_mem, hpow] at h
      simpa [SModEq.sub_mem] using h.2
  have hPre : IsPrecomplete I (M × N) := by
    constructor
    intro a ha
    have ha₁ : ∀ {m n}, m ≤ n →
        (a m).1 ≡ (a n).1 [SMOD (I ^ m • (⊤ : Submodule A M))] := by
      intro m n hmn
      have h := ha hmn
      rw [SModEq.sub_mem, hpow] at h
      simpa [SModEq.sub_mem] using h.1
    have ha₂ : ∀ {m n}, m ≤ n →
        (a m).2 ≡ (a n).2 [SMOD (I ^ m • (⊤ : Submodule A N))] := by
      intro m n hmn
      have h := ha hmn
      rw [SModEq.sub_mem, hpow] at h
      simpa [SModEq.sub_mem] using h.2
    obtain ⟨x, hx⟩ := IsPrecomplete.prec' (I := I) (fun n => (a n).1) ha₁
    obtain ⟨y, hy⟩ := IsPrecomplete.prec' (I := I) (fun n => (a n).2) ha₂
    refine ⟨(x,y), ?_⟩
    intro n
    rw [SModEq.sub_mem, hpow]
    exact ⟨by simpa [SModEq.sub_mem] using hx n,
      by simpa [SModEq.sub_mem] using hy n⟩
  exact { toIsHausdorff := hHaus, toIsPrecomplete := hPre }

private theorem isAdicComplete_pullback_of_surjective {R S T : Type*}
    [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsAdicComplete (maximalIdeal S) S]
    [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (maximalIdeal T) T]
    (f : S →+* R) (g : T →+* R) [IsLocalHom g]
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    letI : IsLocalRing (f.pullback g) := RingHom.isLocalRing_pullback f g
    IsAdicComplete (maximalIdeal (f.pullback g)) (f.pullback g) := by
  let : IsLocalRing (f.pullback g) := RingHom.isLocalRing_pullback f g
  let : IsNoetherianRing (f.pullback g) := isNoetherianRing_pullback_of_surjective f g hf hg
  let P := f.pullback g
  let α : P →+* S := f.pullbackFst g
  let β : P →+* T := f.pullbackSnd g
  let h : P →+* R := f.comp α
  let I : Ideal P := maximalIdeal P
  have hα : Function.Surjective α := RingHom.surjective_pullbackFst_of_surjective f g hg
  have hβ : Function.Surjective β := RingHom.surjective_pullbackSnd_of_surjective f g hf
  have hh : Function.Surjective h := hf.comp hα
  let : Algebra P S := α.toAlgebra
  let : Algebra P T := β.toAlgebra
  let : Algebra P R := h.toAlgebra
  have : IsAdicComplete I S := by
    apply (IsAdicComplete.map_algebraMap_iff (R := P) (S := S) I S).mp
    rw [show algebraMap P S = α from rfl,
      IsLocalRing.map_maximalIdeal_of_surjective α hα]
    exact inferInstance
  have : IsAdicComplete I T := by
    apply (IsAdicComplete.map_algebraMap_iff (R := P) (S := T) I T).mp
    rw [show algebraMap P T = β from rfl,
      IsLocalRing.map_maximalIdeal_of_surjective β hβ]
    exact inferInstance
  have : IsAdicComplete I R := by
    apply (IsAdicComplete.map_algebraMap_iff (R := P) (S := R) I R).mp
    rw [show algebraMap P R = h from rfl,
      IsLocalRing.map_maximalIdeal_of_surjective h hh]
    exact inferInstance
  have : IsAdicComplete I (S × T) := isAdicComplete_prod I
  let inc : P →ₗ[P] S × T := {
    toFun := fun x => x.val
    map_add' _ _ := rfl
    map_smul' _ _ := Prod.ext rfl rfl
  }
  let diff : S × T →ₗ[P] R := {
    toFun := fun x => f x.1 - g x.2
    map_add' x y := by
      change f (x.1 + y.1) - g (x.2 + y.2) = (f x.1 - g x.2) + (f y.1 - g y.2)
      rw [map_add, map_add]
      abel
    map_smul' a x := by
      change f (α a * x.1) - g (β a * x.2) = h a * (f x.1 - g x.2)
      rw [map_mul, map_mul, show g (β a) = h a from a.property.symm,
        show f (α a) = h a from rfl]
      ring
  }
  have hinc : Function.Injective inc := fun _ _ hxy ↦ Subtype.ext hxy
  have hex : Function.Exact inc diff := fun x ↦
    ⟨fun hx ↦ ⟨⟨x, sub_eq_zero.mp hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact sub_eq_zero.mpr y.property⟩
  have hdiff : Function.Surjective diff := fun r ↦ by
    obtain ⟨s, hs⟩ := hf r
    exact ⟨(s, 0), by simpa [diff] using hs⟩
  have : Module.Finite P R := Module.Finite.of_surjective (Algebra.linearMap P R) hh
  have : Module.Finite P (S × T) := Module.Finite.of_exact hex hdiff
  exact isAdicComplete_of_exact I inc diff hinc hex

/-- **Stacks 09Q8.** The pullback of two surjective maps of complete Noetherian local rings is
again a complete Noetherian local ring. -/
@[stacks 09Q8, ega "IV 19.3.2.1" "(iii)"]
public theorem isNoetherianCompleteLocalRing_pullback.{u, v, w}
    {R : Type u} {S : Type v} {S' : Type w}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
    [CommRing S'] [IsLocalRing S'] [IsNoetherianRing S']
    [IsAdicComplete (IsLocalRing.maximalIdeal S') S']
    (f : S →+* R) (f' : S' →+* R)
    (hf : Function.Surjective f) (hf' : Function.Surjective f') :
    ∃ hlocal : IsLocalRing (f.pullback f'),
      letI := hlocal
      IsNoetherianRing (f.pullback f') ∧
        IsAdicComplete (IsLocalRing.maximalIdeal (f.pullback f')) (f.pullback f') := by
  let : IsLocalHom f' := IsLocalHom.of_surjective f' hf'
  let hlocal : IsLocalRing (f.pullback f') := RingHom.isLocalRing_pullback f f'
  refine ⟨hlocal, ?_⟩
  let := hlocal
  exact ⟨isNoetherianRing_pullback_of_surjective f f' hf hf',
    isAdicComplete_pullback_of_surjective f f' hf hf'⟩

end

end

end

end
