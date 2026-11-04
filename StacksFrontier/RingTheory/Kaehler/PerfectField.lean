module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.RingTheory.Derivation.MapPowChar
public import Std.Tactic.BVDecide.Normalize.Prop
public import StacksFrontier.FieldTheory.PthRoots
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing differentials over a perfect field are `p`-th powers

Let `k` be a perfect field of characteristic `p > 0` and let `K/k` be a field extension. The
universal `k`-derivation `d : K → Ω[K⁄k]` kills every `p`-th power, and the converse holds:
`d a = 0` precisely when `a ∈ K` is a `p`-th power. In other words the kernel of
`d : K → Ω[K⁄k]` is the subfield `K^p` of `p`-th powers.

## Main results

* `Stacks.KaehlerDifferential.PthPowers.solution`: for `K/k` an extension of a perfect field `k`
  of characteristic `p`, `KaehlerDifferential.D k K a = 0` if and only if `a = b ^ p` for some
  `b : K`.
* `KaehlerDifferential.D_eq_zero_iff_exists_pow_eq`: the same statement.

## References

* [StacksProject 031W](https://stacks.math.columbia.edu/tag/031W)
-/

@[expose] public section

@[expose] public section

namespace Stacks.KaehlerDifferential.PthPowers

open Polynomial

/-- A derivation of a field extension `K/F` vanishing on a set `s` vanishes on `F(s)`. -/
private lemma Derivation.eq_zero_of_mem_adjoin {F K M : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup M] [Module F M] [Module K M] (D : Derivation F K M) {s : Set K}
    (hs : ∀ x ∈ s, D x = 0) {y : K} (hy : y ∈ IntermediateField.adjoin F s) : D y = 0 := by
  induction hy using IntermediateField.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap x => exact D.map_algebraMap x
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | inv x _ hx => rw [D.leibniz_inv, hx, smul_zero]
  | mul x y _ _ hx hy => rw [D.leibniz, hx, hy, smul_zero, smul_zero, add_zero]

/-- The bottom intermediate field of `K` over an intermediate field `M` of `K/F` is `M` itself. -/
private lemma mem_bot_iff_mem {F K : Type*} [Field F] [Field K] [Algebra F K]
    (M : IntermediateField F K) {y : K} : y ∈ (⊥ : IntermediateField ↥M K) ↔ y ∈ M := by
  rw [← IntermediateField.mem_restrictScalars (K := F),
    IntermediateField.restrictScalars_bot_eq_self]

/-- If `d a = 0` in `Ω[K⁄F]`, then `d a = 0` in `Ω[K⁄S]` for an intermediate ring `S`. -/
private lemma D_eq_zero_of_tower {F S K : Type*} [CommRing F] [CommRing S] [CommRing K]
    [Algebra F S] [Algebra F K] [Algebra S K] [IsScalarTower F S K] {a : K}
    (hd : KaehlerDifferential.D F K a = 0) : KaehlerDifferential.D S K a = 0 := by
  simpa [KaehlerDifferential.map_D] using congrArg (KaehlerDifferential.map F S K K) hd

/-- An element whose `p`-th power lies in the base field is integral over it. -/
private lemma isIntegral_of_pow_eq {F K : Type*} [Field F] [Field K] [Algebra F K] {p : ℕ}
    [Fact p.Prime] {x : K} {c : F} (hc : algebraMap F K c = x ^ p) : IsIntegral F x :=
  IsIntegral.of_pow (Fact.out : p.Prime).pos (hc ▸ isIntegral_algebraMap)

/-- If `x ^ p = c` lies in the base field `F` and `x ∉ F`, the minimal polynomial of `x` over `F`
is `X ^ p - c`. -/
private lemma minpoly_eq_X_pow_sub_C {F K : Type*} [Field F] [Field K] [Algebra F K] {p : ℕ}
    [Fact p.Prime] [CharP K p] {x : K} {c : F} (hc : algebraMap F K c = x ^ p)
    (hx : x ∉ (⊥ : IntermediateField F K)) : minpoly F x = X ^ p - C c := by
  have hp : p.Prime := Fact.out
  have : ExpChar K p := ExpChar.prime hp
  have hb : ∀ b : F, b ^ p ≠ c := fun b hb => hx <| IntermediateField.mem_bot.2
    ⟨b, frobenius_inj K p (by rw [frobenius_def, frobenius_def, ← map_pow, hb, hc])⟩
  exact (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hp hb)
    (by simp [hc]) (monic_X_pow_sub_C c hp.ne_zero)).symm

/-- If `x ^ p` lies in the base field `F` and `x ∉ F`, then `[F(x) : F] = p`. -/
private lemma finrank_adjoin_simple_eq {F K : Type*} [Field F] [Field K] [Algebra F K] {p : ℕ}
    [Fact p.Prime] [CharP K p] {x : K} {c : F} (hc : algebraMap F K c = x ^ p)
    (hx : x ∉ (⊥ : IntermediateField F K)) :
    Module.finrank F (IntermediateField.adjoin F {x}) = p := by
  rw [IntermediateField.adjoin.finrank (isIntegral_of_pow_eq (p := p) hc),
    minpoly_eq_X_pow_sub_C hc hx, natDegree_X_pow_sub_C]

/-- A purely inseparable simple extension `K = F(a)` with `a` integral over `F` and `d a = 0` in
`Ω[K⁄F]` is trivial. -/
@[ega "0 21.1.6" "Field case"]
private lemma surjective_algebraMap_of_D_eq_zero {F K : Type*} [Field F] [Field K] [Algebra F K]
    [IsPurelyInseparable F K] {a : K} (hint : IsIntegral F a)
    (htop : IntermediateField.adjoin F {a} = ⊤) (hd : KaehlerDifferential.D F K a = 0) :
    Function.Surjective (algebraMap F K) := by
  have : FiniteDimensional F K := by
    have h1 := IntermediateField.adjoin.finiteDimensional hint
    rw [htop] at h1
    exact (IntermediateField.topEquiv (F := F) (E := K)).toLinearEquiv.finiteDimensional
  have hsub : Subsingleton Ω[K⁄F] := by
    have hspan : Submodule.span K (Set.range (KaehlerDifferential.D F K)) = ⊥ :=
      Submodule.span_eq_bot.2 <| by
        rintro y ⟨z, rfl⟩
        exact Derivation.eq_zero_of_mem_adjoin _ (by simpa using hd)
          (htop ▸ IntermediateField.mem_top)
    rw [KaehlerDifferential.span_range_derivation] at hspan
    exact subsingleton_of_forall_eq 0 fun y =>
      (Submodule.eq_bot_iff _).1 hspan y Submodule.mem_top
  have : Algebra.FormallyUnramified F K := (Algebra.formallyUnramified_iff F K).2 hsub
  rw [← RingHom.range_eq_top]
  exact Algebra.FormallyUnramified.range_eq_top_of_isPurelyInseparable F K

/-- **The kernel of `d` for a purely inseparable extension of exponent one.** Let `K/F` be an
extension of fields of characteristic `p` in which every `p`-th power of `K` already lies in `F`.
Then `d a = 0` in `Ω[K⁄F]` if and only if `a ∈ F`. -/
@[ega "0 21.4.4" "special case"]
private theorem D_eq_zero_iff_mem_bot {F K : Type*} [Field F] [Field K] [Algebra F K] {p : ℕ}
    [Fact p.Prime] [CharP K p] (hpow : ∀ x : K, x ^ p ∈ (⊥ : IntermediateField F K)) (a : K) :
    KaehlerDifferential.D F K a = 0 ↔ a ∈ (⊥ : IntermediateField F K) := by
  have hp : p.Prime := Fact.out
  refine ⟨fun hd => ?_, fun ha => ?_⟩
  · by_contra ha
    obtain ⟨M, hM⟩ := zorn_le₀ {N : IntermediateField F K | a ∉ N} fun c hcS hc => by
      rcases c.eq_empty_or_nonempty with rfl | ⟨N₀, hN₀⟩
      · exact ⟨⊥, ha, by simp⟩
      · have : Nonempty c := ⟨⟨N₀, hN₀⟩⟩
        refine ⟨sSup c, fun hmem => ?_, fun z hz => le_sSup hz⟩
        rw [sSup_eq_iSup', ← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed
          (directedOn_iff_directed.1 hc.directedOn)] at hmem
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem
        exact hcS i.2 hi
    have hMa : a ∉ M := hM.prop
    have : CharP ↥M p := M.charP' p
    have : ExpChar ↥M p := ExpChar.prime hp
    have hMpow : ∀ x : K, x ^ p ∈ M :=
      fun x => (bot_le : (⊥ : IntermediateField F K) ≤ M) (hpow x)
    have hnotbot : ∀ y : K, y ∉ M → y ∉ (⊥ : IntermediateField ↥M K) :=
      fun y hy h => hy ((mem_bot_iff_mem M).1 h)
    have : IsPurelyInseparable ↥M K := (isPurelyInseparable_iff_pow_mem ↥M p).2 fun x =>
      ⟨1, ⟨⟨x ^ p, hMpow x⟩, by simp⟩⟩
    have htop : IntermediateField.adjoin ↥M {a} = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      by_cases hxM : x ∈ M
      · exact (IntermediateField.adjoin ↥M {a}).algebraMap_mem (⟨x, hxM⟩ : ↥M)
      · have hax : a ∈ IntermediateField.adjoin ↥M {x} := by
          by_contra hax
          have hle : M ≤ (IntermediateField.adjoin ↥M {x}).restrictScalars F := fun y hy =>
            (IntermediateField.adjoin ↥M {x}).algebraMap_mem (⟨y, hy⟩ : ↥M)
          exact hxM (hM.2 hax hle (IntermediateField.mem_adjoin_simple_self ↥M x))
        have : FiniteDimensional ↥M (IntermediateField.adjoin ↥M {x}) :=
          IntermediateField.adjoin.finiteDimensional
            (isIntegral_of_pow_eq (p := p) (c := (⟨x ^ p, hMpow x⟩ : ↥M)) rfl)
        rw [IntermediateField.eq_of_le_of_finrank_le
          (IntermediateField.adjoin_simple_le_iff.2 hax)
          (by rw [finrank_adjoin_simple_eq (c := (⟨a ^ p, hMpow a⟩ : ↥M)) rfl (hnotbot a hMa),
            finrank_adjoin_simple_eq (c := (⟨x ^ p, hMpow x⟩ : ↥M)) rfl (hnotbot x hxM)])]
        exact IntermediateField.mem_adjoin_simple_self _ x
    obtain ⟨y, hy⟩ := surjective_algebraMap_of_D_eq_zero
      (isIntegral_of_pow_eq (p := p) (c := (⟨a ^ p, hMpow a⟩ : ↥M)) rfl) htop
      (D_eq_zero_of_tower hd) a
    exact hMa (hy ▸ y.2)
  · obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.1 ha
    exact Derivation.map_algebraMap _ c

/-- For `k` a perfect field of characteristic `p` and `K/k` a field extension, the `p`-th powers
of `K` form an intermediate field of `K/k`. -/
private lemma exists_intermediateField_mem_iff_exists_pow_eq (k K : Type*) [Field k] [Field K]
    [Algebra k K] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] [CharP K p] :
    ∃ F : IntermediateField k K, ∀ y : K, y ∈ F ↔ ∃ x : K, x ^ p = y := by
  have hp : p.Prime := Fact.out
  have : ExpChar k p := ExpChar.prime hp
  have : ExpChar K p := ExpChar.prime hp
  have : PerfectRing k p := PerfectField.toPerfectRing p
  exact ⟨(frobenius K p).fieldRange.toIntermediateField fun y =>
    ⟨algebraMap k K ((frobeniusEquiv k p).symm y), by
      rw [frobenius_def, ← map_pow, frobeniusEquiv_symm_pow_p]⟩,
    fun y => ⟨fun ⟨z, hz⟩ => ⟨z, hz⟩, fun ⟨z, hz⟩ => ⟨z, hz⟩⟩⟩

/-- For `k` a perfect field of characteristic `p > 0`, `K/k` a field extension and `a : K`,
`d a = 0` in `Ω[K⁄k]` if and only if `a` is a `p`-th power in `K`. -/
public theorem solution {k K : Type*} [Field k] [Field K]
    [Algebra k K] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (a : K) :
    KaehlerDifferential.D k K a = 0 ↔ ∃ b : K, b ^ p = a := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  refine ⟨fun h => ?_, fun ⟨b, hb⟩ => hb ▸ Derivation.map_pow_char_eq_zero _ p b⟩
  obtain ⟨F, hF⟩ := exists_intermediateField_mem_iff_exists_pow_eq k K p
  have : CharP ↥F p := F.charP' p
  exact (hF a).1 ((mem_bot_iff_mem F).1 ((D_eq_zero_iff_mem_bot (p := p)
    (fun x => (mem_bot_iff_mem F).2 ((hF _).2 ⟨x, rfl⟩)) a).1 (D_eq_zero_of_tower h)))

end Stacks.KaehlerDifferential.PthPowers

end

@[expose] public section

/-- **Vanishing differentials over a perfect field are `p`-th powers.** Let `k` be a perfect
field of characteristic `p > 0`, let `K/k` be a field extension and let `a : K`. Then `d a = 0` in
`Ω[K⁄k]` if and only if `a` is a `p`-th power in `K`. Equivalently, the kernel of the universal
`k`-derivation `d : K → Ω[K⁄k]` is the subfield of `p`-th powers of `K`. -/
@[stacks 031W "The source's `d a = 0 in Ω_{K/k}` is `KaehlerDifferential.D k K a = 0` and `a` is a
`p`-th power is `∃ b, b ^ p = a`; characteristic `p > 0` is `[Fact p.Prime] [CharP k p]` on the
base. See the module docstring.",
  ega "0 21.4.4" "more general",
  ega "0 21.4.6" "(a) ⇔ (b), special case"]
public theorem KaehlerDifferential.D_eq_zero_iff_exists_pow_eq {k K : Type*} [Field k] [Field K]
    [Algebra k K] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (a : K) :
    KaehlerDifferential.D k K a = 0 ↔ ∃ b : K, b ^ p = a :=
  Stacks.KaehlerDifferential.PthPowers.solution p a

end
