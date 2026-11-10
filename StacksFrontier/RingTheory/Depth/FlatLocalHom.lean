module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.LinearAlgebra.Matrix.CommSemiring

public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Depth.Criteria
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Depth along a flat local homomorphism

Let `R → S` be a local homomorphism of Noetherian local rings, let `M` be a finite `R`-module and
let `N` be a finite `S`-module which is flat over `R`. Then

`depth_S(N ⊗_R M) = depth_R(M) + depth_S(N/𝔪_R N)`,

the depths being taken along the maximal ideal of the ring each module is written over. Taking
`M = R` and `N = S`, a flat local homomorphism `R → S` of local rings with `S` Noetherian
satisfies `depth(S) = depth(R) + depth(S/𝔪_R S)`.

## Main results

* `Module.depth_tensorProduct_of_flat`: `depth_S(N ⊗_R M) = depth_R(M) + depth_S(N/𝔪_R N)` for
  `N` flat over `R`.
* `Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal`:
  `depth_{𝔪_S}(S) = depth_{𝔪_R}(R) + depth_{𝔪_S}(S/𝔪_R S)` for a flat local homomorphism
  `R → S` onto a Noetherian local ring.
* `Stacks.Depth.FlatLocalFibreRing.depth_quotient_smul_top`: for ideals `I` and `J` of `A`, the
  `I`-depth of the `A`-module `A ⧸ J • ⊤` is that of the quotient ring `A ⧸ J`.

## Implementation notes

Depth is `Module.depth`, a value in `ℕ∞` which is `⊤` exactly when the ideal saturates the
module; with that convention the formula also covers `M = 0` and `N = 0`, where both sides are
`⊤`.

The tensor product is written `N ⊗[R] M`, because the `S`-module structure on a tensor product
over `R` is carried by the left factor (`TensorProduct.AlgebraTensorModule`, through
`IsScalarTower R S N`); it is the `S`-module `M ⊗_R N` by `TensorProduct.comm`. The fibre
`N/𝔪_R N` is spelled `N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤)`: `𝔪_R N` is the
`S`-submodule `(𝔪_R S) • N` of `N`.

The depth of the fibre `N/𝔪_R N`, and of the fibre ring `S/𝔪_R S`, is taken over `S` along
`𝔪_S`. This is its depth over `S/𝔪_R S` along the maximal ideal `𝔪_S/𝔪_R S`: an element of `S`
acts on `N/𝔪_R N` and on its quotients as its class in `S/𝔪_R S` does, and `𝔪_S` surjects onto
`𝔪_S/𝔪_R S`, so the regular sequences of the two kinds correspond, length by length.

In the ring case `IsNoetherianRing R` is not assumed: a flat local homomorphism is faithfully flat
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`), and Noetherianity descends along a faithfully
flat ring map, so it follows from the remaining hypotheses.

## References

* [Stacks Project, Tag 0337](https://stacks.math.columbia.edu/tag/0337)
* [Stacks Project, Tag 0338](https://stacks.math.columbia.edu/tag/0338)
* [EGA IV, Proposition 6.3.1]

## Tags

depth, flat module, local homomorphism, tensor product, base change, fibre ring
-/

@[expose] public section

universe u v

open IsLocalRing Pointwise TensorProduct

@[expose] public section

namespace Stacks.Depth.FlatLocalAdditivity

/-! ### Elementary properties of `Module.depth` -/

section Depth

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The depth is `⊤` as soon as the ideal saturates the module. -/
private lemma depth_eq_top_of_smul_top (I : Ideal R) (h : I • (⊤ : Submodule R M) = ⊤) :
    Module.depth R I M = ⊤ := by
  simp only [Module.depth, h, ite_true]

/-- The depth as a supremum of lengths of regular sequences, when the ideal does not saturate. -/
private lemma depth_eq_iSup (I : Ideal R) (h : I • (⊤ : Submodule R M) ≠ ⊤) :
    Module.depth R I M
      = ⨆ rs ∈ {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs},
          (rs.length : ℕ∞) := by
  simp only [Module.depth, h, ite_false]

/-- An element of an ideal multiplies a submodule into the submodule scaled by the ideal. -/
private lemma smul_le_smul_of_mem {I : Ideal R} {f : R} (hf : f ∈ I) (P : Submodule R M) :
    f • P ≤ I • P := by
  rw [← Submodule.ideal_span_singleton_smul]
  refine Submodule.smul_le.mpr fun r hr n hn => ?_
  exact Submodule.smul_mem_smul (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hf) hr) hn

/-- A submodule whose quotient is trivial is everything. -/
private lemma eq_top_of_top_quotient_eq_bot (P : Submodule R M)
    (h : (⊤ : Submodule R (M ⧸ P)) = ⊥) : P = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  have hx : P.mkQ x ∈ (⊥ : Submodule R (M ⧸ P)) := h ▸ Submodule.mem_top
  rw [Submodule.mem_bot, Submodule.mkQ_apply] at hx
  simpa using (Submodule.Quotient.mk_eq_zero P).mp hx

/-- A nonzerodivisor drawn from an ideal that does not saturate `M` is a regular sequence of
length one. -/
private lemma isRegular_singleton {I : Ideal R} (h : I • (⊤ : Submodule R M) ≠ ⊤) {f : R}
    (hf : f ∈ I) (hreg : IsSMulRegular M f) : RingTheory.Sequence.IsRegular M [f] := by
  have hne : f • (⊤ : Submodule R M) ≠ ⊤ := fun hc =>
    h (le_antisymm le_top ((le_of_eq hc.symm).trans
      (smul_le_smul_of_mem hf (⊤ : Submodule R M))))
  have : Nontrivial (QuotSMulTop f M) := Submodule.Quotient.nontrivial_iff.mpr hne
  exact (RingTheory.Sequence.isRegular_cons_iff M f []).mpr ⟨hreg, .nil _ _⟩

/-- Vanishing of the depth means no element of the ideal is a nonzerodivisor. -/
private lemma depth_eq_zero_iff (I : Ideal R) (h : I • (⊤ : Submodule R M) ≠ ⊤) :
    Module.depth R I M = 0 ↔ ∀ f ∈ I, ¬ IsSMulRegular M f := by
  rw [depth_eq_iSup I h, ← le_zero_iff, iSup₂_le_iff]
  constructor
  · intro h0 f hf hreg
    have hmem : [f] ∈ {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs} := by
      refine ⟨?_, isRegular_singleton h hf hreg⟩
      intro r hr
      rw [List.mem_singleton] at hr
      exact hr ▸ hf
    have h1 := h0 [f] hmem
    simp at h1
  · intro hno rs hrs
    obtain ⟨hrs1, hrs2⟩ := hrs
    match rs with
    | [] => simp
    | f :: t =>
      exact absurd ((RingTheory.Sequence.isRegular_cons_iff M f t).mp hrs2).1
        (hno f (hrs1 f (by simp)))

/-- Nonvanishing of the depth produces a nonzerodivisor in the ideal. -/
private lemma exists_isSMulRegular_of_depth_ne_zero (I : Ideal R)
    (h : I • (⊤ : Submodule R M) ≠ ⊤) (h0 : Module.depth R I M ≠ 0) :
    ∃ f ∈ I, IsSMulRegular M f := by
  by_contra hcon
  exact h0 ((depth_eq_zero_iff I h).mpr (by simpa using hcon))

/-- Nakayama: the maximal ideal does not saturate a nonzero finite module. -/
private lemma smul_top_ne_top [IsLocalRing R] [Module.Finite R M] [Nontrivial M] :
    maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := by
  intro h
  refine top_ne_bot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤
    Module.Finite.fg_top (by rw [h]) ?_)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]

/-- Every ideal saturates a trivial module. -/
private lemma smul_top_eq_top_of_subsingleton (I : Ideal R) [Subsingleton M] :
    I • (⊤ : Submodule R M) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  have hx : x = 0 := Subsingleton.elim x 0
  rw [hx]
  exact Submodule.zero_mem _

/-- The depth of a nonzero finite module over a Noetherian ring along an ideal that does not
saturate it is finite. -/
private lemma depth_ne_top [IsNoetherianRing R] [Module.Finite R M] [Nontrivial M] (I : Ideal R)
    (h : I • (⊤ : Submodule R M) ≠ ⊤) : Module.depth R I M ≠ ⊤ := by
  obtain ⟨ss, -, -, hlen⟩ :=
    (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append I M).2 h [] (by simp)
      (.nil R M)
  rw [← hlen]
  exact ENat.natCast_ne_top _

/-- Modulo a nonzerodivisor in `I`, the `I`-depth drops by one. -/
private lemma depth_quotSMulTop_eq_iff [IsNoetherianRing R] [Module.Finite R M] {I : Ideal R}
    {f : R} (hf : f ∈ I) (hreg : IsSMulRegular M f) {a : ℕ} :
    Module.depth R I (QuotSMulTop f M) = a ↔ Module.depth R I M = ((a + 1 : ℕ) : ℕ∞) := by
  rw [← (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append I M).1 f hf hreg,
    Nat.cast_add_one]
  exact (WithTop.add_right_inj ENat.one_ne_top).symm

/-- A module with finite depth has an ideal that does not saturate it. -/
private lemma smul_top_ne_top_of_depth_ne_top {I : Ideal R} (h : Module.depth R I M ≠ ⊤) :
    I • (⊤ : Submodule R M) ≠ ⊤ := fun hc => h (depth_eq_top_of_smul_top I hc)

/-- **The socle of a module of depth zero is nonzero.** Over a Noetherian local ring, if no
element of the maximal ideal is a nonzerodivisor on a finite module `M`, then some nonzero
`z ∈ M` is killed by the whole maximal ideal — that is, `𝔪` is an associated prime of `M`. -/
@[ega "0 16.4.2" "necessity, special case",
  ega "0 16.4.6" "(i)",
  ega "0 17.3.1.2" "special case",
  ega "IV 21.1.10" "partial"]
private lemma exists_ne_zero_maximalIdeal_smul_eq_zero [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] (h : ∀ f ∈ maximalIdeal R, ¬ IsSMulRegular M f) :
    ∃ z : M, z ≠ 0 ∧ ∀ a ∈ maximalIdeal R, a • z = 0 := by
  have hsub : ((maximalIdeal R : Ideal R) : Set R) ⊆
      ⋃ p ∈ associatedPrimes R M, ((p : Ideal R) : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular R M]
    exact fun f hf => h f hf
  obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite (f := fun q : Ideal R => q)
    (associatedPrimes.finite R M) ⊥ ⊥ (fun q hq _ _ => hq.isPrime)).mp hsub
  have hpm : p = maximalIdeal R :=
    ((maximalIdeal.isMaximal R).eq_of_le hp.isPrime.ne_top hle).symm
  obtain ⟨x, hx⟩ := hp.eq_radical_colon
  rw [hpm] at hx
  have hann : ∀ a : R, a ∈ (⊥ : Submodule R M).colon {x} ↔ a • x = 0 := by
    intro a
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  have hx0 : x ≠ 0 := by
    intro hxz
    refine (maximalIdeal.isMaximal R).ne_top ?_
    rw [hx, Ideal.radical_eq_top.mpr ?_]
    refine Ideal.eq_top_iff_one _ |>.mpr ?_
    rw [hann, hxz, smul_zero]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (le_of_eq hx)
    (IsNoetherian.noetherian (maximalIdeal R))
  have hpow : ∀ a ∈ (maximalIdeal R) ^ n, a • x = 0 := fun a ha => (hann a).mp (hn ha)
  clear hx hann hn hsub hpm hle hp h
  induction n generalizing x with
  | zero =>
    exact absurd (by simpa using hpow 1 (by simp)) hx0
  | succ m IH =>
    by_cases hcase : ∀ a ∈ (maximalIdeal R) ^ m, a • x = 0
    · exact IH x hx0 hcase
    · push Not at hcase
      obtain ⟨w, hw, hwy⟩ := hcase
      refine ⟨w • x, hwy, fun a ha => ?_⟩
      rw [smul_smul]
      refine hpow (a * w) ?_
      rw [pow_succ, mul_comm a w]
      exact Ideal.mul_mem_mul hw ha

end Depth

/-! ### The two spellings of the fibre, and quotients of tensor products -/

section Bridges

variable {R S M N : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

omit [IsNoetherianRing R] [IsNoetherianRing S] in
/-- The image of the maximal ideal of `R` in `S` lies in the maximal ideal of `S`. -/
private lemma map_maximalIdeal_le :
    (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
  refine fun hu => ha ?_
  exact IsLocalHom.map_nonunit (f := algebraMap R S) a hu

omit [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)] in
/-- The `S`-submodule `(𝔪_R S) • N` and the `R`-submodule `𝔪_R • N` have the same elements. -/
private lemma restrictScalars_map_smul_top (I : Ideal R) :
    ((I.map (algebraMap R S)) • (⊤ : Submodule S N)).restrictScalars R
      = I • (⊤ : Submodule R N) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hstab : ∀ (s : S) (y : N), y ∈ I • (⊤ : Submodule R N) →
        s • y ∈ I • (⊤ : Submodule R N) := by
      intro s y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro a ha n _
        rw [smul_comm]
        exact Submodule.smul_mem_smul ha trivial
      · intro y z hy hz
        rw [smul_add]
        exact Submodule.add_mem _ hy hz
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro j hj n _
      refine Submodule.span_induction
        (p := fun (j : S) _ => ∀ n : N, j • n ∈ I • (⊤ : Submodule R N)) ?_ ?_ ?_ ?_ hj n
      · intro s hs n
        obtain ⟨a, ha, rfl⟩ := hs
        rw [algebraMap_smul]
        exact Submodule.smul_mem_smul ha trivial
      · intro n; simp
      · intro x y _ _ hx hy n
        rw [add_smul]
        exact Submodule.add_mem _ (hx n) (hy n)
      · intro s x _ hx n
        rw [smul_assoc]
        exact hstab s _ (hx n)
    · intro y z hy hz
      exact Submodule.add_mem _ hy hz
  · refine Submodule.smul_le.mpr fun a ha n _ => ?_
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul (A := S) (r := a)]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) trivial

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- A tensor product with a trivial right factor is trivial. -/
private lemma subsingleton_tensorProduct_right [Subsingleton M] : Subsingleton (N ⊗[R] M) := by
  have h : ∀ w : N ⊗[R] M, w = 0 := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul n m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => by rw [h x, h y]⟩

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- A tensor product with a trivial left factor is trivial. -/
private lemma subsingleton_tensorProduct_left [Subsingleton N] : Subsingleton (N ⊗[R] M) :=
  have := subsingleton_tensorProduct_right (R := R) (M := N) (N := M)
  (TensorProduct.comm R N M).toEquiv.injective.subsingleton

omit [IsNoetherianRing R] [IsNoetherianRing S] [Module R N] [IsScalarTower R S N] in
/-- A finite `S`-module whose fibre over `R` vanishes is zero. -/
private lemma subsingleton_of_subsingleton_fibre [Module.Finite S N]
    [Subsingleton (N ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N)))] :
    Subsingleton N := by
  have htop : ((maximalIdeal R).map (algebraMap R S)) • (⊤ : Submodule S N) = ⊤ :=
    eq_top_of_top_quotient_eq_bot _ (Subsingleton.elim _ _)
  have hbot : (⊤ : Submodule S N) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ ⊤ Module.Finite.fg_top (by rw [htop])
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact map_maximalIdeal_le)
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ (⊥ : Submodule S N) := hbot ▸ Submodule.mem_top
  have hy : y ∈ (⊥ : Submodule S N) := hbot ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at hx hy
  rw [hx, hy]

omit [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)] in
/-- A tensor product of a finite `S`-module with a finite `R`-module is a finite `S`-module. -/
private lemma finite_tensorProduct [Module.Finite R M] [Module.Finite S N] :
    Module.Finite S (N ⊗[R] M) := by
  have : Module.Finite S (S ⊗[R] M) := Module.Finite.base_change R S M
  exact Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange R S S N M)

/-! ### Two spellings of the same quotient -/

omit [IsNoetherianRing S] [IsLocalRing S] in
/-- Multiplication by `f` kills `N/fN`. -/
private lemma smul_mk_eq_zero (f : S) (n : N) :
    f • (Submodule.Quotient.mk n : QuotSMulTop f N) = 0 := by
  rw [← Submodule.Quotient.mk_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_pointwise_smul n f ⊤ trivial)

omit [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)] in
/-- Multiplication by `f` kills `(N/fN) ⊗_R M`. -/
private lemma smul_quotSMulTop_tensor_eq_zero (f : S) (w : (QuotSMulTop f N) ⊗[R] M) :
    f • w = 0 := by
  induction w with
  | tmul x m =>
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective (f • ⊤ : Submodule S N) x
    rw [TensorProduct.smul_tmul', smul_mk_eq_zero, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- Two successive quotients of a module may be taken in either order. -/
private def quotQuotComm (A B : Submodule S N) :
    ((N ⧸ A) ⧸ (B.map A.mkQ)) ≃ₗ[S] ((N ⧸ B) ⧸ (A.map B.mkQ)) :=
  Submodule.quotientQuotientEquivQuotientSup A B ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (sup_comm A B) ≪≫ₗ
      (Submodule.quotientQuotientEquivQuotientSup B A).symm

omit [IsNoetherianRing S] [IsLocalRing S] in
/-- `I • (N/A)` is the image of `I • N`. -/
private lemma smul_top_map_mkQ (I : Ideal S) (A : Submodule S N) :
    (I • (⊤ : Submodule S (N ⧸ A))) = (I • (⊤ : Submodule S N)).map A.mkQ := by
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]

omit [IsNoetherianRing S] [IsLocalRing S] in
/-- `f • (N/A)` is the image of `f • N`. -/
private lemma pointwise_smul_top_map_mkQ (f : S) (A : Submodule S N) :
    (f • (⊤ : Submodule S (N ⧸ A))) = (f • (⊤ : Submodule S N)).map A.mkQ := by
  rw [Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ]

/-- The fibre of `N/fN` along an ideal `I` of `S` is the fibre of `N` modulo `f`: both are `N`
modulo `fN + IN`. -/
private def fibreQuotSMulTopEquiv (I : Ideal S) (f : S) :
    ((QuotSMulTop f N) ⧸ (I • (⊤ : Submodule S (QuotSMulTop f N))))
      ≃ₗ[S] QuotSMulTop f (N ⧸ (I • (⊤ : Submodule S N))) :=
  Submodule.quotEquivOfEq _ _ (smul_top_map_mkQ I _) ≪≫ₗ
    quotQuotComm _ _ ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (pointwise_smul_top_map_mkQ f _).symm

/-- **Right exactness of the tensor product in the left factor.** For `f ∈ S`,
`(N ⊗_R M)/f(N ⊗_R M)` is `(N/fN) ⊗_R M`, as `S`-modules. -/
private noncomputable def quotSMulTopTensorEquiv (f : S) :
    QuotSMulTop f (N ⊗[R] M) ≃ₗ[S] (QuotSMulTop f N) ⊗[R] M :=
  LinearEquiv.ofLinearMap
    (Submodule.liftQ _ (AlgebraTensorModule.map
        (Submodule.mkQ (f • ⊤ : Submodule S N)) (LinearMap.id : M →ₗ[R] M))
      (by
        intro w hw
        obtain ⟨w', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hw
        rw [LinearMap.mem_ker, map_smul, smul_quotSMulTop_tensor_eq_zero]))
    (AlgebraTensorModule.lift (Submodule.liftQ _
        (AlgebraTensorModule.curry
          (Submodule.mkQ (f • ⊤ : Submodule S (N ⊗[R] M)))) (by
        intro n hn
        obtain ⟨n', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hn
        rw [LinearMap.mem_ker]
        refine LinearMap.ext fun m => ?_
        simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
          LinearMap.coe_restrictScalars, Submodule.mkQ_apply, LinearMap.zero_apply]
        rw [← TensorProduct.smul_tmul']
        exact (Submodule.Quotient.mk_eq_zero _).mpr
          (Submodule.smul_mem_pointwise_smul _ f ⊤ trivial))))
    (by
      refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      induction w with
      | tmul x m =>
        obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective (f • ⊤ : Submodule S N) x
        rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (by
      refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (f • ⊤ : Submodule S (N ⊗[R] M)) w
      induction v with
      | tmul n m => rfl
      | add x y hx hy =>
        rw [Submodule.Quotient.mk_add] at *
        rw [map_add, map_add, hx, hy])

omit [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)] in
/-- The submodule of `N ⊗_R M` generated by `N ⊗ fM`, for `f ∈ R`, is `f(N ⊗_R M)`. -/
private lemma range_lTensor_smul_top_subtype (f : R) :
    LinearMap.range (AlgebraTensorModule.lTensor S N
        ((f • ⊤ : Submodule R M).subtype.restrictScalars R))
      = (algebraMap R S f) • (⊤ : Submodule S (N ⊗[R] M)) := by
  refine le_antisymm ?_ ?_
  · rw [LinearMap.range_le_iff_comap]
    refine Submodule.eq_top_iff'.mpr fun w => ?_
    rw [Submodule.mem_comap]
    induction w with
    | tmul n y =>
      obtain ⟨m, -, hm⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp y.2
      have hval : (AlgebraTensorModule.lTensor S N
          ((f • ⊤ : Submodule R M).subtype.restrictScalars R)) (n ⊗ₜ[R] y)
          = (algebraMap R S f) • (n ⊗ₜ[R] m) := by
        rw [algebraMap_smul, ← TensorProduct.tmul_smul, hm,
          AlgebraTensorModule.lTensor_tmul]
        rfl
      rw [hval]
      exact Submodule.smul_mem_pointwise_smul _ _ _ trivial
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · have key : ∀ w : N ⊗[R] M, (algebraMap R S f) • w ∈
        LinearMap.range (AlgebraTensorModule.lTensor S N
          ((f • ⊤ : Submodule R M).subtype.restrictScalars R)) := by
      intro w
      induction w with
      | tmul n m =>
        refine ⟨n ⊗ₜ[R] ⟨f • m, Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top⟩, ?_⟩
        rw [AlgebraTensorModule.lTensor_tmul, algebraMap_smul, ← TensorProduct.tmul_smul]
        rfl
      | add u v hu hv => rw [smul_add]; exact Submodule.add_mem _ hu hv
    intro x hx
    obtain ⟨w, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact key w

/-- **Right exactness of the tensor product in the right factor.** For `f ∈ R`,
`N ⊗_R (M/fM)` is `(N ⊗_R M)/f(N ⊗_R M)`, as `S`-modules. -/
private noncomputable def tensorQuotSMulTopEquiv (f : R) :
    N ⊗[R] (QuotSMulTop f M) ≃ₗ[S] QuotSMulTop (algebraMap R S f) (N ⊗[R] M) :=
  AlgebraTensorModule.tensorQuotientEquiv S R N (f • ⊤ : Submodule R M) ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (range_lTensor_smul_top_subtype f)

/-! ### Nonzerodivisors and depth on tensor products -/

omit [IsNoetherianRing R] in
/-- A nonzerodivisor `f ∈ S` on the fibre `N/𝔪_R N` is a nonzerodivisor on `N`, and `N/fN` is
again flat over `R`. -/
private theorem isSMulRegular_and_flat_quotSMulTop [Module.Finite S N] [Module.Flat R N] (f : S)
    (hf : IsSMulRegular
      (N ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N))) f) :
    IsSMulRegular N f ∧ Module.Flat R (QuotSMulTop f N) := by
  have hsub : maximalIdeal R • (⊤ : Submodule R N)
      = (((maximalIdeal R).map (algebraMap R S)) • (⊤ : Submodule S N)).restrictScalars R :=
    (restrictScalars_map_smul_top _).symm
  set e : (N ⧸ (maximalIdeal R • (⊤ : Submodule R N)))
      ≃ₗ[R] N ⧸ (((maximalIdeal R).map (algebraMap R S)) • (⊤ : Submodule S N)) :=
    Submodule.quotEquivOfEq _ _ hsub ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv R _ with he
  have hcomm : ∀ x, e (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R N))
      (maximalIdeal R • (⊤ : Submodule R N)) ((LinearMap.lsmul S N f).restrictScalars R)
      (Submodule.smul_top_le_comap_smul_top _ _) x) = f • e x := by
    intro x
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  have hmapQ : Function.Injective (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R N))
      (maximalIdeal R • (⊤ : Submodule R N)) ((LinearMap.lsmul S N f).restrictScalars R)
      (Submodule.smul_top_le_comap_smul_top _ _)) := by
    intro x y hxy
    refine e.injective (hf ?_)
    change f • e x = f • e y
    rw [← hcomm, ← hcomm, hxy]
  obtain ⟨hinj, hflat⟩ :=
    Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
      (S := S) ((LinearMap.lsmul S N f).restrictScalars R) hmapQ
  refine ⟨hinj, ?_⟩
  have hrange : LinearMap.range ((LinearMap.lsmul S N f).restrictScalars R)
      = (f • (⊤ : Submodule S N)).restrictScalars R := by
    refine Submodule.ext fun x => ?_
    simp only [LinearMap.mem_range, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply,
      Submodule.restrictScalars_mem, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨n, h⟩ => ⟨n, trivial, h⟩, fun ⟨n, _, h⟩ => ⟨n, h⟩⟩
  exact Module.Flat.of_linearEquiv
    (Submodule.quotEquivOfEq _ _ hrange ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv R _).symm

omit [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)] in
/-- If `f ∈ S` is a nonzerodivisor on `N` and `N/fN` is flat over `R`, then `f` is a
nonzerodivisor on `N ⊗_R M` for every `R`-module `M`. -/
private theorem isSMulRegular_tensorProduct_left (f : S)
    (hf : IsSMulRegular N f) (hflat : Module.Flat R (QuotSMulTop f N)) :
    IsSMulRegular (N ⊗[R] M) f := by
  have hexact : Function.Exact ((LinearMap.lsmul S N f).restrictScalars R)
      ((Submodule.mkQ (f • ⊤ : Submodule S N)).restrictScalars R) := by
    intro x
    simp only [LinearMap.coe_restrictScalars, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists, Set.mem_range,
      LinearMap.lsmul_apply]
    exact ⟨fun ⟨y, _, h⟩ => ⟨y, h⟩, fun ⟨y, h⟩ => ⟨y, trivial, h⟩⟩
  have hsurj : Function.Surjective
      ((Submodule.mkQ (f • ⊤ : Submodule S N)).restrictScalars R) :=
    Submodule.mkQ_surjective (f • ⊤ : Submodule S N)
  have hinj : Function.Injective (((LinearMap.lsmul S N f).restrictScalars R).lTensor M) :=
    LinearMap.lTensor_injective_of_exact_of_flat _ hsurj
      ((LinearMap.lsmul S N f).restrictScalars R) hf hexact M
  have hinj' : Function.Injective (((LinearMap.lsmul S N f).restrictScalars R).rTensor M) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj (M := M)
      (f := (LinearMap.lsmul S N f).restrictScalars R)).1 hinj
  have key : ∀ w : N ⊗[R] M,
      f • w = ((LinearMap.lsmul S N f).restrictScalars R).rTensor M w := by
    intro w
    induction w with
    | tmul n m => rw [LinearMap.rTensor_tmul]; rfl
    | add x y hx hy => rw [smul_add, map_add, hx, hy]
  intro x y hxy
  exact hinj' (by rw [← key, ← key]; exact hxy)

omit [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)] in
/-- If `f ∈ R` is a nonzerodivisor on `M` and `N` is flat over `R`, then the image of `f` in `S`
is a nonzerodivisor on `N ⊗_R M`. -/
private theorem isSMulRegular_tensorProduct_right [Module.Flat R N] (f : R)
    (hf : IsSMulRegular M f) : IsSMulRegular (N ⊗[R] M) (algebraMap R S f) := by
  have key : ∀ w : N ⊗[R] M, (algebraMap R S f) • w = (LinearMap.lsmul R M f).lTensor N w := by
    intro w
    induction w with
    | tmul n m =>
      rw [algebraMap_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
        LinearMap.lTensor_tmul, LinearMap.lsmul_apply]
    | add x y hx hy => rw [smul_add, map_add, hx, hy]
  have hinj : Function.Injective ((LinearMap.lsmul R M f).lTensor N) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hf
  intro x y hxy
  exact hinj (by rw [← key, ← key]; exact hxy)

omit [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R]
  [IsLocalHom (algebraMap R S)] in
/-- For `f ∈ S`, the depth of `(N ⊗_R M)/f(N ⊗_R M)` is that of `(N/fN) ⊗_R M`. -/
private theorem depth_quotSMulTop_tensorProduct_left (f : S) :
    Module.depth S (maximalIdeal S) (QuotSMulTop f (N ⊗[R] M))
      = Module.depth S (maximalIdeal S) ((QuotSMulTop f N) ⊗[R] M) :=
  Module.depth_eq_depth_of_linearEquiv _ (quotSMulTopTensorEquiv f)

omit [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R]
  [IsLocalHom (algebraMap R S)] in
/-- For `f ∈ R`, the depth of `(N ⊗_R M)/f(N ⊗_R M)` is that of `N ⊗_R (M/fM)`. -/
private theorem depth_quotSMulTop_tensorProduct_right (f : R) :
    Module.depth S (maximalIdeal S) (QuotSMulTop (algebraMap R S f) (N ⊗[R] M))
      = Module.depth S (maximalIdeal S) (N ⊗[R] (QuotSMulTop f M)) :=
  (Module.depth_eq_depth_of_linearEquiv _ (tensorQuotSMulTopEquiv f)).symm

omit [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] [Module R N]
  [IsScalarTower R S N] in
/-- The fibre of `N/fN` and the fibre of `N` modulo `f` have the same depth, both being `N`
modulo `fN + 𝔪_R N`. -/
private theorem depth_fibre_quotSMulTop (f : S) :
    Module.depth S (maximalIdeal S)
        ((QuotSMulTop f N) ⧸ ((maximalIdeal R).map (algebraMap R S) •
          (⊤ : Submodule S (QuotSMulTop f N))))
      = Module.depth S (maximalIdeal S)
        (QuotSMulTop f (N ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N)))) :=
  Module.depth_eq_depth_of_linearEquiv _ (fibreQuotSMulTopEquiv _ f)

omit [IsLocalHom (algebraMap R S)] in
/-- If `M` has depth zero over `R` and the fibre `N/𝔪_R N` has depth zero over `S`, then
`N ⊗_R M` has depth zero over `S`. -/
private theorem depth_tensorProduct_eq_zero [Module.Finite R M] [Module.Finite S N]
    [Module.Flat R N] (hM : Module.depth R (maximalIdeal R) M = 0)
    (hN : Module.depth S (maximalIdeal S)
      (N ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N))) = 0) :
    Module.depth S (maximalIdeal S) (N ⊗[R] M) = 0 := by
  have hMtop := smul_top_ne_top_of_depth_ne_top (hM ▸ ENat.zero_ne_top)
  have hNtop := smul_top_ne_top_of_depth_ne_top (hN ▸ ENat.zero_ne_top)
  obtain ⟨z, hz0, hz⟩ :=
    exists_ne_zero_maximalIdeal_smul_eq_zero ((depth_eq_zero_iff _ hMtop).mp hM)
  obtain ⟨y, hy0, hy⟩ :=
    exists_ne_zero_maximalIdeal_smul_eq_zero ((depth_eq_zero_iff _ hNtop).mp hN)
  set ι : (R ⧸ (maximalIdeal R : Submodule R R)) →ₗ[R] M :=
    Submodule.liftQ _ (LinearMap.toSpanSingleton R M z)
      (fun a ha => by
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
        exact hz a ha) with hιdef
  have hιinj : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).mpr fun x hx => ?_
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    by_contra hrn
    have hu : IsUnit r := by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hrn
    have hrz : r • z = 0 := hx
    exact hz0 (hu.isSMulRegular M (by simpa using hrz))
  set ψ : N →ₗ[S] N ⊗[R] M :=
    { toFun := fun n => n ⊗ₜ[R] z
      map_add' := fun a b => TensorProduct.add_tmul a b z
      map_smul' := fun s n => (TensorProduct.smul_tmul' s n z).symm } with hψdef
  have hker : ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N))
      ≤ LinearMap.ker ψ := by
    intro x hx
    have hx' : x ∈ maximalIdeal R • (⊤ : Submodule R N) := by
      rw [← restrictScalars_map_smul_top (R := R) (S := S) (N := N) (maximalIdeal R)]
      exact hx
    refine Submodule.smul_induction_on hx' ?_ ?_
    · intro a ha n _
      rw [LinearMap.mem_ker]
      change (a • n) ⊗ₜ[R] z = 0
      rw [TensorProduct.smul_tmul, hz a ha, TensorProduct.tmul_zero]
    · intro u v hu hv
      exact Submodule.add_mem _ hu hv
  have hψinj : Function.Injective (Submodule.liftQ _ ψ hker) := by
    refine (injective_iff_map_eq_zero _).mpr fun q hq => ?_
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hnz : n ⊗ₜ[R] z = 0 := hq
    have h1 : (ι.lTensor N)
        (n ⊗ₜ[R] (Submodule.Quotient.mk (1 : R) :
          R ⧸ (maximalIdeal R : Submodule R R))) = 0 := by
      rw [LinearMap.lTensor_tmul]
      change n ⊗ₜ[R] (LinearMap.toSpanSingleton R M z) (1 : R) = 0
      rw [LinearMap.toSpanSingleton_apply, one_smul]
      exact hnz
    have h2 : n ⊗ₜ[R] (Submodule.Quotient.mk (1 : R) :
        R ⧸ (maximalIdeal R : Submodule R R)) = 0 :=
      Module.Flat.lTensor_preserves_injective_linearMap ι hιinj (by rw [h1, map_zero])
    have h3 : (Submodule.Quotient.mk n :
        N ⧸ (maximalIdeal R • (⊤ : Submodule R N))) = 0 := by
      have hzero := congrArg (TensorProduct.tensorQuotEquivQuotSMul N (maximalIdeal R)) h2
      rw [map_zero] at hzero
      have key := TensorProduct.tensorQuotEquivQuotSMul_tmul_mk (M := N) (maximalIdeal R) n 1
      rw [one_smul] at key
      exact key.symm.trans hzero
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    rw [← Submodule.restrictScalars_mem (S := R), restrictScalars_map_smul_top]
    exact (Submodule.Quotient.mk_eq_zero _).mp h3
  have hw0 : (Submodule.liftQ _ ψ hker) y ≠ 0 := fun hc => hy0 (hψinj (by rw [hc, map_zero]))
  have hfin := finite_tensorProduct (R := R) (S := S) (M := M) (N := N)
  have hnt : Nontrivial (N ⊗[R] M) := ⟨⟨_, 0, hw0⟩⟩
  refine (depth_eq_zero_iff (maximalIdeal S) smul_top_ne_top).mpr fun g hg hreg => ?_
  have hgw : g • (Submodule.liftQ _ ψ hker) y = 0 := by
    rw [← LinearMap.map_smul, hy g hg, map_zero]
  exact hw0 (hreg (by simpa using hgw))

end Bridges

/-! ### The depth formula -/

section Main

variable {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- The depth formula for a flat base change, when its right hand side is a natural number
`n`. -/
@[ega "IV 6.3.1" "special case"]
private theorem depth_tensorProduct_aux (n : ℕ) :
    ∀ (M : Type u) (N : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Finite S N]
      [Module.Flat R N],
      Module.depth R (maximalIdeal R) M + Module.depth S (maximalIdeal S)
          (N ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N))) = (n : ℕ∞) →
        Module.depth S (maximalIdeal S) (N ⊗[R] M) = (n : ℕ∞) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro M N _ _ _ _ _ _ _ _ _ hn
  have := finite_tensorProduct (R := R) (S := S) (M := M) (N := N)
  have hne : Module.depth R (maximalIdeal R) M + Module.depth S (maximalIdeal S)
      (N ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N))) ≠ ⊤ :=
    hn ▸ ENat.natCast_ne_top n
  rw [Ne, ENat.add_eq_top, not_or] at hne
  obtain ⟨hane, hbne⟩ := hne
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hane
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hbne
  rw [← ha, ← hb] at hn
  have hab : a + b = n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · have h0 : Module.depth S (maximalIdeal S) (N ⊗[R] M) = 0 :=
        depth_tensorProduct_eq_zero (by rw [← ha, ha0]; rfl) (by rw [← hb, hb0]; rfl)
      rw [h0, show n = 0 from by omega]
      simp
    · obtain ⟨f, hfmem, hfreg⟩ := exists_isSMulRegular_of_depth_ne_zero (maximalIdeal R)
        (smul_top_ne_top_of_depth_ne_top hane) (by rw [← ha]; exact_mod_cast hapos.ne')
      have hc := (depth_quotSMulTop_eq_iff (M := M) hfmem hfreg (a := a - 1)).mpr
        (by rw [← ha, Nat.sub_add_cancel hapos])
      have h2 : Module.depth S (maximalIdeal S) (N ⊗[R] (QuotSMulTop f M))
          = ((a - 1 : ℕ) : ℕ∞) := by
        refine IH (a - 1) (by omega) (QuotSMulTop f M) N ?_
        rw [hc, ← hb, hb0, Nat.cast_zero, add_zero]
      rw [← hab, hb0, add_zero, ← Nat.sub_add_cancel hapos]
      refine (depth_quotSMulTop_eq_iff (M := N ⊗[R] M) (map_maximalIdeal_le
        (Ideal.mem_map_of_mem _ hfmem)) (isSMulRegular_tensorProduct_right f hfreg)).mp ?_
      rw [depth_quotSMulTop_tensorProduct_right f, h2]
  · obtain ⟨f, hfmem, hfreg⟩ := exists_isSMulRegular_of_depth_ne_zero (maximalIdeal S)
      (smul_top_ne_top_of_depth_ne_top hbne) (by rw [← hb]; exact_mod_cast hbpos.ne')
    have hc := (depth_quotSMulTop_eq_iff hfmem hfreg (a := b - 1)).mpr
      (by rw [← hb, Nat.sub_add_cancel hbpos])
    obtain ⟨hfregN, hflat⟩ := isSMulRegular_and_flat_quotSMulTop f hfreg
    have h2 : Module.depth S (maximalIdeal S) ((QuotSMulTop f N) ⊗[R] M)
        = ((a + (b - 1) : ℕ) : ℕ∞) := by
      refine IH (a + (b - 1)) (by omega) M (QuotSMulTop f N) ?_
      rw [depth_fibre_quotSMulTop f, hc, ← ha, Nat.cast_add]
    rw [← hab, show a + b = a + (b - 1) + 1 by omega]
    refine (depth_quotSMulTop_eq_iff (M := N ⊗[R] M) hfmem
      (isSMulRegular_tensorProduct_left f hfregN hflat)).mp ?_
    rw [depth_quotSMulTop_tensorProduct_left f, h2]

end Main

open Module in
/-- For a local homomorphism `R → S` of Noetherian local rings, a finite `R`-module `M` and a
finite `S`-module `N` flat over `R`, `depth_S(N ⊗_R M) = depth_R(M) + depth_S(N/𝔪_R N)`. -/
public theorem solution {R S M N : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Finite S N]
    [Module.Flat R N] :
    depth S (maximalIdeal S) (N ⊗[R] M) = depth R (maximalIdeal R) M +
      depth S (maximalIdeal S)
        (N ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N))) := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · have : Subsingleton (N ⊗[R] M) := subsingleton_tensorProduct_right
    rw [depth_eq_top_of_smul_top (R := S) (M := N ⊗[R] M) _
        (smul_top_eq_top_of_subsingleton _),
      depth_eq_top_of_smul_top (R := R) (M := M) _ (smul_top_eq_top_of_subsingleton _), top_add]
  · rcases subsingleton_or_nontrivial
      (N ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N))) with hQ | hQ
    · have : Subsingleton N := subsingleton_of_subsingleton_fibre (R := R) (S := S)
      have : Subsingleton (N ⊗[R] M) := subsingleton_tensorProduct_left
      rw [depth_eq_top_of_smul_top (R := S) (M := N ⊗[R] M) _
          (smul_top_eq_top_of_subsingleton _),
        depth_eq_top_of_smul_top (R := S)
          (M := N ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N))) _
          (smul_top_eq_top_of_subsingleton _), add_top]
    · have hane : depth R (maximalIdeal R) M ≠ ⊤ := depth_ne_top _ smul_top_ne_top
      have hbne : depth S (maximalIdeal S)
          (N ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N))) ≠ ⊤ :=
        depth_ne_top _ smul_top_ne_top
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hane
      obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hbne
      rw [← ha, ← hb,
        depth_tensorProduct_aux (a + b) M N (by rw [← ha, ← hb]; push_cast; ring)]
      push_cast
      ring

end Stacks.Depth.FlatLocalAdditivity

end

open IsLocalRing TensorProduct

@[expose] public section

namespace Module

/-- **Depth is additive along a flat local homomorphism.** Let `R → S` be a local homomorphism
of Noetherian local rings, let `M` be a finite `R`-module and let `N` be a finite `S`-module
flat over `R`. Then `depth_S(N ⊗_R M) = depth_R(M) + depth_S(N/𝔪_R N)`. -/
@[stacks 0338 "The fibre `N/𝔪_R N` has its depth taken over `S` along `𝔪_S` rather than over \
  `S/𝔪_R S`, which is the same value, and the tensor product is written with `N` on the left.", ega
    "IV 6.3.1", ega "IV 6.3.4" "more general", sga "2 III 2.11" "special case"]
public theorem depth_tensorProduct_of_flat {R S M N : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Finite S N]
    [Module.Flat R N] :
    depth S (maximalIdeal S) (N ⊗[R] M) = depth R (maximalIdeal R) M +
      depth S (maximalIdeal S)
        (N ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N))) :=
  Stacks.Depth.FlatLocalAdditivity.solution

end Module

end

open IsLocalRing RingTheory.Sequence TensorProduct

@[expose] public section

namespace Stacks.Depth.FlatLocalFibreRing

/-- An ideal `J` of a commutative ring `A` acting on `A` is `J` again, so the `I`-depth of the
`A`-module `A ⧸ J • ⊤` is the `I`-depth of the quotient ring `A ⧸ J`. -/
public lemma depth_quotient_smul_top {A : Type*} [CommRing A] (I J : Ideal A) :
    Module.depth A I (A ⧸ (J • (⊤ : Submodule A A))) = Module.depth A I (A ⧸ J) :=
  Module.depth_eq_depth_of_linearEquiv I (Submodule.quotEquivOfEq _ _ (by simp))

/-- The source of a flat local homomorphism onto a Noetherian local ring is Noetherian. -/
@[ega "0 6.5.2" "special case", ega "0 6.6.2" "special case"]
public lemma isNoetherianRing_of_flat_of_isLocalHom (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] :
    IsNoetherianRing R :=
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat (A := S)
    (isNoetherian_of_linearEquiv (AlgebraTensorModule.rid R S S).symm)

/-- For a flat local homomorphism `R → S` of local rings with `S` Noetherian,
`depth_{𝔪_S}(S) = depth_{𝔪_R}(R) + depth_{𝔪_S}(S/𝔪_R S)`. -/
public theorem solution (R S : Type*)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] :
    Module.depth S (IsLocalRing.maximalIdeal S) S =
      Module.depth R (IsLocalRing.maximalIdeal R) R +
        Module.depth S (IsLocalRing.maximalIdeal S)
          (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  have := isNoetherianRing_of_flat_of_isLocalHom R S
  rw [Module.depth_eq_depth_of_linearEquiv (maximalIdeal S) (AlgebraTensorModule.rid R S S).symm,
    Module.depth_tensorProduct_of_flat (M := R), depth_quotient_smul_top]

end Stacks.Depth.FlatLocalFibreRing

end

@[expose] public section

namespace Module

/-- **Depth is additive along a flat local homomorphism.** Let `R → S` be a flat local
homomorphism of local rings with `S` Noetherian, with maximal ideals `𝔪_R` and `𝔪_S`. Then
`depth_{𝔪_S}(S) = depth_{𝔪_R}(R) + depth_{𝔪_S}(S/𝔪_R S)`, where `𝔪_R S` is the ideal of `S`
generated by the image of `𝔪_R`. The depth of the fibre `S/𝔪_R S` is taken over `S` along `𝔪_S`,
which is its depth as a local ring in its own right. -/
@[stacks 0337 "Stated for `Module.depth` along the maximal ideals (Tag 00LI), with the fibre \
  ring spelled as the `S`-module `S ⧸ 𝔪_R S`, of the same depth as the local ring `S/𝔪_R S`, \
  and with `IsNoetherianRing R` dropped, being a consequence of faithful flatness. See the \
  module docstring.", ega "IV 6.3.1" "case M = R, N = S", sga "2 III 2.11" "M = A"]
public theorem depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal (R S : Type*)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] :
    depth S (IsLocalRing.maximalIdeal S) S =
      depth R (IsLocalRing.maximalIdeal R) R +
        depth S (IsLocalRing.maximalIdeal S)
          (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
  Stacks.Depth.FlatLocalFibreRing.solution R S

end Module

end
