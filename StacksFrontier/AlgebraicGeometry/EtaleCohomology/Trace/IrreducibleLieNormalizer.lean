module

public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Algebra.Lie.Normalizer
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Semisimple.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The normalizer of an irreducible linear Lie algebra

Let `V` be a finite-dimensional vector space over an algebraically closed field `K` of
characteristic zero and let `𝔤 ⊆ 𝔤𝔩(V)` be a Lie subalgebra acting irreducibly on `V`.  Then the
normalizer of `𝔤` in `𝔤𝔩(V)` is `𝔤 + K · 1`: every endomorphism `n` with `[n, 𝔤] ⊆ 𝔤` is an
element of `𝔤` plus a scalar.

This is the Lie-algebra form of Deligne, Weil II 1.3.9 (Kedlaya, *Fourier transforms and p-adic
Weil II*, Proposition 6.1.3).

## Main results

* `Stacks.EtaleCohomology.isSolvable_traceRadical`: the radical of the trace form is solvable.
* `Stacks.EtaleCohomology.traceRadical_eq_bot`: for an irreducible `𝔤` it is zero.
* `Stacks.EtaleCohomology.exists_sub_smul_one_mem_of_mem_normalizer`: the normalizer of `𝔤` is
  `𝔤 + K · 1`.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.3.9.
* K. Kedlaya, *Fourier transforms and p-adic "Weil II"*, Compos. Math. 142 (2006),
  Proposition 6.1.3.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

namespace Stacks.EtaleCohomology

open LieModule LieAlgebra Module

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The radical `𝔤 ∩ 𝔤^⊥` of the trace form `(x, y) ↦ tr(xy)` on a linear Lie algebra `𝔤`. -/
def traceRadical (g : LieSubalgebra K (Module.End K V)) : LieIdeal K g :=
  LieAlgebra.InvariantForm.orthogonal (traceForm K g V) (traceForm_lieInvariant K g V) ⊤

omit [CharZero K] [FiniteDimensional K V] in
/-- An element `a` of `𝔤` lies in the radical of the trace form if and only if `tr(y a) = 0` for
every `y ∈ 𝔤`. -/
theorem mem_traceRadical {g : LieSubalgebra K (Module.End K V)} {a : g} :
    a ∈ traceRadical g ↔ ∀ y : g, LinearMap.trace K V ((y : Module.End K V) * a) = 0 := by
  rw [traceRadical, LieAlgebra.InvariantForm.mem_orthogonal]
  exact ⟨fun h y => h y (LieSubmodule.mem_top y), fun h y _ => h y⟩

/-- **Cartan's criterion for the trace form**: the radical of the trace form of a linear Lie
algebra is solvable. -/
theorem isSolvable_traceRadical (g : LieSubalgebra K (Module.End K V)) :
    IsSolvable (traceRadical g) := by
  set I := traceRadical g
  set DI : LieIdeal K g := ⁅I, I⁆
  set DDI : LieIdeal K g := ⁅DI, DI⁆
  have tf_eq_zero : traceForm K DI V = 0 := by
    ext ⟨x, hx⟩ ⟨y, hy⟩
    show LinearMap.trace K V ((x : Module.End K V) * y) = 0
    exact mem_traceRadical.mp (LieSubmodule.lie_le_left I I hy) x
  have module_nilp : LieModule.IsNilpotent (derivedSeries K DI 1) V :=
    LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero tf_eq_zero
  have ring_nilp : LieRing.IsNilpotent DDI := by
    rw [LieAlgebra.isNilpotent_iff_forall (R := K)]
    rintro ⟨x, hx⟩
    apply LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad (DDI : LieSubalgebra K g) (x := ⟨x, hx⟩)
    apply LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad g (x := x)
    apply LieAlgebra.ad_nilpotent_of_nilpotent
    exact (LieModule.isNilpotent_iff_forall' (R := K)).mp module_nilp
      ⟨⟨x, LieSubmodule.lie_le_left DI DI hx⟩, by
        rwa [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap, LieIdeal.mem_comap]⟩
  obtain ⟨k, hk⟩ := IsSolvable.solvable K DDI
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hk
  refine IsSolvable.mk (k := k + 2) ((LieIdeal.derivedSeries_eq_bot_iff I (k + 2)).mpr ?_)
  rwa [derivedSeriesOfIdeal_add, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ,
    derivedSeriesOfIdeal_zero]

variable [IsAlgClosed K]

/-- For a Lie algebra acting irreducibly, the trace form is nondegenerate. -/
theorem traceRadical_eq_bot (g : LieSubalgebra K (Module.End K V))
    [IsIrreducible K g V] : traceRadical g = ⊥ := by
  have _i := nontrivial_of_isIrreducible K g V
  have hsolv := isSolvable_traceRadical g
  have hrad : traceRadical g ≤ radical K g := (LieIdeal.solvable_iff_le_radical K g _).mp hsolv
  obtain ⟨hcent, hscalar⟩ := hasCentralRadical_and_of_isIrreducible_of_isFaithful K g V
  rw [LieSubmodule.eq_bot_iff]
  intro a ha
  have hz : a ∈ center K g := by
    rw [← (hasCentralRadical_iff K g).mp hcent]
    exact hrad ha
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((hscalar a).mp hz)
  have ha' : (a : Module.End K V) = c • 1 := hc.symm
  have htr := mem_traceRadical.mp ha a
  rw [ha', smul_mul_smul, one_mul, map_smul, LinearMap.trace_one, smul_eq_mul,
    mul_eq_zero] at htr
  have hdim : (finrank K V : K) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  have hc0 : c = 0 := by
    rcases htr with h | h
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp (by rw [sq]; exact h)
    · exact absurd h hdim
  exact Subtype.ext (by rw [ha', hc0, zero_smul]; rfl)

/-- An element of an irreducible linear Lie algebra whose trace pairing with `𝔤` vanishes is
zero. -/
private theorem eq_zero_of_forall_trace_mul_eq_zero (g : LieSubalgebra K (Module.End K V))
    [IsIrreducible K g V] {a : g}
    (h : ∀ y : g, LinearMap.trace K V ((y : Module.End K V) * a) = 0) : a = 0 := by
  have : a ∈ traceRadical g := mem_traceRadical.mpr h
  rwa [traceRadical_eq_bot g] at this

omit [CharZero K] in
/-- **Schur's lemma** for a linear Lie algebra acting irreducibly: an endomorphism commuting with
it is a scalar. -/
theorem exists_eq_smul_one_of_forall_commute (g : LieSubalgebra K (Module.End K V))
    [IsIrreducible K g V] {b : Module.End K V} (hb : ∀ x ∈ g, Commute b x) :
    ∃ c : K, b = c • 1 := by
  have _i := nontrivial_of_isIrreducible K g V
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue b
  let W : LieSubmodule K g V :=
    { toSubmodule := LinearMap.ker (b - c • 1)
      lie_mem := by
        intro x v hv
        have hv' : (b - c • 1) v = 0 := hv
        show (b - c • 1) ((x : Module.End K V) v) = 0
        have e : (b - c • 1) * (x : Module.End K V) = (x : Module.End K V) * (b - c • 1) := by
          rw [sub_mul, mul_sub, (hb x x.2).eq, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
        rw [← Module.End.mul_apply, e, Module.End.mul_apply, hv', map_zero] }
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hW : Nontrivial W := by
    refine nontrivial_of_ne ⟨v, ?_⟩ 0 ?_
    · show v ∈ LinearMap.ker (b - c • 1)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hv.apply_eq_smul, LinearMap.smul_apply,
        Module.End.one_apply, sub_self]
    · intro h
      exact hv.2 (congrArg Subtype.val h)
  have htop : W = ⊤ := W.eq_top_of_isIrreducible K g V
  refine ⟨c, LinearMap.ext fun w => ?_⟩
  have hw : w ∈ W := htop ▸ LieSubmodule.mem_top w
  have hw' : (b - c • 1) w = 0 := hw
  rwa [LinearMap.sub_apply, sub_eq_zero] at hw'

/-- **The normalizer of an irreducible linear Lie algebra** (the Lie-algebra form of Weil II
1.3.9).  If `𝔤 ⊆ 𝔤𝔩(V)` acts irreducibly on `V`, over an algebraically closed field of
characteristic zero, then every `n` normalizing `𝔤` is an element of `𝔤` plus a scalar. -/
theorem exists_sub_smul_one_mem_of_mem_normalizer (g : LieSubalgebra K (Module.End K V))
    [IsIrreducible K g V] {n : Module.End K V} (hn : n ∈ g.normalizer) :
    ∃ c : K, n - c • 1 ∈ g := by
  rw [LieSubalgebra.mem_normalizer_iff] at hn
  have hnd : (traceForm K g V).Nondegenerate :=
    ⟨fun a ha => eq_zero_of_forall_trace_mul_eq_zero g fun y => by
      rw [LinearMap.trace_mul_comm]; exact ha y,
     fun a ha => eq_zero_of_forall_trace_mul_eq_zero g ha⟩
  let φ : Module.Dual K g :=
    (LinearMap.trace K V ∘ₗ LinearMap.mul K (Module.End K V) n) ∘ₗ g.toSubmodule.subtype
  set a : g := ((traceForm K g V).toDual hnd).symm φ
  have ha : ∀ y : g, LinearMap.trace K V ((a : Module.End K V) * y) =
      LinearMap.trace K V (n * y) := fun y =>
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) φ y
  set b := n - (a : Module.End K V)
  have hbperp : ∀ y : g, LinearMap.trace K V (b * y) = 0 := fun y => by
    rw [sub_mul, map_sub, ha, sub_self]
  have hbnorm : ∀ y ∈ g, ⁅b, y⁆ ∈ g := fun y hy => by
    rw [sub_lie]
    exact g.sub_mem (hn y hy) (g.lie_mem a.2 hy)
  have hcomm : ∀ x ∈ g, Commute b x := by
    intro x hx
    have hc : (⟨⁅b, x⁆, hbnorm x hx⟩ : g) = 0 := by
      refine eq_zero_of_forall_trace_mul_eq_zero g fun y => ?_
      show LinearMap.trace K V ((y : Module.End K V) * (b * x - x * b)) = 0
      rw [LinearMap.trace_mul_comm, sub_mul, map_sub, mul_assoc, mul_assoc,
        LinearMap.trace_mul_comm K x, mul_assoc, ← map_sub, ← mul_sub]
      exact hbperp ⟨⁅x, (y : Module.End K V)⁆, g.lie_mem hx y.2⟩
    have hc' : ⁅b, x⁆ = 0 := congrArg Subtype.val hc
    rwa [LieRing.of_associative_ring_bracket, sub_eq_zero] at hc'
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_forall_commute g hcomm
  refine ⟨c, ?_⟩
  rw [← hc]
  simp [b]

end Stacks.EtaleCohomology
