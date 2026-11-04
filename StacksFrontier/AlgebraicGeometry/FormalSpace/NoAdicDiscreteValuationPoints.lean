module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap

/-!
# An adic ring admitting no adic map to a complete discrete valuation ring

Let `k` be a field. The ring `⋃_{n ≥ 1} k[t^{1/n}]` of polynomials in all the fractional powers
of `t` is the monoid algebra `k[ℚ≥0]` of the additive monoid of nonnegative rationals, the basis
element at `q` being `t^q`; let `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧` be its `t`-adic completion. The
image of `t` in `A` is nonzero and has an `n`-th root for every `n ≥ 1`.

**Stacks 0AQZ** observes that there are no adic morphisms `Spf R ⟶ Spf A` with `R` a complete
discrete valuation ring, so that the lifting condition of **Stacks 0AQQ** holds vacuously for
every morphism `X ⟶ Spf A`, even for `X = ∅`, although `A` is a domain in which `t` is nonzero
and so ought to carry a rig-point. A morphism `Spf R ⟶ Spf A` of affine formal algebraic spaces
is `Spf` of a continuous ring map `A → R` (Stacks 0AN0), and such a morphism is adic exactly
when that ring map is adic in the sense of `RingHom.IsAdic` (Stacks 0GBR); the assertion is
therefore that no ring map `A → R` is adic, and that is what is proved here.

The obstruction is divisibility in the value group. An adic map `φ : A → R` carries the ideal
of definition `(t)` of `A` into the maximal ideal of `R` and some power of that maximal ideal
back into `(φ t)`, so `φ t` is neither zero nor a unit; but `t = s ^ n` forces the additive
valuation of `φ t` to be divisible by every `n ≥ 1`, hence to be `0` or `⊤`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.FractionalPowers.Completion`: the ring
  `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧` of **Stacks 0AQZ**.
* `AlgebraicGeometry.FormalSpace.FractionalPowers.generator`: the element `t` of `k[ℚ≥0]`.
* `AlgebraicGeometry.FormalSpace.FractionalPowers.completionGenerator`: its image `t` in `A`.

## Main results

* `AlgebraicGeometry.FormalSpace.FractionalPowers.not_isAdic_toDiscreteValuationRing`:
  **Stacks 0AQZ**, no ring map from `A` to a complete discrete valuation ring is adic.
* `AlgebraicGeometry.FormalSpace.not_isAdic_of_forall_exists_pow`: the same conclusion for any
  topological ring whose topology is the adic topology of a principal ideal whose generator
  admits roots of all orders.

## Implementation notes

Adicness of a morphism `Spf R ⟶ Spf A` is rendered by adicness of the corresponding ring map,
which is `RingHom.IsAdic`, the definition of Stacks 0GBR: some ideal defining the topology of
the source extends to an ideal defining the topology of the target. Quantifying over all ring
maps `A → R` rather than over morphisms of formal spectra over a base makes the statement no
weaker, since every such morphism gives rise to a ring map; what it avoids is the
identification, at the affine level, of adic morphisms of formal algebraic spaces with adic
ring maps, which the library does not yet have.

As in `AlgebraicGeometry.FormalSpace.IsRigSurjective`, the topologies are parameters subject to
hypotheses naming the ideals that define them, namely `Ideal.span {t}` for `A` and the maximal
ideal for `R`; both hypotheses are satisfied by `Ideal.adicTopology` of the ideal in question,
so neither statement is vacuous. Completeness of `R` is recorded in the main result to match the
source although the argument does not use it.

The source also calls `A` a domain; what is recorded here instead is
`AlgebraicGeometry.FormalSpace.FractionalPowers.completionGenerator_ne_zero`, which is the use
the source makes of that, namely that the element `t` whose rig-points are wanted is nonzero in
`A`.

## References

* [Stacks Project, Tag 0AQZ](https://stacks.math.columbia.edu/tag/0AQZ)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0GBR](https://stacks.math.columbia.edu/tag/0GBR)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.FormalSpace

universe u

/-- An element of a discrete valuation ring which admits an `n`-th root for every `n ≥ 1` is
zero or a unit: its additive valuation is divisible by every `n ≥ 1`. -/
private theorem eq_zero_or_isUnit_of_forall_exists_pow (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {x : R} (hx : ∀ n : ℕ, n ≠ 0 → ∃ y : R, y ^ n = x) :
    x = 0 ∨ IsUnit x := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hx0, hxu⟩ := h
  have hne : IsDiscreteValuationRing.addVal R x ≠ ⊤ :=
    fun hh => hx0 (IsDiscreteValuationRing.addVal_eq_top_iff.mp hh)
  have hnz : IsDiscreteValuationRing.addVal R x ≠ 0 :=
    fun hh => hxu (IsDiscreteValuationRing.addVal_eq_zero_iff.mp hh)
  lift IsDiscreteValuationRing.addVal R x to ℕ using hne with m hm
  obtain ⟨y, hy⟩ := hx (m + 1) (Nat.succ_ne_zero m)
  have hvy : IsDiscreteValuationRing.addVal R y ≠ ⊤ := by
    intro hh
    rw [IsDiscreteValuationRing.addVal_eq_top_iff] at hh
    rw [hh, zero_pow (Nat.succ_ne_zero m)] at hy
    exact hx0 hy.symm
  lift IsDiscreteValuationRing.addVal R y to ℕ using hvy with j hj
  have key : (m : ℕ∞) = ((m + 1) * j : ℕ) := by
    rw [hm, ← hy, IsDiscreteValuationRing.addVal_pow, ← hj, nsmul_eq_mul]
    push_cast
    ring
  have hmj : m = (m + 1) * j := by exact_mod_cast key
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · rw [hj0, Nat.mul_zero] at hmj
    simp [hmj] at hnz
  · have := Nat.le_mul_of_pos_right (m + 1) hj0
    omega

/-- If ideals `J` and `K` both define the topology, then some power of `J` lies in `K`. -/
private theorem exists_pow_le_of_isAdic {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] {J K : Ideal B} (hJ : _root_.IsAdic J) (hK : _root_.IsAdic K) :
    ∃ n : ℕ, J ^ n ≤ K := by
  have hKop : IsOpen (K : Set B) := by simpa using (isAdic_iff.mp hK).1 1
  exact (isAdic_iff.mp hJ).2 _ (hKop.mem_nhds K.zero_mem)

/-- No ring map to a discrete valuation ring carrying its maximal-adic topology is adic, when
the source carries the adic topology of a principal ideal whose generator admits an `n`-th root
for every `n ≥ 1`: adicness would make the image of the generator neither zero nor a unit,
while its roots make the additive valuation of that image divisible by every `n ≥ 1`. -/
theorem not_isAdic_of_forall_exists_pow {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {τ : A} (hA : _root_.IsAdic (Ideal.span {τ}))
    (hτ : ∀ n : ℕ, n ≠ 0 → ∃ s : A, s ^ n = τ) {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (hR : _root_.IsAdic (IsLocalRing.maximalIdeal R)) (φ : A →+* R) : ¬ φ.IsAdic := by
  rintro ⟨I, hI, hIR⟩
  obtain ⟨m, hm⟩ := exists_pow_le_of_isAdic hA hI
  obtain ⟨nI, hnI⟩ := exists_pow_le_of_isAdic hI hA
  obtain ⟨a, ha⟩ := exists_pow_le_of_isAdic hIR hR
  obtain ⟨b, hb⟩ := exists_pow_le_of_isAdic hR hIR
  have hprime := (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  -- The image of `τ` lies in the maximal ideal, so it is not a unit.
  have htm : τ ^ m ∈ I :=
    hm (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
  have hmem : (φ τ) ^ (m * a) ∈ IsLocalRing.maximalIdeal R := by
    refine ha ?_
    rw [pow_mul]
    exact Ideal.pow_mem_pow (by rw [← map_pow]; exact Ideal.mem_map_of_mem φ htm) a
  have hnotunit : ¬ IsUnit (φ τ) := fun hu =>
    hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ (hprime.mem_of_pow_mem _ hmem) hu)
  -- A power of the maximal ideal lies in the ideal generated by the image of `τ`, which is
  -- therefore nonzero.
  have hchain : IsLocalRing.maximalIdeal R ^ (b * nI) ≤ Ideal.span {φ τ} :=
    calc IsLocalRing.maximalIdeal R ^ (b * nI)
        = (IsLocalRing.maximalIdeal R ^ b) ^ nI := by rw [pow_mul]
      _ ≤ (I.map φ) ^ nI := Ideal.pow_right_mono hb nI
      _ = Ideal.map φ (I ^ nI) := (Ideal.map_pow φ I nI).symm
      _ ≤ Ideal.map φ (Ideal.span {τ}) := Ideal.map_mono hnI
      _ = Ideal.span {φ τ} := by rw [Ideal.map_span]; simp
  obtain ⟨z, hz, hz0⟩ := Submodule.ne_bot_iff _ |>.mp
    (fun hh => IsDiscreteValuationRing.not_isField R
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hh))
  have hτ0 : φ τ ≠ 0 := by
    intro hh
    have hmemz : z ^ (b * nI) ∈ Ideal.span {φ τ} := hchain (Ideal.pow_mem_pow hz _)
    rw [hh, Ideal.span_singleton_eq_bot.mpr rfl] at hmemz
    exact pow_ne_zero _ hz0 (Ideal.mem_bot.mp hmemz)
  have hroot : ∀ n : ℕ, n ≠ 0 → ∃ y : R, y ^ n = φ τ := by
    intro n hn
    obtain ⟨s, hs⟩ := hτ n hn
    exact ⟨φ s, by rw [← map_pow, hs]⟩
  rcases eq_zero_or_isUnit_of_forall_exists_pow R hroot with h | h
  · exact hτ0 h
  · exact hnotunit h

namespace FractionalPowers

variable (k : Type u) [Field k]

/-- The element `t` of the ring `⋃_{n ≥ 1} k[t^{1/n}]` of polynomials in the fractional powers
of `t`, realised as the monoid algebra `k[ℚ≥0]` in which `t^q` is the basis element at `q`. -/
def generator : AddMonoidAlgebra k ℚ≥0 := AddMonoidAlgebra.single 1 1

/-- The ring `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧`, the `t`-adic completion of the ring of polynomials
in the fractional powers of `t`. -/
abbrev Completion : Type u :=
  AdicCompletion (Ideal.span {generator k}) (AddMonoidAlgebra k ℚ≥0)

/-- The element `t` of `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧`, the image of the element `t` of
`⋃_{n ≥ 1} k[t^{1/n}]`. -/
def completionGenerator : Completion k :=
  algebraMap (AddMonoidAlgebra k ℚ≥0) (Completion k) (generator k)

/-- The element `t` of `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧` has an `n`-th root for every `n ≥ 1`,
namely the image of `t^{1/n}`. -/
theorem exists_pow_eq_completionGenerator {n : ℕ} (hn : n ≠ 0) :
    ∃ s : Completion k, s ^ n = completionGenerator k := by
  refine ⟨algebraMap _ _ (AddMonoidAlgebra.single ((n : ℚ≥0)⁻¹) (1 : k)), ?_⟩
  rw [← map_pow, AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn)]
  rfl

/-- The element `t` of `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧` is nonzero: already in
`⋃_{n ≥ 1} k[t^{1/n}]` the element `t` is not divisible by `t^2`, since multiplying by `t^2`
raises every exponent occurring by `2`. -/
theorem completionGenerator_ne_zero : completionGenerator k ≠ 0 := by
  intro h
  have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {generator k}) 2) h
  rw [map_zero, completionGenerator, AdicCompletion.algebraMap_apply,
    Algebra.algebraMap_self_apply, AdicCompletion.evalₐ_of] at h2
  have hmem : generator k ∈ Ideal.span {generator k} ^ 2 :=
    (Submodule.Quotient.mk_eq_zero _).mp h2
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨y, hy⟩ := hmem
  rw [generator, AddMonoidAlgebra.single_pow] at hy
  have h3 : (AddMonoidAlgebra.single (1 : ℚ≥0) (1 : k)).coeff 1
      = (AddMonoidAlgebra.single ((2 : ℕ) • (1 : ℚ≥0)) ((1 : k) ^ 2) * y).coeff 1 := by
    rw [hy]
  rw [AddMonoidAlgebra.coeff_single_mul_of_forall_add_ne _ y
    (fun d hd => by
      simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one] at hd
      have h4 : (2 : ℚ≥0) ≤ 1 := hd ▸ le_self_add
      norm_num at h4)] at h3
  simp at h3

/-- **Stacks 0AQZ.** No ring map from `A = (⋃_{n ≥ 1} k[t^{1/n}])^∧`, carrying its `t`-adic
topology, to a complete discrete valuation ring `R`, carrying its maximal-adic topology, is
adic. Since a morphism `Spf R ⟶ Spf A` of affine formal algebraic spaces is `Spf` of a
continuous ring map `A → R` by Stacks 0AN0, there are therefore no adic morphisms
`Spf R ⟶ Spf A`, and every morphism `X ⟶ Spf A` satisfies the lifting condition of
Stacks 0AQQ vacuously, although `t` is a nonzero element of `A`. -/
@[stacks 0AQZ]
theorem not_isAdic_toDiscreteValuationRing [TopologicalSpace (Completion k)]
    [IsTopologicalRing (Completion k)]
    (hA : _root_.IsAdic (Ideal.span {completionGenerator k})) (R : Type*) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hR : _root_.IsAdic (IsLocalRing.maximalIdeal R)) (φ : Completion k →+* R) : ¬ φ.IsAdic :=
  not_isAdic_of_forall_exists_pow hA
    (fun _ hn => exists_pow_eq_completionGenerator k hn) hR φ

end FractionalPowers

end AlgebraicGeometry.FormalSpace

end
