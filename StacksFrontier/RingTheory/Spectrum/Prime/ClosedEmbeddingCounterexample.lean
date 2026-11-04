module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

/-!
# Spectra of finite-type algebras that are closed embeddings without the algebra being finite

Let `A → B` be a ring map of finite type whose induced map `Spec B → Spec A` is a homeomorphism
onto a closed subset. One may be tempted to read this hypothesis as an assertion about the ring
map: that `B` is a finite `A`-module, or at least that `A → B/rad(B)` is surjective, `rad`
denoting the Jacobson radical. Both readings are false, and this file produces the witnesses.

The witness for the second reading is the *cusp*: inside `k[t]` sits the subalgebra

  `k[t², t³] = {f : k[t] | f.coeff 1 = 0}`,

which is the coordinate ring of the cuspidal cubic. The extension is module-finite — `k[t]` is
spanned over it by `1` and `t` — so `Spec k[t] → Spec k[t², t³]` is a closed map, and it is
injective because for primes `p`, `q` with the same contraction either `t² ∉ p`, and then
multiplying by `t²` carries `p` into the subalgebra and hence into `q`, or `t² ∈ p`, and then `t`
lies in both and the same bookkeeping applies. So the map is a closed embedding, while
`k[t², t³] → k[t]` is not surjective, `t` being omitted. Since `k[t]` has zero Jacobson radical,
no quotient by radicals repairs this.

## Main definitions

* `Polynomial.cuspSubalgebra`: the subalgebra `k[t², t³]` of `k[t]`, presented by the vanishing of
  the degree-one coefficient.

## Main results

* `Ideal.le_of_comap_algebraMap_eq_of_notMem`, `Ideal.le_of_comap_algebraMap_eq_of_mem`: two
  criteria forcing two prime ideals with the same contraction to `A` to be comparable, for `R`
  spanned over `A` by `1` and one element `x`.
* `Polynomial.isClosedEmbedding_comap_algebraMap_cuspSubalgebra`:
  `Spec k[t] → Spec k[t², t³]` is a closed embedding.
* `Polynomial.not_forall_exists_algebraMap_sub_mem_jacobson`: a finite-type ring map whose
  spectrum is a closed embedding need not be surjective modulo the Jacobson radical of the
  target.

## Implementation notes

The reading refuted here is the one used in the proof of Stacks 09VG, which asserts that for
`i : X → Y` inducing a homeomorphism of `X` with a closed subset of `Y` the induced map on affine
pieces "means that `A/rad(A) → B/rad(B)` is surjective". The counterexample refutes exactly that
step: the Jacobson radical of `k[t]` is zero, so the asserted surjectivity would make
`k[t², t³] → k[t]` surjective, which it is not. **It does not by itself refute the statement of
Stacks 09VG**, whose conclusion is about pseudo-coherence relative to a base and not about the
ring map.

## References

* [Stacks, Tag 09VG](https://stacks.math.columbia.edu/tag/09VG)
* [Stacks, Tag 09UJ](https://stacks.math.columbia.edu/tag/09UJ)
-/

namespace Ideal

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

/-- Ideals with the same contraction to `A` contain the same elements coming from `A`. -/
private theorem mem_iff_of_comap_algebraMap_eq {p q : Ideal R}
    (h : p.comap (algebraMap A R) = q.comap (algebraMap A R)) {a : A} :
    algebraMap A R a ∈ p ↔ algebraMap A R a ∈ q :=
  Ideal.ext_iff.mp h a

/-- If `R` is spanned over `A` by `1` and `x`, every `y : R` is `a + b * x` with `a b : A`. -/
private theorem exists_eq_algebraMap_add_mul {x : R} (hspan : Submodule.span A {1, x} = ⊤)
    (y : R) : ∃ a b : A, y = algebraMap A R a + algebraMap A R b * x := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hspan ▸ Submodule.mem_top (x := y))
  exact ⟨a, b, by rw [← hab]; simp [Algebra.smul_def]⟩

/--
Suppose `R` is spanned over `A` by `1` and `x`, and that `u * x` comes from `A`, say
`u * x = v` with `u v : A`. If two ideals of `R` have the same contraction to `A`, the second is
prime, and `u` does not map into the first, then the first is contained in the second: an element
`y` of the first can be written `a + b * x`, so `u * y = u * a + b * v` comes from `A`, hence lies
in the common contraction, hence `u * y` lies in the second ideal, and `u` does not.
-/
theorem le_of_comap_algebraMap_eq_of_notMem {x : R} (hspan : Submodule.span A {1, x} = ⊤)
    {u v : A} (huv : algebraMap A R u * x = algebraMap A R v) {p q : Ideal R} [hq : q.IsPrime]
    (h : p.comap (algebraMap A R) = q.comap (algebraMap A R))
    (hu : algebraMap A R u ∉ p) : p ≤ q := by
  intro y hy
  obtain ⟨a, b, hy'⟩ := exists_eq_algebraMap_add_mul hspan y
  have key : algebraMap A R u * y = algebraMap A R (u * a + b * v) := by
    rw [hy', map_add, map_mul, map_mul, ← huv]; ring
  have hq' : algebraMap A R u * y ∈ q := by
    rw [key]
    exact (mem_iff_of_comap_algebraMap_eq h).mp (key ▸ p.mul_mem_left _ hy)
  exact (hq.mem_or_mem hq').resolve_left fun h₁ => hu ((mem_iff_of_comap_algebraMap_eq h).mpr h₁)

/--
Suppose `R` is spanned over `A` by `1` and `x`. If two ideals of `R` have the same contraction to
`A` and both contain `x`, then the first is contained in the second: an element `y` of the first
can be written `a + b * x`, and then `a` comes from `A` and lies in the first ideal, hence in the
common contraction, hence in the second.
-/
theorem le_of_comap_algebraMap_eq_of_mem {x : R} (hspan : Submodule.span A {1, x} = ⊤)
    {p q : Ideal R} (h : p.comap (algebraMap A R) = q.comap (algebraMap A R))
    (hp : x ∈ p) (hq : x ∈ q) : p ≤ q := by
  intro y hy
  obtain ⟨a, b, hy'⟩ := exists_eq_algebraMap_add_mul hspan y
  have h₁ : algebraMap A R a ∈ p := by
    have he : algebraMap A R a = y - algebraMap A R b * x := by rw [hy']; ring
    rw [he]
    exact sub_mem hy (p.mul_mem_left _ hp)
  rw [hy']
  exact add_mem ((mem_iff_of_comap_algebraMap_eq h).mp h₁) (q.mul_mem_left _ hq)

end Ideal

namespace Polynomial

open scoped Polynomial

variable (k : Type*) [CommRing k]

/--
The coordinate ring `k[t², t³]` of the cuspidal cubic, realised inside `k[t]` as the subalgebra of
polynomials whose degree-one coefficient vanishes; that condition is what every argument below
uses.
-/
def cuspSubalgebra : Subalgebra k k[X] where
  carrier := {f | f.coeff 1 = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      ha, hb]
  one_mem' := by simp [coeff_one]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    simp [ha, hb]
  zero_mem' := by simp
  algebraMap_mem' := by intro r; simp

variable {k} in
/-- Membership in `k[t², t³]` is the vanishing of the degree-one coefficient. -/
@[simp] theorem mem_cuspSubalgebra {f : k[X]} : f ∈ cuspSubalgebra k ↔ f.coeff 1 = 0 := Iff.rfl

/-- `k[t]` is spanned over `k[t², t³]` by `1` and `t`: subtracting `(f.coeff 1) * t` from `f`
kills the degree-one coefficient. -/
theorem span_one_X_cuspSubalgebra : Submodule.span (cuspSubalgebra k) {1, (X : k[X])} = ⊤ := by
  refine top_unique fun f _ => ?_
  refine Submodule.mem_span_pair.mpr
    ⟨⟨f - C (f.coeff 1) * X, ?_⟩, ⟨C (f.coeff 1), ?_⟩, ?_⟩
  · simp
  · simp
  · simp [Algebra.smul_def]

/-- `k[t]` is a finite module over `k[t², t³]`, spanned by `1` and `t`. -/
instance module_finite_cuspSubalgebra : Module.Finite (cuspSubalgebra k) k[X] :=
  Module.finite_def.mpr (Submodule.fg_def.mpr
    ⟨{1, X}, (Set.finite_singleton _).insert _, span_one_X_cuspSubalgebra k⟩)

/--
`Spec k[t] → Spec k[t², t³]` is injective. For primes `p`, `q` with the same contraction, either
`t² ∉ p`, and then multiplication by `t²` lands `p` inside `k[t², t³]`, or `t² ∈ p`, and then `t`
lies in both `p` and `q`.
-/
theorem injective_comap_algebraMap_cuspSubalgebra :
    Function.Injective (PrimeSpectrum.comap (algebraMap (cuspSubalgebra k) k[X])) := by
  intro p q h
  have := p.2
  have := q.2
  have h' : p.asIdeal.comap (algebraMap (cuspSubalgebra k) k[X])
      = q.asIdeal.comap (algebraMap (cuspSubalgebra k) k[X]) := by
    simpa using congrArg PrimeSpectrum.asIdeal h
  set u : cuspSubalgebra k := ⟨X ^ 2, by simp⟩ with hu
  set v : cuspSubalgebra k := ⟨X ^ 3, by simp⟩ with hv
  have hcoe : algebraMap (cuspSubalgebra k) k[X] u = X ^ 2 := rfl
  have hcoe' : algebraMap (cuspSubalgebra k) k[X] v = X ^ 3 := rfl
  have huv : algebraMap (cuspSubalgebra k) k[X] u * X = algebraMap (cuspSubalgebra k) k[X] v := by
    rw [hcoe, hcoe']; ring
  have hspan := span_one_X_cuspSubalgebra k
  by_cases hX : (X : k[X]) ∈ p.asIdeal
  · have hsq : (X : k[X]) ^ 2 ∈ q.asIdeal := by
      rw [← hcoe]
      exact (Ideal.mem_iff_of_comap_algebraMap_eq h').mp
        (p.asIdeal.pow_mem_of_mem hX 2 (by norm_num))
    have hXq : (X : k[X]) ∈ q.asIdeal := q.2.mem_of_pow_mem 2 hsq
    exact PrimeSpectrum.ext (le_antisymm
      (Ideal.le_of_comap_algebraMap_eq_of_mem hspan h' hX hXq)
      (Ideal.le_of_comap_algebraMap_eq_of_mem hspan h'.symm hXq hX))
  · have hup : algebraMap (cuspSubalgebra k) k[X] u ∉ p.asIdeal := by
      rw [hcoe]
      exact fun hm => hX (p.2.mem_of_pow_mem 2 hm)
    have huq : algebraMap (cuspSubalgebra k) k[X] u ∉ q.asIdeal := by
      exact fun hm => hup ((Ideal.mem_iff_of_comap_algebraMap_eq h').mpr hm)
    exact PrimeSpectrum.ext (le_antisymm
      (Ideal.le_of_comap_algebraMap_eq_of_notMem hspan huv h' hup)
      (Ideal.le_of_comap_algebraMap_eq_of_notMem hspan huv h'.symm huq))

/--
`Spec k[t] → Spec k[t², t³]` is a closed embedding: it is continuous, injective, and closed
because `k[t]` is integral over `k[t², t³]`.
-/
theorem isClosedEmbedding_comap_algebraMap_cuspSubalgebra :
    Topology.IsClosedEmbedding (PrimeSpectrum.comap (algebraMap (cuspSubalgebra k) k[X])) := by
  have : Algebra.IsIntegral (cuspSubalgebra k) k[X] := Algebra.IsIntegral.of_finite _ _
  refine .of_continuous_injective_isClosedMap (PrimeSpectrum.continuous_comap _)
    (injective_comap_algebraMap_cuspSubalgebra k)
    (PrimeSpectrum.isClosedMap_comap_of_isIntegral _ fun x => Algebra.IsIntegral.isIntegral x)

/--
**The reformulation used in the proof of Stacks 09VG is false.** That proof asserts that a map of
schemes locally of finite type inducing a homeomorphism onto a closed subset "means that
`A/rad(A) → B/rad(B)` is surjective" on affine pieces, `rad` denoting the Jacobson radical;
equivalently, that `A → B/rad(B)` is surjective. The cusp `ℚ[t², t³] ⊆ ℚ[t]` refutes this: the
extension is module-finite, hence of finite type, its spectrum map is a closed embedding
(`Polynomial.isClosedEmbedding_comap_algebraMap_cuspSubalgebra`), the Jacobson radical of `ℚ[t]`
is zero because `ℚ[t]` is a reduced Jacobson ring, and `t` is not in `ℚ[t², t³]`.

This refutes that **step** of the proof. It does not refute the statement of Stacks 09VG, whose
conclusion concerns `m`-pseudo-coherence relative to a base scheme.
-/
theorem not_forall_exists_algebraMap_sub_mem_jacobson :
    ¬ ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B],
        Algebra.FiniteType A B →
        Topology.IsClosedEmbedding (PrimeSpectrum.comap (algebraMap A B)) →
        ∀ b : B, ∃ a : A, algebraMap A B a - b ∈ (⊥ : Ideal B).jacobson := by
  intro h
  obtain ⟨a, ha⟩ := h (cuspSubalgebra ℚ) ℚ[X] (Module.Finite.finiteType _)
    (isClosedEmbedding_comap_algebraMap_cuspSubalgebra ℚ) X
  have hJ : IsJacobsonRing ℚ[X] := inferInstance
  have hjac : (⊥ : Ideal ℚ[X]).jacobson = ⊥ := hJ.out Ideal.isRadical_bot
  rw [hjac, Ideal.mem_bot, sub_eq_zero] at ha
  have hcoeff : (X : ℚ[X]).coeff 1 = 0 := ha ▸ a.2
  simp at hcoeff

end Polynomial
