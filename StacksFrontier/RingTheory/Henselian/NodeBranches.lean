module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Henselian
public import StacksFrontier.RingTheory.Etale.IndEtaleSeparablyClosed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two branches of a node over a henselian extension

Let `O` be a local domain with elements `x, y` of its maximal ideal satisfying the equation
`y² = x²(1 + x)` of a node, with `y ∉ x O` (the node is not unibranch: `y / x` is not in `O`), and
with `2` invertible. Let `R` be a henselian local `O`-algebra which is faithfully flat over `O`.
Hensel's lemma gives a square root `u ≡ 1` of `1 + x` in `R`, and the equation of the node
factors in `R` as `e₁ e₂ = 0` with `e₁ = y - x u` and `e₂ = y + x u`: the node acquires two
branches. Neither branch vanishes, and neither meets `O` except in `0`.

Consequently, if `R` is moreover ind-étale over `O`, there are two ring maps `R → K` into an
algebraically closed field which agree on `O`, one killing `e₁` and the other not. Geometrically:
the fibre of `Spec R → Spec O` over the generic point of `O` contains a point on each branch, and
both are `K`-points over the same `K`-point of `Spec O`.

This is the algebra underlying the counterexample to the statement of Stacks Tag 0EZV as written,
where `O` is the local ring of a nodal curve at its node and `R` is its strict henselization.

## Main results

* `HenselianLocalRing.exists_sq_eq_one_add`: in a henselian local ring in which `2` is a unit,
  `1 + a` has a square root congruent to `1` for every `a` in the maximal ideal.
* `StacksDraft.NodeBranches.branch_ne_zero`, `StacksDraft.NodeBranches.comap_span_branch`: the
  branches `y ∓ x u` are nonzero and meet `O` only in `0`.
* `StacksDraft.NodeBranches.exists_two_points`: two ring maps `R → K` agreeing on `O`, the first
  killing `y - x u` and the second not.

## References

* [Stacks Project, Tag 0EZV](https://stacks.math.columbia.edu/tag/0EZV)
-/

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

universe u

/-- **Square roots in a henselian local ring.** If `2` is a unit in a henselian local ring `R`,
then for every `a` in the maximal ideal, `1 + a` has a square root congruent to `1` modulo the
maximal ideal. -/
public theorem HenselianLocalRing.exists_sq_eq_one_add {R : Type*} [CommRing R]
    [HenselianLocalRing R] (h2 : IsUnit (2 : R)) {a : R} (ha : a ∈ maximalIdeal R) :
    ∃ v : R, v ^ 2 = 1 + a ∧ v - 1 ∈ maximalIdeal R := by
  have hmonic : (X ^ 2 - C (1 + a)).Monic := by
    apply Polynomial.monic_X_pow_sub_C
    norm_num
  obtain ⟨v, hv, hv1⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C (1 + a)) hmonic 1
    (by simpa using (maximalIdeal R).neg_mem_iff.mpr ha)
    (by simpa [Polynomial.derivative_X_pow, one_add_one_eq_two] using h2)
  refine ⟨v, ?_, hv1⟩
  simpa [sub_eq_zero] using hv

/-- In a local ring in which `2` is a unit, two square roots of the same element which are both
congruent to `1` coincide. -/
public theorem IsLocalRing.eq_of_sq_eq_of_sub_one_mem {R : Type*} [CommRing R] [IsLocalRing R]
    (h2 : IsUnit (2 : R)) {v w : R} (hvw : v ^ 2 = w ^ 2) (hv : v - 1 ∈ maximalIdeal R)
    (hw : w - 1 ∈ maximalIdeal R) : v = w := by
  have hunit : IsUnit (v + w) := by
    have : v + w = 2 + ((v - 1) + (w - 1)) := by ring
    rw [this]
    by_contra h
    have hmem : 2 + ((v - 1) + (w - 1)) ∈ maximalIdeal R := (mem_maximalIdeal _).mpr h
    exact (mem_maximalIdeal _).mp (by
      simpa using (maximalIdeal R).sub_mem hmem ((maximalIdeal R).add_mem hv hw)) h2
  have : (v - w) * (v + w) = 0 := by linear_combination hvw
  exact sub_eq_zero.mp ((hunit.mul_left_eq_zero).mp this)

namespace StacksDraft.NodeBranches

variable {O : Type u} [CommRing O] [IsDomain O] {R : Type u} [CommRing R] [Algebra O R]
  [Module.FaithfullyFlat O R]

variable (x y : O) {v : R}

omit [IsDomain O] [Module.FaithfullyFlat O R] in
/-- The two branches `y ∓ x v` of the node `y² = x²(1 + x)` multiply to zero once `v` is a
square root of `1 + x`. -/
public theorem branch_mul_branch (hxy : y ^ 2 = x ^ 2 * (1 + x))
    (hv : v ^ 2 = 1 + algebraMap O R x) :
    (algebraMap O R y - algebraMap O R x * v) * (algebraMap O R y + algebraMap O R x * v) = 0 := by
  have : algebraMap O R y ^ 2 = algebraMap O R x ^ 2 * (1 + algebraMap O R x) := by
    rw [← map_pow, hxy]; simp
  linear_combination this - algebraMap O R x ^ 2 * hv

omit [IsDomain O] in
/-- **A branch of the node is nonzero.** If `y = ± x v` in `R`, then `y` lies in `x R ∩ O = x O`
by faithful flatness, which is excluded. -/
public theorem branch_ne_zero (hy : y ∉ Ideal.span {x}) (s : R) (_hs : s = 1 ∨ s = -1) :
    algebraMap O R y - s * algebraMap O R x * v ≠ 0 := by
  intro h
  apply hy
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R) (Ideal.span {x}), Ideal.mem_comap,
    Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
  refine ⟨s * v, ?_⟩
  linear_combination -h

/-- **A branch of the node meets `O` only in `0`.** If `c ∈ O` is a multiple of `y - s x v` in
`R`, then `c` kills the other branch `y + s x v`, which is nonzero; since `R` is flat over the
domain `O`, this forces `c = 0`. -/
public theorem comap_span_branch (hxy : y ^ 2 = x ^ 2 * (1 + x)) (hy : y ∉ Ideal.span {x})
    (hv : v ^ 2 = 1 + algebraMap O R x) (s : R) (hs : s = 1 ∨ s = -1) :
    Ideal.comap (algebraMap O R)
      (Ideal.span {algebraMap O R y - s * algebraMap O R x * v}) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hc
  obtain ⟨r, hr⟩ := hc
  rw [Ideal.mem_bot]
  by_contra hc0
  have hother : algebraMap O R y - (-s) * algebraMap O R x * v ≠ 0 :=
    branch_ne_zero x y hy (-s) (by rcases hs with rfl | rfl <;> simp)
  have hprod : (algebraMap O R y - s * algebraMap O R x * v) *
      (algebraMap O R y - (-s) * algebraMap O R x * v) = 0 := by
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> ring
    have := branch_mul_branch x y hxy (v := s * v) (by rw [mul_pow, hs2, one_mul, hv])
    linear_combination this
  have hreg : IsSMulRegular R c :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc0)
  apply hother
  apply hreg
  change c • _ = c • (0 : R)
  rw [smul_zero, Algebra.smul_def, ← hr, mul_assoc, hprod, mul_zero]

/-- **Two points on different branches over the same point of `O`.** Let `e ∈ R` be nonzero
with `e R ∩ O = 0`, and let `R` be ind-étale over `O`. Then there are an algebraically closed
field `K` and two ring maps `k, t : R → K` which agree on `O`, are injective on `O`, and satisfy
`k e = 0` and `t e ≠ 0`. -/
public theorem exists_two_points (hind : IndEtale O R) {e : R} (he : e ≠ 0)
    (hcomap : Ideal.comap (algebraMap O R) (Ideal.span {e}) = ⊥) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (k t : R →+* K),
      k.comp (algebraMap O R) = t.comp (algebraMap O R) ∧
        Function.Injective (k.comp (algebraMap O R)) ∧ k e = 0 ∧ t e ≠ 0 := by
  classical
  -- a prime of `R` through `e` meeting `O` only in `0`
  obtain ⟨P, hP, heP, hdisj⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {e})
    ((nonZeroDivisors O).map (algebraMap O R)) (by
      rw [Set.disjoint_left]
      rintro _ hmem ⟨c, hc, rfl⟩
      have : c ∈ Ideal.comap (algebraMap O R) (Ideal.span {e}) := hmem
      rw [hcomap, Ideal.mem_bot] at this
      exact nonZeroDivisors.ne_zero hc this)
  have := hP
  let K := AlgebraicClosure (FractionRing (R ⧸ P))
  let k : R →+* K := (algebraMap (FractionRing (R ⧸ P)) K).comp
    ((algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P))
  have hk_ker : ∀ r, k r = 0 ↔ r ∈ P := by
    intro r
    simp only [k, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (RingHom.injective (algebraMap (FractionRing (R ⧸ P)) K)),
      IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hkO : Function.Injective (k.comp (algebraMap O R)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra hc0
    rw [RingHom.comp_apply, hk_ker] at hc
    exact Set.disjoint_left.mp hdisj hc ⟨c, mem_nonZeroDivisors_of_ne_zero hc0, rfl⟩
  -- the fibre algebra `K ⊗[O] R`, ind-étale over `K`, in which `1 ⊗ e` is not nilpotent
  let : Algebra O K := (k.comp (algebraMap O R)).toAlgebra
  have hKR : IndEtale K (K ⊗[O] R) := indEtale_tensorProduct K hind
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[O] K ⊗[O] R) := by
    have h1 : Function.Injective ((Algebra.linearMap O K).rTensor R) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hkO
    intro r r' hrr'
    have := h1 (a₁ := 1 ⊗ₜ r) (a₂ := 1 ⊗ₜ r') (by
      simpa [LinearMap.rTensor_tmul] using hrr')
    simpa using congrArg (TensorProduct.lid O R) this
  have hred := hKR.isReduced
  have hne : ¬ IsNilpotent ((1 : K) ⊗ₜ[O] e) := fun h => he (hinj (by simpa using h.eq_zero))
  obtain ⟨Q, hQ, heQ⟩ : ∃ Q : Ideal (K ⊗[O] R), Q.IsPrime ∧ (1 : K) ⊗ₜ[O] e ∉ Q := by
    by_contra! H
    exact hne (nilpotent_iff_mem_prime.mpr fun Q hQ => H Q hQ)
  obtain ⟨χ, hχ⟩ := hKR.exists_algHom_ker_eq Q
  let t : R →+* K := (χ : K ⊗[O] R →+* K).comp
    (Algebra.TensorProduct.includeRight : R →ₐ[O] K ⊗[O] R).toRingHom
  refine ⟨K, inferInstance, inferInstance, k, t, ?_, hkO, (hk_ker e).mpr (heP
    (Ideal.subset_span rfl)), ?_⟩
  · ext c
    simp only [t, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply]
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    have : (algebraMap O K c) ⊗ₜ[O] (1 : R) = algebraMap K (K ⊗[O] R) (algebraMap O K c) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [this, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    rfl
  · exact fun h => heQ (hχ ▸ h)

end StacksDraft.NodeBranches

/-! ### The node `y² = x²(1 + x)` -/

namespace StacksDraft.Node

variable (k : Type u) [Field k]

/-- The coordinate ring of the nodal cubic `y² = x²(1 + x)`, realized through its normalization
as the subalgebra of `k[t]` generated by `x = t² - 1` and `y = t³ - t`. -/
@[ega "IV 6.5.5"]
public noncomputable abbrev ring : Subalgebra k k[X] :=
  Algebra.adjoin k {X ^ 2 - 1, X ^ 3 - X}

/-- The coordinate `x = t² - 1` on the node. -/
public noncomputable def x : ring k := ⟨X ^ 2 - 1, Algebra.subset_adjoin (by simp)⟩

/-- The coordinate `y = t³ - t` on the node. -/
public noncomputable def y : ring k := ⟨X ^ 3 - X, Algebra.subset_adjoin (by simp)⟩

/-- The equation of the node. -/
public theorem y_sq : y k ^ 2 = x k ^ 2 * (1 + x k) := by
  apply Subtype.ext
  simp only [x, y, SubmonoidClass.mk_pow]
  change (X ^ 3 - X : k[X]) ^ 2 = (X ^ 2 - 1) ^ 2 * (1 + (X ^ 2 - 1))
  ring

/-- Evaluation at `t = a`, restricted to the node. -/
public noncomputable def eval (a : k) : ring k →ₐ[k] k := (Polynomial.aeval a).comp (ring k).val

/-- The two preimages `t = ± 1` of the node have the same image: evaluation at `1` and at `-1`
agree on the coordinate ring of the node. -/
public theorem eval_one_eq_eval_neg_one : eval k 1 = eval k (-1) := by
  apply AlgHom.ext
  rintro ⟨f, hf⟩
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with rfl | rfl <;> norm_num [eval]
  | algebraMap r => simp [eval]
  | add f g _ _ hf hg => simpa [eval] using congrArg₂ (· + ·) hf hg
  | mul f g _ _ hf hg => simpa [eval] using congrArg₂ (· * ·) hf hg

/-- The ideal of the node: the kernel of evaluation at `t = 1`. -/
public noncomputable abbrev maximalIdeal : Ideal (ring k) := RingHom.ker (eval k 1)

public instance : (maximalIdeal k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun a => ⟨algebraMap k _ a, by simp⟩

public theorem x_mem_maximalIdeal : x k ∈ maximalIdeal k := by
  simp [RingHom.mem_ker, eval, x]

public theorem y_mem_maximalIdeal : y k ∈ maximalIdeal k := by
  simp [RingHom.mem_ker, eval, y]

section Localization

variable {k} (O : Type u) [CommRing O] [Algebra (ring k) O]
  [IsLocalization.AtPrime O (maximalIdeal k)]

include k

/-- The local ring of the node at the singular point is a domain. -/
public theorem isDomain_localization : IsDomain O :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := (maximalIdeal k).primeCompl) O
    (fun _ hs => mem_nonZeroDivisors_of_ne_zero fun h => hs (h ▸ (maximalIdeal k).zero_mem))

public instance (a : k) : (RingHom.ker (Polynomial.aeval a : k[X] →ₐ[k] k)).IsPrime :=
  RingHom.ker_isPrime _

/-- Localizing `k[t]` at the prime of `t = a`. -/
noncomputable abbrev localPoly (a : k) :=
  Localization.AtPrime (RingHom.ker (Polynomial.aeval a : k[X] →ₐ[k] k))

/-- The map from the local ring of the node at the singular point to the local ring of `k[t]` at
either preimage `t = ± 1`. -/
noncomputable def toLocalPoly (a : k) (ha : a = 1 ∨ a = -1) : O →+* localPoly a :=
  IsLocalization.lift (M := (maximalIdeal k).primeCompl) (S := O)
    (g := (algebraMap k[X] (localPoly a)).comp (ring k).val.toRingHom) (by
      rintro ⟨s, hs⟩
      apply IsLocalization.map_units (localPoly a) (⟨(s : k[X]), ?_⟩ :
        (RingHom.ker (Polynomial.aeval a : k[X] →ₐ[k] k)).primeCompl)
      intro hmem
      apply hs
      change eval k 1 s = 0
      rcases ha with rfl | rfl
      · simpa [eval] using RingHom.mem_ker.mp hmem
      · rw [eval_one_eq_eval_neg_one]; simpa [eval] using RingHom.mem_ker.mp hmem)

theorem toLocalPoly_algebraMap (a : k) (ha : a = 1 ∨ a = -1) (f : ring k) :
    toLocalPoly O a ha (algebraMap (ring k) O f) = algebraMap k[X] (localPoly a) f :=
  IsLocalization.lift_eq _ _

/-- Evaluation at `t = a` on the local ring of `k[t]` there. -/
noncomputable def evalLocalPoly (a : k) : localPoly a →+* k :=
  IsLocalization.lift (M := (RingHom.ker (Polynomial.aeval a : k[X] →ₐ[k] k)).primeCompl)
    (g := (Polynomial.aeval a : k[X] →ₐ[k] k).toRingHom) (by
      rintro ⟨s, hs⟩
      exact isUnit_iff_ne_zero.mpr fun h => hs h)

theorem evalLocalPoly_algebraMap (a : k) (f : k[X]) :
    evalLocalPoly a (algebraMap k[X] (localPoly a) f) = Polynomial.aeval a f :=
  IsLocalization.lift_eq _ _

/-- **The node is not unibranch: `y / x = t` is not in its local ring.** If `y = g x` in the local
ring at the singular point, then in the local rings of `k[t]` at `t = ± 1` the image of `g` is
`t`, whose values `± 1` at the two preimages differ — whereas both values of `g` are its value at
the singular point. -/
public theorem y_not_mem_span_x (h2 : (2 : k) ≠ 0) :
    algebraMap (ring k) O (y k) ∉ Ideal.span {algebraMap (ring k) O (x k)} := by
  intro hmem
  rw [Ideal.mem_span_singleton'] at hmem
  obtain ⟨g, hg⟩ := hmem
  have key : ∀ (a : k) (ha : a = 1 ∨ a = -1),
      evalLocalPoly a (toLocalPoly O a ha g) = a := by
    intro a ha
    have h1 := congrArg (toLocalPoly O a ha) hg
    rw [map_mul, toLocalPoly_algebraMap, toLocalPoly_algebraMap] at h1
    have hx0 : algebraMap k[X] (localPoly a) (X ^ 2 - 1) ≠ 0 := by
      rw [Ne, IsLocalization.to_map_eq_zero_iff (localPoly a)
        (Ideal.primeCompl_le_nonZeroDivisors
          (RingHom.ker (Polynomial.aeval a : k[X] →ₐ[k] k)))]
      intro h
      have := congrArg (Polynomial.eval 0) h
      simp at this
    have ht : toLocalPoly O a ha g = algebraMap k[X] (localPoly a) X := by
      apply mul_right_cancel₀ hx0
      simp only [x, y] at h1
      rw [h1, ← map_mul]
      congr 1
      ring
    rw [ht, evalLocalPoly_algebraMap, Polynomial.aeval_X]
  have hsame : (evalLocalPoly (1 : k)).comp (toLocalPoly O 1 (Or.inl rfl)) =
      (evalLocalPoly (-1 : k)).comp (toLocalPoly O (-1) (Or.inr rfl)) := by
    apply IsLocalization.ringHom_ext (maximalIdeal k).primeCompl
    ext f
    simp only [RingHom.comp_apply, toLocalPoly_algebraMap, evalLocalPoly_algebraMap]
    exact congrArg (fun φ : ring k →ₐ[k] k => φ f) (eval_one_eq_eval_neg_one k)
  have := congrArg (fun φ : O →+* k => φ g) hsame
  simp only [RingHom.comp_apply, key] at this
  apply h2
  linear_combination this

end Localization

end StacksDraft.Node
