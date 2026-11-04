module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors

/-!
# Retractions of exterior powers from a retraction divisible outside a finite set

Let `R` be a commutative ring, `y : R`, let `F` be an `R`-module and let `G` be free with basis
`b : Module.Basis ι R G` indexed by a linearly ordered type `ι`. Suppose `α : F →ₗ[R] G` and
`β : G →ₗ[R] F` satisfy `α ∘ₗ β = y • id`, so that `β` is a retraction of `α` up to `y`, and
suppose moreover that `β` is divisible by `y` on every basis vector outside a finite set `Q` of
indices: there is a family `β' : ι → F` with `β (b i) = (if i ∈ Q then 1 else y) • β' i`.

This file shows that then, for every `a : ℕ`, the map `⋀^a α` admits a retraction up to `y ^ r`
as soon as `Q.card ≤ r`, with no dependence of `r` on `a`.

The mechanism is a counting one. The basis of `⋀[R]^a G` attached to `b` is indexed by the
`a`-element finsets `s` of `ι` (`Module.Basis.exteriorPower`), and on the basis vector indexed by
`s` the map `⋀^a β` is divisible by `y ^ #(s \ Q)` — one factor of `y` for each index of `s` lying
outside `Q`. Since `#s = a` and `#(s ∩ Q) ≤ #Q ≤ r`, we get `a ≤ r + #(s \ Q)`, so the element
`y ^ (r + #(s \ Q) - a) • (⋀^a β) (b_s) / y ^ #(s \ Q)` — which is an honest element of `⋀[R]^a F`,
namely `y ^ (r + #(s \ Q) - a) • ιMulti_family R a β' s` — is a preimage of `y ^ r • b_s` under
`⋀^a α`. The loss `y ^ a` coming from `α ∘ₗ β = y • id` is exactly absorbed by the `y`'s extracted
from `β`, uniformly in `a`.

This is the linear algebra behind the pole bound in the Stacks Project, Tag 0G5G.

## Main results

* `exteriorPower.map_smul_id`: `⋀^a (y • id) = y ^ a • id`.
* `exteriorPower.exists_comp_map_eq_pow_smul`: **the retraction.** Under the hypotheses above,
  and assuming that `y` acts injectively on `⋀[R]^a G`, there is `ψ : ⋀[R]^a G →ₗ[R] ⋀[R]^a F`
  with `⋀^a α ∘ₗ ψ = y ^ r • id`.
* `exteriorPower.exists_comp_map_eq_pow_smul_of_mem_nonZeroDivisors`: the same conclusion with the
  injectivity hypothesis replaced by `y ∈ nonZeroDivisors R`.
* `exteriorPower.eq_zero_of_smul_eq_zero`: a non-zero-divisor of `R` acts injectively on the
  exterior powers of a free module.
* `exteriorPower.exists_comp_map_eq_pow_smul_of_forall`: the same conclusion with the
  divisibility hypothesis split into the two cases it packages.

## Implementation notes

The injectivity hypothesis on `y` is stated as `∀ z : ⋀[R]^a G, y • z = 0 → z = 0` rather than
through a typeclass, because it is needed only in the single exterior power at hand and is the
weakest form the proof uses: the identity for `ψ` is first established after multiplying by
`y ^ #(s \ Q)` and then the factor is cancelled, which is what
`exteriorPower.eq_of_pow_smul_eq_pow_smul` does.

No `NoZeroSMulDivisors` assumption appears in the `nonZeroDivisors` variant: `G` is free by
hypothesis, hence so is `⋀[R]^a G`, and on a free module a non-zero-divisor acts injectively
because it does so on each coordinate.

## References

* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
-/

@[expose] public section

open Set

namespace exteriorPower

variable {R : Type*} [CommRing R]

section Cancellation

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- If multiplication by `y` is injective on `M` (in the form: it has trivial kernel), then so is
multiplication by any power of `y`. -/
private lemma eq_of_pow_smul_eq_pow_smul {y : R} (hy : ∀ z : M, y • z = 0 → z = 0) (k : ℕ)
    {z w : M} (h : y ^ k • z = y ^ k • w) : z = w := by
  induction k generalizing z w with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ', mul_smul, mul_smul] at h
    exact ih (sub_eq_zero.mp (hy _ (by rw [smul_sub, h, sub_self])))

end Cancellation

variable {G : Type*} [AddCommGroup G] [Module R G]

/-- The `a`-th exterior power of the homothety of ratio `y` is the homothety of ratio `y ^ a`:
each of the `a` wedge factors contributes one scalar. -/
lemma map_smul_id (y : R) (a : ℕ) :
    map a (y • LinearMap.id : G →ₗ[R] G) = (y ^ a) • LinearMap.id := by
  refine linearMap_ext (AlternatingMap.ext fun v => ?_)
  simp only [LinearMap.compAlternatingMap_apply, map_apply_ιMulti, LinearMap.smul_apply,
    LinearMap.id_apply]
  have h : ((y • LinearMap.id : G →ₗ[R] G) ∘ v) = fun i => y • v i := rfl
  rw [h, (ιMulti R a).map_smul_univ (fun _ => y) v]
  simp

variable {F : Type*} [AddCommGroup F] [Module R F] {ι : Type*} [LinearOrder ι]

/-- An `a`-element finset `s` of `ι` is the image of the increasing enumeration of its elements,
read as a `Finset.map` along `Set.powersetCard.ofFinEmbEquiv.symm s`. -/
private lemma coe_eq_univ_map (a : ℕ) (s : powersetCard ι a) :
    Finset.univ.map (powersetCard.ofFinEmbEquiv.symm s).toEmbedding = (s : Finset ι) := by
  rw [← powersetCard.val_ofFinEmb, ← powersetCard.ofFinEmbEquiv_apply, Equiv.apply_symm_apply]

/-- The scalars extracted from the `a` wedge factors indexed by `s` multiply to `y` raised to the
number of indices of `s` lying outside `Q`. -/
private lemma prod_ite_eq_pow (y : R) (Q : Finset ι) (a : ℕ) (s : powersetCard ι a) :
    ∏ j : Fin a, (if powersetCard.ofFinEmbEquiv.symm s j ∈ Q then (1 : R) else y)
      = y ^ ((s : Finset ι) \ Q).card := by
  have h : ∏ i ∈ (s : Finset ι), (if i ∈ Q then (1 : R) else y)
      = ∏ j : Fin a, (if powersetCard.ofFinEmbEquiv.symm s j ∈ Q then (1 : R) else y) := by
    rw [← coe_eq_univ_map a s, Finset.prod_map]
    rfl
  rw [← h, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.sdiff_eq_filter]

/-- **Divisibility of `⋀^a β` on basis vectors.** If `β` is divisible by `y` on every basis vector
outside `Q`, then on the basis vector of `⋀[R]^a G` indexed by an `a`-element finset `s` the map
`⋀^a β` is divisible by `y ^ #(s \ Q)`, the explicit cofactor being the wedge of the `β' i` for
`i ∈ s`. -/
private lemma map_basis_apply (b : Module.Basis ι R G) (y : R) (β : G →ₗ[R] F)
    (Q : Finset ι) (β' : ι → F)
    (hβ' : ∀ i, β (b i) = (if i ∈ Q then (1 : R) else y) • β' i) (a : ℕ)
    (s : powersetCard ι a) :
    map a β (b.exteriorPower a s) =
      y ^ ((s : Finset ι) \ Q).card • ιMulti_family R a β' s := by
  rw [basis_apply, map_apply_ιMulti_family, ιMulti_family, ιMulti_family]
  have h : ((β ∘ b) ∘ (powersetCard.ofFinEmbEquiv.symm s)) =
      fun j => (if powersetCard.ofFinEmbEquiv.symm s j ∈ Q then (1 : R) else y) •
        (β' ∘ powersetCard.ofFinEmbEquiv.symm s) j :=
    funext fun _ => hβ' _
  rw [h, (ιMulti R a).map_smul_univ, prod_ite_eq_pow]

/-- **The counting step.** An `a`-element finset `s` meets `Q` in at most `#Q ≤ r` elements, so at
least `a - r` of its elements lie outside `Q`; equivalently `a ≤ r + #(s \ Q)`. -/
private lemma le_add_card_sdiff (Q : Finset ι) {r a : ℕ} (hr : Q.card ≤ r)
    (s : powersetCard ι a) : a ≤ r + ((s : Finset ι) \ Q).card := by
  have h := Finset.card_sdiff_add_card_inter (s : Finset ι) Q
  have h2 : ((s : Finset ι) ∩ Q).card ≤ r :=
    le_trans (Finset.card_le_card Finset.inter_subset_right) hr
  rw [powersetCard.card_eq] at h
  omega

/-- **A retraction of `⋀^a α` up to `y ^ r`, with `r` independent of `a`.**

Let `G` be free on a linearly ordered index type, let `β : G →ₗ[R] F` be a retraction of
`α : F →ₗ[R] G` up to `y` (that is, `α ∘ₗ β = y • id`), and suppose `β` is divisible by `y` on
every basis vector whose index lies outside a finite set `Q`. Then for any `r ≥ #Q` and any `a`,
the induced map `⋀^a α` admits a retraction up to `y ^ r`, provided `y` acts injectively on
`⋀[R]^a G`.

The exponent `r` does not depend on `a`: a wedge of `a` basis vectors uses at most `#Q` indices
from `Q`, so `⋀^a β` is divisible by `y` to a power that compensates all but `r` of the `a` factors
of `y` lost in `α ∘ₗ β = y • id`. -/
theorem exists_comp_map_eq_pow_smul (b : Module.Basis ι R G) (y : R)
    (α : F →ₗ[R] G) (β : G →ₗ[R] F) (hαβ : α ∘ₗ β = y • LinearMap.id)
    (Q : Finset ι) (β' : ι → F)
    (hβ' : ∀ i, β (b i) = (if i ∈ Q then (1 : R) else y) • β' i)
    {r a : ℕ} (hr : Q.card ≤ r) (hy : ∀ z : ⋀[R]^a G, y • z = 0 → z = 0) :
    ∃ ψ : (⋀[R]^a G) →ₗ[R] (⋀[R]^a F), map a α ∘ₗ ψ = (y ^ r) • LinearMap.id := by
  refine ⟨(b.exteriorPower a).constr R fun s =>
    y ^ (r + ((s : Finset ι) \ Q).card - a) • ιMulti_family R a β' s, ?_⟩
  refine (b.exteriorPower a).ext fun s => ?_
  set k := ((s : Finset ι) \ Q).card
  refine eq_of_pow_smul_eq_pow_smul hy k ?_
  calc y ^ k • (map a α ∘ₗ (b.exteriorPower a).constr R fun s =>
          y ^ (r + ((s : Finset ι) \ Q).card - a) • ιMulti_family R a β' s)
          (b.exteriorPower a s)
      = y ^ (r + k - a) • (y ^ k • map a α (ιMulti_family R a β' s)) := by
        rw [LinearMap.comp_apply, Module.Basis.constr_basis, map_smul, smul_comm]
    _ = y ^ (r + k - a) • map a α (map a β (b.exteriorPower a s)) := by
        rw [map_basis_apply b y β Q β' hβ' a s, map_smul]
    _ = y ^ (r + k - a) • (y ^ a • b.exteriorPower a s) := by
        rw [← LinearMap.comp_apply, ← map_comp, hαβ, map_smul_id]
        simp
    _ = y ^ k • ((y ^ r) • LinearMap.id (b.exteriorPower a s)) := by
        rw [smul_smul, ← pow_add, Nat.sub_add_cancel (le_add_card_sdiff Q hr s),
          LinearMap.id_apply, smul_smul, ← pow_add, add_comm k r]

/-- A non-zero-divisor of `R` acts injectively on the exterior powers of a free module: it does so
on each coordinate with respect to the induced basis. -/
theorem eq_zero_of_smul_eq_zero (b : Module.Basis ι R G) {y : R}
    (hy : y ∈ nonZeroDivisors R) (a : ℕ) (z : ⋀[R]^a G) (hz : y • z = 0) : z = 0 := by
  refine (b.exteriorPower a).repr.injective ?_
  rw [map_zero]
  ext s
  simpa using mem_nonZeroDivisors_iff_left.mp hy _
    (by simpa using congrArg (fun w => (b.exteriorPower a).repr w s) hz)

/-- The convenient form of `exteriorPower.exists_comp_map_eq_pow_smul`: since `G` is free, it is
enough to know that `y` is a non-zero-divisor of `R` for it to act injectively on `⋀[R]^a G`. -/
theorem exists_comp_map_eq_pow_smul_of_mem_nonZeroDivisors (b : Module.Basis ι R G) {y : R}
    (hy : y ∈ nonZeroDivisors R) (α : F →ₗ[R] G) (β : G →ₗ[R] F)
    (hαβ : α ∘ₗ β = y • LinearMap.id) (Q : Finset ι) (β' : ι → F)
    (hβ' : ∀ i, β (b i) = (if i ∈ Q then (1 : R) else y) • β' i)
    {r a : ℕ} (hr : Q.card ≤ r) :
    ∃ ψ : (⋀[R]^a G) →ₗ[R] (⋀[R]^a F), map a α ∘ₗ ψ = (y ^ r) • LinearMap.id :=
  exists_comp_map_eq_pow_smul b y α β hαβ Q β' hβ' hr (eq_zero_of_smul_eq_zero b hy a)

/-- **The retraction, with the divisibility hypothesis split into its two cases.** This is
`exteriorPower.exists_comp_map_eq_pow_smul_of_mem_nonZeroDivisors` with the single `if`-shaped
hypothesis replaced by the two implications it packages, which is the form a consumer can
discharge without having to match the decidability instance of the `if`. -/
theorem exists_comp_map_eq_pow_smul_of_forall (b : Module.Basis ι R G) {y : R}
    (hy : y ∈ nonZeroDivisors R) (α : F →ₗ[R] G) (β : G →ₗ[R] F)
    (hαβ : α ∘ₗ β = y • LinearMap.id) (Q : Finset ι) (β' : ι → F)
    (hmem : ∀ i ∈ Q, β (b i) = β' i) (hnotmem : ∀ i ∉ Q, β (b i) = y • β' i)
    {r a : ℕ} (hr : Q.card ≤ r) :
    ∃ ψ : (⋀[R]^a G) →ₗ[R] (⋀[R]^a F), map a α ∘ₗ ψ = (y ^ r) • LinearMap.id :=
  exists_comp_map_eq_pow_smul_of_mem_nonZeroDivisors b hy α β hαβ Q β'
    (fun i => by
      split_ifs with h
      · rw [hmem i h, one_smul]
      · rw [hnotmem i h]) hr

end exteriorPower

end
