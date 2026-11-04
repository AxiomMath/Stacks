module

public import StacksFrontier.Homology.Eta.Perfect.DeterminantalIdealLocalPrincipality

/-!
# The normalized determinantal product of a bounded complex

Let `A` be a commutative ring, `f ∈ A` a nonzerodivisor and `M^•` a bounded complex of finite
free `A`-modules. The determinantal ideals `I_i(M^•, f) ⊆ A` are not invariant under replacing
`M^•` by another complex representing the same object of `D(A)`; instead
`f^m I_i(M^•, f) = f^n I_i(N^•, f)` whenever `m + χ_i(M^•) = n + χ_i(N^•)`, where
`χ_i(M^•) = ∑_{j ≥ i} (-1)^{j-i} rk(M^j)` is the tail Euler characteristic.

The *normalized* determinantal ideals `f^{q - χ_i(M^•)} I_i(M^•, f)`, for a bound `q ≥ χ_i(M^•)`,
and their finite product over a finite set of degrees are invariants: two complexes representing
isomorphic objects of the derived category have the same normalized product, even after the
nonzerodivisor is replaced by a unit multiple of itself.

## Main definitions

* `BoundedComplex.normalizedExponent`: the exponent `q - χ_i(M^•)`, as a natural number.
* `BoundedComplex.normalizedProduct`: the ideal `∏_{i ∈ s} f^{q - χ_i(M^•)} I_i(M^•, f)`.

## Main results

* `BoundedComplex.normalizedProduct_eq_pow_mul`: the normalizing factors come out of the product
  as a single power of `f`, leaving `∏_{i ∈ s} I_i(M^•, f)`.
* `BoundedComplex.pow_mem_normalizedProduct`: a power of `f` lies in the normalized product.
* `BoundedComplex.normalizedProduct_fg`: the normalized product is finitely generated.
* `BoundedComplex.map_normalizedProduct`: it commutes with base change.
* `BoundedComplex.normalizedProduct_eq_of_derived_iso_unit` and
  `BoundedComplex.map_normalizedProduct_eq_of_derived_iso_unit`: **the invariance**, over one
  ring and after base change to a common ring.

## Implementation notes

The exponent is `((q : ℤ) - χ_i(M^•)).toNat`, which is the intended `q - χ_i(M^•)` exactly when
`χ_i(M^•) ≤ q`; every statement that uses its defining property takes that bound as a hypothesis,
through `BoundedComplex.normalizedExponent_add`.

## References

* [Stacks Project, Tag 0GSS](https://stacks.math.columbia.edu/tag/0GSS)
* [Stacks Project, Tag 0GST](https://stacks.math.columbia.edu/tag/0GST)
* [Stacks Project, Tag 0GSU](https://stacks.math.columbia.edu/tag/0GSU)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Eta.DeterminantalIdeal

variable {A : Type u} [CommRing A]

private theorem prod_pow_mul_idealI_eq_pow_mul (f : A) (M : BoundedComplex A) (s : Finset ℤ)
    (m : ℤ → ℕ) :
    (∏ i ∈ s, Ideal.span {f ^ m i} * idealI M f i)
      = Ideal.span {f ^ (∑ i ∈ s, m i)} * ∏ i ∈ s, idealI M f i := by
  rw [Finset.prod_mul_distrib, Ideal.prod_span_singleton, Finset.prod_pow_eq_pow_sum]

private theorem pow_mem_prod_pow_mul_idealI (f : A) (M : BoundedComplex A) (s : Finset ℤ)
    (m : ℤ → ℕ) :
    f ^ (∑ i ∈ s, (m i + M.rank i)) ∈ ∏ i ∈ s, Ideal.span {f ^ m i} * idealI M f i := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Ideal.prod_mem_prod fun i _ => ?_
  rw [pow_add]
  exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton _)) (pow_rank_mem_idealI M f i)

private theorem fg_prod_pow_mul_idealI (f : A) (M : BoundedComplex A) (s : Finset ℤ)
    (m : ℤ → ℕ) : (∏ i ∈ s, Ideal.span {f ^ m i} * idealI M f i).FG :=
  Finset.prod_induction _ Submodule.FG (fun _ _ => Submodule.FG.mul) ⟨{1}, by simp⟩ fun i _ =>
    (Submodule.fg_span_singleton _).mul (Stacks.DeterminantalIdeal.fg_idealI M f i)

private theorem map_prod_pow_mul_idealI {B : Type u} [CommRing B] (φ : A →+* B) (f : A)
    (M : BoundedComplex A) (s : Finset ℤ) (m : ℤ → ℕ) :
    Ideal.map φ (∏ i ∈ s, Ideal.span {f ^ m i} * idealI M f i)
      = ∏ i ∈ s, Ideal.span {φ f ^ m i} * idealI (M.baseChange φ) (φ f) i := by
  rw [← Ideal.mapHom_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Ideal.mapHom_apply, Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_pow,
    map_idealI_eq_idealI_baseChange]

end Stacks.Eta.DeterminantalIdeal

namespace BoundedComplex

open Stacks.Eta.DeterminantalIdeal

variable {A : Type u} [CommRing A]

/-- The exponent `q - χ_i(M^•)` normalizing the `i`-th determinantal ideal, where
`χ_i(M^•) = ∑_{j ≥ i} (-1)^{j-i} rk(M^j)` is the tail Euler characteristic. -/
def normalizedExponent (M : BoundedComplex A) (q : ℕ) (i : ℤ) : ℕ :=
  ((q : ℤ) - M.tailEulerCharacteristic i).toNat

/-- If `χ_i(M^•) ≤ q`, then `(q - χ_i(M^•)) + χ_i(M^•) = q`. -/
theorem normalizedExponent_add (M : BoundedComplex A) {q : ℕ} {i : ℤ}
    (h : M.tailEulerCharacteristic i ≤ (q : ℤ)) :
    ((M.normalizedExponent q i : ℕ) : ℤ) + M.tailEulerCharacteristic i = q := by
  rw [normalizedExponent, Int.toNat_of_nonneg (sub_nonneg.mpr h)]
  ring

/-- The **normalized determinantal product** `∏_{i ∈ s} f^{q - χ_i(M^•)} I_i(M^•, f)` over a
finite set `s` of degrees and a bound `q` on the tail Euler characteristics. -/
def normalizedProduct (M : BoundedComplex A) (f : A) (s : Finset ℤ) (q : ℕ) : Ideal A :=
  ∏ i ∈ s, Ideal.span {f ^ M.normalizedExponent q i} * idealI M f i

/-- The normalizing factors come out of the product as a single power of `f`. -/
theorem normalizedProduct_eq_pow_mul (M : BoundedComplex A) (f : A) (s : Finset ℤ) (q : ℕ) :
    M.normalizedProduct f s q
      = Ideal.span {f ^ (∑ i ∈ s, M.normalizedExponent q i)} * ∏ i ∈ s, idealI M f i :=
  prod_pow_mul_idealI_eq_pow_mul f M s (M.normalizedExponent q)

/-- A power of `f` lies in the normalized product, since `f^{r_i} ∈ I_i(M^•, f)`. -/
theorem pow_mem_normalizedProduct (M : BoundedComplex A) (f : A) (s : Finset ℤ) (q : ℕ) :
    f ^ (∑ i ∈ s, (M.normalizedExponent q i + M.rank i)) ∈ M.normalizedProduct f s q :=
  pow_mem_prod_pow_mul_idealI f M s (M.normalizedExponent q)

/-- The normalized product is finitely generated. -/
theorem normalizedProduct_fg (M : BoundedComplex A) (f : A) (s : Finset ℤ) (q : ℕ) :
    (M.normalizedProduct f s q).FG :=
  fg_prod_pow_mul_idealI f M s (M.normalizedExponent q)

/-- The normalized product commutes with base change, the tail Euler characteristics and hence
the normalizing exponents being unchanged. -/
theorem map_normalizedProduct {B : Type u} [CommRing B] (φ : A →+* B) (M : BoundedComplex A)
    (f : A) (s : Finset ℤ) (q : ℕ) :
    Ideal.map φ (M.normalizedProduct f s q) = (M.baseChange φ).normalizedProduct (φ f) s q :=
  map_prod_pow_mul_idealI φ f M s (M.normalizedExponent q)

/-- **Two complexes representing isomorphic objects have the same normalized product**, even
after replacing the nonzerodivisor by a unit multiple of it. -/
theorem normalizedProduct_eq_of_derived_iso_unit (f : A) (hf : f ∈ nonZeroDivisors A) (u : Aˣ)
    (M N : BoundedComplex A) (s : Finset ℤ) (q : ℕ)
    (hMN : Nonempty ((DerivedCategory.Q).obj M.toCochainComplex ≅
      (DerivedCategory.Q).obj N.toCochainComplex))
    (hM : ∀ i ∈ s, M.tailEulerCharacteristic i ≤ (q : ℤ))
    (hN : ∀ i ∈ s, N.tailEulerCharacteristic i ≤ (q : ℤ)) :
    M.normalizedProduct f s q = N.normalizedProduct ((u : A) * f) s q := by
  classical
  refine Finset.prod_congr rfl fun i hi => ?_
  have hspan : Ideal.span {((u : A) * f) ^ N.normalizedExponent q i}
      = Ideal.span {f ^ N.normalizedExponent q i} := by
    rw [mul_pow]
    exact Ideal.span_singleton_mul_left_unit (u.isUnit.pow _) _
  rw [hspan, ← idealI_unit_mul_eq N f u i]
  exact pow_mul_idealI_eq_of_derived_iso f hf M N i _ _ hMN
    ((M.normalizedExponent_add (hM i hi)).trans (N.normalizedExponent_add (hN i hi)).symm)

/-- **The normalized products of two complexes over different rings agree after base change to a
common ring**, when the base-changed complexes represent isomorphic objects there and the two
nonzerodivisors become unit multiples of one another. -/
theorem map_normalizedProduct_eq_of_derived_iso_unit {B R : Type u} [CommRing B] [CommRing R]
    (φ : A →+* R) (ψ : B →+* R) (f : A) (g : B) (M : BoundedComplex A) (N : BoundedComplex B)
    (u : Rˣ) (s : Finset ℤ) (q : ℕ) (hfR : φ f ∈ nonZeroDivisors R)
    (hMN : Nonempty ((DerivedCategory.Q).obj (M.baseChange φ).toCochainComplex ≅
      (DerivedCategory.Q).obj (N.baseChange ψ).toCochainComplex))
    (heq : ψ g = (u : R) * φ f)
    (hM : ∀ i ∈ s, M.tailEulerCharacteristic i ≤ (q : ℤ))
    (hN : ∀ i ∈ s, N.tailEulerCharacteristic i ≤ (q : ℤ)) :
    Ideal.map φ (M.normalizedProduct f s q) = Ideal.map ψ (N.normalizedProduct g s q) := by
  rw [map_normalizedProduct, map_normalizedProduct, heq]
  exact normalizedProduct_eq_of_derived_iso_unit (φ f) hfR u (M.baseChange φ) (N.baseChange ψ)
    s q hMN hM hN

end BoundedComplex

end
