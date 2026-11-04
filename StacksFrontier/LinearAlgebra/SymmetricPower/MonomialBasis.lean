module

public import StacksFrontier.LinearAlgebra.SymmetricPower.FreePresentation

/-!
# The monomial basis of a symmetric power, computed on basis elements

`SymPow.basisSymmetricPower b n` is the basis of the `n`-th symmetric power
`SymPow.symmetricPower n R M` of a module with a basis `b : Module.Basis κ R M`, indexed by the
degree-`n` multidegrees `{d : κ →₀ ℕ | d.degree = n}`. It is built in
`StacksFrontier.LinearAlgebra.SymmetricPower.FreePresentation` by transporting the monomial basis
`MvPolynomial.basisHomogeneousSubmodule` of the degree-`n` homogeneous part of a polynomial ring
along `SymmetricAlgebra.equivMvPolynomial b`, and that construction says nothing about the value
of the basis at a multidegree. On the polynomial side the value is
`MvPolynomial.coe_basisHomogeneousSubmodule_apply`, in
`StacksFrontier.RingTheory.MvPolynomial.HomogeneousBasis`; this file carries it across to the
symmetric algebra, where the basis element at `d` is the monomial

`∏ i ∈ d.support, (SymmetricAlgebra.ι R M (b i)) ^ d i`

in `SymmetricAlgebra R M`.

## Main results

* `SymPow.coe_symmetricPowerEquivHomogeneousSubmodule_apply` : the comparison
  `SymPow.symmetricPowerEquivHomogeneousSubmodule` is `SymmetricAlgebra.equivMvPolynomial` read on
  underlying elements.
* `SymPow.coe_symmetricPowerEquivHomogeneousSubmodule_symm_C` : **the degree-`0` value of the
  comparison**, the constant polynomial `C r` corresponding to `r • 1`.
* `SymPow.coe_basisSymmetricPower_apply` : **the monomial formula**, the value of
  `SymPow.basisSymmetricPower b n` at a multidegree `d`, as a product over `d.support`.
* `SymPow.coe_basisSymmetricPower_apply_eq_prod_univ` : the same formula with the product taken
  over all of `κ`, for `κ` a `Fintype`.
* `SymPow.exists_prod_ι_eq_coe_basisSymmetricPower` : every basis element is a product of exactly
  `n` degree-one generators, indexed by `Fin n`.
* `Finsupp.prod_map_toMultiset` : an auxiliary computation of the product of a multiset obtained
  by relabelling `Finsupp.toMultiset`.

## Implementation notes

**The degree is kept a variable in every statement below.** `SymmetricAlgebra R M` is a reducible
`abbrev` for a `RingCon` quotient of `TensorAlgebra R M` and `SymPow.symmetricPower n R M` is
`LinearMap.range (SymmetricAlgebra.ι R M) ^ n`, so with `n` a numeral the elaborator unfolds the
power through `Submodule.mul` and `Submodule.span` and then through the quotient; a statement with
a literal degree can fail to elaborate even when the proof body is left unproved. Instantiating
`n` in an already-elaborated statement is harmless, so literal degrees belong at the point of use.

**Why the statements are about the coercion to `SymmetricAlgebra R M` rather than about elements
of the submodule.** `SymPow.symmetricPower n R M` is a `Submodule`, so a basis element is a
subtype element whose membership proof is irrelevant; a product of generators is naturally an
element of the ambient algebra, and equating the two in the submodule would mean carrying a
membership proof in the statement.

**The product over `d.support` is the primitive form.** It needs no finiteness of `κ`, and it is
the shape of `MvPolynomial.prod_X_pow_eq_monomial`. The `Fintype` form over all of `κ` follows by
`Finsupp.prod_fintype`, since the exponent-zero factors are `1`.

## References

* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

namespace Finsupp

/-- The product of a multiset obtained by relabelling `Finsupp.toMultiset` along `g` is the
product of the `g`-images raised to the multiplicities. -/
theorem prod_map_toMultiset {κ : Type*} {β : Type*} [CommMonoid β] (d : κ →₀ ℕ) (g : κ → β) :
    (d.toMultiset.map g).prod = d.prod fun i e => g i ^ e := by
  rw [toMultiset_map, prod_toMultiset,
    prod_mapDomain_index (h := fun (x : β) (e : ℕ) => x ^ e) (fun _ => pow_zero _)
      fun _ _ _ => pow_add _ _ _]

end Finsupp

namespace MvPolynomial

variable (σ R : Type*) [CommRing R] (n : ℕ)

/-- A constant is homogeneous of degree `0`. -/
theorem C_mem_homogeneousSubmodule_zero (r : R) :
    (C r : MvPolynomial σ R) ∈ homogeneousSubmodule σ R 0 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_C _ _)

end MvPolynomial

namespace SymPow

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The comparison of `Symⁿ(M)` with the degree-`n` homogeneous part of the polynomial ring on a
basis is `SymmetricAlgebra.equivMvPolynomial` read on underlying elements. -/
theorem coe_symmetricPowerEquivHomogeneousSubmodule_apply {κ : Type*} (b : Module.Basis κ R M)
    (n : ℕ) (x : symmetricPower n R M) :
    ((symmetricPowerEquivHomogeneousSubmodule b n x :
        MvPolynomial.homogeneousSubmodule κ R n) : MvPolynomial κ R) =
      SymmetricAlgebra.equivMvPolynomial b (x : SymmetricAlgebra R M) :=
  rfl

/-- **The degree-`0` part of the comparison.** The inverse comparison carries the constant
polynomial `C r` to the scalar multiple `r • 1` of the unit of the symmetric algebra, which is
the image of `r` under the structure map. -/
theorem coe_symmetricPowerEquivHomogeneousSubmodule_symm_C {κ : Type*} (b : Module.Basis κ R M)
    (r : R) :
    (((symmetricPowerEquivHomogeneousSubmodule b 0).symm
          ⟨MvPolynomial.C r, MvPolynomial.C_mem_homogeneousSubmodule_zero κ R r⟩ :
        symmetricPower 0 R M) : SymmetricAlgebra R M) = r • 1 := by
  have h := coe_symmetricPowerEquivHomogeneousSubmodule_apply b 0
    ((symmetricPowerEquivHomogeneousSubmodule b 0).symm
      ⟨MvPolynomial.C r, MvPolynomial.C_mem_homogeneousSubmodule_zero κ R r⟩)
  rw [LinearEquiv.apply_symm_apply] at h
  refine (SymmetricAlgebra.equivMvPolynomial b).injective ?_
  rw [← h]
  show (MvPolynomial.C r : MvPolynomial κ R) = _
  rw [map_smul, map_one, ← Algebra.algebraMap_eq_smul_one, MvPolynomial.algebraMap_eq]

/-- **The monomial formula for the basis of a symmetric power.** For a basis `b` of `M` and a
multidegree `d` of total degree `n`, the basis element `SymPow.basisSymmetricPower b n d` is the
monomial `∏ i ∈ d.support, (ι (b i)) ^ d i` in `SymmetricAlgebra R M`. -/
theorem coe_basisSymmetricPower_apply {κ : Type*} (b : Module.Basis κ R M) (n : ℕ)
    (d : {d : κ →₀ ℕ | d.degree = n}) :
    ((basisSymmetricPower b n d : symmetricPower n R M) : SymmetricAlgebra R M) =
      ∏ i ∈ (d : κ →₀ ℕ).support, SymmetricAlgebra.ι R M (b i) ^ (d : κ →₀ ℕ) i := by
  refine (SymmetricAlgebra.equivMvPolynomial b).injective ?_
  rw [map_prod]
  simp only [map_pow, SymmetricAlgebra.equivMvPolynomial_ι_apply,
    MvPolynomial.prod_X_pow_eq_monomial]
  rw [← coe_symmetricPowerEquivHomogeneousSubmodule_apply b n, basisSymmetricPower,
    Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    MvPolynomial.coe_basisHomogeneousSubmodule_apply]

/-- The monomial formula of `SymPow.coe_basisSymmetricPower_apply` with the product taken over all
of a finite index type: the factors at exponent zero are `1`. -/
theorem coe_basisSymmetricPower_apply_eq_prod_univ {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) (n : ℕ) (d : {d : κ →₀ ℕ | d.degree = n}) :
    ((basisSymmetricPower b n d : symmetricPower n R M) : SymmetricAlgebra R M) =
      ∏ i, SymmetricAlgebra.ι R M (b i) ^ (d : κ →₀ ℕ) i := by
  rw [coe_basisSymmetricPower_apply]
  exact (d : κ →₀ ℕ).prod_fintype _ fun _ => pow_zero _

/-- **Every basis element of `Symⁿ(M)` is a product of exactly `n` degree-one generators.** -/
theorem exists_prod_ι_eq_coe_basisSymmetricPower {κ : Type*} (b : Module.Basis κ R M) (n : ℕ)
    (d : {d : κ →₀ ℕ | d.degree = n}) :
    ∃ s : Fin n → M, ∏ i : Fin n, SymmetricAlgebra.ι R M (s i) =
      ((basisSymmetricPower b n d : symmetricPower n R M) : SymmetricAlgebra R M) := by
  set l : List M := ((d : κ →₀ ℕ).toMultiset.map b).toList with hl
  have hlen : l.length = n := by
    rw [hl, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
    exact d.2
  refine ⟨fun i => l[(i.cast hlen.symm : Fin l.length).1], ?_⟩
  rw [coe_basisSymmetricPower_apply]
  rw [Fin.prod_congr' (fun i : Fin l.length => SymmetricAlgebra.ι R M l[i.1]) hlen.symm,
    ← Fin.prod_ofFn, List.ofFn_getElem_eq_map, hl, ← Multiset.prod_coe, ← Multiset.map_coe,
    Multiset.coe_toList, Multiset.map_map, Finsupp.prod_map_toMultiset, Finsupp.prod]
  exact Finset.prod_congr rfl fun i _ => rfl

end SymPow

end
