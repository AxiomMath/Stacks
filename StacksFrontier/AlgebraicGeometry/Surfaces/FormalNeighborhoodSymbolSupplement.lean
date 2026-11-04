module

public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodSymbol
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.DegreewiseSymbol
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodFiltration
public import StacksFrontier.RingTheory.MvPolynomial.BinaryFormBasis

/-!
# Monomial symbol systems as degreewise symbol systems

For a monomial symbol system `S`, the filtration ideal `Iₙ₊₁` lies in `I₁ · Iₙ + Iₙ₊₂`, and,
over a field and for a decreasing filtration, `S` is a degreewise symbol system with residue map
the degree-zero symbol.

These are results about the objects of
`StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodSymbol` that need imports beyond those
of that module.

## Main definitions

* `MonomialSymbol.scalarHom`: The degree-zero symbol, as a ring homomorphism `A →+* k`.
* `MonomialSymbol.toDegreewiseSymbol`: A monomial symbol system with decreasing filtration, as a
  degreewise symbol system.

## Main results

* `MonomialSymbol.ideal_succ_le_mul_ideal_sup`: `Iₙ₊₁ ≤ I₁ · Iₙ ⊔ Iₙ₊₂`.
* `MonomialSymbol.surjective_symbol_mem`: Every binary form of degree `n` is the symbol of an
  element of `Iₙ`.
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace AlgebraicGeometry.SemistableReduction

namespace MonomialSymbol

variable {A : Type u} [CommRing A] {k : Type u} [CommRing k] (S : MonomialSymbol A k)

variable {x y : A} (hx : x ∈ S.ideal 1) (hy : y ∈ S.ideal 1)

/-- **The associated graded ring of a monomial symbol system is generated in degree one**:
`Iₙ₊₁ ≤ I₁ · Iₙ ⊔ Iₙ₊₂`. `Iₙ₊₁` is spanned by the degree-`(n + 1)` monomials in the two generators
modulo `Iₙ₊₂`, and those lie in `I₁ · Iₙ`, because the generators lie in `I₁` and the powers of
`I₁` sit inside the filtration.  This is the one statement about the filtration that stands in for
multiplicativity of the symbol in `AlgebraicGeometry.SemistableReduction.DegreewiseSymbol`. -/
theorem ideal_succ_le_mul_ideal_sup (n : ℕ) :
    S.ideal (n + 1) ≤ S.ideal 1 * S.ideal n ⊔ S.ideal (n + 2) := by
  have hpow : Ideal.span ({S.gen₁, S.gen₂} : Set A) ^ (n + 1) ≤ S.ideal 1 * S.ideal n := by
    rw [pow_succ']
    exact Ideal.mul_mono S.span_gen_le_ideal_one
      ((pow_le_pow_left' S.span_gen_le_ideal_one n).trans (S.ideal_one_pow_le n))
  have h := S.ideal_le_span_gen_pow_sup (n + 1)
  rw [show n + 1 + 1 = n + 2 from rfl] at h
  exact h.trans (sup_le (le_sup_of_le_left hpow) le_sup_right)

end MonomialSymbol

/-! ### A monomial symbol system is a degreewise symbol system -/

namespace MonomialSymbol

variable {A : Type u} [CommRing A] {k : Type u} [Field k] (S : MonomialSymbol A k)

/-- The degree-zero symbol of a monomial symbol system, as a ring homomorphism `A ⟶ k`: the
residue map of the filtration, `A ⟶ A / I₁ = k`. -/
def scalarHom : A →+* k where
  toFun a := MvPolynomial.constantCoeff (S.symbol 0 a)
  map_one' := by rw [S.symbol_one]; simp
  map_mul' a b := by
    have h := S.symbol_mul 0 0 (S.mem_ideal_zero a) (S.mem_ideal_zero b)
    rw [zero_add] at h
    rw [h, map_mul]
  map_zero' := by rw [S.symbol_zero 0]; simp
  map_add' a b := by
    rw [S.symbol_add 0 (S.mem_ideal_zero a) (S.mem_ideal_zero b), map_add]

/-- The residue map sends `a` to the constant coefficient of its degree-zero symbol. -/
@[simp]
theorem scalarHom_apply (a : A) :
    S.scalarHom a = MvPolynomial.constantCoeff (S.symbol 0 a) := rfl

/-- The degree-zero symbol is the constant with value the residue. -/
theorem symbol_zero_eq_C (a : A) : S.symbol 0 a = MvPolynomial.C (S.scalarHom a) := by
  obtain ⟨c, hc⟩ := S.exists_symbol_zero_eq_C a
  rw [hc, scalarHom_apply, hc, MvPolynomial.constantCoeff_C]

/-- The kernel of the residue map is `I₁`. -/
theorem ker_scalarHom : RingHom.ker S.scalarHom = S.ideal 1 := by
  ext a
  rw [RingHom.mem_ker, S.mem_ideal_one_iff, S.symbol_zero_eq_C a, MvPolynomial.C_eq_zero]

/-- The residue map is surjective. -/
theorem surjective_scalarHom : Function.Surjective S.scalarHom := by
  intro c
  obtain ⟨a, ha⟩ := S.surjective_symbol_zero c
  exact ⟨a, by rw [scalarHom_apply, ha, MvPolynomial.constantCoeff_C]⟩

/-- The symbol is semilinear over the residue map. -/
theorem symbol_smul_scalarHom (n : ℕ) (c : A) {a : A} (ha : a ∈ S.ideal n) :
    S.symbol n (c * a) = S.scalarHom c • S.symbol n a := by
  have h := S.symbol_mul 0 n (S.mem_ideal_zero c) ha
  rw [zero_add, S.symbol_zero_eq_C c] at h
  rw [h, MvPolynomial.smul_eq_C_mul]

/-- **Every binary form of degree `n` is the symbol of an element of `Iₙ`**: it is a combination
of the degree-`n` monomials, and those are the symbols of the monomials in the two
generators. -/
theorem surjective_symbol_mem (n : ℕ) (v : MvPolynomial (Fin 2) k)
    (hv : v ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k n) :
    ∃ a ∈ S.ideal n, S.symbol n a = v := by
  obtain ⟨lam, hlam⟩ := exists_eq_sum_binaryMonomial n v hv
  choose c hc using fun j : ℕ => S.surjective_symbol_zero (lam j)
  have hterm : ∀ j ∈ Finset.range (n + 1),
      c j * genMonomial S.gen₁ S.gen₂ n j ∈ S.ideal n := fun j hj =>
    Ideal.mul_mem_left _ _ (S.genMonomial_mem_ideal S.gen₁_mem S.gen₂_mem
      (Finset.mem_range_succ_iff.1 hj))
  refine ⟨∑ j ∈ Finset.range (n + 1), c j * genMonomial S.gen₁ S.gen₂ n j,
    Submodule.sum_mem _ hterm, ?_⟩
  rw [S.symbol_sum_range n (n + 1) _ hterm, hlam]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [S.symbol_mul_genMonomial S.gen₁_mem S.gen₂_mem S.symbol_gen₁ S.symbol_gen₂
    (Finset.mem_range_succ_iff.1 hj) (c j), hc j, MvPolynomial.smul_eq_C_mul]

/-- **A monomial symbol system is a degreewise symbol system**, for a decreasing filtration, with
the same filtration and symbols, and with residue map the degree-zero symbol `scalarHom`.

Everything a degreewise symbol system asks for is available: the residue map is the degree-zero
symbol, semilinearity and surjectivity of the symbols are the multiplicativity of the symbol
read in degrees `(0, n)` and the monomial basis of the degree-`n` forms.  So the hypothesis
bundle of `AlgebraicGeometry.SemistableReduction.DegreewiseSymbol` together with degree-one
generation, `AlgebraicGeometry.SemistableReduction.MonomialSymbol.ideal_succ_le_mul_ideal_sup`,
is no stronger than a monomial symbol system — and it is consistent, a witness being the
leading-form filtration of `k[T₀, T₁]`,
`AlgebraicGeometry.SemistableReduction.binaryPolynomialMonomialSymbol`. -/
def toDegreewiseSymbol (hanti : ∀ n, S.ideal (n + 1) ≤ S.ideal n) : DegreewiseSymbol A k where
  ideal := S.ideal
  scalar := S.scalarHom
  symbol := S.symbol
  ideal_zero := S.ideal_zero
  ideal_succ_le := hanti
  mul_le := S.mul_le
  ker_scalar := S.ker_scalarHom
  surjective_scalar := S.surjective_scalarHom
  symbol_mem := S.symbol_mem
  symbol_add := S.symbol_add
  symbol_smul := fun n c _ ha => S.symbol_smul_scalarHom n c ha
  symbol_eq_zero_iff := S.symbol_eq_zero_iff
  surjective_symbol := S.surjective_symbol_mem

/-- The filtration of `S.toDegreewiseSymbol hanti` is that of `S`. -/
@[simp]
theorem toDegreewiseSymbol_ideal (hanti : ∀ n, S.ideal (n + 1) ≤ S.ideal n) :
    (S.toDegreewiseSymbol hanti).ideal = S.ideal := rfl

end MonomialSymbol

end AlgebraicGeometry.SemistableReduction
