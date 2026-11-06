module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Ideal.Operations
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.SetTheory.Cardinal.Order
public import StacksFrontier.RingTheory.Koszul.Defs
public import StacksFrontier.RingTheory.Koszul.Relations
public import StacksFrontier.RingTheory.Tor.Balancing
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The Koszul complex of the variables of a polynomial ring

Let `A` be a commutative ring and `E` a type, and let `P = A[E]`.  The Koszul complex of the
dual sending each basis vector to the corresponding variable is a free resolution of `A` over
`P`, and it carries an `A`-linear contracting homotopy: contraction against the smallest
variable occurring in a monomial.  That contraction lowers the filtration of `K_j` by the
powers of the ideal of variables by exactly one, which is the mechanism behind Tag 08RE.

This module collects the construction and all of its properties, including the contraction in
exterior degree zero and the induced contraction on `K_j ⊗_P I ^ n`.

## Main definitions

* `MvPolynomial.variableKoszulDual`: The functional sending each basis vector to its variable.
* `MvPolynomial.variableKoszulChosenContract`: The contracting homotopy of the Koszul complex,
  contracting against the smallest variable of the multidegree.
* `MvPolynomial.variableKoszulFiltration`: The filtration of `K_j` by monomial degree.
* `MvPolynomial.variableKoszulResolution`: The Koszul complex as a projective resolution of `A`.
* `MvPolynomial.koszulTensorContract`: The contraction `K_j ⊗ I ^ (n + 1) → K_(j+1) ⊗ I ^ n`.

## Main results

* `MvPolynomial.variableKoszulChosenContract_homotopy`: The contraction is a homotopy in
  positive degree.
* `MvPolynomial.variableKoszulFiltration_eq_idealPower_smul`: The `n`-th filtration step is
  `I ^ n • K_j`.
* `MvPolynomial.koszulTensorContract_homotopy`: The homotopy identity on `K_• ⊗ I ^ n`.

## References

* [Stacks Project, Tag 08RE](https://stacks.math.columbia.edu/tag/08RE)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace MvPolynomial

/-- The functional on the free module `E →₀ A[E]` sending the basis vector at `e` to the
variable `X e`. -/
noncomputable def variableKoszulDual (A : Type u) [CommRing A] (E : Type v) :
    Module.Dual (MvPolynomial E A) (E →₀ MvPolynomial E A) :=
  Finsupp.linearCombination (MvPolynomial E A) (MvPolynomial.X : E → MvPolynomial E A)

/-- `variableKoszulDual` sends the basis vector at `e` to the variable `X e`. -/
lemma variableKoszulDual_single (A : Type u) [CommRing A] (E : Type v) (e : E) :
    variableKoszulDual A E (Finsupp.single e 1) = MvPolynomial.X e := by
  simp [variableKoszulDual]

/-- The coordinate functional at `e` on the free module `E →₀ A[E]`. -/
noncomputable def variableCoordinateDual
    (A : Type u) [CommRing A] (E : Type v) (e : E) :
    Module.Dual (MvPolynomial E A) (E →₀ MvPolynomial E A) :=
  Finsupp.lapply e

/-- The coordinate functional at `e` takes the value `1` on the basis vector at `e` and `0` on
every other basis vector. -/
lemma variableCoordinateDual_single
    (A : Type u) [CommRing A] (E : Type v) [DecidableEq E] (e f : E) :
    variableCoordinateDual A E e (Finsupp.single f 1) =
      if e = f then 1 else 0 := by
  classical
  simp [variableCoordinateDual, Finsupp.single_apply, eq_comm]

/-- Under the identifications `⋀¹ M ≃ M` and `⋀⁰ M ≃ R`, the Koszul differential
`⋀¹ M → ⋀⁰ M` of `φ` is `φ`. -/
lemma koszul_zeroEquiv_d_zero {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (φ : Module.Dual R M) (x : ⋀[R]^1 M) :
    exteriorPower.zeroEquiv R M (Koszul.d φ 0 x) =
      φ (exteriorPower.oneEquiv R M x) := by
  apply Koszul.zeroEquiv_eq_of_coe
  rw [Koszul.d_apply_coe, Koszul.coe_oneEquiv,
    CliffordAlgebra.contractLeft_ι]

/-- Under the identification `⋀⁰ M ≃ R`, the image of the Koszul differential `⋀¹ M → ⋀⁰ M`
of `φ` is the range of `φ`. -/
lemma koszul_range_d_zero {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (φ : Module.Dual R M) :
    Submodule.map (exteriorPower.zeroEquiv R M).toLinearMap
      (LinearMap.range (Koszul.d φ 0)) = LinearMap.range φ := by
  rw [← LinearMap.range_comp]
  have h : (exteriorPower.zeroEquiv R M).toLinearMap.comp (Koszul.d φ 0) =
      φ.comp (exteriorPower.oneEquiv R M).toLinearMap :=
    LinearMap.ext (koszul_zeroEquiv_d_zero φ)
  rw [h, LinearMap.range_comp]
  simp

/-- Under the identification `⋀⁰ ≃ A[E]`, the image of the first differential of the Koszul
complex of the variables is the ideal generated by the variables. -/
lemma variableKoszul_range_d_zero (A : Type u) [CommRing A] (E : Type v) :
    Submodule.map (exteriorPower.zeroEquiv (MvPolynomial E A) (E →₀ MvPolynomial E A)).toLinearMap
      (LinearMap.range (Koszul.d (variableKoszulDual A E) 0)) =
        (Ideal.span (Set.range MvPolynomial.X) : Ideal (MvPolynomial E A)) := by
  rw [koszul_range_d_zero]
  simpa only [variableKoszulDual, Ideal.span] using
    (Finsupp.range_linearCombination (R := MvPolynomial E A)
      (v := (MvPolynomial.X : E → MvPolynomial E A)))

/-- The `A`-basis of `⋀^j (E →₀ A[E])` whose element indexed by `(m, s)` is the product of the
monomial `X^m` with the wedge of the basis vectors at the `j` elements of `s`. -/
noncomputable def variableKoszulTermBasis
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j : ℕ) :
    Module.Basis ((E →₀ ℕ) × {s : Finset E // s.card = j}) A
      (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) :=
  (MvPolynomial.basisMonomials E A).smulTower
    ((Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower j)

/-- The multidegree `m + ∑ e ∈ s, single e 1` of the basis element indexed by `(m, s)`. -/
noncomputable def variableKoszulMultidegree
    {E : Type v} (j : ℕ) (p : (E →₀ ℕ) × {s : Finset E // s.card = j}) : E →₀ ℕ := by
  classical
  exact p.1 + ∑ e ∈ p.2.1, Finsupp.single e 1

/-- The contraction of the basis element indexed by `(m, s)`. Let `e` be the smallest variable
in the support of its multidegree. This is zero if the multidegree is zero or `e ∈ s`, and
otherwise it is `(-1) ^ #{f ∈ s | f < e}` times the basis element indexed by
`(m - single e 1, insert e s)`. -/
noncomputable def variableKoszulContractBasis
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = j}) :
    ⋀[MvPolynomial E A]^(j + 1) (E →₀ MvPolynomial E A) := by
  classical
  let α := variableKoszulMultidegree j p
  by_cases hα : α = 0
  · exact 0
  · have hsupport : α.support.Nonempty := by
      by_contra h
      exact hα (Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp h))
    let e := α.support.min' hsupport
    by_cases he : e ∈ p.2.1
    · exact 0
    · let t : {s : Finset E // s.card = j + 1} :=
        ⟨insert e p.2.1, by simp [Finset.card_insert_of_notMem he, p.2.2]⟩
      exact (-1 : A) ^ (p.2.1.filter (· < e)).card •
        variableKoszulTermBasis A E (j + 1) (p.1 - Finsupp.single e 1, t)

/-- The `A`-linear map `⋀^j → ⋀^(j+1)` sending each element of `variableKoszulTermBasis` to
its image under `variableKoszulContractBasis`. -/
noncomputable def variableKoszulContract
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j : ℕ) :
    (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) →ₗ[A]
      (⋀[MvPolynomial E A]^(j + 1) (E →₀ MvPolynomial E A)) :=
  (variableKoszulTermBasis A E j).constr A
    (variableKoszulContractBasis A E j)

/-- `variableKoszulContract` sends the basis element indexed by `p` to
`variableKoszulContractBasis A E j p`. -/
lemma variableKoszulContract_termBasis
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = j}) :
    variableKoszulContract A E j (variableKoszulTermBasis A E j p) =
      variableKoszulContractBasis A E j p :=
  Module.Basis.constr_basis _ _ _ _

/-- Left multiplication by `e` in the exterior algebra, as a linear map
`⋀^j M → ⋀^(j+1) M`. -/
noncomputable def koszulWedge {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (e : M) (j : ℕ) :
    (⋀[R]^j M) →ₗ[R] (⋀[R]^(j + 1) M) := by
  let f : (⋀[R]^j M) →ₗ[R] ExteriorAlgebra R M :=
    (LinearMap.mulLeft R (ExteriorAlgebra.ι R e)).comp (⋀[R]^j M).subtype
  refine LinearMap.codRestrict _ f ?_
  intro x
  change ExteriorAlgebra.ι R e * (x : ExteriorAlgebra R M) ∈ ⋀[R]^(j + 1) M
  simpa only [Nat.add_comm] using
    (SetLike.mul_mem_graded (Koszul.ι_mem_one e) x.property)

/-- The Koszul differential of `φ` satisfies `d (e ∧ x) + e ∧ d x = φ e • x`. -/
lemma koszul_d_wedge_add_wedge_d {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (φ : Module.Dual R M)
    (e : M) (j : ℕ) (x : ⋀[R]^(j + 1) M) :
    Koszul.d φ (j + 1) (koszulWedge e (j + 1) x) +
      koszulWedge e j (Koszul.d φ j x) = φ e • x := by
  apply Subtype.ext
  show CliffordAlgebra.contractLeft φ
        (ExteriorAlgebra.ι R e * (x : ExteriorAlgebra R M)) +
      ExteriorAlgebra.ι R e *
        CliffordAlgebra.contractLeft φ (x : ExteriorAlgebra R M) =
      φ e • (x : ExteriorAlgebra R M)
  rw [CliffordAlgebra.contractLeft_ι_mul]
  simp [sub_eq_add_neg]

/-- For the Koszul differential `d` of the coordinate functional at `e`, wedging with the basis
vector at `e` satisfies `d (e ∧ x) + e ∧ d x = x`. -/
lemma variableCoordinate_wedge_homotopy
    (A : Type u) [CommRing A] (E : Type v) (e : E)
    (j : ℕ) (x : ⋀[MvPolynomial E A]^(j + 1) (E →₀ MvPolynomial E A)) :
    Koszul.d (variableCoordinateDual A E e) (j + 1)
        (koszulWedge (Finsupp.single e 1) (j + 1) x) +
      koszulWedge (Finsupp.single e 1) j
        (Koszul.d (variableCoordinateDual A E e) j x) = x := by
  simpa [variableCoordinateDual] using
    koszul_d_wedge_add_wedge_d (variableCoordinateDual A E e) (Finsupp.single e 1) j x

/-- The basis element of `⋀^j (E →₀ A[E])` indexed by `s` is the wedge of the basis vectors at
the elements of `s`, taken in increasing order. -/
lemma variableExteriorBasis_apply
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j : ℕ)
    (s : {s : Finset E // s.card = j}) :
    (Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower j s =
      ⟨ExteriorAlgebra.ιMulti (MvPolynomial E A) j
        (fun k ↦ Finsupp.single (s.1.orderEmbOfFin s.2 k) 1),
        Koszul.ιMulti_mem j _⟩ := by
  show (Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower j
    (⟨s.1, s.2⟩ : Set.powersetCard E j) = _
  rw [exteriorPower.basis_apply]
  apply Subtype.ext
  simp [exteriorPower.ιMulti_family,
    Set.powersetCard.ofFinEmbEquiv_symm_apply,
    exteriorPower.ιMulti_apply_coe, Function.comp_def,
    Finsupp.coe_basisSingleOne]

/-- The increasing enumeration of `s` with its `k`-th element removed is the increasing
enumeration of `s` composed with `Fin.succAboveOrderEmb k`. -/
lemma variableOrderEmbOfFin_erase {E : Type v} [LinearOrder E] {q : ℕ}
    (s : Finset E) (hs : s.card = q + 1) (k : Fin (q + 1))
    (h : (s.erase (s.orderEmbOfFin hs k)).card = q) :
    (s.erase (s.orderEmbOfFin hs k)).orderEmbOfFin h =
      k.succAboveOrderEmb.trans (s.orderEmbOfFin hs) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro j
  simp only [RelEmbedding.coe_trans, Function.comp_apply, Finset.mem_erase]
  exact ⟨fun he ↦ Fin.succAbove_ne k j ((s.orderEmbOfFin hs).injective he),
    s.orderEmbOfFin_mem hs _⟩

/-- The `q`-element set obtained from a `(q + 1)`-element set `s` by removing its `k`-th
smallest element. -/
abbrev variableEraseIndex {E : Type v} [LinearOrder E] {q : ℕ}
    (s : {s : Finset E // s.card = q + 1}) (k : Fin (q + 1)) :
    {s : Finset E // s.card = q} :=
  ⟨s.1.erase (s.1.orderEmbOfFin s.2 k), by
    rw [Finset.card_erase_of_mem (s.1.orderEmbOfFin_mem s.2 k), s.2]
    omega⟩

/-- The Koszul differential of `φ` on the wedge `e_s` of the basis vectors at the elements of
`s` is `∑ k, (-1) ^ k * φ (e_(s k)) • e_(s ∖ s k)`, where `s k` is the `k`-th element of `s`. -/
lemma variableKoszul_d_exteriorBasis
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (φ : Module.Dual (MvPolynomial E A) (E →₀ MvPolynomial E A))
    (q : ℕ) (s : {s : Finset E // s.card = q + 1}) :
    Koszul.d φ q
      ((Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower (q + 1) s) =
      ∑ k : Fin (q + 1),
        ((-1 : MvPolynomial E A) ^ k.val *
            φ (Finsupp.single (s.1.orderEmbOfFin s.2 k) 1)) •
          (Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower q
            (variableEraseIndex s k) := by
  apply Subtype.ext
  simp only [variableExteriorBasis_apply, Koszul.d_apply_coe,
    AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
  rw [Koszul.contraction_ιMulti]
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  funext j
  dsimp only [Function.comp_apply, variableEraseIndex]
  rw [variableOrderEmbOfFin_erase]
  rfl

/-- The increasing enumeration of `s` sends the index of `e ∈ s` back to `e`. -/
private lemma orderEmbOfFin_orderIsoOfFin_symm {E : Type v} [LinearOrder E] {q : ℕ}
    {s : Finset E} (hs : s.card = q + 1) {e : E} (he : e ∈ s) :
    s.orderEmbOfFin hs ((s.orderIsoOfFin hs).symm ⟨e, he⟩) = e := by
  rw [← s.coe_orderIsoOfFin_apply]
  simp

/-- If `e ∉ s`, the Koszul differential of the coordinate functional at `e` kills the basis
element indexed by `s`. -/
lemma variableCoordinate_d_exteriorBasis_eq_zero
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (q : ℕ) (s : {s : Finset E // s.card = q + 1})
    (he : e ∉ s.1) :
    Koszul.d (variableCoordinateDual A E e) q
      ((Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower
        (q + 1) s) = 0 := by
  classical
  rw [variableKoszul_d_exteriorBasis]
  apply Finset.sum_eq_zero
  intro k _
  have hne : e ≠ s.1.orderEmbOfFin s.2 k := fun h => he (h ▸ s.1.orderEmbOfFin_mem s.2 k)
  rw [variableCoordinateDual_single, ite_eq_right hne]
  simp

/-- If `e ∉ s`, the Koszul differential of the coordinate functional at `e` sends `e ∧ e_s` to
`e_s`. -/
lemma variableCoordinate_d_wedge_exteriorBasis_of_not_mem
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (q : ℕ) (s : {s : Finset E // s.card = q + 1})
    (he : e ∉ s.1) :
    Koszul.d (variableCoordinateDual A E e) (q + 1)
      (koszulWedge (Finsupp.single e 1) (q + 1)
        ((Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower
          (q + 1) s)) =
      (Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower
        (q + 1) s := by
  have h := variableCoordinate_wedge_homotopy A E e q
    ((Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower
      (q + 1) s)
  rwa [variableCoordinate_d_exteriorBasis_eq_zero A E e q s he,
    map_zero, add_zero] at h

/-- If `e` is the `k`-th element of `s`, the Koszul differential of the coordinate functional
at `e` sends `e_s` to `(-1) ^ k • e_(s ∖ {e})`. -/
lemma variableCoordinate_d_exteriorBasis_of_mem
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (q : ℕ) (s : {s : Finset E // s.card = q + 1})
    (he : e ∈ s.1) :
    let k := (s.1.orderIsoOfFin s.2).symm ⟨e, he⟩
    Koszul.d (variableCoordinateDual A E e) q
      ((Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower
        (q + 1) s) =
      (-1 : MvPolynomial E A) ^ k.val •
        (Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower q
          (variableEraseIndex s k) := by
  classical
  let k : Fin (q + 1) := (s.1.orderIsoOfFin s.2).symm ⟨e, he⟩
  have hk := orderEmbOfFin_orderIsoOfFin_symm s.2 he
  rw [variableKoszul_d_exteriorBasis, Finset.sum_eq_single k]
  · rw [variableCoordinateDual_single, ite_eq_left hk.symm, mul_one]
  · intro k' hk' hne
    have hne' : e ≠ s.1.orderEmbOfFin s.2 k' := fun h =>
      hne ((s.1.orderEmbOfFin s.2).injective (h.symm.trans hk.symm))
    rw [variableCoordinateDual_single, ite_eq_right hne']
    simp
  · exact fun h => (h (Finset.mem_univ k)).elim

/-- If `e ∈ s`, then `e ∧ e_s = 0`. -/
lemma variableWedge_exteriorBasis_eq_zero_of_mem
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (q : ℕ) (s : {s : Finset E // s.card = q + 1})
    (he : e ∈ s.1) :
    koszulWedge (Finsupp.single e 1) (q + 1)
      ((Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower
        (q + 1) s) = 0 := by
  classical
  have hk := orderEmbOfFin_orderIsoOfFin_symm s.2 he
  apply Subtype.ext
  rw [variableExteriorBasis_apply]
  show ExteriorAlgebra.ι (MvPolynomial E A)
      (Finsupp.single e (1 : MvPolynomial E A)) *
      ExteriorAlgebra.ιMulti (MvPolynomial E A) (q + 1)
        (fun i ↦ Finsupp.single (s.1.orderEmbOfFin s.2 i)
          (1 : MvPolynomial E A)) = 0
  rw [ExteriorAlgebra.ιMulti_apply]
  simpa only [hk] using
    (ExteriorAlgebra.ι_mul_prod_list (R := MvPolynomial E A)
      (fun i : Fin (q + 1) ↦ Finsupp.single (s.1.orderEmbOfFin s.2 i)
        (1 : MvPolynomial E A)) ((s.1.orderIsoOfFin s.2).symm ⟨e, he⟩))

/-- If `e ∈ s`, then `e ∧ d e_s = e_s`, where `d` is the Koszul differential of the coordinate
functional at `e`. -/
lemma variableWedge_coordinate_d_exteriorBasis_of_mem
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (q : ℕ) (s : {s : Finset E // s.card = q + 1})
    (he : e ∈ s.1) :
    koszulWedge (Finsupp.single e 1) q
      (Koszul.d (variableCoordinateDual A E e) q
        ((Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower
          (q + 1) s)) =
      (Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower
        (q + 1) s := by
  have h := variableCoordinate_wedge_homotopy A E e q
    ((Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower
      (q + 1) s)
  rwa [variableWedge_exteriorBasis_eq_zero_of_mem A E e q s he, map_zero,
    zero_add] at h

/-- If `e` is the `k`-th element of `s`, then `(-1) ^ k • (e ∧ e_(s ∖ {e})) = e_s`. -/
lemma variableWedge_exteriorBasis_erase
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (q : ℕ) (s : {s : Finset E // s.card = q + 1})
    (he : e ∈ s.1) :
    let k := (s.1.orderIsoOfFin s.2).symm ⟨e, he⟩
    (-1 : MvPolynomial E A) ^ k.val •
      koszulWedge (Finsupp.single e 1) q
        ((Finsupp.basisSingleOne (R := MvPolynomial E A)
          (ι := E)).exteriorPower q (variableEraseIndex s k)) =
      (Finsupp.basisSingleOne (R := MvPolynomial E A)
        (ι := E)).exteriorPower (q + 1) s := by
  have h := variableWedge_coordinate_d_exteriorBasis_of_mem A E e q s he
  rw [variableCoordinate_d_exteriorBasis_of_mem A E e q s he] at h
  simpa only [map_smul] using h

/-- The element of `variableKoszulTermBasis` indexed by `(m, s)` is `X^m • e_s`. -/
lemma variableKoszulTermBasis_apply
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (j : ℕ) (p : (E →₀ ℕ) × {s : Finset E // s.card = j}) :
    variableKoszulTermBasis A E j p =
      (MvPolynomial.basisMonomials E A) p.1 •
        (Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower j p.2 :=
  Module.Basis.smulTower_apply _ _ _

/-- The Koszul differential of the variables sends the basis element indexed by `(m, s)` to
`∑ k, (-1) ^ k •` the basis element indexed by `(m + single (s k) 1, s ∖ {s k})`, where `s k`
is the `k`-th element of `s`. -/
lemma variableKoszul_d_termBasis
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (q : ℕ) (p : (E →₀ ℕ) × {s : Finset E // s.card = q + 1}) :
    Koszul.d (variableKoszulDual A E) q
      (variableKoszulTermBasis A E (q + 1) p) =
      ∑ k : Fin (q + 1),
        (-1 : A) ^ k.val •
          variableKoszulTermBasis A E q
            (p.1 + Finsupp.single (p.2.1.orderEmbOfFin p.2.2 k) 1,
              variableEraseIndex p.2 k) := by
  classical
  rw [variableKoszulTermBasis_apply, map_smul]
  rw [variableKoszul_d_exteriorBasis]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [variableKoszulDual_single, variableKoszulTermBasis_apply]
  rw [variableExteriorBasis_apply A E q (variableEraseIndex p.2 k)]
  rw [← algebraMap_smul (MvPolynomial E A) ((-1 : A) ^ k.val)]
  simp only [smul_smul]
  congr 1
  simp [MvPolynomial.monomial_add_single, mul_left_comm]

/-- Every basis element occurring in the Koszul differential of a basis element has the same
multidegree as it. -/
lemma variableKoszulMultidegree_d
    {E : Type v} [LinearOrder E] {q : ℕ}
    (p : (E →₀ ℕ) × {s : Finset E // s.card = q + 1}) (k : Fin (q + 1)) :
    variableKoszulMultidegree q
      (p.1 + Finsupp.single (p.2.1.orderEmbOfFin p.2.2 k) 1,
        variableEraseIndex p.2 k) =
      variableKoszulMultidegree (q + 1) p := by
  classical
  unfold variableKoszulMultidegree
  rw [← Finset.sum_erase_add (s := p.2.1)
    (a := p.2.1.orderEmbOfFin p.2.2 k)
    (f := fun e : E ↦ Finsupp.single e 1)
    (p.2.1.orderEmbOfFin_mem p.2.2 k)]
  simp [add_left_comm, add_comm]

/-- If `m e ≠ 0`, then `m - single e 1 + single e 1 = m`. -/
lemma variableExponent_sub_single_add {E : Type v}
    (m : E →₀ ℕ) (e : E) (he : m e ≠ 0) :
    m - Finsupp.single e 1 + Finsupp.single e 1 = m :=
  tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr he))

/-- If `m e ≠ 0`, the degree of `m - single e 1` is one less than the degree of `m`. -/
lemma variableExponent_degree_sub_single {E : Type v}
    (m : E →₀ ℕ) (e : E) (he : m e ≠ 0) :
    (m - Finsupp.single e 1).degree + 1 = m.degree := by
  have h := congrArg Finsupp.degree (variableExponent_sub_single_add m e he)
  simpa only [map_add, Finsupp.degree_single] using h

/-- For `e ≠ f`, subtracting `single e 1` commutes with adding `single f 1`. -/
lemma variableExponent_sub_single_add_other {E : Type v}
    (m : E →₀ ℕ) (e f : E) (hef : e ≠ f) :
    m + Finsupp.single f 1 - Finsupp.single e 1 =
      m - Finsupp.single e 1 + Finsupp.single f 1 := by
  classical
  apply Finsupp.ext
  intro x
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  by_cases hxe : x = e
  · subst x
    simp [hef, hef.symm]
  · by_cases hxf : x = f
    · subst x
      simp [hef.symm]
    · simp [hxe, hxf, Ne.symm hxf]

/-- If `m e ≠ 0`, dividing the monomial `X^m` by `X e` gives `X^(m - single e 1)`. -/
lemma variableMonomial_div_X
    (A : Type u) [CommRing A] (E : Type v)
    (m : E →₀ ℕ) (e : E) (he : m e ≠ 0) :
    (MvPolynomial.monomial m (1 : A)).divMonomial (Finsupp.single e 1) =
      MvPolynomial.monomial (m - Finsupp.single e 1) 1 := by
  have hpoly : MvPolynomial.monomial m (1 : A) =
      MvPolynomial.X e *
        MvPolynomial.monomial (m - Finsupp.single e 1) 1 := by
    calc
      _ = MvPolynomial.monomial
          (m - Finsupp.single e 1 + Finsupp.single e 1) (1 : A) := by
            rw [variableExponent_sub_single_add m e he]
      _ = MvPolynomial.monomial (m - Finsupp.single e 1) (1 : A) *
          MvPolynomial.X e := by simp only [MvPolynomial.monomial_add_single, pow_one]
      _ = _ := mul_comm _ _
  rw [hpoly, MvPolynomial.X_mul_divMonomial]

/-- If `m e = 0`, dividing the monomial `X^m` by `X e` gives `0`. -/
lemma variableMonomial_div_X_eq_zero
    (A : Type u) [CommRing A] (E : Type v)
    (m : E →₀ ℕ) (e : E) (he : m e = 0) :
    (MvPolynomial.monomial m (1 : A)).divMonomial (Finsupp.single e 1) = 0 := by
  classical
  apply MvPolynomial.ext
  intro s
  rw [MvPolynomial.coeff_divMonomial]
  have hne : Finsupp.single e 1 + s ≠ m := by
    intro h
    have hs := congrArg (fun t : E →₀ ℕ ↦ t e) h
    simp [he] at hs
  simp [MvPolynomial.coeff_monomial, hne.symm]

/-- Division by the variable `X e`, as an `A`-linear map: it sends `X^m` to
`X^(m - single e 1)` when `m e ≠ 0`, and to `0` otherwise. -/
noncomputable def variableDivX
    (A : Type u) [CommRing A] (E : Type v) (e : E) :
    MvPolynomial E A →ₗ[A] MvPolynomial E A where
  toFun p := p.divMonomial (Finsupp.single e 1)
  map_add' p q := MvPolynomial.add_divMonomial p q _
  map_smul' a p := by
    classical
    apply MvPolynomial.ext
    intro m
    simp [MvPolynomial.coeff_divMonomial]

/-- Dividing `X e * p` by `X e` gives `p`. -/
lemma variableDivX_X_mul
    (A : Type u) [CommRing A] (E : Type v) (e : E)
    (p : MvPolynomial E A) :
    variableDivX A E e (MvPolynomial.X e * p) = p :=
  MvPolynomial.X_mul_divMonomial e p

/-- For `e ≠ f`, division by `X e` commutes with multiplication by `X f` on monomials. -/
lemma variableDivX_X_mul_other_monomial
    (A : Type u) [CommRing A] (E : Type v)
    (e f : E) (hef : e ≠ f) (m : E →₀ ℕ) :
    variableDivX A E e
      (MvPolynomial.X f * MvPolynomial.monomial m (1 : A)) =
      MvPolynomial.X f *
        variableDivX A E e (MvPolynomial.monomial m (1 : A)) := by
  have hX (q : E →₀ ℕ) :
      MvPolynomial.X f * MvPolynomial.monomial q (1 : A) =
        MvPolynomial.monomial (q + Finsupp.single f 1) 1 := by
    simp [MvPolynomial.monomial_add_single, mul_comm]
  rw [hX]
  have hme : ((m + Finsupp.single f 1) : E →₀ ℕ) e = m e := by
    simp [hef]
  by_cases hm : m e = 0
  · rw [show variableDivX A E e
        (MvPolynomial.monomial (m + Finsupp.single f 1) (1 : A)) = 0 from
          variableMonomial_div_X_eq_zero A E _ e (hme.trans hm)]
    rw [show variableDivX A E e (MvPolynomial.monomial m (1 : A)) = 0 from
      variableMonomial_div_X_eq_zero A E m e hm]
    simp
  · rw [show variableDivX A E e
        (MvPolynomial.monomial (m + Finsupp.single f 1) (1 : A)) =
          MvPolynomial.monomial
            (m + Finsupp.single f 1 - Finsupp.single e 1) 1 from
              variableMonomial_div_X A E _ e (by rwa [hme])]
    rw [show variableDivX A E e (MvPolynomial.monomial m (1 : A)) =
        MvPolynomial.monomial (m - Finsupp.single e 1) 1 from
          variableMonomial_div_X A E m e hm]
    rw [variableExponent_sub_single_add_other m e f hef]
    exact (hX _).symm

/-- For `e ≠ f`, division by `X e` commutes with multiplication by `X f`. -/
lemma variableDivX_X_mul_other
    (A : Type u) [CommRing A] (E : Type v)
    (e f : E) (hef : e ≠ f) (p : MvPolynomial E A) :
    variableDivX A E e (MvPolynomial.X f * p) =
      MvPolynomial.X f * variableDivX A E e p := by
  let l : MvPolynomial E A →ₗ[A] MvPolynomial E A :=
    (variableDivX A E e).comp (LinearMap.mulLeft A (MvPolynomial.X f))
  let r : MvPolynomial E A →ₗ[A] MvPolynomial E A :=
    (LinearMap.mulLeft A (MvPolynomial.X f)).comp (variableDivX A E e)
  have hlr : l = r :=
    (MvPolynomial.basisMonomials E A).ext (variableDivX_X_mul_other_monomial A E e f hef)
  exact LinearMap.congr_fun hlr p

end MvPolynomial

end
