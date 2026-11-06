module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.BrauerGroupCField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFieldFiniteExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFields
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.HomogeneousZeros
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tsen's theorem

A rational function field in `r` variables over an algebraically closed field `k` is a
\(C_r\) field: a form of degree `d > 0` in `n` variables with `d ^ r < n` has a nontrivial
zero. As a consequence, a field finite over `RatFunc k` is a \(C_1\) field and has trivial Brauer
group.

## Main results

* `exists_nonzero_zero_of_isHomogeneous_mvPolynomial`: a form of degree `d > 0` in `n > d ^ r`
  variables over `k[x_1, ..., x_r]` has a zero with polynomial entries, not all zero.
* `isCField_of_isFractionRing_mvPolynomial`: a fraction field of `k[x_1, ..., x_r]` is a
  \(C_r\) field.
* `brauerGroup_eq_one_of_isFractionRing_mvPolynomial`: the Brauer group of a rational function
  field in one variable over an algebraically closed field is trivial.
* `isCField_one_ratFunc`: `RatFunc k` is a \(C_1\) field for `k` algebraically closed.
* `isCField_one_of_module_finite_ratFunc`: Tsen's theorem in dimension one — a field finite
  over `RatFunc k` is a \(C_1\) field.
* `brauerGroup_eq_one_of_module_finite_ratFunc`: such a field has trivial Brauer group.
* `brauerGroup_eq_one_of_module_finite_tower_ratFunc`: so does every finite extension of it.

## References

* [Stacks Project, Tag 03RD](https://stacks.math.columbia.edu/tag/03RD)
* [Stacks Project, Tag 03RF](https://stacks.math.columbia.edu/tag/03RF)
* [Stacks Project, Tag 03RG](https://stacks.math.columbia.edu/tag/03RG)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public noncomputable section

universe u

/-- `(x + 1) ^ (r + 1)` is at most `x ^ (r + 1) + (r + 1) * (x + 1) ^ r`. -/
theorem Nat.add_one_pow_succ_le (x r : ℕ) :
    (x + 1) ^ (r + 1) ≤ x ^ (r + 1) + (r + 1) * (x + 1) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc (x + 1) ^ (r + 2) = (x + 1) * (x + 1) ^ (r + 1) := by ring
      _ ≤ (x + 1) * (x ^ (r + 1) + (r + 1) * (x + 1) ^ r) := Nat.mul_le_mul_left _ ih
      _ = x ^ (r + 2) + x ^ (r + 1) + (r + 1) * (x + 1) ^ (r + 1) := by ring
      _ ≤ x ^ (r + 2) + (x + 1) ^ (r + 1) + (r + 1) * (x + 1) ^ (r + 1) := by gcongr; omega
      _ = x ^ (r + 2) + (r + 2) * (x + 1) ^ (r + 1) := by ring

/-- If `d ^ r < n`, then for every `D` there is `e > 0` with `(d * e + D) ^ r < n * e ^ r`. -/
theorem exists_pos_mul_add_pow_lt {d n r : ℕ} (hn : d ^ r < n) (D : ℕ) :
    ∃ e, 0 < e ∧ (d * e + D) ^ r < n * e ^ r := by
  obtain _ | q := r
  · exact ⟨1, one_pos, by simpa using hn⟩
  set m := (q + 1) * (d + 1) ^ q + 1 with hm
  have hm1 : 0 < m := by omega
  have hmq : 0 < m ^ q := Nat.pow_pos hm1
  have key : (d * m + 1) ^ (q + 1) < n * m ^ (q + 1) := by
    have h1 : (d * m + 1) ^ (q + 1) ≤ (d * m) ^ (q + 1) + (q + 1) * (d * m + 1) ^ q :=
      Nat.add_one_pow_succ_le _ _
    have h2 : (q + 1) * (d * m + 1) ^ q ≤ (q + 1) * ((d + 1) ^ q * m ^ q) := by
      refine Nat.mul_le_mul_left _ ?_
      rw [← mul_pow]
      exact Nat.pow_le_pow_left (by nlinarith) _
    have h3 : (q + 1) * ((d + 1) ^ q * m ^ q) < m * m ^ q := by
      rw [← mul_assoc]
      exact Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl hmq
    have h4 : (d * m) ^ (q + 1) = d ^ (q + 1) * m ^ (q + 1) := mul_pow _ _ _
    have h5 : d ^ (q + 1) * m ^ (q + 1) + m ^ (q + 1) ≤ n * m ^ (q + 1) := by
      have hdn : d ^ (q + 1) + 1 ≤ n := hn
      nlinarith [Nat.zero_le (m ^ (q + 1))]
    have h6 : m * m ^ q = m ^ (q + 1) := (pow_succ' m q).symm
    omega
  refine ⟨(D + 1) * m, by positivity, ?_⟩
  calc (d * ((D + 1) * m) + D) ^ (q + 1) ≤ ((D + 1) * (d * m + 1)) ^ (q + 1) :=
        Nat.pow_le_pow_left (by nlinarith) _
    _ = (D + 1) ^ (q + 1) * (d * m + 1) ^ (q + 1) := mul_pow _ _ _
    _ < (D + 1) ^ (q + 1) * (n * m ^ (q + 1)) := Nat.mul_lt_mul_of_le_of_lt (le_refl _) key
      (Nat.pow_pos (Nat.succ_pos D))
    _ = n * ((D + 1) * m) ^ (q + 1) := by rw [mul_pow]; ring

/-- Over an algebraically closed field, a family of homogeneous polynomials of positive degree
indexed by a finite type smaller than the finite type of variables has a common nonzero
zero. -/
theorem exists_nonzero_common_zero_of_isHomogeneous_of_card_lt
    (k : Type*) [Field k] [IsAlgClosed k] {S I : Type*} [Fintype S] [Fintype I]
    (d : S → ℕ) (f : S → MvPolynomial I k) (hd : ∀ i, 0 < d i)
    (hf : ∀ i, (f i).IsHomogeneous (d i)) (hc : Fintype.card S < Fintype.card I) :
    ∃ α : I → k, α ≠ 0 ∧ ∀ i, MvPolynomial.eval α (f i) = 0 := by
  classical
  obtain ⟨τ⟩ := Fintype.truncEquivFin S
  obtain ⟨σ⟩ := Fintype.truncEquivFin I
  obtain ⟨α, hα0, hα⟩ := exists_nonzero_common_zero_of_isHomogeneous k
    (fun j ↦ d (τ.symm j)) (fun j ↦ MvPolynomial.rename σ (f (τ.symm j)))
    (fun j ↦ hd _) (fun j ↦ (hf _).rename_isHomogeneous) hc
  refine ⟨α ∘ σ, fun hcon ↦ hα0 (funext fun j ↦ by simpa using congrFun hcon (σ.symm j)),
    fun i ↦ ?_⟩
  simpa [MvPolynomial.eval_rename] using hα (τ i)

namespace MvPolynomial

variable {σ τ k : Type*} [CommSemiring k]

/-- A polynomial whose coefficients are themselves polynomials is coefficientwise homogeneous
of degree `d` if each of its coefficients is a homogeneous polynomial of degree `d`. -/
def IsCoeffHomogeneous (p : MvPolynomial σ (MvPolynomial τ k)) (d : ℕ) : Prop :=
  ∀ ν, (p.coeff ν).IsHomogeneous d

/-- A conditionally vanishing homogeneous polynomial is homogeneous. -/
private theorem isHomogeneous_ite {d : ℕ} {a : MvPolynomial τ k} (h : a.IsHomogeneous d)
    (p : Prop) [Decidable p] : (if p then a else 0).IsHomogeneous d := by
  split
  · exact h
  · exact isHomogeneous_zero τ k d

/-- The constant polynomial `1` is coefficientwise homogeneous of degree `0`. -/
theorem isCoeffHomogeneous_one :
    IsCoeffHomogeneous (1 : MvPolynomial σ (MvPolynomial τ k)) 0 := by
  intro ν
  classical
  rw [coeff_one]
  exact isHomogeneous_ite (isHomogeneous_one τ k) _

/-- A monomial with a homogeneous coefficient is coefficientwise homogeneous. -/
theorem isCoeffHomogeneous_monomial {d : ℕ} {a : MvPolynomial τ k} (ν₀ : σ →₀ ℕ)
    (h : a.IsHomogeneous d) : IsCoeffHomogeneous (monomial ν₀ a) d := by
  intro ν
  classical
  rw [coeff_monomial]
  exact isHomogeneous_ite h _

/-- Viewing a polynomial over `k` as a polynomial whose coefficients are constants gives a
coefficientwise homogeneous polynomial of degree `0`. -/
theorem isCoeffHomogeneous_map_C (c : MvPolynomial σ k) :
    IsCoeffHomogeneous (map (C (σ := τ) (R := k)) c) 0 := fun ν ↦ by
  rw [coeff_map]
  exact isHomogeneous_C _ _

namespace IsCoeffHomogeneous

/-- Coefficientwise homogeneity adds degrees under multiplication. -/
theorem mul {d d' : ℕ} {p q : MvPolynomial σ (MvPolynomial τ k)}
    (hp : IsCoeffHomogeneous p d) (hq : IsCoeffHomogeneous q d') :
    IsCoeffHomogeneous (p * q) (d + d') := by
  intro ν
  classical
  rw [coeff_mul]
  exact IsHomogeneous.sum _ _ _ fun x _ ↦ (hp x.1).mul (hq x.2)

/-- A finite sum of coefficientwise homogeneous polynomials of degree `d` is coefficientwise
homogeneous of degree `d`. -/
theorem sum {ι : Type*} {d : ℕ} (s : Finset ι) (p : ι → MvPolynomial σ (MvPolynomial τ k))
    (h : ∀ i ∈ s, IsCoeffHomogeneous (p i) d) : IsCoeffHomogeneous (∑ i ∈ s, p i) d :=
  fun ν ↦ by
    rw [coeff_sum]
    exact IsHomogeneous.sum _ _ _ fun i hi ↦ h i hi ν

/-- Coefficientwise homogeneity multiplies degrees under taking powers. -/
theorem pow {d : ℕ} {p : MvPolynomial σ (MvPolynomial τ k)} (hp : IsCoeffHomogeneous p d)
    (j : ℕ) : IsCoeffHomogeneous (p ^ j) (d * j) := by
  induction j with
  | zero => simpa using isCoeffHomogeneous_one
  | succ j ih =>
    rw [pow_succ, show d * (j + 1) = d * j + d by ring]
    exact ih.mul hp

/-- A finite product of coefficientwise homogeneous polynomials is coefficientwise homogeneous
of the summed degree. -/
theorem prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ (MvPolynomial τ k))
    (m : ι → ℕ) (h : ∀ i ∈ s, IsCoeffHomogeneous (p i) (m i)) :
    IsCoeffHomogeneous (∏ i ∈ s, p i) (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isCoeffHomogeneous_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Substituting coefficientwise linear polynomials into a homogeneous polynomial of degree
`d` gives a coefficientwise homogeneous polynomial of degree `d`. -/
theorem eval₂ {ι : Type*} {d : ℕ} {p : MvPolynomial ι (MvPolynomial σ k)}
    (hp : p.IsHomogeneous d) (g : ι → MvPolynomial σ (MvPolynomial τ k))
    (hg : ∀ i, IsCoeffHomogeneous (g i) 1) :
    IsCoeffHomogeneous (MvPolynomial.eval₂ (map (C (σ := τ) (R := k))) g p) d := by
  classical
  rw [eval₂_eq]
  refine sum _ _ fun ν hν ↦ ?_
  have hdeg : d = ∑ i ∈ ν.support, 1 * ν i := by
    simpa using hp.degree_eq_sum_deg_support hν
  have hprod : IsCoeffHomogeneous (∏ i ∈ ν.support, g i ^ ν i) d := by
    rw [hdeg]
    exact prod _ _ _ fun i _ ↦ (hg i).pow (ν i)
  simpa using (isCoeffHomogeneous_map_C (p.coeff ν)).mul hprod

end IsCoeffHomogeneous

end MvPolynomial

/-- The exponent vector of the monomial attached to a tuple of exponents, each bounded by
`e`. -/
def boxExponent {r e : ℕ} (v : Fin r → Fin e) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j ↦ (v j : ℕ)

/-- The exponent of the `j`-th variable in `boxExponent v` is `v j`. -/
theorem boxExponent_apply {r e : ℕ} (v : Fin r → Fin e) (j : Fin r) :
    boxExponent v j = (v j : ℕ) := rfl

/-- Distinct bounded exponent tuples give distinct monomials. -/
theorem boxExponent_injective {r e : ℕ} :
    Function.Injective (boxExponent (r := r) (e := e)) := fun u v h ↦
  funext fun j ↦ by simpa [boxExponent_apply, Fin.val_inj] using congrArg (fun t ↦ t j) h

/-- The generic polynomial in `r` variables whose exponents are bounded by `e` in each
variable and whose coefficients are the indeterminates of the `i`-th block. -/
def genericBoundedPolynomial (k : Type*) [CommSemiring k] {r e n : ℕ} (i : Fin n) :
    MvPolynomial (Fin r) (MvPolynomial (Fin n × (Fin r → Fin e)) k) :=
  ∑ b : Fin r → Fin e, MvPolynomial.monomial (boxExponent b) (MvPolynomial.X (i, b))

/-- The generic bounded polynomial is linear in its unknown coefficients. -/
theorem isCoeffHomogeneous_genericBoundedPolynomial (k : Type*) [CommSemiring k]
    {r e n : ℕ} (i : Fin n) :
    (genericBoundedPolynomial k (r := r) (e := e) i).IsCoeffHomogeneous 1 :=
  MvPolynomial.IsCoeffHomogeneous.sum _ _ fun _b _ ↦
    MvPolynomial.isCoeffHomogeneous_monomial _ (MvPolynomial.isHomogeneous_X _ _)

/-- Every variable occurs in the generic bounded polynomial to degree at most `e - 1`. -/
theorem degreeOf_genericBoundedPolynomial_le (k : Type*) [CommSemiring k] {r e n : ℕ}
    (i : Fin n) (j : Fin r) :
    (genericBoundedPolynomial k (r := r) (e := e) i).degreeOf j ≤ e - 1 := by
  classical
  refine le_trans (MvPolynomial.degreeOf_sum_le _ _ _) (Finset.sup_le fun b _ ↦ ?_)
  refine MvPolynomial.degreeOf_le_iff.mpr fun m hm ↦ ?_
  obtain rfl : m = boxExponent b :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
  simpa [boxExponent_apply] using Nat.le_sub_one_of_lt (b j).isLt

/-- The coefficient of the generic bounded polynomial at a bounded exponent tuple is the
corresponding indeterminate. -/
theorem coeff_genericBoundedPolynomial (k : Type*) [CommSemiring k] {r e n : ℕ} (i : Fin n)
    (b : Fin r → Fin e) :
    (genericBoundedPolynomial k (r := r) (e := e) i).coeff (boxExponent b)
      = MvPolynomial.X (i, b) := by
  classical
  simp only [genericBoundedPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ _) fun c _ hc ↦ by
    simp [boxExponent_injective.ne hc]]
  simp

/-- The degree in each variable of the generic substitution into a homogeneous form of
degree `d` is bounded by the degrees of its coefficients plus `d * (e - 1)`. -/
private theorem degreeOf_eval₂_genericBoundedPolynomial_le (k : Type*) [CommSemiring k]
    {r n d e : ℕ} (f : MvPolynomial (Fin n) (MvPolynomial (Fin r) k)) (hf : f.IsHomogeneous d)
    (j : Fin r) :
    (MvPolynomial.eval₂ (MvPolynomial.map (MvPolynomial.C (σ := Fin n × (Fin r → Fin e))))
      (genericBoundedPolynomial k (r := r) (e := e)) f).degreeOf j
      ≤ (f.support.sup fun ν => (f.coeff ν).totalDegree) + d * (e - 1) := by
  classical
  have hb : ∀ ν ∈ f.support,
      (MvPolynomial.map (MvPolynomial.C (σ := Fin n × (Fin r → Fin e))) (f.coeff ν) *
        ∏ i ∈ ν.support, genericBoundedPolynomial k (r := r) (e := e) i ^ ν i).degreeOf j
        ≤ (f.support.sup fun ν ↦ (f.coeff ν).totalDegree) + d * (e - 1) := by
    intro ν hν
    refine le_trans (MvPolynomial.degreeOf_mul_le _ _ _) (Nat.add_le_add ?_ ?_)
    · calc (MvPolynomial.map MvPolynomial.C (f.coeff ν)).degreeOf j
          ≤ (f.coeff ν).degreeOf j := MvPolynomial.degreeOf_le_iff.mpr fun m hm ↦
              MvPolynomial.le_degreeOf_of_mem_support j
                (MvPolynomial.support_map_subset _ _ hm)
        _ ≤ (f.coeff ν).totalDegree := MvPolynomial.degreeOf_le_totalDegree _ j
        _ ≤ _ := Finset.le_sup (f := fun ν ↦ (f.coeff ν).totalDegree) hν
    · calc (∏ i ∈ ν.support, genericBoundedPolynomial k (r := r) (e := e) i ^ ν i).degreeOf j
          ≤ ∑ i ∈ ν.support, (genericBoundedPolynomial k (r := r) (e := e) i ^ ν i).degreeOf j :=
            MvPolynomial.degreeOf_prod_le _ _ _
        _ ≤ ∑ i ∈ ν.support, ν i * (e - 1) := Finset.sum_le_sum fun i _ ↦
              le_trans (MvPolynomial.degreeOf_pow_le _ _ _) (Nat.mul_le_mul_left _
                (degreeOf_genericBoundedPolynomial_le k i j))
        _ = (∑ i ∈ ν.support, ν i) * (e - 1) := Finset.sum_mul .. |>.symm
        _ = d * (e - 1) := by rw [← hf.degree_eq_sum_deg_support hν]
  rw [MvPolynomial.eval₂_eq]
  exact le_trans (MvPolynomial.degreeOf_sum_le _ _ _) (Finset.sup_le hb)

/-- Specialising the unknown coefficients of the generic bounded polynomials at a nonzero point
gives a family of polynomials that is not identically zero. -/
private theorem map_eval_genericBoundedPolynomial_ne_zero (k : Type*) [CommSemiring k] {r e n : ℕ}
    {a : Fin n × (Fin r → Fin e) → k} (ha : a ≠ 0) :
    (fun i => MvPolynomial.map (MvPolynomial.eval a)
      (genericBoundedPolynomial k (r := r) (e := e) i)) ≠ 0 := by
  obtain ⟨⟨i₀, b₀⟩, hib⟩ := Function.ne_iff.mp ha
  intro hcon
  have h := congrArg (fun q => q.coeff (boxExponent b₀)) (congrFun hcon i₀)
  simp only [MvPolynomial.coeff_map, coeff_genericBoundedPolynomial, MvPolynomial.eval_X,
    Pi.zero_apply, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
  exact hib h

/-- Specialising the coefficients of the coefficients commutes with substituting polynomials
into a polynomial over `MvPolynomial σ k`. -/
private theorem map_eval_eval₂_map_C {k σ τ ι : Type*} [CommSemiring k] (a : τ → k)
    (β : ι → MvPolynomial σ (MvPolynomial τ k)) (f : MvPolynomial ι (MvPolynomial σ k)) :
    MvPolynomial.map (MvPolynomial.eval a)
        (MvPolynomial.eval₂ (MvPolynomial.map (MvPolynomial.C (σ := τ) (R := k))) β f)
      = MvPolynomial.eval (fun i => MvPolynomial.map (MvPolynomial.eval a) (β i)) f := by
  have hCid : (MvPolynomial.eval a).comp (MvPolynomial.C (σ := τ) (R := k)) = RingHom.id k :=
    RingHom.ext fun x ↦ by simp
  have hcomp : (MvPolynomial.map (MvPolynomial.eval a)).comp
      (MvPolynomial.map (MvPolynomial.C (σ := τ) (R := k))) = RingHom.id (MvPolynomial σ k) :=
    RingHom.ext fun c ↦ by
      rw [RingHom.comp_apply, MvPolynomial.map_map, hCid, MvPolynomial.map_id, RingHom.id_apply]
  have hcl := MvPolynomial.eval₂_comp_left (MvPolynomial.map (MvPolynomial.eval a))
    (MvPolynomial.map (MvPolynomial.C (σ := τ) (R := k))) β f
  rwa [hcomp, MvPolynomial.eval₂_id] at hcl

/-- Tsen's dimension count: over a polynomial ring in `r` variables over an algebraically closed
field, a homogeneous polynomial of degree `d > 0` in `n` variables with `d ^ r < n` has a zero
whose entries are polynomials, not all zero. -/
theorem exists_nonzero_zero_of_isHomogeneous_mvPolynomial
    (k : Type*) [Field k] [IsAlgClosed k] {r n d : ℕ} (hd : 0 < d) (hdn : d ^ r < n)
    (f : MvPolynomial (Fin n) (MvPolynomial (Fin r) k)) (hf : f.IsHomogeneous d) :
    ∃ α : Fin n → MvPolynomial (Fin r) k, α ≠ 0 ∧ MvPolynomial.eval α f = 0 := by
  classical
  obtain ⟨e, he, hcount⟩ :=
    exists_pos_mul_add_pow_lt hdn (f.support.sup fun ν ↦ (f.coeff ν).totalDegree)
  obtain ⟨D, hD⟩ : ∃ D, D = f.support.sup fun ν ↦ (f.coeff ν).totalDegree := ⟨_, rfl⟩
  rw [← hD] at hcount
  obtain ⟨cc, hcc⟩ : ∃ cc, cc = (MvPolynomial.C
      (σ := Fin n × (Fin r → Fin e)) (R := k)) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ :
      ∃ β : Fin n → MvPolynomial (Fin r) (MvPolynomial (Fin n × (Fin r → Fin e)) k),
      β = fun i ↦ genericBoundedPolynomial k i := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = MvPolynomial.eval₂ (MvPolynomial.map cc) β f := ⟨_, rfl⟩
  have hgHC : g.IsCoeffHomogeneous d := by
    rw [hg, hcc, hβ]
    exact MvPolynomial.IsCoeffHomogeneous.eval₂ hf _ fun i ↦
      isCoeffHomogeneous_genericBoundedPolynomial k i
  have hdegg : ∀ j, g.degreeOf j < d * e + D := by
    intro j
    have hle : g.degreeOf j ≤ D + d * (e - 1) := by
      rw [hg, hcc, hβ, hD]
      exact degreeOf_eval₂_genericBoundedPolynomial_le k f hf j
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have hmul : d * (e' + 1 - 1) + d = d * (e' + 1) := by rw [Nat.add_sub_cancel]; ring
    omega
  have hsupp : ∀ ν, g.coeff ν ≠ 0 → ∃ w : Fin r → Fin (d * e + D), boxExponent w = ν :=
    fun ν hν ↦ ⟨fun j ↦ ⟨ν j, (MvPolynomial.le_degreeOf_of_mem_support j
      (MvPolynomial.mem_support_iff.mpr hν)).trans_lt (hdegg j)⟩, Finsupp.ext fun j ↦ rfl⟩
  obtain ⟨a, ha0, ha⟩ := exists_nonzero_common_zero_of_isHomogeneous_of_card_lt k
    (fun _ : Fin r → Fin (d * e + D) ↦ d) (fun w ↦ g.coeff (boxExponent w)) (fun _ ↦ hd)
    (fun w ↦ hgHC _) (by simpa using hcount)
  refine ⟨fun i ↦ MvPolynomial.map (MvPolynomial.eval a) (β i), ?_, ?_⟩
  · rw [hβ]
    exact map_eval_genericBoundedPolynomial_ne_zero k ha0
  · have hcl := map_eval_eval₂_map_C a β f
    rw [← hcc, ← hg] at hcl
    have hzero : MvPolynomial.map (MvPolynomial.eval a) g = 0 := by
      refine MvPolynomial.ext _ _ fun ν ↦ ?_
      rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      by_cases hν : g.coeff ν = 0
      · simp [hν]
      · obtain ⟨w, rfl⟩ := hsupp ν hν
        exact ha w
    exact hcl ▸ hzero

/-- Clearing denominators: a polynomial over a fraction field of `R` becomes, after
multiplication by a nonzero divisor of `R`, the image of a polynomial over `R`. -/
private theorem exists_map_eq_C_mul_of_isFractionRing (R : Type*) {K σ : Type*} [CommRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (f : MvPolynomial σ K) :
    ∃ (b : nonZeroDivisors R) (f' : MvPolynomial σ R),
      MvPolynomial.map (algebraMap R K) f' = MvPolynomial.C (algebraMap R K b) * f := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors R) (f.support.image fun ν ↦ f.coeff ν)
  obtain ⟨h, hh⟩ : ∃ h, h = MvPolynomial.C (algebraMap R K (b : R)) * f := ⟨_, rfl⟩
  have hint : ∀ ν, ∃ y, algebraMap R K y = h.coeff ν := by
    intro ν
    by_cases hν : ν ∈ f.support
    · obtain ⟨y, hy⟩ := hb _ (Finset.mem_image_of_mem _ hν)
      exact ⟨y, by rw [hh, MvPolynomial.coeff_C_mul, hy, Algebra.smul_def]⟩
    · refine ⟨0, ?_⟩
      rw [hh, MvPolynomial.coeff_C_mul, MvPolynomial.notMem_support_iff.mp hν, map_zero,
        mul_zero]
  refine ⟨b, ∑ ν ∈ h.support, MvPolynomial.monomial ν
    (Function.invFun (algebraMap R K) (h.coeff ν)), ?_⟩
  rw [← hh]
  refine MvPolynomial.ext _ _ fun τ ↦ ?_
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_sum]
  by_cases hτ : τ ∈ h.support
  · rw [Finset.sum_eq_single_of_mem τ hτ fun c _ hc ↦ by
      simp [MvPolynomial.coeff_monomial, hc]]
    simpa using Function.invFun_eq (hint τ)
  · rw [Finset.sum_eq_zero fun c hc ↦ by
      have hcτ : c ≠ τ := fun hct ↦ hτ (hct ▸ hc)
      simp [MvPolynomial.coeff_monomial, hcτ], map_zero]
    exact (MvPolynomial.notMem_support_iff.mp hτ).symm

/-- Tsen's theorem for rational function fields: a fraction field of the polynomial ring in `r`
variables over an algebraically closed field is a \(C_r\) field. -/
theorem isCField_of_isFractionRing_mvPolynomial (k : Type*) [Field k] [IsAlgClosed k] {r : ℕ}
    (K : Type*) [Field K] [Algebra (MvPolynomial (Fin r) k) K]
    [IsFractionRing (MvPolynomial (Fin r) k) K] : IsCField K r := by
  classical
  rintro d n ⟨hd, hdn⟩ f hf
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin r) k) K) :=
    IsFractionRing.injective _ _
  obtain ⟨b, f', hf'⟩ := exists_map_eq_C_mul_of_isFractionRing (MvPolynomial (Fin r) k) f
  have hf'hom : f'.IsHomogeneous d :=
    MvPolynomial.IsHomogeneous.of_map hinj (by rw [hf']; exact hf.C_mul _)
  obtain ⟨α, hα0, hα⟩ := exists_nonzero_zero_of_isHomogeneous_mvPolynomial k hd hdn f' hf'hom
  refine ⟨fun i ↦ algebraMap (MvPolynomial (Fin r) k) K (α i),
    fun hcon ↦ hα0 (funext fun i ↦ hinj (by simpa using congrFun hcon i)), ?_⟩
  have hcl := MvPolynomial.eval₂_comp_left (algebraMap (MvPolynomial (Fin r) k) K)
    (RingHom.id (MvPolynomial (Fin r) k)) α f'
  rw [MvPolynomial.eval₂_id, hα, map_zero] at hcl
  have hev : MvPolynomial.eval (fun i ↦ algebraMap (MvPolynomial (Fin r) k) K (α i))
      (MvPolynomial.C (algebraMap (MvPolynomial (Fin r) k) K b) * f) = 0 := by
    rw [← hf', MvPolynomial.eval_map]
    simpa [Function.comp_def] using hcl.symm
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C] at hev
  exact (mul_eq_zero.mp hev).resolve_left fun hx ↦
    nonZeroDivisors.coe_ne_zero b (hinj (by rw [hx, map_zero]))

/-- A rational function field in `r` variables over an algebraically closed field is a
\(C_r\) field. -/
theorem isCField_fractionRing_mvPolynomial (k : Type*) [Field k] [IsAlgClosed k] (r : ℕ) :
    IsCField (FractionRing (MvPolynomial (Fin r) k)) r :=
  isCField_of_isFractionRing_mvPolynomial k _

/-- The Brauer group of a rational function field in one variable over an algebraically closed
field is trivial. -/
@[sga "4½ Arcata 3.2.2" "special case"]
theorem brauerGroup_eq_one_of_isFractionRing_mvPolynomial (k : Type u) [Field k] [IsAlgClosed k]
    (K : Type u) [Field K] [Algebra (MvPolynomial (Fin 1) k) K]
    [IsFractionRing (MvPolynomial (Fin 1) k) K] (x : BrauerGroup K) : x = 1 :=
  brauerGroup_eq_one_of_isCField K (isCField_of_isFractionRing_mvPolynomial k K) x

/-- The field of rational functions in one variable over an algebraically closed field is a
\(C_1\) field. -/
theorem isCField_one_ratFunc (k : Type*) [Field k] [IsAlgClosed k] : IsCField (RatFunc k) 1 :=
  (isCField_fractionRing_mvPolynomial k 1).of_ringEquiv
    (IsFractionRing.ringEquivOfRingEquiv (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv)

/-- Tsen's theorem in dimension one: a field finite over the rational function field in one
variable over an algebraically closed field is a \(C_1\) field. -/
theorem isCField_one_of_module_finite_ratFunc (k : Type*) [Field k] [IsAlgClosed k]
    (K : Type*) [Field K] [Algebra (RatFunc k) K] [Module.Finite (RatFunc k) K] :
    IsCField K 1 :=
  isCField_one_of_module_finite (RatFunc k) K (isCField_one_ratFunc k)

/-- A field finite over a fraction field of `k[x]`, for `k` algebraically closed, is a \(C_1\)
field. -/
theorem isCField_one_of_module_finite_isFractionRing_mvPolynomial (k : Type*) [Field k]
    [IsAlgClosed k] (F : Type*) [Field F] [Algebra (MvPolynomial (Fin 1) k) F]
    [IsFractionRing (MvPolynomial (Fin 1) k) F] (K : Type*) [Field K] [Algebra F K]
    [Module.Finite F K] : IsCField K 1 :=
  isCField_one_of_module_finite F K (isCField_of_isFractionRing_mvPolynomial k F)

/-- A field finite over the rational function field in one variable over an algebraically closed
field has trivial Brauer group. -/
@[sga "4½ Arcata 3.2.2" "special case"]
theorem brauerGroup_eq_one_of_module_finite_ratFunc (k : Type u) [Field k] [IsAlgClosed k]
    (K : Type u) [Field K] [Algebra (RatFunc k) K] [Module.Finite (RatFunc k) K]
    (x : BrauerGroup K) : x = 1 :=
  brauerGroup_eq_one_of_isCField K (isCField_one_of_module_finite_ratFunc k K) x

/-- The Brauer group of a field finite over a fraction field of `k[x]`, for `k` algebraically
closed, is trivial. -/
theorem brauerGroup_eq_one_of_module_finite_isFractionRing_mvPolynomial (k : Type u) [Field k]
    [IsAlgClosed k] (F : Type u) [Field F] [Algebra (MvPolynomial (Fin 1) k) F]
    [IsFractionRing (MvPolynomial (Fin 1) k) F] (K : Type u) [Field K] [Algebra F K]
    [Module.Finite F K] (x : BrauerGroup K) : x = 1 :=
  brauerGroup_eq_one_of_isCField K
    (isCField_one_of_module_finite_isFractionRing_mvPolynomial k F K) x

/-- Every finite extension of a field finite over `RatFunc k`, for `k` algebraically closed,
again has trivial Brauer group. -/
@[sga "4½ Arcata 3.2.2" "finite towers over k(t)"]
theorem brauerGroup_eq_one_of_module_finite_tower_ratFunc (k : Type u) [Field k] [IsAlgClosed k]
    (K : Type u) [Field K] [Algebra (RatFunc k) K] [Module.Finite (RatFunc k) K]
    (K' : Type u) [Field K'] [Algebra K K'] [Module.Finite K K'] [Algebra (RatFunc k) K']
    [IsScalarTower (RatFunc k) K K'] (x : BrauerGroup K') : x = 1 :=
  have : Module.Finite (RatFunc k) K' := Module.Finite.trans K K'
  brauerGroup_eq_one_of_module_finite_ratFunc k K' x
