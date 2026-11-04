module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The universal quotient of a polynomial ring with a prescribed basis

Let `R` be a commutative ring, let `ι` be a type and let `f₁, …, f_d` be polynomials in
`R[x_i; i ∈ ι]`. For an `R`-algebra `A`, consider the ideals `J ⊂ A[x_i; i ∈ ι]` such that the
images of the `f_l` form an `A`-basis of the quotient `A[x_i] / J`. This file constructs an
`R`-algebra `Univ f` representing this functor of `A`: the `R`-algebra maps `Univ f → A`
correspond bijectively to such ideals, compatibly with base change along `A → B`.

This is the explicit construction in the source's proof of [Stacks, Tag 0B99], which shows that
the subfunctor `F_W` of the Hilbert functor of an affine space is representable by an affine
scheme.

## Implementation notes

The source presents the universal object through structure constants of an algebra structure
on `A^d`. We use an equivalent presentation that needs only one polynomial ring. An ideal `J`
with the basis property is determined by its coordinate map `λ : A[x_i] → A^d` (the
`A`-linear map sending `g` to the coordinates of `g mod J` in the basis), and `λ` is in turn
determined by its values `λ(x^α)` on monomials. A family of values `v α ∈ A^d` comes from such
an ideal exactly when
1. `λ(f_l) = e_l` for every `l`, and
2. `λ(x_i x^α) = ∑_l λ(x^α)_l λ(x_i f_l)` for every monomial `x^α` and every `i`,

the second condition saying that the kernel of `λ` is an ideal. Both are polynomial conditions
in the coordinates `X(α, k) = λ(x^α)_k`, so `Univ f` is the quotient of the polynomial ring in
the variables `X(α, k)` by the ideal they generate.

## Main definitions

* `Stacks.Hilbert.BasisQuotient.IsBasisIdeal`: the images of the `f_l` form a basis of the
  quotient.
* `Stacks.Hilbert.BasisQuotient.Univ`: the representing `R`-algebra.
* `Stacks.Hilbert.BasisQuotient.equiv`: `(Univ f →ₐ[R] A) ≃ {J // IsBasisIdeal f J}`.

## Main results

* `Stacks.Hilbert.BasisQuotient.equiv_comp`: the bijection commutes with base change.

## References

* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
-/

@[expose] public noncomputable section

open MvPolynomial Module

universe u v w

namespace Stacks.Hilbert.BasisQuotient

variable {R : Type*} [CommRing R] {ι : Type u} {d : ℕ} (f : Fin d → MvPolynomial ι R)

section Coordinates

variable {A : Type v} [CommRing A] [Algebra R A]

/-- The polynomial `f l`, with coefficients moved to an `R`-algebra `A`. -/
abbrev fA (A : Type v) [CommRing A] [Algebra R A] (l : Fin d) : MvPolynomial ι A :=
  map (algebraMap R A) (f l)

/-- The images of the `f l` in the quotient by `J` form an `A`-basis of it. -/
def IsBasisIdeal (J : Ideal (MvPolynomial ι A)) : Prop :=
  LinearIndependent A (fun l ↦ Ideal.Quotient.mk J (fA f A l)) ∧
    ⊤ ≤ Submodule.span A (Set.range fun l ↦ Ideal.Quotient.mk J (fA f A l))

/-- The `A`-linear map `A[x_i] → A^d` with prescribed values on the monomials. -/
def lam (v : (ι →₀ ℕ) → Fin d → A) : MvPolynomial ι A →ₗ[A] (Fin d → A) :=
  (basisMonomials ι A).constr A v

/-- The monomial `c x^u` is `c` times the basis vector of `x^u`. -/
private theorem monomial_eq_smul_basisMonomials {S : Type*} [CommSemiring S] (u : ι →₀ ℕ)
    (c : S) : monomial u c = c • basisMonomials ι S u := by
  rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]

/-- The coordinate map sends `c x^u` to `c • v u`. -/
@[simp]
theorem lam_monomial (v : (ι →₀ ℕ) → Fin d → A) (u : ι →₀ ℕ) (c : A) :
    lam v (monomial u c) = c • v u := by
  rw [monomial_eq_smul_basisMonomials, map_smul, lam, Basis.constr_basis]

/-- The coordinate map is compatible with base change along `ψ : A → B`. -/
theorem lam_map {B : Type w} [CommRing B] (ψ : A →+* B) (v : (ι →₀ ℕ) → Fin d → A)
    (g : MvPolynomial ι A) :
    lam (fun u k ↦ ψ (v u k)) (map ψ g) = fun k ↦ ψ (lam v g k) := by
  induction g using MvPolynomial.induction_on' with
  | monomial u c =>
    funext k
    simp [map_monomial]
  | add p q hp hq =>
    funext k
    rw [map_add, map_add, hp, hq]
    simp

end Coordinates

section Universal

variable (ι d) in
/-- The variables of the universal ring: `X(α, k)` is the `k`-th coordinate of `x^α`. -/
abbrev Var : Type u := (ι →₀ ℕ) × Fin d

variable (d) in
/-- The `k`-th coordinate of a polynomial over `R`, as a linear form in the universal
variables. -/
def lin (k : Fin d) : MvPolynomial ι R →ₗ[R] MvPolynomial (Var ι d) R :=
  (basisMonomials ι R).constr R fun u ↦ X (u, k)

/-- The `k`-th coordinate form sends `a x^u` to `a X(u, k)`. -/
@[simp]
theorem lin_monomial (k : Fin d) (u : ι →₀ ℕ) (a : R) :
    lin d k (monomial u a) = C a * X (u, k) := by
  rw [monomial_eq_smul_basisMonomials, map_smul, lin, Basis.constr_basis, C_mul']

/-- The relations saying that the coordinates of `f l` are the `l`-th unit vector. -/
def relBasis : Fin d × Fin d → MvPolynomial (Var ι d) R :=
  fun lk ↦ lin d lk.2 (f lk.1) - if lk.1 = lk.2 then 1 else 0

/-- The relations saying that the kernel of the coordinate map is stable under multiplication
by each variable. -/
def relIdeal : (ι →₀ ℕ) × ι × Fin d → MvPolynomial (Var ι d) R :=
  fun x ↦ X (Finsupp.single x.2.1 1 + x.1, x.2.2) -
    ∑ l, X (x.1, l) * lin d x.2.2 (X x.2.1 * f l)

/-- The ideal of relations of the universal ring. -/
def relations : Ideal (MvPolynomial (Var ι d) R) :=
  Ideal.span (Set.range (relBasis f) ∪ Set.range (relIdeal f))

/-- **The universal ring.** `R`-algebra maps out of it correspond to ideals of `A[x_i]` in which
the images of the `f l` form a basis of the quotient. -/
abbrev Univ := MvPolynomial (Var ι d) R ⧸ relations f

variable {A : Type v} [CommRing A] [Algebra R A]

/-- Evaluating a coordinate form gives the corresponding coordinate of the coordinate map. -/
theorem aeval_lin (ψ : MvPolynomial (Var ι d) R →ₐ[R] A) (k : Fin d) (p : MvPolynomial ι R) :
    ψ (lin d k p) = lam (fun u k ↦ ψ (X (u, k))) (map (algebraMap R A) p) k := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    simp [map_monomial]
  | add p q hp hq =>
    simp [hp, hq]

/-- The coordinates on monomials determined by an `R`-algebra map out of the universal ring. -/
def coord (φ : Univ f →ₐ[R] A) : (ι →₀ ℕ) → Fin d → A :=
  fun u k ↦ φ (Ideal.Quotient.mk _ (X (u, k)))

/-- An `R`-algebra map out of the universal ring kills the image of every relation. -/
private theorem map_mk_relation {φ : Univ f →ₐ[R] A} {r : MvPolynomial (Var ι d) R}
    (hr : r ∈ relations f) : φ (Ideal.Quotient.mk _ r) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- The coordinates of `φ` are the values of `φ` composed with the quotient map on the universal
variables. -/
theorem coord_eq (φ : Univ f →ₐ[R] A) :
    coord f φ = fun u k ↦ (φ.comp (Ideal.Quotient.mkₐ R (relations f))) (X (u, k)) :=
  rfl

end Universal

section FromCoordinates

variable {A : Type v} [CommRing A] [Algebra R A] (v : (ι →₀ ℕ) → Fin d → A)

/-- The two conditions on coordinates on monomials that make them come from an ideal. -/
structure IsAdmissible : Prop where
  basis : ∀ l k, lam v (fA f A l) k = if l = k then 1 else 0
  ideal : ∀ u i k, v (Finsupp.single i 1 + u) k = ∑ l, v u l * lam v (X i * fA f A l) k

variable {f v}

/-- For admissible coordinates, `λ(x_i g) = ∑_l λ(g)_l λ(x_i f_l)` for every polynomial `g`. -/
theorem IsAdmissible.lam_X_mul (hv : IsAdmissible f v) (i : ι) (g : MvPolynomial ι A) :
    lam v (X i * g) = ∑ l, lam v g l • lam v (X i * fA f A l) := by
  induction g using MvPolynomial.induction_on' with
  | monomial u c =>
    funext k
    rw [X, monomial_mul, one_mul, lam_monomial, lam_monomial, Pi.smul_apply, smul_eq_mul,
      hv.ideal, Finset.mul_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← mul_assoc]
    rfl
  | add p q hp hq =>
    rw [mul_add, map_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_add, Pi.add_apply, add_smul]

/-- For admissible coordinates, the coordinate map sends `∑_l c_l f_l` to `c`. -/
theorem IsAdmissible.lam_sum_smul (hv : IsAdmissible f v) (c : Fin d → A) :
    lam v (∑ l, c l • fA f A l) = c := by
  funext k
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv.basis,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The kernel of an admissible coordinate map, as an ideal. -/
def kerIdeal (hv : IsAdmissible f v) : Ideal (MvPolynomial ι A) where
  carrier := {g | lam v g = 0}
  zero_mem' := map_zero _
  add_mem' {a b} ha hb := by simp_all
  smul_mem' h g hg := by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at hg ⊢
    induction h using MvPolynomial.induction_on generalizing g with
    | C a => rw [C_mul', map_smul, hg, smul_zero]
    | add p q hp hq => rw [add_mul, map_add, hp g hg, hq g hg, add_zero]
    | mul_X p i hp =>
      rw [mul_assoc]
      refine hp _ ?_
      rw [hv.lam_X_mul, hg]
      simp

/-- A polynomial lies in `kerIdeal hv` if and only if its coordinates vanish. -/
theorem mem_kerIdeal (hv : IsAdmissible f v) (g : MvPolynomial ι A) :
    g ∈ kerIdeal hv ↔ lam v g = 0 :=
  Iff.rfl

/-- Every polynomial `g` is congruent to `∑_l λ(g)_l f_l` modulo `kerIdeal hv`. -/
theorem IsAdmissible.sub_mem_kerIdeal (hv : IsAdmissible f v) (g : MvPolynomial ι A) :
    g - ∑ l, lam v g l • fA f A l ∈ kerIdeal hv := by
  rw [mem_kerIdeal, map_sub, hv.lam_sum_smul, sub_self]

/-- In the quotient by `kerIdeal hv`, the image of `g` is the sum over `l` of `λ(g)_l` times the
image of `f_l`. -/
private theorem IsAdmissible.mk_eq_sum (hv : IsAdmissible f v) (g : MvPolynomial ι A) :
    Ideal.Quotient.mk (kerIdeal hv) g =
      ∑ l, lam v g l • Ideal.Quotient.mk (kerIdeal hv) (fA f A l) := by
  rw [← Ideal.Quotient.mkₐ_eq_mk A, ← sub_eq_zero]
  have := hv.sub_mem_kerIdeal g
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk A, map_sub, map_sum] at this
  simpa [map_smul] using this

/-- The kernel of an admissible coordinate map has the basis property. -/
theorem IsAdmissible.isBasisIdeal (hv : IsAdmissible f v) : IsBasisIdeal f (kerIdeal hv) := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have hmem : ∑ l, c l • fA f A l ∈ kerIdeal hv := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk A, map_sum]
      simpa [map_smul] using hc
    rw [mem_kerIdeal, hv.lam_sum_smul] at hmem
    exact congrFun hmem
  · rintro q -
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [hv.mk_eq_sum g]
    exact Submodule.sum_mem _ fun l _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

end FromCoordinates

section FromIdeal

variable {A : Type v} [CommRing A] [Algebra R A] {J : Ideal (MvPolynomial ι A)}

/-- The basis of the quotient given by the images of the `f l`. -/
def basisOf (hJ : IsBasisIdeal f J) : Basis (Fin d) A (MvPolynomial ι A ⧸ J) :=
  Basis.mk hJ.1 hJ.2

/-- The `l`-th vector of `basisOf f hJ` is the image of `f l` in the quotient. -/
theorem basisOf_apply (hJ : IsBasisIdeal f J) (l : Fin d) :
    basisOf f hJ l = Ideal.Quotient.mk J (fA f A l) :=
  Basis.mk_apply _ _ _

/-- The coordinates on monomials of the quotient by an ideal with the basis property. -/
def coordOf (hJ : IsBasisIdeal f J) : (ι →₀ ℕ) → Fin d → A :=
  fun u ↦ (basisOf f hJ).equivFun (Ideal.Quotient.mk J (monomial u 1))

/-- The coordinate map attached to `coordOf f hJ` sends `g` to the coordinates of `g mod J` in
`basisOf f hJ`. -/
theorem lam_coordOf (hJ : IsBasisIdeal f J) (g : MvPolynomial ι A) :
    lam (coordOf f hJ) g = (basisOf f hJ).equivFun (Ideal.Quotient.mk J g) := by
  induction g using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [lam_monomial, coordOf, ← Ideal.Quotient.mkₐ_eq_mk A,
      show monomial u c = c • monomial u (1 : A) by rw [smul_monomial, smul_eq_mul, mul_one],
      map_smul, map_smul]
  | add p q hp hq => rw [map_add, hp, hq, map_add, map_add]

/-- The coordinates on monomials of an ideal with the basis property are admissible. -/
theorem isAdmissible_coordOf (hJ : IsBasisIdeal f J) : IsAdmissible f (coordOf f hJ) where
  basis l k := by
    rw [lam_coordOf, ← basisOf_apply f hJ, Basis.equivFun_self]
  ideal u i k := by
    have hu : Ideal.Quotient.mk J (monomial u 1) =
        ∑ l, coordOf f hJ u l • basisOf f hJ l :=
      ((basisOf f hJ).sum_equivFun _).symm
    have : Ideal.Quotient.mk J (monomial (Finsupp.single i 1 + u) (1 : A)) =
        ∑ l, coordOf f hJ u l • Ideal.Quotient.mk J (X i * fA f A l) := by
      rw [← one_mul (1 : A), ← monomial_mul, map_mul, ← X, hu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [basisOf_apply, mul_smul_comm, map_mul]
    change (basisOf f hJ).equivFun _ k = _
    rw [this, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, lam_coordOf]

/-- An ideal with the basis property is the kernel of its own coordinate map. -/
theorem kerIdeal_coordOf (hJ : IsBasisIdeal f J) : kerIdeal (isAdmissible_coordOf f hJ) = J := by
  ext g
  rw [mem_kerIdeal, lam_coordOf, LinearEquiv.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end FromIdeal

section Equiv

variable {A : Type v} [CommRing A] [Algebra R A]

/-- Moving coefficients to `A` sends `x_i f_l` to `x_i` times `fA f A l`. -/
theorem map_X_mul (i : ι) (l : Fin d) :
    map (algebraMap R A) (X i * f l) = X i * fA f A l := by
  rw [RingHom.map_mul, map_X]

/-- Admissible coordinates give an `R`-algebra map out of the universal ring. -/
def univHom {v : (ι →₀ ℕ) → Fin d → A} (hv : IsAdmissible f v) : Univ f →ₐ[R] A :=
  Ideal.Quotient.liftₐ (relations f) (aeval fun x ↦ v x.1 x.2) (by
    intro a ha
    have hX : (fun u k ↦ (aeval (R := R) fun x : Var ι d ↦ v x.1 x.2) (X (u, k))) = v := by
      funext u k
      simp
    refine (Submodule.span_le (p := RingHom.ker (aeval (R := R) fun x : Var ι d ↦ v x.1 x.2))
      |>.mpr ?_) ha
    rintro _ (⟨⟨l, k⟩, rfl⟩ | ⟨⟨u, i, k⟩, rfl⟩)
    · simp only [SetLike.mem_coe, RingHom.mem_ker, relBasis, map_sub]
      change (aeval fun x : Var ι d ↦ v x.1 x.2) (lin d k (f l)) -
        (aeval fun x : Var ι d ↦ v x.1 x.2) (if l = k then 1 else 0) = 0
      rw [aeval_lin, hX, hv.basis]
      split_ifs <;> simp
    · simp only [SetLike.mem_coe, RingHom.mem_ker, relIdeal, map_sub, map_sum, _root_.map_mul]
      change (aeval fun x : Var ι d ↦ v x.1 x.2) (X (Finsupp.single i 1 + u, k)) -
        ∑ l, (aeval fun x : Var ι d ↦ v x.1 x.2) (X (u, l)) *
          (aeval fun x : Var ι d ↦ v x.1 x.2) (lin d k (X i * f l)) = 0
      simp only [aeval_lin, aeval_X]
      rw [hv.ideal, sub_eq_zero]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [map_X_mul])

/-- The coordinates of `univHom f hv` are `v`. -/
theorem coord_univHom {v : (ι →₀ ℕ) → Fin d → A} (hv : IsAdmissible f v) :
    coord f (univHom f hv) = v := by
  funext u k
  change (aeval fun x : Var ι d ↦ v x.1 x.2) (X (u, k)) = v u k
  simp

/-- Equal admissible coordinates give equal `R`-algebra maps. -/
theorem univHom_congr {v w : (ι →₀ ℕ) → Fin d → A} (hv : IsAdmissible f v)
    (hw : IsAdmissible f w) (h : v = w) : univHom f hv = univHom f hw := by
  subst h
  rfl

/-- Equal admissible coordinates give equal kernel ideals. -/
theorem kerIdeal_congr {v w : (ι →₀ ℕ) → Fin d → A} (hv : IsAdmissible f v)
    (hw : IsAdmissible f w) (h : v = w) : kerIdeal hv = kerIdeal hw := by
  subst h
  rfl

/-- Applying `φ` to the `k`-th coordinate form of `p` gives the `k`-th coordinate of `p` under
the coordinate map of `coord f φ`. -/
theorem coord_lin (φ : Univ f →ₐ[R] A) (k : Fin d) (p : MvPolynomial ι R) :
    φ (Ideal.Quotient.mk _ (lin d k p)) = lam (coord f φ) (map (algebraMap R A) p) k :=
  aeval_lin (φ.comp (Ideal.Quotient.mkₐ R (relations f))) k p

/-- The coordinates of an `R`-algebra map out of the universal ring are admissible. -/
theorem isAdmissible_coord (φ : Univ f →ₐ[R] A) : IsAdmissible f (coord f φ) where
  basis l k := by
    have h : φ (Ideal.Quotient.mk _ (relBasis f (l, k))) = 0 :=
      map_mk_relation f (Ideal.subset_span (Set.mem_union_left _ ⟨(l, k), rfl⟩))
    simp only [relBasis] at h
    rw [map_sub, map_sub, coord_lin, sub_eq_zero] at h
    exact h.trans (by split_ifs <;> simp)
  ideal u i k := by
    have h : φ (Ideal.Quotient.mk _ (relIdeal f (u, i, k))) = 0 :=
      map_mk_relation f (Ideal.subset_span (Set.mem_union_right _ ⟨(u, i, k), rfl⟩))
    simp only [relIdeal, map_sub, map_sum, _root_.map_mul, coord_lin, map_X] at h
    exact sub_eq_zero.mp h

/-- An `R`-algebra map out of the universal ring is recovered from its coordinates. -/
theorem univHom_coord (φ : Univ f →ₐ[R] A) : univHom f (isAdmissible_coord f φ) = φ := by
  refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun x ↦ ?_)
  change (aeval fun x : Var ι d ↦ coord f φ x.1 x.2) (X x) = φ (Ideal.Quotient.mk _ (X x))
  simp [coord]

/-- **The universal property.** `R`-algebra maps from the universal ring to `A` correspond to
ideals of `A[x_i; i ∈ ι]` in whose quotient the images of `f₁, …, f_d` form a basis. -/
def equiv : (Univ f →ₐ[R] A) ≃ {J : Ideal (MvPolynomial ι A) // IsBasisIdeal f J} where
  toFun φ := ⟨kerIdeal (isAdmissible_coord f φ), (isAdmissible_coord f φ).isBasisIdeal⟩
  invFun J := univHom f (isAdmissible_coordOf f J.2)
  left_inv φ := by
    dsimp only
    have hc : coordOf f (isAdmissible_coord f φ).isBasisIdeal = coord f φ := by
      funext u
      have hv := isAdmissible_coord f φ
      have hb : Ideal.Quotient.mk (kerIdeal hv) (monomial u 1) =
          ∑ l, coord f φ u l • basisOf f hv.isBasisIdeal l := by
        simpa [basisOf_apply] using hv.mk_eq_sum (monomial u 1)
      rw [coordOf, hb, Basis.equivFun_apply, Basis.repr_sum_self]
    exact (univHom_congr f _ _ hc).trans (univHom_coord f φ)
  right_inv J := Subtype.ext <|
    (kerIdeal_congr f (isAdmissible_coord f _) _ (coord_univHom f _)).trans (kerIdeal_coordOf f J.2)

/-- A polynomial lies in the ideal attached to `φ` if and only if its coordinates under
`coord f φ` vanish. -/
theorem equiv_apply_coe (φ : Univ f →ₐ[R] A) (g : MvPolynomial ι A) :
    g ∈ (equiv f φ).1 ↔ lam (coord f φ) g = 0 :=
  Iff.rfl

/-- **Base change.** The ideal attached to `ψ ∘ φ` is generated by the image of the ideal
attached to `φ`. -/
theorem equiv_comp {B : Type w} [CommRing B] [Algebra R B] (φ : Univ f →ₐ[R] A)
    (ψ : A →ₐ[R] B) :
    (equiv f (ψ.comp φ)).1 = Ideal.map (MvPolynomial.map (ψ : A →+* B)) (equiv f φ).1 := by
  have hc : coord f (ψ.comp φ) = fun u k ↦ (ψ : A →+* B) (coord f φ u k) := rfl
  have hfB (l : Fin d) : MvPolynomial.map (ψ : A →+* B) (fA f A l) = fA f B l := by
    rw [MvPolynomial.map_map, AlgHom.comp_algebraMap_of_tower]
  have hv := isAdmissible_coord f φ
  have hker : (equiv f φ).1 = kerIdeal hv := rfl
  have key : ∀ g : MvPolynomial ι B, g - ∑ l, lam (coord f (ψ.comp φ)) g l • fA f B l ∈
      Ideal.map (MvPolynomial.map (ψ : A →+* B)) (equiv f φ).1 := by
    intro g
    induction g using MvPolynomial.induction_on' with
    | monomial u c =>
      have h1 := Ideal.mul_mem_left _ (C c) (Ideal.mem_map_of_mem
        (MvPolynomial.map (ψ : A →+* B)) (hv.sub_mem_kerIdeal (monomial u 1)))
      rw [← hker] at h1
      have e : monomial u c - ∑ l, lam (coord f (ψ.comp φ)) (monomial u c) l • fA f B l =
          C c * MvPolynomial.map (ψ : A →+* B)
            (monomial u 1 - ∑ l, lam (coord f φ) (monomial u 1) l • fA f A l) := by
        simp only [lam_monomial, hc, Pi.smul_apply, smul_eq_mul, smul_eq_C_mul,
          map_sub, map_sum, _root_.map_mul, map_C, hfB, map_monomial, map_one, mul_sub,
          Finset.mul_sum, C_mul_monomial, mul_one, one_mul, mul_assoc]
      rwa [e]
    | add p q hp hq =>
      convert Ideal.add_mem _ hp hq using 1
      rw [map_add]
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      abel
  refine le_antisymm
    (fun g hg ↦ by simpa [(equiv_apply_coe f (ψ.comp φ) g).mp hg] using key g) ?_
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap, equiv_apply_coe, hc, lam_map]
  rw [equiv_apply_coe] at hg
  funext k
  simp [hg]

end Equiv

end Stacks.Hilbert.BasisQuotient

end
