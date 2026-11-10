module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# The universal algebra of a chart of the Hilbert functor of affine space

Let `R` be a ring and let `W_1, …, W_d ∈ R[x_i ; i ∈ n]`. For an `R`-algebra `B`, a quotient
`B[x] → C` in which the images of the `W_l` form a `B`-basis is determined by the coordinates
`v(m) ∈ B^d` of the images of the monomials `x^m` in that basis. This file records the
polynomial conditions on such a family `v` and constructs the universal `R`-algebra
`ChartAlgebra.Univ W` carrying a family satisfying them, together with the universal quotient
algebra, free with basis the `W_l`. These are the algebraic inputs of the representability of the
subfunctors `F_W` in the proof of Stacks Tag 0B99.

## Main definitions

* `Stacks.Hilbert.ChartAlgebra.coordMap`: for `v : (n →₀ ℕ) → Fin d → B`, the `R`-linear map
  `R[x] → B^d` sending `x^m` to `v(m)`.
* `Stacks.Hilbert.ChartAlgebra.IsDatum`: the conditions `v(W_l) = e_l` and
  `v(x^{m + m'}) = ∑_l v(m')_l · v(x^m W_l)`.
* `Stacks.Hilbert.ChartAlgebra.Univ`: the universal `R`-algebra carrying a datum, with
  `Stacks.Hilbert.ChartAlgebra.lift` its universal property.
* `Stacks.Hilbert.ChartAlgebra.Quot`: for a datum `v` over `B`, the quotient of `B[x]` by the
  kernel of `B[x] → B^d`, and `Stacks.Hilbert.ChartAlgebra.basis`, its basis given by the `W_l`.

## Implementation notes

The second condition says that the kernel of `B[x] → B^d` is an ideal; together with the first
it makes `B[x]` modulo that kernel an algebra free on the `W_l` in which `x^m` has coordinates
`v(m)`. This is the presentation suggested in the source by the description of the points of the
representing scheme, with the structure constants replaced by the coordinates of monomials.

## References

* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace Stacks.Hilbert.ChartAlgebra

variable {R : Type u} [CommRing R] {n : Type u} {d : ℕ}

/-! ### Coordinates of polynomials -/

section CoordMap

variable {B : Type*} [CommRing B] [Algebra R B]

/-- The `R`-linear map `R[x] → B^d` sending the monomial `x^m` to `v m`. -/
def coordMap (v : (n →₀ ℕ) → Fin d → B) : MvPolynomial n R →ₗ[R] (Fin d → B) :=
  (basisMonomials n R).constr R v

/-- The coordinates of a monomial term. -/
@[simp]
theorem coordMap_monomial (v : (n →₀ ℕ) → Fin d → B) (m : n →₀ ℕ) (r : R) :
    coordMap v (monomial m r) = r • v m := by
  have h : coordMap v (monomial m 1) = v m := (basisMonomials n R).constr_basis R v m
  rw [show (monomial m r : MvPolynomial n R) = r • (monomial m 1 : MvPolynomial n R) by
    rw [smul_monomial, smul_eq_mul, mul_one], map_smul, h]

/-- Coordinates are natural in the algebra. -/
theorem coordMap_map {B' : Type*} [CommRing B'] [Algebra R B'] (f : B →ₐ[R] B')
    (v : (n →₀ ℕ) → Fin d → B) (P : MvPolynomial n R) (k : Fin d) :
    coordMap (fun m l ↦ f (v m l)) P k = f (coordMap v P k) := by
  induction P using MvPolynomial.induction_on' with
  | monomial m r => simp
  | add P Q hP hQ => simp only [map_add, Pi.add_apply, hP, hQ]

/-- The conditions on a family `v` of coordinates of monomials for the kernel of
`coordMap v` to cut out an algebra free on the `W_l`: the `W_l` have coordinates the standard
basis, and the kernel is stable under multiplication by monomials. -/
def IsDatum (W : Fin d → MvPolynomial n R) (v : (n →₀ ℕ) → Fin d → B) : Prop :=
  (∀ l, coordMap v (W l) = Pi.single l 1) ∧
    ∀ m m', v (m + m') = ∑ l, v m' l • coordMap v (monomial m 1 * W l)

/-- Algebra maps preserve the standard basis vectors. -/
private theorem map_single_one_apply {F B B' : Type*} [CommRing B] [CommRing B'] [FunLike F B B']
    [RingHomClass F B B'] (f : F) (l k : Fin d) :
    f ((Pi.single l 1 : Fin d → B) k) = (Pi.single l 1 : Fin d → B') k := by
  rcases eq_or_ne l k with rfl | h
  · simp
  · simp [Ne.symm h]

/-- Data are transported along algebra maps. -/
theorem IsDatum.map {W : Fin d → MvPolynomial n R} {v : (n →₀ ℕ) → Fin d → B}
    (hv : IsDatum W v) {B' : Type*} [CommRing B'] [Algebra R B'] (f : B →ₐ[R] B') :
    IsDatum W (fun m l ↦ f (v m l)) := by
  refine ⟨fun l ↦ funext fun k ↦ ?_, fun m m' ↦ funext fun k ↦ ?_⟩
  · rw [coordMap_map, hv.1 l, map_single_one_apply]
  · have := congrFun (hv.2 m m') k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    simp only [coordMap_map, this, map_sum, map_mul]

end CoordMap

/-! ### The universal algebra -/

variable (W : Fin d → MvPolynomial n R)

/-- The variables of the universal algebra: one for each coordinate of each monomial. -/
abbrev Vars (n : Type u) (d : ℕ) : Type u := (n →₀ ℕ) × Fin d

/-- The universal family of coordinates, in the polynomial ring on `Vars n d`. -/
def gens : (n →₀ ℕ) → Fin d → MvPolynomial (Vars n d) R :=
  fun m l ↦ X (m, l)

/-- The polynomial relations expressing `IsDatum` for the universal family. -/
def relations : Set (MvPolynomial (Vars n d) R) :=
  {P | ∃ l k, P = coordMap gens (W l) k -
    (Pi.single l 1 : Fin d → MvPolynomial (Vars n d) R) k} ∪
    {P | ∃ m m' k, P = gens (m + m') k -
      ∑ l, gens m' l * coordMap gens (monomial m 1 * W l) k}

/-- The universal `R`-algebra carrying a datum for `W`. -/
abbrev Univ : Type u := MvPolynomial (Vars n d) R ⧸ Ideal.span (relations W)

/-- The universal datum. -/
def univVec : (n →₀ ℕ) → Fin d → Univ W :=
  fun m l ↦ Ideal.Quotient.mk _ (X (m, l))

/-- An algebra map out of the polynomial ring sends the universal coordinates of a polynomial
to the coordinates for the images of the variables. -/
theorem aeval_coordMap_gens {B : Type*} [CommRing B] [Algebra R B]
    (f : MvPolynomial (Vars n d) R →ₐ[R] B) (P : MvPolynomial n R) (k : Fin d) :
    f (coordMap gens P k) = coordMap (fun m l ↦ f (gens m l)) P k :=
  (coordMap_map f gens P k).symm

/-- An algebra map out of the polynomial ring kills the relations exactly when the images of the
variables form a datum. -/
theorem relations_subset_ker_iff {B : Type*} [CommRing B] [Algebra R B]
    (f : MvPolynomial (Vars n d) R →ₐ[R] B) :
    relations W ⊆ RingHom.ker f ↔ IsDatum W (fun m l ↦ f (gens m l)) := by
  constructor
  · intro h
    refine ⟨fun l ↦ funext fun k ↦ ?_, fun m m' ↦ funext fun k ↦ ?_⟩
    · have := h (Or.inl ⟨l, k, rfl⟩)
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, aeval_coordMap_gens, sub_eq_zero] at this
      rw [this, map_single_one_apply]
    · have := h (Or.inr ⟨m, m', k, rfl⟩)
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, sub_eq_zero, map_sum] at this
      simpa only [map_mul, aeval_coordMap_gens, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        using this
  · rintro ⟨h₁, h₂⟩ P (⟨l, k, rfl⟩ | ⟨m, m', k, rfl⟩)
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, aeval_coordMap_gens, h₁ l,
        map_single_one_apply, sub_eq_zero]
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, sub_eq_zero, map_sum]
      simp only [map_mul, aeval_coordMap_gens]
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun (h₂ m m') k

/-- The universal datum is a datum. -/
theorem isDatum_univVec : IsDatum W (univVec W) :=
  (relations_subset_ker_iff W (Ideal.Quotient.mkₐ R (Ideal.span (relations W)))).mp
    fun P hP ↦ by
      rw [SetLike.mem_coe, RingHom.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hP)

/-- The universal property of `Univ W`: an algebra map classifying a datum. -/
def lift {B : Type*} [CommRing B] [Algebra R B] (v : (n →₀ ℕ) → Fin d → B)
    (hv : IsDatum W v) : Univ W →ₐ[R] B :=
  Ideal.Quotient.liftₐ _ (aeval fun i ↦ v i.1 i.2) fun a ha ↦ RingHom.mem_ker.mp
    (Ideal.span_le.mpr ((relations_subset_ker_iff W (aeval fun i ↦ v i.1 i.2)).mpr (by
      simpa [gens] using hv)) ha)

/-- The classifying map of a datum sends the universal datum to it. -/
@[simp]
theorem lift_univVec {B : Type*} [CommRing B] [Algebra R B] (v : (n →₀ ℕ) → Fin d → B)
    (hv : IsDatum W v) (m : n →₀ ℕ) (l : Fin d) : lift W v hv (univVec W m l) = v m l := by
  change aeval (fun i ↦ v i.1 i.2) (X (m, l)) = _
  exact aeval_X _ _

/-- Algebra maps out of `Univ W` are determined by their values on the universal datum. -/
theorem algHom_ext {B : Type*} [CommRing B] [Algebra R B] {f g : Univ W →ₐ[R] B}
    (h : ∀ m l, f (univVec W m l) = g (univVec W m l)) : f = g :=
  Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i ↦ h i.1 i.2)

/-! ### The quotient algebra attached to a datum -/

section Quot

variable {B : Type u} [CommRing B] [Algebra R B] {W} {v : (n →₀ ℕ) → Fin d → B}

/-- The `B`-linear map `B[x] → B^d` sending the monomial `x^m` to `v m`. -/
def coordMap' (v : (n →₀ ℕ) → Fin d → B) : MvPolynomial n B →ₗ[B] (Fin d → B) :=
  (basisMonomials n B).constr B v

/-- The `B`-linear coordinates of a monomial term. -/
@[simp]
theorem coordMap'_monomial (v : (n →₀ ℕ) → Fin d → B) (m : n →₀ ℕ) (b : B) :
    coordMap' v (monomial m b) = b • v m :=
  coordMap_monomial (R := B) v m b

/-- The `B`-linear coordinates extend the `R`-linear ones. -/
theorem coordMap'_map (v : (n →₀ ℕ) → Fin d → B) (P : MvPolynomial n R) :
    coordMap' v (MvPolynomial.map (algebraMap R B) P) = coordMap v P := by
  induction P using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [map_monomial, coordMap'_monomial, coordMap_monomial, algebraMap_smul]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

/-- The image of `W_l` in `B[x]`. -/
abbrev Wbar (W : Fin d → MvPolynomial n R) (B : Type u) [CommRing B] [Algebra R B] (l : Fin d) :
    MvPolynomial n B :=
  MvPolynomial.map (algebraMap R B) (W l)

/-- **The multiplication rule.** For a datum, the coordinates of a product are determined by the
coordinates of one factor: `v(q p) = ∑_l v(p)_l · v(q W_l)`. -/
theorem coordMap'_mul (hv : IsDatum W v) (q p : MvPolynomial n B) :
    coordMap' v (q * p) = ∑ l, coordMap' v p l • coordMap' v (q * Wbar W B l) := by
  induction p using MvPolynomial.induction_on' with
  | add p p' hp hp' =>
    simp only [mul_add, map_add, hp, hp', Pi.add_apply, add_smul, Finset.sum_add_distrib]
  | monomial m' b =>
    induction q using MvPolynomial.induction_on' with
    | add q q' hq hq' =>
      simp only [add_mul, map_add, hq, hq', smul_add, Finset.sum_add_distrib]
    | monomial m a =>
      rw [monomial_mul_monomial, coordMap'_monomial, coordMap'_monomial, hv.2 m m']
      have hW (l : Fin d) : monomial m a * Wbar W B l =
          a • MvPolynomial.map (algebraMap R B) (monomial m 1 * W l) := by
        rw [map_mul, map_monomial, map_one, smul_eq_C_mul, ← mul_assoc,
          C_mul_monomial, mul_one]
      simp only [hW, map_smul, coordMap'_map, Finset.smul_sum, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [smul_smul, smul_smul]
      congr 1
      ring

/-- The kernel of `coordMap' v` as an ideal of `B[x]`, for a datum `v`. -/
def kerIdeal (hv : IsDatum W v) : Ideal (MvPolynomial n B) where
  carrier := {p | coordMap' v p = 0}
  add_mem' {a b} (ha : coordMap' v a = 0) (hb : coordMap' v b = 0) := by
    change coordMap' v (a + b) = 0
    rw [map_add, ha, hb, add_zero]
  zero_mem' := map_zero _
  smul_mem' q p (hp : coordMap' v p = 0) := by
    change coordMap' v (q * p) = 0
    rw [coordMap'_mul hv, hp]
    simp

/-- The quotient algebra attached to a datum. -/
abbrev Quot (hv : IsDatum W v) : Type u := MvPolynomial n B ⧸ kerIdeal hv

/-- For a datum, the `W_l` have the standard basis vectors as coordinates. -/
theorem coordMap'_Wbar (hv : IsDatum W v) (l : Fin d) :
    coordMap' v (Wbar W B l) = Pi.single l 1 := by
  rw [coordMap'_map, hv.1 l]

/-- In the quotient algebra every polynomial is the combination of the `W_l` given by its
coordinates. -/
theorem mk_eq_sum (hv : IsDatum W v) (p : MvPolynomial n B) :
    Ideal.Quotient.mk (kerIdeal hv) p =
      ∑ l, coordMap' v p l • Ideal.Quotient.mk (kerIdeal hv) (Wbar W B l) := by
  have : p - ∑ l, coordMap' v p l • Wbar W B l ∈ kerIdeal hv := by
    change coordMap' v _ = 0
    rw [map_sub, map_sum]
    simp only [map_smul, coordMap'_Wbar hv]
    rw [sub_eq_zero]
    ext k
    simp [Pi.single_apply]
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at this
  rw [this, ← Ideal.Quotient.mkₐ_eq_mk B, map_sum]
  simp only [map_smul]

/-- The images of the `W_l` form a basis of the quotient algebra attached to a datum. -/
def basis (hv : IsDatum W v) : Module.Basis (Fin d) B (Quot hv) :=
  Module.Basis.mk (v := fun l ↦ Ideal.Quotient.mk (kerIdeal hv) (Wbar W B l))
    (by
      rw [Fintype.linearIndependent_iff]
      intro c hc k
      have hmem : ∑ l, c l • Wbar W B l ∈ kerIdeal hv := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk B, map_sum]
        simpa only [map_smul, Ideal.Quotient.mkₐ_eq_mk] using hc
      simpa [map_sum, coordMap'_Wbar hv, Pi.single_apply] using
        congrFun (show coordMap' v _ = 0 from hmem) k)
    (by
      rintro x -
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [mk_eq_sum hv p]
      exact Submodule.sum_mem _ fun l _ ↦ Submodule.smul_mem _ _
        (Submodule.subset_span ⟨l, rfl⟩))

/-- The basis vectors of the quotient algebra are the classes of the `W_l`. -/
@[simp]
theorem basis_apply (hv : IsDatum W v) (l : Fin d) :
    basis hv l = Ideal.Quotient.mk (kerIdeal hv) (Wbar W B l) :=
  Module.Basis.mk_apply _ _ _

end Quot

end Stacks.Hilbert.ChartAlgebra

end
