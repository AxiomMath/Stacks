module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesGrading
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreNormalCone
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalAlgebraSheafSections
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedGenerators
public import StacksFrontier.RingTheory.GradedAlgebra.SymmetricAway.LineChart
public import StacksFrontier.RingTheory.RegularLocalRing.AssociatedGradedPolynomial

/-!
# The associated graded ring of `(I, s)` in `A[s]`

Let `A` be a commutative ring, `I ⊆ A` an ideal and `J = (I, s) ⊆ A[s]` the ideal of the centre of
the blowup at infinity on the chart at infinity (`Stacks.Chow.infinityChartIdeal`). The source
computes the exceptional divisor of the blowup at infinity of a regular immersion from the
associated graded ring of `J`. This file supplies the two algebraic facts that computation rests
on.

* **`Gr_J(A[s]) = Gr_I(A)[T]`**, with `T` the class of `s` in degree one. The powers of `J` are
  described coefficientwise (`Stacks.Chow.mem_pow_infinityChartIdeal_iff`: `f ∈ Jᵐ` exactly when
  the coefficient of `sʲ` lies in `I^(m - j)`), so `Jⁿ/Jⁿ⁺¹ = ⨁_{j ≤ n} I^(n-j)/I^(n-j+1) sʲ`.
  No hypothesis on `I` is needed.
* **`Sym_R(M ⊕ R) = Sym_R(M)[T]`**, for a module `N` split as `N = j(M) ⊕ R t₀`
  (`Stacks.SymmetricAway.LineSplitting`), with `T` the class of `t₀`.

## Main definitions

* `Stacks.Chow.infinityChartGradedMap`: the ring map `Gr_I(A)[T] ⟶ Gr_J(A[s])`, `T ↦ s̄`.
* `Stacks.Chow.infinityChartGradedEquiv`: the same map as a ring isomorphism.
* `Stacks.SymmetricAway.LineSplitting.symPolynomialEquiv`: the ring isomorphism
  `Sym_R(N) ≃ Sym_R(M)[T]`.
* `Stacks.Blowup.reesToGraded`: the quotient map `R[Jt] ⟶ Gr_J(R)` of the Rees algebra.
* `Stacks.Blowup.baseChangeReesToGraded`: the map `R/J ⊗_R R[Jt] ⟶ Gr_J(R)` it induces, for an
  `R`-algebra which is a quotient of `R` by an ideal contained in `J`.

## Main results

* `Stacks.Chow.bijective_infinityChartGradedMap`: `Gr_I(A)[T] ⟶ Gr_J(A[s])` is bijective.
* `Stacks.Chow.infinityChartGradedMap_monomial_classOfPow`: on the monomial `ā Tʲ`, `a ∈ Iᵏ`, the
  map is the class of `a sʲ` in degree `k + j`.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
-/

@[expose] public noncomputable section

open Polynomial

namespace AssociatedGraded

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- The class in degree `n` of an element of `Iⁿ⁺¹` vanishes. -/
theorem classOfPow_eq_zero {n : ℕ} {a : A} (ha : a ∈ I ^ n) (ha' : a ∈ I ^ (n + 1)) :
    classOfPow I n ⟨a, ha⟩ = 0 := by
  show DFinsupp.single n _ = 0
  rw [DFinsupp.single_eq_zero]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  show a ∈ power (M := A) I (n + 1)
  rw [ring_power_eq]
  exact ha'

/-- Two elements of `Iⁿ` congruent modulo `Iⁿ⁺¹` have the same class in degree `n`. -/
theorem classOfPow_eq_of_sub_mem {n : ℕ} {a b : A} (ha : a ∈ I ^ n) (hb : b ∈ I ^ n)
    (hab : a - b ∈ I ^ (n + 1)) : classOfPow I n ⟨a, ha⟩ = classOfPow I n ⟨b, hb⟩ := by
  rw [← sub_eq_zero, ← map_sub]
  exact classOfPow_eq_zero I _ hab

/-- The map of associated graded rings induced by a ring homomorphism carries the class of `a` to
the class of the image of `a`. -/
theorem gradedRingMapOfRingHom_classOfPow {B : Type*} [CommRing B] (f : A →+* B)
    {I' : Ideal B} (hI : I.map f ≤ I') (n : ℕ) (a : ↥(I ^ n)) :
    gradedRingMapOfRingHom f hI (classOfPow I n a) =
      classOfPow I' n ⟨f a, (Ideal.map_le_iff_le_comap.1 (Ideal.map_pow f I n ▸
        Ideal.pow_right_mono hI n)) a.2⟩ := by
  show gradedRingMapOfRingHom f hI (DirectSum.of _ n _) = DirectSum.of _ n _
  rw [gradedRingMapOfRingHom_of, pieceMapOfRingHom_mk]

/-- The associated graded ring is spanned additively by the classes of elements of the powers. -/
theorem induction_classOfPow {motive : gradedRing I → Prop} (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (cls : ∀ (n : ℕ) (a : ↥(I ^ n)), motive (classOfPow I n a)) (x : gradedRing I) :
    motive x := by
  induction x using DirectSum.induction_on with
  | zero => exact zero
  | of n y =>
    induction y using Submodule.Quotient.induction_on with
    | _ b => exact cls n ⟨b.1, by simpa only [ring_power_eq] using b.2⟩
  | add x y hx hy => exact add x y hx hy

end AssociatedGraded

namespace Stacks.Chow

open AssociatedGraded

variable {A : Type*} [CommRing A] (I : Ideal A)

/-! ### `Gr_J(A[s]) = Gr_I(A)[T]` -/

/-- The constants of `I` lie in `J = (I, s)`. -/
theorem map_C_le_infinityChartIdeal : I.map (C : A →+* A[X]) ≤ infinityChartIdeal I :=
  le_sup_left

/-- The coordinate `s` lies in `J¹`. -/
theorem X_mem_infinityChartIdeal_pow_one : (Polynomial.X : A[X]) ∈ infinityChartIdeal I ^ 1 := by
  rw [pow_one]
  exact X_mem_infinityChartIdeal I

/-- The class `s̄` of the coordinate `s` in degree one of `Gr_J(A[s])`. -/
def infinityChartCoordinateClass : gradedRing (infinityChartIdeal I) :=
  classOfPow (infinityChartIdeal I) 1 ⟨Polynomial.X, X_mem_infinityChartIdeal_pow_one I⟩

/-- **The comparison map `Gr_I(A)[T] ⟶ Gr_J(A[s])`**: the map of associated graded rings induced
by `A ⟶ A[s]` on coefficients, and `T ↦ s̄`. -/
def infinityChartGradedMap : (gradedRing I)[X] →+* gradedRing (infinityChartIdeal I) :=
  eval₂RingHom (gradedRingMapOfRingHom C (map_C_le_infinityChartIdeal I))
    (infinityChartCoordinateClass I)

/-- `a sʲ ∈ Jᵏ⁺ʲ` for `a ∈ Iᵏ`. -/
theorem C_mul_X_pow_mem {k : ℕ} {a : A} (ha : a ∈ I ^ k) (j : ℕ) :
    C a * (Polynomial.X : A[X]) ^ j ∈ infinityChartIdeal I ^ (k + j) := by
  rw [pow_add]
  exact Ideal.mul_mem_mul (C_mem_pow_infinityChartIdeal ha) (X_pow_mem_pow_infinityChartIdeal I j)

/-- The `j`-th power of the class of `s` is the class of `sʲ` in degree `j`. -/
theorem infinityChartCoordinateClass_pow (j : ℕ) :
    infinityChartCoordinateClass I ^ j =
      classOfPow (infinityChartIdeal I) j
        ⟨(Polynomial.X : A[X]) ^ j, X_pow_mem_pow_infinityChartIdeal I j⟩ := by
  induction j with
  | zero =>
    rw [pow_zero]
    rfl
  | succ j ih =>
    rw [pow_succ, ih, infinityChartCoordinateClass, ← classOfPow_mul]
    exact classOfPow_congr _ rfl (by exact (pow_succ _ _).symm)

/-- **On the monomial `ā Tʲ`, `a ∈ Iᵏ`, the comparison map is the class of `a sʲ` in degree
`k + j`.** -/
theorem infinityChartGradedMap_monomial_classOfPow (j k : ℕ) (a : ↥(I ^ k)) :
    infinityChartGradedMap I (monomial j (classOfPow I k a)) =
      classOfPow (infinityChartIdeal I) (k + j)
        ⟨C a.1 * (Polynomial.X : A[X]) ^ j, C_mul_X_pow_mem I a.2 j⟩ := by
  rw [infinityChartGradedMap, coe_eval₂RingHom, eval₂_monomial,
    gradedRingMapOfRingHom_classOfPow, infinityChartCoordinateClass_pow, ← classOfPow_mul]

/-- The `j`-th coefficient of an element of `Jⁿ` lies in `Iⁿ⁻ʲ`. -/
theorem coeff_mem_pow_sub {n : ℕ} {f : A[X]} (hf : f ∈ infinityChartIdeal I ^ n) (j : ℕ) :
    f.coeff j ∈ I ^ (n - j) :=
  mem_pow_infinityChartIdeal_iff.1 hf j

/-- The degree-`n` piece of the inverse comparison, on representatives: `f ∈ Jⁿ` goes to
`∑_{j ≤ n} (class of the coefficient of sʲ in degree n - j) Tʲ`. -/
def infinityChartGradedInvRep (n : ℕ) : ↥(infinityChartIdeal I ^ n) →+ (gradedRing I)[X] where
  toFun f := ∑ j ∈ Finset.range (n + 1),
    monomial j (classOfPow I (n - j) ⟨(f : A[X]).coeff j, coeff_mem_pow_sub I f.2 j⟩)
  map_zero' := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have h : (⟨((0 : ↥(infinityChartIdeal I ^ n)) : A[X]).coeff j,
        coeff_mem_pow_sub I (0 : ↥(infinityChartIdeal I ^ n)).2 j⟩ : ↥(I ^ (n - j))) = 0 :=
      Subtype.ext (coeff_zero j)
    rw [h, map_zero, map_zero]
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_add, ← map_add]
    congr 2
    exact Subtype.ext (coeff_add _ _ _)

/-- The value of `infinityChartGradedInvRep` on a representative. -/
theorem infinityChartGradedInvRep_apply (n : ℕ) (f : ↥(infinityChartIdeal I ^ n)) :
    infinityChartGradedInvRep I n f = ∑ j ∈ Finset.range (n + 1),
      monomial j (classOfPow I (n - j) ⟨(f : A[X]).coeff j, coeff_mem_pow_sub I f.2 j⟩) := rfl

/-- `infinityChartGradedInvRep` kills `Jⁿ⁺¹`. -/
theorem infinityChartGradedInvRep_eq_zero {n : ℕ} (f : ↥(infinityChartIdeal I ^ n))
    (hf : (f : A[X]) ∈ infinityChartIdeal I ^ (n + 1)) : infinityChartGradedInvRep I n f = 0 := by
  rw [infinityChartGradedInvRep_apply]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [classOfPow_eq_zero I _ ?_, map_zero]
  have := coeff_mem_pow_sub I hf j
  rwa [show n + 1 - j = n - j + 1 by
    have := Finset.mem_range.1 hj
    omega] at this

/-- The degree-`n` piece of the inverse comparison `Jⁿ/Jⁿ⁺¹ ⟶ Gr_I(A)[T]`. -/
def infinityChartGradedInvPiece (n : ℕ) :
    piece (M := A[X]) (infinityChartIdeal I) n →+ (gradedRing I)[X] :=
  AddMonoidHom.mk'
    (fun c => Quotient.liftOn c
      (fun y => infinityChartGradedInvRep I n
        ⟨(y : A[X]), mem_pow_of_mem_associatedGradedPower y.2⟩)
      (by
        intro y z hyz
        have h : ((y : A[X]) - (z : A[X])) ∈
            power (M := A[X]) (infinityChartIdeal I) (n + 1) :=
          (Submodule.Quotient.eq ((power (M := A[X]) (infinityChartIdeal I) (n + 1)).comap
            (Submodule.subtype (power (M := A[X]) (infinityChartIdeal I) n)))).mp
            (Quotient.sound hyz)
        rw [← sub_eq_zero, ← map_sub]
        exact infinityChartGradedInvRep_eq_zero I _ (mem_pow_of_mem_associatedGradedPower h)))
    (by
      intro c d
      induction c using Quotient.inductionOn with
      | _ y =>
        induction d using Quotient.inductionOn with
        | _ z =>
          change infinityChartGradedInvRep I n ⟨(y : A[X]) + (z : A[X]), _⟩ =
            infinityChartGradedInvRep I n ⟨(y : A[X]), _⟩ +
              infinityChartGradedInvRep I n ⟨(z : A[X]), _⟩
          rw [← map_add]
          rfl)

/-- **The inverse comparison `Gr_J(A[s]) ⟶ Gr_I(A)[T]`**, as an additive map. -/
def infinityChartGradedInv : gradedRing (infinityChartIdeal I) →+ (gradedRing I)[X] :=
  DirectSum.toAddMonoid (infinityChartGradedInvPiece I)

/-- The inverse `Gr_J(A[s]) ⟶ Gr_I(A)[T]` on the class of a representative. -/
theorem infinityChartGradedInv_classOfPow (n : ℕ) (f : ↥(infinityChartIdeal I ^ n)) :
    infinityChartGradedInv I (classOfPow (infinityChartIdeal I) n f) =
      infinityChartGradedInvRep I n f := by
  show DirectSum.toAddMonoid _ (DirectSum.of _ n _) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

/-- The truncation of `f` below degree `n + 1` is congruent to `f` modulo `Jⁿ⁺¹`. -/
theorem sub_sum_range_mem {n : ℕ} (f : A[X]) :
    f - ∑ j ∈ Finset.range (n + 1), C (f.coeff j) * (Polynomial.X : A[X]) ^ j ∈
      infinityChartIdeal I ^ (n + 1) := by
  rw [mem_pow_infinityChartIdeal_iff]
  intro j
  rw [coeff_sub, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range (n + 1)) j (fun k => f.coeff k)]
  split_ifs with hj
  · rw [sub_self]
    exact zero_mem _
  · rw [sub_zero, show n + 1 - j = 0 by
      have := Finset.mem_range.not.1 hj
      omega, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

/-- A monomial term of an element of `Jⁿ` lies in `Jⁿ`. -/
theorem C_coeff_mul_X_pow_mem {n : ℕ} {f : A[X]} (hf : f ∈ infinityChartIdeal I ^ n) (j : ℕ) :
    C (f.coeff j) * (Polynomial.X : A[X]) ^ j ∈ infinityChartIdeal I ^ n := by
  rw [mem_pow_infinityChartIdeal_iff]
  intro l
  rw [coeff_C_mul_X_pow]
  split_ifs with hl
  · subst hl
    exact coeff_mem_pow_sub I hf l
  · exact zero_mem _

/-- `Gr_I(A)[T] ⟶ Gr_J(A[s])` is a left inverse of `infinityChartGradedInv`. -/
theorem infinityChartGradedMap_comp_inv (x : gradedRing (infinityChartIdeal I)) :
    infinityChartGradedMap I (infinityChartGradedInv I x) = x := by
  induction x using AssociatedGraded.induction_classOfPow with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | cls n f =>
    rw [infinityChartGradedInv_classOfPow]
    rw [infinityChartGradedInvRep_apply, map_sum]
    have key : ∀ j ∈ Finset.range (n + 1),
        infinityChartGradedMap I (monomial j (classOfPow I (n - j)
          ⟨(f : A[X]).coeff j, coeff_mem_pow_sub I f.2 j⟩)) =
        classOfPow (infinityChartIdeal I) n ⟨C ((f : A[X]).coeff j) * (Polynomial.X : A[X]) ^ j,
          C_coeff_mul_X_pow_mem I f.2 j⟩ := by
      intro j hj
      rw [infinityChartGradedMap_monomial_classOfPow]
      exact classOfPow_congr _ (by have := Finset.mem_range.1 hj; omega) (by rfl)
    rw [Finset.sum_congr rfl key, ← map_sum]
    have hs : (∑ j ∈ Finset.range (n + 1), (⟨C ((f : A[X]).coeff j) * Polynomial.X ^ j,
        C_coeff_mul_X_pow_mem I f.2 j⟩ : ↥(infinityChartIdeal I ^ n))) =
        ⟨∑ j ∈ Finset.range (n + 1), C ((f : A[X]).coeff j) * Polynomial.X ^ j,
          sum_mem fun j _ => C_coeff_mul_X_pow_mem I f.2 j⟩ :=
      Subtype.ext (Submodule.coe_sum _ _ _)
    have h := sub_sum_range_mem I (n := n) (f : A[X])
    rw [← neg_mem_iff, neg_sub] at h
    rw [hs]
    exact classOfPow_eq_of_sub_mem _ _ f.2 h

/-- `infinityChartGradedInv` is a left inverse of `Gr_I(A)[T] ⟶ Gr_J(A[s])`. -/
theorem infinityChartGradedInv_comp_map (p : (gradedRing I)[X]) :
    infinityChartGradedInv I (infinityChartGradedMap I p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial j x =>
    induction x using AssociatedGraded.induction_classOfPow with
    | zero => rw [monomial_zero_right, map_zero, map_zero]
    | add x y hx hy => rw [map_add (monomial j), map_add, map_add, hx, hy]
    | cls k a =>
      rw [infinityChartGradedMap_monomial_classOfPow, infinityChartGradedInv_classOfPow]
      rw [infinityChartGradedInvRep_apply, Finset.sum_eq_single j]
      · congr 1
        refine classOfPow_congr _ (by omega) ?_
        show (C (a : A) * Polynomial.X ^ j).coeff j = (a : A)
        rw [coeff_C_mul_X_pow, ite_eq_left rfl]
      · intro l _ hl
        rw [classOfPow_eq_zero I _ (by
          rw [coeff_C_mul_X_pow, ite_eq_right hl]
          exact zero_mem _), monomial_zero_right]
      · intro hj
        exact absurd (Finset.mem_range.2 (by omega)) hj

/-- **`Gr_I(A)[T] ⟶ Gr_J(A[s])` is bijective**: `Gr_J(A[s]) = Gr_I(A)[T]`. -/
theorem bijective_infinityChartGradedMap : Function.Bijective (infinityChartGradedMap I) :=
  ⟨Function.LeftInverse.injective (infinityChartGradedInv_comp_map I),
    Function.RightInverse.surjective (infinityChartGradedMap_comp_inv I)⟩

/-- **`Gr_J(A[s]) = Gr_I(A)[T]`, as rings**, `T` corresponding to the class `s̄` of `s`. -/
def infinityChartGradedEquiv : (gradedRing I)[X] ≃+* gradedRing (infinityChartIdeal I) :=
  RingEquiv.ofBijective (infinityChartGradedMap I) (bijective_infinityChartGradedMap I)

/-- `infinityChartGradedEquiv` is `infinityChartGradedMap`. -/
@[simp]
theorem infinityChartGradedEquiv_apply (p : (gradedRing I)[X]) :
    infinityChartGradedEquiv I p = infinityChartGradedMap I p := rfl

end Stacks.Chow

/-! ### `Sym_R(M ⊕ R) = Sym_R(M)[T]` -/

namespace Stacks.SymmetricAway

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (S : LineSplitting R M N)

/-- The linear map `N ⟶ Sym_R(M)[T]`, `n ↦ p(n) + q(n) T`. -/
def LineSplitting.toPolynomialLinear : N →ₗ[R] (SymmetricAlgebra R M)[X] :=
  (Polynomial.CAlgHom.toLinearMap ∘ₗ SymmetricAlgebra.ι R M ∘ₗ S.p) +
    LinearMap.smulRight S.q (Polynomial.X : (SymmetricAlgebra R M)[X])

/-- **`Sym_R(N) ⟶ Sym_R(M)[T]`** along a splitting `N = j(M) ⊕ R t₀`: `n ↦ p(n) + q(n) T`. -/
def LineSplitting.toPolynomial : SymmetricAlgebra R N →ₐ[R] (SymmetricAlgebra R M)[X] :=
  SymmetricAlgebra.lift S.toPolynomialLinear

/-- `Sym(N) ⟶ Sym(M)[T]` on a generator `n`: `p(n) + q(n) T`. -/
@[simp]
theorem LineSplitting.toPolynomial_ι (n : N) :
    S.toPolynomial (SymmetricAlgebra.ι R N n) =
      C (SymmetricAlgebra.ι R M (S.p n)) + S.q n • (Polynomial.X : (SymmetricAlgebra R M)[X]) := by
  rw [LineSplitting.toPolynomial, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- `Sym(N) ⟶ Sym(M)[T]` on a generator `n`, with the scalar `q(n)` as a constant. -/
theorem LineSplitting.toPolynomial_ι' (n : N) :
    S.toPolynomial (SymmetricAlgebra.ι R N n) =
      C (SymmetricAlgebra.ι R M (S.p n)) +
        C (algebraMap R (SymmetricAlgebra R M) (S.q n)) *
          (Polynomial.X : (SymmetricAlgebra R M)[X]) := by
  rw [S.toPolynomial_ι, Algebra.smul_def, Polynomial.algebraMap_apply]

/-- The inclusion `Sym_R(M) ⟶ Sym_R(N)` induced by `j`. -/
def LineSplitting.symInclusion : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N :=
  SymmetricAlgebra.lift (SymmetricAlgebra.ι R N ∘ₗ S.j)

/-- `Sym(M) ⟶ Sym(N)` on a generator. -/
theorem LineSplitting.symInclusion_ι (m : M) :
    S.symInclusion (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (S.j m) :=
  SymmetricAlgebra.lift_ι_apply _ m

/-- **`Sym_R(M)[T] ⟶ Sym_R(N)`**, `T ↦ t₀`, inverse to `toPolynomial`. -/
def LineSplitting.ofPolynomial : (SymmetricAlgebra R M)[X] →ₐ[R] SymmetricAlgebra R N :=
  Polynomial.eval₂AlgHom S.symInclusion (SymmetricAlgebra.ι R N S.t₀)
    (fun _ => Commute.all _ _)

/-- `Sym(M)[T] ⟶ Sym(N)` on a constant. -/
private theorem LineSplitting.ofPolynomial_C (x : SymmetricAlgebra R M) :
    S.ofPolynomial (C x) = S.symInclusion x := by
  rw [LineSplitting.ofPolynomial, Polynomial.eval₂AlgHom_apply, eval₂_C]
  rfl

/-- `Sym(M)[T] ⟶ Sym(N)` on `T`. -/
private theorem LineSplitting.ofPolynomial_X :
    S.ofPolynomial (Polynomial.X : (SymmetricAlgebra R M)[X]) = SymmetricAlgebra.ι R N S.t₀ := by
  rw [LineSplitting.ofPolynomial, Polynomial.eval₂AlgHom_apply, eval₂_X]

/-- `Sym(M)[T] ⟶ Sym(N)` is a left inverse of `Sym(N) ⟶ Sym(M)[T]`. -/
theorem LineSplitting.ofPolynomial_toPolynomial (x : SymmetricAlgebra R N) :
    S.ofPolynomial (S.toPolynomial x) = x := by
  have h : S.ofPolynomial.comp S.toPolynomial = AlgHom.id R _ := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun n => ?_)
    show S.ofPolynomial (S.toPolynomial (SymmetricAlgebra.ι R N n)) = SymmetricAlgebra.ι R N n
    rw [LineSplitting.toPolynomial_ι, map_add, map_smul, S.ofPolynomial_C, S.ofPolynomial_X,
      LineSplitting.symInclusion_ι, ← map_smul, ← map_add, S.j_p_add_q_smul]
  exact AlgHom.congr_fun h x

/-- `Sym(N) ⟶ Sym(M)[T]` is a left inverse of `Sym(M)[T] ⟶ Sym(N)`. -/
theorem LineSplitting.toPolynomial_ofPolynomial (p : (SymmetricAlgebra R M)[X]) :
    S.toPolynomial (S.ofPolynomial p) = p := by
  have hC : S.toPolynomial.comp S.symInclusion = Polynomial.CAlgHom := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
    show S.toPolynomial (S.symInclusion (SymmetricAlgebra.ι R M m)) =
      C (SymmetricAlgebra.ι R M m)
    rw [LineSplitting.symInclusion_ι, LineSplitting.toPolynomial_ι, S.p_j, S.q_j, zero_smul,
      add_zero]
  have h : (S.toPolynomial.comp S.ofPolynomial).toRingHom = RingHom.id _ := by
    refine Polynomial.ringHom_ext (fun x => ?_) ?_
    · show S.toPolynomial (S.ofPolynomial (C x)) = C x
      rw [S.ofPolynomial_C]
      exact AlgHom.congr_fun hC x
    · show S.toPolynomial (S.ofPolynomial (Polynomial.X : (SymmetricAlgebra R M)[X])) =
        Polynomial.X
      rw [S.ofPolynomial_X, LineSplitting.toPolynomial_ι, S.p_t₀, S.q_t₀, map_zero, map_zero,
        one_smul, zero_add]
  exact RingHom.congr_fun h p

/-- **`Sym_R(N) ≃ Sym_R(M)[T]`** along a splitting `N = j(M) ⊕ R t₀`, `t₀ ↦ T`. -/
def LineSplitting.symPolynomialEquiv : SymmetricAlgebra R N ≃ₐ[R] (SymmetricAlgebra R M)[X] :=
  AlgEquiv.ofAlgHom S.toPolynomial S.ofPolynomial
    (AlgHom.ext S.toPolynomial_ofPolynomial) (AlgHom.ext S.ofPolynomial_toPolynomial)

/-- `symPolynomialEquiv` is `toPolynomial`. -/
@[simp]
theorem LineSplitting.symPolynomialEquiv_apply (x : SymmetricAlgebra R N) :
    S.symPolynomialEquiv x = S.toPolynomial x := rfl

end Stacks.SymmetricAway


/-! ### The Rees algebra modulo its ideal is the associated graded ring -/

namespace Stacks.Blowup

open AssociatedGraded TensorProduct

variable {R : Type*} [CommRing R] (J : Ideal R)

/-- The degree-`n` piece of `R[Jt] ⟶ Gr_J(R)`: the class of the coefficient. -/
def reesPieceToGraded (n : ℕ) : reesGrading J n →+ gradedRing J :=
  (classOfPow J n).comp (reesGradingEquivPow J n).symm.toLinearMap.toAddMonoidHom

/-- The degree-`n` part of `reesToGraded` on an element. -/
theorem reesPieceToGraded_apply (n : ℕ) (f : reesGrading J n) :
    reesPieceToGraded J n f =
      classOfPow J n ⟨((f : reesAlgebra J) : R[X]).coeff n, (f : reesAlgebra J).2 n⟩ :=
  congrArg (classOfPow J n) (Subtype.ext (coe_reesGradingEquivPow_symm J f))

/-- The leading coefficient of a product of homogeneous elements of the Rees algebra. -/
theorem coeff_mul_of_mem {i j : ℕ} {a b : reesAlgebra J} (ha : a ∈ reesGrading J i)
    (hb : b ∈ reesGrading J j) :
    ((a * b : reesAlgebra J) : R[X]).coeff (i + j) = (a : R[X]).coeff i * (b : R[X]).coeff j := by
  rw [Subalgebra.coe_mul]
  conv_lhs => rw [coe_eq_monomial J ha, coe_eq_monomial J hb]
  rw [monomial_mul_monomial, coeff_monomial_same]


/-- `R[Jt] ⟶ Gr_J(R)` on the direct sum of the homogeneous pieces of the Rees algebra. -/
def reesSumToGraded : (DirectSum ℕ fun n => reesGrading J n) →+* gradedRing J :=
  DirectSum.toSemiring (reesPieceToGraded J)
    ((reesPieceToGraded_apply J 0 _).trans ((classOfPow_congr J rfl (by exact coeff_one_zero)).trans
      (AssociatedGraded.classOfPow_zero_one J (by simp))))
    (fun {i j} a b => by
      rw [reesPieceToGraded_apply, reesPieceToGraded_apply, reesPieceToGraded_apply,
        ← classOfPow_mul]
      exact classOfPow_congr J rfl (by exact coeff_mul_of_mem J a.2 b.2))

/-- **The quotient map `R[Jt] ⟶ Gr_J(R)`** of the Rees algebra onto the associated graded ring,
`a tⁿ ↦` the class of `a ∈ Jⁿ` in degree `n`. -/
def reesToGraded : reesAlgebra J →+* gradedRing J :=
  (reesSumToGraded J).comp (DirectSum.decomposeRingEquiv (reesGrading J)).toRingHom

/-- `R[Jt] ⟶ Gr_J(R)` on a homogeneous element of degree `n`. -/
theorem reesToGraded_of_mem {n : ℕ} {f : reesAlgebra J} (hf : f ∈ reesGrading J n) :
    reesToGraded J f =
      classOfPow J n ⟨((f : reesAlgebra J) : R[X]).coeff n, f.2 n⟩ := by
  show reesSumToGraded J (DirectSum.decompose (reesGrading J) f) = _
  rw [DirectSum.decompose_of_mem _ hf, reesSumToGraded, DirectSum.toSemiring_of,
    reesPieceToGraded_apply]

/-- `R[Jt] ⟶ Gr_J(R)` on the monomial `a tⁿ`, `a ∈ Jⁿ`. -/
theorem reesToGraded_monomial (n : ℕ) (a : ↥(J ^ n)) :
    reesToGraded J ⟨monomial n (a : R), reesAlgebra.monomial_mem.mpr a.2⟩ = classOfPow J n a :=
  (reesToGraded_of_mem J (reesMonomial J n a).2).trans
    (classOfPow_congr J rfl (by exact coeff_monomial_same _ _))

/-- The ring map `R ⟶ Gr_J(R)` onto the degree-zero part. -/
def gradeZeroRingHom : R →+* gradedRing J :=
  (SetLike.GradeZero.subring (grading J)).subtype.comp (gradeZeroHom J)

/-- `gradeZeroRingHom` is the inclusion of the class in degree zero. -/
theorem gradeZeroRingHom_apply (r : R) :
    gradeZeroRingHom J r = DirectSum.of (fun n => piece (M := R) J n) 0 (gradeZeroMk J r) := rfl

/-- `gradeZeroRingHom` is the class in degree zero. -/
theorem gradeZeroRingHom_eq_classOfPow (r : R) :
    gradeZeroRingHom J r = classOfPow J 0 ⟨r, by simp⟩ := rfl

/-- `reesToGraded` on scalars. -/
theorem reesToGraded_algebraMap (r : R) :
    reesToGraded J (algebraMap R (reesAlgebra J) r) = gradeZeroRingHom J r := by
  have h : algebraMap R (reesAlgebra J) r = ⟨monomial 0 r, reesAlgebra.monomial_mem.mpr
      (by simp)⟩ := Subtype.ext (by simp [monomial_zero_left])
  rw [h]
  exact reesToGraded_monomial J 0 ⟨r, by simp⟩

variable {S : Type*} [CommRing S] [Algebra R S]

/-- The ring map `S ⟶ Gr_J(R)` of a quotient `S` of `R` by an ideal contained in `J`. -/
def quotientToGraded (hsurj : Function.Surjective (algebraMap R S))
    (hker : RingHom.ker (algebraMap R S) ≤ J) : S →+* gradedRing J :=
  (algebraMap R S).liftOfSurjective hsurj ⟨gradeZeroRingHom J, fun r hr => by
    rw [RingHom.mem_ker, gradeZeroRingHom_apply]
    rw [(gradeZeroMk_eq_zero_iff J r).2 (hker hr), map_zero]⟩

/-- `quotientToGraded` on the image of a scalar. -/
theorem quotientToGraded_algebraMap (hsurj : Function.Surjective (algebraMap R S))
    (hker : RingHom.ker (algebraMap R S) ≤ J) (r : R) :
    quotientToGraded J hsurj hker (algebraMap R S r) = gradeZeroRingHom J r :=
  RingHom.liftOfSurjective_comp_apply _ _ _ r

/-- **The map `S ⊗_R R[Jt] ⟶ C`** induced by the quotient map of the Rees algebra followed by a
ring map `ψ : Gr_J(R) ⟶ C`, for an `R`-algebra `S` which is a quotient of `R` by an ideal
contained in `J`. -/
def baseChangeReesToGraded {C : Type*} [CommRing C] (ψ : gradedRing J →+* C)
    (hsurj : Function.Surjective (algebraMap R S)) (hker : RingHom.ker (algebraMap R S) ≤ J) :
    S ⊗[R] reesAlgebra J →+* C :=
  letI : Algebra R C := (ψ.comp (gradeZeroRingHom J)).toAlgebra
  (Algebra.TensorProduct.lift
    ({ toRingHom := ψ.comp (quotientToGraded J hsurj hker)
       commutes' := fun r => congrArg ψ (quotientToGraded_algebraMap J hsurj hker r) } :
      S →ₐ[R] C)
    ({ toRingHom := ψ.comp (reesToGraded J)
       commutes' := fun r => congrArg ψ (reesToGraded_algebraMap J r) } :
      reesAlgebra J →ₐ[R] C)
    (fun _ _ => Commute.all _ _)).toRingHom

/-- `baseChangeReesToGraded` on a pure tensor. -/
theorem baseChangeReesToGraded_tmul {C : Type*} [CommRing C] (ψ : gradedRing J →+* C)
    (hsurj : Function.Surjective (algebraMap R S)) (hker : RingHom.ker (algebraMap R S) ≤ J)
    (s : S) (f : reesAlgebra J) :
    baseChangeReesToGraded J ψ hsurj hker (s ⊗ₜ f) =
      ψ (quotientToGraded J hsurj hker s) * ψ (reesToGraded J f) := rfl


/-- `baseChangeReesToGraded ψ` is `baseChangeReesToGraded id` followed by `ψ`. -/
theorem baseChangeReesToGraded_eq_comp {C : Type*} [CommRing C] (ψ : gradedRing J →+* C)
    (hsurj : Function.Surjective (algebraMap R S)) (hker : RingHom.ker (algebraMap R S) ≤ J) :
    baseChangeReesToGraded J ψ hsurj hker =
      ψ.comp (baseChangeReesToGraded J (RingHom.id _) hsurj hker) := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s f =>
    rw [RingHom.comp_apply, baseChangeReesToGraded_tmul, baseChangeReesToGraded_tmul, map_mul]
    rfl
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- The degree-`n` piece of the inverse of `S ⊗_R R[Jt] ⟶ Gr_J(R)`: `a ↦ 1 ⊗ a tⁿ`. -/
def gradedToBaseChangeRep (n : ℕ) : ↥(J ^ n) →+ S ⊗[R] reesAlgebra J :=
  ((TensorProduct.mk R S (reesAlgebra J) 1).toAddMonoidHom.comp
    ((reesGrading J n).subtype.comp (reesGradingEquivPow J n).toLinearMap).toAddMonoidHom)

/-- The value of `gradedToBaseChangeRep` on a representative. -/
theorem gradedToBaseChangeRep_apply (n : ℕ) (a : ↥(J ^ n)) :
    gradedToBaseChangeRep J n a =
      (1 : S) ⊗ₜ (⟨monomial n (a : R), reesAlgebra.monomial_mem.mpr a.2⟩ : reesAlgebra J) := rfl

/-- `gradedToBaseChangeRep` kills `Jⁿ⁺¹`. -/
theorem gradedToBaseChangeRep_eq_zero (hJ : J ≤ RingHom.ker (algebraMap R S)) {n : ℕ}
    (a : ↥(J ^ n)) (ha : (a : R) ∈ J ^ (n + 1)) : gradedToBaseChangeRep (S := S) J n a = 0 := by
  rw [gradedToBaseChangeRep_apply]
  obtain ⟨a, ha'⟩ := a
  change (a : R) ∈ J ^ (n + 1) at ha
  rw [pow_succ'] at ha
  induction ha using Submodule.mul_induction_on' with
  | mem_mul_mem x hx y hy =>
    have h : (⟨monomial n (x * y), reesAlgebra.monomial_mem.mpr ha'⟩ : reesAlgebra J) =
        x • (⟨monomial n y, reesAlgebra.monomial_mem.mpr hy⟩ : reesAlgebra J) :=
      Subtype.ext (by simp [Polynomial.smul_monomial])
    rw [h, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      RingHom.mem_ker.1 (hJ hx), TensorProduct.zero_tmul]
  | add x hx y hy ihx ihy =>
    have hx' : x ∈ J ^ n := Ideal.mul_le_right (I := J) hx
    have hy' : y ∈ J ^ n := Ideal.mul_le_right (I := J) hy
    have h : (⟨monomial n (x + y), reesAlgebra.monomial_mem.mpr ha'⟩ : reesAlgebra J) =
        ⟨monomial n x, reesAlgebra.monomial_mem.mpr hx'⟩ +
        ⟨monomial n y, reesAlgebra.monomial_mem.mpr hy'⟩ :=
      Subtype.ext (by simp)
    rw [h, TensorProduct.tmul_add, ihx hx', ihy hy', add_zero]

/-- The degree-`n` piece of the inverse of `S ⊗_R R[Jt] ⟶ Gr_J(R)`. -/
def gradedToBaseChangePiece (hJ : J ≤ RingHom.ker (algebraMap R S)) (n : ℕ) :
    piece (M := R) J n →+ S ⊗[R] reesAlgebra J :=
  AddMonoidHom.mk'
    (fun c => Quotient.liftOn c
      (fun y => gradedToBaseChangeRep J n ⟨(y : R), by simpa only [ring_power_eq] using y.2⟩)
      (by
        intro y z hyz
        have h : ((y : R) - (z : R)) ∈ power (M := R) J (n + 1) :=
          (Submodule.Quotient.eq ((power (M := R) J (n + 1)).comap
            (Submodule.subtype (power (M := R) J n)))).mp (Quotient.sound hyz)
        rw [← sub_eq_zero, ← map_sub]
        have h' : ((y : R) - (z : R)) ∈ J ^ (n + 1) := by simpa only [ring_power_eq] using h
        exact gradedToBaseChangeRep_eq_zero J hJ _ h'))
    (by
      intro c d
      induction c using Quotient.inductionOn with
      | _ y =>
        induction d using Quotient.inductionOn with
        | _ z =>
          change gradedToBaseChangeRep J n ⟨(y : R) + (z : R), _⟩ =
            gradedToBaseChangeRep J n ⟨(y : R), _⟩ + gradedToBaseChangeRep J n ⟨(z : R), _⟩
          rw [← map_add]
          rfl)

/-- **The inverse of `S ⊗_R R[Jt] ⟶ Gr_J(R)`**, as an additive map, `ā ↦ 1 ⊗ a tⁿ`. -/
def gradedToBaseChange (hJ : J ≤ RingHom.ker (algebraMap R S)) :
    gradedRing J →+ S ⊗[R] reesAlgebra J :=
  DirectSum.toAddMonoid (gradedToBaseChangePiece J hJ)

/-- `gradedToBaseChange` on the class of a representative. -/
theorem gradedToBaseChange_classOfPow (hJ : J ≤ RingHom.ker (algebraMap R S)) (n : ℕ)
    (a : ↥(J ^ n)) : gradedToBaseChange J hJ (classOfPow J n a) = gradedToBaseChangeRep J n a := by
  show DirectSum.toAddMonoid _ (DirectSum.of _ n _) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

/-- `gradedToBaseChange` is a left inverse of `reesToGraded` on base changes. -/
theorem gradedToBaseChange_reesToGraded (hJ : J ≤ RingHom.ker (algebraMap R S))
    (f : reesAlgebra J) : gradedToBaseChange J hJ (reesToGraded J f) = (1 : S) ⊗ₜ f := by
  induction f using DirectSum.Decomposition.inductionOn (reesGrading J) with
  | zero => rw [map_zero, map_zero, TensorProduct.tmul_zero]
  | homogeneous f =>
    rename_i n
    rw [reesToGraded_of_mem J f.2, gradedToBaseChange_classOfPow, gradedToBaseChangeRep_apply]
    congr 1
    exact Subtype.ext (coe_eq_monomial J f.2).symm
  | add f g hf hg => rw [map_add, map_add, hf, hg, TensorProduct.tmul_add]

/-- **`S ⊗_R R[Jt] ≅ Gr_J(R)` when `S = R/J'` with `J' ⊆ J ⊆ ker(R ⟶ S)`.** -/
theorem bijective_baseChangeReesToGraded (hsurj : Function.Surjective (algebraMap R S))
    (hker : RingHom.ker (algebraMap R S) ≤ J) (hJ : J ≤ RingHom.ker (algebraMap R S)) :
    Function.Bijective (baseChangeReesToGraded J (RingHom.id _) hsurj hker) := by
  refine ⟨Function.LeftInverse.injective (g := gradedToBaseChange J hJ) fun z => ?_,
    Function.RightInverse.surjective (g := gradedToBaseChange J hJ) fun x => ?_⟩
  · induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul s f =>
      obtain ⟨r, rfl⟩ := hsurj s
      rw [baseChangeReesToGraded_tmul, RingHom.id_apply, RingHom.id_apply,
        quotientToGraded_algebraMap, ← reesToGraded_algebraMap, ← map_mul,
        gradedToBaseChange_reesToGraded, ← Algebra.smul_def, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  · induction x using AssociatedGraded.induction_classOfPow with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | cls n a =>
      rw [gradedToBaseChange_classOfPow, gradedToBaseChangeRep_apply,
        baseChangeReesToGraded_tmul, map_one, RingHom.id_apply, one_mul, RingHom.id_apply,
        reesToGraded_monomial]

end Stacks.Blowup

end
