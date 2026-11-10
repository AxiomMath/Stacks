module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.OfBasis

/-!
# Classifying maps of free algebra structures, and the local form of the universal family

A free `d`-dimensional algebra structure over a commutative ring `R` is the same datum as a ring
homomorphism from the universal coefficient ring `A_d` to `R`, namely the one sending each
universal structure constant to the corresponding structure constant. If an algebra `B` over `A`
is free on a basis whose first vector is `1`, the classifying map of the structure constants of
that basis exhibits `B` as the base change of the universal family `B_d` over `A_d`, so that the
square of rings so formed is a pushout.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.classify` is the ring homomorphism out of the universal
  coefficient ring classifying a free `d`-dimensional algebra structure.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.classify_universalStructureConstant` identifies the images
  of the universal structure constants under a classifying map.
* `AlgebraicGeometry.isPushout_universalFamily_of_basis_one` realizes an algebra free on a basis
  whose first vector is `1` as a base change of the universal family.

## Implementation notes

The classifying map is the evaluation of polynomials in the universal structure constants at the
given ones, which kills the defining relations precisely because the structure constants are
associative, commutative and unital.

Base change is checked by exhibiting a basis of the upper edge of the square and matching it with
the given basis of the lower one, which is the content of the auxiliary pushout criterion of this
file. The coefficient ring and the free carrier are lifted into the universe of the given rings,
as they are when the universal family is formed, and their coordinate formulas are read off from
the given algebra structure rather than from instances.

## References

* [Stacks Project, Tag 0FKZ](https://stacks.math.columbia.edu/tag/0FKZ)
-/

@[expose] public noncomputable section

open scoped BigOperators TensorProduct

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace FiniteFreeAlgebra

variable {R : Type*} [CommRing R] {d : ℕ} [NeZero d]

/-- The ring hom classifying a free `d`-dimensional algebra structure. -/
def classify (m : FiniteFreeAlgebra R d) : universalRing d →+* R :=
  Ideal.Quotient.lift (Ideal.span (universalRelations d))
    (MvPolynomial.eval₂Hom (algebraMap ℤ R) fun q : CoeffIndex d => m.coeff q.1 q.2.1 q.2.2)
    (by
      have hker : Ideal.span (universalRelations d) ≤ RingHom.ker
          (MvPolynomial.eval₂Hom (algebraMap ℤ R)
            fun q : CoeffIndex d => m.coeff q.1 q.2.1 q.2.2) := by
        refine Ideal.span_le.2 fun p hp => ?_
        rcases hp with (hp | hp) | hp
        · obtain ⟨i, j, k, n, rfl⟩ := hp
          simpa [RingHom.mem_ker, universalCoeff] using sub_eq_zero.mpr (m.assoc i j k n)
        · obtain ⟨i, j, k, rfl⟩ := hp
          simpa [RingHom.mem_ker, universalCoeff] using sub_eq_zero.mpr (m.comm i j k)
        · obtain ⟨i, j, rfl⟩ := hp
          rcases eq_or_ne i j with rfl | hij
          · simpa [RingHom.mem_ker, universalCoeff, MvPolynomial.eval₂Hom] using
              sub_eq_zero.mpr (m.unit_coeff i i)
          · simpa [RingHom.mem_ker, universalCoeff, MvPolynomial.eval₂Hom, hij] using
              sub_eq_zero.mpr (m.unit_coeff i j)
      exact fun a ha => RingHom.mem_ker.mp (hker ha))

/-- The classifying map of a free algebra structure sends the universal structure constant
`universalStructureConstant d i j k` to the structure constant `m.coeff i j k`. -/
@[simp] theorem classify_universalStructureConstant {R : Type*} [CommRing R]
    {d : ℕ} [NeZero d] (m : FiniteFreeAlgebra R d) (i j k : Fin d) :
    m.classify (universalStructureConstant d i j k) = m.coeff i j k := by
  change MvPolynomial.eval₂Hom (algebraMap ℤ R)
      (fun q : CoeffIndex d => m.coeff q.1 q.2.1 q.2.2) (universalCoeff d i j k) = m.coeff i j k
  simp [universalCoeff]

end FiniteFreeAlgebra

open FiniteFreeAlgebra

/-- A commuting square of commutative rings whose two horizontal edges carry bases indexed by the
same type, the lower one expanding the images of the upper one, is a pushout square. -/
private lemma isPushout_of_bases {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A]
    [CommRing B] [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B] {d : ℕ}
    (bU : Module.Basis (Fin d) R S) (b : Module.Basis (Fin d) A B)
    (h : ∀ x : S, algebraMap S B x = ∑ i, algebraMap R A (bU.repr x i) • b i) :
    Algebra.IsPushout R S A B := by
  refine Algebra.IsPushout.symm ?_
  rw [Algebra.isPushout_iff]
  refine IsBaseChange.of_equiv ((bU.baseChange A).equiv b (Equiv.refl (Fin d))) fun x => ?_
  have hbase : ∀ i : Fin d,
      ((bU.baseChange A).equiv b (Equiv.refl (Fin d))) (1 ⊗ₜ[R] bU i) = b i := by
    intro i
    have h1 : (1 : A) ⊗ₜ[R] bU i = (bU.baseChange A) i :=
      (Module.Basis.baseChange_apply (S := A) bU i).symm
    rw [h1, Module.Basis.equiv_apply, Equiv.refl_apply]
  change ((bU.baseChange A).equiv b (Equiv.refl (Fin d))) (1 ⊗ₜ[R] x) = algebraMap S B x
  rw [h x]
  conv_lhs => rw [← bU.sum_repr x]
  rw [TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.tmul_smul, ← algebraMap_smul A (bU.repr x i), map_smul, hbase i]

/-- Multiplication by the image of a scalar on the universal free carrier is multiplication by
that scalar on each coordinate. -/
private lemma algebraMap_mul_coeff (d : ℕ) [NeZero d] (s : UniversalAlgebraStructure d)
    (a : universalRing d) (x : UniversalFiniteFreeModule d) (i : Fin d) :
    letI := s.ring
    letI := s.algebra
    (algebraMap (universalRing d) (UniversalFiniteFreeModule d) a * x).coeff i = a * x.coeff i := by
  let := s.ring
  let := s.algebra
  rw [s.mul_eq]
  simp only [universalMultiplication, s.algebraMap_coeff]
  simp [universalStructureConstant_zero_left]

/-- **The affine local structure of a finite free algebra with `1` in its basis.**  If `B` is an
`A`-algebra free on a basis whose first vector is `1`, then the square formed by the universal
family `π_d` and the classifying map of the structure constants of that basis is a pushout of
commutative rings. -/
theorem isPushout_universalFamily_of_basis_one {A B : CommRingCat.{u}} (ψ : A ⟶ B)
    {d : ℕ} [NeZero d] (s : UniversalAlgebraStructure d)
    (b : letI := ψ.hom.toAlgebra; Module.Basis (Fin d) A B) (hb : b 0 = 1) :
    letI := s.ring
    letI := s.algebra
    ∃ (φ : CommRingCat.of (ULift.{u} (FiniteFreeAlgebra.universalRing d)) ⟶ A)
      (Φ : CommRingCat.of (ULift.{u} (UniversalFiniteFreeModule d)) ⟶ B),
      CategoryTheory.IsPushout
        (CommRingCat.ofHom (RingHom.ulift
          (algebraMap (FiniteFreeAlgebra.universalRing d) (UniversalFiniteFreeModule d))))
        φ Φ ψ := by
  classical
  let := s.ring
  let := s.algebra
  let : Algebra (A : Type u) (B : Type u) := ψ.hom.toAlgebra
  let : Algebra (ULift.{u} (universalRing d)) (ULift.{u} (UniversalFiniteFreeModule d)) :=
    ULift.algebra' (universalRing d) (ULift.{u} (UniversalFiniteFreeModule d))
  let eU : ULift.{u} (UniversalFiniteFreeModule d) ≃ₗ[ULift.{u} (universalRing d)]
      (Fin d → ULift.{u} (universalRing d)) :=
    { toFun := fun x i => ULift.up (x.down.coeff i)
      invFun := fun f => ULift.up ⟨fun i => (f i).down⟩
      left_inv := fun x => by cases x with | up x => cases x; rfl
      right_inv := fun _ => rfl
      map_add' := fun x y => by
        funext i
        exact ULift.ext (s.add_coeff x.down y.down i)
      map_smul' := fun a x => by
        funext i
        refine ULift.ext ?_
        change (a.down • x.down : UniversalFiniteFreeModule d).coeff i = a.down * x.down.coeff i
        rw [Algebra.smul_def]
        exact algebraMap_mul_coeff d s a.down x.down i }
  let bU : Module.Basis (Fin d) (ULift.{u} (universalRing d))
      (ULift.{u} (UniversalFiniteFreeModule d)) :=
    Module.Basis.ofRepr (eU.trans (Finsupp.linearEquivFunOnFinite
      (ULift.{u} (universalRing d)) (ULift.{u} (universalRing d)) (Fin d)).symm)
  let m : FiniteFreeAlgebra (A : Type u) d := FiniteFreeAlgebra.ofBasis b hb
  let φ : CommRingCat.of (ULift.{u} (universalRing d)) ⟶ A :=
    CommRingCat.ofHom (m.classify.comp ULift.ringEquiv.toRingHom)
  let c : universalRing d →+* (B : Type u) := ψ.hom.comp m.classify
  let f : ULift.{u} (UniversalFiniteFreeModule d) → (B : Type u) :=
    fun x => ∑ i, c (x.down.coeff i) * b i
  have hzero : f 0 = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show ((0 : ULift.{u} (UniversalFiniteFreeModule d)).down).coeff i = 0 from s.zero_coeff i,
      map_zero, zero_mul]
  have hadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    change ∑ i, c (((x + y).down).coeff i) * b i
      = (∑ i, c ((x.down).coeff i) * b i) + ∑ i, c ((y.down).coeff i) * b i
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ((x + y).down).coeff i = (x.down).coeff i + (y.down).coeff i from
      s.add_coeff x.down y.down i, map_add, add_mul]
  have hfa : ∀ r : universalRing d,
      f (ULift.up (algebraMap (universalRing d) (UniversalFiniteFreeModule d) r)) = c r := by
    intro r
    simp only [f, s.algebraMap_coeff, apply_ite c, map_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, hb, mul_one]
  have hone : f 1 = 1 := by
    have h := hfa 1
    rwa [map_one, map_one] at h
  have hmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    have hc : ∀ i j k : Fin d, c (universalStructureConstant d i j k)
        = algebraMap (A : Type u) (B : Type u) (b.repr (b i * b j) k) := by
      intro i j k
      change ψ.hom (m.classify (universalStructureConstant d i j k)) = _
      rw [FiniteFreeAlgebra.classify_universalStructureConstant]
      rfl
    have hprod : ∀ i j : Fin d,
        (∑ k, c (universalStructureConstant d i j k) * b k) = b i * b j := by
      intro i j
      rw [Finset.sum_congr rfl fun k _ => by rw [hc i j k, ← Algebra.smul_def]]
      exact b.sum_repr _
    have hxy : ∀ k, ((x * y).down).coeff k
        = ∑ i, ∑ j, (x.down).coeff i * (y.down).coeff j * universalStructureConstant d i j k := by
      intro k
      change ((x.down * y.down : UniversalFiniteFreeModule d)).coeff k = _
      rw [s.mul_eq]
      rfl
    change ∑ k, c (((x * y).down).coeff k) * b k
      = (∑ i, c ((x.down).coeff i) * b i) * ∑ j, c ((y.down).coeff j) * b j
    calc ∑ k, c (((x * y).down).coeff k) * b k
        = ∑ k, ∑ i, ∑ j, (c ((x.down).coeff i) * c ((y.down).coeff j)) *
            (c (universalStructureConstant d i j k) * b k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hxy k, map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, map_mul]
          ring
      _ = ∑ i, ∑ j, (c ((x.down).coeff i) * c ((y.down).coeff j)) * (b i * b j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum, hprod]
      _ = _ := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  let Ψ : ULift.{u} (UniversalFiniteFreeModule d) →+* (B : Type u) :=
    { toFun := f
      map_one' := hone
      map_mul' := hmul
      map_zero' := hzero
      map_add' := hadd }
  let Φ : CommRingCat.of (ULift.{u} (UniversalFiniteFreeModule d)) ⟶ B := CommRingCat.ofHom Ψ
  let : Algebra (ULift.{u} (universalRing d)) (A : Type u) := φ.hom.toAlgebra
  let : Algebra (ULift.{u} (UniversalFiniteFreeModule d)) (B : Type u) := Φ.hom.toAlgebra
  let : Algebra (ULift.{u} (universalRing d)) (B : Type u) :=
    ((algebraMap (A : Type u) (B : Type u)).comp
      (algebraMap (ULift.{u} (universalRing d)) (A : Type u))).toAlgebra
  have : IsScalarTower (ULift.{u} (universalRing d)) (A : Type u) (B : Type u) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (ULift.{u} (universalRing d))
      (ULift.{u} (UniversalFiniteFreeModule d)) (B : Type u) := by
    refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => ?_)
    exact (hfa r.down).symm
  have : Algebra.IsPushout (ULift.{u} (universalRing d))
      (ULift.{u} (UniversalFiniteFreeModule d)) (A : Type u) (B : Type u) := by
    refine isPushout_of_bases (R := ULift.{u} (universalRing d))
      (S := ULift.{u} (UniversalFiniteFreeModule d)) (A := (A : Type u)) (B := (B : Type u))
      bU b fun x => ?_
    change f x = _
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def]
    rfl
  exact ⟨φ, Φ, CommRingCat.isPushout_of_isPushout (ULift.{u} (universalRing d))
    (ULift.{u} (UniversalFiniteFreeModule d)) (A : Type u) (B : Type u)⟩

end AlgebraicGeometry

end
