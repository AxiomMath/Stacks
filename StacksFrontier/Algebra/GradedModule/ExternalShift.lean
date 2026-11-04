module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Sign

/-!
# Shifts of externally graded modules

An *externally* graded algebra over a commutative ring `R` is an integer-indexed family of
`R`-modules with associative unital multiplication maps `A^i × A^j → A^{i+j}`, and an externally
graded right or left module over it is a family with compatible action maps. This file
constructs the integer shifts of such modules: the degree-`n` piece of `M[k]` is `M^{n+k}`, and
on a left module the action of a homogeneous element of degree `i` acquires the Koszul factor
`(-1)^{i k}`.

## Main definitions

* `ExternallyGradedAlgebra`: an externally graded algebra.
* `ExternallyGradedRightModule` and `ExternallyGradedLeftModule`: externally graded modules.
* `ExternallyGraded.degreeCast`: transport between graded pieces of equal degree.
* `ExternallyGradedRightModule.shift` and `ExternallyGradedLeftModule.shift`: the shifts.

## Main results

The two shift constructions are the content of the definition; the following
heterogeneous-equality lemmas are what make their associativity laws provable.

* `ExternallyGraded.degreeCast_heq`: transport of degree is heterogeneously the identity.
* `ExternallyGradedRightModule.smul_degreeCast_heq` and
  `ExternallyGradedLeftModule.smul_degreeCast_heq`: the actions respect transport of the degree
  of the module argument.

## Implementation notes

Graded objects are represented externally, as integer-indexed families of modules, rather than
internally as submodules of a single module; this is the representation in which a shift is a
reindexing and no transport of the ambient module is needed. Equalities between different
parenthesizations of degrees are handled by `degreeCast`, and the laws of the shifted structures
are therefore stated as heterogeneous equalities, exactly as the laws of the unshifted ones are.
The Koszul factor is `DifferentialGraded.gradedSign`, acting through the `R`-module structure of
each piece.

## References

* [Stacks Project, Tag 0FQ1](https://stacks.math.columbia.edu/tag/0FQ1)
-/

@[expose] public section

namespace ExternallyGraded

universe u v w

variable {R : Type u} [CommRing R]

/-- Transport between equal graded pieces, as a linear map. -/
def degreeCast {X : ℤ → Type v} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
    {i j : ℤ} (h : i = j) : X i →ₗ[R] X j := h ▸ LinearMap.id

/-- Casting a homogeneous element does not change the element heterogeneously. -/
theorem degreeCast_heq {X : ℤ → Type v} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
    {i j : ℤ} (h : i = j) (x : X i) : degreeCast (R := R) h x ≍ x := by
  subst h; rfl

end ExternallyGraded

open ExternallyGraded

universe u v w

variable {R : Type u} [CommRing R]

/-- An externally `ℤ`-graded algebra over a commutative ring `R`: a family of `R`-modules with
associative unital multiplication maps adding degrees. -/
@[ega "II 2.4.5" "more general"]
structure ExternallyGradedAlgebra (R : Type u) [CommRing R] where
  /-- The graded piece of degree `n`. -/
  piece : ℤ → Type v
  [addCommGroup : ∀ n, AddCommGroup (piece n)]
  [module : ∀ n, Module R (piece n)]
  /-- The multiplication map `A^i × A^j → A^{i+j}`, bilinear over `R`. -/
  mul : ∀ i j, piece i →ₗ[R] (piece j →ₗ[R] piece (i + j))
  /-- The unit, an element of degree `0`. -/
  one : piece 0
  /-- Multiplication is associative, up to the identification of degrees. -/
  mul_assoc : ∀ i j l (a : piece i) (b : piece j) (c : piece l),
    HEq (mul (i + j) l (mul i j a b) c) (mul i (j + l) a (mul j l b c))
  /-- The unit is a left identity for multiplication. -/
  one_mul : ∀ i (a : piece i), HEq (mul 0 i one a) a
  /-- The unit is a right identity for multiplication. -/
  mul_one : ∀ i (a : piece i), HEq (mul i 0 a one) a

attribute [instance] ExternallyGradedAlgebra.addCommGroup ExternallyGradedAlgebra.module

/-- A graded right module over an externally graded algebra. -/
structure ExternallyGradedRightModule (A : ExternallyGradedAlgebra.{u, v} R) where
  /-- The graded piece of degree `n`. -/
  piece : ℤ → Type w
  [addCommGroup : ∀ n, AddCommGroup (piece n)]
  [module : ∀ n, Module R (piece n)]
  /-- The action map `M^n × A^i → M^{n+i}`, bilinear over `R`. -/
  smul : ∀ n i, piece n →ₗ[R] (A.piece i →ₗ[R] piece (n + i))
  /-- Acting by `a` and then by `b` is acting by the product `a b`. -/
  smul_mul : ∀ n i j (x : piece n) (a : A.piece i) (b : A.piece j),
    HEq (smul (n + i) j (smul n i x a) b) (smul n (i + j) x (A.mul i j a b))
  /-- The unit of `A` acts as the identity. -/
  smul_one : ∀ n (x : piece n), HEq (smul n 0 x A.one) x

attribute [instance] ExternallyGradedRightModule.addCommGroup ExternallyGradedRightModule.module

/-- A graded left module over an externally graded algebra. -/
structure ExternallyGradedLeftModule (A : ExternallyGradedAlgebra.{u, v} R) where
  /-- The graded piece of degree `n`. -/
  piece : ℤ → Type w
  [addCommGroup : ∀ n, AddCommGroup (piece n)]
  [module : ∀ n, Module R (piece n)]
  /-- The action map `A^i × M^n → M^{i+n}`, bilinear over `R`. -/
  smul : ∀ i n, A.piece i →ₗ[R] (piece n →ₗ[R] piece (i + n))
  /-- Acting by the product `a b` is acting by `b` and then by `a`. -/
  mul_smul : ∀ i j n (a : A.piece i) (b : A.piece j) (x : piece n),
    HEq (smul (i + j) n (A.mul i j a b) x) (smul i (j + n) a (smul j n b x))
  /-- The unit of `A` acts as the identity. -/
  one_smul : ∀ n (x : piece n), HEq (smul 0 n A.one x) x

attribute [instance] ExternallyGradedLeftModule.addCommGroup ExternallyGradedLeftModule.module

/-- A right action respects transport of the degree of its module argument. -/
theorem ExternallyGradedRightModule.smul_degreeCast_heq {A : ExternallyGradedAlgebra.{u, v} R}
    (M : ExternallyGradedRightModule.{u, v, w} A)
    {n n' i : ℤ} (h : n = n') (x : M.piece n) (a : A.piece i) :
    M.smul n' i (degreeCast (R := R) h x) a ≍ M.smul n i x a := by
  subst h; rfl

/-- A left action respects transport of the degree of its module argument. -/
theorem ExternallyGradedLeftModule.smul_degreeCast_heq {A : ExternallyGradedAlgebra.{u, v} R}
    (M : ExternallyGradedLeftModule.{u, v, w} A)
    {n n' i : ℤ} (h : n = n') (a : A.piece i) (x : M.piece n) :
    M.smul i n' a (degreeCast (R := R) h x) ≍ M.smul i n a x := by
  subst h; rfl

namespace ExternallyGraded

/-- Scalar multiplication preserves heterogeneous equality in a graded family. -/
theorem scalar_heq {X : ℤ → Type v} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
    {i j : ℤ} {x : X i} {y : X j} {r s : R} (hij : i = j) (hrs : r = s)
    (hxy : x ≍ y) : r • x ≍ s • y := by
  subst hij; subst hrs; rw [eq_of_heq hxy]

/-- Transport between equal graded pieces commutes with scalar multiplication. -/
theorem degreeCast_smul {X : ℤ → Type v} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
    {i j : ℤ} (h : i = j) (r : R) (x : X i) :
    degreeCast (R := R) h (r • x) = r • degreeCast (R := R) h x := LinearMap.map_smul _ _ _

end ExternallyGraded

namespace ExternallyGradedRightModule

/-- The shift `M[k]` of a graded right module, with `M[k]ⁿ = Mⁿ⁺ᵏ`. -/
@[stacks 0FQ1 "right graded modules"]
def shift {A : ExternallyGradedAlgebra R} (M : ExternallyGradedRightModule A) (k : ℤ) :
    ExternallyGradedRightModule A where
  piece n := M.piece (n + k)
  addCommGroup n := M.addCommGroup (n + k)
  module n := M.module (n + k)
  smul n i :=
    { toFun := fun x => (degreeCast (R := R) (X := M.piece) (by omega)).comp (M.smul (n + k) i x)
      map_add' := by intro x y; ext a; simp
      map_smul' := by intro r x; ext a; simp }
  smul_mul := by
    intro n i j x a b
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply]
    refine HEq.trans (degreeCast_heq _ _) ?_
    refine HEq.trans (M.smul_degreeCast_heq (show n + k + i = n + i + k by omega)
      (M.smul (n + k) i x a) b) ?_
    refine HEq.trans (M.smul_mul (n + k) i j x a b) ?_
    · exact (degreeCast_heq _ _).symm
  smul_one := by
    intro n x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply]
    exact HEq.trans (degreeCast_heq _ _) (M.smul_one (n + k) x)

end ExternallyGradedRightModule

namespace ExternallyGradedLeftModule

/-- The shift `M[k]` of a graded left module.  A homogeneous element of degree `i`
acts with the Koszul factor `(-1)^(i*k)`. -/
@[stacks 0FQ1 "left graded modules"]
def shift {A : ExternallyGradedAlgebra R} (M : ExternallyGradedLeftModule A) (k : ℤ) :
    ExternallyGradedLeftModule A where
  piece n := M.piece (n + k)
  addCommGroup n := M.addCommGroup (n + k)
  module n := M.module (n + k)
  smul i n :=
    { toFun := fun a => DifferentialGraded.gradedSign R (i * k) •
        (degreeCast (R := R) (X := M.piece) (by omega)).comp (M.smul i (n + k) a)
      map_add' := by intro a b; ext x; simp
      map_smul' := by
        intro r a
        ext x
        simp only [LinearMap.coe_comp, Function.comp_apply, map_smul,
          LinearMap.smul_apply, RingHom.id_apply]
        rw [smul_comm] }
  mul_smul := by
    intro i j n a b x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      LinearMap.coe_comp, Function.comp_apply]
    rw [LinearMap.map_smul (M.smul i (j + n + k) a), degreeCast_smul, smul_smul]
    apply scalar_heq
    · omega
    · rw [add_mul, DifferentialGraded.gradedSign_add]
    · refine HEq.trans (degreeCast_heq _ _) ?_
      refine HEq.trans (M.mul_smul i j (n + k) a b x) ?_
      refine HEq.trans ?_ (degreeCast_heq _ _).symm
      exact (M.smul_degreeCast_heq (show j + (n + k) = j + n + k by omega) a
        (M.smul j (n + k) b x)).symm
  one_smul := by
    intro n x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      LinearMap.coe_comp, Function.comp_apply, zero_mul, DifferentialGraded.gradedSign_zero]
    rw [_root_.one_smul R]
    exact HEq.trans (degreeCast_heq _ _) (M.one_smul (n + k) x)

end ExternallyGradedLeftModule

