module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Differential graded modules and the dual complex `M^vee`

Let `(A, d)` be a differential graded algebra over a commutative ring `R`, graded by `ℤ`, and
let `M` be a right differential graded `A`-module. This file sets up the basic objects and the
dual complex `M^vee`, with `(M^vee)^n = Hom_Z(M^{-n}, Q/Z)` and differential
`f ↦ (-1)^{n+1} (f ∘ d_M)`.

## Main definitions

* `DGAlgebra`: a differential graded `R`-algebra.
* `DGAlgebra.RightModule`, `DGAlgebra.LeftModule`: right and left differential graded
  modules over a differential graded algebra.
* `DGAlgebra.RightModuleHom`: the abelian group of homomorphisms of right differential graded
  modules.
* `DGAlgebra.RightModule.shift`: the shift `M[k]`, with `(M[k])^n = M^{n+k}` and differential
  `(-1)^k d_M`.
* `DGAlgebra.RightModule.dDual`, `DGAlgebra.RightModule.cocycles`,
  `DGAlgebra.RightModule.cohomology`: the differential, cocycles and cohomology of the dual
  complex `M^vee`.

## Main results

* `DGAlgebra.RightModule.dDual_comp_dDual`: the differential of `M^vee` squares to zero.

## Implementation notes

A graded object is a family `carrier : ℤ → Type u` of `R`-modules, and multiplications and
differentials are families of `R`-(bi)linear maps between the graded pieces. Elements are
transported along equalities of degrees by `degCast` and `degCastLin`. The dualizing object
`Q/Z` is `QZ = AddCircle (1 : ℚ)`.

## References

* [Stacks Project, Tag 09K4](https://stacks.math.columbia.edu/tag/09K4)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Stacks.DifferentialGradedDual

universe u

/-! ### Transport along equalities of degrees -/

/-- Transport an element along an equality of degrees in a `Z`-graded family of
types. -/
abbrev degCast {V : ℤ → Type u} {a b : ℤ} (h : a = b) (x : V a) : V b := h ▸ x

/-- Transport along an equality of degrees, as an additive group isomorphism, in a
`Z`-graded family of additive groups. -/
def degCastAddHom {V : ℤ → Type u} [∀ n, AddCommGroup (V n)] {a b : ℤ} (h : a = b) :
    V a →+ V b := by subst h; exact AddMonoidHom.id _

/-- Transport along an equality of degrees, as an `R`-linear isomorphism, in a
`Z`-graded family of `R`-modules. -/
def degCastLin (R : Type u) [CommRing R] {V : ℤ → Type u} [∀ n, AddCommGroup (V n)]
    [∀ n, Module R (V n)] {a b : ℤ} (h : a = b) : V a ≃ₗ[R] V b := by
  subst h; exact LinearEquiv.refl _ _

/-- Transporting along `degCastLin` gives an element heterogeneously equal to the original. -/
theorem degCastLin_heq (R : Type u) [CommRing R] {V : ℤ → Type u}
    [∀ n, AddCommGroup (V n)] [∀ n, Module R (V n)] {a b : ℤ} (h : a = b) (x : V a) :
    HEq (degCastLin R h x) x := by subst h; rfl

/-- Transporting along `degCast` gives an element heterogeneously equal to the original. -/
theorem degCast_heq {V : ℤ → Type u} {a b : ℤ} (h : a = b) (x : V a) :
    HEq (degCast h x) x := by subst h; rfl

/-- `degCast` sends `0` to `0`. -/
theorem degCast_zero {V : ℤ → Type u} [∀ n, AddCommGroup (V n)] {a b : ℤ} (h : a = b) :
    degCast h (0 : V a) = 0 := by subst h; rfl

/-- `degCast` is additive. -/
theorem degCast_add {V : ℤ → Type u} [∀ n, AddCommGroup (V n)] {a b : ℤ} (h : a = b)
    (x y : V a) : degCast h (x + y) = degCast h x + degCast h y := by subst h; rfl

/-- `degCast` commutes with negation. -/
theorem degCast_neg {V : ℤ → Type u} [∀ n, AddCommGroup (V n)] {a b : ℤ} (h : a = b)
    (x : V a) : degCast h (-x) = -degCast h x := by subst h; rfl

/-- A family of `R`-linear maps `V n → W (n + 1)` commutes with `degCastLin`. -/
theorem family_degCastLin (R : Type u) [CommRing R] {V W : ℤ → Type u}
    [∀ n, AddCommGroup (V n)] [∀ n, Module R (V n)]
    [∀ n, AddCommGroup (W n)] [∀ n, Module R (W n)]
    (F : ∀ n, V n →ₗ[R] W (n + 1)) {a b : ℤ} (h : a = b) (x : V a) :
    F b (degCastLin R h x) = degCastLin R (by rw [h]) (F a x) := by subst h; rfl

/-- Transport a degree-preserving family of `R`-linear maps through a cast. -/
theorem family0_degCastLin (R : Type u) [CommRing R] {V W : ℤ → Type u}
    [∀ n, AddCommGroup (V n)] [∀ n, Module R (V n)]
    [∀ n, AddCommGroup (W n)] [∀ n, Module R (W n)]
    (F : ∀ n, V n →ₗ[R] W n) {a b : ℤ} (h : a = b) (x : V a) :
    F b (degCastLin R h x) = degCastLin R h (F a x) := by subst h; rfl

/-- Transporting along `a = b` and then `b = c` is transporting along `a = c`. -/
theorem degCastLin_trans (R : Type u) [CommRing R] {V : ℤ → Type u}
    [∀ n, AddCommGroup (V n)] [∀ n, Module R (V n)] {a b c : ℤ} (h1 : a = b) (h2 : b = c)
    (x : V a) :
    degCastLin R h2 (degCastLin R h1 x) = degCastLin R (h1.trans h2) x := by
  subst h1; subst h2; rfl

/-- `degCastLin` commutes with multiplication by an integer. -/
theorem degCastLin_smul (R : Type u) [CommRing R] {V : ℤ → Type u}
    [∀ n, AddCommGroup (V n)] [∀ n, Module R (V n)] {a b : ℤ} (h : a = b) (r : ℤ) (x : V a) :
    degCastLin R h (r • x) = r • degCastLin R h x := by subst h; rfl

/-- `degCastLin` sends `0` to `0`. -/
theorem degCastLin_zero (R : Type u) [CommRing R] {V : ℤ → Type u}
    [∀ n, AddCommGroup (V n)] [∀ n, Module R (V n)] {a b : ℤ} (h : a = b) :
    degCastLin R h (0 : V a) = 0 := by subst h; rfl

/-- `degCast` commutes with multiplication by an integer. -/
theorem degCast_smul {V : ℤ → Type u} [∀ n, AddCommGroup (V n)] {a b : ℤ} (h : a = b)
    (r : ℤ) (x : V a) : degCast h (r • x) = r • degCast h x := by subst h; rfl

/-- Transport a bilinear family through a cast of the first argument. -/
theorem bil_degCastLin (R : Type u) [CommRing R] {V W U : ℤ → Type u}
    [∀ n, AddCommGroup (V n)] [∀ n, Module R (V n)]
    [∀ n, AddCommGroup (W n)] [∀ n, Module R (W n)]
    [∀ n, AddCommGroup (U n)] [∀ n, Module R (U n)]
    (F : ∀ n m, V n →ₗ[R] W m →ₗ[R] U (n + m)) {a b : ℤ} (h : a = b) (m : ℤ)
    (x : V a) (y : W m) :
    F b m (degCastLin R h x) y = degCastLin R (by rw [h]) (F a m x y) := by
  subst h; rfl

/-- `(-1)^|k| * (-1)^|n+k| = (-1)^|n|`. -/
theorem sign_recon (n k : ℤ) :
    ((-1 : ℤ) ^ k.natAbs) * ((-1 : ℤ) ^ (n + k).natAbs) = (-1 : ℤ) ^ n.natAbs := by
  rw [← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := n.natAbs)]
  congr 1; omega

/-- `(-1)^|a| * (-1)^|b| = (-1)^|a+b|`. -/
theorem neg_one_pow_natAbs_add (a b : ℤ) :
    ((-1 : ℤ) ^ a.natAbs) * ((-1 : ℤ) ^ b.natAbs) = (-1 : ℤ) ^ (a + b).natAbs := by
  rw [← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := (a + b).natAbs)]
  congr 1; omega

/-- `(-1)^|n+1| = -(-1)^|n|`. -/
theorem neg_one_pow_natAbs_succ (n : ℤ) :
    ((-1 : ℤ) ^ (n + 1).natAbs) = -((-1 : ℤ) ^ n.natAbs) := by
  have : ((-1 : ℤ) ^ n.natAbs) * ((-1 : ℤ) ^ (1 : ℤ).natAbs) = (-1 : ℤ) ^ (n + 1).natAbs :=
    neg_one_pow_natAbs_add n 1
  simp only [show (1 : ℤ).natAbs = 1 from rfl, pow_one] at this
  rw [← this]; ring

/-- The group `Q/Z`, as the additive circle `AddCircle (1 : ℚ)`. -/
abbrev QZ : Type := AddCircle (1 : ℚ)

/-! ### The dual of an `R`-module into `Q/Z`

For an `R`-module `X` over a commutative ring `R`, the abelian group `X ->+ Q/Z` carries the
`R`-module structure `(r . f)(x) = f(r . x)`. -/

/-- `RDual R X = X ->+ Q/Z`, the additive dual into `Q/Z`, with `R`-module structure
`(r . f)(x) = f(r . x)`. -/
def RDual (R : Type u) [CommRing R] (X : Type u) [AddCommGroup X] [Module R X] : Type u :=
  X →+ QZ

namespace RDual
variable {R : Type u} [CommRing R] {X : Type u} [AddCommGroup X] [Module R X]

/-- The pointwise additive group structure on `RDual R X`. -/
instance : AddCommGroup (RDual R X) := inferInstanceAs (AddCommGroup (X →+ QZ))

/-- View an `RDual` element as the underlying additive hom. -/
@[coe] def toFun (f : RDual R X) : X →+ QZ := f

/-- The action `(r • f)(x) = f(r • x)` of `R` on `RDual R X`. -/
instance : SMul R (RDual R X) where
  smul r f := (show X →+ QZ from f).comp ((r • (LinearMap.id : X →ₗ[R] X)).toAddMonoidHom)

/-- `(r • f)(x) = f(r • x)`. -/
@[simp] theorem smul_apply (r : R) (f : RDual R X) (x : X) :
    (show X →+ QZ from r • f) x = (show X →+ QZ from f) (r • x) := rfl

/-- `(f + g)(x) = f(x) + g(x)`. -/
@[simp] theorem add_apply (f g : RDual R X) (x : X) :
    (show X →+ QZ from f + g) x = (show X →+ QZ from f) x + (show X →+ QZ from g) x := rfl

/-- The zero element of `RDual R X` vanishes at every point. -/
@[simp] theorem zero_apply (x : X) : (show X →+ QZ from (0 : RDual R X)) x = 0 := rfl

/-- `(-f)(x) = -f(x)`. -/
@[simp] theorem neg_apply (f : RDual R X) (x : X) :
    (show X →+ QZ from -f) x = -(show X →+ QZ from f) x := rfl

/-- The `R`-module structure on `RDual R X` given by `(r • f)(x) = f(r • x)`. -/
instance : Module R (RDual R X) where
  one_smul f := by
    apply AddMonoidHom.ext; intro x; change (show X →+ QZ from f) ((1 : R) • x) = _
    rw [one_smul]
  mul_smul r s f := by
    apply AddMonoidHom.ext; intro x
    change (show X →+ QZ from f) ((r * s) • x) = (show X →+ QZ from f) (s • (r • x))
    rw [smul_smul, mul_comm s r]
  smul_zero r := by apply AddMonoidHom.ext; intro x; rfl
  smul_add r f g := by apply AddMonoidHom.ext; intro x; rfl
  add_smul r s f := by
    apply AddMonoidHom.ext; intro x
    change (show X →+ QZ from f) ((r + s) • x) = _
    rw [add_smul, map_add]; rfl
  zero_smul f := by
    apply AddMonoidHom.ext; intro x
    change (show X →+ QZ from f) ((0 : R) • x) = _
    rw [zero_smul, map_zero]; rfl

/-- Two elements of `RDual R X` agreeing at every point are equal. -/
@[ext] theorem ext {f g : RDual R X} (h : ∀ x, (show X →+ QZ from f) x = (show X →+ QZ from g) x) :
    f = g := AddMonoidHom.ext h

/-- Precompose an `RDual` element with an `R`-linear map `φ : Y →ₗ[R] X`, giving an
`R`-linear map `RDual R X →ₗ[R] RDual R Y`. -/
def precompₗ {Y : Type u} [AddCommGroup Y] [Module R Y] (φ : Y →ₗ[R] X) :
    RDual R X →ₗ[R] RDual R Y where
  toFun f := (f : X →+ QZ).comp φ.toAddMonoidHom
  map_add' f g := by apply AddMonoidHom.ext; intro y; rfl
  map_smul' r f := by
    apply AddMonoidHom.ext; intro y
    change (RDual.toFun f) (r • φ y) = (RDual.toFun f) (φ (r • y))
    rw [LinearMap.map_smul]

/-- `precompₗ φ f` evaluated at `y` is `f (φ y)`. -/
@[simp] theorem precompₗ_apply {Y : Type u} [AddCommGroup Y] [Module R Y] (φ : Y →ₗ[R] X)
    (f : RDual R X) (y : Y) :
    (show Y →+ QZ from precompₗ φ f) y = (show X →+ QZ from f) (φ y) := rfl

end RDual

variable (R : Type u) [CommRing R]

/-- A differential graded `R`-algebra: a `Z`-graded associative unital `R`-algebra
`A = (+) A^n` with an `R`-linear degree `+1` differential `d` satisfying `d . d = 0` and the
Leibniz rule `d(ab) = d(a) b + (-1)^n a d(b)` for `a in A^n`. -/
structure DGAlgebra where
  /-- The graded piece `A^n` in degree `n`. -/
  carrier : ℤ → Type u
  [addCommGroup : ∀ n, AddCommGroup (carrier n)]
  [module : ∀ n, Module R (carrier n)]
  /-- Multiplication `A^n x A^m -> A^{n+m}`, `R`-bilinear. -/
  mul : ∀ n m, carrier n →ₗ[R] carrier m →ₗ[R] carrier (n + m)
  /-- The unit `1 in A^0`. -/
  one : carrier 0
  mul_assoc : ∀ (n m p : ℤ) (a : carrier n) (b : carrier m) (c : carrier p),
    degCast (add_assoc n m p) (mul (n + m) p (mul n m a b) c) = mul n (m + p) a (mul m p b c)
  one_mul : ∀ (n : ℤ) (a : carrier n), degCast (zero_add n) (mul 0 n one a) = a
  mul_one : ∀ (n : ℤ) (a : carrier n), degCast (add_zero n) (mul n 0 a one) = a
  /-- The differential `d : A^n -> A^{n+1}`. -/
  d : ∀ n, carrier n →ₗ[R] carrier (n + 1)
  d_comp_d : ∀ (n : ℤ) (a : carrier n), d (n + 1) (d n a) = 0
  leibniz : ∀ (n m : ℤ) (a : carrier n) (b : carrier m),
    d (n + m) (mul n m a b)
      = degCast (by ring) (mul (n + 1) m (d n a) b)
        + ((-1 : ℤ) ^ n.natAbs) • degCast (by ring) (mul n (m + 1) a (d m b))

attribute [instance] DGAlgebra.addCommGroup DGAlgebra.module

namespace DGAlgebra
variable {R}

/-- A right differential graded `A`-module: a right graded `A`-module `M = (+) M^n` with an
`R`-linear degree `+1` differential `d`, `d . d = 0`, and Leibniz rule
`d(x a) = d(x) a + (-1)^n x d(a)` for `x in M^n`. -/
structure RightModule (A : DGAlgebra R) where
  /-- The graded piece `M^n` in degree `n`. -/
  carrier : ℤ → Type u
  [addCommGroup : ∀ n, AddCommGroup (carrier n)]
  [module : ∀ n, Module R (carrier n)]
  /-- Right action `M^n x A^m -> M^{n+m}`. -/
  smul : ∀ n m, carrier n →ₗ[R] A.carrier m →ₗ[R] carrier (n + m)
  smul_assoc : ∀ (n m p : ℤ) (x : carrier n) (a : A.carrier m) (b : A.carrier p),
    degCast (add_assoc n m p) (smul (n + m) p (smul n m x a) b) = smul n (m + p) x (A.mul m p a b)
  smul_one : ∀ (n : ℤ) (x : carrier n), degCast (add_zero n) (smul n 0 x A.one) = x
  /-- The differential `d : M^n -> M^{n+1}`. -/
  d : ∀ n, carrier n →ₗ[R] carrier (n + 1)
  d_comp_d : ∀ (n : ℤ) (x : carrier n), d (n + 1) (d n x) = 0
  leibniz : ∀ (n m : ℤ) (x : carrier n) (a : A.carrier m),
    d (n + m) (smul n m x a)
      = degCast (by ring) (smul (n + 1) m (d n x) a)
        + ((-1 : ℤ) ^ n.natAbs) • degCast (by ring) (smul n (m + 1) x (A.d m a))

attribute [instance] RightModule.addCommGroup RightModule.module

/-- A left differential graded `A`-module: a left graded `A`-module `L = (+) L^n` with an
`R`-linear degree `+1` differential, `d . d = 0`, and Leibniz rule
`d(a x) = d(a) x + (-1)^m a d(x)` for `a in A^m`. -/
structure LeftModule (A : DGAlgebra R) where
  /-- The graded piece `L^n` in degree `n`. -/
  carrier : ℤ → Type u
  [addCommGroup : ∀ n, AddCommGroup (carrier n)]
  [module : ∀ n, Module R (carrier n)]
  /-- Left action `A^m x L^n -> L^{m+n}`. -/
  smul : ∀ m n, A.carrier m →ₗ[R] carrier n →ₗ[R] carrier (m + n)
  smul_assoc : ∀ (m p n : ℤ) (a : A.carrier m) (b : A.carrier p) (x : carrier n),
    degCast (add_assoc m p n) (smul (m + p) n (A.mul m p a b) x) = smul m (p + n) a (smul p n b x)
  one_smul : ∀ (n : ℤ) (x : carrier n), degCast (zero_add n) (smul 0 n A.one x) = x
  /-- The differential `d : L^n -> L^{n+1}`. -/
  d : ∀ n, carrier n →ₗ[R] carrier (n + 1)
  d_comp_d : ∀ (n : ℤ) (x : carrier n), d (n + 1) (d n x) = 0
  leibniz : ∀ (m n : ℤ) (a : A.carrier m) (x : carrier n),
    d (m + n) (smul m n a x)
      = degCast (by ring) (smul (m + 1) n (A.d m a) x)
        + ((-1 : ℤ) ^ m.natAbs) • degCast (by ring) (smul m (n + 1) a (d n x))

attribute [instance] LeftModule.addCommGroup LeftModule.module

variable {A : DGAlgebra R}

/-- The regular left differential graded `A`-module: `A` acting on itself by left
multiplication. -/
def regularLeft (A : DGAlgebra R) : LeftModule A where
  carrier := A.carrier
  smul := A.mul
  smul_assoc := A.mul_assoc
  one_smul := A.one_mul
  d := A.d
  d_comp_d := A.d_comp_d
  leibniz := A.leibniz

/-- A homomorphism of right differential graded `A`-modules: a degree-`0`, `R`-linear,
right `A`-linear family of maps commuting with the differentials. -/
structure RightModuleHom (M N : RightModule A) where
  /-- The component `M^n -> N^n` in degree `n`. -/
  toFun : ∀ n, M.carrier n →ₗ[R] N.carrier n
  map_smul : ∀ (n m : ℤ) (x : M.carrier n) (a : A.carrier m),
    toFun (n + m) (M.smul n m x a) = N.smul n m (toFun n x) a
  map_d : ∀ (n : ℤ) (x : M.carrier n), toFun (n + 1) (M.d n x) = N.d n (toFun n x)

namespace RightModuleHom
variable {M N : RightModule A}

/-- Two homomorphisms with the same components are equal. -/
@[ext] theorem ext {f g : RightModuleHom M N} (h : ∀ n x, f.toFun n x = g.toFun n x) : f = g := by
  cases f; cases g; congr 1; ext n x; exact h n x

/-- The zero homomorphism. -/
instance : Zero (RightModuleHom M N) where
  zero := { toFun := fun _ => 0, map_smul := by intro n m x a; simp, map_d := by intro n x; simp }

/-- The componentwise sum of homomorphisms. -/
instance : Add (RightModuleHom M N) where
  add f g := { toFun := fun n => f.toFun n + g.toFun n
               map_smul := by
                 intro n m x a
                 simp only [LinearMap.add_apply, f.map_smul, g.map_smul, map_add]
               map_d := by
                 intro n x
                 simp only [LinearMap.add_apply, f.map_d, g.map_d, map_add] }

/-- The componentwise negation of a homomorphism. -/
instance : Neg (RightModuleHom M N) where
  neg f := { toFun := fun n => -f.toFun n
             map_smul := by
               intro n m x a
               simp only [LinearMap.neg_apply, f.map_smul, map_neg]
             map_d := by
               intro n x
               simp only [LinearMap.neg_apply, f.map_d, map_neg] }

/-- The components of the zero homomorphism vanish. -/
@[simp] theorem zero_toFun (n : ℤ) (x : M.carrier n) : (0 : RightModuleHom M N).toFun n x = 0 := rfl
/-- The components of `f + g` are the sums of the components of `f` and `g`. -/
@[simp] theorem add_toFun (f g : RightModuleHom M N) (n : ℤ) (x : M.carrier n) :
    (f + g).toFun n x = f.toFun n x + g.toFun n x := rfl
/-- The components of `-f` are the negatives of the components of `f`. -/
@[simp] theorem neg_toFun (f : RightModuleHom M N) (n : ℤ) (x : M.carrier n) :
    (-f).toFun n x = -f.toFun n x := rfl

/-- The homomorphism group `Hom_{Mod_(A,d)}(M, N)`. -/
instance : AddCommGroup (RightModuleHom M N) where
  add_assoc := by intros; ext n x; simp [add_assoc]
  zero_add := by intros; ext n x; simp
  add_zero := by intros; ext n x; simp
  add_comm := by intros; ext n x; simp [add_comm]
  neg_add_cancel := by intros; ext n x; simp
  nsmul := nsmulRec
  zsmul := zsmulRec

end RightModuleHom

/-- Composition of homomorphisms of right differential graded modules. -/
def RightModuleHom.comp {M N P : RightModule A} (g : RightModuleHom N P) (f : RightModuleHom M N) :
    RightModuleHom M P where
  toFun n := (g.toFun n).comp (f.toFun n)
  map_smul := by intro n m x a; simp only [LinearMap.comp_apply, f.map_smul, g.map_smul]
  map_d := by intro n x; simp only [LinearMap.comp_apply, f.map_d, g.map_d]

/-- The components of `g.comp f` are the composites of the components. -/
@[simp] theorem RightModuleHom.comp_toFun {M N P : RightModule A} (g : RightModuleHom N P)
    (f : RightModuleHom M N) (n : ℤ) (x : M.carrier n) :
    (g.comp f).toFun n x = g.toFun n (f.toFun n x) := rfl

namespace RightModule
variable (M : RightModule A)

/-- Congruence of `M.smul` in its first argument under `HEq`. -/
theorem smul_congr_heq {i j p : ℤ} (hij : i = j) {x : M.carrier i} {y : M.carrier j}
    (hxy : HEq x y) (a : A.carrier p) : HEq (M.smul i p x a) (M.smul j p y a) := by
  subst hij; cases hxy; rfl

/-- The shift `M[k]`: `(M[k])^n = M^{n+k}`, with `d_{M[k]} = (-1)^k d_M` and the same right
action. -/
noncomputable def shift (k : ℤ) : RightModule A where
  carrier n := M.carrier (n + k)
  smul n m :=
    (LinearMap.llcomp R (A.carrier m) (M.carrier ((n + k) + m)) (M.carrier ((n + m) + k))
        (degCastLin R (show (n + k) + m = (n + m) + k by ring)).toLinearMap).comp (M.smul (n + k) m)
  smul_assoc := by
    intro n m p x a b
    simp only [LinearMap.llcomp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    apply eq_of_heq
    refine HEq.trans (degCast_heq _ _) ?_
    refine HEq.trans (degCastLin_heq R _ _) ?_
    have hassoc := M.smul_assoc (n + k) m p x a b
    refine HEq.trans ?_ ((degCastLin_heq R _ _).symm)
    refine HEq.trans ?_ (heq_of_eq hassoc)
    refine HEq.trans ?_ (degCast_heq _ _).symm
    exact smul_congr_heq M (by ring) (degCastLin_heq R _ _) b
  smul_one := by
    intro n x
    simp only [LinearMap.llcomp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    apply eq_of_heq
    refine HEq.trans (degCast_heq _ _) ?_
    refine HEq.trans (degCastLin_heq R _ _) ?_
    exact (degCast_heq _ _).symm.trans (heq_of_eq (M.smul_one (n + k) x))
  d n := (degCastLin R (show (n + k) + 1 = (n + 1) + k by ring)).toLinearMap.comp
            (((-1 : ℤ) ^ k.natAbs) • M.d (n + k))
  d_comp_d := by
    intro n x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe]
    rw [family_degCastLin R M.d, degCastLin_smul, degCastLin_trans, map_zsmul, M.d_comp_d,
      smul_zero, degCastLin_zero, smul_zero]
  leibniz := by
    intro n m x a
    simp only [LinearMap.comp_apply, LinearMap.llcomp_apply, LinearMap.smul_apply,
      LinearEquiv.coe_coe]
    rw [family_degCastLin R M.d]
    rw [degCastLin_smul]
    rw [degCastLin_trans]
    rw [map_zsmul]
    rw [M.leibniz (n + k) m]
    rw [map_add, smul_add]
    rw [show ((-1 : ℤ) ^ k.natAbs • (degCastLin R (show (n + k) + 1 = (n + 1) + k by ring))
          ((M.d (n + k)) x)) = (degCastLin R (show (n + k) + 1 = (n + 1) + k by ring))
          ((-1 : ℤ) ^ k.natAbs • (M.d (n + k)) x) from (degCastLin_smul R _ _ _).symm]
    rw [bil_degCastLin R M.smul]
    simp only [map_zsmul, LinearMap.smul_apply, degCast_smul]
    congr 1
    · congr 1
      apply eq_of_heq
      refine HEq.trans (degCastLin_heq R _ _) ?_
      refine HEq.trans (degCast_heq _ _) ?_
      refine HEq.trans ?_ (degCast_heq _ _).symm
      refine HEq.trans ?_ (degCastLin_heq R _ _).symm
      refine HEq.trans ?_ (degCastLin_heq R _ _).symm
      rfl
    · rw [smul_smul, sign_recon]
      congr 1
      apply eq_of_heq
      refine HEq.trans (degCastLin_heq R _ _) ?_
      refine HEq.trans (degCast_heq _ _) ?_
      refine HEq.trans ?_ (degCast_heq _ _).symm
      refine HEq.trans ?_ (degCastLin_heq R _ _).symm
      rfl

/-! ### The dual complex `M^vee` -/

/-- The degree-`n` piece of the dual complex `M^vee`: `(M^vee)^n = Hom_Z(M^{-n}, Q/Z)`, with
the `R`-module structure `(r . f)(x) = f(r . x)`. -/
abbrev dualSpace (n : ℤ) : Type u := RDual R (M.carrier (-n))

/-- The differential of `M`, viewed as the `R`-linear map `M^{-(n+1)} -> M^{-n}`. -/
noncomputable def dDownshift (n : ℤ) : M.carrier (-(n + 1)) →ₗ[R] M.carrier (-n) :=
  (degCastLin R (show (-(n + 1)) + 1 = -n by ring)).toLinearMap.comp (M.d (-(n + 1)))

/-- `dDownshift n x` is `d_M x` transported into degree `-n`. -/
@[simp] theorem dDownshift_apply (n : ℤ) (x : M.carrier (-(n + 1))) :
    M.dDownshift n x
      = degCastLin R (show (-(n + 1)) + 1 = -n by ring) (M.d (-(n + 1)) x) := rfl

/-- The differential of the dual complex, `d_{M^vee} : (M^vee)^n -> (M^vee)^{n+1}`,
`f |-> (-1)^{n+1} . (f . d_M)`, as an `R`-linear map. -/
noncomputable def dDual (n : ℤ) : M.dualSpace n →ₗ[R] M.dualSpace (n + 1) :=
  ((-1 : ℤ) ^ (n + 1).natAbs) • (RDual.precompₗ (M.dDownshift n))

/-- `(d_{M^vee} f)(x) = (-1)^{n+1} f(d_M x)`. -/
@[simp] theorem dDual_apply (n : ℤ) (f : M.dualSpace n) (x : M.carrier (-(n + 1))) :
    (show M.carrier (-(n + 1)) →+ QZ from M.dDual n f) x
      = ((-1 : ℤ) ^ (n + 1).natAbs) •
          (show M.carrier (-n) →+ QZ from f) (M.dDownshift n x) := by
  change (show M.carrier (-(n + 1)) →+ QZ from
      (((-1 : ℤ) ^ (n + 1).natAbs) • (RDual.precompₗ (M.dDownshift n))) f) x = _
  rw [LinearMap.smul_apply]
  change (show M.carrier (-(n + 1)) →+ QZ from
      ((-1 : ℤ) ^ (n + 1).natAbs) • (RDual.precompₗ (M.dDownshift n) f)) x = _
  rw [AddMonoidHom.zsmul_apply, RDual.precompₗ_apply]

/-- The differential of the dual complex squares to zero: `d_{M^vee} . d_{M^vee} = 0`. -/
theorem dDual_comp_dDual (n : ℤ) (f : M.dualSpace n) :
    M.dDual (n + 1) (M.dDual n f) = 0 := by
  apply RDual.ext
  intro x
  rw [dDual_apply]
  show _ = (show M.carrier (-(n + 1 + 1)) →+ QZ from (0 : M.dualSpace (n + 1 + 1))) x
  rw [RDual.zero_apply]
  rw [dDual_apply, dDownshift_apply, dDownshift_apply]
  have hzero : M.d (-(n + 1)) (degCastLin R (show (-(n + 1 + 1)) + 1 = -(n + 1) by ring)
      (M.d (-(n + 1 + 1)) x)) = 0 := by
    rw [family_degCastLin R M.d, M.d_comp_d, degCastLin_zero]
  rw [hzero, degCastLin_zero, map_zero, smul_zero, smul_zero]

/-- Cocycles `Z^k(M^vee) = ker(d_{M^vee} : (M^vee)^k -> (M^vee)^{k+1})`, as an
`R`-submodule of `(M^vee)^k`. -/
noncomputable def cocyclesₛ (k : ℤ) : Submodule R (M.dualSpace k) := LinearMap.ker (M.dDual k)

/-- Coboundaries `B^k(M^vee) = im(d_{M^vee} : (M^vee)^{k-1} -> (M^vee)^k)`, transported
into `(M^vee)^k`, as an `R`-submodule. -/
noncomputable def coboundariesₛ (k : ℤ) : Submodule R (M.dualSpace k) :=
  (LinearMap.range (M.dDual (k - 1))).map
    (degCastLin R (show k - 1 + 1 = k by ring) (V := fun n => M.dualSpace n)).toLinearMap

/-- Coboundaries of the dual complex are cocycles: `B^k(M^vee) <= Z^k(M^vee)`. -/
theorem coboundariesₛ_le_cocyclesₛ (k : ℤ) : M.coboundariesₛ k ≤ M.cocyclesₛ k := by
  rintro y ⟨z, ⟨w, hw⟩, hz⟩
  rw [cocyclesₛ, LinearMap.mem_ker]
  subst hz
  subst hw
  change M.dDual k (degCastLin R (show k - 1 + 1 = k by ring) (M.dDual (k - 1) w)) = 0
  rw [family_degCastLin R (fun n => M.dDual n) (show k - 1 + 1 = k by ring)]
  rw [M.dDual_comp_dDual (k - 1), degCastLin_zero]

/-- The cocycles `Z^k(M^vee)`, as an additive subgroup of `(M^vee)^k`. -/
noncomputable def cocycles (k : ℤ) : AddSubgroup (M.dualSpace k) :=
  (M.cocyclesₛ k).toAddSubgroup

/-- The coboundaries `B^k(M^vee)`, as an additive subgroup of `(M^vee)^k`. -/
noncomputable def coboundaries (k : ℤ) : AddSubgroup (M.dualSpace k) :=
  (M.coboundariesₛ k).toAddSubgroup

/-- The coboundary subgroup `B^k(M^vee)` is contained in the cocycle subgroup `Z^k(M^vee)`. -/
theorem coboundaries_le_cocycles (k : ℤ) : M.coboundaries k ≤ M.cocycles k := by
  intro x hx
  exact M.coboundariesₛ_le_cocyclesₛ k hx

/-- The cohomology `H^k(M^vee) = Z^k(M^vee) / B^k(M^vee)` of the dual complex. -/
noncomputable def cohomology (k : ℤ) : Type u :=
  (M.cocycles k) ⧸ ((M.coboundaries k).addSubgroupOf (M.cocycles k))

/-- The quotient group structure on `H^k(M^vee)`. -/
noncomputable instance (k : ℤ) : AddCommGroup (M.cohomology k) := by
  unfold cohomology; infer_instance

end RightModule

end DGAlgebra

end Stacks.DifferentialGradedDual
