module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RepresentationTheory.Intertwining
public import StacksCore.Tactic.StacksAttribute

/-!
# Projectivity and finiteness for a diagonal group action

Let `A` be a commutative ring, `Λ` a possibly noncommutative `A`-algebra and `G` a group.
Given an `A`-linear representation of `G` on `P` and a `Λ`-linear representation of `G` on
`M`, the tensor product `P ⊗[A] M` carries the diagonal action of `G`, hence is a module over
the group algebra `Λ[G]`.  It is finite over `Λ[G]` when `P` is finite over `A[G]` and `M` is
finite over `Λ`, and projective over `Λ[G]` when `P` is projective over `A[G]` and `M` is
projective over `Λ`.

## Main definitions

* `Stacks.Trace.Representation.asModuleNC`: the module over a group algebra attached to a
  representation with possibly noncommutative coefficient ring.
* `Stacks.Trace.diagonalTensorProduct`: the tensor product `P ⊗[A] M`, with its
  coefficient-module structure.
* `Stacks.Trace.Representation.tprodAlgebra`: the diagonal action on that tensor product.
* `Stacks.Trace.Representation.tprodAlgebraCommModuleEquiv`: tensor symmetry, as an equivalence
  of modules over the group algebra.

## Main results

* `Stacks.Trace.diagonalAction_module_finite`: finiteness for the diagonal action.
* `Stacks.Trace.diagonalAction_module_projective`: projectivity for the diagonal action.

## Implementation notes

The type `diagonalTensorProduct A Λ P M` is the tensor product in the order `P ⊗[A] M`.
Mathlib supplies a coefficient-module structure on the opposite order `M ⊗[A] P`, and the
`Λ`-module structure is transported across tensor symmetry.

Modules over group algebras are presented in the equivalent language of linear
representations.  Mathlib's `Representation.asModule` carries a `Λ[G]`-module structure only
for commutative `Λ`, since it factors through `Representation.asAlgebraHom`;
`Representation.asModuleNC` is the variant whose module structure is built from
`MonoidAlgebra.liftNCRingHom` and so is available for a noncommutative coefficient ring.

## References

* [Stacks Project, Tag 03U9](https://stacks.math.columbia.edu/tag/03U9)
-/

@[expose] public section

universe uA uΛ uG uP uM

namespace Stacks.Trace

open MonoidAlgebra

/-- The tensor product `P ⊗[A] M`, equipped below with the `Λ`-module structure induced from
its second factor. -/
def diagonalTensorProduct
    (A : Type uA) (_Λ : Type uΛ) (P : Type uP) (M : Type uM)
    [CommSemiring A] [Semiring _Λ] [Algebra A _Λ]
    [AddCommMonoid P] [Module A P]
    [AddCommMonoid M] [Module A M] [Module _Λ M] [IsScalarTower A _Λ M] :=
  TensorProduct A P M
  deriving AddCommMonoid, Module A

/-- Tensor symmetry, as an additive equivalence from `P ⊗[A] M` to the order `M ⊗[A] P` in
which Mathlib supplies the coefficient-module structure. -/
def diagonalTensorCommAddEquiv
    {A : Type uA} {Λ : Type uΛ} {P : Type uP} {M : Type uM}
    [CommSemiring A] [Semiring Λ] [Algebra A Λ]
    [AddCommMonoid P] [Module A P]
    [AddCommMonoid M] [Module A M] [Module Λ M] [IsScalarTower A Λ M] :
    diagonalTensorProduct A Λ P M ≃+ TensorProduct A M P :=
  (TensorProduct.comm A P M).toAddEquiv

/-- The `Λ`-module structure on `P ⊗[A] M`, transported from `M ⊗[A] P` across tensor
symmetry. -/
noncomputable instance diagonalTensorProduct.module
    {A : Type uA} {Λ : Type uΛ} {P : Type uP} {M : Type uM}
    [CommSemiring A] [Semiring Λ] [Algebra A Λ]
    [AddCommMonoid P] [Module A P]
    [AddCommMonoid M] [Module A M] [Module Λ M] [IsScalarTower A Λ M] :
    Module Λ (diagonalTensorProduct A Λ P M) :=
  (diagonalTensorCommAddEquiv (A := A) (Λ := Λ) (P := P) (M := M)).module Λ

/-- Tensor symmetry as a `Λ`-linear equivalence. -/
noncomputable def diagonalTensorComm
    {A : Type uA} {Λ : Type uΛ} {P : Type uP} {M : Type uM}
    [CommSemiring A] [Semiring Λ] [Algebra A Λ]
    [AddCommMonoid P] [Module A P]
    [AddCommMonoid M] [Module A M] [Module Λ M] [IsScalarTower A Λ M] :
    diagonalTensorProduct A Λ P M ≃ₗ[Λ] TensorProduct A M P :=
  (diagonalTensorCommAddEquiv (A := A) (Λ := Λ) (P := P) (M := M)).linearEquiv Λ

namespace Representation

/-- The module over a possibly noncommutative group algebra associated to a linear
representation.  This is the noncommutative-coefficient analogue of Mathlib's
`Representation.asModule`. -/
def asModuleNC
    {k : Type*} {G : Type*} {V : Type*} [Semiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] (_ : _root_.Representation k G V) := V
  deriving AddCommMonoid, Module k, Module (AddMonoid.End V)

/-- A representation, read as a monoid homomorphism from `G` to the additive endomorphisms of
the underlying module. -/
def actionAddEnd
    {k : Type*} {G : Type*} {V : Type*} [Semiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] (ρ : _root_.Representation k G V) :
    G →* AddMonoid.End V where
  toFun g := (ρ g).toAddMonoidHom
  map_one' := by
    ext v
    change ρ 1 v = v
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v
    change ρ (g * h) v = ρ g (ρ h v)
    rw [map_mul]
    rfl

/-- The `k[G]`-module structure on `asModuleNC ρ`, built from the scalar action of `k` and the
action of `G` by `MonoidAlgebra.liftNCRingHom`.  Unlike the instance on
`Representation.asModule`, this does not require `k` to be commutative. -/
noncomputable instance asModuleNC.moduleMonoidAlgebra
    {k : Type*} {G : Type*} {V : Type*} [Semiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] (ρ : _root_.Representation k G V) :
    Module k[G] (asModuleNC ρ) :=
  Module.compHom _ (MonoidAlgebra.liftNCRingHom (Module.toAddMonoidEnd k V)
    (actionAddEnd ρ) fun r g => by ext v; exact ((ρ g).map_smul r v).symm)

/-- Acting by `single g a` on `asModuleNC ρ` is acting by `g` and then scaling by `a`. -/
lemma single_smul_asModuleNC
    {k : Type*} {G : Type*} {V : Type*} [Semiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] (ρ : _root_.Representation k G V)
    (a : k) (g : G) (x : asModuleNC ρ) :
    (MonoidAlgebra.single g a : k[G]) • x = a • ρ g x := by
  let hcomm : ∀ r g, Commute (Module.toAddMonoidEnd k V r) (actionAddEnd ρ g) :=
    fun r g => by ext v; exact ((ρ g).map_smul r v).symm
  change (MonoidAlgebra.liftNCRingHom (Module.toAddMonoidEnd k V) (actionAddEnd ρ) hcomm
    (MonoidAlgebra.single g a)) x = _
  rw [MonoidAlgebra.liftNCRingHom_single]
  rfl

/-- Acting by `single 1 a` on `asModuleNC ρ` is scaling by `a`. -/
private lemma single_one_smul_asModuleNC
    {k : Type*} {G : Type*} {V : Type*} [Semiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] (ρ : _root_.Representation k G V)
    (a : k) (x : asModuleNC ρ) :
    (MonoidAlgebra.single 1 a : k[G]) • x = a • x := by
  rw [single_smul_asModuleNC, map_one]
  rfl

/-- Acting by `of g` on `asModuleNC ρ` is acting by `g`. -/
private lemma of_smul_asModuleNC
    {k : Type*} {G : Type*} {V : Type*} [Semiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] (ρ : _root_.Representation k G V)
    (g : G) (x : asModuleNC ρ) :
    (MonoidAlgebra.of k G g : k[G]) • x = ρ g x := by
  rw [MonoidAlgebra.of_apply, single_smul_asModuleNC, one_smul]

/-- Scaling an element of the group algebra by `a` is multiplying by `single 1 a`. -/
private lemma smul_eq_single_one_mul
    {k : Type*} {G : Type*} [Semiring k] [Monoid G] (a : k) (r : k[G]) :
    a • r = MonoidAlgebra.single 1 a * r := by
  ext g
  simp [MonoidAlgebra.coeff_single_one_mul]

/-- A `k`-linear map between the modules of two representations which intertwines the group
actions is `k[G]`-linear. -/
lemma map_smul_asModuleNC
    {k : Type*} {G : Type*} {V : Type*} {W : Type*} [Semiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (ρ : _root_.Representation k G V) (σ : _root_.Representation k G W)
    (f : asModuleNC ρ →ₗ[k] asModuleNC σ) (hf : ∀ g x, f (ρ g x) = σ g (f x))
    (r : k[G]) (x : asModuleNC ρ) :
    f (r • x) = r • f x := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
      rw [MonoidAlgebra.of_apply, single_smul_asModuleNC, single_smul_asModuleNC,
        one_smul, one_smul]
      exact hf g x
  | add r s hr hs => rw [add_smul, map_add, hr, hs, add_smul]
  | smul a r hr =>
      rw [smul_eq_single_one_mul, mul_smul, mul_smul, single_one_smul_asModuleNC,
        single_one_smul_asModuleNC]
      change f (a • (r • x)) = a • (r • f x)
      rw [map_smul, hr]

/-- The diagonal `G`-action on `M ⊗[A] P`. -/
noncomputable def tprodAlgebraReversed
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommSemiring A] [Semiring Λ] [Algebra A Λ] [Monoid G]
    [AddCommMonoid P] [Module A P]
    [AddCommMonoid M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M) :
    _root_.Representation Λ G (TensorProduct A M P) where
  toFun g := TensorProduct.AlgebraTensorModule.map (σ g) (ρ g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/-- The diagonal `G`-action on the tensor product `P ⊗[A] M`. -/
@[sga "4½ Rapport 5.7"]
noncomputable def tprodAlgebra
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommSemiring A] [Semiring Λ] [Algebra A Λ] [Monoid G]
    [AddCommMonoid P] [Module A P]
    [AddCommMonoid M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M) :
    _root_.Representation Λ G (diagonalTensorProduct A Λ P M) :=
  let e := diagonalTensorComm (A := A) (Λ := Λ) (P := P) (M := M)
  { toFun g := e.symm.toLinearMap.comp ((tprodAlgebraReversed ρ σ g).comp e.toLinearMap)
    map_one' := by ext x; simp
    map_mul' g h := by ext x; simp }

/-- The diagonal action on a pure tensor acts on each factor. -/
@[simp]
lemma tprodAlgebra_apply_tmul
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommSemiring A] [Semiring Λ] [Algebra A Λ] [Monoid G]
    [AddCommMonoid P] [Module A P]
    [AddCommMonoid M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (g : G) (p : P) (m : M) :
    tprodAlgebra ρ σ g (p ⊗ₜ[A] m) = ρ g p ⊗ₜ[A] σ g m :=
  rfl

/-- Tensor symmetry intertwines the diagonal actions on `P ⊗[A] M` and on `M ⊗[A] P`. -/
noncomputable def tprodAlgebraCommEquiv
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommSemiring A] [Semiring Λ] [Algebra A Λ] [Monoid G]
    [AddCommMonoid P] [Module A P]
    [AddCommMonoid M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M) :
    (tprodAlgebra ρ σ).Equiv (tprodAlgebraReversed ρ σ) :=
  _root_.Representation.Equiv.mk diagonalTensorComm fun g => by ext x; simp [tprodAlgebra]

/-- Tensor symmetry as a linear equivalence over the (possibly noncommutative-coefficient)
group algebra, from `P ⊗[A] M` to `M ⊗[A] P`. -/
noncomputable def tprodAlgebraCommModuleEquiv
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommSemiring A] [Semiring Λ] [Algebra A Λ] [Monoid G]
    [AddCommMonoid P] [Module A P]
    [AddCommMonoid M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M) :
    asModuleNC (tprodAlgebra ρ σ) ≃ₗ[Λ[G]] asModuleNC (tprodAlgebraReversed ρ σ) :=
  { diagonalTensorComm with
    map_smul' r x := map_smul_asModuleNC (tprodAlgebra ρ σ) (tprodAlgebraReversed ρ σ)
      diagonalTensorComm.toLinearMap (fun g x ↦
        LinearMap.congr_fun ((tprodAlgebraCommEquiv ρ σ).toIntertwiningMap.isIntertwining' g) x)
      r x }

/-- Tensor symmetry swaps the factors of a pure tensor. -/
@[simp]
lemma tprodAlgebraCommModuleEquiv_apply_tmul
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommSemiring A] [Semiring Λ] [Algebra A Λ] [Monoid G]
    [AddCommMonoid P] [Module A P]
    [AddCommMonoid M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (p : P) (m : M) :
    tprodAlgebraCommModuleEquiv ρ σ (p ⊗ₜ[A] m) = m ⊗ₜ[A] p :=
  rfl

end Representation

/-- Acting by `single g a` on a pure tensor of `P ⊗[A] M` with the diagonal action. -/
private lemma single_smul_diagonal_tmul
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (g : G) (a : Λ) (p : P) (m : M) :
    (MonoidAlgebra.single g a : Λ[G]) •
      (show Representation.asModuleNC (Representation.tprodAlgebra ρ σ) from p ⊗ₜ[A] m) =
      (ρ g p ⊗ₜ[A] (a • σ g m)) := by
  rw [Representation.single_smul_asModuleNC,
    Representation.tprodAlgebra_apply_tmul]
  rfl

/-- `tmul_zero`, transported to the type synonym carrying the diagonal action. -/
private lemma diagonal_tmul_zero
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (p : P) : (p ⊗ₜ[A] (0 : M) : Representation.asModuleNC
      (Representation.tprodAlgebra ρ σ)) = 0 :=
  TensorProduct.tmul_zero M p

/-- `zero_tmul`, transported to the type synonym carrying the diagonal action. -/
private lemma diagonal_zero_tmul
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (m : M) : ((0 : P) ⊗ₜ[A] m : Representation.asModuleNC
      (Representation.tprodAlgebra ρ σ)) = 0 :=
  TensorProduct.zero_tmul P m

/-- `tmul_add`, transported to the type synonym carrying the diagonal action. -/
private lemma diagonal_tmul_add
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (p : P) (m n : M) : (p ⊗ₜ[A] (m + n) : Representation.asModuleNC
      (Representation.tprodAlgebra ρ σ)) = p ⊗ₜ[A] m + p ⊗ₜ[A] n :=
  TensorProduct.tmul_add p m n

/-- `add_tmul`, transported to the type synonym carrying the diagonal action. -/
private lemma diagonal_add_tmul
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (p q : P) (m : M) : ((p + q) ⊗ₜ[A] m : Representation.asModuleNC
      (Representation.tprodAlgebra ρ σ)) = p ⊗ₜ[A] m + q ⊗ₜ[A] m :=
  TensorProduct.add_tmul p q m

/-- `smul_tmul`, transported to the type synonym carrying the diagonal action. -/
private lemma diagonal_smul_tmul
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (a : A) (p : P) (m : M) : ((a • p) ⊗ₜ[A] m : Representation.asModuleNC
      (Representation.tprodAlgebra ρ σ)) = p ⊗ₜ[A] (a • m) :=
  TensorProduct.smul_tmul a p m

/-- Acting by `single g a` on a pure tensor of `M ⊗[A] P` with the diagonal action. -/
lemma single_smul_reversed_tmul
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (g : G) (a : Λ) (m : M) (p : P) :
    (MonoidAlgebra.single g a : Λ[G]) •
      (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
        m ⊗ₜ[A] p) = (a • σ g m) ⊗ₜ[A] ρ g p := by
  rw [Representation.single_smul_asModuleNC]
  rfl

/-- `tmul_add`, transported to the type synonym carrying the action on `M ⊗[A] P`. -/
private lemma reversed_tmul_add
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (m : M) (p q : P) : (m ⊗ₜ[A] (p + q) : Representation.asModuleNC
      (Representation.tprodAlgebraReversed ρ σ)) = m ⊗ₜ[A] p + m ⊗ₜ[A] q :=
  TensorProduct.tmul_add m p q

/-- `add_tmul`, transported to the type synonym carrying the action on `M ⊗[A] P`. -/
private lemma reversed_add_tmul
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (m n : M) (p : P) : ((m + n) ⊗ₜ[A] p : Representation.asModuleNC
      (Representation.tprodAlgebraReversed ρ σ)) = m ⊗ₜ[A] p + n ⊗ₜ[A] p :=
  TensorProduct.add_tmul m n p

/-- Balancing a scalar from `A` across a pure tensor of `M ⊗[A] P`. -/
private lemma reversed_tmul_smul
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (a : A) (m : M) (p : P) : (m ⊗ₜ[A] (a • p) : Representation.asModuleNC
      (Representation.tprodAlgebraReversed ρ σ)) = (a • m) ⊗ₜ[A] p :=
  (TensorProduct.smul_tmul a m p).symm

/-- Acting by `single 1 a` on `M ⊗[A] P` scales the first factor by `a`. -/
private lemma reversed_coeff_smul
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (a : Λ) (m : M) (p : P) :
    (MonoidAlgebra.single 1 a : Λ[G]) •
      (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
        m ⊗ₜ[A] p) = (a • m) ⊗ₜ[A] p := by
  rw [single_smul_reversed_tmul, map_one, map_one]
  rfl

/-- A tensor product with diagonal action is finite over the
group algebra when both input modules are finite over their respective rings. -/
@[stacks 03U9 "finiteness"]
lemma diagonalAction_module_finite
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    [Module.Finite A[G] (Representation.asModuleNC ρ)] [Module.Finite Λ M] :
    Module.Finite Λ[G] (Representation.asModuleNC (Representation.tprodAlgebra ρ σ)) := by
  classical
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin (R := A[G])
    (M := Representation.asModuleNC ρ)
  obtain ⟨k, m, hm⟩ := Module.Finite.exists_fin (R := Λ) (M := M)
  let t : Fin n × Fin k → Representation.asModuleNC (Representation.tprodAlgebra ρ σ) :=
    fun ij => p ij.1 ⊗ₜ[A] m ij.2
  let S : Submodule Λ[G] (Representation.asModuleNC (Representation.tprodAlgebra ρ σ)) :=
    Submodule.span Λ[G] (Set.range t)
  have hgen_m (i : Fin n) (x : M) : (p i ⊗ₜ[A] x :
      Representation.asModuleNC (Representation.tprodAlgebra ρ σ)) ∈ S := by
    have hx : x ∈ Submodule.span Λ (Set.range m) := by rw [hm]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨j, rfl⟩
        exact Submodule.subset_span ⟨(i, j), rfl⟩
    | zero =>
        exact (diagonal_tmul_zero ρ σ (p i)).symm ▸ S.zero_mem
    | add x y hx hy ihx ihy =>
        exact (diagonal_tmul_add ρ σ (p i) x y).symm ▸ S.add_mem ihx ihy
    | smul a x hx ih =>
        have h := S.smul_mem (MonoidAlgebra.single 1 a : Λ[G]) ih
        have heq : (MonoidAlgebra.single 1 a : Λ[G]) •
            (show Representation.asModuleNC (Representation.tprodAlgebra ρ σ) from
              p i ⊗ₜ[A] x) = (p i ⊗ₜ[A] (a • x)) := by
          refine (single_smul_diagonal_tmul ρ σ 1 a _ x).trans ?_
          rw [map_one, map_one]
          rfl
        exact heq ▸ h
  have hgen_p (x : Representation.asModuleNC ρ)
      (hx : x ∈ Submodule.span A[G] (Set.range p)) : ∀ y : M,
      (x ⊗ₜ[A] y : Representation.asModuleNC (Representation.tprodAlgebra ρ σ)) ∈ S := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨i, rfl⟩
        exact hgen_m i
    | zero => exact fun y => (diagonal_zero_tmul ρ σ y).symm ▸ S.zero_mem
    | add x z hx hz ihx ihz =>
        exact fun y => (diagonal_add_tmul ρ σ x z y).symm ▸ S.add_mem (ihx y) (ihz y)
    | smul r x hx ih =>
        intro y
        induction r using MonoidAlgebra.induction_on generalizing y with
        | of g =>
            have h := S.smul_mem (MonoidAlgebra.single g (1 : Λ) : Λ[G])
              (ih (σ g⁻¹ y))
            have hdiag : (MonoidAlgebra.single g (1 : Λ) : Λ[G]) •
                (show Representation.asModuleNC (Representation.tprodAlgebra ρ σ) from
                  x ⊗ₜ[A] σ g⁻¹ y) = (ρ g x ⊗ₜ[A] y) := by
              refine (single_smul_diagonal_tmul ρ σ g 1 x _).trans ?_
              rw [one_smul, Representation.self_inv_apply]
            rw [Representation.of_smul_asModuleNC]
            exact hdiag ▸ h
        | add r s hr hs =>
            rw [add_smul]
            exact (diagonal_add_tmul ρ σ (r • x) (s • x) y).symm ▸
              S.add_mem (hr y) (hs y)
        | smul a r hr =>
            have hbalance : (((a • r) • x) ⊗ₜ[A] y :
                Representation.asModuleNC (Representation.tprodAlgebra ρ σ)) =
                (r • x) ⊗ₜ[A] (a • y) := by
              rw [Representation.smul_eq_single_one_mul, mul_smul,
                Representation.single_one_smul_asModuleNC]
              exact diagonal_smul_tmul ρ σ a (r • x) y
            exact hbalance ▸ hr (a • y)
  have hspan : S = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun z => ?_
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact hgen_p x (by rw [hp]; trivial) y
    | add x y hx hy => exact S.add_mem hx hy
  exact Module.Finite.of_fg_top (hspan ▸ Submodule.fg_span (Set.finite_range t))

/-- A `Λ[G]`-module, read as a module over the coefficient rings `Λ` and `A`. -/
private def coefficientModule (A : Type*) (Λ : Type*) (G : Type*) (N : Type*)
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommMonoid N] [Module Λ[G] N] := N

/-- The additive structure of a coefficient module is that of the module it comes from. -/
private instance (A : Type*) (Λ : Type*) (G : Type*) (N : Type*)
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommMonoid N] [Module Λ[G] N] :
    AddCommMonoid (coefficientModule A Λ G N) :=
  inferInstanceAs (AddCommMonoid N)

/-- A coefficient module is still a module over the group algebra. -/
private noncomputable instance (A : Type*) (Λ : Type*) (G : Type*) (N : Type*)
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommMonoid N] [Module Λ[G] N] :
    Module Λ[G] (coefficientModule A Λ G N) :=
  inferInstanceAs (Module Λ[G] N)

/-- The `Λ`-action on a coefficient module, by restriction of scalars along `Λ → Λ[G]`. -/
private noncomputable instance (A : Type*) (Λ : Type*) (G : Type*) (N : Type*)
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommMonoid N] [Module Λ[G] N] : Module Λ (coefficientModule A Λ G N) :=
  Module.compHom _ (MonoidAlgebra.singleOneRingHom (R := Λ) (M := G))

/-- The `A`-action on a coefficient module, by restriction of scalars along `A → Λ`. -/
private noncomputable instance (A : Type*) (Λ : Type*) (G : Type*) (N : Type*)
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommMonoid N] [Module Λ[G] N] : Module A (coefficientModule A Λ G N) :=
  Module.compHom _ (algebraMap A Λ)

/-- The two coefficient actions on a coefficient module form a scalar tower. -/
private instance (A : Type*) (Λ : Type*) (G : Type*) (N : Type*)
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommMonoid N] [Module Λ[G] N] : IsScalarTower A Λ (coefficientModule A Λ G N) :=
  IsScalarTower.of_compHom A Λ _

/-- The two coefficient actions on a coefficient module commute. -/
private instance (A : Type*) (Λ : Type*) (G : Type*) (N : Type*)
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommMonoid N] [Module Λ[G] N] : SMulCommClass A Λ (coefficientModule A Λ G N) :=
  ⟨fun a l n => by simpa using (smul_algebra_smul_comm a l n).symm⟩

/-- The representation of `G` on the coefficient module of a `Λ[G]`-module, given by the action
of the group elements. -/
private noncomputable def coeffRep (A : Type*) (Λ : Type*) (G : Type*) (N : Type*)
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommMonoid N] [Module Λ[G] N] :
    _root_.Representation Λ G (coefficientModule A Λ G N) where
  toFun g := {
    toFun n := (MonoidAlgebra.of Λ G g : Λ[G]) • n
    map_add' := by intros; exact smul_add _ _ _
    map_smul' := by
      intro a n
      change (MonoidAlgebra.of Λ G g : Λ[G]) •
          ((MonoidAlgebra.single 1 a : Λ[G]) • n) =
        (MonoidAlgebra.single 1 a : Λ[G]) •
          ((MonoidAlgebra.of Λ G g : Λ[G]) • n)
      rw [← mul_smul, ← mul_smul]
      congr 1
      simp [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single] }
  map_one' := by
    ext n
    change (MonoidAlgebra.of Λ G 1 : Λ[G]) • n = n
    change (1 : Λ[G]) • n = n
    exact one_smul _ _
  map_mul' g h := by
    ext n
    change (MonoidAlgebra.of Λ G (g * h) : Λ[G]) • n =
      (MonoidAlgebra.of Λ G g : Λ[G]) • ((MonoidAlgebra.of Λ G h : Λ[G]) • n)
    rw [← mul_smul, map_mul]

/-- The representation of `G` on the `Λ`-linear maps `M → N` obtained by conjugating with the
action on `M` and the action on `N`. -/
private noncomputable def homRep
    {A : Type*} {Λ : Type*} {G : Type*} {M : Type*} {N : Type*}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [AddCommMonoid N] [Module Λ[G] N]
    (σ : _root_.Representation Λ G M) :
    _root_.Representation A G (M →ₗ[Λ] coefficientModule A Λ G N) where
  toFun g := {
    toFun f := (coeffRep A Λ G N g).comp (f.comp (σ g⁻¹))
    map_add' := by intro f h; ext m; simp
    map_smul' := by intro a f; ext m; simp }
  map_one' := by ext f m; simp
  map_mul' g h := by
    ext f m
    simp [mul_inv_rev, map_mul, LinearMap.comp_apply]

/-- A `Λ[G]`-linear map, read as a `Λ`-linear map of coefficient modules. -/
private noncomputable def coeffMap
    {A : Type*} {Λ : Type*} {G : Type*} {N Q : Type*}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommMonoid N] [Module Λ[G] N] [AddCommMonoid Q] [Module Λ[G] Q]
    (f : N →ₗ[Λ[G]] Q) : coefficientModule A Λ G N →ₗ[Λ] coefficientModule A Λ G Q where
  toFun := f
  map_add' := f.map_add
  map_smul' a n := by
    change f ((MonoidAlgebra.single 1 a : Λ[G]) • n) =
      (MonoidAlgebra.single 1 a : Λ[G]) • f n
    exact f.map_smul _ _

/-- Post-composition with a `Λ[G]`-linear map, as an `A`-linear map between modules of
`Λ`-linear maps out of `M`. -/
private noncomputable def homMap
    {A : Type*} {Λ : Type*} {G : Type*} {M : Type*} {N Q : Type*}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [AddCommMonoid N] [Module Λ[G] N] [AddCommMonoid Q] [Module Λ[G] Q]
    (f : N →ₗ[Λ[G]] Q) :
      (M →ₗ[Λ] coefficientModule A Λ G N) →ₗ[A] (M →ₗ[Λ] coefficientModule A Λ G Q) where
  toFun φ := (coeffMap f).comp φ
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

/-- Post-composition commutes with the conjugation action of `G`. -/
private theorem homMap_commutes
    {A : Type*} {Λ : Type*} {G : Type*} {M : Type*} {N Q : Type*}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [AddCommMonoid N] [Module Λ[G] N] [AddCommMonoid Q] [Module Λ[G] Q]
    (σ : _root_.Representation Λ G M) (f : N →ₗ[Λ[G]] Q)
    (g : G) (φ : M →ₗ[Λ] coefficientModule A Λ G N) :
    homMap f (homRep σ g φ) = homRep σ g (homMap f φ) := by
  ext m
  change f ((MonoidAlgebra.of Λ G g : Λ[G]) • φ (σ g⁻¹ m)) =
    (MonoidAlgebra.of Λ G g : Λ[G]) • f (φ (σ g⁻¹ m))
  exact f.map_smul _ _

/-- Post-composition with a surjection is surjective when `M` is projective over `Λ`. -/
private theorem homMap_surjective
    {A : Type*} {Λ : Type*} {G : Type*} {M : Type*} {N Q : Type*}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [AddCommMonoid N] [Module Λ[G] N] [AddCommMonoid Q] [Module Λ[G] Q]
    [Module.Projective Λ M]
    (f : N →ₗ[Λ[G]] Q) (hf : Function.Surjective f) :
    Function.Surjective (homMap (A := A) (M := M) f) := by
  intro φ
  have hf' : Function.Surjective (coeffMap (A := A) f) := hf
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property (coeffMap (A := A) f) φ hf'
  refine ⟨ψ, ?_⟩
  ext m
  exact LinearMap.congr_fun hψ m

/-- `homMap`, as a map of modules over `A[G]`. -/
private noncomputable def homMapGroup
    {A : Type*} {Λ : Type*} {G : Type*} {M : Type*} {N Q : Type*}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [AddCommMonoid N] [Module Λ[G] N] [AddCommMonoid Q] [Module Λ[G] Q]
    (σ : _root_.Representation Λ G M) (f : N →ₗ[Λ[G]] Q) :
    Representation.asModuleNC (homRep (A := A) (N := N) σ) →ₗ[A[G]]
      Representation.asModuleNC (homRep (A := A) (N := Q) σ) :=
  { homMap (A := A) (M := M) f with
    map_smul' := by
      intro r φ
      exact Representation.map_smul_asModuleNC
        (homRep (A := A) (N := N) σ) (homRep (A := A) (N := Q) σ)
        (homMap (A := A) (M := M) f)
        (homMap_commutes (A := A) σ f) r φ }

/-- The `A`-linear transpose of a `Λ[G]`-linear map out of `M ⊗[A] P`. -/
private noncomputable def tensorCurryA
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    {Q : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [AddCommMonoid Q] [Module Λ[G] Q]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (h : Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) →ₗ[Λ[G]] Q) :
    Representation.asModuleNC ρ →ₗ[A] (M →ₗ[Λ] coefficientModule A Λ G Q) where
  toFun p := {
    toFun m := h (m ⊗ₜ[A] p)
    map_add' := by
      intro m n
      exact congrArg h (reversed_add_tmul ρ σ m n p) |>.trans (h.map_add _ _)
    map_smul' := by
      intro a m
      have heq := reversed_coeff_smul ρ σ a m p
      have hh := h.map_smul (MonoidAlgebra.single 1 a : Λ[G])
        (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
          m ⊗ₜ[A] p)
      exact heq.symm ▸ hh }
  map_add' := by
    intro p q
    ext m
    exact congrArg h (reversed_tmul_add ρ σ m p q) |>.trans (h.map_add _ _)
  map_smul' := by
    intro a p
    ext m
    have hbal := reversed_tmul_smul ρ σ a m p
    have hcoef := reversed_coeff_smul ρ σ (algebraMap A Λ a) m p
    calc
      h (m ⊗ₜ[A] (a • p)) = h ((a • m) ⊗ₜ[A] p) := congrArg h hbal
      _ = h (((algebraMap A Λ a) • m) ⊗ₜ[A] p) := by
        rw [IsScalarTower.algebraMap_smul]
      _ = h ((MonoidAlgebra.single 1 (algebraMap A Λ a) : Λ[G]) •
            (show Representation.asModuleNC
              (Representation.tprodAlgebraReversed ρ σ) from m ⊗ₜ[A] p)) :=
        congrArg h hcoef.symm
      _ = (show Q from a • (show coefficientModule A Λ G Q from h (m ⊗ₜ[A] p))) := by
        rw [h.map_smul]
        rfl

/-- `tensorCurryA`, as a map of modules over `A[G]`: the tensor-hom adjunction in the direction
that turns a map out of the tensor product into a map out of `P`. -/
private noncomputable def tensorCurryGroup
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    {Q : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [AddCommMonoid Q] [Module Λ[G] Q]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (h : Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) →ₗ[Λ[G]] Q) :
    Representation.asModuleNC ρ →ₗ[A[G]]
      Representation.asModuleNC (homRep (A := A) (N := Q) σ) :=
  { tensorCurryA ρ σ h with
    map_smul' := by
      intro r p
      apply Representation.map_smul_asModuleNC ρ (homRep (A := A) (N := Q) σ)
        (tensorCurryA ρ σ h)
      · intro g p
        apply LinearMap.ext
        intro m
        have hdiag : (MonoidAlgebra.single g (1 : Λ) : Λ[G]) •
            (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ)
              from σ g⁻¹ m ⊗ₜ[A] p) = m ⊗ₜ[A] ρ g p := by
          rw [single_smul_reversed_tmul, one_smul, Representation.self_inv_apply]
        calc
          tensorCurryA ρ σ h (ρ g p) m =
              (show coefficientModule A Λ G Q from h (m ⊗ₜ[A] ρ g p)) := rfl
          _ = (show coefficientModule A Λ G Q from h ((MonoidAlgebra.single g (1 : Λ) : Λ[G]) •
                (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ)
                  from σ g⁻¹ m ⊗ₜ[A] p))) := congrArg h hdiag.symm
          _ = (MonoidAlgebra.single g (1 : Λ) : Λ[G]) •
                (show coefficientModule A Λ G Q from h (σ g⁻¹ m ⊗ₜ[A] p)) :=
            h.map_smul _ _
          _ = homRep (A := A) (N := Q) σ g (tensorCurryA ρ σ h p) m := rfl
      }

/-- A `A[G]`-linear map between the modules of two representations intertwines the group
actions. -/
private lemma groupLinearMap_commutes
    {A : Type*} {G : Type*} {V : Type*} {W : Type*}
    [Semiring A] [Monoid G] [AddCommMonoid V] [Module A V]
    [AddCommMonoid W] [Module A W]
    (ρ : _root_.Representation A G V) (τ : _root_.Representation A G W)
    (u : Representation.asModuleNC ρ →ₗ[A[G]] Representation.asModuleNC τ)
    (g : G) (v : V) : u (ρ g v) = τ g (u v) := by
  have h := u.map_smul (MonoidAlgebra.single g (1 : A) : A[G])
    (show Representation.asModuleNC ρ from v)
  rw [Representation.single_smul_asModuleNC,
    Representation.single_smul_asModuleNC] at h
  simpa using h

/-- A `A[G]`-linear map between the modules of two representations is `A`-linear. -/
private lemma groupLinearMap_smul_base
    {A : Type*} {G : Type*} {V : Type*} {W : Type*}
    [Semiring A] [Monoid G] [AddCommMonoid V] [Module A V]
    [AddCommMonoid W] [Module A W]
    (ρ : _root_.Representation A G V) (τ : _root_.Representation A G W)
    (u : Representation.asModuleNC ρ →ₗ[A[G]] Representation.asModuleNC τ)
    (a : A) (v : V) : u (a • v) = a • u v := by
  have h := u.map_smul (MonoidAlgebra.single 1 a : A[G])
    (show Representation.asModuleNC ρ from v)
  rwa [Representation.single_one_smul_asModuleNC, Representation.single_one_smul_asModuleNC]
    at h

/-- The bilinear map underlying the inverse of `tensorCurryGroup`. -/
private noncomputable def tensorUncurryFlip
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    {N : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [AddCommMonoid N] [Module Λ[G] N]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (u : Representation.asModuleNC ρ →ₗ[A[G]]
      Representation.asModuleNC (homRep (A := A) (N := N) σ)) :
    M →ₗ[Λ] (P →ₗ[A] coefficientModule A Λ G N) where
  toFun m := {
    toFun p := (show M →ₗ[Λ] coefficientModule A Λ G N from u p) m
    map_add' := by
      intro p q
      exact congrArg (fun φ : Representation.asModuleNC
        (homRep (A := A) (N := N) σ) =>
          (show M →ₗ[Λ] coefficientModule A Λ G N from φ) m) (u.map_add p q)
    map_smul' := by
      intro a p
      exact congrArg (fun φ : Representation.asModuleNC
        (homRep (A := A) (N := N) σ) =>
          (show M →ₗ[Λ] coefficientModule A Λ G N from φ) m)
        (groupLinearMap_smul_base ρ (homRep (A := A) (N := N) σ) u a p) }
  map_add' := by
    intro m n
    ext p
    exact (show M →ₗ[Λ] coefficientModule A Λ G N from u p).map_add m n
  map_smul' := by
    intro a m
    ext p
    exact (show M →ₗ[Λ] coefficientModule A Λ G N from u p).map_smul a m

/-- The `Λ`-linear map out of `M ⊗[A] P` determined by `tensorUncurryFlip`. -/
private noncomputable def tensorUncurryLinear
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    {N : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [AddCommMonoid N] [Module Λ[G] N]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (u : Representation.asModuleNC ρ →ₗ[A[G]]
      Representation.asModuleNC (homRep (A := A) (N := N) σ)) :
    Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) →ₗ[Λ]
      coefficientModule A Λ G N :=
  TensorProduct.AlgebraTensorModule.lift (tensorUncurryFlip ρ σ u)

/-- `tensorUncurryLinear` intertwines the diagonal action on `M ⊗[A] P` with the action on the
coefficient module. -/
private lemma tensorUncurryLinear_commutes
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    {N : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [AddCommMonoid N] [Module Λ[G] N]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (u : Representation.asModuleNC ρ →ₗ[A[G]]
      Representation.asModuleNC (homRep (A := A) (N := N) σ))
    (g : G) (z : Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ)) :
    tensorUncurryLinear ρ σ u (Representation.tprodAlgebraReversed ρ σ g z) =
      coeffRep A Λ G N g (tensorUncurryLinear ρ σ u z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m p =>
      have hu := groupLinearMap_commutes ρ (homRep (A := A) (N := N) σ) u g p
      have heval := congrArg (fun φ : Representation.asModuleNC
        (homRep (A := A) (N := N) σ) =>
          (show M →ₗ[Λ] coefficientModule A Λ G N from φ) (σ g m)) hu
      change (show M →ₗ[Λ] coefficientModule A Λ G N from u (ρ g p)) (σ g m) =
        (MonoidAlgebra.of Λ G g : Λ[G]) •
          (show M →ₗ[Λ] coefficientModule A Λ G N from u p) (σ g⁻¹ (σ g m)) at heval
      change (show M →ₗ[Λ] coefficientModule A Λ G N from u (ρ g p)) (σ g m) =
        (MonoidAlgebra.of Λ G g : Λ[G]) •
          (show M →ₗ[Λ] coefficientModule A Λ G N from u p) m
      rwa [Representation.inv_self_apply] at heval
  | add x y hx hy =>
      calc
        tensorUncurryLinear ρ σ u (Representation.tprodAlgebraReversed ρ σ g (x + y)) =
            tensorUncurryLinear ρ σ u
              (Representation.tprodAlgebraReversed ρ σ g x +
                Representation.tprodAlgebraReversed ρ σ g y) :=
          congrArg (tensorUncurryLinear ρ σ u)
            ((Representation.tprodAlgebraReversed ρ σ g).map_add x y)
        _ = tensorUncurryLinear ρ σ u (Representation.tprodAlgebraReversed ρ σ g x) +
              tensorUncurryLinear ρ σ u (Representation.tprodAlgebraReversed ρ σ g y) :=
          (tensorUncurryLinear ρ σ u).map_add _ _
        _ = coeffRep A Λ G N g (tensorUncurryLinear ρ σ u x) +
              coeffRep A Λ G N g (tensorUncurryLinear ρ σ u y) :=
          congrArg₂ (· + ·) hx hy
        _ = coeffRep A Λ G N g
              (tensorUncurryLinear ρ σ u x + tensorUncurryLinear ρ σ u y) :=
          ((coeffRep A Λ G N g).map_add _ _).symm
        _ = coeffRep A Λ G N g (tensorUncurryLinear ρ σ u (x + y)) :=
          congrArg (coeffRep A Λ G N g) ((tensorUncurryLinear ρ σ u).map_add x y).symm

/-- `tensorUncurryLinear`, as a map of modules over `Λ[G]`: the inverse direction of the
group-equivariant tensor-hom adjunction. -/
private noncomputable def tensorUncurryGroup
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    {N : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [AddCommMonoid N] [Module Λ[G] N]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (u : Representation.asModuleNC ρ →ₗ[A[G]]
      Representation.asModuleNC (homRep (A := A) (N := N) σ)) :
    Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) →ₗ[Λ[G]]
      coefficientModule A Λ G N :=
  { tensorUncurryLinear ρ σ u with
    map_smul' := by
      intro r z
      induction r using MonoidAlgebra.induction_on with
      | of g =>
          rw [Representation.of_smul_asModuleNC]
          exact tensorUncurryLinear_commutes ρ σ u g z
      | add r s hr hs =>
          change tensorUncurryLinear ρ σ u ((r + s) • z) =
            (r + s) • tensorUncurryLinear ρ σ u z
          change tensorUncurryLinear ρ σ u (r • z) =
            r • tensorUncurryLinear ρ σ u z at hr
          change tensorUncurryLinear ρ σ u (s • z) =
            s • tensorUncurryLinear ρ σ u z at hs
          calc
            _ = tensorUncurryLinear ρ σ u (r • z + s • z) := by rw [add_smul]
            _ = tensorUncurryLinear ρ σ u (r • z) +
                tensorUncurryLinear ρ σ u (s • z) :=
              (tensorUncurryLinear ρ σ u).map_add _ _
            _ = r • tensorUncurryLinear ρ σ u z +
                s • tensorUncurryLinear ρ σ u z := congrArg₂ (· + ·) hr hs
            _ = _ := (add_smul r s (tensorUncurryLinear ρ σ u z)).symm
      | smul a r hr =>
          change tensorUncurryLinear ρ σ u ((a • r) • z) =
            (a • r) • tensorUncurryLinear ρ σ u z
          change tensorUncurryLinear ρ σ u (r • z) =
            r • tensorUncurryLinear ρ σ u z at hr
          rw [Representation.smul_eq_single_one_mul]
          have hcoef : tensorUncurryLinear ρ σ u
              ((MonoidAlgebra.single 1 a : Λ[G]) • (r • z)) =
              (MonoidAlgebra.single 1 a : Λ[G]) • tensorUncurryLinear ρ σ u (r • z) := by
            rw [Representation.single_one_smul_asModuleNC]
            exact (tensorUncurryLinear ρ σ u).map_smul a (r • z)
          rw [mul_smul, hcoef, hr, mul_smul] }

/-- Uncurrying the curry of a map out of `M ⊗[A] P` gives the map back, on the nose. -/
private theorem tensorUncurry_curry
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    {N : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [AddCommMonoid N] [Module Λ[G] N]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (h : Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) →ₗ[Λ[G]] N) :
    tensorUncurryGroup ρ σ (tensorCurryGroup ρ σ h) =
      (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) →ₗ[Λ[G]]
        coefficientModule A Λ G N from h) := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | tmul m p => rfl
  | add x y hx hy =>
      calc
        tensorUncurryGroup ρ σ (tensorCurryGroup ρ σ h) (x + y) =
            tensorUncurryGroup ρ σ (tensorCurryGroup ρ σ h) x +
              tensorUncurryGroup ρ σ (tensorCurryGroup ρ σ h) y :=
          (tensorUncurryGroup ρ σ (tensorCurryGroup ρ σ h)).map_add x y
        _ = (show coefficientModule A Λ G N from h x) +
              (show coefficientModule A Λ G N from h y) := congrArg₂ (· + ·) hx hy
        _ = (show coefficientModule A Λ G N from h (x + y)) := (h.map_add x y).symm

/-- A `Λ[G]`-linear map, read as a `Λ[G]`-linear map of coefficient modules. -/
private noncomputable def coeffMapGroup
    {A : Type*} {Λ : Type*} {G : Type*} {N Q : Type*}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommMonoid N] [Module Λ[G] N] [AddCommMonoid Q] [Module Λ[G] Q]
    (f : N →ₗ[Λ[G]] Q) : coefficientModule A Λ G N →ₗ[Λ[G]] coefficientModule A Λ G Q := f

/-- `tensorUncurryGroup` is natural in the target. -/
private theorem tensorUncurry_natural
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    {N Q : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [AddCommMonoid N] [Module Λ[G] N] [AddCommMonoid Q] [Module Λ[G] Q]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (f : N →ₗ[Λ[G]] Q)
    (u : Representation.asModuleNC ρ →ₗ[A[G]]
      Representation.asModuleNC (homRep (A := A) (N := N) σ)) :
    (coeffMapGroup (A := A) f).comp (tensorUncurryGroup ρ σ u) =
      tensorUncurryGroup ρ σ ((homMapGroup σ f).comp u) := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | tmul m p => rfl
  | add x y hx hy =>
      calc
        ((coeffMapGroup (A := A) f).comp (tensorUncurryGroup ρ σ u)) (x + y) =
            ((coeffMapGroup (A := A) f).comp (tensorUncurryGroup ρ σ u)) x +
              ((coeffMapGroup (A := A) f).comp (tensorUncurryGroup ρ σ u)) y :=
          (LinearMap.comp (coeffMapGroup (A := A) f)
            (tensorUncurryGroup ρ σ u)).map_add x y
        _ = tensorUncurryGroup ρ σ ((homMapGroup σ f).comp u) x +
              tensorUncurryGroup ρ σ ((homMapGroup σ f).comp u) y :=
          congrArg₂ (· + ·) hx hy
        _ = tensorUncurryGroup ρ σ ((homMapGroup σ f).comp u) (x + y) :=
          (tensorUncurryGroup ρ σ ((homMapGroup σ f).comp u)).map_add x y |>.symm

/-- A tensor product with diagonal action is projective over the group algebra when the first
input is projective over its group algebra and the second is projective over the coefficient
ring. -/
@[stacks 03U9 "projectivity",
  sga "4½ Rapport 5.7" "more general",
  sga "4½ Rapport 5.9" "P⊗M projective"]
lemma diagonalAction_module_projective
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    [Module.Projective A[G] (Representation.asModuleNC ρ)] [Module.Projective Λ M] :
    Module.Projective Λ[G]
      (Representation.asModuleNC (Representation.tprodAlgebra ρ σ)) := by
  let T := Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ)
  have hT : Module.Projective Λ[G] T := by
    apply Module.Projective.of_lifting_property''
    intro f hf
    let H := homMapGroup (A := A) (M := M) σ f
    have hH : Function.Surjective H := homMap_surjective (A := A) (M := M) f hf
    let c := tensorCurryGroup ρ σ (LinearMap.id (R := Λ[G]) (M := T))
    obtain ⟨u, hu⟩ := Module.projective_lifting_property H c hH
    let l : T →ₗ[Λ[G]] (T →₀ Λ[G]) := tensorUncurryGroup ρ σ u
    refine ⟨l, ?_⟩
    have hn := tensorUncurry_natural ρ σ f u
    have hi := tensorUncurry_curry ρ σ (LinearMap.id (R := Λ[G]) (M := T))
    refine LinearMap.ext fun z => ?_
    have hz := LinearMap.congr_fun hn z
    dsimp [H, c] at hu
    rw [hu, hi] at hz
    exact hz
  exact Module.Projective.of_equiv' (Representation.tprodAlgebraCommModuleEquiv ρ σ).symm

end Stacks.Trace
