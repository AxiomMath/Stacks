module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change along an algebra with a linear section

Let `Λ'` be a commutative `Λ`-algebra. Base change `M ↦ Λ' ⊗_Λ M`, formed with the `Λ`-module
structure that the algebra carries, is left adjoint to restriction of scalars. If moreover the
structure map has a `Λ`-linear section `s : Λ' → Λ`, `algebraMap Λ Λ' (s t) = t`, base change is
also *right* adjoint to restriction of scalars: the unit is `n ↦ 1 ⊗ n` and the counit is
`t ⊗ m ↦ s t • m`. This is the situation of the quotient `Λ → Λ ⧸ (1 - e)` by an idempotent,
with section `a ↦ a e`. Being a right adjoint, base change then preserves all limits, so it can be
applied to sheaves sectionwise.

## Main definitions

* `Stacks.ModuleCat.baseChangeFunctor`: `M ↦ Λ' ⊗_Λ M`, at an arbitrary module universe.
* `Stacks.ModuleCat.baseChangeRestrictScalarsAdj`: base change `⊣` restriction of scalars.
* `Stacks.ModuleCat.restrictScalarsBaseChangeAdjOfSection`: restriction of scalars `⊣` base
  change, given a linear section.

## Implementation notes

`Stacks.algebraBaseChange` is the same functor with the module universe tied to the ring universe,
and Mathlib's `ModuleCat.extendScalars` is the same construction formed with the module structure
`Module.compHom Λ' (algebraMap Λ Λ')` on `Λ'`. The coefficient rings of étale sheaves live in a
lower universe than their sections, which rules out the first, and working with the algebra's own
module structure keeps `LinearMap.baseChange` and its API available, which rules out the second.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe v u u'

namespace Stacks.ModuleCat

variable (Λ : Type u) (Λ' : Type u') [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ']

/-- Restricted scalars form a scalar tower over the algebra. -/
public instance isScalarTower_restrictScalars (N : _root_.ModuleCat.{v} Λ') :
    IsScalarTower Λ Λ' ((_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj N) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- **Base change of modules** `M ↦ Λ' ⊗_Λ M` along a commutative algebra, at an arbitrary module
universe. -/
public abbrev baseChangeFunctor : _root_.ModuleCat.{v} Λ ⥤ _root_.ModuleCat.{max v u'} Λ' where
  obj M := _root_.ModuleCat.of Λ' (Λ' ⊗[Λ] M)
  map f := _root_.ModuleCat.ofHom (f.hom.baseChange Λ')
  map_id M := by
    ext : 1
    exact LinearMap.baseChange_id
  map_comp f g := by
    ext : 1
    exact LinearMap.baseChange_comp _ _

variable {Λ Λ'} in
/-- Base change of a morphism `f` sends `t ⊗ m` to `t ⊗ f m`. -/
@[simp]
public theorem baseChangeFunctor_map_tmul {M M' : _root_.ModuleCat.{v} Λ} (f : M ⟶ M') (t : Λ')
    (m : M) : (baseChangeFunctor.{v} Λ Λ').map f (t ⊗ₜ m) = t ⊗ₜ f m :=
  rfl

/-- Additive maps out of `S ⊗[R] M` agreeing on pure tensors are equal. -/
private theorem tensor_ext_of_tmul {R S M P F : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [AddCommMonoid M] [Module R M] [AddCommMonoid P] [FunLike F (S ⊗[R] M) P]
    [AddMonoidHomClass F (S ⊗[R] M) P] {f g : F}
    (h : ∀ (t : S) (m : M), f (t ⊗ₜ[R] m) = g (t ⊗ₜ[R] m)) : f = g :=
  DFunLike.ext _ _ fun x => TensorProduct.induction_on x
    ((map_zero f).trans (map_zero g).symm) h
    fun x y hx hy => (map_add f x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add g x y).symm)

variable {Λ Λ'} in
/-- A morphism out of a base change is determined by its values on the elements `1 ⊗ m`. -/
public theorem baseChangeFunctor_hom_ext {M : _root_.ModuleCat.{v} Λ}
    {N : _root_.ModuleCat.{max v u'} Λ'} {f g : (baseChangeFunctor.{v} Λ Λ').obj M ⟶ N}
    (h : ∀ m : M, f ((1 : Λ') ⊗ₜ m) = g ((1 : Λ') ⊗ₜ m)) : f = g := by
  refine _root_.ModuleCat.hom_ext (tensor_ext_of_tmul fun t m => ?_)
  rw [← mul_one t, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul]
  exact congrArg (t • ·) (h m)

variable {Λ Λ'} in
/-- The map `m ↦ 1 ⊗ m` into the restriction of scalars of the base change. -/
public def tmulOne (M : _root_.ModuleCat.{max v u'} Λ) :
    M ⟶ (_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj
      ((baseChangeFunctor.{max v u'} Λ Λ').obj M) :=
  _root_.ModuleCat.ofHom
    (Y := (_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj
      ((baseChangeFunctor.{max v u'} Λ Λ').obj M))
  { toFun := fun m => ((1 : Λ') ⊗ₜ[Λ] m : Λ' ⊗[Λ] M)
    map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
    map_smul' := fun a m => by
      change (1 : Λ') ⊗ₜ[Λ] (a • m) = algebraMap Λ Λ' a • ((1 : Λ') ⊗ₜ[Λ] m : Λ' ⊗[Λ] M)
      rw [algebraMap_smul, TensorProduct.tmul_smul] }

variable {Λ Λ'} in
/-- The map `t ⊗ n ↦ t • n` out of the base change of a restriction of scalars. -/
public def smulTmul (N : _root_.ModuleCat.{max v u'} Λ') :
    (baseChangeFunctor.{max v u'} Λ Λ').obj
      ((_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj N) ⟶ N :=
  letI : Module Λ N := Module.compHom N (algebraMap Λ Λ')
  haveI : IsScalarTower Λ Λ' N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  _root_.ModuleCat.ofHom
    (X := (baseChangeFunctor.{max v u'} Λ Λ').obj
      ((_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj N))
    (LinearMap.liftBaseChange Λ' (LinearMap.id : N →ₗ[Λ] N))

variable {Λ Λ'} in
/-- `smulTmul` sends `t ⊗ n` to `t • n`. -/
public theorem smulTmul_tmul (N : _root_.ModuleCat.{max v u'} Λ') (t : Λ')
    (n : (_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj N) :
    smulTmul N (t ⊗ₜ[Λ] n) = t • (show N from n) :=
  rfl

/-- **Base change is left adjoint to restriction of scalars.** -/
public def baseChangeRestrictScalarsAdj :
    baseChangeFunctor.{max v u'} Λ Λ' ⊣
      _root_.ModuleCat.restrictScalars.{max v u'} (algebraMap Λ Λ') :=
  Adjunction.mkOfUnitCounit
  { unit :=
      { app := fun M => tmulOne M
        naturality := fun M M' f => by
          ext m
          rfl }
    counit :=
      { app := fun N => smulTmul N
        naturality := fun N N' f => by
          refine baseChangeFunctor_hom_ext fun n => ?_
          change (1 : Λ') • f n = f ((1 : Λ') • (show N from n))
          rw [one_smul, one_smul] }
    left_triangle := by
      refine NatTrans.ext (funext fun M => ?_)
      refine baseChangeFunctor_hom_ext fun m => ?_
      change (1 : Λ') • ((1 : Λ') ⊗ₜ[Λ] m : Λ' ⊗[Λ] M) = (1 : Λ') ⊗ₜ m
      rw [one_smul]
    right_triangle := by
      refine NatTrans.ext (funext fun N => ?_)
      refine _root_.ModuleCat.hom_ext (LinearMap.ext fun n => ?_)
      change (1 : Λ') • (show N from n) = n
      rw [one_smul] }

variable {Λ Λ'} (s : Λ' →ₗ[Λ] Λ) (hs : ∀ t, algebraMap Λ Λ' (s t) = t)

include hs in
/-- The unit `N ⟶ Λ' ⊗_Λ N`, `n ↦ 1 ⊗ n`, of restriction of scalars `⊣` base change, for an
algebra with a linear section. -/
public def oneTmulOfSection (N : _root_.ModuleCat.{max v u'} Λ') :
    N ⟶ (baseChangeFunctor.{max v u'} Λ Λ').obj
      ((_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj N) :=
  _root_.ModuleCat.ofHom
    (Y := (baseChangeFunctor.{max v u'} Λ Λ').obj
      ((_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj N))
  { toFun := fun n => (1 : Λ') ⊗ₜ[Λ]
      (show (_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj N from n)
    map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
    map_smul' := fun t n => by
      obtain ⟨a, rfl⟩ : ∃ a, algebraMap Λ Λ' a = t := ⟨s t, hs t⟩
      let n' : (_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj N := n
      change (1 : Λ') ⊗ₜ[Λ] (a • n') = algebraMap Λ Λ' a • ((1 : Λ') ⊗ₜ[Λ] n')
      rw [algebraMap_smul, TensorProduct.tmul_smul] }

/-- The counit `Λ' ⊗_Λ M ⟶ M`, `t ⊗ m ↦ s t • m`, of restriction of scalars `⊣` base change. -/
public def sectionSMul (M : _root_.ModuleCat.{max v u'} Λ) :
    (_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj
      ((baseChangeFunctor.{max v u'} Λ Λ').obj M) ⟶ M :=
  _root_.ModuleCat.ofHom
    (X := (_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj
      ((baseChangeFunctor.{max v u'} Λ Λ').obj M))
  { toFun := fun x => TensorProduct.lift ((LinearMap.lsmul Λ M).comp s) (x : Λ' ⊗[Λ] M)
    map_add' := fun x y => map_add (TensorProduct.lift ((LinearMap.lsmul Λ M).comp s))
      (x : Λ' ⊗[Λ] M) y
    map_smul' := fun a x => by
      change TensorProduct.lift ((LinearMap.lsmul Λ M).comp s)
          (algebraMap Λ Λ' a • (x : Λ' ⊗[Λ] M)) =
        a • TensorProduct.lift ((LinearMap.lsmul Λ M).comp s) (x : Λ' ⊗[Λ] M)
      refine TensorProduct.induction_on (motive := fun y : Λ' ⊗[Λ] M =>
          TensorProduct.lift ((LinearMap.lsmul Λ M).comp s) (algebraMap Λ Λ' a • y) =
            a • TensorProduct.lift ((LinearMap.lsmul Λ M).comp s) y) (x : Λ' ⊗[Λ] M)
        (by rw [smul_zero, map_zero, smul_zero]) (fun t m => ?_)
        (fun y z hy hz => by rw [smul_add, map_add, map_add, hy, hz, smul_add])
      rw [TensorProduct.smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul,
        LinearMap.comp_apply, LinearMap.comp_apply, algebraMap_smul, map_smul,
        LinearMap.lsmul_apply, LinearMap.lsmul_apply, smul_assoc] }

/-- A morphism out of the restriction of scalars of a base change is determined by its values on
the elements `t ⊗ m`. -/
public theorem restrictScalars_baseChangeFunctor_hom_ext {M : _root_.ModuleCat.{max v u'} Λ}
    {P : _root_.ModuleCat.{max v u'} Λ}
    {f g : (_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj
      ((baseChangeFunctor.{max v u'} Λ Λ').obj M) ⟶ P}
    (h : ∀ (t : Λ') (m : M), f (t ⊗ₜ[Λ] m : Λ' ⊗[Λ] M) = g (t ⊗ₜ[Λ] m : Λ' ⊗[Λ] M)) :
    f = g := by
  exact _root_.ModuleCat.hom_ext (tensor_ext_of_tmul h)

/-- `sectionSMul` sends `t ⊗ m` to `s t • m`. -/
public theorem sectionSMul_tmul (M : _root_.ModuleCat.{max v u'} Λ) (t : Λ') (m : M) :
    sectionSMul s M (t ⊗ₜ[Λ] m : Λ' ⊗[Λ] M) = s t • m :=
  rfl

/-- `t ⊗ m ↦ s t • m ↦ 1 ⊗ s t • m` into a base change along any algebra `Λ''`: it is
`algebraMap Λ Λ'' (s t) ⊗ m` on pure tensors. -/
public theorem tmulOne_sectionSMul_tmul {Λ'' : Type u'} [CommRing Λ''] [Algebra Λ Λ'']
    (M : _root_.ModuleCat.{max v u'} Λ) (t : Λ') (m : M) :
    tmulOne (Λ' := Λ'') M (sectionSMul s M (t ⊗ₜ[Λ] m : Λ' ⊗[Λ] M)) =
      (algebraMap Λ Λ'' (s t) ⊗ₜ[Λ] m : Λ'' ⊗[Λ] M) := by
  show (1 : Λ'') ⊗ₜ[Λ] (s t • m) = _
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

include hs in
/-- **`Λ' ⊗_Λ M` is a retract of `M`**: `t ⊗ m ↦ s t • m ↦ 1 ⊗ s t • m` is the identity. -/
public theorem sectionSMul_comp_tmulOne (M : _root_.ModuleCat.{max v u'} Λ) :
    sectionSMul s M ≫ tmulOne M = 𝟙 _ := by
  refine restrictScalars_baseChangeFunctor_hom_ext fun t m => ?_
  show tmulOne M (sectionSMul s M (t ⊗ₜ[Λ] m : Λ' ⊗[Λ] M)) = (t ⊗ₜ[Λ] m : Λ' ⊗[Λ] M)
  rw [tmulOne_sectionSMul_tmul, hs]

/-- If `s` followed by `Λ → Λ''` is zero, `Λ' ⊗_Λ M → M → Λ'' ⊗_Λ M` is zero. -/
public theorem sectionSMul_comp_tmulOne_eq_zero {Λ'' : Type u'} [CommRing Λ''] [Algebra Λ Λ'']
    (h : ∀ t, algebraMap Λ Λ'' (s t) = 0) (M : _root_.ModuleCat.{max v u'} Λ) :
    sectionSMul s M ≫ tmulOne (Λ' := Λ'') M = 0 := by
  refine restrictScalars_baseChangeFunctor_hom_ext fun t m => ?_
  show tmulOne (Λ' := Λ'') M (sectionSMul s M (t ⊗ₜ[Λ] m : Λ' ⊗[Λ] M)) = 0
  rw [tmulOne_sectionSMul_tmul, h, TensorProduct.zero_tmul]
  rfl

/-- `m ↦ 1 ⊗ m ↦ s 1 • m`. -/
public theorem sectionSMul_tmulOne (M : _root_.ModuleCat.{max v u'} Λ) (m : M) :
    sectionSMul s M (tmulOne M m) = s 1 • m :=
  rfl

/-- **Base change is right adjoint to restriction of scalars**, along an algebra with a linear
section. -/
public def restrictScalarsBaseChangeAdjOfSection :
    _root_.ModuleCat.restrictScalars.{max v u'} (algebraMap Λ Λ') ⊣
      baseChangeFunctor.{max v u'} Λ Λ' :=
  Adjunction.mkOfUnitCounit
  { unit :=
      { app := fun N => oneTmulOfSection s hs N
        naturality := fun N N' g => by
          ext n
          rfl }
    counit :=
      { app := fun M => sectionSMul s M
        naturality := fun M M' g => by
          refine restrictScalars_baseChangeFunctor_hom_ext fun t m => ?_
          change s t • g m = g (s t • m)
          rw [map_smul] }
    left_triangle := by
      refine NatTrans.ext (funext fun N => ?_)
      refine _root_.ModuleCat.hom_ext (LinearMap.ext fun n => ?_)
      change s 1 • (show (_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj N from n) = n
      rw [← algebraMap_smul (A := Λ') (s 1)
        (show (_root_.ModuleCat.restrictScalars (algebraMap Λ Λ')).obj N from n), hs, one_smul]
    right_triangle := by
      refine NatTrans.ext (funext fun M => ?_)
      refine baseChangeFunctor_hom_ext fun m => ?_
      change (1 : Λ') ⊗ₜ[Λ] (s 1 • m) = (1 : Λ') ⊗ₜ m
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, hs, mul_one] }

end Stacks.ModuleCat

end
