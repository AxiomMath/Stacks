module

public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksFrontier.RingTheory.PushoutTensor
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Transpose

/-!
# Comparing two extensions of scalars across a pushout square of rings

Let

    A  ⟶  B
    |      |
    A' ⟶  B'

be a pushout square of commutative rings and let `M` be a `B`-module.  Base changing `M` to
`A'` along `A ⟶ A'` and base changing it to `B'` along `B ⟶ B'` give the same thing, by
`Stacks.Algebra.PushoutBaseChange.isBaseChange_mk_one`.  This file turns that into the form
the geometric application needs: **a map between two modules, each exhibited as a base change
of `M`, which is compatible with the two structural maps from `M`, is invertible.**

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.bijective_of_isBaseChange`: two base changes of
  one module along one ring map are identified by any linear map over the two structural maps.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isBaseChange_restrictScalars`: a base change
  along `B ⟶ B'` is also a base change along `A ⟶ A'`.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_of_isPushout`: the statement above, for
  modules over objects of `CommRingCat` and with the two base changes presented as invertible
  transposes under extension of scalars.

## Route

`bijective_of_isBaseChange` exhibits a two-sided inverse: the lift of one structural map
through the other, `IsBaseChange.lift`, whose two composites with the given map are the
identity by `IsBaseChange.algHom_ext`.

`isBaseChange_restrictScalars` composes `Stacks.Algebra.PushoutBaseChange.isBaseChange_mk_one`
with the linear equivalence `IsBaseChange.equiv` attached to the given base change, and feeds
the composite to `IsBaseChange.of_equiv`; the two agree on `1 ⊗ m` by `IsBaseChange.equiv_tmul`
and `one_smul`.

`isIso_of_isPushout` is the bridge.  The `Algebra` instances come from `algebraize` applied to
the four ring homomorphisms and to the composite along the top and right of the square, the
remaining scalar tower and the `Algebra.IsPushout` instance from
`CommRingCat.isPushout_iff_isPushout`, exactly as in Mathlib's
`CommRingCat.finrank_eq_of_isPushout`.  The module structures on the carriers are the ones
restriction of scalars puts there, so every scalar tower holds by `rfl` apart from the one
that goes round the square, which is the commutativity of the square.

## Implementation notes

The three linear maps are introduced by `let` with their types written out.  This is load
bearing rather than cosmetic: the carrier of `(ModuleCat.restrictScalars β).obj M` and the
carrier of `M` are the same type, but their `AddCommGroup` instances are two terms one
unfolding apart, so a bare `ModuleCat.Hom.hom` arrives carrying the wrapped instance and
instance search for the unwrapped one then fails.  Writing the type on a `let` pins the
instances while keeping the body available for the element computations.

## What is not done

**This file is commutative algebra and proves no assertion of any Stacks tag; no project tag
attribute is attached.**  Nothing here mentions a scheme, a sheaf of modules or a base-change
morphism of direct images; the hypothesis that the two modules are base changes is an input,
not something established here.
-/

@[expose] public section

open CategoryTheory TensorProduct
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChangeIso

/-- Two base changes of the same module along the same ring map are identified by any linear
map compatible with the two structural maps, which is therefore bijective. -/
theorem bijective_of_isBaseChange {R S M N O : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommGroup O] [Module R O] [Module S O] [IsScalarTower R S O]
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) {g : M →ₗ[R] O} (hg : IsBaseChange S g)
    (σ : N →ₗ[S] O) (h : ∀ x, σ (f x) = g x) : Function.Bijective σ := by
  have hσ : σ = (hf.equiv.symm.trans hg.equiv : N ≃ₗ[S] O) :=
    hf.algHom_ext _ _ fun x => by simp [h, IsBaseChange.equiv_symm_apply, IsBaseChange.equiv_tmul]
  rw [hσ]
  exact LinearEquiv.bijective _

/-- A base change along `B ⟶ B'` is also a base change along `A ⟶ A'`, for a pushout square of
commutative rings. -/
theorem isBaseChange_restrictScalars {A B A' B' M N' : Type*}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra B B'] [Algebra A' B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [Algebra.IsPushout A B A' B']
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup N'] [Module A N'] [Module B N'] [Module A' N'] [Module B' N']
    [IsScalarTower A B N'] [IsScalarTower A A' N'] [IsScalarTower B B' N']
    [IsScalarTower A' B' N']
    {v : M →ₗ[B] N'} (hv : IsBaseChange B' v) :
    IsBaseChange A' (v.restrictScalars A) := by
  have hT : IsBaseChange A' ((TensorProduct.mk B B' M (1 : B')).restrictScalars A) :=
    Stacks.Algebra.PushoutBaseChange.isBaseChange_mk_one
  refine IsBaseChange.of_equiv (hT.equiv.trans (hv.equiv.restrictScalars A')) fun m => ?_
  simp [IsBaseChange.equiv_tmul]

variable {A B A' B' : CommRingCat.{u}}

/-- **Two extensions of scalars across a pushout square of rings.**  Let the square `pb`, `qa`,
`qb`, `pb'` be a pushout, let `M` be a `B`-module, let `P` be an `A'`-module exhibited by `u`
as the extension of scalars of `M` along `A ⟶ A'` and let `N'` be a `B'`-module exhibited by
`v` as the extension of scalars of `M` along `B ⟶ B'`.  Then a map `σ` to a module identified
with `N'` which is compatible with `u` and `v` is invertible. -/
theorem isIso_of_isPushout {pb : A ⟶ B} {qa : A ⟶ A'} {qb : B ⟶ B'} {pb' : A' ⟶ B'}
    (hsq : IsPushout pb qa qb pb')
    {M : ModuleCat.{u} B} {P Q : ModuleCat.{u} A'} {N' : ModuleCat.{u} B'}
    {u : (ModuleCat.restrictScalars pb.hom).obj M ⟶ (ModuleCat.restrictScalars qa.hom).obj P}
    (hu : IsIso (transposeExtend qa u))
    {v : M ⟶ (ModuleCat.restrictScalars qb.hom).obj N'} (hv : IsIso (transposeExtend qb v))
    (e : Q ≅ (ModuleCat.restrictScalars pb'.hom).obj N') (σ : P ⟶ Q)
    (htri : ∀ x : M, e.hom (σ (u x)) = v x) : IsIso σ := by
  algebraize [pb.hom, qa.hom, qb.hom, pb'.hom, qb.hom.comp pb.hom]
  have hsc : IsScalarTower (A : Type u) (A' : Type u) (B' : Type u) :=
    .of_algebraMap_eq' <| congr($(hsq.1.1).hom)
  have hpo : Algebra.IsPushout (A : Type u) (B : Type u) (A' : Type u) (B' : Type u) :=
    CommRingCat.isPushout_iff_isPushout.mp hsq
  let iAM : Module (A : Type u) (M : Type u) := Module.compHom _ pb.hom
  let iAP : Module (A : Type u) (P : Type u) := Module.compHom _ qa.hom
  let iBN : Module (B : Type u) (N' : Type u) := Module.compHom _ qb.hom
  let iA'N : Module (A' : Type u) (N' : Type u) := Module.compHom _ pb'.hom
  let iAN : Module (A : Type u) (N' : Type u) := Module.compHom _ (qb.hom.comp pb.hom)
  have t1 : IsScalarTower (A : Type u) (B : Type u) (M : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  have t2 : IsScalarTower (A : Type u) (A' : Type u) (P : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  have t3 : IsScalarTower (A : Type u) (B : Type u) (N' : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  have t4 : IsScalarTower (B : Type u) (B' : Type u) (N' : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  have t5 : IsScalarTower (A' : Type u) (B' : Type u) (N' : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  have t6 : IsScalarTower (A : Type u) (A' : Type u) (N' : Type u) :=
    .of_algebraMap_smul fun r x => congrArg (· • x) (congr($(hsq.1.1).hom r)).symm
  let u' : (M : Type u) →ₗ[(A : Type u)] (P : Type u) := u.hom
  let v' : (M : Type u) →ₗ[(B : Type u)] (N' : Type u) := v.hom
  let σ' : (P : Type u) →ₗ[(A' : Type u)] (N' : Type u) := (σ ≫ e.hom).hom
  have hbu : IsBaseChange (A' : Type u) u' :=
    IsBaseChange.of_equiv (asIso (transposeExtend qa u)).toLinearEquiv fun m =>
      transposeExtend_one_tmul qa u m
  have hbv : IsBaseChange (B' : Type u) v' :=
    IsBaseChange.of_equiv (asIso (transposeExtend qb v)).toLinearEquiv fun m =>
      transposeExtend_one_tmul qb v m
  have hbij : Function.Bijective σ' :=
    bijective_of_isBaseChange hbu (isBaseChange_restrictScalars hbv) σ' htri
  have h1 : IsIso (σ ≫ e.hom) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hbij
  exact IsIso.of_isIso_comp_right σ e.hom

end Stacks.AlgebraicGeometry.AffineBaseChangeIso

end
