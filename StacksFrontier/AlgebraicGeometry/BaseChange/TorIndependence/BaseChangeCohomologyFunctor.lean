module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMapTransport
public import StacksFrontier.Homology.Tor.BaseChangeCohomologyDevissage

/-!
# The cohomology of a derived base change, as a functor

`RingTheory.TorIndependence.baseChangeCohomology` assigns to an object `K` of `D(A)` the
`A ⊗_R R'`-module `H^n(K ⊗ᴸ_R R')`, and `RingTheory.TorIndependence.baseChangeCohomologyFunctor n`
makes it a functor `D(A) ⥤ ModuleCat (A ⊗_R R')`. This file describes the action of that functor
on a morphism as `H^n` of its derived base change through `derivedBaseChangeFunctor`.

## Main definitions

* `RingTheory.TorIndependence.tensorLinearMapOfIncludes`: an additive map between
  `A ⊗_R S`-modules is linear as soon as it is linear for the two tensor inclusions.
* `RingTheory.TorIndependence.baseChangeCohomologyMap`: the `A ⊗_R R'`-linear map induced by a
  morphism of `D(A)`, written through `derivedBaseChangeFunctor`.

## Main results

* `RingTheory.TorIndependence.baseChangeCohomologyMap_apply`: the underlying function is the
  cohomology of the derived base change of the morphism.
* `RingTheory.TorIndependence.baseChangeCohomologyFunctor_map`: the functor
  `RingTheory.TorIndependence.baseChangeCohomologyFunctor` acts on morphisms by
  `baseChangeCohomologyMap`.
* `RingTheory.TorIndependence.derivedBaseChangeHomology_smul_id_comm`: scalar multiplication on
  `K` commutes with every morphism of `D(A)` after derived base change and cohomology.

Every statement takes `[HasDerivedCategory.{w} (ModuleCat.{u} ·)]` for each of the three rings as
a binder, as in `RingTheory.TorIndependence.baseChangeCohomology`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u w

namespace RingTheory.TorIndependence

/-! ### Linearity over a tensor product of rings -/

section Algebraic

variable {R A S : Type u} [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]

/-- In `A ⊗_R S` a pure tensor is the product of the two inclusions. -/
theorem tmul_eq_includeLeft_mul_includeRight (a : A) (s : S) :
    (a ⊗ₜ[R] s : A ⊗[R] S) =
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] S) *
        Algebra.TensorProduct.includeRight s := by
  change a ⊗ₜ[R] s = (a ⊗ₜ[R] (1 : S)) * ((1 : A) ⊗ₜ[R] s)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- **An additive map of `A ⊗_R S`-modules linear for both tensor inclusions is linear.** -/
def tensorLinearMapOfIncludes {M N : Type u} [AddCommGroup M] [Module (A ⊗[R] S) M]
    [AddCommGroup N] [Module (A ⊗[R] S) N] (g : M →+ N)
    (hL : ∀ (a : A) (m : M),
      g ((Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] S) • m) =
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] S) • g m)
    (hR : ∀ (s : S) (m : M),
      g ((Algebra.TensorProduct.includeRight s : A ⊗[R] S) • m) =
        (Algebra.TensorProduct.includeRight s : A ⊗[R] S) • g m) :
    M →ₗ[A ⊗[R] S] N where
  toFun := g
  map_add' := g.map_add
  map_smul' t m := by
    simp only [RingHom.id_apply]
    induction t using TensorProduct.induction_on with
    | zero => rw [zero_smul, zero_smul, map_zero]
    | tmul a s =>
      rw [tmul_eq_includeLeft_mul_includeRight, mul_smul, hL, hR, mul_smul]
    | add x y hx hy => rw [add_smul, add_smul, map_add, hx, hy]

end Algebraic

/-! ### The functor -/

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-- **Scalar multiplication on `K` commutes with any morphism of `D(A)`, after derived base
change and cohomology.** -/
theorem derivedBaseChangeHomology_smul_id_comm (n : ℤ)
    {K L : DerivedCategory (ModuleCat.{u} A)} (φ : K ⟶ L) (a : A)
    (x : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    ((derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map φ).hom
        (((derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map (a • 𝟙 K)).hom x) =
      ((derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map (a • 𝟙 L)).hom
        (((derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map φ).hom x) := by
  have hcomm : (a • 𝟙 K) ≫ φ = φ ≫ (a • 𝟙 L) := by
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  have h := congrArg (fun ψ => (derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map ψ) hcomm
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  exact congrArg (fun ξ => ModuleCat.Hom.hom ξ x) h

/-- **The map induced on the cohomology of a derived base change by a morphism of `D(A)`**, as an
`A ⊗_R R'`-linear map whose underlying function is `H^n` of the derived base change of the
morphism. -/
def baseChangeCohomologyMap (n : ℤ) {K L : DerivedCategory (ModuleCat.{u} A)} (φ : K ⟶ L) :
    baseChangeCohomology (R := R) (R' := R') K n ⟶
      baseChangeCohomology (R := R) (R' := R') L n :=
  ModuleCat.ofHom
    (X := (baseChangeCohomology (R := R) (R' := R') K n : Type u))
    (Y := (baseChangeCohomology (R := R) (R' := R') L n : Type u))
    (tensorLinearMapOfIncludes (R := R) (A := A) (S := R')
      ((derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map φ).hom.toAddMonoidHom
      (fun a m =>
        ((congrArg _ (baseChangeCohomology_includeLeft_smul
            (R := R) (R' := R') K n a m)).trans
          (derivedBaseChangeHomology_smul_id_comm (R := R) (R' := R') n φ a m)).trans
          (baseChangeCohomology_includeLeft_smul (R := R) (R' := R') L n a _).symm)
      (fun r m =>
        ((congrArg _ (baseChangeCohomology_includeRight_smul
            (R := R) (R' := R') K n r m)).trans
          (map_smul ((derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map φ).hom r
              (show baseChangeCohomologyOverBase (R := R) (R' := R') K n from m))).trans
          (baseChangeCohomology_includeRight_smul (R := R) (R' := R') L n r _).symm))

/-- The underlying function of the induced map is `H^n` of the derived base change of the
morphism. -/
theorem baseChangeCohomologyMap_apply (n : ℤ) {K L : DerivedCategory (ModuleCat.{u} A)}
    (φ : K ⟶ L) (m : baseChangeCohomology (R := R) (R' := R') K n) :
    (baseChangeCohomologyMap (R := R) (R' := R') n φ).hom m =
      ((derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map φ).hom m :=
  rfl

/-- The cohomology functor of a derived base change on objects. -/
@[simp]
theorem baseChangeCohomologyFunctor_obj (n : ℤ) (K : DerivedCategory (ModuleCat.{u} A)) :
    (baseChangeCohomologyFunctor (R := R) (R' := R') n).obj K =
      baseChangeCohomology (R := R) (R' := R') K n :=
  rfl

/-- **The cohomology functor of a derived base change acts on a morphism by `H^n` of its derived
base change**, read through `derivedBaseChangeFunctor`. -/
@[simp]
theorem baseChangeCohomologyFunctor_map (n : ℤ) {K L : DerivedCategory (ModuleCat.{u} A)}
    (φ : K ⟶ L) :
    (baseChangeCohomologyFunctor (R := R) (R' := R') n).map φ =
      baseChangeCohomologyMap (R := R) (R' := R') n φ :=
  rfl

end RingTheory.TorIndependence

end
