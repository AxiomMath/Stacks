module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Extension of scalars from the integers

Let `R` be a ring, not necessarily commutative. Every abelian group `M` gives the left
`R`-module `R ⊗_ℤ M`, and `M ↦ R ⊗_ℤ M` is left adjoint to the forgetful functor from
`R`-modules to abelian groups: an `R`-linear map `R ⊗_ℤ M ⟶ N` is the same as an additive map
`M ⟶ N`. Tensoring with `R` over `ℤ` preserves the injectivity of `M ⟶ M'` as soon as the
cokernel is torsion free, the cokernel being then flat over `ℤ`.

## Main definitions

* `ModuleCat.extendScalarsFromInt R`: the functor `M ↦ R ⊗_ℤ M` from abelian groups to
  `R`-modules.
* `ModuleCat.extendScalarsFromIntAdj R`: it is left adjoint to
  `forget₂ (ModuleCat R) AddCommGrpCat`.

## Main results

* `ModuleCat.mono_extendScalarsFromInt_map`: `R ⊗_ℤ -` preserves the monomorphism of an exact
  sequence `0 ⟶ M ⟶ M' ⟶ M''` with `M''` torsion free.

## Implementation notes

Mathlib's `ModuleCat.extendScalars` needs commutative rings. Over `ℤ` no relative tensor product
is needed: `R ⊗[ℤ] M` is a left `R`-module through the left factor, and its universal property is
`TensorProduct.AlgebraTensorModule.lift`, which allows the left ring to be noncommutative.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

universe v r

namespace ModuleCat

variable (R : Type r) [Ring R]

/-- **Extension of scalars from `ℤ` to a ring `R`**: the `R`-module `R ⊗_ℤ M` of an abelian group
`M`. -/
def extendScalarsFromInt : AddCommGrpCat.{max r v} ⥤ ModuleCat.{max r v} R where
  obj M := ModuleCat.of R (R ⊗[ℤ] M)
  map f := ModuleCat.ofHom
    (TensorProduct.AlgebraTensorModule.lTensor R R f.hom.toIntLinearMap)
  map_id _ := ModuleCat.hom_ext TensorProduct.AlgebraTensorModule.lTensor_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r m
    rfl

/-- `R`-linear maps out of `R ⊗_ℤ M` are additive maps out of `M`. -/
def extendScalarsFromIntHomEquiv (M : AddCommGrpCat.{max r v}) (N : ModuleCat.{max r v} R) :
    ((extendScalarsFromInt.{v} R).obj M ⟶ N) ≃
      (M ⟶ (forget₂ (ModuleCat R) AddCommGrpCat).obj N) :=
  (ModuleCat.homEquiv).trans
    ((TensorProduct.AlgebraTensorModule.lift.equiv ℤ R ℤ R M N).toEquiv.symm.trans
      ((LinearMap.ringLmapEquivSelf R ℤ (M →ₗ[ℤ] N)).toEquiv.trans
        { toFun := fun f => AddCommGrpCat.ofHom f.toAddMonoidHom
          invFun := fun f => f.hom.toIntLinearMap
          left_inv _ := rfl
          right_inv _ := rfl }))

/-- **Extension of scalars from `ℤ` is left adjoint to the forgetful functor** from `R`-modules to
abelian groups. -/
def extendScalarsFromIntAdj :
    extendScalarsFromInt.{v} R ⊣ forget₂ (ModuleCat.{max r v} R) AddCommGrpCat :=
  Adjunction.mkOfHomEquiv {
    homEquiv := extendScalarsFromIntHomEquiv R
    homEquiv_naturality_left_symm := by
      intro M M' N f g
      apply ModuleCat.hom_ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro r m
      rfl
    homEquiv_naturality_right := by
      intro M N N' f g
      rfl }

/-- Extension of scalars from `ℤ` to `R` is an additive functor. -/
instance : (extendScalarsFromInt.{v} R).Additive :=
  (extendScalarsFromIntAdj R).left_adjoint_additive

/-- **`R ⊗_ℤ -` preserves the monomorphism of an exact sequence `0 ⟶ M ⟶ M' ⟶ M''` whose last
term is torsion free**. -/
theorem mono_extendScalarsFromInt_map (S : ShortComplex AddCommGrpCat.{max r v})
    (hS : S.Exact) [Mono S.f] [Module.IsTorsionFree ℤ S.X₃] :
    Mono ((extendScalarsFromInt.{v} R).map S.f) :=
  (ModuleCat.mono_iff_injective _).2 <|
    LinearMap.lTensor_injective_of_exact_of_flat S.g.hom.toIntLinearMap.rangeRestrict
      S.g.hom.toIntLinearMap.surjective_rangeRestrict S.f.hom.toIntLinearMap
      ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)
      (fun x ↦ by
        show (S.g.hom.toIntLinearMap.rangeRestrict x = 0) ↔ x ∈ Set.range S.f.hom
        rw [Subtype.ext_iff]
        exact (S.ab_exact_iff_function_exact.mp hS) x) R

end ModuleCat

end
