module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The Eilenberg–Watts comparison map

Let `R` be a commutative ring and let `F : ModuleCat R ⥤ ModuleCat R` be an `R`-linear functor.
There is a canonical `R`-linear map

  `F(R) ⊗[R] M ⟶ F(M)`,

natural in `M`, sending `x ⊗ m` to `F(r ↦ r • m)(x)`. This file constructs it and proves it is an
isomorphism at `M = R`.

## Main definitions

* `Stacks.EilenbergWatts.wattsMap`: the comparison map, as a morphism of `ModuleCat R`.

## Main results

* `Stacks.EilenbergWatts.wattsMap_naturality`: the comparison map is natural in `M`.
* `Stacks.EilenbergWatts.wattsMap_unit`: at `M = R` the comparison map is `TensorProduct.rid`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u

namespace Stacks.EilenbergWatts

variable {R : Type u} [CommRing R] (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
  [F.Additive] [F.Linear R]

/-- `F` applied to the morphism `r ↦ r • m`, as a linear map depending linearly on `m`. -/
def wattsBilin (M : ModuleCat.{u} R) :
    M →ₗ[R] F.obj (ModuleCat.of R R) →ₗ[R] F.obj M where
  toFun m := (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))).hom
  map_add' m m' := by
    simp only [LinearMap.toSpanSingleton_add, ModuleCat.ofHom_add, F.map_add,
      ModuleCat.hom_add]
  map_smul' r m := by
    simp only [RingHom.id_apply, LinearMap.toSpanSingleton_smul]
    rw [show ModuleCat.ofHom (r • LinearMap.toSpanSingleton R M m)
        = r • ModuleCat.ofHom (LinearMap.toSpanSingleton R M m) from rfl,
      Functor.map_smul, ModuleCat.hom_smul]

/-- `wattsBilin F M m` is `F` applied to `r ↦ r • m`. -/
@[simp]
theorem wattsBilin_apply (M : ModuleCat.{u} R) (m : M) (x : F.obj (ModuleCat.of R R)) :
    wattsBilin F M m x = (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))).hom x :=
  rfl

/-- **The Eilenberg–Watts comparison map.** The canonical `R`-linear map
`F(R) ⊗[R] M ⟶ F(M)` sending `x ⊗ m` to `F(r ↦ r • m)(x)`. -/
def wattsMap (M : ModuleCat.{u} R) :
    ModuleCat.of R (F.obj (ModuleCat.of R R) ⊗[R] M) ⟶ F.obj M :=
  ModuleCat.ofHom (TensorProduct.lift (wattsBilin F M).flip)

/-- The comparison map sends `x ⊗ m` to `F(r ↦ r • m)(x)`. -/
@[simp]
theorem wattsMap_tmul (M : ModuleCat.{u} R) (x : F.obj (ModuleCat.of R R)) (m : M) :
    (wattsMap F M).hom (x ⊗ₜ[R] m) =
      (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))).hom x :=
  rfl

/-- **Naturality of the comparison map**: `F(R) ⊗ f` followed by the comparison map at `N` is the
comparison map at `M` followed by `F(f)`. -/
theorem wattsMap_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ModuleCat.ofHom (TensorProduct.map LinearMap.id f.hom) ≫ wattsMap F N =
      wattsMap F M ≫ F.map f := by
  refine ModuleCat.hom_ext (TensorProduct.ext' fun x m => ?_)
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton R N (f.hom m)) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R M m) ≫ f :=
    ModuleCat.hom_ext (LinearMap.ext fun r => by simp [LinearMap.toSpanSingleton_apply])
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rw [wattsMap_tmul, wattsMap_tmul, h, F.map_comp]
  rfl

/-- The map `s ↦ s • r` of `R` is multiplication by `r`. -/
theorem toSpanSingleton_self (r : R) :
    LinearMap.toSpanSingleton R R r = r • LinearMap.id :=
  LinearMap.ext fun s => by simp [LinearMap.toSpanSingleton_apply, mul_comm]

/-- At `M = R` the comparison map is the right unitor `F(R) ⊗[R] R ≅ F(R)`. -/
theorem wattsMap_unit :
    wattsMap F (ModuleCat.of R R) =
      ModuleCat.ofHom (TensorProduct.rid R (F.obj (ModuleCat.of R R))).toLinearMap := by
  refine ModuleCat.hom_ext (TensorProduct.ext' fun x r => ?_)
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton R (ModuleCat.of R R) r) =
      r • 𝟙 (ModuleCat.of R R) := by
    rw [toSpanSingleton_self]
    rfl
  rw [wattsMap_tmul, h, Functor.map_smul, F.map_id]
  rfl

end Stacks.EilenbergWatts

end
