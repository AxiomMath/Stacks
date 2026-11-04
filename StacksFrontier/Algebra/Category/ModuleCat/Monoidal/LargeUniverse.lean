module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

/-!
# Tensor product of modules whose carrier universe exceeds the ring's

Mathlib equips `ModuleCat.{v} R` with a monoidal structure only when `v` is the universe of
`R` itself, with tensor unit `R`. The tensor product `M ⊗[R] N` of two `R`-modules in
`Type (max u v)` is again an `R`-module in `Type (max u v)`, and `ULift.{v} R` is a unit for it.

This file installs that structure. For `R : Type u` and any `v`, `ModuleCat.{max u v} R` is a
symmetric monoidal category, monoidally preadditive, and monoidal closed, with

* `M ⊗ N = ModuleCat.of R (M ⊗[R] N)`, the ordinary tensor product of modules, and
* `𝟙_ = ModuleCat.of R (ULift.{v} R)`, the ring lifted into the module universe.

The instances have priority 100.

## Main definitions

* `ModuleCat.liftedModuleMonoidalStruct`: the tensor product, unit, associator and unitors.
* `ModuleCat.liftedModuleMonoidal`: the coherence axioms, so `ModuleCat.{max u v} R` is monoidal.
* `ModuleCat.liftedBraiding`: the symmetry `M ⊗ N ≅ N ⊗ M` of the tensor product.
* `ModuleCat.liftedModuleSymmetric`: the braiding axioms, so `ModuleCat.{max u v} R` is symmetric
  monoidal.
* `ModuleCat.liftedModuleMonoidalPreadditive`: tensoring is additive in each variable.
* `ModuleCat.liftedModuleMonoidalClosedHomEquiv`: the tensor-hom adjunction bijection.
* `ModuleCat.liftedModuleMonoidalClosed`: `ModuleCat.{max u v} R` is monoidal closed, hence
  tensoring preserves colimits.
* `ModuleCat.moduleTensorLarge`: the tensor product as a bifunctor.
-/

open CategoryTheory MonoidalCategory

universe u v

namespace ModuleCat

open scoped TensorProduct

/-- The tensor product, unit, associator and unitors on `ModuleCat.{max u v} R` for
`R : Type u`. The tensor product is the ordinary tensor product of `R`-modules and the unit is
`ULift.{v} R`. -/
instance (priority := 100) liftedModuleMonoidalStruct {R : Type u} [CommRing R] :
    MonoidalCategoryStruct (ModuleCat.{max v u} R) where
  tensorObj M N := ModuleCat.of R (M ⊗[R] N)
  whiskerLeft M _ _ f := ModuleCat.ofHom <| f.hom.lTensor M
  whiskerRight f M := ModuleCat.ofHom <| f.hom.rTensor M
  tensorHom f g := ModuleCat.ofHom <| TensorProduct.map f.hom g.hom
  tensorUnit := ModuleCat.of R (ULift.{v} R)
  associator M N K := (TensorProduct.assoc R M N K).toModuleIso
  leftUnitor M := ((TensorProduct.congr ULift.moduleEquiv (LinearEquiv.refl R M)).trans
    (TensorProduct.lid R M)).toModuleIso
  rightUnitor M := ((TensorProduct.congr (LinearEquiv.refl R M) ULift.moduleEquiv).trans
    (TensorProduct.rid R M)).toModuleIso

/-- `ModuleCat.{max u v} R` is a monoidal category under the ordinary tensor product of
`R`-modules. -/
instance (priority := 100) liftedModuleMonoidal {R : Type u} [CommRing R] :
    MonoidalCategory (ModuleCat.{max v u} R) :=
  MonoidalCategory.ofTensorHom
  (id_tensorHom_id := by
    intros
    ext : 1
    exact TensorProduct.ext rfl)
  (tensorHom_comp_tensorHom := by
    intros
    ext : 1
    exact TensorProduct.ext rfl)
  (associator_naturality := by
    intros
    ext : 1
    exact TensorProduct.ext_threefold fun _ _ _ ↦ rfl)
  (leftUnitor_naturality := by
    intro M N f
    ext : 1
    refine TensorProduct.ext (LinearMap.ext₂ fun x y ↦ ?_)
    exact (map_smul f.hom (ULift.down x) y).symm)
  (rightUnitor_naturality := by
    intro M N f
    ext : 1
    refine TensorProduct.ext (LinearMap.ext₂ fun x y ↦ ?_)
    exact (map_smul f.hom (ULift.down y) x).symm)
  (pentagon := by
    intros
    ext : 1
    exact TensorProduct.ext_fourfold fun _ _ _ _ ↦ rfl)
  (triangle := by
    intros
    ext : 1
    refine TensorProduct.ext_threefold fun x y z ↦ ?_
    change x ⊗ₜ[R] ((ULift.down y) • z) = ((ULift.down y) • x) ⊗ₜ[R] z
    exact TensorProduct.tmul_smul _ _ _)

/-- The symmetry `M ⊗ N ≅ N ⊗ M` of the tensor product of `R`-modules, for modules in a
universe above the ring's, given by `TensorProduct.comm`. -/
def liftedBraiding {R : Type u} [CommRing R] (M N : ModuleCat.{max v u} R) :
    M ⊗ N ≅ N ⊗ M :=
  (TensorProduct.comm R M N).toModuleIso

/-- `ModuleCat.{max u v} R` is symmetric monoidal, with braiding `liftedBraiding`. -/
instance (priority := 100) liftedModuleSymmetric {R : Type u} [CommRing R] :
    SymmetricCategory (ModuleCat.{max v u} R) where
  braiding := liftedBraiding
  braiding_naturality_left := by
    intros
    ext : 1
    exact TensorProduct.ext' fun _ _ ↦ rfl
  braiding_naturality_right := by
    intros
    ext : 1
    exact TensorProduct.ext' fun _ _ ↦ rfl
  hexagon_forward := by
    intros
    ext : 1
    exact TensorProduct.ext_threefold fun _ _ _ ↦ rfl
  hexagon_reverse X Y Z := by
    apply (cancel_epi (α_ X Y Z).hom).1
    ext : 1
    exact TensorProduct.ext_threefold fun _ _ _ ↦ rfl
  symmetry := by
    intros
    ext : 1
    exact TensorProduct.ext' fun _ _ ↦ rfl

/-- Tensoring is additive in each variable: it sends zero morphisms to zero and preserves sums of
morphisms. -/
instance (priority := 100) liftedModuleMonoidalPreadditive
    {R : Type u} [CommRing R] :
    MonoidalPreadditive (ModuleCat.{max v u} R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y Z
    ext : 1
    refine TensorProduct.ext (LinearMap.ext₂ fun x y ↦ ?_)
    change x ⊗ₜ[R] (0 : Z) = 0
    simp
  · intro X Y Z
    ext : 1
    refine TensorProduct.ext (LinearMap.ext₂ fun x y ↦ ?_)
    change (0 : Z) ⊗ₜ[R] y = 0
    simp
  · intro X Y Z f g
    ext : 1
    refine TensorProduct.ext (LinearMap.ext₂ fun x y ↦ ?_)
    change x ⊗ₜ[R] ((f + g) y) = x ⊗ₜ[R] f y + x ⊗ₜ[R] g y
    simp [TensorProduct.tmul_add]
  · intro X Y Z f g
    ext : 1
    refine TensorProduct.ext (LinearMap.ext₂ fun x y ↦ ?_)
    change ((f + g) x) ⊗ₜ[R] y = f x ⊗ₜ[R] y + g x ⊗ₜ[R] y
    simp [TensorProduct.add_tmul]

/-- The tensor-hom adjunction for modules in a universe larger than the ring's: a map out of
`M ⊗ N` is a map out of `N` into the internal hom `Hom(M, -)`. -/
def liftedModuleMonoidalClosedHomEquiv {R : Type u} [CommRing R]
    (M N P : ModuleCat.{max u v} R) :
    ((MonoidalCategory.tensorLeft M).obj N ⟶ P) ≃
      (N ⟶ ((linearCoyoneda R (ModuleCat.{max u v} R)).obj (Opposite.op M)).obj P) where
  toFun f := ofHom₂ (TensorProduct.curry f.hom).flip
  invFun f := ofHom (TensorProduct.lift f.hom₂.flip)
  left_inv f := by
    ext : 1
    exact TensorProduct.ext' fun _ _ ↦ rfl
  right_inv f := by
    ext n m
    rfl

/-- `ModuleCat.{max u v} R` is monoidal closed, with internal hom the `R`-linear coyoneda
functor. -/
instance (priority := 100) liftedModuleMonoidalClosed {R : Type u} [CommRing R] :
    MonoidalClosed (ModuleCat.{max u v} R) where
  closed M :=
    { rightAdj := (linearCoyoneda R (ModuleCat.{max u v} R)).obj (Opposite.op M)
      adj := Adjunction.mkOfHomEquiv
        { homEquiv := fun N P ↦ liftedModuleMonoidalClosedHomEquiv M N P
          homEquiv_naturality_left_symm := by
            intros
            ext : 1
            exact TensorProduct.ext' fun _ _ ↦ rfl } }

/-- The tensor product of `R`-modules as a bifunctor on `ModuleCat.{max u v} R`: its value on
objects is `M ⊗[R] N` and on morphisms the left and right tensorings. -/
abbrev moduleTensorLarge (R : Type u) [CommRing R] :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  curriedTensor (ModuleCat.{max u v} R)

end ModuleCat

end
