module

public import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullback

/-!
# Functoriality of pullback on `K₀(Vect(-))`

The pullback ring maps `f^* : K₀(Vect(X)) → K₀(Vect(Y))` of
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom` form a contravariant functor:
`(𝟙 X)^* = id` and `(f ≫ g)^* = f^* ∘ g^*`.

## Main results

* `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom_id`: `(𝟙 X)^* = id`.
* `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom_comp`: `(f ≫ g)^* = f^* ∘ g^*`.
* `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom_comp_apply`: the same, on elements.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.FiniteLocallyFree

universe u

namespace AlgebraicGeometry.VectorBundleKZero

variable {X Y Z : Scheme.{u}}

/-- **Pullback along the identity is the identity on `K₀(Vect(X))`.** -/
theorem pullbackRingHom_id (X : Scheme.{u}) :
    pullbackRingHom (𝟙 X) = RingHom.id (VectorBundleKZero X) := by
  refine RingHom.toAddMonoidHom_injective (addHom_ext fun M hM => ?_)
  change pullbackRingHom (𝟙 X) (classOf X M) = classOf X M
  rw [pullbackRingHom_classOf _ M hM]
  exact classOf_eq_of_iso ((Scheme.Modules.pullbackId X).app M)
    (isFiniteLocallyFree_pullback _ M hM)

/-- **Pullback on `K₀(Vect(-))` is contravariantly functorial**: `(f ≫ g)^* = f^* ∘ g^*`. -/
theorem pullbackRingHom_comp (f : Z ⟶ Y) (g : Y ⟶ X) :
    pullbackRingHom (f ≫ g) = (pullbackRingHom f).comp (pullbackRingHom g) := by
  refine RingHom.toAddMonoidHom_injective (addHom_ext fun M hM => ?_)
  change pullbackRingHom (f ≫ g) (classOf X M) =
    pullbackRingHom f (pullbackRingHom g (classOf X M))
  rw [pullbackRingHom_classOf _ M hM, pullbackRingHom_classOf _ M hM,
    pullbackRingHom_classOf _ _ (isFiniteLocallyFree_pullback g M hM)]
  exact (classOf_eq_of_iso ((Scheme.Modules.pullbackComp f g).app M)
    (isFiniteLocallyFree_pullback f _ (isFiniteLocallyFree_pullback g M hM))).symm

/-- **`(f ≫ g)^* a = f^*(g^* a)`** in `K₀(Vect(-))`. -/
theorem pullbackRingHom_comp_apply (f : Z ⟶ Y) (g : Y ⟶ X) (a : VectorBundleKZero X) :
    pullbackRingHom (f ≫ g) a = pullbackRingHom f (pullbackRingHom g a) :=
  DFunLike.congr_fun (pullbackRingHom_comp f g) a

end AlgebraicGeometry.VectorBundleKZero

end
