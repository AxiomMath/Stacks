module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import StacksCore.CategoryTheory.FiberedInGroupoids

/-!
# The costructured arrows over an object are fibred in groupoids

Let `F : C ⥤ D` be a functor and `T` an object of `D`.  The projection
`CostructuredArrow F T ⥤ C`, which forgets the structure morphism `F.obj X ⟶ T`, is fibred in
groupoids.  This is the costructured-arrow counterpart of
`CategoryTheory.Functor.IsFiberedInGroupoids.over_forget`, the same statement for a slice
category, and it is proved the same way: a morphism `f : V ⟶ x.left` of `C` lifts to the
costructured arrow `F.obj V ⟶ F.obj x.left ⟶ T` with the morphism
`CategoryTheory.CostructuredArrow.homMk' x f`, and a fill-in in `C` is automatically a morphism
of costructured arrows, uniquely so because the projection is faithful.

The fibres of the projection are discrete: a morphism of costructured arrows over an identity of
`C` is an identity.  So the conclusion is really that the projection is a fibred category, which
is how the source phrases the corresponding statement for a presheaf.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.costructuredArrow_proj`: the projection of the
  costructured arrows of `F` over `T` to `C` is fibred in groupoids.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The projection `CostructuredArrow F T ⥤ C` is fibred in groupoids.

A morphism `f : V ⟶ x.left` of `C` lifts to the costructured arrow `CostructuredArrow.mk` of
`F.map f ≫ x.hom` together with `CategoryTheory.CostructuredArrow.homMk' x f`; a fill-in `h` in
`C` commutes with the structure morphisms because the two morphisms it is required to factor do,
and it is the unique fill-in because a morphism of costructured arrows is determined by its
component in `C`. -/
theorem Functor.IsFiberedInGroupoids.costructuredArrow_proj (F : C ⥤ D) (T : D) :
    (CostructuredArrow.proj F T).IsFiberedInGroupoids := by
  constructor
  · intro V W f x hx
    exact ⟨CostructuredArrow.mk (F.map (f ≫ eqToHom hx.symm) ≫ x.hom),
      CostructuredArrow.homMk' x (f ≫ eqToHom hx.symm),
      IsHomLift.of_fac' (CostructuredArrow.proj F T) f _ rfl hx (by simp)⟩
  · intro x y z φ ψ g hg
    simp only [CostructuredArrow.proj_map] at hg
    have hw : F.map g ≫ y.hom = z.hom := by
      rw [← CostructuredArrow.w φ, ← Category.assoc, ← F.map_comp, hg, CostructuredArrow.w ψ]
    refine ⟨CostructuredArrow.homMk g hw, ⟨by simp, CostructuredArrow.hom_ext _ _ (by simpa)⟩,
      fun χ hχ ↦ CostructuredArrow.hom_ext _ _ ?_⟩
    simpa using hχ.1

end CategoryTheory

end
