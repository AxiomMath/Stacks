module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDescent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful

/-!
# Descent of a homomorphism of sheaves of graded algebras along a quotient of the ring sheaf

Let `α : R ⟶ R'` be a locally surjective morphism of sheaves of rings and let `A` and `B` be
sheaves of graded `R`-algebras every homogeneous piece of which is annihilated by the kernel of
`α`, so that both descend to sheaves of graded `R'`-algebras by
`SheafOfModules.GradedAlgebra.descend`. This file descends homomorphisms as well: a unital
homomorphism `A ⟶ B` of sheaves of graded `R`-algebras is a unital homomorphism of the descended
sheaves of graded `R'`-algebras, with the same components on local sections, and it is an
isomorphism in a degree when the original is.

## Main definitions

* `Stacks.SheafOfModules.ChangeOfRings.liftedSheafMap`: a morphism of sheaves of `R`-modules
  between two annihilated sheaves, read as a morphism of the descended sheaves of `R'`-modules.
* `SheafOfModules.GradedAlgebra.UnitalHom.descend`: the descended unital homomorphism.
* `SheafOfModules.GradedAlgebra.descendIso`: the descended algebras are isomorphic as sheaves of
  graded `R'`-algebras, for a homomorphism which is an isomorphism in every degree.

## Main statements

* `Stacks.SheafOfModules.ChangeOfRings.liftedSheafMap_val_app` and
  `SheafOfModules.GradedAlgebra.UnitalHom.descend_app_val_app`: the descended morphism is the
  original one on local sections.
* `SheafOfModules.GradedAlgebra.UnitalHom.isIso_descend_app`: the descended homomorphism is an
  isomorphism in every degree in which the original one is.

## References

* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u t

namespace Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{t}} (α : R ⟶ R') [Presheaf.IsLocallySurjective J α.hom]
  {G₁ G₂ : SheafOfModules.{t} R}
  (hG₁ : ∀ (X : Cᵒᵖ) (b : R.obj.obj X), b ∈ RingHom.ker (α.hom.app X).hom →
    ∀ m : G₁.val.obj X, b • m = 0)
  (hG₂ : ∀ (X : Cᵒᵖ) (b : R.obj.obj X), b ∈ RingHom.ker (α.hom.app X).hom →
    ∀ m : G₂.val.obj X, b • m = 0)

/-- A morphism between two sheaves of `R`-modules annihilated by the kernel of `α`, read as a
morphism of the descended sheaves of `R'`-modules. -/
def liftedSheafMap (f : G₁ ⟶ G₂) : liftedSheaf α G₁ hG₁ ⟶ liftedSheaf α G₂ hG₂ :=
  (fullyFaithfulOfIsLocallySurjective.{t} α).preimage
    ((restrictScalarsLiftedSheafIso α G₁ hG₁).hom ≫ f ≫
      (restrictScalarsLiftedSheafIso α G₂ hG₂).inv)

/-- Restriction of scalars takes the lifted morphism back to the conjugate of the original. -/
theorem restrictScalars_map_liftedSheafMap (f : G₁ ⟶ G₂) :
    (SheafOfModules.restrictScalars.{t} α).map (liftedSheafMap α hG₁ hG₂ f) =
      (restrictScalarsLiftedSheafIso α G₁ hG₁).hom ≫ f ≫
        (restrictScalarsLiftedSheafIso α G₂ hG₂).inv :=
  (fullyFaithfulOfIsLocallySurjective.{t} α).map_preimage _

/-- The lifted morphism acts on local sections exactly as the morphism it lifts. -/
theorem liftedSheafMap_val_app (f : G₁ ⟶ G₂) (U : Cᵒᵖ)
    (x : (liftedSheaf α G₁ hG₁).val.obj U) :
    (liftedSheafMap α hG₁ hG₂ f).val.app U x = f.val.app U x :=
  ConcreteCategory.congr_hom
    (congrArg (fun g ↦ (SheafOfModules.Hom.val g).app U)
      (restrictScalars_map_liftedSheafMap α hG₁ hG₂ f)) x

/-- The lifted morphism is an isomorphism when the morphism it lifts is. -/
instance isIso_liftedSheafMap (f : G₁ ⟶ G₂) [IsIso f] :
    IsIso (liftedSheafMap α hG₁ hG₂ f) := by
  have : IsIso ((SheafOfModules.restrictScalars.{t} α).map (liftedSheafMap α hG₁ hG₂ f)) := by
    rw [restrictScalars_map_liftedSheafMap]
    infer_instance
  exact (fullyFaithfulOfIsLocallySurjective.{t} α).isIso_of_isIso_map _

end Stacks.SheafOfModules.ChangeOfRings

namespace SheafOfModules.GradedAlgebra

open Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{t}} (α : R ⟶ R') [Presheaf.IsLocallySurjective J α.hom]
  {A B : GradedAlgebra.{t, t} R}
  (hA : ∀ (n : ℤ) (X : Cᵒᵖ) (b : R.obj.obj X), b ∈ RingHom.ker (α.hom.app X).hom →
    ∀ m : (A.piece n).val.obj X, b • m = 0)
  (hB : ∀ (n : ℤ) (X : Cᵒᵖ) (b : R.obj.obj X), b ∈ RingHom.ker (α.hom.app X).hom →
    ∀ m : (B.piece n).val.obj X, b • m = 0)

/-- The descent of a unital homomorphism of sheaves of graded algebras along a quotient of the
ring sheaf: its components are the components of the given homomorphism, read on the descended
pieces by `Stacks.SheafOfModules.ChangeOfRings.liftedSheafMap`. -/
def UnitalHom.descend (g : UnitalHom A B) :
    UnitalHom (GradedAlgebra.descend α A hA) (GradedAlgebra.descend α B hB) where
  app n := liftedSheafMap α (hA n) (hB n) (g.app n)
  map_mul i j U x y :=
    (liftedSheafMap_val_app α (hA (i + j)) (hB (i + j)) (g.app (i + j)) U
      (((GradedAlgebra.descend α A hA).mul i j).app U x y)).trans <|
    (g.map_mul i j U x y).trans <|
      congrArg₂ (fun a b ↦ ((GradedAlgebra.descend α B hB).mul i j).app U a b)
        (liftedSheafMap_val_app α (hA i) (hB i) (g.app i) U x).symm
        (liftedSheafMap_val_app α (hA j) (hB j) (g.app j) U y).symm
  map_one U :=
    (liftedSheafMap_val_app α (hA 0) (hB 0) (g.app 0) U
      ((GradedAlgebra.descend α A hA).one.eval U)).trans (g.map_one U)

/-- The components of the descended homomorphism are the lifts of the original components. -/
@[simp] theorem UnitalHom.descend_app (g : UnitalHom A B) (n : ℤ) :
    (g.descend α hA hB).app n = liftedSheafMap α (hA n) (hB n) (g.app n) :=
  rfl

/-- The descended homomorphism acts on local sections exactly as the one it descends. -/
theorem UnitalHom.descend_app_val_app (g : UnitalHom A B) (n : ℤ) (U : Cᵒᵖ)
    (x : ((GradedAlgebra.descend α A hA).piece n).val.obj U) :
    ((g.descend α hA hB).app n).val.app U x = (g.app n).val.app U x :=
  liftedSheafMap_val_app α (hA n) (hB n) (g.app n) U x

/-- The descended homomorphism is an isomorphism in every degree in which the original one
is. -/
instance UnitalHom.isIso_descend_app (g : UnitalHom A B) (n : ℤ) [IsIso (g.app n)] :
    IsIso ((g.descend α hA hB).app n) :=
  isIso_liftedSheafMap α (hA n) (hB n) (g.app n)

/-- The two descended algebras are isomorphic as sheaves of graded `R'`-algebras, for a unital
homomorphism between them over `R` which is an isomorphism in every degree. -/
def descendIso (g : UnitalHom A B) [∀ n, IsIso (g.app n)] :
    GradedAlgebra.descend α A hA ≅ GradedAlgebra.descend α B hB where
  hom := (g.descend α hA hB).toHom
  inv := (g.descend α hA hB).inverse.toHom
  hom_inv_id := Hom.ext fun n ↦ by simpa using IsIso.hom_inv_id ((g.descend α hA hB).app n)
  inv_hom_id := Hom.ext fun n ↦ by simpa using IsIso.inv_hom_id ((g.descend α hA hB).app n)

end SheafOfModules.GradedAlgebra

end
