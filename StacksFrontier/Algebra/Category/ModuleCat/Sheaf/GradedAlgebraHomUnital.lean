module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge

/-!
# Homomorphisms of sheaves of graded algebras: unitality of isomorphisms, and direct images

A homomorphism of sheaves of graded algebras (`SheafOfModules.GradedAlgebra.Hom`) need not
preserve the distinguished unit.  This file records that one which is an isomorphism in degree
zero does: the image of the unit is a left identity for the image of every section, hence for
the unit of the target, and a right identity times the unit is itself.  It also records the
direct image of a homomorphism along a continuous functor of sites.

## Main definitions

* `SheafOfModules.GradedAlgebra.Hom.pushforward`: the direct image of a homomorphism along a
  continuous functor and a morphism of sheaves of rings.
* `SheafOfModules.GradedAlgebra.UnitalHom.ofHomOfIsIso`: a homomorphism invertible in degree
  zero, as a unital homomorphism.

## Main results

* `SheafOfModules.GradedAlgebra.Hom.map_one_of_isIso`: a homomorphism invertible in degree zero
  preserves the unit.
-/

@[expose] public section

open CategoryTheory

universe t a v u v₁ u₁ v₂ u₂

namespace SheafOfModules.GradedAlgebra

section Unital

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}

/-- **A homomorphism of sheaves of graded algebras which is an isomorphism in degree zero
preserves the unit.** -/
theorem Hom.map_one_of_isIso (φ : Hom A B) [IsIso (φ.app 0)] (U : Cᵒᵖ) :
    (φ.app 0).val.app U (A.one.eval U) = B.one.eval U := by
  set x := (inv (φ.app 0)).val.app U (B.one.eval U)
  have hx : (φ.app 0).val.app U x = B.one.eval U :=
    congrArg (fun g : B.piece 0 ⟶ B.piece 0 => g.val.app U (B.one.eval U))
      (IsIso.inv_hom_id (φ.app 0))
  have h1 : (φ.app (0 + 0)).val.app U ((A.mul 0 0).app U (A.one.eval U) x) =
      (B.mul 0 0).app U ((φ.app 0).val.app U (A.one.eval U)) ((φ.app 0).val.app U x) :=
    φ.map_mul 0 0 U _ _
  have h2 : (A.mul 0 0).app U (A.one.eval U) x = x := eq_of_heq (A.one_mul 0 U x)
  have h3 : (B.mul 0 0).app U ((φ.app 0).val.app U (A.one.eval U)) (B.one.eval U) =
      (φ.app 0).val.app U (A.one.eval U) := eq_of_heq (B.mul_one 0 U _)
  rw [h2, hx, h3] at h1
  exact (h1.symm.trans hx)

/-- A homomorphism of sheaves of graded algebras which is an isomorphism in degree zero, as a
unital homomorphism. -/
def UnitalHom.ofHomOfIsIso (φ : Hom A B) [IsIso (φ.app 0)] : UnitalHom A B where
  app := φ.app
  map_mul := φ.map_mul
  map_one := φ.map_one_of_isIso

/-- In each degree `n`, the unital homomorphism `UnitalHom.ofHomOfIsIso φ` is `φ.app n`. -/
@[simp] theorem UnitalHom.ofHomOfIsIso_app (φ : Hom A B) [IsIso (φ.app 0)] (n : ℤ) :
    (UnitalHom.ofHomOfIsIso φ).app n = φ.app n := rfl

end Unital

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {G : C ⥤ D}
  [G.IsContinuous J K] {S : Sheaf J RingCat.{t}} {R : Sheaf K RingCat.{t}}
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{t} J K).obj R)

/-- **The direct image of a homomorphism of sheaves of graded algebras** along a continuous
functor and a morphism of sheaves of rings: degreewise the direct image of sheaves of modules. -/
noncomputable def Hom.pushforward {A B : GradedAlgebra.{t, a} R} (g : Hom A B) :
    Hom (GradedAlgebra.pushforward φ A) (GradedAlgebra.pushforward φ B) where
  app n := (SheafOfModules.pushforward.{a} φ).map (g.app n)
  map_mul i j U x y := g.map_mul i j (G.op.obj U) x y

/-- In each degree `n`, the direct image `g.pushforward φ` is the direct image of `g.app n` as a
morphism of sheaves of modules. -/
@[simp] theorem Hom.pushforward_app {A B : GradedAlgebra.{t, a} R} (g : Hom A B) (n : ℤ) :
    (g.pushforward φ).app n = (SheafOfModules.pushforward.{a} φ).map (g.app n) := rfl

/-- **The direct image of an isomorphism of sheaves of graded algebras.** -/
noncomputable def Iso.pushforward {A B : GradedAlgebra.{t, a} R} (e : A ≅ B) :
    GradedAlgebra.pushforward φ A ≅ GradedAlgebra.pushforward φ B where
  hom := Hom.pushforward φ e.hom
  inv := Hom.pushforward φ e.inv
  hom_inv_id := Hom.ext fun n => by
    have h : e.hom.app n ≫ e.inv.app n = 𝟙 _ := congrArg (fun k => Hom.app k n) e.hom_inv_id
    exact ((SheafOfModules.pushforward.{a} φ).map_comp (e.hom.app n) (e.inv.app n)).symm.trans
      ((congrArg (SheafOfModules.pushforward.{a} φ).map h).trans
        ((SheafOfModules.pushforward.{a} φ).map_id _))
  inv_hom_id := Hom.ext fun n => by
    have h : e.inv.app n ≫ e.hom.app n = 𝟙 _ := congrArg (fun k => Hom.app k n) e.inv_hom_id
    exact ((SheafOfModules.pushforward.{a} φ).map_comp (e.inv.app n) (e.hom.app n)).symm.trans
      ((congrArg (SheafOfModules.pushforward.{a} φ).map h).trans
        ((SheafOfModules.pushforward.{a} φ).map_id _))

end Pushforward

end SheafOfModules.GradedAlgebra
