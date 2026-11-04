module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Unique
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The free abelian group on a type is the free module on it over the integers

An abelian group is a module over the integers in exactly one way, and an additive map of abelian
groups is automatically linear, so the free abelian group functor `AddCommGrpCat.free` and the
free-module functor `ModuleCat.free (ULift ℤ)` read in abelian groups are two constructions of
the same thing. This file identifies them, by exhibiting the second as a left adjoint of the
forgetful functor to types and appealing to the uniqueness of left adjoints — which makes the
identification natural, rather than a family of isomorphisms of abelian groups.

The point of the identification is that the two constructions have genuinely different carriers:
`AddCommGrpCat.free.obj X` is `FreeAbelianGroup X`, a quotient of a free monoid, whereas
`ModuleCat.free (ULift ℤ) |>.obj X` is `X →₀ ULift ℤ`. The free *presheaf of modules*
`PresheafOfModules.freeObj` is built on the second, while a free abelian presheaf is built on the
first, and a projection formula relating a sheafified free abelian presheaf to a tensor product
of presheaves of modules has to cross between them.

## Main definitions

* `AddCommGrpCat.freeIntModule`: the free module over the integers on a type, read as an abelian
  group.
* `AddCommGrpCat.uliftIntHomEquiv`: an additive map out of `ULift ℤ` is its value at `1`.
* `AddCommGrpCat.freeIntModuleAddHomEquiv`: an additive map out of `X →₀ ULift ℤ` is a family of
  elements indexed by `X`.
* `AddCommGrpCat.freeIntModuleAdj`: `freeIntModule` is left adjoint to the forgetful functor.

## Main results

* `AddCommGrpCat.freeIsoFreeIntModule`: **the free abelian group on a type is the free module on
  it over the integers**, as an isomorphism of functors.
* `AddCommGrpCat.freeIntModule_map_single`: the action of `freeIntModule` on a map reindexes the
  summands, which is what every computation with it needs.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AddCommGrpCat

/-- The free module over the integers on a type, read as an abelian group: the finitely supported
families of integers indexed by that type. -/
@[sga "4 V 7.2.0" "partial"]
def freeIntModule : Type u ⥤ AddCommGrpCat.{u} :=
  ModuleCat.free (ULift.{u} ℤ) ⋙ forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}

/-- The sections of the free module over the integers on `X` are the finitely supported families
of integers indexed by `X`. -/
theorem freeIntModule_obj (X : Type u) :
    freeIntModule.obj X = AddCommGrpCat.of (X →₀ ULift.{u} ℤ) :=
  rfl

/-- The free module over the integers of a map of types reindexes the summands. -/
@[simp] theorem freeIntModule_map_single {X Y : Type u} (f : X ⟶ Y) (x : X)
    (n : ULift.{u} ℤ) :
    AddCommGrpCat.Hom.hom (freeIntModule.map f) (Finsupp.single x n) =
      Finsupp.single (f x) n := by
  change Finsupp.mapDomain f (Finsupp.single x n) = _
  rw [Finsupp.mapDomain_single]

/-- **An additive map out of `ULift ℤ` is its value at `1`.** -/
def uliftIntHomEquiv (A : Type u) [AddCommGroup A] : (ULift.{u} ℤ →+ A) ≃ A where
  toFun φ := φ (ULift.up 1)
  invFun a := (zmultiplesHom A a).comp (AddEquiv.ulift (α := ℤ)).toAddMonoidHom
  left_inv φ := by
    apply AddMonoidHom.ext
    intro n
    change n.down • φ (ULift.up 1) = φ n
    rw [← φ.map_zsmul]
    congr 1
    apply ULift.ext
    simp
  right_inv a := by
    change (1 : ℤ) • a = a
    rw [one_smul]

/-- **An additive map out of `X →₀ ULift ℤ` is a family of elements indexed by `X`**: the free
module over the integers on `X` is free on the summand inclusions. -/
def freeIntModuleAddHomEquiv (X : Type u) (A : Type u) [AddCommGroup A] :
    (X → A) ≃ ((X →₀ ULift.{u} ℤ) →+ A) :=
  (Equiv.arrowCongr (Equiv.refl X) (uliftIntHomEquiv A).symm).trans
    Finsupp.liftAddHom.toEquiv

/-- The value of an additive map out of `X →₀ ULift ℤ` on the summand labelled by `x`. -/
@[simp] theorem freeIntModuleAddHomEquiv_apply_single (X : Type u) (A : Type u) [AddCommGroup A]
    (ψ : X → A) (x : X) (n : ULift.{u} ℤ) :
    freeIntModuleAddHomEquiv X A ψ (Finsupp.single x n) = n.down • ψ x :=
  Finsupp.liftAddHom_apply_single _ x n

/-- **The free module over the integers is left adjoint to the forgetful functor.** -/
def freeIntModuleAdj : freeIntModule.{u} ⊣ forget AddCommGrpCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X A => ConcreteCategory.homEquiv.trans
        ((freeIntModuleAddHomEquiv X (A : Type u)).symm.trans TypeCat.homEquiv.symm)
      homEquiv_naturality_left_symm := by
        intro X' X A f g
        apply AddCommGrpCat.hom_ext
        apply Finsupp.addHom_ext
        intro x n
        change (freeIntModuleAddHomEquiv X' (A : Type u) fun y => g (f y))
            (Finsupp.single x n) =
          (freeIntModuleAddHomEquiv X (A : Type u) fun y => g y)
            (AddCommGrpCat.Hom.hom (freeIntModule.map f) (Finsupp.single x n))
        rw [freeIntModule_map_single, freeIntModuleAddHomEquiv_apply_single,
          freeIntModuleAddHomEquiv_apply_single]
      homEquiv_naturality_right := by
        intro X A A' f g
        rfl }

/-- **The free abelian group on a type is the free module on it over the integers.** Both are
left adjoint to the forgetful functor to types, and a left adjoint is unique up to a unique
isomorphism. -/
def freeIsoFreeIntModule : AddCommGrpCat.free.{u} ≅ freeIntModule.{u} :=
  AddCommGrpCat.adj.leftAdjointUniq freeIntModuleAdj

end AddCommGrpCat

end
