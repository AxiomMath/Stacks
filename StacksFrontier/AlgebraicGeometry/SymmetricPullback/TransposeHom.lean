module

public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Transpose

/-!
# The adjoint transpose of a homomorphism out of a pulled-back graded algebra

`Stacks.RingedSpace.transposeUnitalHom` transposes a *unital* homomorphism `A ⟶ f_*C` of sheaves
of graded algebras to a unital homomorphism `f^*A ⟶ C`.  Multiplicativity of the transpose uses
only multiplicativity of the original, so the construction applies to an arbitrary homomorphism
of sheaves of graded algebras; this file records that form.

## Main definitions

* `Stacks.RingedSpace.transposeHom`: the adjoint transpose of a homomorphism `A ⟶ f_*C`, as a
  homomorphism `f^*A ⟶ C`.

## Main results

* `Stacks.RingedSpace.transposeHom_app`: its degreewise components are the adjoint transposes.
* `Stacks.RingedSpace.transposeUnitalHom_toHom`: on a unital homomorphism it is the transpose of
  `Stacks.RingedSpace.transposeUnitalHom`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite

universe u

namespace Stacks.RingedSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction
  SheafOfModules.GradedAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)}
  {C : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}

/-- The degreewise adjoint transpose of a homomorphism `A ⟶ f_*C`. -/
noncomputable def transposeHomApp (h : Hom A (pushforwardAlgebra f C)) (n : ℤ) :
    (pullbackGradedAlgebra f A).piece n ⟶ C.piece n :=
  ((pullbackAdjunction f).homEquiv (A.piece n) (C.piece n)).symm (h.app n)

/-- On the image of a section `a` of `A` under the pullback unit, the degreewise transpose of `h`
agrees with `h`. -/
lemma transposeHomApp_pullbackUnit (h : Hom A (pushforwardAlgebra f C)) (n : ℤ)
    (V : Opens Y.carrier) (a : (A.piece n).val.obj (op V)) :
    (transposeHomApp f h n).val.app (op ((opensMap f).obj V))
        (pullbackUnit f (A.piece n) (op V) a) =
      (h.app n).val.app (op V) a :=
  homEquiv_symm_val_app_unit f (M := A.piece n) (N := C.piece n) (h.app n) (op V) a

/-- The adjoint transpose of a homomorphism `A ⟶ f_*C` of sheaves of graded algebras, as a
homomorphism `f^*A ⟶ C`. Both sides of multiplicativity are bilinear, so it is enough to check it
on images of the pullback unit. -/
noncomputable def transposeHom (h : Hom A (pushforwardAlgebra f C)) :
    Hom (pullbackGradedAlgebra f A) C where
  app := transposeHomApp f h
  map_mul i j U x y := by
    obtain ⟨U⟩ := U
    refine pullbackBilinear_ext f
      (bilinPostcomp ((pullbackGradedAlgebra f A).mul i j) (transposeHomApp f h (i + j)))
      ((((C.mul i j).compLeft (transposeHomApp f h i).val).compRight
        (transposeHomApp f h j).val)) (fun V a b => ?_) U x y
    change (transposeHomApp f h (i + j)).val.app (op ((opensMap f).obj V))
        (((pullbackGradedAlgebra f A).mul i j).app (op ((opensMap f).obj V))
          (pullbackUnit f (A.piece i) (op V) a) (pullbackUnit f (A.piece j) (op V) b)) =
      (C.mul i j).app (op ((opensMap f).obj V))
        ((transposeHomApp f h i).val.app (op ((opensMap f).obj V))
          (pullbackUnit f (A.piece i) (op V) a))
        ((transposeHomApp f h j).val.app (op ((opensMap f).obj V))
          (pullbackUnit f (A.piece j) (op V) b))
    rw [pullbackGradedAlgebra_mul_pullbackUnit f A i j V a b, transposeHomApp_pullbackUnit,
      transposeHomApp_pullbackUnit, transposeHomApp_pullbackUnit]
    exact h.map_mul i j (op V) a b

/-- The degreewise components of `transposeHom f h` are the adjoint transposes of those of `h`. -/
@[simp] lemma transposeHom_app (h : Hom A (pushforwardAlgebra f C)) (n : ℤ) :
    (transposeHom f h).app n =
      ((pullbackAdjunction f).homEquiv (A.piece n) (C.piece n)).symm (h.app n) := rfl

/-- On a unital homomorphism the transpose is the one of
`Stacks.RingedSpace.transposeUnitalHom`. -/
lemma transposeUnitalHom_toHom (h : UnitalHom A (pushforwardAlgebra f C)) :
    (transposeUnitalHom f h).toHom = transposeHom f h.toHom := rfl

end Stacks.RingedSpace
