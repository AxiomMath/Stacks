module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingClosedSubspaces

/-! # An invertible module which is a zero object forces the scheme to be empty
Tensoring by an invertible module is an equivalence, and tensoring it with the structure sheaf
returns the module itself, so a scheme carrying an invertible zero module has a trivial structure
sheaf and hence no points.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

variable {T : Scheme.{u}}

/-- **Tensoring a module by the structure sheaf returns the module.** The tensor functor of `L`
evaluated at the unit sheaf of modules is the sheafification of `L.val ⊗ 𝒪`, which the right unit
constraint of the presheaf tensor product identifies with the sheafification of `L.val`, and that
is `L` again because `L` is a sheaf. -/
public def zeroNotInvertible_tensorLeftFunctorObjUnitIso
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf T.presheaf T.ringCatSheaf.2)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨T.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (T.presheaf) (forget₂ CommRingCat RingCat)
          (T.ringCatSheaf.2)⟩).obj (L))).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf T.presheaf
          T.ringCatSheaf.2)) ≅ L :=
  (Stacks.SheafOfModules.TensorSheafification.sheafify T.presheaf T.ringCatSheaf.2).mapIso
      (MonoidalCategory.rightUnitor (C := PresheafOfModules
        (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf T.presheaf)) L.val) ≪≫
    (Stacks.SheafOfModules.forgetSheafifyIso T.presheaf T.ringCatSheaf.2).app L

/-- **An invertible module which is a zero object forces the structure sheaf to be a zero
object.** Tensoring by `L` is an equivalence, hence faithful, and it carries the structure sheaf
to `L`, which is a zero object; a faithful functor sending an object to a zero object sends its
identity to the zero morphism, which forces the object itself to be a zero object. -/
public theorem zeroNotInvertible_isZero_unit
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf T.presheaf T.ringCatSheaf.2))
    (hinv : Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L)
    (hL : IsZero L) :
    IsZero (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf T.presheaf T.ringCatSheaf.2)) := by
  have h := (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence T.presheaf
    T.ringCatSheaf.2 L).mp hinv
  have hz := hL.of_iso (zeroNotInvertible_tensorLeftFunctorObjUnitIso L)
  exact @IsZero.of_full_of_faithful_of_isZero _ _ _ _ _ h.full h.faithful _ hz

/-- **A scheme carrying an invertible module which is a zero object is empty.** The structure
sheaf is then a zero object, so the unit of the ring of global sections vanishes. -/
public theorem isEmpty_of_isZero_of_isInvertible (T : Scheme.{u}) (L : T.Modules)
    (hinv : Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L)
    (hL : IsZero L) : IsEmpty T := by
  have : Subsingleton Γ(T, ⊤) :=
    _root_.Stacks.subsingleton_of_isZero (zeroNotInvertible_isZero_unit L hinv hL) (op ⊤)
  exact Scheme.isEmpty_of_one_eq_zero (Subsingleton.elim _ _)

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
