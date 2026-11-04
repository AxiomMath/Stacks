module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback

/-!
# The inverse image of the unit module is the unit module

The inverse image of sheaves of modules of Stacks 03D2 along a finite-product-preserving functor
`Φ` between categories of sheaves of sets is built by transporting the scalar action along `Φ`,
and the inverse-image sheaf of rings is built by transporting the ring operations along the same
`Φ`.  Applied to a sheaf of rings viewed as a module over itself the two constructions transport
the *same* multiplication map, so the inverse image of the unit module **is** the unit module of
the inverse-image sheaf of rings, on the nose.

## Main results

* `Stacks.Sheaves.ToposPullback.moduleSheaf_unit`: the sheaf of sets underlying the unit module
  is the sheaf of sets underlying the sheaf of rings.
* `Stacks.Sheaves.ToposPullback.pullbackModuleObj_unit`: the inverse image of the unit module is
  the unit module of the inverse-image sheaf of rings.
* `Stacks.Sheaves.ToposPullback.pullbackModuleObj_unit_smul`: its scalar action is therefore the
  multiplication of that sheaf of rings.

## Implementation notes

Both are `rfl`.  They are recorded as named statements because a consumer needs them as
*equalities of objects*: the middle term of the inverse image of a short complex of ideal
sheaves inside `𝒪` is the inverse image of the unit module, and a statement about its sections
has to be read as a statement about sections of the inverse-image sheaf of rings.  Without the
names, that reading appears in a consumer only as an unexplained coincidence of two spellings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe ww ww' vv uu vv' uu'

namespace Stacks.Sheaves.ToposPullback

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'})

/-- The sheaf of sets underlying a sheaf of rings read as a module over itself is the sheaf of
sets underlying that sheaf of rings. -/
theorem moduleSheaf_unit : moduleSheaf O (SheafOfModules.unit O) = ringSheaf O := rfl

omit [J.HasSheafCompose (forget RingCat)] [J.HasSheafCompose (forget AddCommGrpCat)] in
/-- **The inverse image of the unit module is the unit module of the inverse-image sheaf of
rings.**  Both transport the multiplication of `O` along `Φ`. -/
theorem pullbackModuleObj_unit :
    pullbackModuleObj J Φ O (SheafOfModules.unit O) =
      SheafOfModules.unit (pullbackRingSheaf J Φ O) := rfl

omit [J.HasSheafCompose (forget RingCat)] [J.HasSheafCompose (forget AddCommGrpCat)] in
/-- **The scalar action on the inverse image of the unit module is the multiplication** of the
inverse-image sheaf of rings. -/
theorem pullbackModuleObj_unit_smul (U : Cᵒᵖ)
    (a : ToType ((pullbackRingSheaf J Φ O).obj.obj U))
    (m : ToType ((pullbackModuleObj J Φ O (SheafOfModules.unit O)).val.obj U)) :
    a • m = a * (show ToType ((pullbackRingSheaf J Φ O).obj.obj U) from m) := rfl

end Stacks.Sheaves.ToposPullback

end
