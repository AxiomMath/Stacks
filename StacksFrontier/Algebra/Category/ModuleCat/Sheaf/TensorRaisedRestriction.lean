module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRaisedSymmetry

/-!
# The tensor product commutes with restriction to a slice site

Testing a local property of a tensor product on a covering needs the tensor product formed on a
slice site to be the restriction to that slice of the tensor product formed on the whole site.
`Stacks.SheafOfModules.TensorLocalProperties.tensorOverIso` is that comparison for the tensor
product whose module universe equals the universe of the ring sheaf.  This file proves it for
`Stacks.SheafOfModules.Tensor.sheafTensor`, the Stacks 0GMW tensor product, whose module universe
is independent of the universe of the ring sheaf — which is the form needed at the raised
universe in which a global presentation lives.

## Main results

* `Stacks.SheafOfModules.TensorRaised.presheafTensorRestrictIso`: the objectwise tensor product of
  presheaves of modules commutes with restriction to a slice, which is computed objectwise.
* `Stacks.SheafOfModules.TensorRaised.tensorOverRaisedIso`: **the tensor product of sheaves of
  modules commutes with restriction to a slice.**

## Implementation notes

Both sides are sheafifications on the slice site: the left one of the objectwise tensor product of
the restrictions, the right one — being a restriction of a sheafification — of the restriction of
the objectwise tensor product.  The first receives its own sheafification unit and the second the
restriction of the sheafification unit on the whole site, which is locally bijective because
restriction along a cocontinuous functor preserves local injectivity and surjectivity.  The two
sources are identified objectwise, so
`Stacks.SheafOfModules.UliftTensor.isoOfLocallyBijective` applies.

## References

* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

universe u v w z

namespace Stacks.SheafOfModules.TensorRaised

open Stacks.SheafOfModules.UliftTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Restriction of presheaves of modules to a slice site, at a module universe independent of the
universe of the ring presheaf. -/
noncomputable abbrev presheafRestrictionRaised (O : Cᵒᵖ ⥤ CommRingCat.{w}) (V : C) :
    PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{z} (((Over.forget V).op ⋙ O) ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.pushforward.{z} (F := Over.forget V)
    (𝟙 (((Over.forget V).op ⋙ O) ⋙ forget₂ CommRingCat.{w} RingCat.{w}))

/-- The objectwise tensor product of presheaves of modules commutes with restriction to a slice
site: both are computed objectwise, so the comparison is the identity on sections. -/
noncomputable def presheafTensorRestrictIso (O : Cᵒᵖ ⥤ CommRingCat.{w}) (V : C)
    (A B : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.tensorObj (O := (Over.forget V).op ⋙ O)
        ((presheafRestrictionRaised.{u, v, w, z} O V).obj A)
        ((presheafRestrictionRaised.{u, v, w, z} O V).obj B) ≅
      (presheafRestrictionRaised.{u, v, w, z} O V).obj
        (PresheafOfModules.tensorObj (O := O) A B) :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _)
    (by intro X Y f; exact ModuleCat.tensor_ext fun x y ↦ rfl)

/-- **The tensor product of sheaves of modules commutes with restriction to a slice site**, at a
module universe independent of the universe of the ring sheaf. -/
noncomputable def tensorOverRaisedIso (R : Sheaf J CommRingCat.{w}) (V : C)
    [HasWeakSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [(J.over V).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify (J.over V) AddCommGrpCat.{z}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{z}]
    (A B : SheafOfModules.{z} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, z, z} (R.over V)).obj (A.over V)).obj
        (B.over V) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} R).obj A).obj B).over V :=
  let S := (Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) R
  let L := presheafRestrictionRaised.{u, v, w, z} R.obj V
  let TAB : PresheafOfModules.{z} (R.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) :=
    PresheafOfModules.tensorObj (O := R.obj) A.val B.val
  isoOfLocallyBijective
    (sheafifyUnit (R := S.over V)
      (PresheafOfModules.tensorObj (O := (Over.forget V).op ⋙ R.obj)
        (L.obj A.val) (L.obj B.val)))
    (L.map (sheafifyUnit (R := S) TAB))
    (isLocallyInjective_sheafifyUnit _) (isLocallySurjective_sheafifyUnit _)
    (Presheaf.isLocallyInjective_whisker (J.over V) J (Over.forget V)
      (CategoryTheory.toSheafify J TAB.presheaf))
    (Presheaf.isLocallySurjective_whisker (J.over V) J (Over.forget V)
      (CategoryTheory.toSheafify J TAB.presheaf))
    (presheafTensorRestrictIso.{u, v, w, z} R.obj V A.val B.val)

end Stacks.SheafOfModules.TensorRaised

end
