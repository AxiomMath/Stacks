module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Deformation.ToposThickening.Basic
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.TensorSheafSections

/-!
# Uniqueness of the canonical action map of an extension

Let `i : (Sh(C), O') ⟶ (Sh(C), O)` be a first order thickening with defining ideal `I`, let `F`
and `K` be `O`-modules, and let `E` be an extension of `F` by `K` as an exact sequence of
`O'`-modules.  The canonical action map `c_E : I ⊗_O F ⟶ K` of [Stacks Project, Tag 08MB] is
characterized by the local formula
`f (c_E (a ⊗ g x)) = a • x` for a section `a` of `I` and a section `x` of the middle term of
`E`, where `f` and `g` are the two maps of the extension.  This file shows that the formula
determines the map: any morphism `I ⊗_O F ⟶ K` satisfying it is equal to `c_E`.

## Main results

* `Deformation.ToposThickening.extensionActionMap_unique`: a morphism `I ⊗_O F ⟶ K` satisfying
  the characterizing local formula of `Deformation.ToposThickening.extensionActionMap` is that
  map.

## References

* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w'

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}}
  {Y : RingedTopos.{v', u', w'}}

/-- The canonical action map `I ⊗[O] F → K` of an extension is the only morphism satisfying its
characterizing local formula. -/
lemma extensionActionMap_unique
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K)
    (hc : ∀ (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : E.Z.left.val.obj U),
      E.f.val.app U
          (c.val.app U
            (((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
                i.toToposHom).obj X.O))
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
                i.toToposHom).obj X.O)).obj)).unit.app
              (PresheafOfModules.tensorObj hi.I.val F.val)).app U
              (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U]
                E.g.val.app U x))) =
        (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from
          hi.incl.val.app U a) • x) :
    (extensionActionMap hi E).1 = c := by
  have : Mono E.f.val := (SheafOfModules.forget _).map_mono E.f
  let p : E.Z.left.val.presheaf ⟶ F.val.presheaf :=
    (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj).map E.g.val
  have : Presheaf.IsLocallySurjective Y.J p := sheafModule_epi_locallySurjective E.g
  exact tensorSheaf_hom_ext_of_locallySurjective
    ((pushforwardCommRingFunctor i.toToposHom).obj X.O) p fun U a x =>
      PresheafOfModules.injective_of_mono E.f.val U
        (((extensionActionMap hi E).2 U a x).trans (hc U a x).symm)

end Deformation.ToposThickening

end
