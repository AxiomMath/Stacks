module

public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaOfClosed
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex

/-!
# Transporting the comparison of Stacks 03EL along an equation of morphisms of ringed topoi

For a morphism of ringed topoi `g`, the comparison `g^*(A ⊗ B) ≅ g^*A ⊗ g^*B` of Stacks 03EL,
read at the uncurried tensor bifunctor, is a tensor comparison for the pullback functor
`g^*`. Two equal morphisms `g₁ = g₂` have pullbacks identified by the `eqToIso` of that equation,
and reading the comparison of `g₁` through that identification gives the comparison of `g₂`.
This lets a statement about the comparison along one spelling of a morphism of ringed topoi be
read along another spelling without the two spellings ever being compared definitionally.

## Main results

* `Stacks.SheafOfModules.tensorIsoOfNatIsoRight_eqToIso_pullbackTensorIso`.
* `Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_uncurry`: the naturality of the
  comparison at the uncurried tensor bifunctor.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

namespace Stacks.SheafOfModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- **Stacks 03EL, naturality at the uncurried tensor bifunctor**: the comparison
`g^*(A ⊗ B) ≅ g^*A ⊗ g^*B` is natural for morphisms of pairs, the tensor products being read
through `Functor.uncurry`. -/
theorem pullbackTensorIso_hom_naturality_uncurry (g : RingedToposHom X Y)
    {AB AB' : SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
      SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))} (ab : AB ⟶ AB') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) ⋙
          RingedToposHom.pullbackModules g).map ab ≫ ((pullbackTensorIso g).app AB').hom =
      ((pullbackTensorIso g).app AB).hom ≫
        ((RingedToposHom.pullbackModules g).prod (RingedToposHom.pullbackModules g) ⋙
          Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).map ab :=
  pullbackTensorIso_hom_naturality_map g ab.1 ab.2

/-- **The comparison of Stacks 03EL is transported along an equation of morphisms of ringed
topoi to the comparison of the other morphism.** For `g₁ = g₂`, the uncurried comparison of
`g₁`, read through the identification `g₂^* ≅ g₁^*` given by the `eqToIso` of the equation, is
the uncurried comparison of `g₂`. -/
theorem tensorIsoOfNatIsoRight_eqToIso_pullbackTensorIso {g₁ g₂ : RingedToposHom X Y}
    (hg : g₁ = g₂) :
    PullbackInternalHom.tensorIsoOfNatIsoRight (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (eqToIso (congrArg (fun g : RingedToposHom X Y ↦ RingedToposHom.pullbackModules g) hg)).symm
        (NatIso.ofComponents
          (F := Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) ⋙
            RingedToposHom.pullbackModules g₁)
          (G := (RingedToposHom.pullbackModules g₁).prod (RingedToposHom.pullbackModules g₁) ⋙
            Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))
          (fun AB ↦ (pullbackTensorIso g₁).app AB)
          (pullbackTensorIso_hom_naturality_uncurry g₁)) =
      NatIso.ofComponents
          (F := Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) ⋙
            RingedToposHom.pullbackModules g₂)
          (G := (RingedToposHom.pullbackModules g₂).prod (RingedToposHom.pullbackModules g₂) ⋙
            Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))
          (fun AB ↦ (pullbackTensorIso g₂).app AB)
          (pullbackTensorIso_hom_naturality_uncurry g₂) := by
  subst hg
  exact PullbackInternalHom.tensorIsoOfNatIsoRight_refl _ _ _

end Stacks.SheafOfModules

end
