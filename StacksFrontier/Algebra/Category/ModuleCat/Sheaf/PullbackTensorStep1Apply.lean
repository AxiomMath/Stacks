module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor

/-!
# The first link of the chain of Tag 03EL, pointwise

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. The first of the six
steps of the chain of **Stacks 03EL**, `Stacks.SheafOfModules.pullbackTensorStep1`, is the
hom-set bijection

`Hom_{O_C}(f^*(F ⊗_{O_D} G), N) = Hom_{O_D}(F ⊗_{O_D} G, f_*N)`

of the adjunction `f^* ⊣ f_*` of **Stacks 03D7**. This file records what that bijection does to a
morphism: it is the unit of the adjunction at `F ⊗_{O_D} G` followed by the direct image of the
morphism, and dually its inverse is the pullback of a morphism followed by the counit.

Both formulas are stated for an *arbitrary* morphism, so they rewrite the first link out of any
instance of the chain without knowing what the remaining links are applied to.

## Main results

* `Stacks.SheafOfModules.pullbackTensorStep1_apply`: step 1 of the chain of Tag 03EL is the unit
  of Tag 03D7 followed by the direct image.
* `Stacks.SheafOfModules.pullbackTensorStep1_symm_apply`: its inverse is the pullback followed by
  the counit of Tag 03D7.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe w w' v u v' u'

section Step1

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)
  (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **Step 1 of the chain of Tag 03EL, pointwise**: the hom-set bijection of the adjunction
`f^* ⊣ f_*` of Tag 03D7 carries `h : f^*(F ⊗ G) ⟶ N` to the unit of that adjunction at `F ⊗ G`
followed by the direct image `f_*h`.

The statement is generic in `h`, which is what makes it compose with the characterizations of the
remaining links of the regrouped chain of
`Stacks.SheafOfModules.pullbackTensorHomEquiv_apply`: no link needs to know the morphism the
others are applied to. -/
theorem pullbackTensorStep1_apply
    (h : (f.pullbackModules).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) ⟶ N) :
    pullbackTensorStep1 f F G N h =
      (pullbackAdjPushforwardModules f).unit.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) ≫
        (pushforwardModules f).map h :=
  (pullbackAdjPushforwardModules f).homEquiv_unit
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) N h

/-- **The inverse of step 1 of the chain of Tag 03EL, pointwise**: the inverse hom-set bijection
of Tag 03D7 carries `t : F ⊗ G ⟶ f_*N` to the pullback `f^*t` followed by the counit of the
adjunction at `N`. This is the direction the inverse comparison of Tag 03EL is built from. -/
theorem pullbackTensorStep1_symm_apply
    (t : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G) ⟶
      (pushforwardModules f).obj N) :
    (pullbackTensorStep1 f F G N).symm t =
      (f.pullbackModules).map t ≫ (pullbackAdjPushforwardModules f).counit.app N :=
  (pullbackAdjPushforwardModules f).homEquiv_counit
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) N t

end Step1

end Stacks.SheafOfModules

end
