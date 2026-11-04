module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor

/-!
# The last five steps of the chain of Tag 03EL, traversed backwards

The comparison of **Tag 03EL** is the preimage of the identity under the six-step chain of
bijections `Stacks.SheafOfModules.pullbackTensorHomEquiv`, and step 1 of that chain is the
adjunction of Stacks 03D7. So the adjoint transpose of the comparison — and more generally of the
comparison followed by any morphism — is the *last five* steps of the chain traversed backwards.
This file names that five-step composite and records the two identities that make it the shape
every composition law of the chain is read against.

## Main definitions

* `Stacks.SheafOfModules.pullbackTensorLower`: **the last five steps of the chain of Tag 03EL,
  traversed backwards.**

## Main results

* `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp'`: the comparison of Tag 03EL followed by
  a morphism is the inverse chain at that morphism.
* `Stacks.SheafOfModules.pullbackTensorStep1_pullbackTensorIso_hom_app_comp`: **the adjoint
  transpose of the comparison of Tag 03EL followed by a morphism is the five lower steps traversed
  backwards from that morphism.**

## Implementation notes

`StacksDraft.…​.PullbackTensorMateMonoidal` writes the five-step composite out in full in every one
of its statements, which is what makes that file a thousand lines long; naming it here is the same
move `Stacks.SheafOfModules.pullbackTensorBottomHom` makes for the bottom two steps, and for the
same reason — a statement mentioning the composite twice is otherwise expensive to elaborate.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe w w' v u v' u'

section Lower

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y) (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The last five steps of the chain of Tag 03EL, traversed backwards.** A morphism
`g : f^*F ⊗_{O_C} f^*G ⟶ N` is carried by steps 6, 5, 4, 3 and 2 of the chain, each traversed
backwards, to a morphism `F ⊗_{O_D} G ⟶ f_*N`.

By `Stacks.SheafOfModules.pullbackTensorStep1_pullbackTensorIso_hom_app_comp` this is the adjoint
transpose, across the adjunction of Stacks 03D7 that step 1 is, of the comparison of Tag 03EL
followed by `g`. -/
def pullbackTensorLower
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G) ⟶ N) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G) ⟶
      (pushforwardModules f).obj N :=
  (pullbackTensorStep2 f F G N).symm
    ((pullbackTensorStep3 f F G N).symm
      ((pullbackTensorStep4 f F G N).symm
        ((pullbackTensorStep5 f F G N).symm ((pullbackTensorStep6 f F G N).symm g))))

/-- The chain of Tag 03EL traversed backwards is step 1 traversed backwards after the five lower
steps traversed backwards. This is the definition of
`Stacks.SheafOfModules.pullbackTensorHomEquiv` as a composite of bijections, read at the inverse,
and it is named because the five-step composite is otherwise reached only through a definitional
unfolding of `Equiv.trans`. -/
lemma pullbackTensorHomEquiv_symm_apply
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G) ⟶ N) :
    (pullbackTensorHomEquiv f F G N).symm g =
      (pullbackTensorStep1 f F G N).symm (pullbackTensorLower f F G N g) := rfl

/-- **The comparison of Tag 03EL followed by a morphism is the chain traversed backwards at that
morphism.** The comparison is the preimage of the identity, and the inverse chain is natural in
the sheaf of values. -/
lemma pullbackTensorIso_hom_app_comp'
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G) ⟶ N) :
    (pullbackTensorIso f).hom.app (F, G) ≫ g = (pullbackTensorHomEquiv f F G N).symm g :=
  (congrArg (fun m ↦ m ≫ g) (pullbackTensorIso_hom_app f F G)).trans
    ((pullbackTensorHomEquiv_symm_naturality f F G
        (𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
          ((f.pullbackModules).obj F, (f.pullbackModules).obj G))) g).symm.trans
      (congrArg (pullbackTensorHomEquiv f F G N).symm (Category.id_comp g)))

/-- **The adjoint transpose of the comparison of Tag 03EL followed by a morphism is the five lower
steps of the chain traversed backwards from that morphism.** Step 1 of the chain is the adjunction
of Stacks 03D7, and transposing undoes it.

At `g = 𝟙` this is the statement
`Stacks.SheafOfModules.homEquiv_pullbackTensorIso_hom_app` of
`StacksDraft.…​.PullbackTensorMateMonoidal`; the general form is what a composition law for the
chain is read against, because a composite's comparison meets the factors' comparisons only after
one of them has been followed by something. -/
lemma pullbackTensorStep1_pullbackTensorIso_hom_app_comp
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G) ⟶ N) :
    pullbackTensorStep1 f F G N ((pullbackTensorIso f).hom.app (F, G) ≫ g) =
      pullbackTensorLower f F G N g :=
  (congrArg (pullbackTensorStep1 f F G N)
      ((pullbackTensorIso_hom_app_comp' f F G N g).trans
        (pullbackTensorHomEquiv_symm_apply f F G N g))).trans
    (Equiv.apply_symm_apply (pullbackTensorStep1 f F G N) (pullbackTensorLower f F G N g))

end Lower

end Stacks.SheafOfModules

end
