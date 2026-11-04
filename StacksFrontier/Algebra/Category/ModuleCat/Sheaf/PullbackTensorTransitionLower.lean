module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorLower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposTransition

/-!
# The coherence of a transition of pullbacks, reduced to the five lower steps of Tag 03EL

`Stacks.SheafOfModules.PullbackTensorTransitionCoherence` is an equation between two morphisms out
of the iterated pullback `φ^*ψ^*(A ⊗ B)`, and that object is the value of the left adjoint of the
composite of the two adjunctions of Stacks 03D7. So the equation may be transposed, and once it is,
every occurrence of a comparison of Tag 03EL disappears in favour of
`Stacks.SheafOfModules.pullbackTensorLower`, the five lower steps of the chain traversed backwards.

What is left is an equation between the five lower steps for `ψ` after the five lower steps for
`φ`, and the five lower steps for `χ` — that is, exactly what the five composition laws of
steps 2 to 6 of the chain speak about, with step 1 and the comparisons of Tag 03EL themselves
eliminated. This file performs that reduction.

## Main results

* `Stacks.SheafOfModules.pullbackTensorStep1_homEquiv_pullbackTensorIso_comp`: **the adjoint
  transpose of the two comparisons of Tag 03EL composed is the five lower steps for `ψ` after the
  five lower steps for `φ`.** No transition appears: this is a statement about a composable pair of
  morphisms of ringed topoi and nothing else.
* `Stacks.SheafOfModules.pullbackTensorTransitionCoherence_app_of_lower`: **the coherence of a
  transition at one pair of sheaves of modules follows from the step 1 law for the transition
  together with the corresponding equation between the five lower steps.**
* `Stacks.SheafOfModules.pullbackTensorTransitionCoherence_of_lower`: the same for all pairs, which
  is `Stacks.SheafOfModules.PullbackTensorTransitionCoherence` itself.

## Implementation notes

The transposition is taken along `Stacks.SheafOfModules.pullbackTensorStep1` for `ψ` after the
adjunction of Stacks 03D7 for `φ`, which is the composite adjunction's hom-set bijection written so
that the step 1 composition law
`Stacks.SheafOfModules.pullbackTensorStep1_comp'` is literally a hypothesis of the reduction. The
comparison `e` of the two readings of the iterated direct image is left an arbitrary isomorphism;
at the compositor of Stacks 03D8 it is
`Stacks.SheafOfModules.pushforwardModulesCompAppIso`.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

section Transition

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (φ : RingedToposHom X Y) (ψ : RingedToposHom Y Z)

/-- **The adjoint transpose of the two comparisons of Tag 03EL composed is the five lower steps of
the chain for `ψ` after the five lower steps for `φ`.**

For a morphism `m : φ^*ψ^*A ⊗_{O_C} φ^*ψ^*B ⟶ N`, the pullback along `φ` of the comparison for
`ψ`, followed by the comparison for `φ` and then by `m`, is transposed — first across the
adjunction of Stacks 03D7 for `φ` and then across step 1 of the chain for `ψ` — to the five lower
steps for `ψ` applied to the five lower steps for `φ` applied to `m`.

No transition of pullbacks appears: this is a statement about a composable pair of morphisms of
ringed topoi, and it is the right-hand side of every transition coherence transposed. -/
theorem pullbackTensorStep1_homEquiv_pullbackTensorIso_comp
    (A B : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (m : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((φ.pullbackModules).obj ((ψ.pullbackModules).obj A),
          (φ.pullbackModules).obj ((ψ.pullbackModules).obj B)) ⟶ N) :
    pullbackTensorStep1 ψ A B ((pushforwardModules φ).obj N)
        ((pullbackAdjPushforwardModules φ).homEquiv
          ((ψ.pullbackModules).obj
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (A, B))) N
          ((φ.pullbackModules).map ((pullbackTensorIso ψ).hom.app (A, B)) ≫
            (pullbackTensorIso φ).hom.app
                ((ψ.pullbackModules).obj A, (ψ.pullbackModules).obj B) ≫ m)) =
      pullbackTensorLower ψ A B ((pushforwardModules φ).obj N)
        (pullbackTensorLower φ ((ψ.pullbackModules).obj A) ((ψ.pullbackModules).obj B) N m) :=
  (congrArg (pullbackTensorStep1 ψ A B ((pushforwardModules φ).obj N))
      ((Adjunction.homEquiv_naturality_left (pullbackAdjPushforwardModules φ)
            ((pullbackTensorIso ψ).hom.app (A, B))
            ((pullbackTensorIso φ).hom.app
              ((ψ.pullbackModules).obj A, (ψ.pullbackModules).obj B) ≫ m)).trans
        (congrArg (fun k ↦ (pullbackTensorIso ψ).hom.app (A, B) ≫ k)
          (pullbackTensorStep1_pullbackTensorIso_hom_app_comp φ ((ψ.pullbackModules).obj A)
            ((ψ.pullbackModules).obj B) N m)))).trans
    (pullbackTensorStep1_pullbackTensorIso_hom_app_comp ψ A B ((pushforwardModules φ).obj N)
      (pullbackTensorLower φ ((ψ.pullbackModules).obj A) ((ψ.pullbackModules).obj B) N m))

variable (χ : RingedToposHom X Z)
  (θ : ψ.pullbackModules ⋙ φ.pullbackModules ⟶ χ.pullbackModules)

/-- **The coherence of a transition of pullbacks with the comparison of Tag 03EL, at one pair of
sheaves of modules, from the five lower steps of the chain.**

The two hypotheses are the step 1 composition law for `θ` at the comparison for `χ` — the
transposition of `θ` followed by that comparison, read against the comparison `e` of the two
readings of the iterated direct image — and the equation between the five lower steps of the chain
that remains once step 1 and all three comparisons of Tag 03EL have been transposed away. -/
theorem pullbackTensorTransitionCoherence_app_of_lower
    (A B : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (e : (pushforwardModules ψ).obj ((pushforwardModules φ).obj
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
            ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))) ≅
        (pushforwardModules χ).obj
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
            ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)))
    (h1 : pullbackTensorStep1 χ A B
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
            ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))
          ((pullbackTensorIso χ).hom.app (A, B)) =
        pullbackTensorStep1 ψ A B
            ((pushforwardModules φ).obj
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
                ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)))
            ((pullbackAdjPushforwardModules φ).homEquiv
              ((ψ.pullbackModules).obj
                (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj
                  (A, B)))
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
                ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))
              (θ.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj
                  (A, B)) ≫
                (pullbackTensorIso χ).hom.app (A, B))) ≫
          e.hom)
    (h2 : pullbackTensorLower ψ A B
            ((pushforwardModules φ).obj
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
                ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)))
            (pullbackTensorLower φ ((ψ.pullbackModules).obj A) ((ψ.pullbackModules).obj B)
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
                ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
                ((θ.app A, θ.app B) :
                  (((φ.pullbackModules).obj ((ψ.pullbackModules).obj A),
                      (φ.pullbackModules).obj ((ψ.pullbackModules).obj B)) : _ × _) ⟶
                    ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)))) ≫
          e.hom =
        pullbackTensorLower χ A B
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
            ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))
          (𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
            ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)))) :
    θ.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (A, B)) ≫
        (pullbackTensorIso χ).hom.app (A, B) =
      (φ.pullbackModules).map ((pullbackTensorIso ψ).hom.app (A, B)) ≫
        (pullbackTensorIso φ).hom.app ((ψ.pullbackModules).obj A, (ψ.pullbackModules).obj B) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
            ((θ.app A, θ.app B) :
              (((φ.pullbackModules).obj ((ψ.pullbackModules).obj A),
                  (φ.pullbackModules).obj ((ψ.pullbackModules).obj B)) : _ × _) ⟶
                ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)) := by
  have hχ : pullbackTensorStep1 χ A B
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
          ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))
        ((pullbackTensorIso χ).hom.app (A, B)) =
      pullbackTensorLower χ A B
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
          ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))
        (𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
          ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))) :=
    (congrArg (pullbackTensorStep1 χ A B
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
          ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)))
      (Category.comp_id ((pullbackTensorIso χ).hom.app (A, B))).symm).trans
      (pullbackTensorStep1_pullbackTensorIso_hom_app_comp χ A B
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
          ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))
        (𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
          ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))))
  refine ((pullbackAdjPushforwardModules φ).homEquiv
    ((ψ.pullbackModules).obj
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (A, B)))
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
      ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))).injective ?_
  refine (pullbackTensorStep1 ψ A B
    ((pushforwardModules φ).obj
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)))).injective ?_
  refine Eq.trans ?_ (pullbackTensorStep1_homEquiv_pullbackTensorIso_comp φ ψ A B _ _).symm
  exact ((Iso.cancel_iso_hom_right _ _ e).mp (h2.trans (hχ.symm.trans h1))).symm

/-- **The coherence of a transition of pullbacks with the comparison of Tag 03EL, from the five
lower steps of the chain.** This is
`Stacks.SheafOfModules.pullbackTensorTransitionCoherence_app_of_lower` for all pairs of sheaves of
modules at once, which is `Stacks.SheafOfModules.PullbackTensorTransitionCoherence` itself. -/
theorem pullbackTensorTransitionCoherence_of_lower
    (e : ∀ A B : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O),
        (pushforwardModules ψ).obj ((pushforwardModules φ).obj
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
              ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))) ≅
          (pushforwardModules χ).obj
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
              ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)))
    (h1 : ∀ A B : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O),
      pullbackTensorStep1 χ A B
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
            ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))
          ((pullbackTensorIso χ).hom.app (A, B)) =
        pullbackTensorStep1 ψ A B
            ((pushforwardModules φ).obj
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
                ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)))
            ((pullbackAdjPushforwardModules φ).homEquiv
              ((ψ.pullbackModules).obj
                (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj
                  (A, B)))
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
                ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))
              (θ.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj
                  (A, B)) ≫
                (pullbackTensorIso χ).hom.app (A, B))) ≫
          (e A B).hom)
    (h2 : ∀ A B : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O),
      pullbackTensorLower ψ A B
            ((pushforwardModules φ).obj
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
                ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)))
            (pullbackTensorLower φ ((ψ.pullbackModules).obj A) ((ψ.pullbackModules).obj B)
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
                ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
                ((θ.app A, θ.app B) :
                  (((φ.pullbackModules).obj ((ψ.pullbackModules).obj A),
                      (φ.pullbackModules).obj ((ψ.pullbackModules).obj B)) : _ × _) ⟶
                    ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)))) ≫
          (e A B).hom =
        pullbackTensorLower χ A B
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
            ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B))
          (𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
            ((χ.pullbackModules).obj A, (χ.pullbackModules).obj B)))) :
    PullbackTensorTransitionCoherence φ ψ χ θ := fun A B ↦
  pullbackTensorTransitionCoherence_app_of_lower φ ψ χ θ A B (e A B) (h1 A B) (h2 A B)

end Transition

end Stacks.SheafOfModules

end
