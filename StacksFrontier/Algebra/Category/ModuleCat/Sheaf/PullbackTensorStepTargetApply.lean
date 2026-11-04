module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear

/-!
# The fourth link of the chain of Tag 03EL, evaluated

The chain of bijections of Tag 03EL regrouped into four links is
`Stacks.SheafOfModules.pullbackTensorHomEquiv_apply`: the adjunction of Tag 03D7, the universal
property of the tensor product over `O_D`, the base change of bilinear pairings, and finally
`Stacks.SheafOfModules.pullbackTensorStepTarget`, the universal property of the tensor product
sheaf of Tag 05NA over the structure sheaf of the *source*, at the two pullbacks.

That fourth link was available only as the `Equiv` it is defined to be. This file evaluates it,
for an **arbitrary** bilinear pairing `c` of the two pullbacks: the morphism
`f^*F ⊗_{O_C} f^*G ⟶ N` the link produces is pinned down by its restriction along the
sheafification unit, and sectionwise by its value on the sheafification-unit image of a pure
tensor, which is the value of `c` on the two sections. Nothing here is special to the pairing
the first three links of the chain produce, so these formulas compose with evaluations of the
other three links by rewriting.

## Main results

* `Stacks.SheafOfModules.unit_comp_pullbackTensorStepTarget_val`: **the fourth link, restricted
  along the sheafification unit.** The tensor product sheaf `f^*F ⊗_{O_C} f^*G` is the
  sheafification of the objectwise tensor product; restricted along the unit of that
  sheafification, the morphism out of it produced by the fourth link from a pairing `c` is the
  morphism out of the objectwise tensor product produced by `c`, which is
  `Stacks.SheafOfModules.tensorHomOfPairing`. This is the whole content of the link, with no
  `Equiv` left and no sections.
* `Stacks.SheafOfModules.pullbackTensorStepTarget_val_app_unit_tmul`: **the fourth link on a pure
  tensor.** On the sheafification-unit image of `a ⊗ₜ b`, the morphism produced by the fourth
  link from `c` takes the value `c` takes on `a` and `b`.
* `Stacks.SheafOfModules.pairingApp_pullbackTensorStepTarget_symm`: the fourth link traversed
  backwards. The pairing it recovers from a morphism `t` out of `f^*F ⊗_{O_C} f^*G` pairs two
  local sections by sending the sheafification-unit image of their tensor through `t`.
* `Stacks.SheafOfModules.pullbackTensorStepTarget_eq_iff_pairingApp`: the fourth link at a
  pairing `c` **equals a given morphism `t` if and only if** `t` takes the value `c` takes on
  every pair of local sections. This is the form in which the identification of a composite of
  the chain of Tag 03EL with another construction is reduced to an identity of values on
  sections.
* `Stacks.SheafOfModules.pullbackTensorHomEquiv_eq_iff_pairingApp`: the same reduction for the
  whole chain of Tag 03EL, for an arbitrary morphism `h` out of `f^*(F ⊗_{O_D} G)`: the chain
  carries `h` to a given morphism `t` if and only if `t` takes, on each pure tensor, the value
  of the pairing produced by the first three links.

## Implementation notes

Every proof is a term. `Stacks.SheafOfModules.pullbackTensorStepTarget` is *defined* as
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom` for the sheaf of rings
`Stacks.SheafOfModules.Tensor.ringSheaf X.O` and the two pullbacks, so each statement here is the
corresponding general formula of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearValueFormulas` at that instance. But the
instance is not reached by a rewrite: the general formulas are stated for a presheaf of
commutative rings `A` together with a proof that `A ⋙ forget₂ _ _` is a sheaf, whereas the link
is declared at the bundled sheaf of rings `Tensor.ringSheaf X.O`, and the two spellings of that
sheaf of rings agree only at default transparency — which is what a term checks and what the
motive check of `rw` does not. So each proof supplies the sheaf condition by name,
`(Tensor.ringSheaf X.O).property`, and is otherwise the general formula applied.

`Stacks.SheafOfModules.pullbackTensorStepTarget_eq_iff_pairingApp` is stated as an iff because
only one direction is an application of injectivity: the other is the evaluation formula itself.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.SheafOfModules

universe w w' v u v' u'

section StepTarget

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The fourth link of the regrouped chain of Tag 03EL, restricted along the sheafification
unit.** The tensor product sheaf `f^*F ⊗_{O_C} f^*G` of Tag 05NA is the sheafification of the
objectwise tensor product of the underlying presheaves of modules. Restricted along the unit of
that sheafification, the morphism out of it that
`Stacks.SheafOfModules.pullbackTensorStepTarget` produces from a bilinear pairing `c` is the
morphism out of the objectwise tensor product that `c` produces,
`Stacks.SheafOfModules.tensorHomOfPairing`.

This is the whole content of the fourth link, with no `Equiv` left unexpanded and no reference
to sections. -/
theorem unit_comp_pullbackTensorStepTarget_val
    (c : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ((f.pullbackModules).obj F) ⨯
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj G) ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q }) :
    (PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (𝟙 _)).unit.app
          (((f.pullbackModules).obj F).val ⊗ ((f.pullbackModules).obj G).val) ≫
        (pullbackTensorStepTarget f F G N c).val =
      tensorHomOfPairing (hO := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) c.2 :=
  unit_comp_bilinearEquivTensorSheafHom_val
    (hA := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) c

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The fourth link of the regrouped chain of Tag 03EL on a pure tensor.** The sheafification
unit carries a pure tensor `a ⊗ₜ b` of two local sections of the pullbacks to a local section of
`f^*F ⊗_{O_C} f^*G`, and the morphism that
`Stacks.SheafOfModules.pullbackTensorStepTarget` produces from a bilinear pairing `c` takes that
section to the value of `c` on `a` and `b`.

The pairing `c` is arbitrary, so this formula composes with evaluations of the other three links
of the regrouped chain by rewriting. -/
theorem pullbackTensorStepTarget_val_app_unit_tmul
    (c : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ((f.pullbackModules).obj F) ⨯
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj G) ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q })
    (U : X.Cᵒᵖ) (a : ((f.pullbackModules).obj F).val.obj U)
    (b : ((f.pullbackModules).obj G).val.obj U) :
    (pullbackTensorStepTarget f F G N c).val.app U
        (((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (𝟙 _)).unit.app
              (((f.pullbackModules).obj F).val ⊗ ((f.pullbackModules).obj G).val)).app U
          (a ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b)) =
      pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf X.O) c.1 U a b :=
  bilinearEquivTensorSheafHom_val_app_unit_tmul
    (hA := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) c U a b

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The fourth link of the regrouped chain of Tag 03EL, traversed backwards.** The bilinear
pairing that `Stacks.SheafOfModules.pullbackTensorStepTarget` recovers from a morphism `t` out of
`f^*F ⊗_{O_C} f^*G` pairs two local sections by sending the sheafification-unit image of their
tensor through `t`. -/
theorem pairingApp_pullbackTensorStepTarget_symm
    (t : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G) ⟶ N)
    (U : X.Cᵒᵖ) (a : ((f.pullbackModules).obj F).val.obj U)
    (b : ((f.pullbackModules).obj G).val.obj U) :
    pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((pullbackTensorStepTarget f F G N).symm t).1 U a b =
      t.val.app U
        (((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (𝟙 _)).unit.app
              (((f.pullbackModules).obj F).val ⊗ ((f.pullbackModules).obj G).val)).app U
          (a ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b)) :=
  pairingApp_bilinearEquivTensorSheafHom_symm
    (hA := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) t U a b

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The fourth link identified against a given morphism, on sections.** The morphism out of
`f^*F ⊗_{O_C} f^*G` that `Stacks.SheafOfModules.pullbackTensorStepTarget` produces from a
bilinear pairing `c` is a given morphism `t` if and only if `t`, evaluated on the
sheafification-unit image of each pure tensor, takes the value `c` takes on the two sections.

This is the shape in which an identification of a composite of the chain of Tag 03EL with
another construction is reduced to an identity of values on local sections: the forward
direction is `Stacks.SheafOfModules.pullbackTensorStepTarget_val_app_unit_tmul`, and the backward
one is that direction together with the injectivity of the fourth link, through the pairing it
recovers from `t`. -/
theorem pullbackTensorStepTarget_eq_iff_pairingApp
    (c : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ((f.pullbackModules).obj F) ⨯
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj G) ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q })
    (t : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G) ⟶ N) :
    pullbackTensorStepTarget f F G N c = t ↔
      ∀ (U : X.Cᵒᵖ) (a : ((f.pullbackModules).obj F).val.obj U)
        (b : ((f.pullbackModules).obj G).val.obj U),
        t.val.app U
            (((PresheafOfModules.sheafificationAdjunction
                    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (𝟙 _)).unit.app
                  (((f.pullbackModules).obj F).val ⊗
                    ((f.pullbackModules).obj G).val)).app U
              (a ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b)) =
          pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf X.O) c.1 U a b :=
  by
  constructor
  · rintro rfl U a b
    exact pullbackTensorStepTarget_val_app_unit_tmul f F G N c U a b
  · intro h
    exact ((pullbackTensorStepTarget f F G N).eq_symm_apply).1
      (Subtype.ext (pairing_ext (Stacks.SheafOfModules.Tensor.ringSheaf X.O) fun U a b ↦
        (h U a b).symm.trans
          (pairingApp_pullbackTensorStepTarget_symm f F G N t U a b).symm))

/-- **The chain of Tag 03EL identified against a given morphism, on sections.** For an arbitrary
morphism `h` out of `f^*(F ⊗_{O_D} G)`, the morphism `f^*F ⊗_{O_C} f^*G ⟶ N` the chain of
Tag 03EL produces from `h` is a given morphism `t` if and only if `t`, on the
sheafification-unit image of each pure tensor of local sections, takes the value on those two
sections of the pairing the first three links of the regrouped chain produce from `h`.

This is `Stacks.SheafOfModules.pullbackTensorHomEquiv_apply` followed by
`pullbackTensorStepTarget_eq_iff_pairingApp`, and it is the form in which an identification of
the comparison of Tag 03EL with another construction is reduced to a computation of the first
three links on a pair of local sections. Both `h` and `t` are arbitrary, so the reduction is
independent of any particular `h`. -/
theorem pullbackTensorHomEquiv_eq_iff_pairingApp
    (h : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)) ⋙
        f.pullbackModules).obj (F, G) ⟶ N)
    (t : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G) ⟶ N) :
    pullbackTensorHomEquiv f F G N h = t ↔
      ∀ (U : X.Cᵒᵖ) (a : ((f.pullbackModules).obj F).val.obj U)
        (b : ((f.pullbackModules).obj G).val.obj U),
        t.val.app U
            (((PresheafOfModules.sheafificationAdjunction
                    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (𝟙 _)).unit.app
                  (((f.pullbackModules).obj F).val ⊗
                    ((f.pullbackModules).obj G).val)).app U
              (a ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b)) =
          pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (pullbackTensorBilinEquiv f F G N
              (pullbackTensorStep2 f F G N (pullbackTensorStep1 f F G N h))).1 U a b :=
  (iff_of_eq (congrArg (· = t) (pullbackTensorHomEquiv_apply f F G N h))).trans
    (pullbackTensorStepTarget_eq_iff_pairingApp f F G N
      (pullbackTensorBilinEquiv f F G N
        (pullbackTensorStep2 f F G N (pullbackTensorStep1 f F G N h))) t)

end StepTarget

end Stacks.SheafOfModules

end
