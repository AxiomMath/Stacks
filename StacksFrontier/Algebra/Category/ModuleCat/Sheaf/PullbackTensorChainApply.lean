module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep1Apply
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep2Apply
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStepTargetApply

/-!
# The chain of Tag 03EL identified against a morphism, with its first, second and fourth links
evaluated

`Stacks.SheafOfModules.pullbackTensorHomEquiv_eq_iff_pairingApp` reduces an identification of the
comparison of Tag 03EL with another construction to a computation, on a pair of local sections,
of the first three links of the regrouped chain of
`Stacks.SheafOfModules.pullbackTensorHomEquiv_apply`. Its first and second links are evaluated by
`Stacks.SheafOfModules.pullbackTensorStep1_apply` and
`Stacks.SheafOfModules.pullbackTensorStep2_apply`. This file substitutes those two evaluations
into that reduction, leaving the base change of bilinear pairings
`Stacks.SheafOfModules.pullbackTensorBilinEquiv` — the third link — as the only part of the chain
not written out.

## Why the composition is done here, generically

A consumer identifying the comparison of Tag 03EL at a *particular* morphism of ringed topoi
cannot perform these substitutions in its own goal. Rewriting with the two link evaluations there
requires their instance arguments to match the ones instance search produced for the particular
ringed topoi, and they match only up to definitional unfolding: `rw` reports that it
did not find the pattern, and supplying the arguments explicitly instead makes the rewrite fire
but builds a term the kernel does not finish checking. Stated once at variables, as below, the
two rewrites are immediate, and a consumer applies the result as an ordinary term application —
where the crossing sits at an explicit argument and costs nothing.

## Main results

* `Stacks.SheafOfModules.pullbackTensorHomEquiv_eq_iff_pairingApp_unit`: the comparison of
  Tag 03EL applied to `h` is a given `t` if and only if `t`, on the sheafification-unit image of
  each pure tensor of local sections, agrees with the base change along `f` of the pairing that
  pairs two sections of `F` and `G` to the image of their tensor under the unit of Tag 03D7
  followed by the direct image of `h`.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.SheafOfModules

universe v u w v' u' w'

section ChainApply

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

/-- **The chain of Tag 03EL identified against a given morphism, with its first, second and
fourth links written out.** For an arbitrary morphism `h` out of `f^*(F ⊗_{O_D} G)`, the chain of
Tag 03EL carries `h` to a given `t` exactly when `t`, evaluated on the sheafification-unit image
of a pure tensor of local sections, agrees with the base change along `f` of the pairing
obtained from `h` by the unit of Tag 03D7 followed by the direct image of `h`.

This is `Stacks.SheafOfModules.pullbackTensorHomEquiv_eq_iff_pairingApp` with
`Stacks.SheafOfModules.pullbackTensorStep1_apply` and
`Stacks.SheafOfModules.pullbackTensorStep2_apply` substituted into its right-hand side. Only the
third link, the base change of bilinear pairings, is left unexpanded. -/
theorem pullbackTensorHomEquiv_eq_iff_pairingApp_unit
    (h : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)) ⋙
        f.pullbackModules).obj (F, G) ⟶ N)
    (t : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G) ⟶ N) :
    pullbackTensorHomEquiv f F G N h = t ↔
      ∀ (W : X.Cᵒᵖ) (a : ((f.pullbackModules).obj F).val.obj W)
        (b : ((f.pullbackModules).obj G).val.obj W),
        t.val.app W
            (((PresheafOfModules.sheafificationAdjunction
                    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (𝟙 _)).unit.app
                  (((f.pullbackModules).obj F).val ⊗
                    ((f.pullbackModules).obj G).val)).app W
              (a ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj W] b)) =
          pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (pullbackTensorBilinEquiv f F G N
              ⟨pairingOfTensorHom
                  (hO := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property)
                  ((PresheafOfModules.sheafificationAdjunction
                        (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (𝟙 _)).unit.app
                      (F.val ⊗ G.val) ≫
                    ((pullbackAdjPushforwardModules f).unit.app
                        (((Functor.uncurry.obj
                          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) ≫
                      (pushforwardModules f).map h).val),
                isBilinearPairing_pairingOfTensorHom
                  (hO := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) _⟩).1 W a b := by
  rw [pullbackTensorHomEquiv_eq_iff_pairingApp f F G N h t, pullbackTensorStep1_apply,
    pullbackTensorStep2_apply]

end ChainApply

end Stacks.SheafOfModules

end
