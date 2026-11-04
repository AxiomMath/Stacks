module

public import StacksFrontier.CategoryTheory.Sites.Descent.CoGrothendieckPullbackComp
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A pseudofunctor is a stack exactly when its Grothendieck construction is

Let `F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat` be a pseudofunctor over a site `(𝒮, J)` and let
`p = CoGrothendieck.forget F` be the fibred category it presents, Stacks 003S.  There are two
notions of being a stack in play: `CategoryTheory.Pseudofunctor.IsStack` for `F`, which asks that
the functor to the descent data of a covering sieve be an equivalence, and
`CategoryTheory.Functor.IsStack` for `p`, the three conditions of Stacks 026F.  This file proves
that they agree, and reads off the form of Stacks 02ZI that a criterion stated for a category
fibred in groupoids consumes.

The two notions were related only through an intermediate pseudofunctor before this file.
`CategoryTheory.Functor.isStack_pullbackPseudofunctor_iff` compares `p` with the *pullback*
pseudofunctor of Stacks 02XO, whose transition functor along `f` is the chosen pullback `f*`, and
that pseudofunctor is not `F`; the comparison between them is
`CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpStrongTrans`.  So a descent statement
about `F` could not be read as one about `p` without first transporting it along that comparison,
which is what the three results below do.

## Main results

* `CategoryTheory.Pseudofunctor.CoGrothendieck.isStackFor_forget_iff`: the pullback pseudofunctor
  of the Grothendieck construction of `F` is a stack for a presieve exactly when `F` is.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.isStack_forget_iff`: **the Grothendieck
  construction of `F` is a stack in the sense of Stacks 026F exactly when `F` is a stack.**
* `CategoryTheory.Pseudofunctor.CoGrothendieck.isStackInGroupoids_forget`: **a pseudofunctor which
  is a stack and whose Grothendieck construction is fibred in groupoids presents a stack in
  groupoids**, Stacks 02ZI.

## Implementation notes

The transport is `CategoryTheory.Pseudofunctor.StrongTrans.isStackFor_iff_of_app_isEquivalence`
along `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpStrongTrans`, whose component at an
object is `CategoryTheory.Pseudofunctor.CoGrothendieck.fiberFunctor`, the identification of the
fibre of `F` over `S` with the fibre of `∫ᶜ F` over `S`.  That functor is an equivalence by the
instance Mathlib attaches to `CategoryTheory.Functor.Fiber.inducedFunctor` of
`CategoryTheory.Pseudofunctor.CoGrothendieck.comp_const`, so the hypothesis of the transport is
discharged by instance synthesis; it is recorded as
`isEquivalence_pullbackCmpStrongTrans_app` because the transport wants it at the component of the
strong transformation, a spelling instance synthesis does not reach on its own.

Passing from the presieve statement to the topology statement in both directions uses
`CategoryTheory.Pseudofunctor.IsStack.of_isStackFor` and
`CategoryTheory.Pseudofunctor.isStackFor'`, which are inverse to each other on covering sieves.

## References

* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open CategoryTheory CategoryTheory.Functor CategoryTheory.Functor.IsFibered Opposite

universe w v₁ u₁ v₂ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{max v₁ v₂, max u₁ u₂})

/-- **The identification of a fibre of `F` with the corresponding fibre of `∫ᶜ F` is an
equivalence.**  This is the instance Mathlib attaches to
`CategoryTheory.Functor.Fiber.inducedFunctor` of
`CategoryTheory.Pseudofunctor.CoGrothendieck.comp_const`, recorded at the
`CategoryTheory.Pseudofunctor.CoGrothendieck.fiberFunctor` spelling that the comparison with the
pullback pseudofunctor uses. -/
@[sga "4 VI 7.1.4" "partial", sga "4 XVII 2.2.12" "partial", sga "4 XVII 3.3.3" "Reverse direction"]
instance isEquivalence_fiberFunctor (S : 𝒮) : (fiberFunctor F S).IsEquivalence :=
  inferInstanceAs (Fiber.inducedFunctor (comp_const F S)).IsEquivalence

/-- Every component of
`CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpStrongTrans` is an equivalence: it is
`CategoryTheory.Pseudofunctor.CoGrothendieck.fiberFunctor`, the identification of a fibre of `F`
with the corresponding fibre of `∫ᶜ F`. -/
@[sga "4 XVII 3.3.3" "Reverse direction"]
lemma isEquivalence_pullbackCmpStrongTrans_app (a : LocallyDiscrete 𝒮ᵒᵖ) :
    ((pullbackCmpStrongTrans F).app a).toFunctor.IsEquivalence :=
  isEquivalence_fiberFunctor F (unop a.as)

/-- **The pullback pseudofunctor of the Grothendieck construction of `F` is a stack for a presieve
exactly when `F` is.**  This is the transport of being a stack along
`CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpStrongTrans`. -/
lemma isStackFor_forget_iff {S : 𝒮} (R : Presieve S) :
    (pullbackPseudofunctor (forget F)).IsStackFor R ↔ F.IsStackFor R :=
  ((pullbackCmpStrongTrans F).isStackFor_iff_of_app_isEquivalence
    (isEquivalence_pullbackCmpStrongTrans_app F) R).symm

/-- **The Grothendieck construction of `F` is a stack in the sense of Stacks 026F exactly when `F`
is a stack.**

Both directions run through the pullback pseudofunctor of `∫ᶜ F`:
`CategoryTheory.Functor.isStack_pullbackPseudofunctor_iff` identifies the left hand side with that
pseudofunctor being a stack, and
`CategoryTheory.Pseudofunctor.CoGrothendieck.isStackFor_forget_iff` identifies its presieve
conditions with those of `F`. -/
theorem isStack_forget_iff (J : GrothendieckTopology 𝒮) :
    (forget F).IsStack J ↔ F.IsStack J := by
  rw [← Functor.isStack_pullbackPseudofunctor_iff]
  exact ⟨fun _ ↦ IsStack.of_isStackFor fun _ R hR ↦
      (isStackFor_forget_iff F R.arrows).1 ((pullbackPseudofunctor (forget F)).isStackFor' R hR),
    fun _ ↦ IsStack.of_isStackFor fun _ R hR ↦
      (isStackFor_forget_iff F R.arrows).2 (F.isStackFor' R hR)⟩

/-- **Stacks 02ZI for a Grothendieck construction.**  A pseudofunctor which is a stack and whose
Grothendieck construction is fibred in groupoids presents a stack in groupoids.

This is `CategoryTheory.Pseudofunctor.CoGrothendieck.isStack_forget_iff` followed by
`CategoryTheory.Functor.IsStack.isStackInGroupoids`. -/
theorem isStackInGroupoids_forget {J : GrothendieckTopology 𝒮} (hF : F.IsStack J)
    (hgpd : (forget F).IsFiberedInGroupoids) :
    (forget F).IsStackInGroupoids.{w} J :=
  ((isStack_forget_iff F J).2 hF).isStackInGroupoids hgpd

end CategoryTheory.Pseudofunctor.CoGrothendieck

end
