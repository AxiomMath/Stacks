module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Quot.QuotToCoherentStackMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stack.PresheafElementsStack
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.StackInSetoidsRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional

/-!
# A model of the Quot functor from representability of the Quot stack (Stacks 09TU)

The proof of Stacks 09TU runs through the stack in groupoids `Quot_{F/X/B}` attached to the Quot
functor: Stacks 09TT makes the functor an fppf sheaf, Stacks 09DS and Stacks 05UM make the stack
algebraic, and the implication (1) ⟹ (3) of Algebraic Stacks, Proposition 04SZ then makes the
stack representable by an algebraic space — which is the conclusion of Stacks 09TU.

That last step is a statement about a *stack*, and the conclusion of Stacks 09TU is a statement
about a *presheaf*. This file supplies the two pieces of connective tissue between them, both
unconditional, so that a proof of algebraicity of the Quot stack discharges the first geometric
clause of Stacks 09TU with nothing further to do.

The first piece is the converse of Stacks 04SV for the stack attached to a presheaf: the library
has `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_fibredCategory`, that the stack of
an algebraic space is representable by an algebraic space, but not the converse, that a presheaf
whose stack is representable by an algebraic space is an algebraic space. The converse is what a
consumer of Stacks 04SZ needs, and it holds because the category of elements of a presheaf of
sets determines the presheaf
(`CategoryTheory.PresheafOfCategories.pointwiseEquivOfEquivalenceOver`): the representing
presheaf and the given one have equivalent categories of elements over the site, hence are
isomorphic, and being an algebraic space is invariant under isomorphism.

The second piece is the hypothesis of Stacks 04SZ that is *not* algebraicity: that the stack is a
stack in setoids. For the stack of a presheaf this is automatic from the sheaf condition, by
Stacks 0430 and Stacks 0431; and the sheaf condition on a model of the Quot presheaf is the sheaf
condition on the Quot presheaf itself, which is Stacks 09TT.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicSpace_of_isRepresentableByAlgebraicSpace_fibredCategory`:
  **the converse of Stacks 04SV for the stack of a presheaf** — a presheaf of sets on the big
  fppf site whose attached stack is representable by an algebraic space is an algebraic space.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_fibredCategory_iff`: the two
  directions together, so representability of the stack of a presheaf *is* algebraicity of the
  presheaf.
* `AlgebraicGeometry.Stack.isStackInSetoids_fibredCategory`: the stack attached to a sheaf of
  sets on the big fppf site is a stack in setoids — the second hypothesis of the implication
  (1) ⟹ (3) of Stacks 04SZ, which for the Quot functor is therefore supplied by Stacks 09TT.
* `AlgebraicGeometry.Space.QuotSitePresheafModel.isSheaf_presheaf`: a model of the Quot presheaf
  is an fppf sheaf as soon as the Quot presheaf is, so Stacks 09TT applies to the model.
* `AlgebraicGeometry.Space.QuotSitePresheafModel.isStackInSetoids_quotStack`: the stack attached
  to a model of the Quot presheaf is a stack in setoids, given Stacks 09TT.
* `AlgebraicGeometry.Space.QuotSitePresheafModel`
  `.isAlgebraicSpace_of_isRepresentableByAlgebraicSpace`: **the first geometric clause of
  Stacks 09TU, reduced to representability of the Quot stack by an algebraic space.**

## Implementation notes

**Where this leaves Stacks 09TU.** With the results below, the first geometric clause of
Stacks 09TU — that a model of the Quot presheaf is an algebraic space — follows from
representability of the Quot stack by an algebraic space and nothing else. What produces that
representability is the implication (1) ⟹ (3) of Stacks 04SZ,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids`, whose two
hypotheses are now both accounted for: the stack-in-setoids hypothesis is
`AlgebraicGeometry.Space.QuotSitePresheafModel.isStackInSetoids_quotStack` given Stacks 09TT, and
the algebraicity hypothesis is what Stacks 09DS and Stacks 05UM supply in the source. That
implication additionally carries `AlgebraicGeometry.Stack.Bootstrap04S6Spaces`, the Bootstrap
chapter's Stacks 04S6 part (3), which this development does not prove.

**Why the converse of Stacks 04SV is not formal.** `AlgebraicGeometry.Stack.fibredCategory` of a
presheaf `F` is the Grothendieck construction of `F ⋙ typeToGrpd`, and
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace` asserts the existence of *some*
algebraic space `G` and an equivalence over the site between the two categories of elements.
Recovering `F ≅ G` from that equivalence is the content of
`CategoryTheory.PresheafOfCategories.pointwiseEquivOfEquivalenceOver`: an object of a category of
elements is recovered from the element it names, so an equivalence over the site is a family of
bijections of sections compatible with restriction. Both presheaves here are valued in the
universe of the site, so that family is an isomorphism of presheaves on the nose and no universe
lift intervenes — unlike
`CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_iff`, which is stated for
presheaves in different value universes and therefore lifts both.

**Model-independence.** The clause proved below is about one model, which is enough:
`AlgebraicGeometry.Space.QuotSitePresheafModel.isAlgebraicSpace_and_lfp_of_model` transports it
between models, so it is a property of `F/X/B`.

## References

* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 09TT](https://stacks.math.columbia.edu/tag/09TT)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 0430](https://stacks.math.columbia.edu/tag/0430)
* [Stacks Project, Tag 0431](https://stacks.math.columbia.edu/tag/0431)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The converse of Stacks 04SV for the stack attached to a presheaf -/

/-- **The converse of Stacks 04SV for the stack attached to a presheaf.** A presheaf of sets on
the big fppf site of `S` whose attached category fibred in groupoids is representable by an
algebraic space is itself an algebraic space.

Representability provides an algebraic space `G` and an equivalence over the site between the
categories of elements of `F` and of `G`; a category of elements determines its presheaf, by
`CategoryTheory.PresheafOfCategories.pointwiseEquivOfEquivalenceOver`, so the two presheaves are
isomorphic, and `AlgebraicGeometry.IsAlgebraicSpace.of_iso` concludes. Both presheaves are
valued in the universe of the site, so the family of bijections is an isomorphism of presheaves
directly. -/
theorem isAlgebraicSpace_of_isRepresentableByAlgebraicSpace_fibredCategory
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (h : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS F)) :
    IsAlgebraicSpace B S hS F := by
  obtain ⟨G, hG, ⟨e⟩⟩ := h
  refine hG.of_iso (NatIso.ofComponents
    (fun U => Equiv.toIso
      ((PresheafOfCategories.pointwiseEquivOfEquivalenceOver e).symm.equiv U)) ?_)
  intro U V g
  apply ConcreteCategory.hom_ext
  intro x
  exact (PresheafOfCategories.pointwiseEquivOfEquivalenceOver e).symm.naturality g x

/-- **Stacks 04SV for the stack attached to a presheaf, in both directions.** The category fibred
in groupoids attached to a presheaf of sets on the big fppf site of `S` is representable by an
algebraic space exactly when the presheaf is an algebraic space.

The forward direction is
`AlgebraicGeometry.Stack.isAlgebraicSpace_of_isRepresentableByAlgebraicSpace_fibredCategory` and
the backward one is `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_fibredCategory`. -/
theorem isRepresentableByAlgebraicSpace_fibredCategory_iff
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS F) ↔
      IsAlgebraicSpace B S hS F :=
  ⟨isAlgebraicSpace_of_isRepresentableByAlgebraicSpace_fibredCategory B S hS F,
    isRepresentableByAlgebraicSpace_fibredCategory B S hS F⟩

/-! ### The stack attached to a sheaf is a stack in setoids -/

/-- **The stack attached to a sheaf of sets is a stack in setoids.** This is Stacks 0430 — the
category of elements of a sheaf is a stack in sets — followed by Stacks 0431, that being a stack
in setoids transports along an equivalence over the site; here the equivalence is the identity,
the attached category fibred in groupoids being the category of elements.

It is the hypothesis of the implication (1) ⟹ (3) of Stacks 04SZ that is not algebraicity. -/
theorem isStackInSetoids_fibredCategory (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) :
    (fibredCategory B S hS F).val.p.IsStackInSetoids (BigFppfOver.topology B S hS) :=
  PresheafOfCategories.isStackInSetoids_of_equivalenceOver_discreteProjection F
    (BigFppfOver.topology B S hS) hF (StacksRepresentableCFG.EquivalenceOver.refl _)

end AlgebraicGeometry.Stack

/-! ### The first geometric clause of Stacks 09TU -/

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : QuotSituation B S hS}

namespace QuotSitePresheafModel

/-- **A model of the Quot presheaf is an fppf sheaf as soon as the Quot presheaf is.** The
universe lift of the model is the Quot presheaf, and the sheaf condition is insensitive to a
universe lift of the values, by `CategoryTheory.Presieve.isSheaf_comp_uliftFunctor_iff`.

So Stacks 09TT, `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf_isSheaf`, is a statement
about every model. -/
theorem isSheaf_presheaf (N : QuotSitePresheafModel D)
    (h : Presheaf.IsSheaf (BigFppfOver.topology B S hS) D.quotSitePresheaf) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) N.presheaf := by
  have h' : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (N.presheaf ⋙ uliftFunctor.{u + 1, u}) := (Presheaf.isSheaf_of_iso_iff N.iso).2 h
  rw [isSheaf_iff_isSheaf_of_type] at h' ⊢
  exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1 h'

/-- **The stack attached to a model of the Quot presheaf is a stack in setoids**, given the
sheaf property of the Quot presheaf, which is Stacks 09TT.

This is the hypothesis of the implication (1) ⟹ (3) of Stacks 04SZ that is not algebraicity,
discharged for `Quot_{F/X/B}`. -/
theorem isStackInSetoids_quotStack (N : QuotSitePresheafModel D)
    (h : Presheaf.IsSheaf (BigFppfOver.topology B S hS) D.quotSitePresheaf) :
    (Stack.fibredCategory B S hS N.presheaf).val.p.IsStackInSetoids
      (BigFppfOver.topology B S hS) :=
  Stack.isStackInSetoids_fibredCategory B S hS N.presheaf (N.isSheaf_presheaf h)

/-- **The first geometric clause of Stacks 09TU, reduced to representability of the Quot stack
by an algebraic space.** If the stack in groupoids attached to a model of the Quot presheaf is
representable by an algebraic space, then that model *is* an algebraic space.

This is the final step of the source's proof: Stacks 09TT makes `Quot_{F/X/B}` an fppf sheaf,
Stacks 09DS and Stacks 05UM make the attached stack algebraic, and the implication (1) ⟹ (3) of
Stacks 04SZ makes it representable by an algebraic space; the conclusion of Stacks 09TU is the
statement below about the presheaf, which
`AlgebraicGeometry.Stack.isAlgebraicSpace_of_isRepresentableByAlgebraicSpace_fibredCategory`
extracts.

By `AlgebraicGeometry.Space.QuotSitePresheafModel.isAlgebraicSpace_and_lfp_of_model` the
conclusion does not depend on the model. -/
theorem isAlgebraicSpace_of_isRepresentableByAlgebraicSpace (N : QuotSitePresheafModel D)
    (h : Stack.IsRepresentableByAlgebraicSpace B S hS
      (Stack.fibredCategory B S hS N.presheaf)) :
    IsAlgebraicSpace B S hS N.presheaf :=
  Stack.isAlgebraicSpace_of_isRepresentableByAlgebraicSpace_fibredCategory B S hS N.presheaf h

/-- **The stack attached to a model of the Quot presheaf is a stack in setoids**, with nothing
assumed: the Quot presheaf is an fppf sheaf by Stacks 09TT
(`AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf_isSheaf_fppf`). -/
theorem isStackInSetoids_quotStack_fppf (N : QuotSitePresheafModel D) :
    (Stack.fibredCategory B S hS N.presheaf).val.p.IsStackInSetoids
      (BigFppfOver.topology B S hS) :=
  N.isStackInSetoids_quotStack D.quotSitePresheaf_isSheaf_fppf

/-- **The first geometric clause of Stacks 09TU, reduced to algebraicity of the Quot stack.**  If
the stack in groupoids attached to a model of the Quot presheaf is an algebraic stack, then the
model is an algebraic space.

This is the last step of the source's proof: the stack is a stack in setoids by Stacks 09TT, so
the implication (1) ⟹ (3) of Stacks 04SZ, with Bootstrap 04S6
(`AlgebraicGeometry.Stack.bootstrap04S6Spaces`), makes it representable by an algebraic space.
What remains of Stacks 09TU is the algebraicity of the Quot stack, which the source obtains from
Stacks 09DS and Stacks 05UM. -/
theorem isAlgebraicSpace_of_isAlgebraicStack.{w} (N : QuotSitePresheafModel D)
    (halg : Stack.IsAlgebraicStack.{u, w} B S hS (Stack.fibredCategory B S hS N.presheaf).val) :
    IsAlgebraicSpace B S hS N.presheaf :=
  N.isAlgebraicSpace_of_isRepresentableByAlgebraicSpace
    (Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids B S hS _ halg
      N.isStackInSetoids_quotStack_fppf)

/-- **The stack attached to a model of the Quot presheaf is equivalent over the site to the
category of elements of the Quot presheaf**,
`AlgebraicGeometry.Space.QuotSituation.quotCatFiberedInGroupoids`: the universe lift of the
model is the Quot presheaf, and a category of elements only depends on its presheaf up to a
pointwise family of bijections. -/
def equivalenceOverQuotCatFiberedInGroupoids (N : QuotSitePresheafModel D) :
    StacksRepresentableCFG.EquivalenceOver D.quotCatFiberedInGroupoids.val.p
      (Stack.fibredCategory B S hS N.presheaf).val.p :=
  PresheafOfCategories.equivalenceOverOfPointwiseEquiv
    { equiv := fun T => (N.iso.app T).toEquiv.symm.trans Equiv.ulift
      naturality := fun {_T _T'} g s => congrArg ULift.down
        (NatTrans.naturality_apply N.iso.inv g s) }

/-- **The first geometric clause of Stacks 09TU, reduced to algebraicity of `Quot_{F/X/B}` as a
category fibred in groupoids.**  If the category of elements of the Quot presheaf,
`AlgebraicGeometry.Space.QuotSituation.quotCatFiberedInGroupoids`, is an algebraic stack, then
every model of the Quot presheaf is an algebraic space.  Algebraicity transports along the
equivalence over the site with the stack attached to the model (Stacks 03YQ), and
`AlgebraicGeometry.Space.QuotSitePresheafModel.isAlgebraicSpace_of_isAlgebraicStack` concludes. -/
theorem isAlgebraicSpace_of_isAlgebraicStack_quotCatFiberedInGroupoids.{w}
    (N : QuotSitePresheafModel D)
    (halg : Stack.IsAlgebraicStack.{u, w} B S hS D.quotCatFiberedInGroupoids.val) :
    IsAlgebraicSpace B S hS N.presheaf :=
  N.isAlgebraicSpace_of_isAlgebraicStack
    (Stack.isAlgebraicStack_of_equivalenceOver B S hS
      N.equivalenceOverQuotCatFiberedInGroupoids halg)

end QuotSitePresheafModel

end AlgebraicGeometry.Space

end
