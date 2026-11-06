module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Colimits and composition of a sheaf with a functor

Let `(C, J)` be a site and let `F : A ⥤ B` be a functor between two categories in which
sheafification of `C`-presheaves exists.  Composition with `F` carries sheaves to sheaves as
soon as `CategoryTheory.GrothendieckTopology.HasSheafCompose` holds, giving the functor
`CategoryTheory.sheafCompose`.  This file proves that `CategoryTheory.sheafCompose` preserves
colimits when `F` preserves colimits and sheafification, and that the universe lift of abelian
groups satisfies the latter hypothesis.

## Main results

* `CategoryTheory.preservesColimitsOfShape_sheafCompose`: `CategoryTheory.sheafCompose`
  preserves colimits of a given shape.
* `AddCommGrpCat.preservesSheafification_uliftFunctor`: the universe lift of abelian groups
  preserves sheafification.

## Implementation notes

For the universe lift of abelian groups `CategoryTheory.sheafCompose` is neither a left nor a
right adjoint, so colimit preservation is proved from the sheafification side.  The composite
`CategoryTheory.presheafToSheaf ⋙ CategoryTheory.sheafCompose` is isomorphic to
`(Functor.whiskeringRight _ _ _).obj F ⋙ CategoryTheory.presheafToSheaf` by
`CategoryTheory.sheafComposeNatIso`, and both of those preserve colimits.  A colimit cocone of a
diagram of sheaves is recognised, through the isomorphism
`CategoryTheory.sheafToPresheaf ⋙ CategoryTheory.presheafToSheaf ≅ 𝟭`, as the image under
sheafification of a colimit cocone of the underlying presheaves, which is where that composite
applies; a second colimit cocone of the same diagram is then isomorphic to it.

That the universe lift preserves sheafification is immediate from the hypothesis
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` at both universes, because local
injectivity and local surjectivity are conditions on sections and `ULift` is a bijection on
sections.  The hypothesis holds for every Grothendieck topology on a site whose objects and
morphisms lie below the universe of sections, and at every universe on an essentially small
site.

The two section-level statements — that the universe lift preserves local injectivity and local
surjectivity — are `CategoryTheory.Presheaf.isLocallyInjective_whiskerRight_uliftFunctor` and
`CategoryTheory.Presheaf.isLocallySurjective_whiskerRight_uliftFunctor` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos`, and they are *not* imported
from there: that file carries the whole sheaf-of-modules comparison of Stacks 01BH, and its
instances make the `HasColimit` synthesis inside
`CategoryTheory.preservesColimitsOfShape_sheafCompose` above exceed the synthesis heartbeat
budget.  Both are two lines on the sections, so they are proved inline below instead.

## References

* [Stacks Project, Tag 00W1](https://stacks.math.columbia.edu/tag/00W1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' t m v u

namespace CategoryTheory

section SheafCompose

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
  [HasWeakSheafify J A] [HasWeakSheafify J B] [J.HasSheafCompose F]
  [J.PreservesSheafification F]

/-- Composing a sheaf with a functor that preserves colimits and sheafification preserves
colimits of sheaves: a colimit of sheaves is the sheafification of the colimit of the underlying
presheaves, where both hypotheses apply. -/
public theorem preservesColimitsOfShape_sheafCompose (K : Type w) [Category.{w'} K]
    [HasColimitsOfShape K (Cᵒᵖ ⥤ A)]
    [PreservesColimitsOfShape K ((Functor.whiskeringRight Cᵒᵖ A B).obj F)] :
    PreservesColimitsOfShape K (sheafCompose J F) := by
  have hstep : PreservesColimitsOfShape K (presheafToSheaf J A ⋙ sheafCompose J F) :=
    preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J F (sheafificationAdjunction J A) (sheafificationAdjunction J B))
  refine ⟨fun {D} => ⟨fun {c} hc => ?_⟩⟩
  let D' := D ⋙ sheafToPresheaf J A
  let e : D' ⋙ presheafToSheaf J A ≅ D :=
    Functor.isoWhiskerLeft D (asIso (sheafificationAdjunction J A).counit)
  let c₂ : Cocone D :=
    (Cocone.precompose e.inv).obj ((presheafToSheaf J A).mapCocone (colimit.cocone D'))
  have hc₂ : IsColimit c₂ :=
    (IsColimit.precomposeInvEquiv e _).symm
      (isColimitOfPreserves (presheafToSheaf J A) (colimit.isColimit D'))
  have hGc₂ : IsColimit ((sheafCompose J F).mapCocone c₂) := by
    refine ((IsColimit.precomposeInvEquiv
      (Functor.isoWhiskerRight e (sheafCompose J F)) _).symm
      (isColimitOfPreserves (presheafToSheaf J A ⋙ sheafCompose J F)
        (colimit.isColimit D'))).ofIsoColimit ?_
    refine Cocone.ext (Iso.refl _) fun j => ?_
    simp [c₂]
  exact ⟨hGc₂.ofIsoColimit ((Cocone.functoriality D (sheafCompose J F)).mapIso
    (hc₂.uniqueUpToIso hc))⟩

end SheafCompose

end CategoryTheory

namespace AddCommGrpCat

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify J AddCommGrpCat.{max t m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t m}]

/-- The universe lift of abelian groups preserves sheafification: becoming an isomorphism after
sheafification is local bijectivity, which is a condition on sections. -/
public instance preservesSheafification_uliftFunctor :
    J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, m} where
  le := by
    intro P₁ P₂ f hf
    rw [GrothendieckTopology.W_iff_isLocallyBijective] at hf
    rw [MorphismProperty.inverseImage_iff, GrothendieckTopology.W_iff_isLocallyBijective]
    refine ⟨⟨fun a b h => ?_⟩, ⟨fun a => ?_⟩⟩
    · exact J.superset_covering (fun _ _ hg => ULift.ext hg)
        (hf.1.equalizerSieve_mem a.down b.down (congrArg ULift.down h))
    · refine J.superset_covering ?_ (hf.2.imageSieve_mem a.down)
      intro Y g hg
      exact ⟨ULift.up hg.choose, ULift.ext hg.choose_spec⟩

end AddCommGrpCat

end
