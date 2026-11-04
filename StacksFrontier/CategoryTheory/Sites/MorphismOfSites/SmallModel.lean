module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSmallModel
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# The site condition at the universe of a small model

Mathlib's criterion for a continuous functor to define a morphism of sites, Stacks 00X5, is
`CategoryTheory.Functor.preservesFiniteLimits_sheafPullback`: for a *small* site, a continuous
representably flat functor has a left exact pullback on sheaves of sets valued in the universe
of the site.  The sites of schemes have their objects one universe above their morphisms, so
that criterion does not apply to them directly, and the unrestricted
`IsMorphismOfSites.{w}` — "the direct image has *some* left exact left adjoint" — has to be
established at the universe `w` one wants.

Which `w` one wants is forced by what the site condition is for.  A ringed site declares its
underlying topos at the universe of the sections of its structure sheaf, so a morphism of
ringed sites between sites of schemes needs the condition for sheaves of sets in `Type u`,
one universe *below* the objects of the sites; the pullback construction that Mathlib supplies
for a `Type (u + 1)` site answers a different question.

This file closes that gap once.  A site which is essentially small at `u` has a small model
there, the restriction of sheaves of sets along the comparison with that model is an
equivalence, and the pullback on the small model is left exact by Stacks 00X5.  Conjugating
that pullback by the two equivalences exhibits a left exact left adjoint of the direct image,
which is exactly `IsMorphismOfSites.{u}`.

## Main results

* `isMorphismOfSites_of_essentiallySmall`: a continuous representably flat functor between
  sites that are essentially small at `u` defines a morphism of sites for sheaves of sets in
  `Type u`.

## Implementation notes

The hypothesis is representable flatness rather than left exactness of the pullback of the
site at hand: the conjugate is *exhibited* as the left adjoint, so no comparison with another
left adjoint is needed, and flatness transports to the small model because the two comparison
functors are equivalences and flatness is stable under composition.

`adjunctionOfConjugate` is the adjunction half of
`CategoryTheory.Adjunction.preservesFiniteLimits_of_conjugate`, which concludes instead that a
*given* left adjoint is left exact.

Two copies of this argument are already in the tree, for the small étale site of a scheme
(`AlgebraicGeometry.smallEtaleBaseChange_isMorphismOfSites_ringUniverse`) and for the inclusion
of a small Zariski site into it
(`AlgebraicGeometry.SmallEtale.opensToSmallEtale_isMorphismOfSites`), and a third for the
spaces-étale sites of algebraic spaces
(`AlgebraicGeometry.Space.spacesToposMorphismTypeU`).  This is the statement they are
instances of; it is added here rather than by rewriting them.

## References

* [Stacks Project, Tag 00X5](https://stacks.math.columbia.edu/tag/00X5)
* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

section Conjugate

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-- Conjugating a left adjoint by equivalences on both sides: if `P₀ ⊣ W ⋙ R ⋙ V` with `V` and
`W` equivalences, then `V ⋙ P₀ ⋙ W` is a left adjoint of `R`. -/
private def adjunctionOfConjugate
    {A : Type u₁} [Category.{v₁} A] {A₀ : Type u₂} [Category.{v₂} A₀]
    {B₀ : Type u₃} [Category.{v₃} B₀] {E : Type u₄} [Category.{v₄} E]
    (V : A ⥤ A₀) (W : B₀ ⥤ E) (R : E ⥤ A) (P₀ : A₀ ⥤ B₀)
    [V.IsEquivalence] [W.IsEquivalence] (adj₀ : P₀ ⊣ W ⋙ R ⋙ V) :
    (V ⋙ P₀) ⋙ W ⊣ R :=
  have hiso : W.asEquivalence.inverse ⋙ ((W ⋙ R ⋙ V) ⋙ V.asEquivalence.inverse) ≅ R :=
    Functor.isoWhiskerLeft W.asEquivalence.inverse
        (Functor.associator W (R ⋙ V) V.asEquivalence.inverse) ≪≫
      W.asEquivalence.invFunIdAssoc ((R ⋙ V) ⋙ V.asEquivalence.inverse) ≪≫
      Functor.associator R V V.asEquivalence.inverse ≪≫
      Functor.isoWhiskerLeft R V.asEquivalence.unitIso.symm ≪≫ R.rightUnitor
  ((V.asEquivalence.toAdjunction.comp adj₀).comp
    W.asEquivalence.toAdjunction).ofNatIsoRight hiso

end Conjugate

section SmallModel

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C]
  {D : Type (u + 1)} [Category.{u} D] [EssentiallySmall.{u} D]

/-- The topology transported to a small model of a site, as the finest topology making the
comparison with the site continuous. -/
private abbrev smallModelTopology (J : GrothendieckTopology C) :
    GrothendieckTopology (SmallModel.{u} C) :=
  AlgebraicGeometry.RingedTopos.smallModelTopology J

/-- The topology transported to a small model of a site, as the finest topology making the
comparison with the site continuous. -/
abbrev smallModelTopology' (J : GrothendieckTopology C) :
    GrothendieckTopology (SmallModel.{u} C) :=
  (equivSmallModel.{u} C).inverse.inducedTopology J

/-- A functor between sites, transported to their small models. -/
private abbrev smallModelFunctor (F : C ⥤ D) : SmallModel.{u} C ⥤ SmallModel.{u} D :=
  (equivSmallModel.{u} C).inverse ⋙ F ⋙ (equivSmallModel.{u} D).functor

/-- The comma categories indexing the right Kan extension along the comparison of a site with
its small model have limits of sets in universe `u`: they are essentially small at `u`, the
small model being small and the site locally small. This is an instance of
`AlgebraicGeometry.RingedTopos.hasLimitsOfShape_structuredArrow_equivSmallModel_inverse_op`. -/
private instance hasLimitsOfShape_structuredArrow_inverse_op (W : Cᵒᵖ) :
    HasLimitsOfShape (StructuredArrow W (equivSmallModel.{u} C).inverse.op) (Type u) :=
  inferInstance

/-- The same for the comparison in the other direction. -/
private instance hasLimitsOfShape_structuredArrow_functor_op
    (W : (SmallModel.{u} C)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow W (equivSmallModel.{u} C).functor.op) (Type u) :=
  inferInstance

/-- The transported functor is continuous for the transported topologies: the two comparisons
with the small models are continuous, and so is the functor itself. -/
private instance isContinuous_smallModelFunctor (F : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [F.IsContinuous J K] :
    (smallModelFunctor.{u} F).IsContinuous (smallModelTopology.{u} J)
      (smallModelTopology.{u} K) :=
  have : (F ⋙ (equivSmallModel.{u} D).functor).IsContinuous J (smallModelTopology.{u} K) :=
    Functor.isContinuous_comp _ _ _ K _
  Functor.isContinuous_comp _ _ _ J _

/-- The direct image of the transported functor is the direct image of the functor, conjugated
by the two restrictions along the comparisons with the small models.  This holds by `rfl`, both
sides being the direct image of the same composite functor. -/
private theorem sheafPushforwardContinuous_smallModelFunctor (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K] :
    ((equivSmallModel.{u} D).functor.sheafPushforwardContinuous (Type u) K
        (smallModelTopology.{u} K)) ⋙
      (F.sheafPushforwardContinuous (Type u) J K) ⋙
      ((equivSmallModel.{u} C).inverse.sheafPushforwardContinuous (Type u)
        (smallModelTopology.{u} J) J) =
    (smallModelFunctor.{u} F).sheafPushforwardContinuous (Type u) (smallModelTopology.{u} J)
      (smallModelTopology.{u} K) := rfl

/-- Restriction of sheaves of sets along the comparison of a site with its small model.  It is
an equivalence, the comparison being a dense subsite inclusion. -/
private abbrev smallModelRestrictSource (J : GrothendieckTopology C) :
    Sheaf J (Type u) ⥤ Sheaf (smallModelTopology.{u} J) (Type u) :=
  (equivSmallModel.{u} C).inverse.sheafPushforwardContinuous (Type u)
    (smallModelTopology.{u} J) J

/-- Restriction of sheaves of sets along the comparison, in the other direction, of a site with
its small model. -/
private abbrev smallModelRestrictTarget (K : GrothendieckTopology D) :
    Sheaf (smallModelTopology.{u} K) (Type u) ⥤ Sheaf K (Type u) :=
  (equivSmallModel.{u} D).functor.sheafPushforwardContinuous (Type u) K
    (smallModelTopology.{u} K)

/-- **Stacks 00X5 at the universe of a small model.**  A continuous representably flat functor
between two sites that are essentially small at `u` defines a morphism of sites for sheaves of
sets valued in `Type u`, one universe below the objects of the sites.

The left exact left adjoint of the direct image is the pullback along the transported functor on
the small models, which is left exact by Stacks 00X5 at the universe of a genuinely small site,
conjugated by the two restriction equivalences along the comparisons with the small models. -/
@[stacks 00X5 "the site condition at the universe of a small model"]
public theorem isMorphismOfSites_of_essentiallySmall (F : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [F.IsContinuous J K] [RepresentablyFlat F] :
    IsMorphismOfSites.{u} F J K := by
  have hP₀ : PreservesFiniteLimits ((smallModelFunctor.{u} F).sheafPullback (Type u)
      (smallModelTopology.{u} J) (smallModelTopology.{u} K)) :=
    Functor.preservesFiniteLimits_sheafPullback _ _ _
  have hL : PreservesFiniteLimits
      ((smallModelRestrictSource.{u} J ⋙
          (smallModelFunctor.{u} F).sheafPullback (Type u) (smallModelTopology.{u} J)
            (smallModelTopology.{u} K)) ⋙
        smallModelRestrictTarget.{u} K) :=
    have := hP₀
    ⟨fun _ _ _ => inferInstance⟩
  exact
    { __ := (inferInstance : F.IsContinuous J K)
      hasExactLeftAdjoint :=
        ⟨(smallModelRestrictSource.{u} J ⋙
            (smallModelFunctor.{u} F).sheafPullback (Type u) (smallModelTopology.{u} J)
              (smallModelTopology.{u} K)) ⋙ smallModelRestrictTarget.{u} K,
          ⟨adjunctionOfConjugate (smallModelRestrictSource.{u} J)
            (smallModelRestrictTarget.{u} K)
            (F.sheafPushforwardContinuous (Type u) J K)
            ((smallModelFunctor.{u} F).sheafPullback (Type u) (smallModelTopology.{u} J)
              (smallModelTopology.{u} K))
            (((smallModelFunctor.{u} F).sheafAdjunctionContinuous (Type u)
                (smallModelTopology.{u} J) (smallModelTopology.{u} K)).ofNatIsoRight
              (eqToIso (sheafPushforwardContinuous_smallModelFunctor F J K).symm))⟩,
          hL⟩ }

end SmallModel

end
