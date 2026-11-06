module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.IsomorphismOfChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineLimitChartCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartPresentationStageDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationMorphismDescentSupplement

/-!
# Four steps of the proof of Stacks 07SQ

The proof of Stacks 07SQ runs over a descent situation (Situation 084R) and, at a separated
stage of it, over the limit situation the chart systems of Stacks 07SI are built on. This file
collects the four steps of that proof which are statements about one of those two structures
alone.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.atCanonicalLimit` replaces the chosen limiting cone
  of a descent situation by the categorical limit cone of its inverse system.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_left_of_presentationBaseChange`: the
  morphism `f₀` of display 70.5.10.1 is locally of finite presentation.
* `AlgebraicGeometry.Space.MorphismDescentSystemOfChartsBounded.isAffineSpace_sourceAt`: in
  Situation 084W with affine source, the base change of the source to a later stage is affine.
* `AlgebraicGeometry.Space.LimitSituation.isPullback_limitChartToSpace_stage`: the limit of a
  chart system is the fibre product of the limit with the chart of any one stage.
* `AlgebraicGeometry.Space.LimitSituation.comp_modelProjection_eq_of_eq`: restriction to the
  charts and passage to the limit commute, as an identity of ring homomorphisms.

## Implementation notes

*Why the limit cone is normalised.* Situation 084W,
`AlgebraicGeometry.Space.MorphismDescentSystemOfChartsBounded`, and with it everything about the
base change of a morphism to the limit, is stated at the categorical limit
`CategoryTheory.Limits.limit` of the inverse system, whereas a descent situation carries a limiting
cone of its own and the chart systems of Stacks 07SI are built over the vertex of that cone.
`AlgebraicGeometry.Space.DescentSituation.atCanonicalLimit` makes the two agree on the nose by
taking the carried cone to be the categorical one; the vertex of the original cone is canonically
isomorphic to it, so no hypothesis is lost and affineness transports along that isomorphism.

*The cancellation step.*
`AlgebraicGeometry.Space.MorphismDescentSystemOfChartsBounded.exists_isIso_mapAt` asks the morphism
to be descended to be locally of finite presentation. For the morphism `f₀` of display 70.5.10.1
this is cancellation: its composite with the left vertical of the square of Stacks 084U is the
étale chart of the stage, which is locally of finite presentation, and that left vertical is
locally of finite type, being the base change of the spectrum of a ring map of finite presentation.
Stacks 05WT, `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_comp`, asks exactly finite
type of the second factor.

*The identity of ring homomorphisms* is
`AlgebraicGeometry.Space.LimitSituation.chartStagesCone_π_chartRestrictionAt` read as an
identity of homomorphisms rather than pointwise, with the composite
`Γ(X, 𝒪) ⟶ Γ(U, 𝒪)` allowed to be presented by any homomorphism equal to it; that freedom is
what lets it be used at the restriction homomorphism along the morphism of the site underlying
the limit chart.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 084U](https://stacks.math.columbia.edu/tag/084U)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 05WT](https://stacks.math.columbia.edu/tag/05WT)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_AffineStageDescentSteps :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_AffineStageDescentSteps
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The morphism of display 70.5.10.1 is locally of finite presentation -/

/-- **The morphism `f₀` of display 70.5.10.1 of the proof of Stacks 07SQ is locally of finite
presentation.** Its composite with the left vertical of the square of Stacks 084U is the étale
chart of the stage, which is locally of finite presentation by Stacks 0468, and that left
vertical is locally of finite type, so Stacks 05WT applies. -/
theorem isLocallyOfFinitePresentation_left_of_presentationBaseChange
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {Ai : Type u} [CommRing Ai] {n : ℕ} (gi : Fin n → MvPolynomial (Fin n) Ai)
    (p : X ⟶ schemePoints B S hS (Spec (CommRingCat.of Ai)))
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ X} (ha : IsEtale B S hS a)
    (f₀ : Over.mk a ⟶ Over.mk (pullback.fst p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom gi)))))) :
    IsLocallyOfFinitePresentation B S hS f₀.left := by
  have hw : f₀.left ≫ pullback.fst p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom gi)))) = a := Over.w f₀
  refine isLocallyOfFinitePresentation_of_comp B S hS
    (isAlgebraicSpace_yoneda B S hS U)
    (isAlgebraicSpace_pullback_schemePointsMap_Spec_map B S hS
      (CommRingCat.ofHom (presentationStructureHom gi))
      (RingHom.FiniteType.of_finitePresentation
        (finitePresentation_presentationStructureHom gi)) hX p)
    hX f₀.left (pullback.fst p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom gi))))) ?_ ?_
  · rw [hw]
    exact isLocallyOfFinitePresentation_atlas B S hS hX ha
  · exact isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (isLocallyOfFinitePresentation_pullback_fst_schemePointsMap_Spec_map B S hS
        (CommRingCat.ofHom (presentationStructureHom gi))
        (finitePresentation_presentationStructureHom gi) p)

/-! ### The categorical limit as the chosen limit of a descent situation -/

namespace DescentSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)]

/-- The same descent situation with the categorical limit of its inverse system for its chosen
limiting cone. -/
def atCanonicalLimit (D : DescentSituation B S hS hZ I) : DescentSituation B S hS hZ I :=
  { D with
    limitCone := limit.cone D.system
    isLimit := limit.isLimit D.system
    limitAlgebraicSpace := D.limitAlgebraicSpace.of_iso
      (D.isLimit.conePointUniqueUpToIso (limit.isLimit D.system)) }

/-- Normalising the limit cone leaves the inverse system unchanged. -/
@[simp]
theorem atCanonicalLimit_system (D : DescentSituation B S hS hZ I) :
    D.atCanonicalLimit.system = D.system := rfl

/-- Normalising the limit cone leaves the distinguished index unchanged. -/
@[simp]
theorem atCanonicalLimit_base (D : DescentSituation B S hS hZ I) :
    D.atCanonicalLimit.base = D.base := rfl

/-- The chosen limiting cone of the normalised descent situation is the categorical limit
cone. -/
@[simp]
theorem atCanonicalLimit_limitCone (D : DescentSituation B S hS hZ I) :
    D.atCanonicalLimit.limitCone = limit.cone D.system := rfl

end DescentSituation

/-! ### The base change of an affine source to a later stage -/

namespace MorphismDescentSystemOfChartsBounded

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)]

/-- **In Situation 084W with affine source, the base change of the source to a later stage is
affine.** That base change is the fibre product of the source with a stage over the
distinguished stage, so its projection to the source is a base change of a transition morphism
of the system and hence affine; an affine morphism with affine target has affine source. -/
theorem isAffineSpace_sourceAt (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (hsrc : IsAffineSpace B S hS D.source₀) (i : I) (hi : D.initial ≤ i) :
    IsAffineSpace B S hS (D.sourceAt i hi) :=
  (isAffineHom_of_isPullback (D.sourceAt_isPullback i hi)
    (D.transition_affine (homOfLE hi).op)).isAffineSpace_source hsrc

end MorphismDescentSystemOfChartsBounded

/-! ### The limit chart over a stage, and the two colimits -/

namespace LimitSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : LimitSituation B S hS hZ X)
  {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  (C : AffineChartSystem B S hS (op A.base) A.system U₀ f₀)
  (L : AffineChartSystem.LimitBridge C)
  (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))

/-- **The limit of a chart system is the fibre product of the limit algebraic space with the
chart of any one stage, over that stage.** This is
`AlgebraicGeometry.Space.AffineChartSystem.LimitBridge.isPullback_stage` transported along the
comparison of the categorical limit of the inverse system with the presheaf the situation is
attached to. -/
theorem isPullback_limitChartToSpace_stage (i : A.Stages) :
    IsPullback (A.limitChartToSpace C L)
      (yoneda.map (L.cone.π.app ((stagesOverEquivalence A).functor.obj (op i))))
      (A.π.app (op i.1)) (A.stagesEtaleChart C hf₀ i).1.hom :=
  (L.isPullback_stage ((stagesOverEquivalence A).functor.obj (op i))).of_iso'
    (Iso.refl _) A.limitIso.symm (Iso.refl _) (Iso.refl _)
    (by simp [limitChartToSpace]) (by simp)
    (by
      show A.limitIso.inv ≫ limit.π A.system (op i.1) = A.π.app (op i.1) ≫ 𝟙 _
      rw [Category.comp_id, ← A.limitIso_hom_comp_π (op i.1), Iso.inv_hom_id_assoc])
    (by
      show (𝟙 _) ≫ (A.stagesEtaleChart C hf₀ i).1.hom
        = (A.stagesEtaleChart C hf₀ i).1.hom ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id])

/-- **Restriction to the stage charts and passage to the limit commute**, as an identity of ring
homomorphisms: the restriction of the global functions of the limit to the limit chart, composed
with the homomorphism out of the model of a stage, is the restriction to the chart of that stage
followed by the projection of the limiting cone of the system of charts.

The restriction homomorphism at the limit is allowed to be presented by any homomorphism equal
to it, which is how the identity is used at the pullback of regular functions along the morphism
of the site underlying the limit chart. -/
theorem comp_modelProjection_eq_of_eq
    (hsurj : IsSurjective B S hS f₀) {R₀ : BigAffineFppf B S hS}
    {t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
      yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
    {s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀}
    (hpb : IsPullback t (yoneda.map s) f₀ f₀) (hX : IsAlgebraicSpace B S hS X)
    (hI : A.ChartsBounded) {Alim : Type u} [CommRing Alim]
    (eA : Alim ≃+* globalFunctions B S hS (A.limitSpace hX).obj)
    {ψl : Alim →+* Γ((A.chartStagesConeOfChartsBounded U₀ f₀ hI).pt, ⊤)}
    (hψl : (globalFunctionsChartRestriction B S hS (A.limitSpace hX)
        (A.limitEtaleChart (A.chartSystem U₀ f₀)
          (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI) hf₀)).comp
      eA.toRingHom = ψl) (i : A.Stages) :
    ψl.comp (A.modelProjection hX eA i)
      = (((A.chartStagesConeOfChartsBounded U₀ f₀ hI).π.app (op i)).appTop.hom).comp
        (A.chartRestrictionAt hf₀ i) := by
  subst hψl
  exact RingHom.ext fun x =>
    (A.chartStagesCone_π_chartRestrictionAt hf₀ hsurj hpb hX hI eA i x).symm

end LimitSituation

end AlgebraicGeometry.Space

end
