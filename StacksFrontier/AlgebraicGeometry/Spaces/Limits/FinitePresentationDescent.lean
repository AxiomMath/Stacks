module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Finite-presentation algebraic spaces over a limit with affine transitions

For a cofiltered inverse system of quasi-compact, quasi-separated algebraic spaces over `S`
whose transition morphisms are affine, base change along the projections from the limit
exhibits the category of algebraic spaces of finite presentation over the limit as the
colimit of the categories of algebraic spaces of finite presentation over the stages.

## Main results

* `AlgebraicGeometry.Space.exists_model_of_finitePresentation`: essential surjectivity — every
  algebraic space of finite presentation over the limit is a base change of one over a stage.
* `AlgebraicGeometry.Space.exists_morphism_after_baseChange`: fullness — a morphism between
  base changes comes from a morphism at a later stage.
* `AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq`: faithfulness — two morphisms of
  stage objects whose base changes to the limit agree already agree at a later stage.

## Implementation notes

The three statements express the filtered colimit of categories without choosing a strict
diagram of pullback functors. In the fullness statement the comparison isomorphisms are
pinned down by their maps to the original stage objects, which makes them the canonical
base-change comparisons. The cardinality hypotheses on the index category are those the big
fppf site needs in order to form the limit as an algebraic space.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! The two projections of an explicit fibre product out of a lift into it are not `simp`
lemmas in Mathlib, where `pullback.hom_ext` is the preferred interface; the explicit cones
built below are compared projection by projection throughout. -/

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

/-! ### Morphism-property interfaces

The descent below repeatedly needs that the inverse images of étaleness and surjectivity of
morphisms of schemes along the structure functor of the site are stable under composition and
respect isomorphisms. None of these is available to instance synthesis as stated, so each is
named once here.
-/

/-- Étaleness, pulled back along a functor to schemes, respects isomorphisms. -/
private theorem etaleInverseImageRespectsIso {C : Type*} [Category* C] (F : C ⥤ Scheme.{u}) :
    MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) F) :=
  MorphismProperty.RespectsIso.inverseImage _ F

/-- Surjectivity, pulled back along a functor to schemes, respects isomorphisms. -/
private theorem surjectiveInverseImageRespectsIso {C : Type*} [Category* C]
    (F : C ⥤ Scheme.{u}) :
    MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) F) :=
  MorphismProperty.RespectsIso.inverseImage _ F

/-- Étaleness, pulled back along a functor to schemes, is stable under composition. -/
private theorem etaleInverseImageIsStableUnderComposition {C : Type*} [Category* C]
    (F : C ⥤ Scheme.{u}) :
    MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) F) :=
  MorphismProperty.IsStableUnderComposition.inverseImage F

/-- The public form of the private `etaleInverseImageIsStableUnderComposition` above. -/
theorem FinitePresentationDescent.etaleInverseImageIsStableUnderComposition :
    ∀ {C : Type*} [Category* C]
    (F : C ⥤ Scheme.{u}),
    MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) F) :=
  @_root_.AlgebraicGeometry.Space.etaleInverseImageIsStableUnderComposition

/-- Surjectivity, pulled back along a functor to schemes, is stable under composition. -/
private theorem surjectiveInverseImageIsStableUnderComposition {C : Type*} [Category* C]
    (F : C ⥤ Scheme.{u}) :
    MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) F) :=
  have := AlgebraicGeometry.surjective_isStableUnderComposition.{u}
  MorphismProperty.IsStableUnderComposition.inverseImage F

/-- The public form of the private `surjectiveInverseImageIsStableUnderComposition` above. -/
theorem FinitePresentationDescent.surjectiveInverseImageIsStableUnderComposition :
    ∀ {C : Type*} [Category* C]
    (F : C ⥤ Scheme.{u}),
    MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) F) :=
  @_root_.AlgebraicGeometry.Space.surjectiveInverseImageIsStableUnderComposition

/-- A morphism property stable under composition induces a relatively representable property
of presheaves that is stable under composition. -/
private theorem presheafIsStableUnderComposition {C : Type*} [Category* C]
    (P : MorphismProperty C) (hP : P.IsStableUnderComposition) :
    P.presheaf.IsStableUnderComposition :=
  have := hP
  MorphismProperty.relative_isStableUnderComposition P

/-- The public form of the private `presheafIsStableUnderComposition` above. -/
theorem FinitePresentationDescent.presheafIsStableUnderComposition :
    ∀ {C : Type*} [Category* C]
    (P : MorphismProperty C) (_hP : P.IsStableUnderComposition),
    P.presheaf.IsStableUnderComposition :=
  @_root_.AlgebraicGeometry.Space.presheafIsStableUnderComposition

private instance schemeBelowPreservesCospan (B : AlgebraicGeometry.BigFppfSite.{u}) :
    PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance

private instance bigFppfOverHasPullbacks (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks (AlgebraicGeometry.BigFppfOver B S hS) := inferInstance

/-- Fibre products of presheaves on the site, resolved in one instance step.

Synthesising `HasPullback f g` for presheaves from `HasLimitsOfShape WalkingCospan` costs
about a tenth of a second each, and the descent below forms a few dozen such fibre products
in a single declaration. -/
private instance (priority := high) bigFppfPresheafHasPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPullback f g := HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Cospan-shaped limits of presheaves on the site (instance search times out without this
shortcut). -/
instance (priority := high) bigFppfPresheafHasLimitsOfShapeCospan_finitePresentationDescent
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasLimitsOfShape WalkingCospan ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- Limits of any cospan of presheaves on the site, also when the two legs' codomains agree
only up to unfolding (as for `Yᵢ.hom` with `Yᵢ : Over _`). -/
instance (priority := high) bigFppfPresheafHasLimitCospan_finitePresentationDescent
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : WalkingCospan ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasLimit F :=
  HasLimitsOfShape.has_limit F

set_option synthInstance.maxHeartbeats 400000 in
/-- Small products of presheaves on the site (instance search times out without this
shortcut). -/
instance (priority := high) bigFppfPresheafHasLimitsOfShapeDiscrete_finitePresentationDescent
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (J : Type) :
    HasLimitsOfShape (Discrete J) ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

private theorem relationTarget_prodLift {S : Scheme.{u}} {R U : Over S}
    (s t : R ⟶ U) :
    Stacks.Groupoids.PreRelation.target (prod.lift s t) = s := by
  dsimp [Stacks.Groupoids.PreRelation.target]
  rw [prod.lift_fst]

private theorem relationSource_prodLift {S : Scheme.{u}} {R U : Over S}
    (s t : R ⟶ U) :
    Stacks.Groupoids.PreRelation.source (prod.lift s t) = t := by
  dsimp [Stacks.Groupoids.PreRelation.source]
  rw [prod.lift_snd]

private theorem exists_affine_etale_atlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hQc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X) :
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
        AlgebraicGeometry.Space.IsEtale B S hS p :=
  (AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
    B S hS X hX).mp hQc



/-- The public form of the private `exists_affine_etale_atlas` above. -/
theorem FinitePresentationDescent.exists_affine_etale_atlas :
    ∀ (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (_hQc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X),
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
        AlgebraicGeometry.Space.IsEtale B S hS p :=
  @_root_.AlgebraicGeometry.Space.exists_affine_etale_atlas

private noncomputable def algebraicSpacePresentation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X) :
    AlgebraicGeometry.Space.Presentation B S hS X hX := by
  let U : AlgebraicGeometry.BigFppfOver B S hS := Classical.choose hX.exists_atlas
  let q : yoneda.obj U ⟶ X := Classical.choose (Classical.choose_spec hX.exists_atlas)
  have hAtlas := Classical.choose_spec (Classical.choose_spec hX.exists_atlas)
  let hqSurj := hAtlas.1
  let hqEtale := hAtlas.2
  let K := atlasKernelPair B S hS q hX.diagonal_representable
  let j : Stacks.Groupoids.PreRelation ((Over.post B.inclusion).obj K.R)
      ((Over.post B.inclusion).obj U) :=
    AlgebraicGeometry.Space.relation B S hS K.t K.s
  have hTarget : j.target = (Over.post B.inclusion).map K.s :=
    relationTarget_prodLift _ _
  have hSource : j.source = (Over.post B.inclusion).map K.t :=
    relationSource_prodLift _ _
  have hRel : IsEquivalenceRelation
      ((Over.post B.inclusion).map K.s) ((Over.post B.inclusion).map K.t) :=
    AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback B S hS q K.s K.t K.kernelPair
  have hTargetEtale : Etale
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.s) :=
    hqEtale.property q (yoneda.map K.t) K.s K.kernelPair.flip
  have hSourceEtale : Etale
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.t) :=
    hqEtale.property q (yoneda.map K.s) K.t K.kernelPair
  letI : Stacks.Groupoids.IsEtaleEquivalenceRelation j := {
    isEquivalenceRelation := by
      rw [hTarget, hSource]
      exact hRel
    etale_source := by
      rw [hSource]
      simpa [AlgebraicGeometry.BigFppfOver.toScheme, AlgebraicGeometry.BigFppfOver.forget,
        Over.post] using hSourceEtale
    etale_target := by
      rw [hTarget]
      simpa [AlgebraicGeometry.BigFppfOver.toScheme, AlgebraicGeometry.BigFppfOver.forget,
        Over.post] using hTargetEtale
  }
  exact {
    U := U
    R := K.R
    target := K.s
    source := K.t
    isEtaleEquivalenceRelation := by
      change Stacks.Groupoids.IsEtaleEquivalenceRelation j
      infer_instance
    toSpace := q
    surjective := hqSurj
    etale := hqEtale
    isPullback := K.kernelPair
  }

private theorem represented_etale_of_isEtale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS} (p : yoneda.obj U ⟶ F)
    (hp : AlgebraicGeometry.Space.IsEtale B S hS p) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p := by
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.RespectsIso := etaleInverseImageRespectsIso _
  have hid : P.presheaf (𝟙 (yoneda.obj U)) := by
    apply MorphismProperty.relative.of_exists
    intro V g
    refine ⟨V, g, 𝟙 V, ?_, ?_⟩
    · simpa using (IsPullback.id_horiz g).flip
    · show Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (𝟙 V))
      infer_instance
  simpa using hp U (𝟙 _) hid

/-- The public form of the private `represented_etale_of_isEtale` above. -/
theorem FinitePresentationDescent.represented_etale_of_isEtale :
    ∀ (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS} (p : yoneda.obj U ⟶ F)
    (_hp : AlgebraicGeometry.Space.IsEtale B S hS p),
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p :=
  @_root_.AlgebraicGeometry.Space.represented_etale_of_isEtale

private theorem precomp_eq_of_baseChange_eq
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' : C} (p : X' ⟶ X) (Y Z : Over X) (f g : Y ⟶ Z)
    (hfg : (Over.pullback p).map f = (Over.pullback p).map g)
    {T : C} (q : T ⟶ Y.left) :
    pullback.snd p (q ≫ Y.hom) ≫ q ≫ f.left =
      pullback.snd p (q ≫ Y.hom) ≫ q ≫ g.left := by
  let k : pullback p (q ≫ Y.hom) ⟶ pullback Y.hom p :=
    pullback.lift (pullback.snd _ _ ≫ q) (pullback.fst _ _)
      (by simp only [Category.assoc, pullback.condition])
  have hh := congrArg (fun e : (Over.pullback p).obj Y ⟶ (Over.pullback p).obj Z =>
    k ≫ e.left ≫ pullback.fst Z.hom p) hfg
  simpa [k, Over.pullback_map_left, Category.assoc] using hh

/-- The public form of the private `precomp_eq_of_baseChange_eq` above. -/
theorem FinitePresentationDescent.precomp_eq_of_baseChange_eq :
    ∀ {C : Type*} [Category* C] [HasPullbacks C]
    {X X' : C} (p : X' ⟶ X) (Y Z : Over X) (f g : Y ⟶ Z)
    (_hfg : (Over.pullback p).map f = (Over.pullback p).map g)
    {T : C} (q : T ⟶ Y.left),
    pullback.snd p (q ≫ Y.hom) ≫ q ≫ f.left =
      pullback.snd p (q ≫ Y.hom) ≫ q ≫ g.left :=
  @_root_.AlgebraicGeometry.Space.precomp_eq_of_baseChange_eq

private theorem hom_ext_of_surjective_etale_atlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) G)
    {U : AlgebraicGeometry.BigFppfOver B S hS} (p : yoneda.obj U ⟶ F)
    (hp : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (f g : F ⟶ G) (hfg : p ≫ f = p ≫ g) : f = g := by
  let K := atlasKernelPair B S hS p hF.diagonal_representable
  obtain ⟨hR, hU, ⟨hc⟩⟩ := AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale
    B S hS p K.s K.t K.kernelPair hF hp he
  let pp : (⟨yoneda.obj U, hU⟩ : Sheaf _ (Type u)) ⟶ ⟨F, hF.isSheaf⟩ := ⟨p⟩
  let ff : (⟨F, hF.isSheaf⟩ : Sheaf _ (Type u)) ⟶ ⟨G, hG⟩ := ⟨f⟩
  let gg : (⟨F, hF.isSheaf⟩ : Sheaf _ (Type u)) ⟶ ⟨G, hG⟩ := ⟨g⟩
  have : Epi pp := epi_of_isColimit_cofork hc
  have hh : pp ≫ ff = pp ≫ gg := Sheaf.hom_ext hfg
  exact congrArg (fun k : (⟨F, hF.isSheaf⟩ : Sheaf _ (Type u)) ⟶ ⟨G, hG⟩ => k.hom)
    ((cancel_epi pp).mp hh)

/- The algebraic-space proof reduces finite presentation to descent for scheme
   charts.  Keep the scheme-level interface here in the exact shape used by
   the chart diagrams below. -/
private theorem scheme_model_of_finitePresentation
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (E : I ⥤ Scheme.{u}) (c : Cone E) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (E.map f)]
    [∀ i, CompactSpace (E.obj i)]
    [∀ i, QuasiSeparatedSpace (E.obj i)]
    (X : Over c.pt) (hFp : AlgebraicGeometry.FinitePresentation X.hom) :
    ∃ (i : I) (Xᵢ : Over (E.obj i)),
      AlgebraicGeometry.FinitePresentation Xᵢ.hom ∧
        Nonempty (X ≅ (Over.pullback (c.π.app i)).obj Xᵢ) :=
  AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation E c hc X hFp

/-- The public form of the private `scheme_model_of_finitePresentation` above. -/
theorem FinitePresentationDescent.scheme_model_of_finitePresentation :
    ∀ {I : Type u} [Category.{u} I] [IsCofiltered I]
    (E : I ⥤ Scheme.{u}) (c : Cone E) (_hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (E.map f)]
    [∀ i, CompactSpace (E.obj i)]
    [∀ i, QuasiSeparatedSpace (E.obj i)]
    (X : Over c.pt) (_hFp : AlgebraicGeometry.FinitePresentation X.hom),
    ∃ (i : I) (Xᵢ : Over (E.obj i)),
      AlgebraicGeometry.FinitePresentation Xᵢ.hom ∧
        Nonempty (X ≅ (Over.pullback (c.π.app i)).obj Xᵢ) :=
  @_root_.AlgebraicGeometry.Space.scheme_model_of_finitePresentation

/-- The public form of the private `hom_ext_of_surjective_etale_atlas` above. -/
theorem FinitePresentationDescent.hom_ext_of_surjective_etale_atlas :
    ∀ (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (_hG : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) G)
    {U : AlgebraicGeometry.BigFppfOver B S hS} (p : yoneda.obj U ⟶ F)
    (_hp : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (_he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (f g : F ⟶ G) (_hfg : p ≫ f = p ≫ g),
    f = g :=
  @_root_.AlgebraicGeometry.Space.hom_ext_of_surjective_etale_atlas

private theorem scheme_morphism_after_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (E : I ⥤ Scheme.{u}) (c : Cone E) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (E.map f)]
    [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)]
    (i : I) (X Y : Over (E.obj i))
    (hX : AlgebraicGeometry.FinitePresentation X.hom)
    (hY : AlgebraicGeometry.FinitePresentation Y.hom)
    (f : (Over.pullback (c.π.app i)).obj X ⟶
      (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (E.map e)).obj X ⟶ (Over.pullback (E.map e)).obj Y)
      (α : (Over.pullback (c.π.app j)).obj ((Over.pullback (E.map e)).obj X) ≅
        (Over.pullback (c.π.app i)).obj X)
      (β : (Over.pullback (c.π.app j)).obj ((Over.pullback (E.map e)).obj Y) ≅
        (Over.pullback (c.π.app i)).obj Y),
      α.hom.left ≫ pullback.fst X.hom (c.π.app i) =
          pullback.fst ((Over.pullback (E.map e)).obj X).hom (c.π.app j) ≫
            pullback.fst X.hom (E.map e) ∧
        β.hom.left ≫ pullback.fst Y.hom (c.π.app i) =
          pullback.fst ((Over.pullback (E.map e)).obj Y).hom (c.π.app j) ≫
            pullback.fst Y.hom (E.map e) ∧
        α.hom ≫ f = (Over.pullback (c.π.app j)).map g ≫ β.hom :=
  AlgebraicGeometry.exists_morphism_after_baseChange E c hc i X Y hX hY f

private theorem scheme_eventually_eq_of_baseChange_eq
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (E : I ⥤ Scheme.{u}) (c : Cone E) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (E.map f)]
    [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)]
    (i : I) (X Y : Over (E.obj i))
    (hX : AlgebraicGeometry.FinitePresentation X.hom)
    (hY : AlgebraicGeometry.FinitePresentation Y.hom)
    (f g : X ⟶ Y)
    (hfg : (Over.pullback (c.π.app i)).map f =
      (Over.pullback (c.π.app i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (E.map e)).map f = (Over.pullback (E.map e)).map g :=
  AlgebraicGeometry.Scheme.eventually_eq_of_baseChange_eq E c hc i X Y hX hY f g hfg

private noncomputable def isLimit_of_cartesian_cone
    {C : Type*} [Category* C] [HasPullbacks C]
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ C) [HasLimit D] (i : J) (T : C) (g : T ⟶ D.obj i)
    (E : Over i ⥤ C) (c : Cone E)
    (p : E ⟶ Over.forget i ⋙ D) (q : E ⟶ (Functor.const _).obj T)
    (hp : ∀ j, IsPullback (p.app j) (q.app j) (D.map j.hom) g)
    (pL : c.pt ⟶ limit D) (qL : c.pt ⟶ T)
    (hL : IsPullback pL qL (limit.π D i) g)
    (hc₁ : ∀ j, c.π.app j ≫ p.app j = pL ≫ limit.π D j.left)
    (hc₂ : ∀ j, c.π.app j ≫ q.app j = qL) : IsLimit c := by
  let : IsConnected (Over i) := IsCofiltered.isConnected _
  let P := (Over.post D) ⋙ Over.pullback g ⋙ Over.forget T
  let e : E ≅ P := NatIso.ofComponents (fun j => (hp j).isoPullback) (by
    intro j k f
    apply pullback.hom_ext
    · change (E.map f ≫ (hp k).isoPullback.hom) ≫ pullback.fst (D.map k.hom) g =
        ((hp j).isoPullback.hom ≫
          pullback.lift (pullback.fst (D.map j.hom) g ≫ D.map f.left)
            (pullback.snd (D.map j.hom) g)
            (by rw [Category.assoc, ← D.map_comp, Over.w f]; exact pullback.condition)) ≫
          pullback.fst (D.map k.hom) g
      simp only [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst,
        IsPullback.isoPullback_hom_fst_assoc]
      exact p.naturality f
    · change (E.map f ≫ (hp k).isoPullback.hom) ≫ pullback.snd (D.map k.hom) g =
        ((hp j).isoPullback.hom ≫
          pullback.lift (pullback.fst (D.map j.hom) g ≫ D.map f.left)
            (pullback.snd (D.map j.hom) g)
            (by rw [Category.assoc, ← D.map_comp, Over.w f]; exact pullback.condition)) ≫
          pullback.snd (D.map k.hom) g
      simp only [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
      simp)
  let cP := (Over.forget T).mapCone ((Over.pullback g).mapCone ((limit.cone D).overPost i))
  have hcP : IsLimit cP := isLimitOfPreserves (Over.forget T)
    (isLimitOfPreserves (Over.pullback g) ((limit.isLimit D).overPost i))
  apply (IsLimit.postcomposeHomEquiv e c).toFun
  apply hcP.ofIsoLimit
  apply Iso.symm
  refine Cone.ext hL.isoPullback ?_
  intro j
  apply pullback.hom_ext
  · change (c.π.app j ≫ (hp j).isoPullback.hom) ≫ pullback.fst _ _ =
      (hL.isoPullback.hom ≫ (pullback.lift (pullback.fst (limit.π D i) g ≫ limit.π D j.left)
          (pullback.snd (limit.π D i) g)
          (by rw [Category.assoc, limit.w]; exact pullback.condition))) ≫
        pullback.fst (D.map j.hom) g
    simp only [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst,
      IsPullback.isoPullback_hom_fst_assoc]
    exact hc₁ j
  · change (c.π.app j ≫ (hp j).isoPullback.hom) ≫ pullback.snd _ _ =
      (hL.isoPullback.hom ≫ (pullback.lift (pullback.fst (limit.π D i) g ≫ limit.π D j.left)
          (pullback.snd (limit.π D i) g)
          (by rw [Category.assoc, limit.w]; exact pullback.condition))) ≫
        pullback.snd (D.map j.hom) g
    simp only [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
    exact hc₂ j

private theorem hasLimit_of_affine_diagram
    {J : Type u} [Category.{u} J] (E : J ⥤ Scheme.{u})
    [∀ j, IsAffine (E.obj j)] : HasLimit E := by
  let α : E ⟶ (E ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec :=
    E.whiskerLeft ΓSpec.adjunction.unit
  have (j : J) : IsIso (α.app j) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact hasLimit_of_iso (asIso α).symm

/-- An affine inverse limit stays below a cutoff when its index is smaller
than the cutoff's cofinality. -/
private theorem size_lt_of_affine_limit
    {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (hJ : Cardinal.mk J < κ.ord.cof)
    (E : J ⥤ Scheme.{u}) [∀ j, IsAffine (E.obj j)]
    (c : Cone E) (hc : IsLimit c) (hE : ∀ j, (E.obj j).size < κ) :
    c.pt.size < κ := by
  classical
  let : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  rw [Scheme.size_of_isAffine]
  refine max_lt hκ ?_
  let f : (Σ j, Γ(E.obj j, ⊤)) → Γ(c.pt, ⊤) :=
    fun x => (c.π.app x.1).appTop x.2
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨j, y, hy⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit E c hc x
    exact ⟨⟨j, y⟩, hy⟩
  apply (Cardinal.mk_le_of_surjective hf).trans_lt
  rw [Cardinal.mk_sigma]
  apply (Cardinal.sum_le_mk_mul_iSup _).trans_lt
  apply Cardinal.mul_lt_of_lt hκ.le (hJ.trans_le (Ordinal.cof_ord_le _))
  apply Cardinal.iSup_lt_of_lt_cof_ord hJ
  intro j
  exact ((E.obj j).mk_sections_le_size ⟨⊤, isAffineOpen_top _⟩).trans_lt (hE j)

private theorem cardinalMk_over_lt
    (B : AlgebraicGeometry.BigFppfSite.{u})
    {J : Type u} [Category.{u} J]
    (hJ : Cardinal.mk J < B.cutoff.ord.cof)
    (hHom : ∀ j k : J, Cardinal.mk (j ⟶ k) < B.cutoff.ord.cof) (i : J) :
    Cardinal.mk (Over i) < B.cutoff.ord.cof := by
  let f : Over i → Σ j : J, j ⟶ i := fun j => ⟨j.left, j.hom⟩
  have hf : Function.Injective f := by
    rintro ⟨j, ⟨⟩, a⟩ ⟨k, ⟨⟩, b⟩ h
    cases h
    rfl
  apply (Cardinal.mk_le_of_injective hf).trans_lt
  rw [Cardinal.mk_sigma]
  exact Cardinal.sum_lt_of_isRegular
    (Cardinal.isRegular_cof (Cardinal.isSuccLimit_ord B.aleph0_lt_cutoff.le))
    hJ (fun j => hHom j i)

private theorem preservesLimit_bounded_affine_diagram
    (B : AlgebraicGeometry.BigFppfSite.{u})
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (hJ : Cardinal.mk J < B.cutoff.ord.cof) (E : J ⥤ B.Schemes)
    [∀ j, IsAffine (B.inclusion.obj (E.obj j))] :
    PreservesLimit E B.inclusion := by
  let : ∀ j, IsAffine ((E ⋙ B.inclusion).obj j) :=
    fun j => (inferInstance : IsAffine (B.inclusion.obj (E.obj j)))
  let : HasLimit (E ⋙ B.inclusion) := hasLimit_of_affine_diagram _
  have hL : (limit (E ⋙ B.inclusion)).size < B.cutoff :=
    size_lt_of_affine_limit B.aleph0_lt_cutoff hJ _ _ (limit.isLimit _)
      (fun j => (E.obj j).property)
  let : CreatesLimit E B.inclusion :=
    createsLimitOfFullyFaithfulOfIso ⟨limit (E ⋙ B.inclusion), hL⟩ (Iso.refl _)
  let : HasLimit E := hasLimit_of_created E B.inclusion
  infer_instance

private noncomputable def isLimit_toScheme_of_affine
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (hJ : Cardinal.mk J < B.cutoff.ord.cof)
    (E : J ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j)))
    (c : Cone E) (hc : IsLimit c) :
    IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c) := by
  let : IsConnected J := IsCofiltered.isConnected J
  let : ∀ j, IsAffine (B.inclusion.obj ((E ⋙ Over.forget (B.obj hS)).obj j)) := hE
  let : PreservesLimit (E ⋙ Over.forget (B.obj hS)) B.inclusion :=
    preservesLimit_bounded_affine_diagram B hJ _
  exact isLimitOfPreserves (AlgebraicGeometry.BigFppfOver.toScheme B S hS) hc

/-- Equality of sections of a limit-preserving presheaf is detected at a stage. -/
private theorem eventually_eq_of_limitPreserving
    {C : Type (u + 1)} [Category.{u} C] (toScheme : C ⥤ Scheme.{u})
    (F : Cᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.LimitPreserving.{u, u, u, u} toScheme F)
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ C) (c : Cone E) (hc : IsLimit (toScheme.mapCone c))
    (hE : ∀ j, IsAffine (toScheme.obj (E.obj j)))
    (hPt : IsAffine (toScheme.obj c.pt)) (j : J) (x y : F.obj (.op (E.obj j)))
    (hxy : F.map (c.π.app j).op x = F.map (c.π.app j).op y) :
    ∃ (k : J) (e : k ⟶ j), F.map (E.map e).op x = F.map (E.map e).op y := by
  obtain ⟨hcolim⟩ := hF J E c hc hE hPt
  obtain ⟨k, e, he⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' hcolim x y).mp hxy
  exact ⟨k.unop, e.unop, he⟩

/-- A lift of a section over an affine limit is defined at a finite stage. -/
private theorem exists_section_of_locallyOfFinitePresentation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (a : F ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (T : AlgebraicGeometry.BigFppfOver B S hS) (t : G.obj (.op T))
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Over T) (c : Cone E)
    (hc : IsLimit ((Over.forget T ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c))
    (hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (E.obj j).left))
    (hPt : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj c.pt.left))
    (x : F.obj (.op c.pt.left)) (hx : a.app _ x = G.map c.pt.hom.op t) :
    ∃ (j : J) (y : F.obj (.op (E.obj j).left)),
      a.app _ y = G.map (E.obj j).hom.op t ∧ F.map (c.π.app j).left.op y = x := by
  have hpres :=
    AlgebraicGeometry.relativelyLimitPreserving_of_isLocallyOfFinitePresentation
      B S hS hF hG ha T t
  obtain ⟨hcolim⟩ := hpres J E c hc hE hPt
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcolim
    (⟨x, hx⟩ : (AlgebraicGeometry.sectionFiber B S hS a T t).obj (.op c.pt))
  exact ⟨j.unop, y.val, y.property, congrArg Subtype.val hy⟩

private theorem exists_hom_of_locallyOfFinitePresentation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (a : F ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (T : AlgebraicGeometry.BigFppfOver B S hS) (t : yoneda.obj T ⟶ G)
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Over T) (c : Cone E)
    (hc : IsLimit ((Over.forget T ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c))
    (hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (E.obj j).left))
    (hPt : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj c.pt.left))
    (f : yoneda.obj c.pt.left ⟶ F) (hf : f ≫ a = yoneda.map c.pt.hom ≫ t) :
    ∃ (j : J) (g : yoneda.obj (E.obj j).left ⟶ F),
      g ≫ a = yoneda.map (E.obj j).hom ≫ t ∧
        yoneda.map (c.π.app j).left ≫ g = f := by
  have hx : a.app _ (yonedaEquiv f) = G.map c.pt.hom.op (yonedaEquiv t) := by
    rw [← yonedaEquiv_comp, yonedaEquiv_naturality, hf]
  obtain ⟨j, y, hy, he⟩ := exists_section_of_locallyOfFinitePresentation
    B S hS hF hG a ha T (yonedaEquiv t) E c hc hE hPt (yonedaEquiv f) hx
  refine ⟨j, yonedaEquiv.symm y, yonedaEquiv.injective ?_, yonedaEquiv.injective ?_⟩
  · rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← yonedaEquiv_naturality]
    exact hy
  · simpa only [← yonedaEquiv_naturality, Equiv.apply_symm_apply] using he

/-- The public form of the private `exists_hom_of_locallyOfFinitePresentation` above. -/
theorem FinitePresentationDescent.exists_hom_of_locallyOfFinitePresentation :
    ∀ (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (_hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (a : F ⟶ G)
    (_ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (T : AlgebraicGeometry.BigFppfOver B S hS) (t : yoneda.obj T ⟶ G)
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Over T) (c : Cone E)
    (_hc : IsLimit ((Over.forget T ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c))
    (_hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (E.obj j).left))
    (_hPt : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj c.pt.left))
    (f : yoneda.obj c.pt.left ⟶ F) (_hf : f ≫ a = yoneda.map c.pt.hom ≫ t),
    ∃ (j : J) (g : yoneda.obj (E.obj j).left ⟶ F),
      g ≫ a = yoneda.map (E.obj j).hom ≫ t ∧
        yoneda.map (c.π.app j).left ≫ g = f :=
  @_root_.AlgebraicGeometry.Space.exists_hom_of_locallyOfFinitePresentation

/-- Relative local finite presentation detects equality of lifts on affine limits. -/
private theorem eventually_eq_sections_of_locallyOfFinitePresentation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (a : F ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (T : AlgebraicGeometry.BigFppfOver B S hS) (t : G.obj (.op T))
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Over T) (c : Cone E)
    (hc : IsLimit ((Over.forget T ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c))
    (hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (E.obj j).left))
    (hPt : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj c.pt.left))
    (j : J) (x y : F.obj (.op (E.obj j).left))
    (hx : a.app _ x = G.map (E.obj j).hom.op t)
    (hy : a.app _ y = G.map (E.obj j).hom.op t)
    (hxy : F.map (c.π.app j).left.op x = F.map (c.π.app j).left.op y) :
    ∃ (k : J) (e : k ⟶ j),
      F.map (E.map e).left.op x = F.map (E.map e).left.op y := by
  have hpres :=
    AlgebraicGeometry.relativelyLimitPreserving_of_isLocallyOfFinitePresentation
      B S hS hF hG ha T t
  obtain ⟨k, e, he⟩ := eventually_eq_of_limitPreserving _ _ hpres E c hc hE hPt j
    (⟨x, hx⟩ : (AlgebraicGeometry.sectionFiber B S hS a T t).obj (.op (E.obj j)))
    ⟨y, hy⟩ (Subtype.ext hxy)
  exact ⟨k, e, congrArg Subtype.val he⟩

private theorem eventually_eq_homs_of_locallyOfFinitePresentation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (a : F ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (T : AlgebraicGeometry.BigFppfOver B S hS) (t : yoneda.obj T ⟶ G)
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Over T) (c : Cone E)
    (hc : IsLimit ((Over.forget T ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c))
    (hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (E.obj j).left))
    (hPt : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj c.pt.left))
    (f g : yoneda.obj T ⟶ F) (hf : f ≫ a = t) (hg : g ≫ a = t)
    (hfg : yoneda.map c.pt.hom ≫ f = yoneda.map c.pt.hom ≫ g) :
    ∃ j : J, yoneda.map (E.obj j).hom ≫ f = yoneda.map (E.obj j).hom ≫ g := by
  classical
  let j : J := Classical.choice IsCofiltered.nonempty
  let x := yonedaEquiv (yoneda.map (E.obj j).hom ≫ f)
  let y := yonedaEquiv (yoneda.map (E.obj j).hom ≫ g)
  have hx : a.app _ x = G.map (E.obj j).hom.op (yonedaEquiv t) := by
    simp [x, ← yonedaEquiv_comp, yonedaEquiv_naturality, Category.assoc, hf]
  have hy : a.app _ y = G.map (E.obj j).hom.op (yonedaEquiv t) := by
    simp [y, ← yonedaEquiv_comp, yonedaEquiv_naturality, Category.assoc, hg]
  have hxy : F.map (c.π.app j).left.op x = F.map (c.π.app j).left.op y := by
    simpa [x, y, yonedaEquiv_naturality, ← Category.assoc, ← yoneda.map_comp] using
      congrArg yonedaEquiv hfg
  obtain ⟨k, e, he⟩ := eventually_eq_sections_of_locallyOfFinitePresentation
    B S hS hF hG a ha T (yonedaEquiv t) E c hc hE hPt j x y hx hy hxy
  refine ⟨k, yonedaEquiv.injective ?_⟩
  simpa [x, y, yonedaEquiv_naturality, ← Category.assoc, ← yoneda.map_comp] using he

/-- The public form of the private `eventually_eq_homs_of_locallyOfFinitePresentation` above. -/
theorem FinitePresentationDescent.eventually_eq_homs_of_locallyOfFinitePresentation :
    ∀ (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (_hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (a : F ⟶ G)
    (_ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (T : AlgebraicGeometry.BigFppfOver B S hS) (t : yoneda.obj T ⟶ G)
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Over T) (c : Cone E)
    (_hc : IsLimit ((Over.forget T ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c))
    (_hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (E.obj j).left))
    (_hPt : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj c.pt.left))
    (f g : yoneda.obj T ⟶ F) (_hf : f ≫ a = t) (_hg : g ≫ a = t)
    (_hfg : yoneda.map c.pt.hom ≫ f = yoneda.map c.pt.hom ≫ g),
    ∃ j : J, yoneda.map (E.obj j).hom ≫ f = yoneda.map (E.obj j).hom ≫ g :=
  @_root_.AlgebraicGeometry.Space.eventually_eq_homs_of_locallyOfFinitePresentation

private theorem exists_affine_finitePresentation_chart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (f : Y ⟶ X) (hf : AlgebraicGeometry.Space.IsFinitePresentation B S hS f)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ X)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p) :
    ∃ (W : AlgebraicGeometry.BigAffineFppf B S hS) (q : yoneda.obj W.obj ⟶ Y) (g : W.obj ⟶ U.obj),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q ∧
      yoneda.map g ≫ p = q ≫ f ∧
      AlgebraicGeometry.FinitePresentation
          ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) := by
  have hU := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U.obj
  have hV := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS p f hU hY hX
  have hVqc := hf.2.1 (yoneda.obj U.obj) hU
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS U.obj U.property) p
  obtain ⟨W, q, hW, hqs, hqe⟩ := exists_affine_etale_atlas B S hS (pullback p f) hV hVqc
  let g := yoneda.preimage (q ≫ pullback.fst p f)
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  have hqes : Q.presheaf (q ≫ pullback.snd p f) :=
    Q.presheaf.comp_mem _ _ (represented_etale_of_isEtale B S hS q hqe)
      (Q.presheaf.of_isPullback (IsPullback.of_hasPullback p f) he)
  have hw : yoneda.map g ≫ p = (q ≫ pullback.snd p f) ≫ f := by
    simp [g, Category.assoc, pullback.condition]
  refine ⟨⟨W, hW⟩, q ≫ pullback.snd p f, g,
    P.presheaf.comp_mem _ _ hqs (P.presheaf.of_isPullback (IsPullback.of_hasPullback p f) hs),
    hqes, hw, hf.1 W U.obj _ p g hqes he hw, ?_, ?_⟩
  · let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W) := hW
    let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U.obj) := U.property
    infer_instance
  · let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W) := hW
    infer_instance


/-- The public form of the private `exists_affine_finitePresentation_chart` above. -/
theorem FinitePresentationDescent.exists_affine_finitePresentation_chart :
    ∀ (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (_hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (f : Y ⟶ X) (_hf : AlgebraicGeometry.Space.IsFinitePresentation B S hS f)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ X)
    (_hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (_he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p),
    ∃ (W : AlgebraicGeometry.BigAffineFppf B S hS) (q : yoneda.obj W.obj ⟶ Y) (g : W.obj ⟶ U.obj),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q ∧
      yoneda.map g ≫ p = q ≫ f ∧
      AlgebraicGeometry.FinitePresentation
          ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) :=
  @_root_.AlgebraicGeometry.Space.exists_affine_finitePresentation_chart

private theorem atlasKernelPair_compactSpace
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hYqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (W : AlgebraicGeometry.BigAffineFppf B S hS) (w : yoneda.obj W.obj ⟶ Y) :
    CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (atlasKernelPair B S hS w hY.diagonal_representable).R) := by
  let K := atlasKernelPair B S hS w hY.diagonal_representable
  have hW := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W.obj
  have hWqc := isQuasiCompactSpace_yoneda_of_isAffine B S hS W.obj W.property
  have hKqc :=
    AlgebraicGeometry.Space.isQuasiCompactSpace_pullback
      B S hS hZ w w hW hY hWqc hWqc hYqs
  exact AlgebraicGeometry.Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
    (U := K.R) (isQuasiCompactSpace_of_iso B S hS K.kernelPair.isoPullback.symm hKqc)

private theorem atlasKernelPair_isSeparated
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (W : AlgebraicGeometry.BigAffineFppf B S hS) (w : yoneda.obj W.obj ⟶ Y) :
    Scheme.IsSeparated ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (atlasKernelPair B S hS w hY.diagonal_representable).R) := by
  let K := atlasKernelPair B S hS w hY.diagonal_representable
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let F : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let r := (AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback B S hS w
    K.s K.t K.kernelPair).nonempty_equivalenceRelation.some
  let p : Q.obj K.R ⟶ pullback (terminal.from (Q.obj W.obj)) (terminal.from (Q.obj W.obj)) :=
    pullback.lift (Q.map K.s) (Q.map K.t) (by simp)
  have hp : Mono p := ⟨by
    intro T a b hab
    have ht : a ≫ Q.map K.s = b ≫ Q.map K.s := by
      simpa [p, Category.assoc] using congrArg
          (fun t => t ≫ pullback.fst (terminal.from (Q.obj W.obj)) _) hab
    have hs : a ≫ Q.map K.t = b ≫ Q.map K.t := by
      simpa [p, Category.assoc] using congrArg
          (fun t => t ≫ pullback.snd (terminal.from (Q.obj W.obj)) _) hab
    let a₁ : T ⟶ (F.obj K.R).left := a
    let b₁ : T ⟶ (F.obj K.R).left := b
    have ht₁ : a₁ ≫ (F.map K.s).left = b₁ ≫ (F.map K.s).left := ht
    have hbase : a ≫ (F.obj K.R).hom = b ≫ (F.obj K.R).hom := by
      have hb : a₁ ≫ (F.obj K.R).hom = b₁ ≫ (F.obj K.R).hom := by
        rw [← Over.w (F.map K.s), ← Category.assoc, ← Category.assoc, ht₁]
      exact hb
    let a' : Over.mk (a ≫ (F.obj K.R).hom) ⟶ F.obj K.R := Over.homMk a
    let b' : Over.mk (a ≫ (F.obj K.R).hom) ⟶ F.obj K.R := Over.homMk b hbase.symm
    have he : a' = b' := r.right_cancellation a' b'
      (Over.OverMorphism.ext ht) (Over.OverMorphism.ext hs)
    exact congrArg (fun t => t.left) he⟩
  let : IsAffine (Q.obj W.obj) := W.property
  show Scheme.IsSeparated (Q.obj K.R)
  refine ⟨?_⟩
  have : _root_.AlgebraicGeometry.IsSeparated (p ≫ pullback.fst (terminal.from (Q.obj W.obj))
      (terminal.from (Q.obj W.obj)) ≫ terminal.from (Q.obj W.obj)) := inferInstance
  simpa only [terminal.comp_from] using this

private theorem atlasKernelPair_target_finitePresentation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hYqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (W : AlgebraicGeometry.BigAffineFppf B S hS) (w : yoneda.obj W.obj ⟶ Y)
    (hw : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w) :
    AlgebraicGeometry.FinitePresentation ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (atlasKernelPair B S hS w hY.diagonal_representable).s) := by
  let K := atlasKernelPair B S hS w hY.diagonal_representable
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : Etale (Q.map K.s) := hw.property w (yoneda.map K.t)
    K.s K.kernelPair.flip
  let : IsAffine (Q.obj W.obj) := W.property
  let : CompactSpace (Q.obj K.R) := atlasKernelPair_compactSpace B S hS hZ hY hYqs W w
  let : Scheme.IsSeparated (Q.obj K.R) := atlasKernelPair_isSeparated B S hS hY W w
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The public form of the private `atlasKernelPair_target_finitePresentation` above. -/
theorem FinitePresentationDescent.atlasKernelPair_target_finitePresentation :
    ∀ (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (_hYqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (W : AlgebraicGeometry.BigAffineFppf B S hS) (w : yoneda.obj W.obj ⟶ Y)
    (_hw : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w),
    AlgebraicGeometry.FinitePresentation ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (atlasKernelPair B S hS w hY.diagonal_representable).s) :=
  @_root_.AlgebraicGeometry.Space.atlasKernelPair_target_finitePresentation

private theorem isQuasiSeparated_yoneda
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (W : AlgebraicGeometry.BigFppfOver B S hS)
    (hW : QuasiSeparatedSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)) :
    AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj W) := by
  apply AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme
    B S hS (yoneda.obj W) hZ
  exact ⟨W, hW, ⟨Functor.RepresentableBy.yoneda W⟩⟩

private theorem isQuasiSeparated_of_isAffineHom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : AlgebraicGeometry.Space.IsAffineHom B S hS f) :
    AlgebraicGeometry.Space.IsQuasiSeparated B S hS f := by
  apply AlgebraicGeometry.Space.isQuasiSeparated_of_isSeparated B S hS
  have h := ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS f hX
      hY).out 2 1).mp hf
  apply (AlgebraicGeometry.Space.isSeparated_iff_presheaf
    B S hS f hX hY h.1).mpr
  exact MorphismProperty.relative_monotone
    (fun _ _ q hq => by
      let : AlgebraicGeometry.IsAffineHom
          ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) := hq
      show _root_.AlgebraicGeometry.IsSeparated
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)
      infer_instance) f h.2

private theorem presheafProperty_id
    {C : Type*} [Category.{u} C] (P : MorphismProperty C) (hPiso : P.RespectsIso)
    (U : C) (hP : ∀ V, P (𝟙 V)) : P.presheaf (𝟙 (yoneda.obj U)) := by
  have := hPiso
  apply MorphismProperty.relative.of_exists
  intro V g
  exact ⟨V, g, 𝟙 V, by simpa using (IsPullback.id_horiz g).flip, hP V⟩

private theorem isFinitePresentation_of_scheme_chart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hXqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ X)
    (W U : AlgebraicGeometry.BigFppfOver B S hS)
    (hWqc : CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W))
    (hWqs : QuasiSeparatedSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W))
    (g : W ⟶ U) (p : yoneda.obj U ⟶ X)
    (hp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (hg : LocallyOfFinitePresentation ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) :
    AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map g ≫ p) := by
  have hW := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W
  refine ⟨?_, ?_, ?_⟩
  · apply (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart B S hS _
      AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
      hW hX _).mpr
    exact ⟨W, U, 𝟙 _, p, g,
      presheafProperty_id _ (etaleInverseImageRespectsIso _) W (fun V => by
        show Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (𝟙 V))
        infer_instance), hp,
      presheafProperty_id _ (surjectiveInverseImageRespectsIso _) W (fun V => by
        show Surjective ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (𝟙 V))
        infer_instance), by simp, hg⟩
  · exact AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace
      B S hS hZ hX hXqs
      (AlgebraicGeometry.Space.isQuasiCompactSpace_yoneda_obj B S hS (U := W) hWqc) _
  · exact AlgebraicGeometry.Space.isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source
      B S hS hZ hW (isQuasiSeparated_yoneda B S hS hZ W hWqs) _

/-- The public form of the private `isFinitePresentation_of_scheme_chart` above. -/
theorem FinitePresentationDescent.isFinitePresentation_of_scheme_chart :
    ∀ (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (_hXqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ X)
    (W U : AlgebraicGeometry.BigFppfOver B S hS)
    (_hWqc : CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W))
    (_hWqs : QuasiSeparatedSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W))
    (g : W ⟶ U) (p : yoneda.obj U ⟶ X)
    (_hp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (_hg : LocallyOfFinitePresentation ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)),
    AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map g ≫ p) :=
  @_root_.AlgebraicGeometry.Space.isFinitePresentation_of_scheme_chart

private theorem exists_site_model_of_finitePresentation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (X : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T))
    (hf : AlgebraicGeometry.FinitePresentation X.hom) :
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (g : U ⟶ T),
      AlgebraicGeometry.FinitePresentation ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ∧
      Nonempty (X ≅ Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) := by
  let : LocallyOfFinitePresentation X.hom := hf.1
  let : QuasiCompact X.hom := hf.2.1
  have hX : B.Contains X.left := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    X.hom T.left.property
  let U : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (⟨X.hom ≫ T.hom.hom⟩ : B.obj hX ⟶ B.obj hS)
  let g : U ⟶ T := Over.homMk (⟨X.hom⟩ : B.obj hX ⟶ T.left) rfl
  exact ⟨U, g, hf, ⟨Over.isoMk (Iso.refl _) (Category.id_comp _)⟩⟩

private theorem exists_site_pullback_model
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' W : AlgebraicGeometry.BigFppfOver B S hS} (q : T ⟶ T') (g : W ⟶ T)
    (W' : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T'))
    (hW' : AlgebraicGeometry.FinitePresentation W'.hom)
    (e : Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
      (Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)).obj W') :
    ∃ (V : AlgebraicGeometry.BigFppfOver B S hS) (f : V ⟶ T') (a : W ⟶ V),
      AlgebraicGeometry.FinitePresentation ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) ≅ W') ∧
      IsPullback a g f q := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let F : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  obtain ⟨V, f, hf, ⟨v⟩⟩ := exists_site_model_of_finitePresentation B S hS T' W' hW'
  let d := e ≪≫ (Over.pullback (Q.map q)).mapIso v
  let a₀ := d.hom.left ≫ pullback.fst (Q.map f) (Q.map q)
  have ha₀ : a₀ ≫ Q.map f = Q.map g ≫ Q.map q := by
    simp only [a₀, Category.assoc, pullback.condition]
    simpa only [← Category.assoc, Over.pullback_obj_hom, Over.mk_hom] using
      congrArg (fun t => t ≫ Q.map q) (Over.w d.hom)
  let a₁ : (F.obj W).left ⟶ (F.obj V).left := a₀
  have ha₁ : a₁ ≫ (F.map f).left = (F.map g).left ≫ (F.map q).left := ha₀
  have haS : a₁ ≫ (F.obj V).hom = (F.obj W).hom := by
    rw [← Over.w (F.map f), ← Category.assoc, ha₁, Category.assoc, Over.w (F.map q),
      Over.w (F.map g)]
  let a : W ⟶ V := Over.homMk (⟨a₀⟩ : W.left ⟶ V.left) (B.inclusion.map_injective haS)
  have hcomm : a ≫ f = g ≫ q := Q.map_injective ha₀
  refine ⟨V, f, a, hf, ⟨v.symm⟩, ?_⟩
  apply IsPullback.of_map Q hcomm
  refine (IsPullback.of_hasPullback (Q.map f) (Q.map q)).of_iso'
    ((Over.forget _).mapIso d) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp)
  · show d.hom.left ≫ pullback.fst (Q.map f) (Q.map q) = Q.map a ≫ 𝟙 _
    simp only [Category.comp_id]
    rfl
  · show d.hom.left ≫ pullback.snd (Q.map f) (Q.map q) = Q.map g ≫ 𝟙 _
    simpa only [Category.comp_id, Over.pullback_obj_hom, Over.mk_hom, Q] using Over.w d.hom

/-- The public form of the private `exists_site_pullback_model` above. -/
theorem FinitePresentationDescent.exists_site_pullback_model :
    ∀ (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' W : AlgebraicGeometry.BigFppfOver B S hS} (q : T ⟶ T') (g : W ⟶ T)
    (W' : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T'))
    (_hW' : AlgebraicGeometry.FinitePresentation W'.hom)
    (_e : Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
      (Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)).obj W'),
    ∃ (V : AlgebraicGeometry.BigFppfOver B S hS) (f : V ⟶ T') (a : W ⟶ V),
      AlgebraicGeometry.FinitePresentation ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) ≅ W') ∧
      IsPullback a g f q :=
  @_root_.AlgebraicGeometry.Space.exists_site_pullback_model

private theorem exists_locallyOfFinitePresentation_kernelPairMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (f : Y ⟶ X) (hf : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS f)
    {U W : AlgebraicGeometry.BigFppfOver B S hS}
    (p : yoneda.obj U ⟶ X) (w : yoneda.obj W ⟶ Y) (g : W ⟶ U)
    (hp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (hw : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (h : yoneda.map g ≫ p = w ≫ f) :
    let KX := atlasKernelPair B S hS p hX.diagonal_representable
    let KY := atlasKernelPair B S hS w hY.diagonal_representable
    ∃ r : KY.R ⟶ KX.R,
      r ≫ KX.s = KY.s ≫ g ∧ r ≫ KX.t = KY.t ≫ g ∧
      LocallyOfFinitePresentation ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r) := by
  dsimp only
  let KX := atlasKernelPair B S hS p hX.diagonal_representable
  let KY := atlasKernelPair B S hS w hY.diagonal_representable
  let r : KY.R ⟶ KX.R := yoneda.preimage (KX.kernelPair.lift
    (yoneda.map KY.s ≫ yoneda.map g) (yoneda.map KY.t ≫ yoneda.map g) (by
      simp only [Category.assoc, h]
      rw [← Category.assoc, KY.kernelPair.w, Category.assoc]))
  have ht : r ≫ KX.s = KY.s ≫ g := by
    apply yoneda.map_injective
    simp [r]
  have hs : r ≫ KX.t = KY.t ≫ g := by
    apply yoneda.map_injective
    simp [r]
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  refine ⟨r, ht, hs, hf KY.R KX.R (yoneda.map KY.s ≫ w)
    (yoneda.map KX.s ≫ p) r
    (Q.presheaf.comp_mem _ _ (Q.presheaf.of_isPullback KY.kernelPair.flip hw) hw)
    (Q.presheaf.comp_mem _ _ (Q.presheaf.of_isPullback KX.kernelPair.flip hp) hp) ?_⟩
  rw [← Category.assoc, ← yoneda.map_comp, ht, yoneda.map_comp]
  simp only [Category.assoc, h]

private theorem equalizes_kernelPair_after_baseChange
    {C : Type*} [Category* C] [HasPullbacks C]
    {U Y X X' Z : C} (p : U ⟶ Y) (r : Y ⟶ X) (e : X' ⟶ X)
    (f : pullback r e ⟶ Z) (g : U ⟶ Z)
    (h : pullback.fst (p ≫ r) e ≫ g =
      pullback.lift (pullback.fst (p ≫ r) e ≫ p) (pullback.snd (p ≫ r) e)
        (by simp only [Category.assoc, pullback.condition]) ≫ f) :
    pullback.fst (pullback.fst p p ≫ p ≫ r) e ≫ pullback.fst p p ≫ g =
      pullback.fst (pullback.fst p p ≫ p ≫ r) e ≫ pullback.snd p p ≫ g := by
  let a := pullback.fst (pullback.fst p p ≫ p ≫ r) e
  let b := pullback.snd (pullback.fst p p ≫ p ≫ r) e
  have hw : (a ≫ pullback.snd p p) ≫ p ≫ r = b ≫ e := by
    rw [Category.assoc, ← pullback.condition_assoc]
    exact pullback.condition
  let s : pullback (pullback.fst p p ≫ p ≫ r) e ⟶ pullback (p ≫ r) e :=
    pullback.lift (a ≫ pullback.fst p p) b (by
      simpa only [Category.assoc] using
        (pullback.condition (f := pullback.fst p p ≫ p ≫ r) (g := e)))
  let t : pullback (pullback.fst p p ≫ p ≫ r) e ⟶ pullback (p ≫ r) e :=
    pullback.lift (a ≫ pullback.snd p p) b hw
  have hs := congrArg (fun k => s ≫ k) h
  have ht := congrArg (fun k => t ≫ k) h
  dsimp [s] at hs
  dsimp [t] at ht
  simp only [pullback.lift_fst_assoc, Category.assoc] at hs ht
  rw [hs, ht]
  let z : pullback (p ≫ r) e ⟶ pullback r e :=
    pullback.lift (pullback.fst (p ≫ r) e ≫ p) (pullback.snd (p ≫ r) e)
      (by simp only [Category.assoc, pullback.condition])
  show s ≫ z ≫ f = t ≫ z ≫ f
  rw [← Category.assoc s z f, ← Category.assoc t z f]
  apply congrArg (fun k => k ≫ f)
  apply pullback.hom_ext
  · simp [s, t, z, Category.assoc, pullback.condition]
  · simp [s, t, z]

/-- The public form of the private `equalizes_kernelPair_after_baseChange` above. -/
theorem FinitePresentationDescent.equalizes_kernelPair_after_baseChange :
    ∀ {C : Type*} [Category* C] [HasPullbacks C]
    {U Y X X' Z : C} (p : U ⟶ Y) (r : Y ⟶ X) (e : X' ⟶ X)
    (f : pullback r e ⟶ Z) (g : U ⟶ Z)
    (_h : pullback.fst (p ≫ r) e ≫ g =
      pullback.lift (pullback.fst (p ≫ r) e ≫ p) (pullback.snd (p ≫ r) e)
        (by simp only [Category.assoc, pullback.condition]) ≫ f),
    pullback.fst (pullback.fst p p ≫ p ≫ r) e ≫ pullback.fst p p ≫ g =
      pullback.fst (pullback.fst p p ≫ p ≫ r) e ≫ pullback.snd p p ≫ g :=
  @_root_.AlgebraicGeometry.Space.equalizes_kernelPair_after_baseChange

private theorem equalizes_kernelPair_of_baseChange_eq
    {C : Type*} [Category* C] [HasPullbacks C]
    {U Y X X' U' Y' Z : C} (p : U ⟶ Y) (r : Y ⟶ X) (e : X' ⟶ X)
    (y : Y' ⟶ Y) (x : Y' ⟶ X') (hy : y ≫ r = x ≫ e)
    (u : U' ⟶ U) (p' : U' ⟶ Y') (hu : u ≫ p = p' ≫ y)
    (g : U ⟶ Z)
    (h : pullback.fst (pullback.fst p p ≫ p ≫ r) e ≫ pullback.fst p p ≫ g =
      pullback.fst (pullback.fst p p ≫ p ≫ r) e ≫ pullback.snd p p ≫ g) :
    pullback.fst p' p' ≫ u ≫ g = pullback.snd p' p' ≫ u ≫ g := by
  let v : pullback p' p' ⟶ pullback p p := pullback.lift
    (pullback.fst p' p' ≫ u) (pullback.snd p' p' ≫ u)
    (by simp only [Category.assoc, hu, pullback.condition_assoc])
  let w : pullback p' p' ⟶ pullback (pullback.fst p p ≫ p ≫ r) e :=
    pullback.lift v (pullback.fst p' p' ≫ p' ≫ x) (by
      simp only [v, pullback.lift_fst_assoc]
      simp only [Category.assoc]
      rw [← Category.assoc u p r, hu, Category.assoc, hy])
  simpa [w, v, Category.assoc] using congrArg (fun k => w ≫ k) h

/-- The public form of the private `equalizes_kernelPair_of_baseChange_eq` above. -/
theorem FinitePresentationDescent.equalizes_kernelPair_of_baseChange_eq :
    ∀ {C : Type*} [Category* C] [HasPullbacks C]
    {U Y X X' U' Y' Z : C} (p : U ⟶ Y) (r : Y ⟶ X) (e : X' ⟶ X)
    (y : Y' ⟶ Y) (x : Y' ⟶ X') (_hy : y ≫ r = x ≫ e)
    (u : U' ⟶ U) (p' : U' ⟶ Y') (_hu : u ≫ p = p' ≫ y)
    (g : U ⟶ Z)
    (_h : pullback.fst (pullback.fst p p ≫ p ≫ r) e ≫ pullback.fst p p ≫ g =
      pullback.fst (pullback.fst p p ≫ p ≫ r) e ≫ pullback.snd p p ≫ g),
    pullback.fst p' p' ≫ u ≫ g = pullback.snd p' p' ≫ u ≫ g :=
  @_root_.AlgebraicGeometry.Space.equalizes_kernelPair_of_baseChange_eq

private noncomputable def iteratedBaseChangeIso
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) (Y : Over X) :
    (Over.pullback q).obj ((Over.pullback p).obj Y) ≅ (Over.pullback r).obj Y := by
  refine Over.isoMk
    { hom := pullback.lift
        (pullback.fst (pullback.snd Y.hom p) q ≫ pullback.fst Y.hom p)
        (pullback.snd (pullback.snd Y.hom p) q) (by
          simp only [Category.assoc, pullback.condition]
          rw [← Category.assoc, pullback.condition, Category.assoc, h])
      inv := pullback.lift
        (pullback.lift (pullback.fst Y.hom r) (pullback.snd Y.hom r ≫ q)
          (by rw [Category.assoc, h]; exact pullback.condition))
        (pullback.snd Y.hom r) (by simp)
      hom_inv_id := by
        apply pullback.hom_ext
        · apply pullback.hom_ext <;> simp [Category.assoc, pullback.condition]
        · simp
      inv_hom_id := by
        apply pullback.hom_ext <;> simp [Category.assoc] } (by simp)

/-- The public form of the private `iteratedBaseChangeIso` above. -/
noncomputable def FinitePresentationDescent.iteratedBaseChangeIso
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) (Y : Over X) :
    (Over.pullback q).obj ((Over.pullback p).obj Y) ≅ (Over.pullback r).obj Y := by
  refine Over.isoMk
    { hom := pullback.lift
        (pullback.fst (pullback.snd Y.hom p) q ≫ pullback.fst Y.hom p)
        (pullback.snd (pullback.snd Y.hom p) q) (by
          simp only [Category.assoc, pullback.condition]
          rw [← Category.assoc, pullback.condition, Category.assoc, h])
      inv := pullback.lift
        (pullback.lift (pullback.fst Y.hom r) (pullback.snd Y.hom r ≫ q)
          (by rw [Category.assoc, h]; exact pullback.condition))
        (pullback.snd Y.hom r) (by simp)
      hom_inv_id := by
        apply pullback.hom_ext
        · apply pullback.hom_ext <;> simp [Category.assoc, pullback.condition]
        · simp
      inv_hom_id := by
        apply pullback.hom_ext <;> simp [Category.assoc] } (by simp)

/-- The two components of the comparison isomorphism between an iterated base change and a
single one, named so that `simp` need not unfold the isomorphism itself. -/
private theorem iteratedBaseChangeIso_hom_left
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) (Y : Over X) :
    (iteratedBaseChangeIso p q r h Y).hom.left =
      pullback.lift (pullback.fst (pullback.snd Y.hom p) q ≫ pullback.fst Y.hom p)
        (pullback.snd (pullback.snd Y.hom p) q)
        (by
          simp only [Category.assoc, pullback.condition]
          rw [← Category.assoc, pullback.condition, Category.assoc, h]) := rfl

/-- The public form of the private `iteratedBaseChangeIso_hom_left` above. -/
theorem FinitePresentationDescent.iteratedBaseChangeIso_hom_left :
    ∀ {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) (Y : Over X),
    (FinitePresentationDescent.iteratedBaseChangeIso p q r h Y).hom.left =
      pullback.lift (pullback.fst (pullback.snd Y.hom p) q ≫ pullback.fst Y.hom p)
        (pullback.snd (pullback.snd Y.hom p) q)
        (by
          simp only [Category.assoc, pullback.condition]
          rw [← Category.assoc, pullback.condition, Category.assoc, h]) :=
  @_root_.AlgebraicGeometry.Space.iteratedBaseChangeIso_hom_left

private theorem iteratedBaseChangeIso_inv_left
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) (Y : Over X) :
    (iteratedBaseChangeIso p q r h Y).inv.left =
      pullback.lift
        (pullback.lift (pullback.fst Y.hom r) (pullback.snd Y.hom r ≫ q)
          (by rw [Category.assoc, h]; exact pullback.condition))
        (pullback.snd Y.hom r) (by simp) := rfl

/-- The public form of the private `iteratedBaseChangeIso_inv_left` above. -/
theorem FinitePresentationDescent.iteratedBaseChangeIso_inv_left :
    ∀ {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) (Y : Over X),
    (FinitePresentationDescent.iteratedBaseChangeIso p q r h Y).inv.left =
      pullback.lift
        (pullback.lift (pullback.fst Y.hom r) (pullback.snd Y.hom r ≫ q)
          (by rw [Category.assoc, h]; exact pullback.condition))
        (pullback.snd Y.hom r) (by simp) :=
  @_root_.AlgebraicGeometry.Space.iteratedBaseChangeIso_inv_left

private theorem iteratedBaseChangeIso_hom_fst
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) (Y : Over X) :
    (iteratedBaseChangeIso p q r h Y).hom.left ≫ pullback.fst Y.hom r =
      pullback.fst (pullback.snd Y.hom p) q ≫ pullback.fst Y.hom p := by
  simp [iteratedBaseChangeIso]

/-- The public form of the private `iteratedBaseChangeIso_hom_fst` above. -/
theorem FinitePresentationDescent.iteratedBaseChangeIso_hom_fst :
    ∀ {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) (Y : Over X),
    (FinitePresentationDescent.iteratedBaseChangeIso p q r h Y).hom.left ≫ pullback.fst Y.hom r =
      pullback.fst (pullback.snd Y.hom p) q ≫ pullback.fst Y.hom p :=
  @_root_.AlgebraicGeometry.Space.iteratedBaseChangeIso_hom_fst

private theorem iteratedBaseChangeIso_inv_fst
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) (Y : Over X) :
    (iteratedBaseChangeIso p q r h Y).inv.left ≫
      pullback.fst (pullback.snd Y.hom p) q =
      pullback.lift (pullback.fst Y.hom r) (pullback.snd Y.hom r ≫ q)
        (by rw [Category.assoc, h]; exact pullback.condition) := by
  simp [iteratedBaseChangeIso]

/-- The public form of the private `iteratedBaseChangeIso_inv_fst` above. -/
theorem FinitePresentationDescent.iteratedBaseChangeIso_inv_fst :
    ∀ {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) (Y : Over X),
    (FinitePresentationDescent.iteratedBaseChangeIso p q r h Y).inv.left ≫
      pullback.fst (pullback.snd Y.hom p) q =
      pullback.lift (pullback.fst Y.hom r) (pullback.snd Y.hom r ≫ q)
        (by rw [Category.assoc, h]; exact pullback.condition) :=
  @_root_.AlgebraicGeometry.Space.iteratedBaseChangeIso_inv_fst

private theorem iteratedBaseChangeIso_unique
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) (Y : Over X)
    (α : (Over.pullback q).obj ((Over.pullback p).obj Y) ≅ (Over.pullback r).obj Y)
    (hα : α.hom.left ≫ pullback.fst Y.hom r =
      pullback.fst ((Over.pullback p).obj Y).hom q ≫ pullback.fst Y.hom p) :
    α = iteratedBaseChangeIso p q r h Y := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact hα.trans (iteratedBaseChangeIso_hom_fst p q r h Y).symm
  · exact α.hom.w.trans (iteratedBaseChangeIso p q r h Y).hom.w.symm

/-- The public form of the private `iteratedBaseChangeIso_unique` above. -/
theorem FinitePresentationDescent.iteratedBaseChangeIso_unique :
    ∀ {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) (Y : Over X)
    (α : (Over.pullback q).obj ((Over.pullback p).obj Y) ≅ (Over.pullback r).obj Y)
    (_hα : α.hom.left ≫ pullback.fst Y.hom r =
      pullback.fst ((Over.pullback p).obj Y).hom q ≫ pullback.fst Y.hom p),
    α = FinitePresentationDescent.iteratedBaseChangeIso p q r h Y :=
  @_root_.AlgebraicGeometry.Space.iteratedBaseChangeIso_unique

private theorem iteratedBaseChangeIso_naturality
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) {Y Z : Over X} (f : Y ⟶ Z) :
    (Over.pullback q).map ((Over.pullback p).map f) ≫
        (iteratedBaseChangeIso p q r h Z).hom =
      (iteratedBaseChangeIso p q r h Y).hom ≫ (Over.pullback r).map f := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;>
    simp [iteratedBaseChangeIso, Over.pullback_map_left, Category.assoc]

/-- The public form of the private `iteratedBaseChangeIso_naturality` above. -/
theorem FinitePresentationDescent.iteratedBaseChangeIso_naturality :
    ∀ {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) {Y Z : Over X} (f : Y ⟶ Z),
    (Over.pullback q).map ((Over.pullback p).map f) ≫
        (FinitePresentationDescent.iteratedBaseChangeIso p q r h Z).hom =
      (FinitePresentationDescent.iteratedBaseChangeIso p q r h Y).hom ≫ (Over.pullback r).map f :=
  @_root_.AlgebraicGeometry.Space.iteratedBaseChangeIso_naturality

private theorem baseChange_eq_of_baseChange_eq
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) {Y Z : Over X} (f g : Y ⟶ Z)
    (hfg : (Over.pullback p).map f = (Over.pullback p).map g) :
    (Over.pullback r).map f = (Over.pullback r).map g := by
  apply (cancel_epi (iteratedBaseChangeIso p q r h Y).hom).mp
  rw [← iteratedBaseChangeIso_naturality p q r h f,
    ← iteratedBaseChangeIso_naturality p q r h g, hfg]

/-- The public form of the private `baseChange_eq_of_baseChange_eq` above. -/
theorem FinitePresentationDescent.baseChange_eq_of_baseChange_eq :
    ∀ {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (_h : q ≫ p = r) {Y Z : Over X} (f g : Y ⟶ Z)
    (_hfg : (Over.pullback p).map f = (Over.pullback p).map g),
    (Over.pullback r).map f = (Over.pullback r).map g :=
  @_root_.AlgebraicGeometry.Space.baseChange_eq_of_baseChange_eq

/-- A morphism lifting a pair of morphisms over one base change lifts it over any
later base change. -/
private theorem exists_liftPair_of_comp
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X)
    (h : q ≫ p = r) {A R W : Over X} (s t : R ⟶ W) (a b : A ⟶ W)
    (v : (Over.pullback p).obj A ⟶ (Over.pullback p).obj R)
    (h₁ : v ≫ (Over.pullback p).map s = (Over.pullback p).map a)
    (h₂ : v ≫ (Over.pullback p).map t = (Over.pullback p).map b) :
    ∃ v' : (Over.pullback r).obj A ⟶ (Over.pullback r).obj R,
      v' ≫ (Over.pullback r).map s = (Over.pullback r).map a ∧
      v' ≫ (Over.pullback r).map t = (Over.pullback r).map b := by
  let δ (Z : Over X) := iteratedBaseChangeIso p q r h Z
  have key : ∀ (x : R ⟶ W) (z : A ⟶ W),
      v ≫ (Over.pullback p).map x = (Over.pullback p).map z →
      ((δ A).inv ≫ (Over.pullback q).map v ≫ (δ R).hom) ≫ (Over.pullback r).map x =
        (Over.pullback r).map z := by
    intro x z hx
    have hx' : (Over.pullback q).map v ≫ (Over.pullback q).map ((Over.pullback p).map x) =
        (Over.pullback q).map ((Over.pullback p).map z) := by
      simpa only [Functor.map_comp] using congrArg (Over.pullback q).map hx
    calc
      ((δ A).inv ≫ (Over.pullback q).map v ≫ (δ R).hom) ≫ (Over.pullback r).map x =
          (δ A).inv ≫ (Over.pullback q).map v ≫
            (Over.pullback q).map ((Over.pullback p).map x) ≫ (δ W).hom := by
        simp only [Category.assoc]
        rw [← iteratedBaseChangeIso_naturality p q r h x]
      _ = (δ A).inv ≫ (Over.pullback q).map ((Over.pullback p).map z) ≫ (δ W).hom := by
        rw [reassoc_of% hx']
      _ = (Over.pullback r).map z := by
        rw [iteratedBaseChangeIso_naturality p q r h z, Iso.inv_hom_id_assoc]
  exact ⟨_, key s a h₁, key t b h₂⟩

private noncomputable def overPullbackCone
    {C : Type*} [Category* C] [HasPullbacks C] {X : C}
    {Y Z T : Over X} (f : Y ⟶ T) (g : Z ⟶ T) : PullbackCone f g := by
  let P : Over X := Over.mk (pullback.fst f.left g.left ≫ Y.hom)
  let a : P ⟶ Y := Over.homMk (pullback.fst f.left g.left) rfl
  let b : P ⟶ Z := Over.homMk (pullback.snd f.left g.left) (by
    rw [← g.w, ← Category.assoc, ← pullback.condition, Category.assoc, f.w]
    rfl)
  exact PullbackCone.mk a b (by ext; exact pullback.condition)

/-- The public form of the private `overPullbackCone` above. -/
noncomputable def FinitePresentationDescent.overPullbackCone
    {C : Type*} [Category* C] [HasPullbacks C] {X : C}
    {Y Z T : Over X} (f : Y ⟶ T) (g : Z ⟶ T) : PullbackCone f g := by
  let P : Over X := Over.mk (pullback.fst f.left g.left ≫ Y.hom)
  let a : P ⟶ Y := Over.homMk (pullback.fst f.left g.left) rfl
  let b : P ⟶ Z := Over.homMk (pullback.snd f.left g.left) (by
    rw [← g.w, ← Category.assoc, ← pullback.condition, Category.assoc, f.w]
    rfl)
  exact PullbackCone.mk a b (by ext; exact pullback.condition)

private theorem overPullbackCone_isPullback
    {C : Type*} [Category* C] [HasPullbacks C] {X : C}
    {Y Z T : Over X} (f : Y ⟶ T) (g : Z ⟶ T) :
    IsPullback (overPullbackCone f g).fst (overPullbackCone f g).snd f g :=
  IsPullback.of_map (Over.forget X) (overPullbackCone f g).condition
    (IsPullback.of_hasPullback f.left g.left)

/-- The public form of the private `overPullbackCone_isPullback` above. -/
theorem FinitePresentationDescent.overPullbackCone_isPullback :
    ∀ {C : Type*} [Category* C] [HasPullbacks C] {X : C}
    {Y Z T : Over X} (f : Y ⟶ T) (g : Z ⟶ T),
    IsPullback (FinitePresentationDescent.overPullbackCone f g).fst
        (FinitePresentationDescent.overPullbackCone f g).snd f g :=
  @_root_.AlgebraicGeometry.Space.overPullbackCone_isPullback

private theorem overPullback_map_isPullback
    {C : Type*} [Category* C] [HasPullbacks C] {X X' : C}
    (p : X' ⟶ X) {Y Z : Over X} (f : Y ⟶ Z) :
    IsPullback ((Over.pullback p).map f).left
      (pullback.fst Y.hom p) (pullback.fst Z.hom p) f.left := by
  apply IsPullback.of_right (h₂₂ := Z.hom) _
    (by simp [Over.pullback_map_left]) (IsPullback.of_hasPullback Z.hom p).flip
  simpa [Over.pullback_map_left] using (IsPullback.of_hasPullback Y.hom p).flip

private theorem eventually_isAffine_pullback
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Scheme.{u}) (c : Cone E) (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (E.map f)]
    (i : J) (X : Over (E.obj i))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [IsAffine ((Over.pullback (c.π.app i)).obj X).left] :
    ∃ (j : J) (e : j ⟶ i), IsAffine ((Over.pullback (E.map e)).obj X).left := by
  let F := Over.post E ⋙ Over.pullback X.hom ⋙ Over.forget X.left
  let d := (Over.forget X.left).mapCone ((Over.pullback X.hom).mapCone (c.overPost i))
  have hd : IsLimit d := isLimitOfPreserves (Over.forget X.left)
    (isLimitOfPreserves (Over.pullback X.hom) (hc.overPost i))
  let : ∀ {j k : Over i} (e : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (F.map e) := by
    intro j k e
    exact MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsAffineHom)
      (overPullback_map_isPullback X.hom ((Over.post E).map e)).flip
      (show _root_.AlgebraicGeometry.IsAffineHom (E.map e.left) from inferInstance)
  let : ∀ j : Over i, CompactSpace (F.obj j) := by
    intro j
    let : _root_.AlgebraicGeometry.IsAffineHom (pullback.snd (E.map j.hom) X.hom) :=
      MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsAffineHom)
        (IsPullback.of_hasPullback (E.map j.hom) X.hom)
        (show _root_.AlgebraicGeometry.IsAffineHom (E.map j.hom) from inferInstance)
    have h := QuasiCompact.compactSpace_of_compactSpace (pullback.snd (E.map j.hom) X.hom)
    exact h
  let : ∀ j : Over i, QuasiSeparatedSpace (F.obj j) := by
    intro j
    let : _root_.AlgebraicGeometry.IsAffineHom (pullback.snd (E.map j.hom) X.hom) :=
      MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsAffineHom)
        (IsPullback.of_hasPullback (E.map j.hom) X.hom)
        (show _root_.AlgebraicGeometry.IsAffineHom (E.map j.hom) from inferInstance)
    have h := quasiSeparatedSpace_of_quasiSeparated (pullback.snd (E.map j.hom) X.hom)
    exact h
  let : IsAffine (pullback X.hom (c.π.app i)) :=
    ‹IsAffine ((Over.pullback (c.π.app i)).obj X).left›
  let : IsAffine d.pt := by
    have h : IsAffine (pullback (c.π.app i) X.hom) :=
      IsAffine.of_isIso (pullbackSymmetry (c.π.app i) X.hom).hom
    exact h
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit F d hd
  let : IsAffine (pullback (E.map j.hom) X.hom) := hj
  refine ⟨j.left, j.hom, ?_⟩
  exact IsAffine.of_isIso (pullbackSymmetry X.hom (E.map j.hom)).hom

private theorem scheme_affine_model_of_finitePresentation
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Scheme.{u}) (c : Cone E) (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (E.map f)]
    [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)]
    (X : Over c.pt) (hFp : AlgebraicGeometry.FinitePresentation X.hom)
    (hXaff : IsAffine X.left) :
    ∃ (i : J) (Xi : Over (E.obj i)), AlgebraicGeometry.FinitePresentation Xi.hom ∧
      IsAffine Xi.left ∧ Nonempty (X ≅ (Over.pullback (c.π.app i)).obj Xi) := by
  have := hXaff
  obtain ⟨i, Xi, hXi, ⟨e⟩⟩ := scheme_model_of_finitePresentation E c hc X hFp
  let : LocallyOfFinitePresentation Xi.hom := hXi.1
  let : QuasiCompact Xi.hom := hXi.2.1
  let : QuasiSeparated Xi.hom := hXi.2.2
  let : CompactSpace Xi.left := QuasiCompact.compactSpace_of_compactSpace Xi.hom
  let : QuasiSeparatedSpace Xi.left := quasiSeparatedSpace_of_quasiSeparated Xi.hom
  let : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget c.pt).map e.inv))
  let : IsAffine ((Over.pullback (c.π.app i)).obj Xi).left :=
    IsAffine.of_isIso e.inv.left
  obtain ⟨j, a, ha⟩ := eventually_isAffine_pullback E c hc i Xi
  refine ⟨j, (Over.pullback (E.map a)).obj Xi, ?_, ha,
    ⟨e ≪≫ (iteratedBaseChangeIso (E.map a) (c.π.app j) (c.π.app i)
      (c.w a) Xi).symm⟩⟩
  show AlgebraicGeometry.FinitePresentation (pullback.snd Xi.hom (E.map a))
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The public form of the private `scheme_affine_model_of_finitePresentation` above. -/
theorem FinitePresentationDescent.scheme_affine_model_of_finitePresentation :
    ∀ {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Scheme.{u}) (c : Cone E) (_hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (E.map f)]
    [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)]
    (X : Over c.pt) (_hFp : AlgebraicGeometry.FinitePresentation X.hom)
    (_hXaff : IsAffine X.left),
    ∃ (i : J) (Xi : Over (E.obj i)), AlgebraicGeometry.FinitePresentation Xi.hom ∧
      IsAffine Xi.left ∧ Nonempty (X ≅ (Over.pullback (c.π.app i)).obj Xi) :=
  @_root_.AlgebraicGeometry.Space.scheme_affine_model_of_finitePresentation

/-- Finite presentation is stable under base change: in a cartesian square of
algebraic spaces over `S`, the base change of a morphism of finite presentation is of finite
presentation. -/
theorem isFinitePresentation_of_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : AlgebraicGeometry.IsAlgebraicSpace B S hS W)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hZ : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (hf : AlgebraicGeometry.Space.IsFinitePresentation B S hS f) :
    AlgebraicGeometry.Space.IsFinitePresentation B S hS b := by
  let P : ObjectProperty ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    AlgebraicGeometry.IsAlgebraicSpace B S hS
  let W' : P.FullSubcategory := ⟨W, hW⟩
  let X' : P.FullSubcategory := ⟨X, hX⟩
  let Y' : P.FullSubcategory := ⟨Y, hY⟩
  let Z' : P.FullSubcategory := ⟨Z, hZ⟩
  have h' : IsPullback (ObjectProperty.homMk a : W' ⟶ X')
      (ObjectProperty.homMk b : W' ⟶ Y')
      (ObjectProperty.homMk f : X' ⟶ Z') (ObjectProperty.homMk g : Y' ⟶ Z') := by
    apply IsPullback.of_map P.ι
    · exact ObjectProperty.hom_ext _ h.w
    · exact h
  exact MorphismProperty.of_isPullback
    (P := fun {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS} (f : X ⟶ Y) =>
      AlgebraicGeometry.Space.IsFinitePresentation B S hS f.hom) h' hf

private theorem finitePresentation_of_yoneda
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (f : U ⟶ V)
    (hf : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map f)) :
    AlgebraicGeometry.FinitePresentation
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : E.RespectsIso := etaleInverseImageRespectsIso _
  have hId (W : AlgebraicGeometry.BigFppfOver B S hS) : E.presheaf (𝟙 (yoneda.obj W)) :=
    presheafProperty_id E (etaleInverseImageRespectsIso _) W (fun T => by
      show Etale (Q.map (𝟙 T))
      infer_instance)
  refine ⟨hf.1 U V (𝟙 _) (𝟙 _) f (hId U) (hId V) (by simp), ?_,
    (AlgebraicGeometry.Space.isQuasiSeparated_yoneda_map_iff B S hS f).mp hf.2.2⟩
  exact MorphismProperty.of_relative_map (P := MorphismProperty.inverseImage
    (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) Q) (F := yoneda)
    ((AlgebraicGeometry.Space.presheaf_quasiCompact_iff_isQuasiCompact B S hS
      (Functor.relativelyRepresentable.map yoneda f)).mpr hf.2.1)

/-- The public form of the private `finitePresentation_of_yoneda` above. -/
theorem FinitePresentationDescent.finitePresentation_of_yoneda :
    ∀ (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (f : U ⟶ V)
    (_hf : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map f)),
    AlgebraicGeometry.FinitePresentation ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) :=
  @_root_.AlgebraicGeometry.Space.finitePresentation_of_yoneda

private theorem etale_of_over_iso {T : Scheme.{u}} {X Y : Over T}
    (e : X ≅ Y) [Etale Y.hom] : Etale X.hom := by
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget T).map e.hom))
  let : Etale e.hom.left := inferInstance
  rw [← e.hom.w]
  infer_instance

private theorem etale_overHom_of_isIso_target {T : Scheme.{u}} {X Y : Over T}
    (f : X ⟶ Y) [Etale X.hom] [IsIso Y.hom] : Etale f.left := by
  have h : f.left = X.hom ≫ inv Y.hom := by
    apply (cancel_mono Y.hom).mp
    simp
  rw [h]
  infer_instance

private theorem etale_iff_pullback_of_isPullback
    {A X Y Z : Scheme.{u}} {a : A ⟶ X} {b : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) : Etale b ↔ Etale (pullback.snd f g) := by
  let e : Over.mk b ≅ Over.mk (pullback.snd f g) :=
    Over.isoMk h.isoPullback h.isoPullback_hom_snd
  constructor
  · intro hb
    let : Etale (Over.mk b).hom := hb
    exact etale_of_over_iso e.symm
  · intro hb
    let : Etale (Over.mk (pullback.snd f g)).hom := hb
    exact etale_of_over_iso e

/-- The public form of the private `etale_iff_pullback_of_isPullback` above. -/
theorem FinitePresentationDescent.etale_iff_pullback_of_isPullback :
    ∀ {A X Y Z : Scheme.{u}} {a : A ⟶ X} {b : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (_h : IsPullback a b f g),
    Etale b ↔ Etale (pullback.snd f g) :=
  @_root_.AlgebraicGeometry.Space.etale_iff_pullback_of_isPullback

private theorem etale_pullback_of_etale_pullback
    {T T' T'' : Scheme.{u}} (p : T' ⟶ T) (q : T'' ⟶ T') (r : T'' ⟶ T)
    (h : q ≫ p = r) (X : Over T)
    [Etale ((Over.pullback p).obj X).hom] : Etale ((Over.pullback r).obj X).hom := by
  let : Etale ((Over.pullback q).obj ((Over.pullback p).obj X)).hom := by
    show Etale (pullback.snd ((Over.pullback p).obj X).hom q)
    infer_instance
  exact etale_of_over_iso (iteratedBaseChangeIso p q r h X).symm

/-- The public form of the private `etale_pullback_of_etale_pullback` above. -/
theorem FinitePresentationDescent.etale_pullback_of_etale_pullback :
    ∀ {T T' T'' : Scheme.{u}} (p : T' ⟶ T) (q : T'' ⟶ T') (r : T'' ⟶ T)
    (_h : q ≫ p = r) (X : Over T)
    [Etale ((Over.pullback p).obj X).hom],
    Etale ((Over.pullback r).obj X).hom :=
  @_root_.AlgebraicGeometry.Space.etale_pullback_of_etale_pullback

private theorem scheme_eventually_etale_pullback
    {J : Type u} [Category.{u} J] [IsCofiltered J] {T : Scheme.{u}}
    (E : J ⥤ Over T) (c : Cone E)
    (hc : IsLimit ((Over.forget T).mapCone c))
    [∀ {i j : J} (a : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (E.map a).left]
    [∀ j, IsAffine (E.obj j).left]
    (X : Over T) (hX : AlgebraicGeometry.FinitePresentation X.hom)
    [Etale ((Over.pullback c.pt.hom).obj X).hom] :
    ∃ j, Etale ((Over.pullback (E.obj j).hom).obj X).hom := by
  classical
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := J)
  let D := E ⋙ Over.forget T
  let d := (Over.forget T).mapCone c
  let X₀ := (Over.pullback (E.obj i).hom).obj X
  let Y₀ : Over (D.obj i) := Over.mk (𝟙 _)
  let f₀ : X₀ ⟶ Y₀ := Over.homMk X₀.hom (by simp [Y₀])
  let : ∀ {i j : J} (a : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (D.map a) :=
    fun {_ _} a => ‹∀ {i j : J} (a : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (E.map a).left› a
  let : LocallyOfFinitePresentation X.hom := hX.1
  let : QuasiCompact X.hom := hX.2.1
  let : QuasiSeparated X.hom := hX.2.2
  let : CompactSpace (D.obj i) := inferInstanceAs (CompactSpace (E.obj i).left)
  let : QuasiSeparatedSpace (D.obj i) := inferInstanceAs (QuasiSeparatedSpace (E.obj i).left)
  let : LocallyOfFinitePresentation X₀.hom := by
    show LocallyOfFinitePresentation (pullback.snd X.hom (E.obj i).hom)
    infer_instance
  let : QuasiCompact X₀.hom := by
    show QuasiCompact (pullback.snd X.hom (E.obj i).hom)
    infer_instance
  let : QuasiSeparated X₀.hom := by
    show QuasiSeparated (pullback.snd X.hom (E.obj i).hom)
    infer_instance
  let : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace X₀.hom
  let : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated X₀.hom
  let : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj i))
  let : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  let : LocallyOfFinitePresentation f₀.left := ‹LocallyOfFinitePresentation X₀.hom›
  let e := iteratedBaseChangeIso (E.obj i).hom (c.π.app i).left c.pt.hom (c.π.app i).w X
  let : Etale ((Over.pullback (d.π.app i)).obj X₀).hom := etale_of_over_iso e
  let : IsIso ((Over.pullback (d.π.app i)).obj Y₀).hom := by
    show IsIso (pullback.snd (𝟙 (D.obj i)) (d.π.app i))
    infer_instance
  let : Etale ((Over.pullback (d.π.app i)).map f₀).left :=
    etale_overHom_of_isIso_target ((Over.pullback (d.π.app i)).map f₀)
  obtain ⟨j, hj⟩ := AlgebraicGeometry.exists_etale_pullback_of_isLimit D d hc i X₀ Y₀ f₀
  let : Etale ((Over.pullback (D.map j.hom)).map f₀).left := hj
  let : IsIso ((Over.pullback (D.map j.hom)).obj Y₀).hom := by
    show IsIso (pullback.snd (𝟙 (D.obj i)) (D.map j.hom))
    infer_instance
  let : Etale ((Over.pullback (D.map j.hom)).obj X₀).hom := by
    rw [← ((Over.pullback (D.map j.hom)).map f₀).w]
    infer_instance
  let : Etale ((Over.pullback (E.map j.hom).left).obj
      ((Over.pullback (E.obj i).hom).obj X)).hom :=
    ‹Etale ((Over.pullback (D.map j.hom)).obj X₀).hom›
  exact ⟨j.left, etale_of_over_iso
    (iteratedBaseChangeIso (E.obj i).hom (E.map j.hom).left (E.obj j.left).hom
      (E.map j.hom).w X).symm⟩

/-- The public form of the private `scheme_eventually_etale_pullback` above. -/
theorem FinitePresentationDescent.scheme_eventually_etale_pullback :
    ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] {T : Scheme.{u}}
    (E : J ⥤ Over T) (c : Cone E)
    (_hc : IsLimit ((Over.forget T).mapCone c))
    [∀ {i j : J} (a : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (E.map a).left]
    [∀ j, IsAffine (E.obj j).left]
    (X : Over T) (_hX : AlgebraicGeometry.FinitePresentation X.hom)
    [Etale ((Over.pullback c.pt.hom).obj X).hom],
    ∃ j, Etale ((Over.pullback (E.obj j).hom).obj X).hom :=
  @_root_.AlgebraicGeometry.Space.scheme_eventually_etale_pullback

private theorem isFinitePresentation_overHom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hXqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X)
    (hXqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ X)
    (Y Z : Over X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Z.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Z.hom) (f : Y ⟶ Z) :
    AlgebraicGeometry.Space.IsFinitePresentation B S hS f.left := by
  have hYqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS
      Y.hom hX hXqc hYfp
  have hYqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS hZ hY hXqs hYfp.2.2
  have hZqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS hZ hZ' hXqs hZfp.2.2
  refine ⟨?_, AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace
    B S hS hZ hZ' hZqs hYqc f.left,
    AlgebraicGeometry.Space.isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source
      B S hS hZ hY hYqs f.left⟩
  apply AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_comp B S hS hY hZ' hX f.left Z.hom
  · simpa only [f.w] using hYfp.1
  · intro U V a b g ha hb hg
    let := hZfp.1 U V a b g ha hb hg
    infer_instance

/-- The public form of the private `isFinitePresentation_overHom` above. -/
theorem FinitePresentationDescent.isFinitePresentation_overHom :
    ∀ (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (_hXqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X)
    (_hXqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ X)
    (Y Z : Over X)
    (_hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (_hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Z.left)
    (_hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom)
    (_hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Z.hom) (f : Y ⟶ Z),
    AlgebraicGeometry.Space.IsFinitePresentation B S hS f.left :=
  @_root_.AlgebraicGeometry.Space.isFinitePresentation_overHom

private theorem advance_represented_model
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hZ : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    {W V : AlgebraicGeometry.BigFppfOver B S hS}
    (v : yoneda.obj V ⟶ Z) (a : W ⟶ V) (w : yoneda.obj W ⟶ X)
    (p : X ⟶ Y) (f : Y ⟶ Z) (q : X ⟶ Z) (hpq : p ≫ f = q)
    (hf : AlgebraicGeometry.Space.IsAffineHom B S hS f)
    (hv : AlgebraicGeometry.Space.IsFinitePresentation B S hS v)
    (h : IsPullback (yoneda.map a) w v q) :
    ∃ (V' : AlgebraicGeometry.BigFppfOver B S hS) (v' : yoneda.obj V' ⟶ Y) (a' : W ⟶ V'),
      AlgebraicGeometry.Space.IsFinitePresentation B S hS v' ∧
      IsPullback (yoneda.map a') w v' p := by
  have hr := ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS f hY
      hZ).out 2 1).mp hf
  let V' := hr.1.pullback v
  let b : V' ⟶ V := hr.1.snd v
  let v' := hr.1.fst v
  have hb : IsPullback v' (yoneda.map b) f v := hr.1.isPullback v
  have hh : IsPullback (yoneda.map a) w v (p ≫ f) := hpq.symm ▸ h
  let a' : W ⟶ V' := yoneda.preimage (hb.flip.lift (yoneda.map a) (w ≫ p)
    (by simpa only [Category.assoc] using hh.w))
  refine ⟨V', v', a', isFinitePresentation_of_isPullback B S hS
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V')
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) hY hZ hb.flip hv, ?_⟩
  simpa only [a', yoneda.map_preimage] using hh.of_right' hb.flip

/-- The public form of the private `advance_represented_model` above. -/
theorem FinitePresentationDescent.advance_represented_model :
    ∀ (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (_hZ : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    {W V : AlgebraicGeometry.BigFppfOver B S hS}
    (v : yoneda.obj V ⟶ Z) (a : W ⟶ V) (w : yoneda.obj W ⟶ X)
    (p : X ⟶ Y) (f : Y ⟶ Z) (q : X ⟶ Z) (_hpq : p ≫ f = q)
    (_hf : AlgebraicGeometry.Space.IsAffineHom B S hS f)
    (_hv : AlgebraicGeometry.Space.IsFinitePresentation B S hS v)
    (_h : IsPullback (yoneda.map a) w v q),
    ∃ (V' : AlgebraicGeometry.BigFppfOver B S hS) (v' : yoneda.obj V' ⟶ Y) (a' : W ⟶ V'),
      AlgebraicGeometry.Space.IsFinitePresentation B S hS v' ∧
      IsPullback (yoneda.map a') w v' p :=
  @_root_.AlgebraicGeometry.Space.advance_represented_model

/-- The kernel pair of a morphism is the base change of the relative diagonal of a
morphism it is a kernel pair over. -/
private theorem isPullback_kernelPair_diagonal
    {C : Type*} [Category* C] [HasPullbacks C]
    {A X T R KW : C} (q : A ⟶ X) (y : X ⟶ T)
    {kt ks : KW ⟶ A} (hKW : IsPullback kt ks (q ≫ y) (q ≫ y))
    {sR tR : R ⟶ A} (hR : IsPullback sR tR q q)
    (ρ : R ⟶ KW) (hρ₁ : ρ ≫ kt = sR) (hρ₂ : ρ ≫ ks = tR) :
    IsPullback ρ (sR ≫ q)
      (pullback.lift (kt ≫ q) (ks ≫ q) (by simpa only [Category.assoc] using hKW.w))
      (pullback.diagonal y) := by
  have hc : CommSq ρ (sR ≫ q)
      (pullback.lift (kt ≫ q) (ks ≫ q)
        (by simpa only [Category.assoc] using hKW.w)) (pullback.diagonal y) := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      rw [reassoc_of% hρ₁]
    · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
      rw [reassoc_of% hρ₂, hR.w]
  have hfst : ∀ c : PullbackCone (pullback.lift (kt ≫ q) (ks ≫ q)
      (by simpa only [Category.assoc] using hKW.w)) (pullback.diagonal y),
      c.fst ≫ kt ≫ q = c.snd := by
    intro c
    have := congrArg (fun k => k ≫ pullback.fst y y) c.condition
    simpa only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
      Category.comp_id] using this
  have hsnd : ∀ c : PullbackCone (pullback.lift (kt ≫ q) (ks ≫ q)
      (by simpa only [Category.assoc] using hKW.w)) (pullback.diagonal y),
      c.fst ≫ ks ≫ q = c.snd := by
    intro c
    have := congrArg (fun k => k ≫ pullback.snd y y) c.condition
    simpa only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
      Category.comp_id] using this
  apply IsPullback.of_isLimit' hc
  refine PullbackCone.IsLimit.mk hc.w
    (fun c => hR.lift (c.fst ≫ kt) (c.fst ≫ ks)
      (by simpa only [Category.assoc] using (hfst c).trans (hsnd c).symm))
    (fun c => hKW.hom_ext ?_ ?_) (fun c => ?_) (fun c m h₁ h₂ => hR.hom_ext ?_ ?_)
  · simp only [Category.assoc, hρ₁, IsPullback.lift_fst]
  · simp only [Category.assoc, hρ₂, IsPullback.lift_snd]
  · simp only [← Category.assoc, IsPullback.lift_fst]
    simpa only [Category.assoc] using hfst c
  · simp only [IsPullback.lift_fst, ← hρ₁, reassoc_of% h₁]
  · simp only [IsPullback.lift_snd, ← hρ₂, reassoc_of% h₁]

private theorem mono_of_mono_left {C : Type*} [Category* C] {X : C} {A A' : Over X}
    (f : A ⟶ A') (hf : Mono f.left) : Mono f := by
  refine ⟨fun {T} g h hgh => ?_⟩
  apply Over.OverMorphism.ext
  apply (cancel_mono f.left).mp
  simpa only [Over.comp_left] using congrArg (fun k => k.left) hgh

private theorem mono_left_of_mono {C : Type*} [Category* C] {X : C} {A A' : Over X}
    (f : A ⟶ A') (hf : Mono f) : Mono f.left := by
  refine ⟨fun {T} g h hgh => ?_⟩
  have hb : h ≫ A.hom = g ≫ A.hom := by
    rw [← Over.w f, ← Category.assoc, ← hgh, Category.assoc, Over.w f]
  let g' : Over.mk (g ≫ A.hom) ⟶ A := Over.homMk g
  let h' : Over.mk (g ≫ A.hom) ⟶ A := Over.homMk h hb
  have hgh' : g' ≫ f = h' ≫ f := Over.OverMorphism.ext (by simpa [g', h'] using hgh)
  simpa [g', h'] using congrArg (fun k => k.left) ((cancel_mono f).mp hgh')


/-- A morphism of the site whose Yoneda image is a monomorphism of presheaves is a
monomorphism of schemes over the base. -/
@[sga "3 VIB 10.1" "partial"]
private theorem mono_overPullback_map {C : Type*} [Category* C] [HasPullbacks C]
    {X X' : C} (p : X' ⟶ X) {Y Z : Over X} (f : Y ⟶ Z) (hf : Mono f) :
    Mono ((Over.pullback p).map f) := by
  infer_instance

private theorem mono_post_of_mono_yoneda
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A A' : AlgebraicGeometry.BigFppfOver B S hS} (ρ : A ⟶ A')
    (hρ : Mono (yoneda.map ρ)) :
    Mono ((Over.post (X := B.obj hS) B.inclusion).map ρ) := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hk : IsPullback (pullback.fst ρ ρ) (pullback.snd ρ ρ) ρ ρ :=
    IsPullback.of_hasPullback ρ ρ
  have heq : pullback.fst ρ ρ = pullback.snd ρ ρ := by
    apply yoneda.map_injective
    apply (cancel_mono (yoneda.map ρ)).mp
    simpa only [← yoneda.map_comp] using
      congrArg yoneda.map (pullback.condition (f := ρ) (g := ρ))
  have hQ : Mono (Q.map ρ) :=
    IsKernelPair.mono_of_eq_fst_snd (hk.map Q) (by rw [heq])
  exact Over.mono_of_mono_left _ (hk := hQ)

/-- Two algebraic spaces with a common surjective étale atlas and a common kernel pair
for it are isomorphic over that atlas. -/
private theorem exists_iso_of_common_atlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    {U R : AlgebraicGeometry.BigFppfOver B S hS} (s t : R ⟶ U)
    (w : yoneda.obj U ⟶ Y) (c : yoneda.obj U ⟶ Z)
    (hws : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (hwe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (hcs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf c)
    (hce : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf c)
    (hwk : IsPullback (yoneda.map s) (yoneda.map t) w w)
    (hck : IsPullback (yoneda.map s) (yoneda.map t) c c) :
    ∃ e : Y ≅ Z, w ≫ e.hom = c := by
  obtain ⟨hR, hU, ⟨hcw⟩⟩ := AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale
    B S hS w s t hwk hY hws hwe
  obtain ⟨hR', hU', ⟨hcc⟩⟩ := AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale
    B S hS c s t hck hZ' hcs hce
  let RF : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u) := ⟨yoneda.obj R, hR⟩
  let UF : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u) := ⟨yoneda.obj U, hU⟩
  let YF : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u) := ⟨Y, hY.isSheaf⟩
  let ZF : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u) := ⟨Z, hZ'.isSheaf⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let wf : UF ⟶ YF := ⟨w⟩
  let cf : UF ⟶ ZF := ⟨c⟩
  have hww : sf ≫ wf = tf ≫ wf := Sheaf.hom_ext hwk.w
  have hcw' : sf ≫ cf = tf ≫ cf := Sheaf.hom_ext hck.w
  have hcw1 : IsColimit (Cofork.ofπ wf hww) := hcw
  have hcc1 : IsColimit (Cofork.ofπ cf hcw') := hcc
  let φ := hcw1.desc (Cofork.ofπ cf hcw')
  let ψ := hcc1.desc (Cofork.ofπ wf hww)
  have hφ : wf ≫ φ = cf := hcw1.fac (Cofork.ofπ cf hcw') WalkingParallelPair.one
  have hψ : cf ≫ ψ = wf := hcc1.fac (Cofork.ofπ wf hww) WalkingParallelPair.one
  have hwEpi : Epi wf := epi_of_isColimit_cofork hcw1
  have hcEpi : Epi cf := epi_of_isColimit_cofork hcc1
  have hid₁ : φ ≫ ψ = 𝟙 YF := by
    apply (cancel_epi wf).mp
    rw [← Category.assoc, hφ, hψ, Category.comp_id]
  have hid₂ : ψ ≫ φ = 𝟙 ZF := by
    apply (cancel_epi cf).mp
    rw [← Category.assoc, hψ, hφ, Category.comp_id]
  refine ⟨⟨φ.hom, ψ.hom, ?_, ?_⟩, congrArg (fun k => k.hom) hφ⟩
  · exact congrArg (fun k => k.hom) hid₁
  · exact congrArg (fun k => k.hom) hid₂

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, Cardinal.mk (i ⟶ j) < B.cutoff.ord.cof)
variable (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))

include hSize hHomSize hD hAffine hQc hQs

omit [IsCofiltered I] hSize hHomSize hD hAffine hQc hQs in
private theorem essentiallySmall_boundedSchemes (κ : Cardinal.{u}) :
    EssentiallySmall.{u} (AlgebraicGeometry.SchemeBelow κ) := by
  classical
  let P : ObjectProperty Scheme.{u} := fun X =>
    ∃ R : CommRingCat.{u}, Cardinal.mk R ≤ κ ∧ Nonempty (X ≅ Spec R)
  let A := MvPolynomial κ.out ℤ
  let Q₀ := ObjectProperty.ofObj (fun J : Ideal A => Spec (CommRingCat.of (A ⧸ J)))
  have hP : ObjectProperty.EssentiallySmall.{u} P := by
    refine ⟨Q₀, inferInstance, ?_⟩
    rintro X ⟨R, hR, ⟨e⟩⟩
    let j := (show Nonempty (R ↪ κ.out) from by
      show Cardinal.mk R ≤ Cardinal.mk κ.out
      simpa using hR).some
    let f : A →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (Function.invFun j)
    have hf : Function.Surjective f := fun r =>
      ⟨MvPolynomial.X (j r), (MvPolynomial.eval₂Hom_X' _ _ _).trans
        (Function.leftInverse_invFun j.injective r)⟩
    refine ⟨Spec (CommRingCat.of (A ⧸ RingHom.ker f)), ⟨RingHom.ker f⟩, ?_⟩
    exact ⟨e ≪≫ Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
      (RingHom.quotientKerEquivOfSurjective hf)).op⟩
  let μ := Order.succ (max κ Cardinal.aleph0)
  let Q := P.colimitsCardinalClosure μ
  have hPQ : AlgebraicGeometry.schemeSizeBelow κ ≤ Q := by
    intro X hX
    have hμ : Cardinal.aleph0 ≤ μ := (le_max_right _ _).trans (Order.le_succ _)
    have hcard : HasCardinalLT X.AffineZariskiSite μ := by
      rw [hasCardinalLT_iff_cardinal_mk_lt]
      exact (X.mk_affineOpens_le_size.trans hX.le).trans_lt
        ((le_max_left _ _).trans_lt (Order.lt_succ _))
    let : Q.IsClosedUnderColimitsOfShape X.AffineZariskiSite :=
      P.isClosedUnderColimitsOfShape_colimitsCardinalClosure μ _
        ((hasCardinalLT_arrow_iff_of_isThin _ _ hμ).mpr hcard)
    apply Q.prop_of_isColimit (Scheme.AffineZariskiSite.isColimitCocone X)
    intro U
    apply P.le_colimitsCardinalClosure μ
    exact ⟨_, (X.mk_sections_le_size ⟨U.1, U.2⟩).trans hX.le, ⟨Iso.refl _⟩⟩
  let : ObjectProperty.EssentiallySmall.{u} (AlgebraicGeometry.schemeSizeBelow κ) :=
    ObjectProperty.EssentiallySmall.of_le hPQ
  infer_instance

omit [IsCofiltered I] hSize hHomSize hD hAffine hQc hQs in
private theorem essentiallySmall_overCategory {C : Type*} [Category.{u} C]
    [EssentiallySmall.{u} C] (X : C) : EssentiallySmall.{u} (Over X) :=
  essentiallySmall_of_fully_faithful (Over.post (equivSmallModel.{u} C).functor)

omit [IsCofiltered I] hSize hHomSize hD hAffine hQc hQs in
private theorem bigFppfOverHasSheafify (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u) := by
  let : EssentiallySmall.{u} B.Schemes := essentiallySmall_boundedSchemes B.cutoff
  let : EssentiallySmall.{u} (AlgebraicGeometry.BigFppfOver B S hS) :=
    essentiallySmall_overCategory _
  exact hasSheafifyEssentiallySmallSite _ _

/-- The presheaf represented by an object of the big fppf site over `S` is the presheaf of points
of its image under postcomposition with the inclusion of the site. -/
private noncomputable def yonedaIsoPointsOfPostInclusion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    yoneda.obj U ≅ Stacks.Groupoids.points (Over.post B.inclusion)
      ((Over.post B.inclusion).obj U) := by
  let F : AlgebraicGeometry.BigFppfOver B S hS ⥤
      Over ((B.inclusion).obj (B.obj hS)) := Over.post (X := B.obj hS) B.inclusion
  letI : F.Full := inferInstance
  letI : F.Faithful := inferInstance
  let hF : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  refine NatIso.ofComponents
    (fun T => Equiv.toIso (hF.homEquiv (X := T.unop)
      (Y := U))) ?_
  intro T T' f
  ext x
  rfl

omit [IsCofiltered I] hSize hHomSize hD hAffine hQc hQs in
private theorem representedAtlas_isSheaf (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : AlgebraicGeometry.BigFppfOver B S hS) :
    Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS)
      (Stacks.Groupoids.points (Over.post B.inclusion)
        ((Over.post B.inclusion).obj U)) := by
  apply (Presheaf.isSheaf_of_iso_iff (yonedaIsoPointsOfPostInclusion B S hS U)).mp
  exact (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U).isSheaf

private noncomputable def algebraicSpaceSheafDiagram :
    I ⥤ Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u) where
  obj i := ⟨D.obj i, (hD i).isSheaf⟩
  map f := ⟨D.map f⟩
  map_id i := by ext; simp
  map_comp f g := by ext; simp

omit hSize hHomSize hQc hQs in
private theorem exists_compatible_limit_presentation
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u)]
    (i₀ : I) (U₀ : Over S) (hU₀mem : B.Contains U₀.left)
    (hU₀ : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS)
      (Stacks.Groupoids.points (Over.post B.inclusion) U₀))
    (p₀ : AlgebraicGeometry.Space.representedSheaf B S hS U₀ hU₀ ⟶
      (algebraicSpaceSheafDiagram B S hS D hD).obj i₀)
    (hp₀ : Epi p₀)
    (hp₀Etale :
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) p₀.hom) :
    ∃ (U : Over S)
        (hU : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS)
          (Stacks.Groupoids.points (Over.post B.inclusion) U))
        (R : Over S) (j : Stacks.Groupoids.PreRelation R U)
        (q : AlgebraicGeometry.Space.representedSheaf B S hS U hU ⟶
          limit (algebraicSpaceSheafDiagram B S hS D hD))
        (f : U ⟶ U₀),
      IsPullback
          ((Over.post B.inclusion).op.whiskerLeft (yoneda.map f))
          q.hom p₀.hom
          (limit.π (algebraicSpaceSheafDiagram B S hS D hD) i₀).hom ∧
        ∃ (hq : Stacks.Groupoids.sourceMap (Over.post B.inclusion) j ≫ q.hom =
            Stacks.Groupoids.targetMap (Over.post B.inclusion) j ≫ q.hom),
          IsPullback
            (Stacks.Groupoids.sourceMap (Over.post B.inclusion) j)
            (Stacks.Groupoids.targetMap (Over.post B.inclusion) j)
            q.hom q.hom ∧
          Stacks.Groupoids.IsEtaleEquivalenceRelation j ∧
    IsIso (AlgebraicGeometry.Space.canonicalQuotientToLimit B S hS
            (algebraicSpaceSheafDiagram B S hS D hD) j hU q hq) :=
  AlgebraicGeometry.Space.exists_quotient_presentation_of_affine_transition
    B S hS (algebraicSpaceSheafDiagram B S hS D hD)
    (fun i => hD i) (fun {_ _} f => hAffine f)
    i₀ U₀ hU₀mem hU₀ p₀ hp₀ hp₀Etale

/- Given an affine chart of one stage, every later transition pulls it back to
   an affine chart. This is the scheme diagram underlying the presentation of
   the limit algebraic space. -/
private structure AffineStageChart (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (j : Over i₀) where
  U : AlgebraicGeometry.BigAffineFppf B S hS
  toStage : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U) ⟶ D.obj j.left
  toChart : (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U ⟶
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  isPullback : IsPullback toStage (yoneda.map toChart) (D.map j.hom) q₀

private noncomputable def affineStageChart (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (j : Over i₀) : AffineStageChart B S hS D i₀ U₀ q₀ j := by
  classical
  let h := hAff j.hom U₀ q₀
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choose (Classical.choose_spec (Classical.choose_spec h)),
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))⟩

private noncomputable def affineStageChartMap (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
        (affineStageChart B S hS D i₀ U₀ q₀ hAff j).U ⟶
      (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
        (affineStageChart B S hS D i₀ U₀ q₀ hAff k).U := by
  classical
  let Cj := affineStageChart B S hS D i₀ U₀ q₀ hAff j
  let Ck := affineStageChart B S hS D i₀ U₀ q₀ hAff k
  have hcomm : Cj.toStage ≫ D.map e.left ≫ D.map k.hom =
      yoneda.map Cj.toChart ≫ q₀ := by
    calc
      Cj.toStage ≫ D.map e.left ≫ D.map k.hom =
          Cj.toStage ≫ D.map (e.left ≫ k.hom) := by rw [← D.map_comp]
      _ = Cj.toStage ≫ D.map j.hom := by rw [Over.w e]
      _ = yoneda.map Cj.toChart ≫ q₀ := Cj.isPullback.w
  exact yoneda.preimage (Ck.isPullback.lift
    (Cj.toStage ≫ D.map e.left) (yoneda.map Cj.toChart) hcomm)

private theorem affineStageChartMap_toStage (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    yoneda.map (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
        (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toStage =
      (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toStage ≫ D.map e.left := by
  simp [affineStageChartMap]

private theorem affineStageChartMap_toChart (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    yoneda.map (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toChart =
      yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart := by
  simp [affineStageChartMap]


/-- The map from a pullback chart over the limit to the affine chart at a later stage,
named so that its two defining identities can be stated and used without unfolding the
`yoneda.preimage` that produces it. -/
private noncomputable def affineStageChartLift (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) (j : Over i₀) :
    U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
      (affineStageChart B S hS D i₀ U₀ q₀ hAff j).U := by
  classical
  exact yoneda.preimage ((affineStageChart B S hS D i₀ U₀ q₀ hAff j).isPullback.lift
    (p ≫ limit.π D j.left) (yoneda.map q) (by
      rw [Category.assoc, limit.w]
      exact h.w))

private noncomputable def affineStageChartOverDiagram (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) :
    Over i₀ ⥤ Over ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) where
  obj j := Over.mk (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart
  map e := Over.homMk (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) (by
    apply yoneda.map_injective
    simpa only [yoneda.map_comp, Over.mk_left, Over.mk_hom] using
      affineStageChartMap_toChart B S hS hZ D hSize hHomSize hD hAffine hQc hQs
        i₀ U₀ q₀ hAff e)
  map_id j := by
    apply Over.OverMorphism.ext
    apply yoneda.map_injective
    apply (affineStageChart B S hS D i₀ U₀ q₀ hAff j).isPullback.hom_ext
    · simp [affineStageChartMap]
    · simp [affineStageChartMap]
  map_comp {j k l} e f := by
    apply Over.OverMorphism.ext
    apply yoneda.map_injective
    apply (affineStageChart B S hS D i₀ U₀ q₀ hAff l).isPullback.hom_ext
    · simp [affineStageChartMap, Category.assoc]
    · simp [affineStageChartMap, Category.assoc]

private noncomputable def affineStageChartCone (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) :
    Cone (affineStageChartOverDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i₀ U₀ q₀ hAff) where
  pt := Over.mk q
  π := {
    app j := Over.homMk (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) (by
      apply yoneda.map_injective
      change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
          yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart = yoneda.map q
      simp [affineStageChartLift])
    naturality j k e := by
      simp only [Functor.const_obj_map]
      apply Over.OverMorphism.ext
      apply yoneda.map_injective
      apply (affineStageChart B S hS D i₀ U₀ q₀ hAff k).isPullback.hom_ext
      · change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h k) ≫
              (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toStage =
            yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j ≫
                affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
              (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toStage
        simp [affineStageChartLift, affineStageChartMap, Category.assoc, limit.w]
      · change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h k) ≫
              yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toChart =
            yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j ≫
                affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
              yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toChart
        simp [affineStageChartLift, affineStageChartMap, Category.assoc]
  }

private noncomputable def affineStageChartConeIsLimit (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) :
    IsLimit (affineStageChartCone B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i₀ U₀ q₀ hAff U p q h) := by
  let E := affineStageChartOverDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAff
  let c := affineStageChartCone B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAff U p q h
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  apply isLimitOfReflects (Over.forget T)
  apply isLimitOfReflects yoneda
  let p' : (E ⋙ Over.forget T) ⋙ yoneda ⟶ Over.forget i₀ ⋙ D := {
    app j := (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toStage
    naturality j k e :=
      affineStageChartMap_toStage B S hS hZ D hSize hHomSize hD hAffine hQc hQs
        i₀ U₀ q₀ hAff e
  }
  let q' : (E ⋙ Over.forget T) ⋙ yoneda ⟶ (Functor.const _).obj (yoneda.obj T) := {
    app j := yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart
    naturality j k e := by
      simpa [E, T, affineStageChartOverDiagram] using
        (affineStageChartMap_toChart B S hS hZ D hSize hHomSize hD hAffine hQc hQs
          i₀ U₀ q₀ hAff e)
  }
  exact isLimit_of_cartesian_cone D i₀ (yoneda.obj T) q₀ _ _ p' q'
    (fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAff j).isPullback)
    p (yoneda.map q) h
    (fun j => by
      change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
          (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toStage = p ≫ limit.π D j.left
      simp [affineStageChartLift])
    (fun j => by
      change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
          yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart = yoneda.map q
      simp [affineStageChartLift])

private theorem existsUnique_affineStageRelationMap (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (q₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    {j k : Over i} (e : j ⟶ k) :
    let Cj := affineStageChart B S hS D i U₀ q₀ hAffine j
    let Ck := affineStageChart B S hS D i U₀ q₀ hAffine k
    let Kj := atlasKernelPair B S hS Cj.toStage (hD j.left).diagonal_representable
    let Kk := atlasKernelPair B S hS Ck.toStage (hD k.left).diagonal_representable
    ∃! r : Kj.R ⟶ Kk.R,
      r ≫ Kk.s = Kj.s ≫ affineStageChartMap B S hS D i U₀ q₀ hAffine e ∧
      r ≫ Kk.t = Kj.t ≫ affineStageChartMap B S hS D i U₀ q₀ hAffine e := by
  dsimp only
  let Cj := affineStageChart B S hS D i U₀ q₀ hAffine j
  let Ck := affineStageChart B S hS D i U₀ q₀ hAffine k
  let Kj := atlasKernelPair B S hS Cj.toStage (hD j.left).diagonal_representable
  let Kk := atlasKernelPair B S hS Ck.toStage (hD k.left).diagonal_representable
  let u := affineStageChartMap B S hS D i U₀ q₀ hAffine e
  have hu : yoneda.map u ≫ Ck.toStage = Cj.toStage ≫ D.map e.left :=
    affineStageChartMap_toStage B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i U₀ q₀ hAffine e
  let r : Kj.R ⟶ Kk.R := yoneda.preimage (Kk.kernelPair.lift
    (yoneda.map Kj.s ≫ yoneda.map u) (yoneda.map Kj.t ≫ yoneda.map u) (by
      simp only [Category.assoc, hu]
      rw [← Category.assoc, Kj.kernelPair.w, Category.assoc]))
  have ht : r ≫ Kk.s = Kj.s ≫ u := by
    apply yoneda.map_injective
    simp [r]
  have hs : r ≫ Kk.t = Kj.t ≫ u := by
    apply yoneda.map_injective
    simp [r]
  refine ⟨r, ⟨ht, hs⟩, ?_⟩
  intro r' hr'
  apply yoneda.map_injective
  apply Kk.kernelPair.hom_ext
  · simpa only [← yoneda.map_comp] using congrArg yoneda.map (hr'.1.trans ht.symm)
  · simpa only [← yoneda.map_comp] using congrArg yoneda.map (hr'.2.trans hs.symm)

private theorem eventually_eq_on_affine_chart (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i₀)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ Z)
    (hf : f ≫ a = q₀) (hg : g ≫ a = q₀)
    (hfg : pullback.snd (limit.π D i₀) q₀ ≫ f =
      pullback.snd (limit.π D i₀) q₀ ≫ g) :
    ∃ j : Over i₀,
      yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ f =
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ g := by
  obtain ⟨U, p, q, h⟩ :=
    AlgebraicGeometry.Space.isAffineHom_limitπ B S hS D hSize hHomSize hAffine i₀ U₀ q₀
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let E := affineStageChartOverDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAffine
  let c := affineStageChartCone B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAffine _ p q h
  let hc := affineStageChartConeIsLimit B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAffine _ p q h
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
    fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.property
  have hh : yoneda.map q ≫ f = yoneda.map q ≫ g := by
    simpa using congrArg (fun k => h.isoPullback.hom ≫ k) hfg
  exact eventually_eq_homs_of_locallyOfFinitePresentation B S hS hZalg (hD i₀)
    a ha T q₀ E c
    (isLimit_toScheme_of_affine B S hS (cardinalMk_over_lt B hSize hHomSize i₀)
      (E ⋙ Over.forget T) hE ((Over.forget T).mapCone c)
      (isLimitOfPreserves (Over.forget T) hc))
    hE U.property f g hf hg hh

private theorem exists_hom_on_affine_chart (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj U₀.obj ⟶ D.obj i₀)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i₀)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f : pullback (limit.π D i₀) q₀ ⟶ Z)
    (hf : f ≫ a = pullback.fst _ _ ≫ limit.π D i₀) :
    ∃ (j : Over i₀) (g : yoneda.obj
      (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.obj ⟶ Z),
      g ≫ a = (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toStage ≫ D.map j.hom ∧
      (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.lift
        (pullback.fst _ _ ≫ limit.π D j.left) (pullback.snd _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition) ≫ g = f := by
  obtain ⟨U, p, q, h⟩ :=
    AlgebraicGeometry.Space.isAffineHom_limitπ B S hS D hSize hHomSize hAffine i₀ U₀ q₀
  let E := affineStageChartOverDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAffine
  let c := affineStageChartCone B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAffine _ p q h
  let hc := affineStageChartConeIsLimit B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAffine _ p q h
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
    fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.property
  obtain ⟨j, g, hg, he⟩ := exists_hom_of_locallyOfFinitePresentation B S hS hZalg
    (hD i₀) a ha U₀.obj q₀ E c
    (isLimit_toScheme_of_affine B S hS (cardinalMk_over_lt B hSize hHomSize i₀)
      (E ⋙ Over.forget U₀.obj) hE ((Over.forget U₀.obj).mapCone c)
      (isLimitOfPreserves (Over.forget U₀.obj) hc))
    hE U.property (h.isoPullback.hom ≫ f) (by
      show (h.isoPullback.hom ≫ f) ≫ a = yoneda.map q ≫ q₀
      rw [Category.assoc, hf, IsPullback.isoPullback_hom_fst_assoc]
      exact h.w)
  refine ⟨j, g, hg.trans (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.w.symm, ?_⟩
  apply (Iso.cancel_iso_hom_left h.isoPullback _ _).mp
  have hh : h.isoPullback.hom ≫
      (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.lift
        (pullback.fst _ _ ≫ limit.π D j.left) (pullback.snd _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition) =
      yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAffine _ p q h j) := by
    apply (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.hom_ext
    · simp [affineStageChartLift]
    · simp [affineStageChartLift]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ g) hh).trans he)

private theorem eventually_eq_on_affine_chart_over (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    {G Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (b : D.obj i₀ ⟶ G)
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ Z)
    (hf : f ≫ a = q₀ ≫ b) (hg : g ≫ a = q₀ ≫ b)
    (hfg : pullback.snd (limit.π D i₀) q₀ ≫ f =
      pullback.snd (limit.π D i₀) q₀ ≫ g) :
    ∃ j : Over i₀,
      yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ f =
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ g := by
  obtain ⟨U, p, q, h⟩ :=
    AlgebraicGeometry.Space.isAffineHom_limitπ B S hS D hSize hHomSize hAffine i₀ U₀ q₀
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let E := affineStageChartOverDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAffine
  let c := affineStageChartCone B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAffine _ p q h
  let hc := affineStageChartConeIsLimit B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAffine _ p q h
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
    fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.property
  have hh : yoneda.map q ≫ f = yoneda.map q ≫ g := by
    simpa using congrArg (fun k => h.isoPullback.hom ≫ k) hfg
  exact eventually_eq_homs_of_locallyOfFinitePresentation B S hS hZalg hG
    a ha T (q₀ ≫ b) E c
    (isLimit_toScheme_of_affine B S hS (cardinalMk_over_lt B hSize hHomSize i₀)
      (E ⋙ Over.forget T) hE ((Over.forget T).mapCone c)
      (isLimitOfPreserves (Over.forget T) hc))
    hE U.property f g hf hg hh

private noncomputable def affineStageChartDiagram (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) :
    Over i₀ ⥤ Scheme.{u} := {
  obj j := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
    ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
      (affineStageChart B S hS D i₀ U₀ q₀ hAff j).U)
  map e := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
    (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e)
  map_id j := by
    let Cj := affineStageChart B S hS D i₀ U₀ q₀ hAff j
    have hsrc : affineStageChartMap B S hS D i₀ U₀ q₀ hAff (𝟙 j) = 𝟙 _ := by
      apply yoneda.map_injective
      apply Cj.isPullback.hom_ext
      · simp [affineStageChartMap, Cj]
      · simp [affineStageChartMap, Cj]
    simpa using congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS |>.map) hsrc
  map_comp {j k l} e f := by
    let Cj := affineStageChart B S hS D i₀ U₀ q₀ hAff j
    let Ck := affineStageChart B S hS D i₀ U₀ q₀ hAff k
    let Cl := affineStageChart B S hS D i₀ U₀ q₀ hAff l
    have hsrc : affineStageChartMap B S hS D i₀ U₀ q₀ hAff (e ≫ f) =
        affineStageChartMap B S hS D i₀ U₀ q₀ hAff e ≫
          affineStageChartMap B S hS D i₀ U₀ q₀ hAff f := by
      apply yoneda.map_injective
      apply Cl.isPullback.hom_ext
      · rw [affineStageChartMap_toStage B S hS hZ D hSize hHomSize hD hAffine hQc hQs
          i₀ U₀ q₀ hAff (e ≫ f)]
        rw [yoneda.map_comp, Category.assoc]
        rw [affineStageChartMap_toStage B S hS hZ D hSize hHomSize hD hAffine hQc hQs
          i₀ U₀ q₀ hAff f]
        rw [← Category.assoc,
          affineStageChartMap_toStage B S hS hZ D hSize hHomSize hD hAffine hQc hQs
            i₀ U₀ q₀ hAff e]
        rw [Category.assoc, ← D.map_comp]
        simp only [Over.comp_left]
      · rw [affineStageChartMap_toChart B S hS hZ D hSize hHomSize hD hAffine hQc hQs
          i₀ U₀ q₀ hAff (e ≫ f)]
        rw [yoneda.map_comp, Category.assoc]
        rw [affineStageChartMap_toChart B S hS hZ D hSize hHomSize hD hAffine hQc hQs
          i₀ U₀ q₀ hAff f]
        exact (affineStageChartMap_toChart B S hS hZ D hSize hHomSize hD hAffine hQc hQs
          i₀ U₀ q₀ hAff e).symm
    simpa [Functor.map_comp] using congrArg
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS |>.map) hsrc
}

private theorem affineStageChartDiagram_map_isAffineHom (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    _root_.AlgebraicGeometry.IsAffineHom
        ((affineStageChartDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i₀ U₀ q₀ hAff).map e) := by
  let Cj := affineStageChart B S hS D i₀ U₀ q₀ hAff j
  let Ck := affineStageChart B S hS D i₀ U₀ q₀ hAff k
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj Cj.U)) := Cj.U.property
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj Ck.U)) := Ck.U.property
  show _root_.AlgebraicGeometry.IsAffineHom ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
    (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e))
  exact AlgebraicGeometry.isAffineHom_of_isAffine _

private theorem affineStageChartDiagram_obj_isAffine (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) (j : Over i₀) :
    IsAffine ((affineStageChartDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i₀ U₀ q₀ hAff).obj j) := by
  show IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
    ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
      (affineStageChart B S hS D i₀ U₀ q₀ hAff j).U))
  exact (affineStageChart B S hS D i₀ U₀ q₀ hAff j).U.property

private theorem affineStageChartDiagram_obj_compact (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) (j : Over i₀) :
    CompactSpace ((affineStageChartDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i₀ U₀ q₀ hAff).obj j) := by
  let := affineStageChartDiagram_obj_isAffine B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAff j
  infer_instance

private theorem affineStageChartDiagram_obj_quasiSeparated (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) (j : Over i₀) :
    QuasiSeparatedSpace ((affineStageChartDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i₀ U₀ q₀ hAff).obj j) := by
  let := affineStageChartDiagram_obj_isAffine B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAff j
  infer_instance

private theorem affineStageChartScheme_model_of_finitePresentation (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (c : Cone (affineStageChartDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i₀ U₀ q₀ hAff))
    (hc : IsLimit c) (X : Over c.pt) (hFp : AlgebraicGeometry.FinitePresentation X.hom) :
    ∃ (j : Over i₀) (Xⱼ : Over ((affineStageChartDiagram B S hS hZ D hSize hHomSize hD
      hAffine hQc hQs i₀ U₀ q₀ hAff).obj j)),
      AlgebraicGeometry.FinitePresentation Xⱼ.hom ∧
        Nonempty (X ≅ (Over.pullback (c.π.app j)).obj Xⱼ) := by
  let E := affineStageChartDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i₀ U₀ q₀ hAff
  let : ∀ {j k : Over i₀} (e : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (E.map e) := by
    intro j k e
    exact affineStageChartDiagram_map_isAffineHom B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i₀ U₀ q₀ hAff e
  let : ∀ j : Over i₀, CompactSpace (E.obj j) := fun j =>
    affineStageChartDiagram_obj_compact B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i₀ U₀ q₀ hAff j
  let : ∀ j : Over i₀, QuasiSeparatedSpace (E.obj j) := fun j =>
    affineStageChartDiagram_obj_quasiSeparated B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i₀ U₀ q₀ hAff j
  exact scheme_model_of_finitePresentation E c hc X hFp

omit hQs in
private theorem exists_affine_limit_atlas (i : I) :
    ∃ (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
      (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
      (q : U.obj ⟶ U₀.obj),
      IsPullback p (yoneda.map q) (limit.π D i) p₀ ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p := by
  obtain ⟨U₀, p₀, hU₀, hs, he⟩ := exists_affine_etale_atlas B S hS (D.obj i) (hD i) (hQc i)
  let U₀' : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  obtain ⟨U, p, q, hp⟩ := AlgebraicGeometry.Space.isAffineHom_limitπ B S hS D hSize hHomSize
      hAffine i U₀' p₀
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  exact ⟨U₀', p₀, U, p, q, hp, P.presheaf.of_isPullback hp.flip hs,
    Q.presheaf.of_isPullback hp.flip (represented_etale_of_isEtale B S hS p₀ he)⟩

private theorem exists_model_over_affine_chart (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) :
    let c := affineStageChartCone B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i U₀ p₀ hAffine U.obj p q hp
    ∃ (j : Over i) (Wj : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (affineStageChart B S hS D i U₀ p₀ hAffine j).U.obj)),
      AlgebraicGeometry.FinitePresentation Wj.hom ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
        (Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
            (c.π.app j).left)).obj Wj) := by
  dsimp only
  let E := affineStageChartOverDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i U₀ p₀ hAffine
  let c := affineStageChartCone B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i U₀ p₀ hAffine U.obj p q hp
  let hc := affineStageChartConeIsLimit B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i U₀ p₀ hAffine U.obj p q hp
  let : IsConnected (Over i) := IsCofiltered.isConnected _
  let F := E ⋙ Over.forget U₀.obj
  let G := F ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hF : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (F.obj j)) :=
    fun j => (affineStageChart B S hS D i U₀ p₀ hAffine j).U.property
  let : ∀ j, IsAffine (G.obj j) := hF
  let : ∀ {j k : Over i} (e : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (G.map e) :=
      fun {_ _} _ => inferInstance
  let : ∀ j : Over i, CompactSpace (G.obj j) := fun _ => inferInstance
  let : ∀ j : Over i, QuasiSeparatedSpace (G.obj j) := fun _ => inferInstance
  let sc := (Over.forget U₀.obj ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c
  have hsc : IsLimit sc := isLimit_toScheme_of_affine B S hS
    (cardinalMk_over_lt B hSize hHomSize i) F hF ((Over.forget U₀.obj).mapCone c)
    (isLimitOfPreserves (Over.forget U₀.obj) hc)
  exact scheme_model_of_finitePresentation G sc hsc
    (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) hg

private theorem exists_affine_model_over_affine_chart (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g))
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)] :
    let c := affineStageChartCone B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i U₀ p₀ hAffine U.obj p q hp
    ∃ (j : Over i) (Wj : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (affineStageChart B S hS D i U₀ p₀ hAffine j).U.obj)),
      AlgebraicGeometry.FinitePresentation Wj.hom ∧ IsAffine Wj.left ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
        (Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
            (c.π.app j).left)).obj Wj) := by
  dsimp only
  let E := affineStageChartOverDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i U₀ p₀ hAffine
  let c := affineStageChartCone B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i U₀ p₀ hAffine U.obj p q hp
  let hc := affineStageChartConeIsLimit B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i U₀ p₀ hAffine U.obj p q hp
  let : IsConnected (Over i) := IsCofiltered.isConnected _
  let F := E ⋙ Over.forget U₀.obj
  let G := F ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hF : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (F.obj j)) :=
    fun j => (affineStageChart B S hS D i U₀ p₀ hAffine j).U.property
  let : ∀ j, IsAffine (G.obj j) := hF
  let : ∀ {j k : Over i} (e : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (G.map e) :=
      fun {_ _} _ => inferInstance
  let : ∀ j : Over i, CompactSpace (G.obj j) := fun _ => inferInstance
  let : ∀ j : Over i, QuasiSeparatedSpace (G.obj j) := fun _ => inferInstance
  let sc := (Over.forget U₀.obj ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c
  have hsc : IsLimit sc := isLimit_toScheme_of_affine B S hS
    (cardinalMk_over_lt B hSize hHomSize i) F hF ((Over.forget U₀.obj).mapCone c)
    (isLimitOfPreserves (Over.forget U₀.obj) hc)
  exact scheme_affine_model_of_finitePresentation G sc hsc
    (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) hg
    ‹IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)›

private theorem exists_site_model_over_affine_chart (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (hp₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p₀)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) :
    ∃ (j : Over i) (V : AlgebraicGeometry.BigFppfOver B S hS)
      (v : yoneda.obj V ⟶ D.obj j.left) (a : W ⟶ V),
      AlgebraicGeometry.Space.IsFinitePresentation B S hS v ∧
      IsPullback (yoneda.map a) (yoneda.map g ≫ p) v (limit.π D j.left) := by
  let c := affineStageChartCone B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i U₀ p₀ hAffine U.obj p q hp
  obtain ⟨j, V₀, hV₀, ⟨e⟩⟩ := exists_model_over_affine_chart B S hS hZ D hSize hHomSize
    hD hAffine hQc hQs i U₀ p₀ U p q hp W g hg
  let Cj := affineStageChart B S hS D i U₀ p₀ hAffine j
  let b : U.obj ⟶ Cj.U.obj := (c.π.app j).left
  obtain ⟨V, f, a, hf, _, ha⟩ := exists_site_pullback_model B S hS b g V₀ hV₀ e
  have hbp : yoneda.map b ≫ Cj.toStage = p ≫ limit.π D j.left := by
    show yoneda.map (affineStageChartLift B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        (affineStageChart B S hS D i U₀ p₀ hAffine j).toStage = p ≫ limit.π D j.left
    simp [affineStageChartLift]
  have hbq : yoneda.map b ≫ yoneda.map Cj.toChart = yoneda.map q := by
    show yoneda.map (affineStageChartLift B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        yoneda.map (affineStageChart B S hS D i U₀ p₀ hAffine j).toChart = yoneda.map q
    simp [affineStageChartLift]
  have hU : IsPullback (yoneda.map b) p Cj.toStage (limit.π D j.left) := by
    apply IsPullback.of_right (h₂₂ := D.map j.hom) _ hbp Cj.isPullback.flip
    rw [hbq, limit.w]
    exact hp.flip
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (etaleInverseImageIsStableUnderComposition _)
  have hpc : P.presheaf Cj.toStage := P.presheaf.of_isPullback Cj.isPullback.flip hp₀
  let : IsAffine (Q.obj Cj.U.obj) := Cj.U.property
  let : LocallyOfFinitePresentation (Q.map f) := hf.1
  let : QuasiCompact (Q.map f) := hf.2.1
  let : QuasiSeparated (Q.map f) := hf.2.2
  have hVqc : CompactSpace (Q.obj V) := QuasiCompact.compactSpace_of_compactSpace (Q.map f)
  have hVqs : QuasiSeparatedSpace (Q.obj V) :=
    quasiSeparatedSpace_of_quasiSeparated (Q.map f)
  refine ⟨j, V, yoneda.map f ≫ Cj.toStage, a,
    isFinitePresentation_of_scheme_chart B S hS hZ (hD j.left) (hQs j.left)
      V Cj.U.obj hVqc hVqs f Cj.toStage hpc hf.1, ?_⟩
  exact (ha.map yoneda).paste_vert hU

private theorem exists_affine_site_model_over_affine_chart (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (hp₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p₀)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g))
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)] :
    ∃ (j : Over i) (V : AlgebraicGeometry.BigFppfOver B S hS)
      (v : yoneda.obj V ⟶ D.obj j.left) (a : W ⟶ V),
      AlgebraicGeometry.Space.IsFinitePresentation B S hS v ∧
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V) ∧
      IsPullback (yoneda.map a) (yoneda.map g ≫ p) v (limit.π D j.left) := by
  let c := affineStageChartCone B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i U₀ p₀ hAffine U.obj p q hp
  obtain ⟨j, V₀, hV₀, hV₀aff, ⟨e⟩⟩ := exists_affine_model_over_affine_chart B S hS hZ
      D hSize hHomSize
    hD hAffine hQc hQs i U₀ p₀ U p q hp W g hg
  let Cj := affineStageChart B S hS D i U₀ p₀ hAffine j
  let b : U.obj ⟶ Cj.U.obj := (c.π.app j).left
  obtain ⟨V, f, a, hf, ⟨eV⟩, ha⟩ := exists_site_pullback_model B S hS b g V₀ hV₀ e
  have hbp : yoneda.map b ≫ Cj.toStage = p ≫ limit.π D j.left := by
    show yoneda.map (affineStageChartLift B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        (affineStageChart B S hS D i U₀ p₀ hAffine j).toStage = p ≫ limit.π D j.left
    simp [affineStageChartLift]
  have hbq : yoneda.map b ≫ yoneda.map Cj.toChart = yoneda.map q := by
    show yoneda.map (affineStageChartLift B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        yoneda.map (affineStageChart B S hS D i U₀ p₀ hAffine j).toChart = yoneda.map q
    simp [affineStageChartLift]
  have hU : IsPullback (yoneda.map b) p Cj.toStage (limit.π D j.left) := by
    apply IsPullback.of_right (h₂₂ := D.map j.hom) _ hbp Cj.isPullback.flip
    rw [hbq, limit.w]
    exact hp.flip
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (etaleInverseImageIsStableUnderComposition _)
  have hpc : P.presheaf Cj.toStage := P.presheaf.of_isPullback Cj.isPullback.flip hp₀
  let : IsAffine (Q.obj Cj.U.obj) := Cj.U.property
  let : LocallyOfFinitePresentation (Q.map f) := hf.1
  let : QuasiCompact (Q.map f) := hf.2.1
  let : QuasiSeparated (Q.map f) := hf.2.2
  have hVqc : CompactSpace (Q.obj V) := QuasiCompact.compactSpace_of_compactSpace (Q.map f)
  have hVqs : QuasiSeparatedSpace (Q.obj V) :=
    quasiSeparatedSpace_of_quasiSeparated (Q.map f)
  refine ⟨j, V, yoneda.map f ≫ Cj.toStage, a,
    isFinitePresentation_of_scheme_chart B S hS hZ (hD j.left) (hQs j.left)
      V Cj.U.obj hVqc hVqs f Cj.toStage hpc hf.1, ?_, ?_⟩
  · let : IsAffine V₀.left := hV₀aff
    let : IsIso eV.hom.left :=
      inferInstanceAs (IsIso ((Over.forget ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
        Cj.U.obj)).map eV.hom))
    exact IsAffine.of_isIso eV.hom.left
  · exact (ha.map yoneda).paste_vert hU

private theorem eventually_etale_over_affine_chart (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (X : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀.obj))
    (hX : AlgebraicGeometry.FinitePresentation X.hom)
    [Etale ((Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)).obj X).hom] :
    ∃ j : Over i, Etale ((Over.pullback
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (affineStageChart B S hS D i U₀ p₀ hAffine j).toChart)).obj X).hom := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let E := affineStageChartOverDiagram B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i U₀ p₀ hAffine
  let c := affineStageChartCone B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i U₀ p₀ hAffine U.obj p q hp
  let hc := affineStageChartConeIsLimit B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    i U₀ p₀ hAffine U.obj p q hp
  let : IsConnected (Over i) := IsCofiltered.isConnected _
  let F := E ⋙ Over.forget U₀.obj
  let E' := E ⋙ Over.post Q
  let sc := (Over.post Q).mapCone c
  have hF (j : Over i) : IsAffine (Q.obj (F.obj j)) :=
    (affineStageChart B S hS D i U₀ p₀ hAffine j).U.property
  have hsc : IsLimit ((Over.forget (Q.obj U₀.obj)).mapCone sc) :=
    isLimit_toScheme_of_affine B S hS (cardinalMk_over_lt B hSize hHomSize i)
      F hF ((Over.forget U₀.obj).mapCone c) (isLimitOfPreserves (Over.forget U₀.obj) hc)
  let : ∀ j, IsAffine (E'.obj j).left := hF
  let : ∀ {j k : Over i} (a : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (E'.map a).left := by
    intro j k a
    infer_instance
  let : Etale ((Over.pullback sc.pt.hom).obj X).hom :=
    ‹Etale ((Over.pullback (Q.map q)).obj X).hom›
  exact scheme_eventually_etale_pullback E' sc hsc X hX

private theorem exists_finitePresentation_atlas_model (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (Y : Over (limit D)) (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hf : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom) :
    let c := affineStageChartCone B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i U₀ p₀ hAffine U.obj p q hp
    ∃ (W : AlgebraicGeometry.BigAffineFppf B S hS) (w : yoneda.obj W.obj ⟶ Y.left)
      (g : W.obj ⟶ U.obj) (j : Over i)
      (Wj : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
        (affineStageChart B S hS D i U₀ p₀ hAffine j).U.obj)),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w ∧
      yoneda.map g ≫ p = w ≫ Y.hom ∧ AlgebraicGeometry.FinitePresentation Wj.hom ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
        (Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
            (c.π.app j).left)).obj Wj) := by
  obtain ⟨W, w, g, hws, hwe, hw, hg⟩ := exists_affine_finitePresentation_chart B S hS
    (AlgebraicGeometry.Space.isAlgebraicSpace_limit B S hS D hSize hHomSize hD hAffine) hY
        Y.hom hf U p hs he
  obtain ⟨j, Wj, hWj, hmodel⟩ := exists_model_over_affine_chart B S hS hZ D hSize hHomSize
    hD hAffine hQc hQs i U₀ p₀ U p q hp W.obj g hg
  exact ⟨W, w, g, j, Wj, hws, hwe, hw, hWj, hmodel⟩

private theorem eventually_eq_on_quasiCompact_source (i : I)
    {Y Z G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hYqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS Y)
    (r : Y ⟶ D.obj i) (a : Z ⟶ G) (b : D.obj i ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : Y ⟶ Z) (hf : f ≫ a = r ≫ b) (hg : g ≫ a = r ≫ b)
    (hfg : pullback.fst r (limit.π D i) ≫ f =
      pullback.fst r (limit.π D i) ≫ g) :
    ∃ (j : I) (e : j ⟶ i),
      pullback.fst r (D.map e) ≫ f = pullback.fst r (D.map e) ≫ g := by
  classical
  obtain ⟨U₀, q₀, hU₀, hsurj, het⟩ := exists_affine_etale_atlas B S hS Y hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hh : pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀ ≫ f =
      pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀ ≫ g := by
    let k : pullback (limit.π D i) (q₀ ≫ r) ⟶ pullback r (limit.π D i) :=
      pullback.lift (pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀)
      (pullback.fst (limit.π D i) (q₀ ≫ r))
      (by simp only [Category.assoc, pullback.condition])
    simpa [k] using congrArg (fun t => k ≫ t) hfg
  obtain ⟨j, hj⟩ := eventually_eq_on_affine_chart_over B S hS hZ D hSize hHomSize
    hD hAffine hQc hQs i U (q₀ ≫ r) hG b hZalg a ha
    (q₀ ≫ f) (q₀ ≫ g) (by simp [hf]) (by simp [hg]) hh
  refine ⟨j.left, j.hom, ?_⟩
  let C := affineStageChart B S hS D i U (q₀ ≫ r) hAffine j
  let p : yoneda.obj C.U.obj ⟶ pullback r (D.map j.hom) :=
    pullback.lift (yoneda.map C.toChart ≫ q₀) C.toStage
      (by simpa only [Category.assoc] using C.isPullback.w.symm)
  have hp : IsPullback (yoneda.map C.toChart) p q₀
      (pullback.fst r (D.map j.hom)) := by
    apply IsPullback.of_bot _ (by simp [p]) (IsPullback.of_hasPullback r (D.map j.hom))
    simpa [p] using C.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  apply hom_ext_of_surjective_etale_atlas B S hS
    (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS r (D.map j.hom) hY (hD j.left) (hD i))
    hZalg.isSheaf p
    (P.presheaf.of_isPullback hp hsurj)
    (Q.presheaf.of_isPullback hp (represented_etale_of_isEtale B S hS q₀ het))
  simpa [p, Category.assoc] using hj

omit hSize hHomSize hD hAffine hQc hQs in
private theorem exists_hom_of_equalizes_atlas
    {Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hZsh : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) Z)
    {U : AlgebraicGeometry.BigFppfOver B S hS} (q : yoneda.obj U ⟶ Y)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (f : yoneda.obj U ⟶ Z)
    (hf : pullback.fst q q ≫ f = pullback.snd q q ≫ f) :
    ∃ g : Y ⟶ Z, q ≫ g = f := by
  let K := atlasKernelPair B S hS q hY.diagonal_representable
  obtain ⟨hR, hU, ⟨hc⟩⟩ := AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale
    B S hS q K.s K.t K.kernelPair hY hs he
  have hw : yoneda.map K.s ≫ f = yoneda.map K.t ≫ f := by
    simpa using congrArg (fun k => K.kernelPair.isoPullback.hom ≫ k) hf
  let sf : (⟨yoneda.obj K.R, hR⟩ : Sheaf _ (Type u)) ⟶ ⟨yoneda.obj U, hU⟩ :=
    ⟨yoneda.map K.s⟩
  let tf : (⟨yoneda.obj K.R, hR⟩ : Sheaf _ (Type u)) ⟶ ⟨yoneda.obj U, hU⟩ :=
    ⟨yoneda.map K.t⟩
  let ff : (⟨yoneda.obj U, hU⟩ : Sheaf _ (Type u)) ⟶ ⟨Z, hZsh⟩ := ⟨f⟩
  let fc : Cofork sf tf := Cofork.ofπ ff (show sf ≫ ff = tf ≫ ff from Sheaf.hom_ext hw)
  exact ⟨(hc.desc fc).hom, congrArg (fun k => k.hom) (hc.fac fc WalkingParallelPair.one)⟩

omit hSize hHomSize hD hAffine hQc hQs in
/-- The public form of the private `exists_hom_of_equalizes_atlas` above. -/
theorem FinitePresentationDescent.exists_hom_of_equalizes_atlas
    {Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hZsh : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) Z)
    {U : AlgebraicGeometry.BigFppfOver B S hS} (q : yoneda.obj U ⟶ Y)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (f : yoneda.obj U ⟶ Z)
    (hf : pullback.fst q q ≫ f = pullback.snd q q ≫ f) :
    ∃ g : Y ⟶ Z, q ≫ g = f :=
  _root_.AlgebraicGeometry.Space.exists_hom_of_equalizes_atlas B S hS hY hZsh q hs he f hf

omit [IsCofiltered I] hZ hSize hHomSize hD hAffine hQc hQs in
/-- An algebraic space with an affine surjective étale atlas is quasi-compact. -/
private theorem isQuasiCompact_of_affine_atlas
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Wo : AlgebraicGeometry.BigFppfOver B S hS}
    (hWoAff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Wo))
    (q : yoneda.obj Wo ⟶ X)
    (hqs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q) :
    AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X := by
  let _ : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  let _ : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  let _ : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) :=
    MorphismProperty.relative_isStableUnderComposition _
  refine ⟨Wo, q, ?_, hqs, fun V φ hφ => MorphismProperty.comp_mem _ _ _ hφ hqe⟩
  let _ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Wo) := hWoAff
  infer_instance

omit [IsCofiltered I] hSize hHomSize hD hAffine hQc hQs in
include hZ in
/-- A map of algebraic spaces is quasi-separated as soon as its source has an affine
surjective étale atlas whose kernel pair is quasi-compact. -/
private theorem isQuasiSeparated_of_affine_atlas
    {T X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : AlgebraicGeometry.IsAlgebraicSpace B S hS T)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    {Wo Ro : AlgebraicGeometry.BigFppfOver B S hS}
    (hWoAff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Wo))
    (q : yoneda.obj Wo ⟶ X)
    (hqs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (y : X ⟶ T) (sR tR : Ro ⟶ Wo)
    (hqk : IsPullback (yoneda.map sR) (yoneda.map tR) q q)
    (hRoqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (yoneda.obj Ro)) :
    AlgebraicGeometry.Space.IsQuasiSeparated B S hS y := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) Q
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : E.presheaf.IsStableUnderBaseChange := E.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : E.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition E (etaleInverseImageIsStableUnderComposition _)
  let WoA : AlgebraicGeometry.BigAffineFppf B S hS := ⟨Wo, hWoAff⟩
  let KW := atlasKernelPair B S hS (q ≫ y) hT.diagonal_representable
  have hKWw : yoneda.map KW.s ≫ q ≫ y = yoneda.map KW.t ≫ q ≫ y :=
    KW.kernelPair.w
  have hcomm : yoneda.map sR ≫ q ≫ y = yoneda.map tR ≫ q ≫ y := by
    rw [← Category.assoc, ← Category.assoc, hqk.w]
  let ρ : Ro ⟶ KW.R := yoneda.preimage
    (KW.kernelPair.lift (yoneda.map sR) (yoneda.map tR) hcomm)
  have hρ : yoneda.map ρ = KW.kernelPair.lift (yoneda.map sR) (yoneda.map tR) hcomm :=
    yoneda.map_preimage _
  have hρ₁ : yoneda.map ρ ≫ yoneda.map KW.s = yoneda.map sR := by
    rw [hρ]; exact KW.kernelPair.lift_fst _ _ _
  have hρ₂ : yoneda.map ρ ≫ yoneda.map KW.t = yoneda.map tR := by
    rw [hρ]; exact KW.kernelPair.lift_snd _ _ _
  let g₁ : yoneda.obj KW.R ⟶ pullback (q ≫ y) y :=
    pullback.lift (yoneda.map KW.s) (yoneda.map KW.t ≫ q)
      (by simpa only [Category.assoc] using hKWw)
  let g₂ : pullback (q ≫ y) y ⟶ pullback y y :=
    pullback.lift (pullback.fst (q ≫ y) y ≫ q) (pullback.snd (q ≫ y) y)
      (by rw [Category.assoc]; exact pullback.condition)
  have hg₁ : IsPullback g₁ (yoneda.map KW.t) (pullback.snd (q ≫ y) y) q := by
    apply IsPullback.of_right (h₂₂ := y) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback (q ≫ y) y)
    rw [show g₁ ≫ pullback.fst (q ≫ y) y = yoneda.map KW.s from
      pullback.lift_fst _ _ _]
    exact KW.kernelPair
  have hg₂ : IsPullback (pullback.fst (q ≫ y) y) g₂ q (pullback.fst y y) := by
    apply IsPullback.of_bot (v₂₂ := y) ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback y y)
    rw [show g₂ ≫ pullback.snd y y = pullback.snd (q ≫ y) y from pullback.lift_snd _ _ _]
    exact IsPullback.of_hasPullback (q ≫ y) y
  have hgg : pullback.lift (yoneda.map KW.s ≫ q) (yoneda.map KW.t ≫ q)
      (by simpa only [Category.assoc] using hKWw) = g₁ ≫ g₂ := by
    apply pullback.hom_ext <;> simp [g₁, g₂]
  have hgE : E.presheaf (g₁ ≫ g₂) :=
    E.presheaf.comp_mem _ _ (E.presheaf.of_isPullback hg₁.flip hqe)
      (E.presheaf.of_isPullback hg₂ hqe)
  have hgP : P.presheaf (g₁ ≫ g₂) :=
    P.presheaf.comp_mem _ _ (P.presheaf.of_isPullback hg₁.flip hqs)
      (P.presheaf.of_isPullback hg₂ hqs)
  have hXX := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS y y hX hX hT
  have hPBd := isPullback_kernelPair_diagonal q y KW.kernelPair hqk (yoneda.map ρ) hρ₁ hρ₂
  let _ : (Q.obj KW.R).IsSeparated := atlasKernelPair_isSeparated B S hS hT WoA (q ≫ y)
  have hKWqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj KW.R) :=
    isQuasiSeparated_yoneda B S hS hZ KW.R inferInstance
  have hsnd : AlgebraicGeometry.Space.IsQuasiCompact B S hS
      (pullback.fst (pullback.lift (yoneda.map KW.s ≫ q)
        (yoneda.map KW.t ≫ q) (by simpa only [Category.assoc] using hKWw))
        (pullback.diagonal y)) :=
    AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace B S hS hZ
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS KW.R) hKWqs
      (isQuasiCompactSpace_of_iso B S hS hPBd.isoPullback hRoqc) _
  have htfae := (AlgebraicGeometry.Space.isQuasiCompact_tfae B S hS hX hXX
    (pullback.diagonal y)).out 5 1
  refine htfae.mp ⟨yoneda.obj KW.R,
      AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS KW.R,
      pullback.lift (yoneda.map KW.s ≫ q) (yoneda.map KW.t ≫ q)
        (by simpa only [Category.assoc] using hKWw), ?_, ?_, hsnd⟩
  · rw [hgg]
    exact (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda B S hS _
        hXX KW.R _).mp hgP
  · intro V φ hφ
    rw [hgg]
    exact E.presheaf.comp_mem _ _ hφ hgE

omit [IsCofiltered I] hSize hHomSize hD hAffine hQc hQs in
/-- A map of algebraic spaces whose composite with a surjective étale atlas of the
source is of finite presentation is locally of finite presentation. -/
private theorem isLocallyOfFinitePresentation_of_atlas
    {T X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : AlgebraicGeometry.IsAlgebraicSpace B S hS T)
    (hTqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS T)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    {Wo : AlgebraicGeometry.BigFppfOver B S hS} (q : yoneda.obj Wo ⟶ X)
    (hqs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (y : X ⟶ T) (hwo : AlgebraicGeometry.Space.IsFinitePresentation B S hS (q ≫ y)) :
    AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS y := by
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : E.presheaf.IsStableUnderBaseChange := E.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : E.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition E (etaleInverseImageIsStableUnderComposition _)
  obtain ⟨V, cV, hVaff, hVs, hVe⟩ := exists_affine_etale_atlas B S hS T hT hTqc
  have hcVe : E.presheaf cV := represented_etale_of_isEtale B S hS cV hVe
  let U := hcVe.1.pullback (q ≫ y)
  let aU : U ⟶ Wo := hcVe.1.snd (q ≫ y)
  have hPB : IsPullback (hcVe.1.fst (q ≫ y)) (yoneda.map aU) cV (q ≫ y) :=
    hcVe.1.isPullback (q ≫ y)
  let h : U ⟶ V := yoneda.preimage (hcVe.1.fst (q ≫ y))
  have hh : yoneda.map h = hcVe.1.fst (q ≫ y) := yoneda.map_preimage _
  have haE : E.presheaf (yoneda.map aU ≫ q) :=
    E.presheaf.comp_mem _ _ (E.presheaf.of_isPullback hPB hcVe) hqe
  have haP : P.presheaf (yoneda.map aU ≫ q) :=
    P.presheaf.comp_mem _ _ (P.presheaf.of_isPullback hPB hVs) hqs
  have hfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map h) := by
    rw [hh]
    exact isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wo)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) hT hPB.flip hwo
  apply (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart B S hS _
    AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
    hX hT y).mpr
  refine ⟨U, V, yoneda.map aU ≫ q, cV, h, haE, hcVe, haP, ?_,
    (finitePresentation_of_yoneda B S hS h hfp).1⟩
  rw [hh, Category.assoc]
  exact hPB.w

omit [IsCofiltered I] hSize hHomSize hD hAffine hQc hQs in
/-- A pair of maps of the site that factors monomorphically through the kernel pair of a
map to an algebraic space is jointly monic over the base. -/
private theorem jointlyMono₂_of_mono_to_kernelPair
    {T : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Wo Ro KR : AlgebraicGeometry.BigFppfOver B S hS}
    (wo : yoneda.obj Wo ⟶ T) (kt ks : KR ⟶ Wo)
    (hk : IsPullback (yoneda.map kt) (yoneda.map ks) wo wo)
    (sR tR : Ro ⟶ Wo) (ρ : Ro ⟶ KR)
    (hρ₁ : ρ ≫ kt = sR) (hρ₂ : ρ ≫ ks = tR)
    (hmono : Mono (yoneda.map ρ)) :
    JointlyMono₂ ((Over.post (X := B.obj hS) B.inclusion).map sR)
      ((Over.post (X := B.obj hS) B.inclusion).map tR) := by
  let F : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  have hFρ : Mono (F.map ρ) := mono_post_of_mono_yoneda B S hS ρ hmono
  let r := (AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback B S hS wo kt ks
    hk).nonempty_equivalenceRelation.some
  refine ⟨fun {Y} f g h₁ h₂ => ?_⟩
  apply (cancel_mono (F.map ρ)).mp
  apply r.right_cancellation
  · rw [Category.assoc, Category.assoc, ← F.map_comp, hρ₁]
    exact h₁
  · rw [Category.assoc, Category.assoc, ← F.map_comp, hρ₂]
    exact h₂

omit [IsCofiltered I] hSize hHomSize hD hAffine hQc hQs in
/-- Reflexivity, symmetry and transitivity witnesses on a jointly monic pair of étale
maps of the site make it an étale equivalence relation. -/
private theorem isEtaleEquivalenceRelation_of_witnesses
    {Wo Ro : AlgebraicGeometry.BigFppfOver B S hS} (sR tR : Ro ⟶ Wo)
    (hsE : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sR))
    (htE : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tR))
    (hjm : JointlyMono₂ ((Over.post (X := B.obj hS) B.inclusion).map sR)
      ((Over.post (X := B.obj hS) B.inclusion).map tR))
    (refl : Wo ⟶ Ro) (hrefl₁ : refl ≫ sR = 𝟙 Wo) (hrefl₂ : refl ≫ tR = 𝟙 Wo)
    (symm : Ro ⟶ Ro) (hsymm₁ : symm ≫ sR = tR) (hsymm₂ : symm ≫ tR = sR)
    (comp : pullback tR sR ⟶ Ro)
    (hcomp₁ : comp ≫ sR = pullback.fst tR sR ≫ sR)
    (hcomp₂ : comp ≫ tR = pullback.snd tR sR ≫ tR) :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
        (AlgebraicGeometry.Space.relation B S hS tR sR) := by
  let F : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  have htarget : (AlgebraicGeometry.Space.relation B S hS tR sR).target = F.map sR :=
    relationTarget_prodLift _ _
  have hsource : (AlgebraicGeometry.Space.relation B S hS tR sR).source = F.map tR :=
    relationSource_prodLift _ _
  have hFP : IsPullback (F.map (pullback.fst tR sR)) (F.map (pullback.snd tR sR))
      (F.map tR) (F.map sR) := by
    apply IsPullback.of_map (Over.forget S) (by
      rw [← F.map_comp, ← F.map_comp, pullback.condition])
    exact (IsPullback.of_hasPullback tR sR).map
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
  · rw [htarget, hsource]
    refine EquivalenceRelation.isEquivalenceRelation
      { right_cancellation := hjm.right_cancellation
        r := F.map refl
        reflexivity₁ := by rw [← F.map_comp, hrefl₁, F.map_id]
        reflexivity₂ := by rw [← F.map_comp, hrefl₂, F.map_id]
        s := F.map symm
        symmetry₁ := by rw [← F.map_comp, hsymm₁]
        symmetry₂ := by rw [← F.map_comp, hsymm₂]
        c := PullbackCone.mk (F.map (pullback.fst tR sR)) (F.map (pullback.snd tR sR))
          (by rw [← F.map_comp, ← F.map_comp, pullback.condition])
        isLimit := hFP.isLimit
        t := F.map comp
        transitivity₁ := by
          show F.map comp ≫ F.map sR = F.map (pullback.fst tR sR) ≫ F.map sR
          rw [← F.map_comp, ← F.map_comp, hcomp₁]
        transitivity₂ := by
          show F.map comp ≫ F.map tR = F.map (pullback.snd tR sR) ≫ F.map tR
          rw [← F.map_comp, ← F.map_comp, hcomp₂] }
  · rwa [hsource]
  · rwa [htarget]

omit [IsCofiltered I] hSize hHomSize hD hAffine hQc hQs in
/-- The quotient of an étale equivalence relation on an object of the site, together with
its surjective étale atlas, its kernel pair, and the map to any target the relation
equalizes. -/
private theorem exists_quotient_of_etaleEquivalenceRelation
    {T : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : AlgebraicGeometry.IsAlgebraicSpace B S hS T)
    {Wo Ro : AlgebraicGeometry.BigFppfOver B S hS} (sR tR : Ro ⟶ Wo)
    (wo : yoneda.obj Wo ⟶ T)
    (hwo : yoneda.map sR ≫ wo = yoneda.map tR ≫ wo)
    (hrel : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (AlgebraicGeometry.Space.relation B S hS tR sR)) :
    ∃ (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_ : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
      (q : yoneda.obj Wo ⟶ X) (y : X ⟶ T),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q ∧
      IsPullback (yoneda.map sR) (yoneda.map tR) q q ∧ q ≫ y = wo := by
  let _ : HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u) :=
    bigFppfOverHasSheafify B S hS
  let _ : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (AlgebraicGeometry.Space.relation B S hS tR sR) := hrel
  have hX := AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional B S hS tR sR
  let q := AlgebraicGeometry.Space.quotientMap B S hS tR sR
  have hrep := AlgebraicGeometry.Space.relativelyRepresentable_quotientMap_of_isAlgebraicSpace
    B S hS tR sR hX
  have hqs := AlgebraicGeometry.Space.quotientMap_surjective B S hS tR sR hrep
  have hqe := AlgebraicGeometry.Space.quotientMap_etale B S hS tR sR hrep
  have hqk : IsPullback (yoneda.map sR) (yoneda.map tR) q q :=
    AlgebraicGeometry.Space.quotientMap_isPullback B S hS tR sR
  obtain ⟨y, hy⟩ := exists_hom_of_equalizes_atlas B S hS hX hT.isSheaf q hqs hqe wo (by
    apply (cancel_epi hqk.isoPullback.hom).mp
    rw [reassoc_of% hqk.isoPullback_hom_fst, reassoc_of% hqk.isoPullback_hom_snd]
    exact hwo)
  exact ⟨_, hX, q, y, hqs, hqe, hqk, hy⟩

omit [IsCofiltered I] hSize hHomSize hD hAffine hQc hQs in
include hZ in
/-- An étale equivalence relation on an affine object of the site, given by witnesses for
reflexivity, symmetry and transitivity on a jointly monic pair, has a quotient which is an
algebraic space of finite presentation over any quasi-compact quasi-separated target the
relation equalizes, provided the relation itself is quasi-compact. -/
private theorem exists_finitePresentation_quotient
    {T : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : AlgebraicGeometry.IsAlgebraicSpace B S hS T)
    (hTqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS T)
    (hTqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ T)
    {Wo Ro : AlgebraicGeometry.BigFppfOver B S hS}
    (hWoAff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Wo))
    (sR tR : Ro ⟶ Wo)
    (hsE : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sR))
    (htE : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tR))
    (hjm : JointlyMono₂ ((Over.post (X := B.obj hS) B.inclusion).map sR)
      ((Over.post (X := B.obj hS) B.inclusion).map tR))
    (refl : Wo ⟶ Ro) (hrefl₁ : refl ≫ sR = 𝟙 Wo) (hrefl₂ : refl ≫ tR = 𝟙 Wo)
    (symm : Ro ⟶ Ro) (hsymm₁ : symm ≫ sR = tR) (hsymm₂ : symm ≫ tR = sR)
    (comp : pullback tR sR ⟶ Ro)
    (hcomp₁ : comp ≫ sR = pullback.fst tR sR ≫ sR)
    (hcomp₂ : comp ≫ tR = pullback.snd tR sR ≫ tR)
    (wo : yoneda.obj Wo ⟶ T)
    (hwo : yoneda.map sR ≫ wo = yoneda.map tR ≫ wo)
    (hwoFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wo)
    (hRoqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (yoneda.obj Ro)) :
    ∃ (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_ : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
      (q : yoneda.obj Wo ⟶ X) (y : X ⟶ T),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q ∧
      IsPullback (yoneda.map sR) (yoneda.map tR) q q ∧ q ≫ y = wo ∧
      AlgebraicGeometry.Space.IsFinitePresentation B S hS y := by
  obtain ⟨X, hX, q, y, hqs, hqe, hqk, hqy⟩ :=
    exists_quotient_of_etaleEquivalenceRelation B S hS hT sR tR wo hwo
      (isEtaleEquivalenceRelation_of_witnesses B S hS sR tR hsE htE hjm
        refl hrefl₁ hrefl₂ symm hsymm₁ hsymm₂ comp hcomp₁ hcomp₂)
  refine ⟨X, hX, q, y, hqs, hqe, hqk, hqy, ?_, ?_, ?_⟩
  · exact isLocallyOfFinitePresentation_of_atlas B S hS hT hTqc hX q hqs hqe y
      (by rw [hqy]; exact hwoFp)
  · exact AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace
      B S hS hZ hT hTqs (isQuasiCompact_of_affine_atlas B S hS hWoAff q hqs hqe) y
  · exact isQuasiSeparated_of_affine_atlas B S hS hZ hT hX hWoAff q hqs hqe y sR tR
      hqk hRoqc

omit [IsCofiltered I] hSize hHomSize hD hAffine hQc hQs in
include hZ in
/-- An étale equivalence relation on an affine object of the site, given by witnesses for
reflexivity, symmetry and transitivity on a jointly monic pair, has a quotient which is an
algebraic space of finite presentation over any quasi-compact quasi-separated target the
relation equalizes, provided the relation itself is quasi-compact. -/
theorem exists_isFinitePresentation_quotient_of_witnesses
    {T : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : AlgebraicGeometry.IsAlgebraicSpace B S hS T)
    (hTqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS T)
    (hTqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ T)
    {Wo Ro : AlgebraicGeometry.BigFppfOver B S hS}
    (hWoAff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Wo))
    (sR tR : Ro ⟶ Wo)
    (hsE : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sR))
    (htE : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tR))
    (hjm : JointlyMono₂ ((Over.post (X := B.obj hS) B.inclusion).map sR)
      ((Over.post (X := B.obj hS) B.inclusion).map tR))
    (refl : Wo ⟶ Ro) (hrefl₁ : refl ≫ sR = 𝟙 Wo) (hrefl₂ : refl ≫ tR = 𝟙 Wo)
    (symm : Ro ⟶ Ro) (hsymm₁ : symm ≫ sR = tR) (hsymm₂ : symm ≫ tR = sR)
    (comp : pullback tR sR ⟶ Ro)
    (hcomp₁ : comp ≫ sR = pullback.fst tR sR ≫ sR)
    (hcomp₂ : comp ≫ tR = pullback.snd tR sR ≫ tR)
    (wo : yoneda.obj Wo ⟶ T)
    (hwo : yoneda.map sR ≫ wo = yoneda.map tR ≫ wo)
    (hwoFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wo)
    (hRoqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (yoneda.obj Ro)) :
    ∃ (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_ : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
      (q : yoneda.obj Wo ⟶ X) (y : X ⟶ T),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q ∧
      IsPullback (yoneda.map sR) (yoneda.map tR) q q ∧ q ≫ y = wo ∧
      AlgebraicGeometry.Space.IsFinitePresentation B S hS y :=
  exists_finitePresentation_quotient B S hS hZ hT hTqc hTqs hWoAff sR tR hsE htE hjm refl hrefl₁
    hrefl₂ symm hsymm₁ hsymm₂ comp hcomp₁ hcomp₂ wo hwo hwoFp hRoqc

omit [IsCofiltered I] hSize hHomSize hD hAffine hQc hQs in
include hZ in
/-- A descended étale presentation of an algebraic space over the apex `L` of a morphism
`π : L ⟶ D.obj o` produces a finite-presentation model at the stage `o`. This is
`AlgebraicGeometry.Space.exists_model_of_descended_presentation` with the limit projection
replaced by an arbitrary morphism to the stage. -/
theorem exists_model_of_descended_presentation_of_hom (o : I)
    {L : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : L ⟶ D.obj o)
    (hLim : AlgebraicGeometry.IsAlgebraicSpace B S hS L)
    (hT : AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj o))
    (hTqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (D.obj o))
    (hTqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (D.obj o))
    (Y : Over L) (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    {W KR : AlgebraicGeometry.BigFppfOver B S hS} (w : yoneda.obj W ⟶ Y.left)
    (hws : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (hwe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (kt ks : KR ⟶ W) (hwk : IsPullback (yoneda.map kt) (yoneda.map ks) w w)
    {Wo Ro : AlgebraicGeometry.BigFppfOver B S hS}
    (hWoAff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Wo))
    (sR tR : Ro ⟶ Wo)
    (hsE : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sR))
    (htE : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tR))
    (hjm : JointlyMono₂ ((Over.post (X := B.obj hS) B.inclusion).map sR)
      ((Over.post (X := B.obj hS) B.inclusion).map tR))
    (refl : Wo ⟶ Ro) (hrefl₁ : refl ≫ sR = 𝟙 Wo) (hrefl₂ : refl ≫ tR = 𝟙 Wo)
    (symm : Ro ⟶ Ro) (hsymm₁ : symm ≫ sR = tR) (hsymm₂ : symm ≫ tR = sR)
    (comp : pullback tR sR ⟶ Ro)
    (hcomp₁ : comp ≫ sR = pullback.fst tR sR ≫ sR)
    (hcomp₂ : comp ≫ tR = pullback.snd tR sR ≫ tR)
    (wo : yoneda.obj Wo ⟶ D.obj o)
    (hwow : yoneda.map sR ≫ wo = yoneda.map tR ≫ wo)
    (hwoFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wo)
    (hRoqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (yoneda.obj Ro))
    (aw : W ⟶ Wo) (ar : KR ⟶ Ro)
    (hawlim : IsPullback (yoneda.map aw) (w ≫ Y.hom) wo π)
    (hsqs : IsPullback ar kt sR aw) (hsqt : IsPullback ar ks tR aw) :
    ∃ Yᵢ : Over (D.obj o),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
          Nonempty (Y ≅ (Over.pullback π).obj Yᵢ) := by
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : E.presheaf.IsStableUnderBaseChange := E.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : E.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition E (etaleInverseImageIsStableUnderComposition _)
  obtain ⟨X, hX, q, y, hqs, hqe, hqk, hqy, hyfp⟩ :=
    exists_finitePresentation_quotient B S hS hZ hT hTqc hTqs hWoAff sR tR hsE htE hjm
      refl hrefl₁ hrefl₂ symm hsymm₁ hsymm₂ comp hcomp₁ hcomp₂ wo hwow hwoFp hRoqc
  have hcq : yoneda.map aw ≫ q ≫ y = (w ≫ Y.hom) ≫ π := by
    rw [hqy]
    exact hawlim.w
  let c : yoneda.obj W ⟶ pullback y π :=
    pullback.lift (yoneda.map aw ≫ q) (w ≫ Y.hom) hcq
  have hcfst : c ≫ pullback.fst y π = yoneda.map aw ≫ q :=
    pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd y π = w ≫ Y.hom :=
    pullback.lift_snd _ _ _
  have hc : IsPullback (yoneda.map aw) c q (pullback.fst y π) := by
    apply IsPullback.of_bot (v₂₂ := y) ?_ hcfst.symm
      (IsPullback.of_hasPullback y π)
    rw [hcsnd, hqy]
    exact hawlim
  have hcs : P.presheaf c := P.presheaf.of_isPullback hc hqs
  have hce : E.presheaf c := E.presheaf.of_isPullback hc hqe
  have hck : IsPullback (yoneda.map kt) (yoneda.map ks) c c := by
    apply IsPullback.of_right (h₂₂ := pullback.fst y π) ?_ ?_ hc
    · rw [hcfst]
      have hpaste := (hsqt.map yoneda).paste_horiz hqk
      rwa [← yoneda.map_comp, hsqs.w, yoneda.map_comp] at hpaste
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hcfst, ← Category.assoc, ← Category.assoc,
          ← yoneda.map_comp, ← yoneda.map_comp, ← hsqs.w, ← hsqt.w, yoneda.map_comp,
          yoneda.map_comp, Category.assoc, Category.assoc, hqk.w]
      · rw [Category.assoc, Category.assoc, hcsnd, ← Category.assoc, ← Category.assoc,
          hwk.w]
  obtain ⟨e, he⟩ := exists_iso_of_common_atlas B S hS hY
    (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS y π hX hLim hT)
    kt ks w c hws hwe hcs hce hwk hck
  refine ⟨Over.mk y, hX, hyfp, ⟨Over.isoMk e ?_⟩⟩
  apply hom_ext_of_surjective_etale_atlas B S hS hY hLim.isSheaf w hws hwe
  rw [reassoc_of% he]
  exact hcsnd

omit [IsCofiltered I] hSize hHomSize hD hAffine hQc hQs in
include hZ in
/-- A descended étale presentation of an algebraic space over the limit produces a
finite-presentation model at the stage it is defined over. -/
private theorem exists_model_of_descended_presentation (o : I)
    (hLim : AlgebraicGeometry.IsAlgebraicSpace B S hS (limit D))
    (hT : AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj o))
    (hTqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (D.obj o))
    (hTqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (D.obj o))
    (Y : Over (limit D)) (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    {W KR : AlgebraicGeometry.BigFppfOver B S hS} (w : yoneda.obj W ⟶ Y.left)
    (hws : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (hwe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (kt ks : KR ⟶ W) (hwk : IsPullback (yoneda.map kt) (yoneda.map ks) w w)
    {Wo Ro : AlgebraicGeometry.BigFppfOver B S hS}
    (hWoAff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Wo))
    (sR tR : Ro ⟶ Wo)
    (hsE : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sR))
    (htE : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tR))
    (hjm : JointlyMono₂ ((Over.post (X := B.obj hS) B.inclusion).map sR)
      ((Over.post (X := B.obj hS) B.inclusion).map tR))
    (refl : Wo ⟶ Ro) (hrefl₁ : refl ≫ sR = 𝟙 Wo) (hrefl₂ : refl ≫ tR = 𝟙 Wo)
    (symm : Ro ⟶ Ro) (hsymm₁ : symm ≫ sR = tR) (hsymm₂ : symm ≫ tR = sR)
    (comp : pullback tR sR ⟶ Ro)
    (hcomp₁ : comp ≫ sR = pullback.fst tR sR ≫ sR)
    (hcomp₂ : comp ≫ tR = pullback.snd tR sR ≫ tR)
    (wo : yoneda.obj Wo ⟶ D.obj o)
    (hwow : yoneda.map sR ≫ wo = yoneda.map tR ≫ wo)
    (hwoFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wo)
    (hRoqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (yoneda.obj Ro))
    (aw : W ⟶ Wo) (ar : KR ⟶ Ro)
    (hawlim : IsPullback (yoneda.map aw) (w ≫ Y.hom) wo (limit.π D o))
    (hsqs : IsPullback ar kt sR aw) (hsqt : IsPullback ar ks tR aw) :
    ∃ Yᵢ : Over (D.obj o),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D o)).obj Yᵢ) :=
  exists_model_of_descended_presentation_of_hom B S hS hZ D o (limit.π D o) hLim hT hTqc hTqs Y
    hY w hws hwe kt ks hwk hWoAff sR tR hsE htE hjm refl hrefl₁ hrefl₂ symm hsymm₁ hsymm₂ comp
    hcomp₁ hcomp₂ wo hwow hwoFp hRoqc aw ar hawlim hsqs hsqt

private theorem exists_stage_atlas_factorization (i : I)
    (Y : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hYqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS Y.left)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f : pullback Y.hom (limit.π D i) ⟶ Z)
    (hf : f ≫ a = pullback.fst Y.hom (limit.π D i) ≫ Y.hom) :
    ∃ (j : Over i) (U : AlgebraicGeometry.BigAffineFppf B S hS)
      (p : yoneda.obj U.obj ⟶ pullback Y.hom (D.map j.hom))
      (g : yoneda.obj U.obj ⟶ Z),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      g ≫ a = p ≫ pullback.snd Y.hom (D.map j.hom) ≫ D.map j.hom ∧
      pullback.fst (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ≫ g =
        pullback.lift
          (pullback.fst (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ≫ p)
          (pullback.snd (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left))
          (by simpa only [Over.pullback_obj_hom, Category.assoc] using
            (pullback.condition (f := p ≫ pullback.snd Y.hom (D.map j.hom))
              (g := limit.π D j.left))) ≫
        (iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
          (limit.w D j.hom) Y).hom.left ≫ f := by
  classical
  obtain ⟨U₀, q₀, hU₀, hs, he⟩ := exists_affine_etale_atlas B S hS Y.left hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  let k : pullback (limit.π D i) (q₀ ≫ Y.hom) ⟶ pullback Y.hom (limit.π D i) :=
    pullback.lift (pullback.snd _ _ ≫ q₀) (pullback.fst _ _)
      (by simp only [Category.assoc, pullback.condition])
  obtain ⟨j, g, hg, hgf⟩ := exists_hom_on_affine_chart B S hS hZ D hSize hHomSize
    hD hAffine hQc hQs i U (q₀ ≫ Y.hom) hZalg a ha (k ≫ f) (by
      rw [Category.assoc, hf]
      simpa [k, Category.assoc] using (pullback.condition (f := limit.π D i)
        (g := q₀ ≫ Y.hom)).symm)
  let C := affineStageChart B S hS D i U (q₀ ≫ Y.hom) hAffine j
  let p : yoneda.obj C.U.obj ⟶ pullback Y.hom (D.map j.hom) :=
    pullback.lift (yoneda.map C.toChart ≫ q₀) C.toStage
      (by simpa only [Category.assoc] using C.isPullback.w.symm)
  have hp : IsPullback (yoneda.map C.toChart) p q₀
      (pullback.fst Y.hom (D.map j.hom)) := by
    apply IsPullback.of_bot _ (by simp [p]) (IsPullback.of_hasPullback Y.hom (D.map j.hom))
    simpa [p] using C.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  refine ⟨j, C.U, p, g, P.presheaf.of_isPullback hp hs,
    Q.presheaf.of_isPullback hp (represented_etale_of_isEtale B S hS q₀ he),
    by simpa [p] using hg, ?_⟩
  let v : pullback (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ⟶
      pullback (limit.π D i) (q₀ ≫ Y.hom) :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ yoneda.map C.toChart) (by
      simp only [Category.assoc]
      rw [← C.isPullback.w, ← limit.w D j.hom]
      simp only [← Category.assoc]
      congr 1
      have hpcomp : p ≫ pullback.snd Y.hom (D.map j.hom) = C.toStage := by simp [p]
      rw [← hpcomp]
      exact pullback.condition.symm)
  let l := C.isPullback.lift
    (pullback.fst (limit.π D i) (q₀ ≫ Y.hom) ≫ limit.π D j.left)
    (pullback.snd (limit.π D i) (q₀ ≫ Y.hom))
    (by rw [Category.assoc, limit.w]; exact pullback.condition)
  have hv : v ≫ l = pullback.fst _ _ := by
    apply C.isPullback.hom_ext
    · simp only [Category.assoc, l, IsPullback.lift_fst, v, pullback.lift_fst_assoc]
      simpa [p, Category.assoc] using
        (pullback.condition (f := p ≫ pullback.snd Y.hom (D.map j.hom))
          (g := limit.π D j.left)).symm
    · simp [l, v]
  conv_lhs => rw [← hv, Category.assoc, hgf]
  simp only [← Category.assoc]
  apply congrArg (fun t => t ≫ f)
  apply pullback.hom_ext
  · simp [v, k, iteratedBaseChangeIso_hom_left, p, Category.assoc]
  · simp [v, k, iteratedBaseChangeIso_hom_left, Category.assoc]

/-- A morphism between base changes of finite-presentation algebraic spaces
is defined at a sufficiently late stage. -/
@[stacks 07SK "fullness"]
public theorem exists_morphism_after_baseChange
    (i : I) (Yᵢ Zᵢ : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f : (Over.pullback (limit.π D i)).obj Yᵢ ⟶
      (Over.pullback (limit.π D i)).obj Zᵢ) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (D.map e)).obj Yᵢ ⟶
        (Over.pullback (D.map e)).obj Zᵢ)
      (α : (Over.pullback (limit.π D j)).obj
          ((Over.pullback (D.map e)).obj Yᵢ) ≅
        (Over.pullback (limit.π D i)).obj Yᵢ)
      (β : (Over.pullback (limit.π D j)).obj
          ((Over.pullback (D.map e)).obj Zᵢ) ≅
        (Over.pullback (limit.π D i)).obj Zᵢ),
      (α.hom.left ≫ pullback.fst Yᵢ.hom (limit.π D i) =
        pullback.fst ((Over.pullback (D.map e)).obj Yᵢ).hom (limit.π D j) ≫
          pullback.fst Yᵢ.hom (D.map e)) ∧
      (β.hom.left ≫ pullback.fst Zᵢ.hom (limit.π D i) =
        pullback.fst ((Over.pullback (D.map e)).obj Zᵢ).hom (limit.π D j) ≫
          pullback.fst Zᵢ.hom (D.map e)) ∧
      α.hom ≫ f = (Over.pullback (limit.π D j)).map g ≫ β.hom := by
  classical
  have hYqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS Yᵢ.hom
    (hD i) (hQc i) hYfp
  have hYqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS hZ hY (hQs i) hYfp.2.2
  let f₀ := f.left ≫ pullback.fst Zᵢ.hom (limit.π D i)
  have hf₀ : f₀ ≫ Zᵢ.hom = pullback.fst Yᵢ.hom (limit.π D i) ≫ Yᵢ.hom := by
    simp only [f₀, Category.assoc, pullback.condition]
    have hw : f.left ≫ pullback.snd Zᵢ.hom (limit.π D i) =
        pullback.snd Yᵢ.hom (limit.π D i) := f.w
    rw [← Category.assoc, hw]
  obtain ⟨j, U, p, g, hs, he, hg, hgf⟩ := exists_stage_atlas_factorization
    B S hS hZ D hSize hHomSize hD hAffine hQc hQs i Yᵢ hY hYqc hZ' Zᵢ.hom hZfp.1 f₀ hf₀
  let Yj := (Over.pullback (D.map j.hom)).obj Yᵢ
  have hYj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom (D.map j.hom)
    hY (hD j.left) (hD i)
  have hYjqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_pullback
    B S hS hZ Yᵢ.hom (D.map j.hom) hY (hD j.left) (hD i) hYqs (hQs j.left)
  have hU := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U.obj
  have hUqc := isQuasiCompactSpace_yoneda_of_isAffine B S hS U.obj U.property
  have hR := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS p p hU hU hYj
  have hRqc := AlgebraicGeometry.Space.isQuasiCompactSpace_pullback
    B S hS hZ p p hU hYj hUqc hUqc hYjqs
  have hlim := equalizes_kernelPair_after_baseChange p Yj.hom (limit.π D j.left)
    ((iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
      (limit.w D j.hom) Yᵢ).hom.left ≫ f₀) g hgf
  obtain ⟨k, e, hkg⟩ := eventually_eq_on_quasiCompact_source B S hS hZ D hSize hHomSize
    hD hAffine hQc hQs j.left hR hZ' (hD i) hRqc
    (pullback.fst p p ≫ p ≫ Yj.hom) Zᵢ.hom (D.map j.hom) hZfp.1
    (pullback.fst p p ≫ g) (pullback.snd p p ≫ g)
    (by simpa only [Yj, Over.pullback_obj_hom, Category.assoc] using congrArg
          (fun t => pullback.fst p p ≫ t) hg)
    (by simpa only [Yj, Over.pullback_obj_hom, Category.assoc, pullback.condition_assoc] using
      congrArg (fun t => pullback.snd p p ≫ t) hg) hlim
  let K := affineStageChart B S hS D j.left U (p ≫ Yj.hom) hAffine (Over.mk e)
  let Yk := (Over.pullback (D.map e)).obj Yj
  let pK : yoneda.obj K.U.obj ⟶ Yk.left :=
    pullback.lift (yoneda.map K.toChart ≫ p) K.toStage
      (by simpa only [Category.assoc, Over.mk_hom] using K.isPullback.w.symm)
  have hpK : IsPullback (yoneda.map K.toChart) pK p (pullback.fst Yj.hom (D.map e)) := by
    apply IsPullback.of_bot _ (by simp [pK]) (IsPullback.of_hasPullback Yj.hom (D.map e))
    simpa [pK] using K.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  have hYk := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yj.hom (D.map e)
    hYj (hD k) (hD j.left)
  have hKs := P.presheaf.of_isPullback hpK hs
  have hKe := Q.presheaf.of_isPullback hpK he
  obtain ⟨gK, hgK⟩ := exists_hom_of_equalizes_atlas B S hS hYk hZ'.isSheaf pK hKs hKe
    (yoneda.map K.toChart ≫ g)
    (equalizes_kernelPair_of_baseChange_eq p Yj.hom (D.map e)
      (pullback.fst Yj.hom (D.map e)) (pullback.snd Yj.hom (D.map e)) pullback.condition
      (yoneda.map K.toChart) pK (by simp [pK]) g hkg)
  have hgKa : gK ≫ Zᵢ.hom = Yk.hom ≫ D.map e ≫ D.map j.hom := by
    apply hom_ext_of_surjective_etale_atlas B S hS hYk (hD i).isSheaf pK hKs hKe
    rw [← Category.assoc, hgK, Category.assoc, hg]
    have hw := congrArg (fun t => t ≫ D.map j.hom) K.isPullback.w
    simpa only [Yj, Yk, pK, Over.pullback_obj_hom, pullback.lift_snd_assoc,
      Over.mk_hom, Category.assoc] using hw.symm
  let d := e ≫ j.hom
  let η := iteratedBaseChangeIso (D.map j.hom) (D.map e) (D.map d)
    (D.map_comp e j.hom).symm Yᵢ
  let raw : pullback Yᵢ.hom (D.map d) ⟶ Zᵢ.left := η.inv.left ≫ gK
  have hrawa : raw ≫ Zᵢ.hom = pullback.snd Yᵢ.hom (D.map d) ≫ D.map d := by
    dsimp only [raw]
    rw [Category.assoc, hgKa]
    simpa only [d, Yk, Yj, Over.pullback_obj_hom, Functor.map_comp, Category.assoc] using
      congrArg (fun t => t ≫ D.map d) (Over.w η.inv)
  let g' : (Over.pullback (D.map d)).obj Yᵢ ⟶ (Over.pullback (D.map d)).obj Zᵢ :=
    Over.homMk (pullback.lift raw (pullback.snd Yᵢ.hom (D.map d)) hrawa) (by simp)
  let α := iteratedBaseChangeIso (D.map d) (limit.π D k) (limit.π D i) (limit.w D d) Yᵢ
  let β := iteratedBaseChangeIso (D.map d) (limit.π D k) (limit.π D i) (limit.w D d) Zᵢ
  let m : pullback Yᵢ.hom (limit.π D i) ⟶ pullback Yᵢ.hom (D.map d) :=
    pullback.lift (pullback.fst Yᵢ.hom (limit.π D i))
      (pullback.snd Yᵢ.hom (limit.π D i) ≫ limit.π D k)
      (by rw [Category.assoc, limit.w]; exact pullback.condition)
  have hraw : m ≫ raw = f₀ := by
    let A := iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
      (limit.w D j.hom) Yᵢ
    let q : pullback (p ≫ Yj.hom) (limit.π D j.left) ⟶ pullback Yj.hom (limit.π D j.left) :=
      pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _)
        (by simp only [Category.assoc, pullback.condition])
    have hq : IsPullback (pullback.fst (p ≫ Yj.hom) (limit.π D j.left)) q p
        (pullback.fst Yj.hom (limit.π D j.left)) := by
      apply IsPullback.of_bot _ (by simp [q]) (IsPullback.of_hasPullback Yj.hom (limit.π D j.left))
      simpa [q] using IsPullback.of_hasPullback (p ≫ Yj.hom) (limit.π D j.left)
    let l : pullback (p ≫ Yj.hom) (limit.π D j.left) ⟶ yoneda.obj K.U.obj :=
      K.isPullback.lift (pullback.snd _ _ ≫ limit.π D k) (pullback.fst _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition.symm)
    have hl : q ≫ A.hom.left ≫ m ≫ η.inv.left = l ≫ pK := by
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp [Yj, Yk, q, A, m, η, l, pK, iteratedBaseChangeIso_hom_left,
            iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc]
        · simp [Yj, Yk, q, A, m, η, l, pK, iteratedBaseChangeIso_hom_left,
            iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc, limit.w,
            pullback.condition]
      · simp [Yj, Yk, q, A, m, η, l, pK, iteratedBaseChangeIso_hom_left,
          iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc]
    have hEq : q ≫ A.hom.left ≫ (m ≫ raw) = q ≫ A.hom.left ≫ f₀ := by
      show q ≫ A.hom.left ≫ m ≫ η.inv.left ≫ gK = _
      have hh := congrArg (fun t => t ≫ gK) hl
      simp only [Category.assoc, hgK] at hh
      rw [hh]
      simpa [l, Category.assoc, q, A, Yj] using hgf
    obtain ⟨V, v, w, hV⟩ := AlgebraicGeometry.Space.isAffineHom_limitπ B S hS D hSize hHomSize
      hAffine j.left U (p ≫ Yj.hom)
    let vq := hV.flip.isoPullback.hom ≫ q
    have hEq' : A.hom.left ≫ (m ≫ raw) = A.hom.left ≫ f₀ := by
      apply hom_ext_of_surjective_etale_atlas B S hS
        (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yj.hom (limit.π D j.left)
          hYj (AlgebraicGeometry.Space.isAlgebraicSpace_limit B S hS D hSize hHomSize hD
              hAffine) (hD j.left))
        hZ'.isSheaf vq
        (MorphismProperty.RespectsIso.precomp _ hV.flip.isoPullback.hom q
          (P.presheaf.of_isPullback hq hs))
        (MorphismProperty.RespectsIso.precomp _ hV.flip.isoPullback.hom q
          (Q.presheaf.of_isPullback hq he))
      simpa only [vq, Category.assoc] using
        congrArg (fun t => hV.flip.isoPullback.hom ≫ t) hEq
    let : IsIso A.hom.left :=
      inferInstanceAs (IsIso ((Over.forget (limit D)).map A.hom))
    exact (cancel_epi A.hom.left).mp hEq'
  refine ⟨k, d, g', α, β, iteratedBaseChangeIso_hom_fst _ _ _ _ _,
    iteratedBaseChangeIso_hom_fst _ _ _ _ _, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hm : α.hom.left ≫ m = pullback.fst ((Over.pullback (D.map d)).obj Yᵢ).hom
      (limit.π D k) := by
      apply pullback.hom_ext <;>
        simp [α, m, iteratedBaseChangeIso_hom_left, Category.assoc, pullback.condition]
    have hh := congrArg (fun t => α.hom.left ≫ t) hraw
    rw [← Category.assoc α.hom.left m raw, hm] at hh
    simpa [g', f₀, Category.assoc, β, iteratedBaseChangeIso_hom_left,
      iteratedBaseChangeIso_inv_left, Over.pullback_map_left] using hh.symm
  · simpa only [Over.comp_left, Over.pullback_obj_hom] using
      (Over.w (α.hom ≫ f)).trans
        (Over.w ((Over.pullback (limit.π D k)).map g' ≫ β.hom)).symm


/-- Two finite-stage morphisms that agree over the limit agree at a sufficiently
late stage. -/
@[stacks 07SK "faithfulness"]
public theorem eventually_eq_of_baseChange_eq
    (i : I) (Yᵢ Zᵢ : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f g : Yᵢ ⟶ Zᵢ)
    (hfg : (Over.pullback (limit.π D i)).map f =
      (Over.pullback (limit.π D i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (D.map e)).map f =
        (Over.pullback (D.map e)).map g := by
  classical
  have hYqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS Yᵢ.hom
    (hD i) (hQc i) hYfp
  obtain ⟨U₀, q₀, hU₀, hsurj, het⟩ := exists_affine_etale_atlas B S hS Yᵢ.left hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hf : (q₀ ≫ f.left) ≫ Zᵢ.hom = q₀ ≫ Yᵢ.hom := by simp
  have hg : (q₀ ≫ g.left) ≫ Zᵢ.hom = q₀ ≫ Yᵢ.hom := by simp
  obtain ⟨j, hj⟩ := eventually_eq_on_affine_chart B S hS hZ D hSize hHomSize
    hD hAffine hQc hQs i U (q₀ ≫ Yᵢ.hom) hZ' Zᵢ.hom hZfp.1
    (q₀ ≫ f.left) (q₀ ≫ g.left) hf hg
    (precomp_eq_of_baseChange_eq (limit.π D i) Yᵢ Zᵢ f g hfg q₀)
  refine ⟨j.left, j.hom, ?_⟩
  let C := affineStageChart B S hS D i U (q₀ ≫ Yᵢ.hom) hAffine j
  let p : yoneda.obj C.U.obj ⟶ pullback Yᵢ.hom (D.map j.hom) :=
    pullback.lift (yoneda.map C.toChart ≫ q₀) C.toStage
      (by simpa only [Category.assoc] using C.isPullback.w.symm)
  have hp : IsPullback (yoneda.map C.toChart) p q₀
      (pullback.fst Yᵢ.hom (D.map j.hom)) := by
    apply IsPullback.of_bot _ (by simp [p]) (IsPullback.of_hasPullback Yᵢ.hom (D.map j.hom))
    simpa [p] using C.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  have hpalgebraic := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom (D.map j.hom)
    hY (hD j.left) (hD i)
  have heq : pullback.fst Yᵢ.hom (D.map j.hom) ≫ f.left =
      pullback.fst Yᵢ.hom (D.map j.hom) ≫ g.left := by
    apply hom_ext_of_surjective_etale_atlas B S hS hpalgebraic hZ'.isSheaf p
      (P.presheaf.of_isPullback hp hsurj)
      (Q.presheaf.of_isPullback hp (represented_etale_of_isEtale B S hS q₀ het))
    simpa [p, Category.assoc] using hj
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa [Over.pullback_map_left] using heq
  · simp [Over.pullback_map_left]


private theorem exists_isIso_after_baseChange
    (i : I) (Y Z : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Z.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Z.hom)
    (f : Y ⟶ Z) [IsIso ((Over.pullback (limit.π D i)).map f)] :
    ∃ (j : I) (e : j ⟶ i), IsIso ((Over.pullback (D.map e)).map f) := by
  classical
  let f₀ := (Over.pullback (limit.π D i)).map f
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ := exists_morphism_after_baseChange
    B S hS hZ D hSize hHomSize hD hAffine hQc hQs i Z Y hZ' hY hZfp hYfp (inv f₀)
  have hα' := iteratedBaseChangeIso_unique (D.map e) (limit.π D j) (limit.π D i)
    (limit.w D e) Z α hα
  have hβ' := iteratedBaseChangeIso_unique (D.map e) (limit.π D j) (limit.π D i)
    (limit.w D e) Y β hβ
  have hn : (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map f) ≫
      α.hom = β.hom ≫ f₀ := by
    rw [hα', hβ']
    exact iteratedBaseChangeIso_naturality _ _ _ (limit.w D e) f
  let Yj := (Over.pullback (D.map e)).obj Y
  let Zj := (Over.pullback (D.map e)).obj Z
  let fj := (Over.pullback (D.map e)).map f
  have hYj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Y.hom (D.map e) hY (hD j) (hD i)
  have hZj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Z.hom (D.map e) hZ' (hD j) (hD i)
  have hYjfp := isFinitePresentation_of_isPullback B S hS hYj hY (hD j) (hD i)
    (IsPullback.of_hasPullback Y.hom (D.map e)) hYfp
  have hZjfp := isFinitePresentation_of_isPullback B S hS hZj hZ' (hD j) (hD i)
    (IsPullback.of_hasPullback Z.hom (D.map e)) hZfp
  have hfg : (Over.pullback (limit.π D j)).map (fj ≫ g) =
      (Over.pullback (limit.π D j)).map (𝟙 Yj) := by
    apply (Iso.cancel_iso_hom_right _ _ β).mp
    simp only [Yj, Functor.map_comp]
    rw [Category.assoc, ← hg, ← Category.assoc, hn, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
    rw [(Over.pullback (limit.π D j)).map_id Yj, Category.id_comp]
  have hgf : (Over.pullback (limit.π D j)).map (g ≫ fj) =
      (Over.pullback (limit.π D j)).map (𝟙 Zj) := by
    apply (Iso.cancel_iso_hom_right _ _ α).mp
    simp only [Zj, Functor.map_comp]
    rw [Category.assoc, hn, ← Category.assoc, ← hg, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]
    rw [(Over.pullback (limit.π D j)).map_id Zj, Category.id_comp]
  obtain ⟨k₁, e₁, hk₁⟩ := eventually_eq_of_baseChange_eq B S hS hZ D
    hSize hHomSize hD hAffine hQc hQs j Yj Yj hYj hYj hYjfp hYjfp (fj ≫ g) (𝟙 Yj) hfg
  obtain ⟨k₂, e₂, hk₂⟩ := eventually_eq_of_baseChange_eq B S hS hZ D
    hSize hHomSize hD hAffine hQc hQs j Zj Zj hZj hZj hZjfp hZjfp (g ≫ fj) (𝟙 Zj) hgf
  let k := IsCofiltered.min (Over.mk e₁) (Over.mk e₂)
  let a := IsCofiltered.minToLeft (Over.mk e₁) (Over.mk e₂)
  let b := IsCofiltered.minToRight (Over.mk e₁) (Over.mk e₂)
  have hk₁' := baseChange_eq_of_baseChange_eq (D.map e₁) (D.map a.left) (D.map k.hom)
    (by rw [← D.map_comp]; exact congrArg D.map a.w) (fj ≫ g) (𝟙 Yj) hk₁
  have hk₂' := baseChange_eq_of_baseChange_eq (D.map e₂) (D.map b.left) (D.map k.hom)
    (by rw [← D.map_comp]; exact congrArg D.map b.w) (g ≫ fj) (𝟙 Zj) hk₂
  let : IsIso ((Over.pullback (D.map k.hom)).map fj) :=
    ⟨⟨(Over.pullback (D.map k.hom)).map g,
      by simpa only [Functor.map_comp] using hk₁'.trans ((Over.pullback (D.map k.hom)).map_id Yj),
      by simpa only [Functor.map_comp] using hk₂'.trans ((Over.pullback (D.map k.hom)).map_id Zj)⟩⟩
  refine ⟨k.left, k.hom ≫ e, ?_⟩
  have h := iteratedBaseChangeIso_naturality (D.map e) (D.map k.hom)
    (D.map (k.hom ≫ e)) (D.map_comp _ _).symm f
  have hf' : (Over.pullback (D.map (k.hom ≫ e))).map f =
      (iteratedBaseChangeIso (D.map e) (D.map k.hom) (D.map (k.hom ≫ e))
        (D.map_comp _ _).symm Y).inv ≫
      (Over.pullback (D.map k.hom)).map fj ≫
      (iteratedBaseChangeIso (D.map e) (D.map k.hom) (D.map (k.hom ≫ e))
        (D.map_comp _ _).symm Z).hom := by
    rw [show fj = (Over.pullback (D.map e)).map f from rfl, h, Iso.inv_hom_id_assoc]
  rw [hf']
  infer_instance

private theorem exists_mono_after_baseChange
    (i : I) (Y Z : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Z.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Z.hom)
    (f : Y ⟶ Z) [Mono ((Over.pullback (limit.π D i)).map f)] :
    ∃ (j : I) (e : j ⟶ i), Mono ((Over.pullback (D.map e)).map f) := by
  let c := overPullbackCone f f
  have hc := overPullbackCone_isPullback f f
  have hf := isFinitePresentation_overHom B S hS hZ (hD i) (hQc i) (hQs i)
    Y Z hY hZ' hYfp hZfp f
  have hR : AlgebraicGeometry.IsAlgebraicSpace B S hS c.pt.left :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f.left f.left hY hY hZ'
  have hRfst := isFinitePresentation_of_isPullback B S hS hR hY hY hZ'
    (IsPullback.of_hasPullback f.left f.left).flip hf
  have hRfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS c.pt.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hR hY (hD i)
      (pullback.fst f.left f.left) Y.hom hRfst hYfp
  have heq : (Over.pullback (limit.π D i)).map c.fst =
      (Over.pullback (limit.π D i)).map c.snd := by
    apply (cancel_mono ((Over.pullback (limit.π D i)).map f)).mp
    rw [← Functor.map_comp, ← Functor.map_comp, c.condition]
  obtain ⟨j, e, hj⟩ := eventually_eq_of_baseChange_eq B S hS hZ D hSize hHomSize
    hD hAffine hQc hQs i c.pt Y hR hY hRfp hYfp c.fst c.snd heq
  exact ⟨j, e, IsKernelPair.mono_of_eq_fst_snd (hc.map (Over.pullback (D.map e))) hj⟩

private theorem exists_lift_pair_after_baseChange
    (i : I) (A R W : Over (D.obj i))
    (hA : AlgebraicGeometry.IsAlgebraicSpace B S hS A.left)
    (hR : AlgebraicGeometry.IsAlgebraicSpace B S hS R.left)
    (hW : AlgebraicGeometry.IsAlgebraicSpace B S hS W.left)
    (hAfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS A.hom)
    (hRfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS R.hom)
    (hWfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS W.hom)
    (s t : R ⟶ W) (a b : A ⟶ W)
    (u : (Over.pullback (limit.π D i)).obj A ⟶ (Over.pullback (limit.π D i)).obj R)
    (hu₁ : u ≫ (Over.pullback (limit.π D i)).map s = (Over.pullback (limit.π D i)).map a)
    (hu₂ : u ≫ (Over.pullback (limit.π D i)).map t = (Over.pullback (limit.π D i)).map b) :
    ∃ (j : I) (e : j ⟶ i)
      (v : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj R),
      v ≫ (Over.pullback (D.map e)).map s = (Over.pullback (D.map e)).map a ∧
      v ≫ (Over.pullback (D.map e)).map t = (Over.pullback (D.map e)).map b := by
  classical
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ := exists_morphism_after_baseChange
    B S hS hZ D hSize hHomSize hD hAffine hQc hQs i A R hA hR hAfp hRfp u
  have hα' := iteratedBaseChangeIso_unique (D.map e) (limit.π D j) (limit.π D i)
    (limit.w D e) A α hα
  have hβ' := iteratedBaseChangeIso_unique (D.map e) (limit.π D j) (limit.π D i)
    (limit.w D e) R β hβ
  let γ := iteratedBaseChangeIso (D.map e) (limit.π D j) (limit.π D i) (limit.w D e) W
  have heq (v : R ⟶ W) (z : A ⟶ W)
      (hz : u ≫ (Over.pullback (limit.π D i)).map v = (Over.pullback (limit.π D i)).map z) :
      (Over.pullback (limit.π D j)).map (g ≫ (Over.pullback (D.map e)).map v) =
        (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map z) := by
    have hv : (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map v) ≫
        γ.hom = β.hom ≫ (Over.pullback (limit.π D i)).map v := by
      rw [hβ']
      exact iteratedBaseChangeIso_naturality _ _ _ (limit.w D e) v
    have hz' : (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map z) ≫
        γ.hom = α.hom ≫ (Over.pullback (limit.π D i)).map z := by
      rw [hα']
      exact iteratedBaseChangeIso_naturality _ _ _ (limit.w D e) z
    apply (Iso.cancel_iso_hom_right _ _ γ).mp
    rw [Functor.map_comp, Category.assoc, hv, ← Category.assoc, ← hg,
      Category.assoc, hz, hz']
  let Aj := (Over.pullback (D.map e)).obj A
  let Wj := (Over.pullback (D.map e)).obj W
  have hAj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS A.hom (D.map e) hA (hD j) (hD i)
  have hWj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS W.hom (D.map e) hW (hD j) (hD i)
  have hAjfp := isFinitePresentation_of_isPullback B S hS hAj hA (hD j) (hD i)
    (IsPullback.of_hasPullback A.hom (D.map e)) hAfp
  have hWjfp := isFinitePresentation_of_isPullback B S hS hWj hW (hD j) (hD i)
    (IsPullback.of_hasPullback W.hom (D.map e)) hWfp
  obtain ⟨k₁, e₁, hk₁⟩ := eventually_eq_of_baseChange_eq B S hS hZ D
    hSize hHomSize hD hAffine hQc hQs j Aj Wj hAj hWj hAjfp hWjfp
    (g ≫ (Over.pullback (D.map e)).map s) ((Over.pullback (D.map e)).map a) (heq s a hu₁)
  obtain ⟨k₂, e₂, hk₂⟩ := eventually_eq_of_baseChange_eq B S hS hZ D
    hSize hHomSize hD hAffine hQc hQs j Aj Wj hAj hWj hAjfp hWjfp
    (g ≫ (Over.pullback (D.map e)).map t) ((Over.pullback (D.map e)).map b) (heq t b hu₂)
  let k := IsCofiltered.min (Over.mk e₁) (Over.mk e₂)
  let c₁ := IsCofiltered.minToLeft (Over.mk e₁) (Over.mk e₂)
  let c₂ := IsCofiltered.minToRight (Over.mk e₁) (Over.mk e₂)
  have hk₁' := baseChange_eq_of_baseChange_eq (D.map e₁) (D.map c₁.left) (D.map k.hom)
    (by rw [← D.map_comp]; exact congrArg D.map c₁.w) _ _ hk₁
  have hk₂' := baseChange_eq_of_baseChange_eq (D.map e₂) (D.map c₂.left) (D.map k.hom)
    (by rw [← D.map_comp]; exact congrArg D.map c₂.w) _ _ hk₂
  let δ (Z : Over (D.obj i)) := iteratedBaseChangeIso (D.map e) (D.map k.hom)
    (D.map (k.hom ≫ e)) (D.map_comp _ _).symm Z
  let v := (δ A).inv ≫ (Over.pullback (D.map k.hom)).map g ≫ (δ R).hom
  have hfinal (x : R ⟶ W) (z : A ⟶ W)
      (hx : (Over.pullback (D.map k.hom)).map (g ≫ (Over.pullback (D.map e)).map x) =
        (Over.pullback (D.map k.hom)).map ((Over.pullback (D.map e)).map z)) :
      v ≫ (Over.pullback (D.map (k.hom ≫ e))).map x =
        (Over.pullback (D.map (k.hom ≫ e))).map z := by
    have hn := iteratedBaseChangeIso_naturality (D.map e) (D.map k.hom)
      (D.map (k.hom ≫ e)) (D.map_comp _ _).symm x
    have hz' := iteratedBaseChangeIso_naturality (D.map e) (D.map k.hom)
      (D.map (k.hom ≫ e)) (D.map_comp _ _).symm z
    calc
      v ≫ (Over.pullback (D.map (k.hom ≫ e))).map x =
          (δ A).inv ≫ (Over.pullback (D.map k.hom)).map g ≫
            (Over.pullback (D.map k.hom)).map ((Over.pullback (D.map e)).map x) ≫
            (δ W).hom := by
        simp only [v, Category.assoc]
        rw [← hn]
      _ = (δ A).inv ≫ (Over.pullback (D.map k.hom)).map
          ((Over.pullback (D.map e)).map z) ≫ (δ W).hom := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun z => (δ A).inv ≫ z ≫ (δ W).hom) hx
      _ = (Over.pullback (D.map (k.hom ≫ e))).map z := by
        rw [hz', Iso.inv_hom_id_assoc]
  exact ⟨k.left, k.hom ≫ e, v, hfinal s a hk₁', hfinal t b hk₂'⟩

omit hSize hHomSize in
include hZ in
/-- The étale relation presenting an algebraic space of finite presentation over the apex of
a cone, once it is defined at a stage, becomes an étale equivalence relation at a later
stage, where it presents a finite-presentation model of the space.

The cone `c` is arbitrary, and the two descent facts the argument needs from it — that a lift
of a pair of morphisms over the apex descends to a finite stage, and that monomorphy over the
apex descends to a finite stage — are taken as hypotheses `hLiftPair` and `hMonoDesc`. This is
what lets the same proof serve both the index-bounded development, where those two facts need
`#I < B.cutoff.ord.cof`, and the size-free development of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentRealised`, where they
hold for a system whose limit is realised in the site. -/
theorem exists_model_of_stage_relation_of_cone (c : Cone D)
    (hLiftPair : ∀ (i : I) (A R W : Over (D.obj i)),
      AlgebraicGeometry.IsAlgebraicSpace B S hS A.left →
      AlgebraicGeometry.IsAlgebraicSpace B S hS R.left →
      AlgebraicGeometry.IsAlgebraicSpace B S hS W.left →
      AlgebraicGeometry.Space.IsFinitePresentation B S hS A.hom →
      AlgebraicGeometry.Space.IsFinitePresentation B S hS R.hom →
      AlgebraicGeometry.Space.IsFinitePresentation B S hS W.hom →
      ∀ (s t : R ⟶ W) (a b : A ⟶ W)
        (u : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj R),
        u ≫ (Over.pullback (c.π.app i)).map s = (Over.pullback (c.π.app i)).map a →
        u ≫ (Over.pullback (c.π.app i)).map t = (Over.pullback (c.π.app i)).map b →
        ∃ (j : I) (e : j ⟶ i)
          (v : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj R),
          v ≫ (Over.pullback (D.map e)).map s = (Over.pullback (D.map e)).map a ∧
          v ≫ (Over.pullback (D.map e)).map t = (Over.pullback (D.map e)).map b)
    (hMonoDesc : ∀ (i : I) (Yᵢ Zᵢ : Over (D.obj i)),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left →
      AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left →
      AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom →
      AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom →
      ∀ f : Yᵢ ⟶ Zᵢ, Mono ((Over.pullback (c.π.app i)).map f) →
        ∃ (j : I) (e : j ⟶ i), Mono ((Over.pullback (D.map e)).map f))
    (nn : I)
    (hLim : AlgebraicGeometry.IsAlgebraicSpace B S hS c.pt)
    (Y : Over c.pt) (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    {W KR : AlgebraicGeometry.BigFppfOver B S hS} (w : yoneda.obj W ⟶ Y.left)
    (hws : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (hwe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (kt ks : KR ⟶ W) (hwk : IsPullback (yoneda.map kt) (yoneda.map ks) w w)
    {Wn Rn : AlgebraicGeometry.BigFppfOver B S hS}
    (hWnAff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Wn))
    (wn : yoneda.obj Wn ⟶ D.obj nn) (sn tn : Rn ⟶ Wn)
    (htn : yoneda.map tn ≫ wn = yoneda.map sn ≫ wn)
    (hsnEtale : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sn))
    (htnEtale : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tn))
    (hWnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wn)
    (hRnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map sn ≫ wn))
    (awn : W ⟶ Wn) (arn : KR ⟶ Rn)
    (hWnlim : IsPullback (yoneda.map awn) (w ≫ Y.hom) wn (c.π.app nn))
    (hRnlim : IsPullback (yoneda.map arn) (yoneda.map kt ≫ w ≫ Y.hom)
      (yoneda.map sn ≫ wn) (c.π.app nn))
    (hsnCompat : arn ≫ sn = kt ≫ awn) (htnCompat : arn ≫ tn = ks ≫ awn) :
    ∃ (i : I) (Yᵢ : Over (D.obj i)),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
          Nonempty (Y ≅ (Over.pullback (c.π.app i)).obj Yᵢ) := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  set rn := yoneda.map sn ≫ wn with hrnDef
  set pW := w ≫ Y.hom with hpWDef
  set pR := yoneda.map kt ≫ pW with hpRDef
  have ht : yoneda.map kt ≫ pW = pR := rfl
  have hs : yoneda.map ks ≫ pW = pR := by
    simpa only [pR, pW, ← Category.assoc] using congrArg (fun z => z ≫ Y.hom) hwk.w.symm
  have hRnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rn
  have hWnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wn
  let Rₙ := Over.mk rn
  let Wₙ := Over.mk wn
  let sₙ : Rₙ ⟶ Wₙ := Over.homMk (yoneda.map sn) rfl
  let tₙ : Rₙ ⟶ Wₙ := Over.homMk (yoneda.map tn) htn
  let sL : Over.mk pR ⟶ Over.mk pW := Over.homMk (yoneda.map kt) ht
  let tL : Over.mk pR ⟶ Over.mk pW := Over.homMk (yoneda.map ks) hs
  let εR : Over.mk pR ≅ (Over.pullback (c.π.app nn)).obj Rₙ :=
    Over.isoMk hRnlim.isoPullback hRnlim.isoPullback_hom_snd
  let εW : Over.mk pW ≅ (Over.pullback (c.π.app nn)).obj Wₙ :=
    Over.isoMk hWnlim.isoPullback hWnlim.isoPullback_hom_snd
  have hεs : εR.hom ≫ (Over.pullback (c.π.app nn)).map sₙ = sL ≫ εW.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [εR, εW, sₙ, sL, Rₙ, Wₙ, Over.pullback_map_left,
        IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc,
        Category.assoc] using congrArg yoneda.map hsnCompat
    · simp [εR, εW, sₙ, sL, Rₙ, Wₙ, Over.pullback_map_left, Category.assoc, ht]
  have hεt : εR.hom ≫ (Over.pullback (c.π.app nn)).map tₙ = tL ≫ εW.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [εR, εW, tₙ, tL, Rₙ, Wₙ, Over.pullback_map_left,
        IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc,
        Category.assoc] using congrArg yoneda.map htnCompat
    · simp [εR, εW, tₙ, tL, Rₙ, Wₙ, Over.pullback_map_left, Category.assoc, hs]
  let rL : Over.mk pW ⟶ Over.mk pR := Over.homMk
    (hwk.lift (𝟙 _) (𝟙 _) (by simp)) (by
      dsimp only [Over.mk_hom, Over.mk_left]
      rw [← ht, IsPullback.lift_fst_assoc, Category.id_comp])
  have hrLs : rL ≫ sL = 𝟙 _ := by ext; simp [rL, sL]
  have hrLt : rL ≫ tL = 𝟙 _ := by ext; simp [rL, tL]
  let rF := εW.inv ≫ rL ≫ εR.hom
  have hrFs : rF ≫ (Over.pullback (c.π.app nn)).map sₙ =
      (Over.pullback (c.π.app nn)).map (𝟙 Wₙ) := by
    simp only [rF, Category.assoc, hεs, ← Category.assoc rL sL, hrLs,
      Category.id_comp, Iso.inv_hom_id]
    exact ((Over.pullback (c.π.app nn)).map_id Wₙ).symm
  have hrFt : rF ≫ (Over.pullback (c.π.app nn)).map tₙ =
      (Over.pullback (c.π.app nn)).map (𝟙 Wₙ) := by
    simp only [rF, Category.assoc, hεt, ← Category.assoc rL tL, hrLt,
      Category.id_comp, Iso.inv_hom_id]
    exact ((Over.pullback (c.π.app nn)).map_id Wₙ).symm
  obtain ⟨ir, er', rr, hrrs, hrrt⟩ := hLiftPair nn Wₙ Rₙ Wₙ
    hWnAlg hRnAlg hWnAlg hWnFp hRnFp hWnFp sₙ tₙ (𝟙 _) (𝟙 _) rF hrFs hrFt
  let invL : Over.mk pR ⟶ Over.mk pR := Over.homMk
    (hwk.lift (yoneda.map ks) (yoneda.map kt) hwk.w.symm) (by
      dsimp only [Over.mk_hom, Over.mk_left]
      rw [← ht, IsPullback.lift_fst_assoc, hs])
  have hiLs : invL ≫ sL = tL := by ext; simp [invL, sL, tL]
  have hiLt : invL ≫ tL = sL := by ext; simp [invL, sL, tL]
  let invF := εR.inv ≫ invL ≫ εR.hom
  have hiFs : invF ≫ (Over.pullback (c.π.app nn)).map sₙ =
      (Over.pullback (c.π.app nn)).map tₙ := by
    simp only [invF, Category.assoc, hεs, ← Category.assoc invL sL, hiLs]
    rw [← hεt, Iso.inv_hom_id_assoc]
  have hiFt : invF ≫ (Over.pullback (c.π.app nn)).map tₙ =
      (Over.pullback (c.π.app nn)).map sₙ := by
    simp only [invF, Category.assoc, hεt, ← Category.assoc invL tL, hiLt]
    rw [← hεs, Iso.inv_hom_id_assoc]
  obtain ⟨ii, ei, ri, hris, hrit⟩ := hLiftPair nn Rₙ Rₙ Wₙ
    hRnAlg hRnAlg hWnAlg hRnFp hRnFp hWnFp sₙ tₙ tₙ sₙ invF hiFs hiFt
  let cn := overPullbackCone tₙ sₙ
  have hCAlg : AlgebraicGeometry.IsAlgebraicSpace B S hS cn.pt.left :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS tₙ.left sₙ.left hRnAlg hRnAlg hWnAlg
  have hsₙfp := isFinitePresentation_overHom B S hS hZ (hD nn) (hQc nn) (hQs nn)
    Rₙ Wₙ hRnAlg hWnAlg hRnFp hWnFp sₙ
  have hCfst := isFinitePresentation_of_isPullback B S hS hCAlg hRnAlg hRnAlg hWnAlg
    (IsPullback.of_hasPullback tₙ.left sₙ.left).flip hsₙfp
  have hCFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS cn.pt.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hCAlg hRnAlg (hD nn)
      (pullback.fst tₙ.left sₙ.left) rn hCfst hRnFp
  let F := Over.pullback (c.π.app nn)
  let ca : F.obj cn.pt ⟶ Over.mk pR := F.map cn.fst ≫ εR.inv
  let cb : F.obj cn.pt ⟶ Over.mk pR := F.map cn.snd ≫ εR.inv
  have hcab : ca ≫ tL = cb ≫ sL := by
    apply (Iso.cancel_iso_hom_right _ _ εW).mp
    simp only [ca, cb, Category.assoc]
    rw [← hεt, ← hεs, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc,
      ← F.map_comp, ← F.map_comp, cn.condition]
  have hcabLeft : ca.left ≫ yoneda.map ks = cb.left ≫ yoneda.map kt :=
    congrArg (fun z => z.left) hcab
  have hcomp : (ca.left ≫ yoneda.map kt) ≫ w =
      (cb.left ≫ yoneda.map ks) ≫ w := by
    rw [Category.assoc, hwk.w, ← Category.assoc, hcabLeft,
      Category.assoc, hwk.w, Category.assoc]
  let compL : F.obj cn.pt ⟶ Over.mk pR := Over.homMk
    (hwk.lift (ca.left ≫ yoneda.map kt) (cb.left ≫ yoneda.map ks) hcomp)
    (by
      dsimp only [Over.mk_hom]
      calc hwk.lift (ca.left ≫ yoneda.map kt)
              (cb.left ≫ yoneda.map ks) hcomp ≫ pR
          = hwk.lift (ca.left ≫ yoneda.map kt)
              (cb.left ≫ yoneda.map ks) hcomp ≫ yoneda.map kt ≫ pW := by
            rw [ht]
        _ = (ca.left ≫ yoneda.map kt) ≫ pW := IsPullback.lift_fst_assoc _ _ _ _ _
        _ = ca.left ≫ pR := by rw [Category.assoc, ht]
        _ = (F.obj cn.pt).hom := ca.w)
  have hcompS : compL ≫ sL = ca ≫ sL := by ext; simp [compL, sL]
  have hcompT : compL ≫ tL = cb ≫ tL := by ext; simp [compL, tL]
  let compF := compL ≫ εR.hom
  have hcompFs : compF ≫ F.map sₙ = F.map (cn.fst ≫ sₙ) := by
    simp only [compF]
    rw [Category.assoc, hεs, ← Category.assoc, hcompS]
    simp only [ca, Category.assoc]
    rw [← hεs, Iso.inv_hom_id_assoc, F.map_comp]
  have hcompFt : compF ≫ F.map tₙ = F.map (cn.snd ≫ tₙ) := by
    simp only [compF]
    rw [Category.assoc, hεt, ← Category.assoc, hcompT]
    simp only [cb, Category.assoc]
    rw [← hεt, Iso.inv_hom_id_assoc, F.map_comp]
  obtain ⟨ic, ec, rc, hrcs, hrct⟩ := hLiftPair nn cn.pt Rₙ Wₙ
    hCAlg hRnAlg hWnAlg hCFp hRnFp hWnFp sₙ tₙ
    (cn.fst ≫ sₙ) (cn.snd ≫ tₙ) compF hcompFs hcompFt
  let KWn := atlasKernelPair B S hS wn (hD nn).diagonal_representable
  have hψcomm : yoneda.map sn ≫ wn = yoneda.map tn ≫ wn := htn.symm
  let ψ₀ : Rn ⟶ KWn.R := yoneda.preimage
    (KWn.kernelPair.lift (yoneda.map sn) (yoneda.map tn) hψcomm)
  have hψ₀ : yoneda.map ψ₀ =
      KWn.kernelPair.lift (yoneda.map sn) (yoneda.map tn) hψcomm := yoneda.map_preimage _
  have hψs : ψ₀ ≫ KWn.s = sn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hψ₀]
    exact KWn.kernelPair.lift_fst _ _ _
  have hψt : ψ₀ ≫ KWn.t = tn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hψ₀]
    exact KWn.kernelPair.lift_snd _ _ _
  let Zₙ : Over (D.obj nn) := Over.mk (yoneda.map KWn.s ≫ wn)
  let ψ : Rₙ ⟶ Zₙ := Over.homMk (yoneda.map ψ₀) (by
    show yoneda.map ψ₀ ≫ yoneda.map KWn.s ≫ wn = rn
    rw [← Category.assoc, ← yoneda.map_comp, hψs])
  have hZnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS KWn.R
  have hKWnt : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map KWn.s) :=
    isFinitePresentation_of_isPullback B S hS hZnAlg hWnAlg hWnAlg (hD nn)
      KWn.kernelPair.flip hWnFp
  have hZnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zₙ.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hZnAlg hWnAlg (hD nn)
      (yoneda.map KWn.s) wn hKWnt hWnFp
  have hψfst : (F.map ψ).left ≫ pullback.fst Zₙ.hom (c.π.app nn) =
      pullback.fst rn (c.π.app nn) ≫ yoneda.map ψ₀ := by
    simp [F, Over.pullback_map_left, ψ, Rₙ]
  have hψsnd : (F.map ψ).left ≫ pullback.snd Zₙ.hom (c.π.app nn) =
      pullback.snd rn (c.π.app nn) := by
    simp [F, Over.pullback_map_left, ψ, Rₙ]
  have e₂ : (hRnlim.isoPullback.hom ≫ (F.map ψ).left) ≫
      pullback.snd Zₙ.hom (c.π.app nn) = pR := by
    rw [Category.assoc, hψsnd, hRnlim.isoPullback_hom_snd]
  have e₁ : (hRnlim.isoPullback.hom ≫ (F.map ψ).left) ≫
      pullback.fst Zₙ.hom (c.π.app nn) ≫ yoneda.map KWn.s =
      yoneda.map kt ≫ yoneda.map awn := by
    rw [Category.assoc, reassoc_of% hψfst, hRnlim.isoPullback_hom_fst_assoc,
      ← yoneda.map_comp ψ₀ KWn.s, hψs, ← yoneda.map_comp, hsnCompat,
      yoneda.map_comp]
  have e₁' : (hRnlim.isoPullback.hom ≫ (F.map ψ).left) ≫
      pullback.fst Zₙ.hom (c.π.app nn) ≫ yoneda.map KWn.t =
      yoneda.map ks ≫ yoneda.map awn := by
    rw [Category.assoc, reassoc_of% hψfst, hRnlim.isoPullback_hom_fst_assoc,
      ← yoneda.map_comp ψ₀ KWn.t, hψt, ← yoneda.map_comp, htnCompat,
      yoneda.map_comp]
  have hμ : Mono (hRnlim.isoPullback.hom ≫ (F.map ψ).left) := by
    refine ⟨fun {T} a b hab => ?_⟩
    have hab' : (a ≫ hRnlim.isoPullback.hom) ≫ (F.map ψ).left =
        (b ≫ hRnlim.isoPullback.hom) ≫ (F.map ψ).left := by
      simpa only [← Category.assoc] using hab
    refine hwk.hom_ext (hWnlim.hom_ext ?_ ?_) (hWnlim.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ← e₁]
      simp only [← Category.assoc]
      rw [hab']
    · rw [Category.assoc, Category.assoc, ht, ← e₂]
      simp only [← Category.assoc]
      rw [hab']
    · rw [Category.assoc, Category.assoc, ← e₁']
      simp only [← Category.assoc]
      rw [hab']
    · rw [Category.assoc, Category.assoc, hs, ← e₂]
      simp only [← Category.assoc]
      rw [hab']
  have hmonoψ : Mono ((Over.pullback (c.π.app nn)).map ψ) := by
    refine Over.mono_of_mono_left _ (hk := ?_)
    have := hμ
    rw [show (F.map ψ).left = inv hRnlim.isoPullback.hom ≫
      (hRnlim.isoPullback.hom ≫ (F.map ψ).left) from by simp]
    infer_instance
  obtain ⟨jm, ejm, hjmMono⟩ := hMonoDesc nn Rₙ Zₙ hRnAlg hZnAlg hRnFp hZnFp ψ hmonoψ
  -- a single stage carrying all of reflexivity, symmetry, transitivity and monicity
  let oo : Over nn := IsCofiltered.min
    (IsCofiltered.min (IsCofiltered.min (Over.mk er') (Over.mk ei)) (Over.mk ec))
    (Over.mk ejm)
  let aMono : oo ⟶ Over.mk ejm := IsCofiltered.minToRight _ _
  let aComp : oo ⟶ Over.mk ec :=
    IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToRight _ _
  let aRefl : oo ⟶ Over.mk er' :=
    IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft _ _
  let aSymm : oo ⟶ Over.mk ei :=
    IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToRight _ _
  obtain ⟨rrO, hrrOs, hrrOt⟩ := exists_liftPair_of_comp (D.map er') (D.map aRefl.left)
    (D.map oo.hom) (by rw [← D.map_comp]; exact congrArg D.map (Over.w aRefl))
    sₙ tₙ (𝟙 Wₙ) (𝟙 Wₙ) rr hrrs hrrt
  obtain ⟨riO, hriOs, hriOt⟩ := exists_liftPair_of_comp (D.map ei) (D.map aSymm.left)
    (D.map oo.hom) (by rw [← D.map_comp]; exact congrArg D.map (Over.w aSymm))
    sₙ tₙ tₙ sₙ ri hris hrit
  obtain ⟨rcO, hrcOs, hrcOt⟩ := exists_liftPair_of_comp (D.map ec) (D.map aComp.left)
    (D.map oo.hom) (by rw [← D.map_comp]; exact congrArg D.map (Over.w aComp))
    sₙ tₙ (cn.fst ≫ sₙ) (cn.snd ≫ tₙ) rc hrcs hrct
  have hmonoO : Mono ((Over.pullback (D.map oo.hom)).map ψ) := by
    have := mono_overPullback_map (D.map aMono.left)
      ((Over.pullback (D.map ejm)).map ψ) hjmMono
    have hcomp' : D.map aMono.left ≫ D.map ejm = D.map oo.hom := by
      rw [← D.map_comp]; exact congrArg D.map (Over.w aMono)
    rw [show (Over.pullback (D.map oo.hom)).map ψ =
        (iteratedBaseChangeIso (D.map ejm) (D.map aMono.left) (D.map oo.hom)
            hcomp' Rₙ).inv ≫
          (Over.pullback (D.map aMono.left)).map ((Over.pullback (D.map ejm)).map ψ) ≫
          (iteratedBaseChangeIso (D.map ejm) (D.map aMono.left) (D.map oo.hom)
            hcomp' Zₙ).hom from by
      rw [iteratedBaseChangeIso_naturality, Iso.inv_hom_id_assoc]]
    exact mono_comp' (IsIso.mono_of_iso _) (mono_comp' this (IsIso.mono_of_iso _))
  -- the descended relation as objects of the site
  have hoAff := ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS (D.map oo.hom)
    (hD oo.left) (hD nn)).out 2 1).mp (hAffine oo.hom)
  let WO := hoAff.1.pullback wn
  let RO := hoAff.1.pullback rn
  let wO := hoAff.1.fst wn
  let rO := hoAff.1.fst rn
  let bW : WO ⟶ Wn := hoAff.1.snd wn
  let bR : RO ⟶ Rn := hoAff.1.snd rn
  have hWO : IsPullback wO (yoneda.map bW) (D.map oo.hom) wn := hoAff.1.isPullback wn
  have hRO : IsPullback rO (yoneda.map bR) (D.map oo.hom) rn := hoAff.1.isPullback rn
  let εWO : Over.mk wO ≅ (Over.pullback (D.map oo.hom)).obj Wₙ :=
    Over.isoMk hWO.flip.isoPullback (by exact hWO.flip.isoPullback_hom_snd)
  let εRO : Over.mk rO ≅ (Over.pullback (D.map oo.hom)).obj Rₙ :=
    Over.isoMk hRO.flip.isoPullback (by exact hRO.flip.isoPullback_hom_snd)
  obtain ⟨sOO, hsOOdef⟩ : ∃ z : Over.mk rO ⟶ Over.mk wO,
      z = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map sₙ ≫ εWO.inv := ⟨_, rfl⟩
  obtain ⟨tOO, htOOdef⟩ : ∃ z : Over.mk rO ⟶ Over.mk wO,
      z = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map tₙ ≫ εWO.inv := ⟨_, rfl⟩
  let sO : RO ⟶ WO := yoneda.preimage sOO.left
  let tO : RO ⟶ WO := yoneda.preimage tOO.left
  have hsOl : yoneda.map sO = sOO.left := yoneda.map_preimage _
  have htOl : yoneda.map tO = tOO.left := yoneda.map_preimage _
  have hsOW : yoneda.map sO ≫ wO = rO := by rw [hsOl]; exact Over.w sOO
  have htOW : yoneda.map tO ≫ wO = rO := by rw [htOl]; exact Over.w tOO
  have hεWfst : εWO.hom.left ≫ pullback.fst wn (D.map oo.hom) = yoneda.map bW :=
    hWO.flip.isoPullback_hom_fst
  have hεRfst : εRO.hom.left ≫ pullback.fst rn (D.map oo.hom) = yoneda.map bR :=
    hRO.flip.isoPullback_hom_fst
  have hsoSq : sO ≫ bW = bR ≫ sn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, hsOl]
    have h1 : sOO ≫ εWO.hom = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map sₙ := by
      rw [hsOOdef]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h2 := congrArg (fun z : Over.mk rO ⟶ (Over.pullback (D.map oo.hom)).obj Wₙ =>
      z.left ≫ pullback.fst wn (D.map oo.hom)) h1
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, Rₙ, Wₙ,
      Over.mk_hom, pullback.lift_fst, hεWfst, reassoc_of% hεRfst, sₙ,
      Over.homMk_left] at h2
    exact h2
  have htoSq : tO ≫ bW = bR ≫ tn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, htOl]
    have h1 : tOO ≫ εWO.hom = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map tₙ := by
      rw [htOOdef]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h2 := congrArg (fun z : Over.mk rO ⟶ (Over.pullback (D.map oo.hom)).obj Wₙ =>
      z.left ≫ pullback.fst wn (D.map oo.hom)) h1
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, Rₙ, Wₙ,
      Over.mk_hom, pullback.lift_fst, hεWfst, reassoc_of% hεRfst, tₙ,
      Over.homMk_left] at h2
    exact h2
  have hsoSite : IsPullback bR sO sn bW := by
    apply IsPullback.of_map yoneda hsoSq.symm
    apply IsPullback.of_bot (v₂₂ := wn) ?_
      (by rw [← yoneda.map_comp, ← yoneda.map_comp, hsoSq]) hWO.flip
    rw [hsOW]
    exact hRO.flip
  have htoSite : IsPullback bR tO tn bW := by
    apply IsPullback.of_map yoneda htoSq.symm
    apply IsPullback.of_bot (v₂₂ := wn) ?_
      (by rw [← yoneda.map_comp, ← yoneda.map_comp, htoSq]) hWO.flip
    rw [htOW, htn]
    exact hRO.flip
  have hsOEtale : Etale (Q.map sO) := by
    let : Etale (Q.map sn) := hsnEtale
    exact (etale_iff_pullback_of_isPullback (hsoSite.map Q)).mpr inferInstance
  have htOEtale : Etale (Q.map tO) := by
    let : Etale (Q.map tn) := htnEtale
    exact (etale_iff_pullback_of_isPullback (htoSite.map Q)).mpr inferInstance
  have hWOAff : IsAffine (Q.obj WO) := by
    let : IsAffine (Q.obj Wn) := hWnAff
    let : _root_.AlgebraicGeometry.IsAffineHom (Q.map bW) := hoAff.2.property wn wO bW hWO
    exact isAffine_of_isAffineHom (Q.map bW)
  have hWOAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS WO
  have hROAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS RO
  have hwOFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wO :=
    isFinitePresentation_of_isPullback B S hS hWOAlg hWnAlg (hD oo.left) (hD nn)
      hWO.flip hWnFp
  have hrOFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rO :=
    isFinitePresentation_of_isPullback B S hS hROAlg hRnAlg (hD oo.left) (hD nn)
      hRO.flip hRnFp
  have hROqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS rO
    (hD oo.left) (hQc oo.left) hrOFp
  -- reflexivity, symmetry and transitivity of the descended relation
  have hsOO : εRO.hom ≫ (Over.pullback (D.map oo.hom)).map sₙ = sOO ≫ εWO.hom := by
    rw [hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have htOO : εRO.hom ≫ (Over.pullback (D.map oo.hom)).map tₙ = tOO ≫ εWO.hom := by
    rw [htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨rflO, hrflOdef⟩ : ∃ z : Over.mk wO ⟶ Over.mk rO, z = εWO.hom ≫ rrO ≫ εRO.inv :=
    ⟨_, rfl⟩
  have hrflS : rflO ≫ sOO = 𝟙 (Over.mk wO) := by
    rw [hrflOdef, hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrrOs]
    rw [show (Over.pullback (D.map oo.hom)).map (𝟙 Wₙ) = 𝟙 _ from
      (Over.pullback (D.map oo.hom)).map_id Wₙ, Category.id_comp, Iso.hom_inv_id]
  have hrflT : rflO ≫ tOO = 𝟙 (Over.mk wO) := by
    rw [hrflOdef, htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrrOt]
    rw [show (Over.pullback (D.map oo.hom)).map (𝟙 Wₙ) = 𝟙 _ from
      (Over.pullback (D.map oo.hom)).map_id Wₙ, Category.id_comp, Iso.hom_inv_id]
  obtain ⟨symO, hsymOdef⟩ : ∃ z : Over.mk rO ⟶ Over.mk rO, z = εRO.hom ≫ riO ≫ εRO.inv :=
    ⟨_, rfl⟩
  have hsymS : symO ≫ sOO = tOO := by
    rw [hsymOdef, hsOOdef, htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hriOs]
  have hsymT : symO ≫ tOO = sOO := by
    rw [hsymOdef, htOOdef, hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hriOt]
  let rflSite : WO ⟶ RO := yoneda.preimage rflO.left
  have hrflSite₁ : rflSite ≫ sO = 𝟙 WO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, hsOl, yoneda.map_id]
    simpa only [Over.comp_left, Over.id_left, Over.mk_left] using
      congrArg (fun z => z.left) hrflS
  have hrflSite₂ : rflSite ≫ tO = 𝟙 WO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, htOl, yoneda.map_id]
    simpa only [Over.comp_left, Over.id_left, Over.mk_left] using
      congrArg (fun z => z.left) hrflT
  let symSite : RO ⟶ RO := yoneda.preimage symO.left
  have hsymSite₁ : symSite ≫ sO = tO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, hsOl, htOl]
    simpa only [Over.comp_left] using congrArg (fun z => z.left) hsymS
  have hsymSite₂ : symSite ≫ tO = sO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, htOl, hsOl]
    simpa only [Over.comp_left] using congrArg (fun z => z.left) hsymT
  have hpoCond : yoneda.map (pullback.fst tO sO) ≫ yoneda.map tO =
      yoneda.map (pullback.snd tO sO) ≫ yoneda.map sO := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, pullback.condition]
  let Pₒ : Over (D.obj oo.left) := Over.mk (yoneda.map (pullback.fst tO sO) ≫ rO)
  let cfstₒ : Pₒ ⟶ Over.mk rO := Over.homMk (yoneda.map (pullback.fst tO sO)) rfl
  let csndₒ : Pₒ ⟶ Over.mk rO := Over.homMk (yoneda.map (pullback.snd tO sO)) (by
    show yoneda.map (pullback.snd tO sO) ≫ rO = yoneda.map (pullback.fst tO sO) ≫ rO
    calc yoneda.map (pullback.snd tO sO) ≫ rO
        = yoneda.map (pullback.snd tO sO) ≫ yoneda.map sO ≫ wO := by rw [hsOW]
      _ = yoneda.map (pullback.fst tO sO) ≫ yoneda.map tO ≫ wO := by
            rw [← Category.assoc, ← Category.assoc, ← hpoCond]
      _ = yoneda.map (pullback.fst tO sO) ≫ rO := by rw [htOW])
  have hcommₒ : cfstₒ ≫ tOO = csndₒ ≫ sOO := by
    apply Over.OverMorphism.ext
    simpa only [Over.comp_left, cfstₒ, csndₒ, Over.homMk_left, hsOl, htOl] using hpoCond
  have hPₒ : IsPullback cfstₒ csndₒ tOO sOO := by
    apply IsPullback.of_map (Over.forget (D.obj oo.left)) hcommₒ
    rw [show ((Over.forget (D.obj oo.left)).map tOO) = yoneda.map tO from htOl.symm,
      show ((Over.forget (D.obj oo.left)).map sOO) = yoneda.map sO from hsOl.symm]
    exact (IsPullback.of_hasPullback tO sO).map yoneda
  have hpbcn : IsPullback ((Over.pullback (D.map oo.hom)).map cn.fst)
      ((Over.pullback (D.map oo.hom)).map cn.snd)
      ((Over.pullback (D.map oo.hom)).map tₙ)
      ((Over.pullback (D.map oo.hom)).map sₙ) :=
    (overPullbackCone_isPullback tₙ sₙ).map (Over.pullback (D.map oo.hom))
  let ζ : Pₒ ⟶ (Over.pullback (D.map oo.hom)).obj cn.pt :=
    hpbcn.lift (cfstₒ ≫ εRO.hom) (csndₒ ≫ εRO.hom) (by
      simpa only [Category.assoc, ← htOO, ← hsOO] using
        congrArg (fun z : Pₒ ⟶ Over.mk wO => z ≫ εWO.hom) hcommₒ)
  have hζfst : ζ ≫ (Over.pullback (D.map oo.hom)).map cn.fst = cfstₒ ≫ εRO.hom :=
    hpbcn.lift_fst _ _ _
  have hζsnd : ζ ≫ (Over.pullback (D.map oo.hom)).map cn.snd = csndₒ ≫ εRO.hom :=
    hpbcn.lift_snd _ _ _
  obtain ⟨cmpO, hcmpOdef⟩ : ∃ z : Pₒ ⟶ Over.mk rO, z = ζ ≫ rcO ≫ εRO.inv := ⟨_, rfl⟩
  have hcmpS : cmpO ≫ sOO = cfstₒ ≫ sOO := by
    rw [hcmpOdef, hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrcOs,
      Functor.map_comp, reassoc_of% hζfst]
  have hcmpT : cmpO ≫ tOO = csndₒ ≫ tOO := by
    rw [hcmpOdef, htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrcOt,
      Functor.map_comp, reassoc_of% hζsnd]
  let cmpSite : pullback tO sO ⟶ RO := yoneda.preimage cmpO.left
  have hcmpSite₁ : cmpSite ≫ sO = pullback.fst tO sO ≫ sO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, yoneda.map_preimage, hsOl]
    simpa only [Over.comp_left, cfstₒ, Over.homMk_left] using
      congrArg (fun z => z.left) hcmpS
  have hcmpSite₂ : cmpSite ≫ tO = pullback.snd tO sO ≫ tO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, yoneda.map_preimage, htOl]
    simpa only [Over.comp_left, csndₒ, Over.homMk_left] using
      congrArg (fun z => z.left) hcmpT
  -- the atlas of the space compared with the descended relation
  let awO : W ⟶ WO := yoneda.preimage (hWO.flip.lift (yoneda.map awn)
    (pW ≫ c.π.app oo.left) (by rw [Category.assoc, c.w]; exact hWnlim.w))
  let arO : KR ⟶ RO := yoneda.preimage (hRO.flip.lift (yoneda.map arn)
    (pR ≫ c.π.app oo.left) (by rw [Category.assoc, c.w]; exact hRnlim.w))
  have hWOlim : IsPullback (yoneda.map awO) pW wO (c.π.app oo.left) := by
    have hh : IsPullback (yoneda.map awn) pW wn (c.π.app oo.left ≫ D.map oo.hom) := by
      rw [c.w]
      exact hWnlim
    simpa only [awO, yoneda.map_preimage] using hh.of_right' hWO.flip
  have hROlim : IsPullback (yoneda.map arO) pR rO (c.π.app oo.left) := by
    have hh : IsPullback (yoneda.map arn) pR rn (c.π.app oo.left ≫ D.map oo.hom) := by
      rw [c.w]
      exact hRnlim
    simpa only [arO, yoneda.map_preimage] using hh.of_right' hRO.flip
  have hawOb : awO ≫ bW = awn := by
    apply yoneda.map_injective
    simp [awO]
  have harOb : arO ≫ bR = arn := by
    apply yoneda.map_injective
    simp [arO]
  have hsOCompat : arO ≫ sO = kt ≫ awO := by
    apply yoneda.map_injective
    apply hWO.hom_ext
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, hsOW,
        hWOlim.w, hROlim.w, ← Category.assoc, ht]
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc,
        ← yoneda.map_comp sO bW, ← yoneda.map_comp awO bW, hsoSq, hawOb, yoneda.map_comp,
        ← Category.assoc, ← yoneda.map_comp arO bR, harOb, ← yoneda.map_comp, hsnCompat,
        yoneda.map_comp]
  have htOCompat : arO ≫ tO = ks ≫ awO := by
    apply yoneda.map_injective
    apply hWO.hom_ext
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, htOW,
        hWOlim.w, hROlim.w, ← Category.assoc, hs]
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc,
        ← yoneda.map_comp tO bW, ← yoneda.map_comp awO bW, htoSq, hawOb, yoneda.map_comp,
        ← Category.assoc, ← yoneda.map_comp arO bR, harOb, ← yoneda.map_comp, htnCompat,
        yoneda.map_comp]
  have hsqsO : IsPullback arO kt sO awO := by
    apply IsPullback.of_map yoneda hsOCompat
    apply IsPullback.of_bot _
      (by simpa only [Functor.map_comp] using congrArg yoneda.map hsOCompat) hWOlim
    simpa only [ht, hsOW] using hROlim
  have hsqtO : IsPullback arO ks tO awO := by
    apply IsPullback.of_map yoneda htOCompat
    apply IsPullback.of_bot _
      (by simpa only [Functor.map_comp] using congrArg yoneda.map htOCompat) hWOlim
    simpa only [hs, htOW] using hROlim
  -- joint monicity of the descended relation
  have hρcomm : yoneda.map sO ≫ wO = yoneda.map tO ≫ wO := by rw [hsOW, htOW]
  let KWO := atlasKernelPair B S hS wO (hD oo.left).diagonal_representable
  let ρ : RO ⟶ KWO.R := yoneda.preimage
    (KWO.kernelPair.lift (yoneda.map sO) (yoneda.map tO) hρcomm)
  have hρl : yoneda.map ρ =
      KWO.kernelPair.lift (yoneda.map sO) (yoneda.map tO) hρcomm := yoneda.map_preimage _
  have hρs : ρ ≫ KWO.s = sO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hρl]
    exact KWO.kernelPair.lift_fst _ _ _
  have hρt : ρ ≫ KWO.t = tO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hρl]
    exact KWO.kernelPair.lift_snd _ _ _
  have _ : IsIso εRO.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (D.obj oo.left)).map εRO.hom))
  have hνmono : Mono (εRO.hom.left ≫
      ((Over.pullback (D.map oo.hom)).map ψ).left) := by
    exact mono_comp' (IsIso.mono_of_iso _) (Over.mono_left_of_mono _)
  have hνfst : εRO.hom.left ≫ ((Over.pullback (D.map oo.hom)).map ψ).left ≫
      pullback.fst Zₙ.hom (D.map oo.hom) = yoneda.map bR ≫ yoneda.map ψ₀ := by
    simp only [Over.pullback_map_left, Rₙ, Over.mk_hom,
      pullback.lift_fst, ψ, Over.homMk_left, reassoc_of% hεRfst]
  have hνsnd : εRO.hom.left ≫ ((Over.pullback (D.map oo.hom)).map ψ).left ≫
      pullback.snd Zₙ.hom (D.map oo.hom) = rO := by
    simp only [Over.pullback_map_left, pullback.lift_snd]
    exact εRO.hom.w
  have hρmono : Mono (yoneda.map ρ) := by
    refine ⟨fun {T} a b hab => ?_⟩
    have ha : a ≫ yoneda.map sO = b ≫ yoneda.map sO := by
      rw [← hρs, yoneda.map_comp]
      simp only [← Category.assoc]
      rw [hab]
    have hb : a ≫ yoneda.map tO = b ≫ yoneda.map tO := by
      rw [← hρt, yoneda.map_comp]
      simp only [← Category.assoc]
      rw [hab]
    apply (cancel_mono (εRO.hom.left ≫ ((Over.pullback (D.map oo.hom)).map ψ).left)).mp
    apply pullback.hom_ext
    · simp only [Category.assoc, hνfst]
      apply KWn.kernelPair.hom_ext
      · simp only [Category.assoc, ← yoneda.map_comp ψ₀ KWn.s, hψs,
          ← yoneda.map_comp bR sn, ← hsoSq, yoneda.map_comp]
        simp only [← Category.assoc]
        rw [ha]
      · simp only [Category.assoc, ← yoneda.map_comp ψ₀ KWn.t, hψt,
          ← yoneda.map_comp bR tn, ← htoSq, yoneda.map_comp]
        simp only [← Category.assoc]
        rw [hb]
    · simp only [Category.assoc, hνsnd]
      rw [← hsOW]
      simp only [← Category.assoc]
      rw [ha]
  have hjmO : JointlyMono₂ ((Over.post (X := B.obj hS) B.inclusion).map sO)
      ((Over.post (X := B.obj hS) B.inclusion).map tO) :=
    jointlyMono₂_of_mono_to_kernelPair B S hS wO KWO.s KWO.t KWO.kernelPair
      sO tO ρ hρs hρt hρmono
  obtain ⟨Yᵢ, hYᵢalg, hYᵢfp, hYᵢiso⟩ := exists_model_of_descended_presentation_of_hom
    B S hS hZ D oo.left (c.π.app oo.left) hLim (hD oo.left) (hQc oo.left) (hQs oo.left) Y hY w
    hws hwe
    kt ks hwk hWOAff sO tO hsOEtale htOEtale hjmO rflSite hrflSite₁ hrflSite₂
    symSite hsymSite₁ hsymSite₂ cmpSite hcmpSite₁ hcmpSite₂ wO hρcomm hwOFp hROqc
    awO arO (by rw [← hpWDef]; exact hWOlim) hsqsO hsqtO
  exact ⟨oo.left, Yᵢ, hYᵢalg, hYᵢfp, hYᵢiso⟩

include hZ hSize hHomSize hD hAffine hQc hQs in
/-- The étale relation presenting an algebraic space of finite presentation over the
limit, once it is defined at a stage, becomes an étale equivalence relation at a later
stage, where it presents a finite-presentation model of the space. -/
private theorem exists_model_of_stage_relation (nn : I)
    (hLim : AlgebraicGeometry.IsAlgebraicSpace B S hS (limit D))
    (Y : Over (limit D)) (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    {W KR : AlgebraicGeometry.BigFppfOver B S hS} (w : yoneda.obj W ⟶ Y.left)
    (hws : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (hwe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (kt ks : KR ⟶ W) (hwk : IsPullback (yoneda.map kt) (yoneda.map ks) w w)
    {Wn Rn : AlgebraicGeometry.BigFppfOver B S hS}
    (hWnAff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Wn))
    (wn : yoneda.obj Wn ⟶ D.obj nn) (sn tn : Rn ⟶ Wn)
    (htn : yoneda.map tn ≫ wn = yoneda.map sn ≫ wn)
    (hsnEtale : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sn))
    (htnEtale : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tn))
    (hWnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wn)
    (hRnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map sn ≫ wn))
    (awn : W ⟶ Wn) (arn : KR ⟶ Rn)
    (hWnlim : IsPullback (yoneda.map awn) (w ≫ Y.hom) wn (limit.π D nn))
    (hRnlim : IsPullback (yoneda.map arn) (yoneda.map kt ≫ w ≫ Y.hom)
      (yoneda.map sn ≫ wn) (limit.π D nn))
    (hsnCompat : arn ≫ sn = kt ≫ awn) (htnCompat : arn ≫ tn = ks ≫ awn) :
    ∃ (i : I) (Yᵢ : Over (D.obj i)),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D i)).obj Yᵢ) := by
  refine exists_model_of_stage_relation_of_cone B S hS hZ D hD hAffine hQc hQs
    (limit.cone D) ?_ ?_ nn hLim Y hY w hws hwe kt ks hwk hWnAff wn sn tn htn
    hsnEtale htnEtale hWnFp hRnFp awn arn hWnlim hRnlim hsnCompat htnCompat
  · intro i A R W' hA hR hW hAfp hRfp hWfp s t a b u hu₁ hu₂
    exact exists_lift_pair_after_baseChange B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i A R W' hA hR hW hAfp hRfp hWfp s t a b u hu₁ hu₂
  · intro i Yᵤ Zᵤ hYᵤ hZᵤ hYᵤfp hZᵤfp f hf
    have : Mono ((Over.pullback (limit.π D i)).map f) := hf
    exact exists_mono_after_baseChange B S hS hZ D hSize hHomSize hD hAffine hQc hQs
      i Yᵤ Zᵤ hYᵤ hZᵤ hYᵤfp hZᵤfp f

/-- Every algebraic space of finite presentation over the limit descends to a
finite stage. -/
@[stacks 07SK "essential surjectivity"]
public theorem exists_model_of_finitePresentation
    (Y : Over (limit D))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom) :
    ∃ (i : I) (Yᵢ : Over (D.obj i)),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
        Nonempty (Y ≅ (Over.pullback (limit.π D i)).obj Yᵢ)  := by
  classical
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨U₀, p₀, hU₀, hs₀, he₀⟩ := exists_affine_etale_atlas B S hS
    (D.obj i) (hD i) (hQc i)
  let U₀' : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hp₀ := represented_etale_of_isEtale B S hS p₀ he₀
  obtain ⟨U, p, q, hp⟩ :=
    AlgebraicGeometry.Space.isAffineHom_limitπ B S hS D hSize hHomSize hAffine i U₀' p₀
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) Q
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : E.presheaf.IsStableUnderBaseChange := E.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : E.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition E (etaleInverseImageIsStableUnderComposition _)
  have hs : P.presheaf p := P.presheaf.of_isPullback hp.flip hs₀
  have he : E.presheaf p := E.presheaf.of_isPullback hp.flip hp₀
  have hX := AlgebraicGeometry.Space.isAlgebraicSpace_limit B S hS D hSize hHomSize hD hAffine
  have hXqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    hX (hQs i)
    (isQuasiSeparated_of_isAffineHom B S hS hX (hD i) (limit.π D i)
      (AlgebraicGeometry.Space.isAffineHom_limitπ B S hS D hSize hHomSize hAffine i))
  have hYqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS hZ hY hXqs hFp.2.2
  obtain ⟨W, w, g, hws, hwe, hw, hg⟩ :=
    exists_affine_finitePresentation_chart B S hS hX hY Y.hom hFp U p hs he
  let K := atlasKernelPair B S hS w hY.diagonal_representable
  have hKt := atlasKernelPair_target_finitePresentation B S hS hZ hY hYqs W w hwe
  have hKg : AlgebraicGeometry.FinitePresentation (Q.map (K.s ≫ g)) := by
    let : LocallyOfFinitePresentation (Q.map K.s) := hKt.1
    let : QuasiCompact (Q.map K.s) := hKt.2.1
    let : QuasiSeparated (Q.map K.s) := hKt.2.2
    let : LocallyOfFinitePresentation (Q.map g) := hg.1
    let : QuasiCompact (Q.map g) := hg.2.1
    let : QuasiSeparated (Q.map g) := hg.2.2
    rw [Q.map_comp]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W.obj) := W.property
  obtain ⟨j, Wj, wj, aw, hwj, hWjaff, hWmodel⟩ := exists_affine_site_model_over_affine_chart
    B S hS hZ D hSize hHomSize hD hAffine hQc hQs i U₀' p₀ hp₀ U p q hp W.obj g hg
  obtain ⟨k, Rk, rk, ar, hrk, hRmodel⟩ := exists_site_model_over_affine_chart
    B S hS hZ D hSize hHomSize hD hAffine hQc hQs i U₀' p₀ hp₀ U p q hp
      K.R (K.s ≫ g) hKg
  let l := IsCofiltered.min j.left k.left
  let ej : l ⟶ j.left := IsCofiltered.minToLeft _ _
  let ek : l ⟶ k.left := IsCofiltered.minToRight _ _
  let pW := yoneda.map g ≫ p
  let pR := yoneda.map (K.s ≫ g) ≫ p
  obtain ⟨WlA, wl, bl, hbl⟩ := hAffine ej ⟨Wj, hWjaff⟩ wj
  let Wl := WlA.obj
  have hwl : AlgebraicGeometry.Space.IsFinitePresentation B S hS wl :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wj)
      (hD l) (hD j.left) hbl.flip hwj
  let awl : W.obj ⟶ Wl := yoneda.preimage (hbl.flip.lift (yoneda.map aw)
    (pW ≫ limit.π D l) (by rw [Category.assoc, limit.w]; exact hWmodel.w))
  have hWl : IsPullback (yoneda.map awl) pW wl (limit.π D l) := by
    have hh : IsPullback (yoneda.map aw) pW wj (limit.π D l ≫ D.map ej) := by
      rw [limit.w]
      exact hWmodel
    simpa only [awl, yoneda.map_preimage] using hh.of_right' hbl.flip
  obtain ⟨Rl, rl, arl, hrl, hRl⟩ := advance_represented_model B S hS
    (hD l) (hD k.left) rk ar pR (limit.π D l) (D.map ek) (limit.π D k.left)
    (limit.w D ek) (hAffine ek) hrk hRmodel
  let KW := atlasKernelPair B S hS wl (hD l).diagonal_representable
  have hWlAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl
  have hKWAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS KW.R
  have hKWt : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map KW.s) :=
    isFinitePresentation_of_isPullback B S hS hKWAlg hWlAlg hWlAlg (hD l)
      KW.kernelPair.flip hwl
  let vKW := yoneda.map KW.s ≫ wl
  have hKWfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS vKW :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hKWAlg hWlAlg (hD l)
      (yoneda.map KW.s) wl hKWt hwl
  have ht : yoneda.map K.s ≫ pW = pR := by
    simp only [pW, pR, Functor.map_comp, Category.assoc]
  have hs : yoneda.map K.t ≫ pW = pR := by
    rw [← ht]
    simpa only [pW, hw, Category.assoc] using
      congrArg (fun t => t ≫ Y.hom) K.kernelPair.w.symm
  let b : yoneda.obj K.R ⟶ yoneda.obj KW.R := KW.kernelPair.lift
    (yoneda.map K.s ≫ yoneda.map awl) (yoneda.map K.t ≫ yoneda.map awl) (by
      simp only [Category.assoc, hWl.w]
      rw [← Category.assoc, ht, ← Category.assoc, hs])
  have hb : b ≫ vKW = pR ≫ limit.π D l := by
    simp only [b, vKW, IsPullback.lift_fst_assoc]
    rw [Category.assoc, hWl.w, ← Category.assoc, ht]
  let source := Over.mk rl
  let target := Over.mk vKW
  let er : Over.mk pR ≅ (Over.pullback (limit.π D l)).obj source :=
    Over.isoMk hRl.isoPullback (by exact hRl.isoPullback_hom_snd)
  let f : (Over.pullback (limit.π D l)).obj source ⟶
      (Over.pullback (limit.π D l)).obj target :=
    Over.homMk (pullback.lift (er.inv.left ≫ b)
      (pullback.snd rl (limit.π D l)) (by
        show (er.inv.left ≫ b) ≫ vKW = _
        rw [Category.assoc, hb, ← Category.assoc]
        exact congrArg (fun t => t ≫ limit.π D l) er.inv.w)) (by simp [source, target])
  obtain ⟨m, em, gm, αm, βm, hαm, hβm, hgm⟩ := exists_morphism_after_baseChange
    B S hS hZ D hSize hHomSize hD hAffine hQc hQs l source target
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rl) hKWAlg hrl hKWfp f
  have hαmEq := iteratedBaseChangeIso_unique (D.map em) (limit.π D m) (limit.π D l)
    (limit.w D em) source αm hαm
  have hβmEq := iteratedBaseChangeIso_unique (D.map em) (limit.π D m) (limit.π D l)
    (limit.w D em) target βm hβm
  rw [hαmEq, hβmEq] at hgm
  have hmAffine := ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS (D.map em)
    (hD m) (hD l)).out 2 1).mp (hAffine em)
  let Rm := hmAffine.1.pullback rl
  let Wm := hmAffine.1.pullback wl
  let rm := hmAffine.1.fst rl
  let wm := hmAffine.1.fst wl
  have hRm : IsPullback rm (yoneda.map (hmAffine.1.snd rl)) (D.map em) rl :=
    hmAffine.1.isPullback rl
  have hWm : IsPullback wm (yoneda.map (hmAffine.1.snd wl)) (D.map em) wl :=
    hmAffine.1.isPullback wl
  have hWmAffineHom : _root_.AlgebraicGeometry.IsAffineHom (Q.map (hmAffine.1.snd wl)) :=
    hmAffine.2.property wl wm (hmAffine.1.snd wl) hWm
  have hWmAffine : IsAffine (Q.obj Wm) := by
    let : IsAffine (Q.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
        WlA)) := WlA.property
    let : _root_.AlgebraicGeometry.IsAffineHom (Q.map (hmAffine.1.snd wl)) := hWmAffineHom
    exact isAffine_of_isAffineHom (Q.map (hmAffine.1.snd wl))
  have hRmFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rm :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rm)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rl) (hD m) (hD l) hRm.flip hrl
  have hWmFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wm :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wm)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl) (hD m) (hD l) hWm.flip hwl
  let st : target ⟶ Over.mk wl := Over.homMk (yoneda.map KW.s) rfl
  let tt : target ⟶ Over.mk wl := Over.homMk (yoneda.map KW.t) KW.kernelPair.w.symm
  let sm₀ := gm ≫ (Over.pullback (D.map em)).map st
  let tm₀ := gm ≫ (Over.pullback (D.map em)).map tt
  let sm : Rm ⟶ Wm := yoneda.preimage
    (hRm.flip.isoPullback.hom ≫ sm₀.left ≫ hWm.flip.isoPullback.inv)
  let tm : Rm ⟶ Wm := yoneda.preimage
    (hRm.flip.isoPullback.hom ≫ tm₀.left ≫ hWm.flip.isoPullback.inv)
  have hsm : yoneda.map sm ≫ wm = rm := by
    simp only [sm, yoneda.map_preimage, Category.assoc, IsPullback.isoPullback_inv_snd]
    rw [show sm₀.left ≫ pullback.snd wl (D.map em) =
      pullback.snd rl (D.map em) from sm₀.w, hRm.flip.isoPullback_hom_snd]
  have htm : yoneda.map tm ≫ wm = rm := by
    simp only [tm, yoneda.map_preimage, Category.assoc, IsPullback.isoPullback_inv_snd]
    rw [show tm₀.left ≫ pullback.snd wl (D.map em) =
      pullback.snd rl (D.map em) from tm₀.w, hRm.flip.isoPullback_hom_snd]
  let arm : K.R ⟶ Rm := yoneda.preimage (hRm.flip.lift (yoneda.map arl)
    (pR ≫ limit.π D m) (by rw [Category.assoc, limit.w]; exact hRl.w))
  let awm : W.obj ⟶ Wm := yoneda.preimage (hWm.flip.lift (yoneda.map awl)
    (pW ≫ limit.π D m) (by rw [Category.assoc, limit.w]; exact hWl.w))
  have hRlim : IsPullback (yoneda.map arm) pR rm (limit.π D m) := by
    have hh : IsPullback (yoneda.map arl) pR rl (limit.π D m ≫ D.map em) := by
      rw [limit.w]
      exact hRl
    simpa only [arm, yoneda.map_preimage] using hh.of_right' hRm.flip
  have hWlim : IsPullback (yoneda.map awm) pW wm (limit.π D m) := by
    have hh : IsPullback (yoneda.map awl) pW wl (limit.π D m ≫ D.map em) := by
      rw [limit.w]
      exact hWl
    simpa only [awm, yoneda.map_preimage] using hh.of_right' hWm.flip
  have harm : yoneda.map arm ≫ yoneda.map (hmAffine.1.snd rl) = yoneda.map arl := by
    simp [arm]
  have hawm : yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl) = yoneda.map awl := by
    simp [awm]
  have harPB : yoneda.map arm ≫ hRm.flip.isoPullback.hom =
      er.hom.left ≫
        (iteratedBaseChangeIso (D.map em) (limit.π D m) (limit.π D l)
          (limit.w D em) source).inv.left ≫
          pullback.fst ((Over.pullback (D.map em)).obj source).hom (limit.π D m) := by
    apply pullback.hom_ext
    · simp [arm, er, source, iteratedBaseChangeIso, Category.assoc]
    · simp [arm, er, source, iteratedBaseChangeIso, Category.assoc]
  have hgm' : yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
      pullback.fst vKW (D.map em) = b := by
    have hh := congrArg (fun z => er.hom ≫
      (iteratedBaseChangeIso (D.map em) (limit.π D m) (limit.π D l)
        (limit.w D em) source).inv ≫ z) hgm
    simp only [Iso.inv_hom_id_assoc] at hh
    have hh' := congrArg (fun z => z.left ≫ pullback.fst vKW (limit.π D l)) hh
    have her : er.hom.left ≫ er.inv.left = 𝟙 _ :=
      congrArg (fun z => z.left) er.hom_inv_id
    simp only [Over.comp_left, Category.assoc] at hh'
    have hβfst := iteratedBaseChangeIso_hom_fst (D.map em) (limit.π D m)
      (limit.π D l) (limit.w D em) target
    change (iteratedBaseChangeIso (D.map em) (limit.π D m) (limit.π D l)
      (limit.w D em) target).hom.left ≫ pullback.fst vKW (limit.π D l) = _ at hβfst
    rw [hβfst] at hh'
    rw [reassoc_of% harPB]
    simpa only [source, target,
      Over.pullback_map_left, Over.pullback_obj_hom, Over.mk_hom, f,
      Over.homMk_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      her, reassoc_of% her, Category.id_comp] using hh'.symm
  have hsmCompat : arm ≫ sm = K.s ≫ awm := by
    apply yoneda.map_injective
    apply hWm.hom_ext
    · simp only [Functor.map_comp, Category.assoc, hsm, hRlim.w,
        hWlim.w]
      rw [← Category.assoc, ht]
    · simp only [Functor.map_comp, Category.assoc, sm, yoneda.map_preimage,
        IsPullback.isoPullback_inv_fst]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫
        (gm ≫ (Over.pullback (D.map em)).map st).left ≫
          pullback.fst wl (D.map em) =
        yoneda.map K.s ≫ yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl)
      simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, hawm, source, target, st, Over.mk_hom, Over.homMk_left]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
        pullback.fst vKW (D.map em) ≫ yoneda.map KW.s = _
      rw [reassoc_of% hgm']
      simp [b]
  have htmCompat : arm ≫ tm = K.t ≫ awm := by
    apply yoneda.map_injective
    apply hWm.hom_ext
    · simp only [Functor.map_comp, Category.assoc, htm, hRlim.w,
        hWlim.w]
      rw [← Category.assoc, hs]
    · simp only [Functor.map_comp, Category.assoc, tm, yoneda.map_preimage,
        IsPullback.isoPullback_inv_fst]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫
        (gm ≫ (Over.pullback (D.map em)).map tt).left ≫
          pullback.fst wl (D.map em) =
        yoneda.map K.t ≫ yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl)
      simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, hawm, source, target, tt, Over.mk_hom, Over.homMk_left]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
        pullback.fst vKW (D.map em) ≫ yoneda.map KW.t = _
      rw [reassoc_of% hgm']
      simp [b]
  have hsmSquare : IsPullback arm K.s sm awm := by
    apply IsPullback.of_map yoneda hsmCompat
    apply IsPullback.of_bot _ (by
      simpa only [Functor.map_comp] using congrArg yoneda.map hsmCompat) hWlim
    simpa only [hsm, ht] using hRlim
  have htmSquare : IsPullback arm K.t tm awm := by
    apply IsPullback.of_map yoneda htmCompat
    apply IsPullback.of_bot _ (by
      simpa only [Functor.map_comp] using congrArg yoneda.map htmCompat) hWlim
    simpa only [htm, hs] using hRlim
  have hRmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rm
  have hWmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wm
  have hSmFp := finitePresentation_of_yoneda B S hS sm
    (isFinitePresentation_overHom B S hS hZ (hD m) (hQc m) (hQs m)
      (Over.mk rm) (Over.mk wm) hRmAlg hWmAlg hRmFp hWmFp
      (Over.homMk (yoneda.map sm) hsm))
  have hTmFp := finitePresentation_of_yoneda B S hS tm
    (isFinitePresentation_overHom B S hS hZ (hD m) (hQc m) (hQs m)
      (Over.mk rm) (Over.mk wm) hRmAlg hWmAlg hRmFp hWmFp
      (Over.homMk (yoneda.map tm) htm))
  let WmA : AlgebraicGeometry.BigAffineFppf B S hS := ⟨Wm, hWmAffine⟩
  let : Etale ((Over.pullback (Q.map awm)).obj (Over.mk (Q.map sm))).hom :=
    (etale_iff_pullback_of_isPullback (hsmSquare.map Q)).mp
      (hwe.property w (yoneda.map K.t) K.s K.kernelPair.flip)
  let : Etale ((Over.pullback (Q.map awm)).obj (Over.mk (Q.map tm))).hom :=
    (etale_iff_pullback_of_isPullback (htmSquare.map Q)).mp
      (hwe.property w (yoneda.map K.s) K.t K.kernelPair)
  obtain ⟨js, hjs⟩ := eventually_etale_over_affine_chart B S hS hZ D hSize hHomSize
    hD hAffine hQc hQs m WmA wm W pW awm hWlim.flip (Over.mk (Q.map sm)) hSmFp
  obtain ⟨jt, hjt⟩ := eventually_etale_over_affine_chart B S hS hZ D hSize hHomSize
    hD hAffine hQc hQs m WmA wm W pW awm hWlim.flip (Over.mk (Q.map tm)) hTmFp
  let n := IsCofiltered.min js jt
  let as' := IsCofiltered.minToLeft js jt
  let at' := IsCofiltered.minToRight js jt
  let En := affineStageChartOverDiagram B S hS hZ D hSize hHomSize
    hD hAffine hQc hQs m WmA wm hAffine
  let Cn := affineStageChart B S hS D m WmA wm hAffine n
  have hsChart : Etale (pullback.snd (Q.map sm) (Q.map Cn.toChart)) := by
    let : Etale ((Over.pullback (Q.map (En.obj js).hom)).obj (Over.mk (Q.map sm))).hom := hjs
    exact etale_pullback_of_etale_pullback (Q.map (En.obj js).hom)
      (Q.map (En.map as').left) (Q.map (En.obj n).hom)
      (by rw [← Q.map_comp]; exact congrArg Q.map (En.map as').w) (Over.mk (Q.map sm))
  have htChart : Etale (pullback.snd (Q.map tm) (Q.map Cn.toChart)) := by
    let : Etale ((Over.pullback (Q.map (En.obj jt).hom)).obj (Over.mk (Q.map tm))).hom := hjt
    exact etale_pullback_of_etale_pullback (Q.map (En.obj jt).hom)
      (Q.map (En.map at').left) (Q.map (En.obj n).hom)
      (by rw [← Q.map_comp]; exact congrArg Q.map (En.map at').w) (Over.mk (Q.map tm))
  let Wn := Cn.U.obj
  let wn := Cn.toStage
  let Rn := pullback sm Cn.toChart
  let sn : Rn ⟶ Wn := pullback.snd sm Cn.toChart
  let br : Rn ⟶ Rm := pullback.fst sm Cn.toChart
  let rn := yoneda.map sn ≫ wn
  have hRn : IsPullback (yoneda.map br) rn rm (D.map n.hom) := by
    have hh := ((IsPullback.of_hasPullback sm Cn.toChart).map yoneda).paste_vert
      Cn.isPullback.flip
    simpa only [hsm] using hh
  let tn : Rn ⟶ Wn := yoneda.preimage (Cn.isPullback.lift rn
    (yoneda.map br ≫ yoneda.map tm) (by
      simp only [Category.assoc, htm]
      exact hRn.w.symm))
  have htn : yoneda.map tn ≫ wn = rn := by simp [tn, wn]
  have htnBr : br ≫ tm = tn ≫ Cn.toChart := by
    apply yoneda.map_injective
    simp [tn]
  have htnSquare : IsPullback br tn tm Cn.toChart := by
    apply IsPullback.of_map yoneda htnBr
    apply IsPullback.of_bot _ (by simpa only [Functor.map_comp] using congrArg yoneda.map htnBr)
      Cn.isPullback.flip
    simpa only [← show wn = Cn.toStage from rfl, htm, htn] using hRn
  have hsnEtale : Etale (Q.map sn) :=
    (etale_iff_pullback_of_isPullback ((IsPullback.of_hasPullback sm Cn.toChart).map Q)).mpr hsChart
  have htnEtale : Etale (Q.map tn) :=
    (etale_iff_pullback_of_isPullback (htnSquare.map Q)).mpr htChart
  have hRnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rn
  have hWnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wn
  have hRnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rn :=
    isFinitePresentation_of_isPullback B S hS hRnAlg hRmAlg (hD n.left) (hD m) hRn hRmFp
  have hWnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wn :=
    isFinitePresentation_of_isPullback B S hS hWnAlg hWmAlg (hD n.left) (hD m)
      Cn.isPullback.flip hWmFp
  let awn : W.obj ⟶ Wn := yoneda.preimage (Cn.isPullback.flip.lift (yoneda.map awm)
    (pW ≫ limit.π D n.left) (by rw [Category.assoc, limit.w]; exact hWlim.w))
  let arn : K.R ⟶ Rn := yoneda.preimage (hRn.lift (yoneda.map arm)
    (pR ≫ limit.π D n.left) (by rw [Category.assoc, limit.w]; exact hRlim.w))
  have hWnlim : IsPullback (yoneda.map awn) pW wn (limit.π D n.left) := by
    have hh : IsPullback (yoneda.map awm) pW wm (limit.π D n.left ≫ D.map n.hom) := by
      rw [limit.w]
      exact hWlim
    simpa only [awn, yoneda.map_preimage] using hh.of_right' Cn.isPullback.flip
  have hRnlim : IsPullback (yoneda.map arn) pR rn (limit.π D n.left) := by
    have hh : IsPullback (yoneda.map arm) pR rm (limit.π D n.left ≫ D.map n.hom) := by
      rw [limit.w]
      exact hRlim
    simpa only [arn, yoneda.map_preimage] using hh.of_right' hRn
  have hArnBr : yoneda.map arn ≫ yoneda.map br = yoneda.map arm := by simp [arn]
  have hAwnBw : yoneda.map awn ≫ yoneda.map Cn.toChart = yoneda.map awm := by simp [awn]
  have hsnCompat : arn ≫ sn = K.s ≫ awn := by
    apply yoneda.map_injective
    apply Cn.isPullback.hom_ext
    · simp only [Functor.map_comp, Category.assoc]
      show yoneda.map arn ≫ rn = yoneda.map K.s ≫ yoneda.map awn ≫ wn
      rw [hRnlim.w, hWnlim.w, ← Category.assoc, ht]
    · simp only [Functor.map_comp, Category.assoc]
      have hsn : sn ≫ Cn.toChart = br ≫ sm := pullback.condition.symm
      rw [← yoneda.map_comp sn Cn.toChart, hsn, yoneda.map_comp,
        ← Category.assoc, hArnBr, hAwnBw]
      exact congrArg yoneda.map hsmCompat
  have htnCompat : arn ≫ tn = K.t ≫ awn := by
    apply yoneda.map_injective
    apply Cn.isPullback.hom_ext
    · simp only [Functor.map_comp, Category.assoc]
      show yoneda.map arn ≫ yoneda.map tn ≫ wn =
        yoneda.map K.t ≫ yoneda.map awn ≫ wn
      rw [htn, hRnlim.w, hWnlim.w, ← Category.assoc, hs]
    · simp only [Functor.map_comp, Category.assoc]
      rw [← yoneda.map_comp tn Cn.toChart, ← htnBr, yoneda.map_comp,
        ← Category.assoc, hArnBr, hAwnBw]
      exact congrArg yoneda.map htmCompat
  have hsnSquare : IsPullback arn K.s sn awn := by
    apply IsPullback.of_map yoneda hsnCompat
    apply IsPullback.of_bot _ (by simpa only [Functor.map_comp] using congrArg yoneda.map hsnCompat)
      hWnlim
    simpa only [ht] using hRnlim
  have htnLimitSquare : IsPullback arn K.t tn awn := by
    apply IsPullback.of_map yoneda htnCompat
    apply IsPullback.of_bot _ (by simpa only [Functor.map_comp] using congrArg yoneda.map htnCompat)
      hWnlim
    simpa only [htn, hs] using hRnlim
  have hRnlim' : IsPullback (yoneda.map arn) (yoneda.map K.s ≫ w ≫ Y.hom)
      (yoneda.map sn ≫ wn) (limit.π D n.left) := by
    rw [show (yoneda.map K.s ≫ w ≫ Y.hom) = pR from by rw [← hw]; exact ht]
    exact hRnlim
  exact exists_model_of_stage_relation B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    n.left hX Y hY w hws hwe K.s K.t K.kernelPair
    (show IsAffine (Q.obj Wn) from Cn.U.property) wn sn tn htn hsnEtale htnEtale
    hWnFp hRnFp awn arn (by rw [← hw]; exact hWnlim) hRnlim' hsnCompat htnCompat



/-! ### The cofinality-free form, for systems with uniformly bounded base changes

The three statements above ask the index category to have fewer objects, and morphism types of
fewer elements, than the cofinality of the site's size cutoff. The cutoff is only a strong limit
cardinal, so that cofinality can be smaller than the number of affine étale neighbourhoods of a
point of an affine scheme in the site; the forms below trade it for fewer objects than the cutoff
itself, morphism types bounded by one cardinal below the cutoff, and
`AlgebraicGeometry.Space.BaseChangeSizeBounded`, as do the cofinality-free forms of Stacks 07SF in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineLimitExistence.lean`. The arguments are those above:
the cardinality hypotheses enter only through the affineness of the projections from the limit and
through the limits of the systems of affine charts at the stages, each of which is a base change
of the system and so bounded by the cardinal that hypothesis provides. -/

section BaseChangeSizeBounded

omit hSize hHomSize

variable {ν : Cardinal.{u}} (hSizeB : Cardinal.mk I < B.cutoff) (hν : ν < B.cutoff)
    (hHomSizeB : ∀ i j : I, Cardinal.mk (i ⟶ j) ≤ ν)
    (hB : AlgebraicGeometry.Space.BaseChangeSizeBounded B S hS D)

omit hD hQc hQs in
include hSizeB hν hHomSizeB hB in
/-- **Every projection from the limit is affine, for a system with uniformly bounded base
changes.** This is `AlgebraicGeometry.Space.isAffineHom_limitπ` with the cofinality bounds on the
index category traded for bounds by the cutoff itself together with
`AlgebraicGeometry.Space.BaseChangeSizeBounded`: the representing objects of the base changes of
the stages along a test morphism are bounded by one cardinal below the cutoff, which is what the
cofinality-free existence of their limit in the site asks for. -/
public theorem isAffineHom_limitπ_of_baseChangeSizeBounded (i : I) :
    AlgebraicGeometry.Space.IsAffineHom B S hS (limit.π D i) := by
  intro Z g
  set E := (Over.post (X := i) D ⋙ Over.pullback g) ⋙
    Over.forget (yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj Z)) with hE
  have hbase := AlgebraicGeometry.Space.isLimitPullbackLimitOverPost B S hS D i g
  have hess : ∀ k : Over i,
      (AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙ yoneda).essImage (E.obj k) := by
    intro k
    obtain ⟨A, p, q, hpb⟩ := hAffine k.hom Z g
    exact ⟨A, ⟨hpb.isoPullback⟩⟩
  set F := AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙ yoneda with hF
  set W := Functor.essImage.liftFunctor E F hess with hW
  have hiso : W ⋙ F ≅ E := Functor.essImage.liftFunctorCompIso E F hess
  set W' := W ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS with hW'
  have hWaff : ∀ k : Over i,
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (W'.obj k)) :=
    fun k => (W.obj k).property
  have hJ : Cardinal.mk (Over i) < B.cutoff :=
    AlgebraicGeometry.mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hSizeB hν hHomSizeB i
  obtain ⟨μ, hμ, hbound⟩ := hB i ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj Z) g
  have hstage : ∀ k : Over i,
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (W'.obj k)).size ≤ μ := by
    intro k
    obtain ⟨A, p, q, hpb⟩ := hAffine k.hom Z g
    have e : yoneda.obj (W'.obj k) ≅
        yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj A) :=
      hiso.app k ≪≫ (show E.obj k ≅ _ from hpb.isoPullback.symm)
    rw [Scheme.size_congr
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapIso (yoneda.preimageIso e))]
    exact hbound k _ p (yoneda.map q) hpb
  have hlim : HasLimit W' :=
    AlgebraicGeometry.BigFppfOver.hasLimit_of_isAffine_of_size_le W' hWaff hJ hμ hstage
  have hLaff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (limit W')) :=
    AlgebraicGeometry.BigFppfOver.isAffine_toScheme_of_isLimit_of_size_le W' hWaff hJ hμ hstage
      (limit.isLimit W')
  have hyoneda : IsLimit ((Cone.postcompose hiso.hom).obj
      (yoneda.mapCone (limit.cone W'))) :=
    (IsLimit.postcomposeHomEquiv hiso (yoneda.mapCone (limit.cone W'))).symm
      (isLimitOfPreserves yoneda (limit.isLimit W'))
  have e : yoneda.obj (limit W') ≅ pullback (limit.π D i) g :=
    hyoneda.conePointUniqueUpToIso hbase
  refine ⟨⟨limit W', hLaff⟩, e.hom ≫ pullback.fst _ _,
    yoneda.preimage (e.hom ≫ pullback.snd _ _), ?_⟩
  exact IsPullback.of_iso_pullback ⟨by rw [Functor.map_preimage]; simp [pullback.condition]⟩
    e rfl (by rw [Functor.map_preimage])

omit hD hAffine hQc hQs in
include hSizeB hν hHomSizeB hB in
/-- The underlying scheme functor preserves the limit of a cofiltered system of affine objects of
the site indexed by the slice over a stage, each of which is the base change of the corresponding
later stage of `D` along one fixed affine scheme-valued point of that stage: the bound attached to
that point by `AlgebraicGeometry.Space.BaseChangeSizeBounded` bounds all of them. -/
private noncomputable def isLimit_toScheme_of_affine_of_bounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (E : Over i₀ ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j)))
    (hpb : ∀ j : Over i₀, ∃ (p : yoneda.obj (E.obj j) ⟶ D.obj j.left)
      (q : yoneda.obj (E.obj j) ⟶
        yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)),
      IsPullback p q (D.map j.hom) q₀)
    (c : Cone E) (hc : IsLimit c) :
    IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c) :=
  have hμ := (hB i₀ _ q₀).choose_spec
  have : PreservesLimit E (AlgebraicGeometry.BigFppfOver.toScheme B S hS) :=
    AlgebraicGeometry.BigFppfOver.preservesLimit_toScheme_of_size_le E hE
      (AlgebraicGeometry.mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hSizeB hν hHomSizeB i₀)
      hμ.1 (fun j => by
        obtain ⟨p, q, h⟩ := hpb j
        exact hμ.2 j _ p q h)
  isLimitOfPreserves _ hc

include hSizeB hν hHomSizeB hB


private theorem affineStageChartMap_toStage_of_baseChangeSizeBounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    yoneda.map (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
        (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toStage =
      (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toStage ≫ D.map e.left := by
  simp [affineStageChartMap]

private theorem affineStageChartMap_toChart_of_baseChangeSizeBounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    yoneda.map (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toChart =
      yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart := by
  simp [affineStageChartMap]


private noncomputable def affineStageChartOverDiagramOfSizeBounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) :
    Over i₀ ⥤ Over ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) where
  obj j := Over.mk (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart
  map e := Over.homMk (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) (by
    apply yoneda.map_injective
    simpa only [yoneda.map_comp, Over.mk_left, Over.mk_hom] using
      affineStageChartMap_toChart_of_baseChangeSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
          hν hHomSizeB hB
        i₀ U₀ q₀ hAff e)
  map_id j := by
    apply Over.OverMorphism.ext
    apply yoneda.map_injective
    apply (affineStageChart B S hS D i₀ U₀ q₀ hAff j).isPullback.hom_ext
    · simp [affineStageChartMap]
    · simp [affineStageChartMap]
  map_comp {j k l} e f := by
    apply Over.OverMorphism.ext
    apply yoneda.map_injective
    apply (affineStageChart B S hS D i₀ U₀ q₀ hAff l).isPullback.hom_ext
    · simp [affineStageChartMap, Category.assoc]
    · simp [affineStageChartMap, Category.assoc]

private noncomputable def affineStageChartConeOfSizeBounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) :
    Cone (affineStageChartOverDiagramOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
        hν hHomSizeB hB
      i₀ U₀ q₀ hAff) where
  pt := Over.mk q
  π := {
    app j := Over.homMk (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) (by
      apply yoneda.map_injective
      change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
          yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart = yoneda.map q
      simp [affineStageChartLift])
    naturality j k e := by
      simp only [Functor.const_obj_map]
      apply Over.OverMorphism.ext
      apply yoneda.map_injective
      apply (affineStageChart B S hS D i₀ U₀ q₀ hAff k).isPullback.hom_ext
      · change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h k) ≫
              (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toStage =
            yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j ≫
                affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
              (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toStage
        simp [affineStageChartLift, affineStageChartMap, Category.assoc, limit.w]
      · change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h k) ≫
              yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toChart =
            yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j ≫
                affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
              yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toChart
        simp [affineStageChartLift, affineStageChartMap, Category.assoc]
  }

private noncomputable def affineStageChartConeIsLimitOfSizeBounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) :
    IsLimit (affineStageChartConeOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB
      i₀ U₀ q₀ hAff U p q h) := by
  let E := affineStageChartOverDiagramOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
      hν hHomSizeB hB
    i₀ U₀ q₀ hAff
  let c := affineStageChartConeOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB
    i₀ U₀ q₀ hAff U p q h
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  apply isLimitOfReflects (Over.forget T)
  apply isLimitOfReflects yoneda
  let p' : (E ⋙ Over.forget T) ⋙ yoneda ⟶ Over.forget i₀ ⋙ D := {
    app j := (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toStage
    naturality j k e :=
      affineStageChartMap_toStage_of_baseChangeSizeBounded B S hS hZ D hD hAffine hQc hQs
          hSizeB hν hHomSizeB hB
        i₀ U₀ q₀ hAff e
  }
  let q' : (E ⋙ Over.forget T) ⋙ yoneda ⟶ (Functor.const _).obj (yoneda.obj T) := {
    app j := yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart
    naturality j k e := by
      simpa [E, T, affineStageChartOverDiagramOfSizeBounded] using
        (affineStageChartMap_toChart_of_baseChangeSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
            hν hHomSizeB hB
          i₀ U₀ q₀ hAff e)
  }
  exact isLimit_of_cartesian_cone D i₀ (yoneda.obj T) q₀ _ _ p' q'
    (fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAff j).isPullback)
    p (yoneda.map q) h
    (fun j => by
      change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
          (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toStage = p ≫ limit.π D j.left
      simp [affineStageChartLift])
    (fun j => by
      change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
          yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart = yoneda.map q
      simp [affineStageChartLift])

private theorem eventually_eq_on_affine_chart_of_baseChangeSizeBounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i₀)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ Z)
    (hf : f ≫ a = q₀) (hg : g ≫ a = q₀)
    (hfg : pullback.snd (limit.π D i₀) q₀ ≫ f =
      pullback.snd (limit.π D i₀) q₀ ≫ g) :
    ∃ j : Over i₀,
      yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ f =
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ g := by
  obtain ⟨U, p, q, h⟩ :=
    isAffineHom_limitπ_of_baseChangeSizeBounded B S hS D hAffine hSizeB hν hHomSizeB hB i₀ U₀ q₀
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let E := affineStageChartOverDiagramOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
      hν hHomSizeB hB
    i₀ U₀ q₀ hAffine
  let c := affineStageChartConeOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB
    i₀ U₀ q₀ hAffine _ p q h
  let hc := affineStageChartConeIsLimitOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
      hν hHomSizeB hB
    i₀ U₀ q₀ hAffine _ p q h
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
    fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.property
  have hh : yoneda.map q ≫ f = yoneda.map q ≫ g := by
    simpa using congrArg (fun k => h.isoPullback.hom ≫ k) hfg
  exact eventually_eq_homs_of_locallyOfFinitePresentation B S hS hZalg (hD i₀)
    a ha T q₀ E c
    (isLimit_toScheme_of_affine_of_bounded B S hS D hSizeB hν hHomSizeB hB i₀ U₀ q₀
      (E ⋙ Over.forget T) hE (fun j =>
          ⟨_, _, (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback⟩)
              ((Over.forget T).mapCone c)
      (isLimitOfPreserves (Over.forget T) hc))
    hE U.property f g hf hg hh

private theorem exists_hom_on_affine_chart_of_baseChangeSizeBounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj U₀.obj ⟶ D.obj i₀)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i₀)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f : pullback (limit.π D i₀) q₀ ⟶ Z)
    (hf : f ≫ a = pullback.fst _ _ ≫ limit.π D i₀) :
    ∃ (j : Over i₀) (g : yoneda.obj
      (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.obj ⟶ Z),
      g ≫ a = (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toStage ≫ D.map j.hom ∧
      (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.lift
        (pullback.fst _ _ ≫ limit.π D j.left) (pullback.snd _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition) ≫ g = f := by
  obtain ⟨U, p, q, h⟩ :=
    isAffineHom_limitπ_of_baseChangeSizeBounded B S hS D hAffine hSizeB hν hHomSizeB hB i₀ U₀ q₀
  let E := affineStageChartOverDiagramOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
      hν hHomSizeB hB
    i₀ U₀ q₀ hAffine
  let c := affineStageChartConeOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB
    i₀ U₀ q₀ hAffine _ p q h
  let hc := affineStageChartConeIsLimitOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
      hν hHomSizeB hB
    i₀ U₀ q₀ hAffine _ p q h
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
    fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.property
  obtain ⟨j, g, hg, he⟩ := exists_hom_of_locallyOfFinitePresentation B S hS hZalg
    (hD i₀) a ha U₀.obj q₀ E c
    (isLimit_toScheme_of_affine_of_bounded B S hS D hSizeB hν hHomSizeB hB i₀ U₀ q₀
      (E ⋙ Over.forget U₀.obj) hE (fun j =>
          ⟨_, _, (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback⟩)
              ((Over.forget U₀.obj).mapCone c)
      (isLimitOfPreserves (Over.forget U₀.obj) hc))
    hE U.property (h.isoPullback.hom ≫ f) (by
      show (h.isoPullback.hom ≫ f) ≫ a = yoneda.map q ≫ q₀
      rw [Category.assoc, hf, IsPullback.isoPullback_hom_fst_assoc]
      exact h.w)
  refine ⟨j, g, hg.trans (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.w.symm, ?_⟩
  apply (Iso.cancel_iso_hom_left h.isoPullback _ _).mp
  have hh : h.isoPullback.hom ≫
      (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.lift
        (pullback.fst _ _ ≫ limit.π D j.left) (pullback.snd _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition) =
      yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAffine _ p q h j) := by
    apply (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.hom_ext
    · simp [affineStageChartLift]
    · simp [affineStageChartLift]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ g) hh).trans he)

private theorem eventually_eq_on_affine_chart_over_of_baseChangeSizeBounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    {G Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (b : D.obj i₀ ⟶ G)
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ Z)
    (hf : f ≫ a = q₀ ≫ b) (hg : g ≫ a = q₀ ≫ b)
    (hfg : pullback.snd (limit.π D i₀) q₀ ≫ f =
      pullback.snd (limit.π D i₀) q₀ ≫ g) :
    ∃ j : Over i₀,
      yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ f =
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ g := by
  obtain ⟨U, p, q, h⟩ :=
    isAffineHom_limitπ_of_baseChangeSizeBounded B S hS D hAffine hSizeB hν hHomSizeB hB i₀ U₀ q₀
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let E := affineStageChartOverDiagramOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
      hν hHomSizeB hB
    i₀ U₀ q₀ hAffine
  let c := affineStageChartConeOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB
    i₀ U₀ q₀ hAffine _ p q h
  let hc := affineStageChartConeIsLimitOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
      hν hHomSizeB hB
    i₀ U₀ q₀ hAffine _ p q h
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
    fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.property
  have hh : yoneda.map q ≫ f = yoneda.map q ≫ g := by
    simpa using congrArg (fun k => h.isoPullback.hom ≫ k) hfg
  exact eventually_eq_homs_of_locallyOfFinitePresentation B S hS hZalg hG
    a ha T (q₀ ≫ b) E c
    (isLimit_toScheme_of_affine_of_bounded B S hS D hSizeB hν hHomSizeB hB i₀ U₀ q₀
      (E ⋙ Over.forget T) hE (fun j =>
          ⟨_, _, (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback⟩)
              ((Over.forget T).mapCone c)
      (isLimitOfPreserves (Over.forget T) hc))
    hE U.property f g hf hg hh

private noncomputable def affineStageChartDiagramOfSizeBounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) :
    Over i₀ ⥤ Scheme.{u} := {
  obj j := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
    ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
      (affineStageChart B S hS D i₀ U₀ q₀ hAff j).U)
  map e := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
    (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e)
  map_id j := by
    let Cj := affineStageChart B S hS D i₀ U₀ q₀ hAff j
    have hsrc : affineStageChartMap B S hS D i₀ U₀ q₀ hAff (𝟙 j) = 𝟙 _ := by
      apply yoneda.map_injective
      apply Cj.isPullback.hom_ext
      · simp [affineStageChartMap, Cj]
      · simp [affineStageChartMap, Cj]
    simpa using congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS |>.map) hsrc
  map_comp {j k l} e f := by
    let Cj := affineStageChart B S hS D i₀ U₀ q₀ hAff j
    let Ck := affineStageChart B S hS D i₀ U₀ q₀ hAff k
    let Cl := affineStageChart B S hS D i₀ U₀ q₀ hAff l
    have hsrc : affineStageChartMap B S hS D i₀ U₀ q₀ hAff (e ≫ f) =
        affineStageChartMap B S hS D i₀ U₀ q₀ hAff e ≫
          affineStageChartMap B S hS D i₀ U₀ q₀ hAff f := by
      apply yoneda.map_injective
      apply Cl.isPullback.hom_ext
      · rw [affineStageChartMap_toStage_of_baseChangeSizeBounded B S hS hZ D hD hAffine hQc hQs
          hSizeB hν hHomSizeB hB
          i₀ U₀ q₀ hAff (e ≫ f)]
        rw [yoneda.map_comp, Category.assoc]
        rw [affineStageChartMap_toStage_of_baseChangeSizeBounded B S hS hZ D hD hAffine hQc hQs
            hSizeB hν hHomSizeB hB
          i₀ U₀ q₀ hAff f]
        rw [← Category.assoc,
          affineStageChartMap_toStage_of_baseChangeSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
              hν hHomSizeB hB
            i₀ U₀ q₀ hAff e]
        rw [Category.assoc, ← D.map_comp]
        simp only [Over.comp_left]
      · rw [affineStageChartMap_toChart_of_baseChangeSizeBounded B S hS hZ D hD hAffine hQc hQs
          hSizeB hν hHomSizeB hB
          i₀ U₀ q₀ hAff (e ≫ f)]
        rw [yoneda.map_comp, Category.assoc]
        rw [affineStageChartMap_toChart_of_baseChangeSizeBounded B S hS hZ D hD hAffine hQc hQs
            hSizeB hν hHomSizeB hB
          i₀ U₀ q₀ hAff f]
        exact (affineStageChartMap_toChart_of_baseChangeSizeBounded B S hS hZ D hD hAffine hQc hQs
            hSizeB hν hHomSizeB hB
          i₀ U₀ q₀ hAff e).symm
    simpa [Functor.map_comp] using congrArg
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS |>.map) hsrc
}

private theorem affineStageChartDiagram_map_isAffineHom_of_baseChangeSizeBounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    _root_.AlgebraicGeometry.IsAffineHom
        ((affineStageChartDiagramOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB
      i₀ U₀ q₀ hAff).map e) := by
  let Cj := affineStageChart B S hS D i₀ U₀ q₀ hAff j
  let Ck := affineStageChart B S hS D i₀ U₀ q₀ hAff k
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj Cj.U)) := Cj.U.property
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj Ck.U)) := Ck.U.property
  show _root_.AlgebraicGeometry.IsAffineHom ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
    (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e))
  exact AlgebraicGeometry.isAffineHom_of_isAffine _

private theorem affineStageChartDiagram_obj_isAffine_of_baseChangeSizeBounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) (j : Over i₀) :
    IsAffine ((affineStageChartDiagramOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
        hν hHomSizeB hB
      i₀ U₀ q₀ hAff).obj j) := by
  show IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
    ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
      (affineStageChart B S hS D i₀ U₀ q₀ hAff j).U))
  exact (affineStageChart B S hS D i₀ U₀ q₀ hAff j).U.property

private theorem affineStageChartDiagram_obj_compact_of_baseChangeSizeBounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) (j : Over i₀) :
    CompactSpace ((affineStageChartDiagramOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
        hν hHomSizeB hB
      i₀ U₀ q₀ hAff).obj j) := by
  let := affineStageChartDiagram_obj_isAffine_of_baseChangeSizeBounded B S hS hZ D hD hAffine hQc
      hQs hSizeB hν hHomSizeB hB
    i₀ U₀ q₀ hAff j
  infer_instance

private theorem affineStageChartDiagram_obj_quasiSeparated_of_baseChangeSizeBounded (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) (j : Over i₀) :
    QuasiSeparatedSpace ((affineStageChartDiagramOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
        hν hHomSizeB hB
      i₀ U₀ q₀ hAff).obj j) := by
  let := affineStageChartDiagram_obj_isAffine_of_baseChangeSizeBounded B S hS hZ D hD hAffine hQc
      hQs hSizeB hν hHomSizeB hB
    i₀ U₀ q₀ hAff j
  infer_instance

private theorem exists_model_over_affine_chart_of_baseChangeSizeBounded (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) :
    let c := affineStageChartConeOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB
      i U₀ p₀ hAffine U.obj p q hp
    ∃ (j : Over i) (Wj : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (affineStageChart B S hS D i U₀ p₀ hAffine j).U.obj)),
      AlgebraicGeometry.FinitePresentation Wj.hom ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
        (Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
            (c.π.app j).left)).obj Wj) := by
  dsimp only
  let E := affineStageChartOverDiagramOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
      hν hHomSizeB hB
    i U₀ p₀ hAffine
  let c := affineStageChartConeOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB
    i U₀ p₀ hAffine U.obj p q hp
  let hc := affineStageChartConeIsLimitOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
      hν hHomSizeB hB
    i U₀ p₀ hAffine U.obj p q hp
  let : IsConnected (Over i) := IsCofiltered.isConnected _
  let F := E ⋙ Over.forget U₀.obj
  let G := F ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hF : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (F.obj j)) :=
    fun j => (affineStageChart B S hS D i U₀ p₀ hAffine j).U.property
  let : ∀ j, IsAffine (G.obj j) := hF
  let : ∀ {j k : Over i} (e : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (G.map e) :=
      fun {_ _} _ => inferInstance
  let : ∀ j : Over i, CompactSpace (G.obj j) := fun _ => inferInstance
  let : ∀ j : Over i, QuasiSeparatedSpace (G.obj j) := fun _ => inferInstance
  let sc := (Over.forget U₀.obj ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c
  have hsc : IsLimit sc := isLimit_toScheme_of_affine_of_bounded B S hS D hSizeB hν
      hHomSizeB hB i U₀ p₀
      F hF (fun j => ⟨_, _, (affineStageChart B S hS D i U₀ p₀ hAffine j).isPullback⟩)
          ((Over.forget U₀.obj).mapCone c)
    (isLimitOfPreserves (Over.forget U₀.obj) hc)
  exact scheme_model_of_finitePresentation G sc hsc
    (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) hg

private theorem exists_affine_model_over_affine_chart_of_baseChangeSizeBounded (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g))
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)] :
    let c := affineStageChartConeOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB
      i U₀ p₀ hAffine U.obj p q hp
    ∃ (j : Over i) (Wj : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (affineStageChart B S hS D i U₀ p₀ hAffine j).U.obj)),
      AlgebraicGeometry.FinitePresentation Wj.hom ∧ IsAffine Wj.left ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
        (Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
            (c.π.app j).left)).obj Wj) := by
  dsimp only
  let E := affineStageChartOverDiagramOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
      hν hHomSizeB hB
    i U₀ p₀ hAffine
  let c := affineStageChartConeOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB
    i U₀ p₀ hAffine U.obj p q hp
  let hc := affineStageChartConeIsLimitOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
      hν hHomSizeB hB
    i U₀ p₀ hAffine U.obj p q hp
  let : IsConnected (Over i) := IsCofiltered.isConnected _
  let F := E ⋙ Over.forget U₀.obj
  let G := F ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hF : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (F.obj j)) :=
    fun j => (affineStageChart B S hS D i U₀ p₀ hAffine j).U.property
  let : ∀ j, IsAffine (G.obj j) := hF
  let : ∀ {j k : Over i} (e : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (G.map e) :=
      fun {_ _} _ => inferInstance
  let : ∀ j : Over i, CompactSpace (G.obj j) := fun _ => inferInstance
  let : ∀ j : Over i, QuasiSeparatedSpace (G.obj j) := fun _ => inferInstance
  let sc := (Over.forget U₀.obj ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c
  have hsc : IsLimit sc := isLimit_toScheme_of_affine_of_bounded B S hS D hSizeB hν
      hHomSizeB hB i U₀ p₀
      F hF (fun j => ⟨_, _, (affineStageChart B S hS D i U₀ p₀ hAffine j).isPullback⟩)
          ((Over.forget U₀.obj).mapCone c)
    (isLimitOfPreserves (Over.forget U₀.obj) hc)
  exact scheme_affine_model_of_finitePresentation G sc hsc
    (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) hg
    ‹IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)›

private theorem exists_site_model_over_affine_chart_of_baseChangeSizeBounded (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (hp₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p₀)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) :
    ∃ (j : Over i) (V : AlgebraicGeometry.BigFppfOver B S hS)
      (v : yoneda.obj V ⟶ D.obj j.left) (a : W ⟶ V),
      AlgebraicGeometry.Space.IsFinitePresentation B S hS v ∧
      IsPullback (yoneda.map a) (yoneda.map g ≫ p) v (limit.π D j.left) := by
  let c := affineStageChartConeOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB
    i U₀ p₀ hAffine U.obj p q hp
  obtain ⟨j, V₀, hV₀, ⟨e⟩⟩ := exists_model_over_affine_chart_of_baseChangeSizeBounded B S hS
      hZ D hD hAffine
    hQc hQs hSizeB hν hHomSizeB hB i U₀ p₀ U p q hp W g hg
  let Cj := affineStageChart B S hS D i U₀ p₀ hAffine j
  let b : U.obj ⟶ Cj.U.obj := (c.π.app j).left
  obtain ⟨V, f, a, hf, _, ha⟩ := exists_site_pullback_model B S hS b g V₀ hV₀ e
  have hbp : yoneda.map b ≫ Cj.toStage = p ≫ limit.π D j.left := by
    show yoneda.map (affineStageChartLift B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        (affineStageChart B S hS D i U₀ p₀ hAffine j).toStage = p ≫ limit.π D j.left
    simp [affineStageChartLift]
  have hbq : yoneda.map b ≫ yoneda.map Cj.toChart = yoneda.map q := by
    show yoneda.map (affineStageChartLift B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        yoneda.map (affineStageChart B S hS D i U₀ p₀ hAffine j).toChart = yoneda.map q
    simp [affineStageChartLift]
  have hU : IsPullback (yoneda.map b) p Cj.toStage (limit.π D j.left) := by
    apply IsPullback.of_right (h₂₂ := D.map j.hom) _ hbp Cj.isPullback.flip
    rw [hbq, limit.w]
    exact hp.flip
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (etaleInverseImageIsStableUnderComposition _)
  have hpc : P.presheaf Cj.toStage := P.presheaf.of_isPullback Cj.isPullback.flip hp₀
  let : IsAffine (Q.obj Cj.U.obj) := Cj.U.property
  let : LocallyOfFinitePresentation (Q.map f) := hf.1
  let : QuasiCompact (Q.map f) := hf.2.1
  let : QuasiSeparated (Q.map f) := hf.2.2
  have hVqc : CompactSpace (Q.obj V) := QuasiCompact.compactSpace_of_compactSpace (Q.map f)
  have hVqs : QuasiSeparatedSpace (Q.obj V) :=
    quasiSeparatedSpace_of_quasiSeparated (Q.map f)
  refine ⟨j, V, yoneda.map f ≫ Cj.toStage, a,
    isFinitePresentation_of_scheme_chart B S hS hZ (hD j.left) (hQs j.left)
      V Cj.U.obj hVqc hVqs f Cj.toStage hpc hf.1, ?_⟩
  exact (ha.map yoneda).paste_vert hU

private theorem exists_affine_site_model_over_affine_chart_of_baseChangeSizeBounded (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (hp₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p₀)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g))
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)] :
    ∃ (j : Over i) (V : AlgebraicGeometry.BigFppfOver B S hS)
      (v : yoneda.obj V ⟶ D.obj j.left) (a : W ⟶ V),
      AlgebraicGeometry.Space.IsFinitePresentation B S hS v ∧
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V) ∧
      IsPullback (yoneda.map a) (yoneda.map g ≫ p) v (limit.π D j.left) := by
  let c := affineStageChartConeOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB
    i U₀ p₀ hAffine U.obj p q hp
  obtain ⟨j, V₀, hV₀, hV₀aff, ⟨e⟩⟩ := exists_affine_model_over_affine_chart_of_baseChangeSizeBounded
      B S hS hZ D hD hAffine
    hQc hQs hSizeB hν hHomSizeB hB i U₀ p₀ U p q hp W g hg
  let Cj := affineStageChart B S hS D i U₀ p₀ hAffine j
  let b : U.obj ⟶ Cj.U.obj := (c.π.app j).left
  obtain ⟨V, f, a, hf, ⟨eV⟩, ha⟩ := exists_site_pullback_model B S hS b g V₀ hV₀ e
  have hbp : yoneda.map b ≫ Cj.toStage = p ≫ limit.π D j.left := by
    show yoneda.map (affineStageChartLift B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        (affineStageChart B S hS D i U₀ p₀ hAffine j).toStage = p ≫ limit.π D j.left
    simp [affineStageChartLift]
  have hbq : yoneda.map b ≫ yoneda.map Cj.toChart = yoneda.map q := by
    show yoneda.map (affineStageChartLift B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        yoneda.map (affineStageChart B S hS D i U₀ p₀ hAffine j).toChart = yoneda.map q
    simp [affineStageChartLift]
  have hU : IsPullback (yoneda.map b) p Cj.toStage (limit.π D j.left) := by
    apply IsPullback.of_right (h₂₂ := D.map j.hom) _ hbp Cj.isPullback.flip
    rw [hbq, limit.w]
    exact hp.flip
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (etaleInverseImageIsStableUnderComposition _)
  have hpc : P.presheaf Cj.toStage := P.presheaf.of_isPullback Cj.isPullback.flip hp₀
  let : IsAffine (Q.obj Cj.U.obj) := Cj.U.property
  let : LocallyOfFinitePresentation (Q.map f) := hf.1
  let : QuasiCompact (Q.map f) := hf.2.1
  let : QuasiSeparated (Q.map f) := hf.2.2
  have hVqc : CompactSpace (Q.obj V) := QuasiCompact.compactSpace_of_compactSpace (Q.map f)
  have hVqs : QuasiSeparatedSpace (Q.obj V) :=
    quasiSeparatedSpace_of_quasiSeparated (Q.map f)
  refine ⟨j, V, yoneda.map f ≫ Cj.toStage, a,
    isFinitePresentation_of_scheme_chart B S hS hZ (hD j.left) (hQs j.left)
      V Cj.U.obj hVqc hVqs f Cj.toStage hpc hf.1, ?_, ?_⟩
  · let : IsAffine V₀.left := hV₀aff
    let : IsIso eV.hom.left :=
      inferInstanceAs (IsIso ((Over.forget ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
        Cj.U.obj)).map eV.hom))
    exact IsAffine.of_isIso eV.hom.left
  · exact (ha.map yoneda).paste_vert hU

private theorem eventually_etale_over_affine_chart_of_baseChangeSizeBounded (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (X : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀.obj))
    (hX : AlgebraicGeometry.FinitePresentation X.hom)
    [Etale ((Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)).obj X).hom] :
    ∃ j : Over i, Etale ((Over.pullback
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (affineStageChart B S hS D i U₀ p₀ hAffine j).toChart)).obj X).hom := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let E := affineStageChartOverDiagramOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
      hν hHomSizeB hB
    i U₀ p₀ hAffine
  let c := affineStageChartConeOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB
    i U₀ p₀ hAffine U.obj p q hp
  let hc := affineStageChartConeIsLimitOfSizeBounded B S hS hZ D hD hAffine hQc hQs hSizeB
      hν hHomSizeB hB
    i U₀ p₀ hAffine U.obj p q hp
  let : IsConnected (Over i) := IsCofiltered.isConnected _
  let F := E ⋙ Over.forget U₀.obj
  let E' := E ⋙ Over.post Q
  let sc := (Over.post Q).mapCone c
  have hF (j : Over i) : IsAffine (Q.obj (F.obj j)) :=
    (affineStageChart B S hS D i U₀ p₀ hAffine j).U.property
  have hsc : IsLimit ((Over.forget (Q.obj U₀.obj)).mapCone sc) :=
    isLimit_toScheme_of_affine_of_bounded B S hS D hSizeB hν hHomSizeB hB i U₀ p₀
      F hF (fun j => ⟨_, _, (affineStageChart B S hS D i U₀ p₀ hAffine j).isPullback⟩)
          ((Over.forget U₀.obj).mapCone c) (isLimitOfPreserves (Over.forget U₀.obj) hc)
  let : ∀ j, IsAffine (E'.obj j).left := hF
  let : ∀ {j k : Over i} (a : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (E'.map a).left := by
    intro j k a
    infer_instance
  let : Etale ((Over.pullback sc.pt.hom).obj X).hom :=
    ‹Etale ((Over.pullback (Q.map q)).obj X).hom›
  exact scheme_eventually_etale_pullback E' sc hsc X hX

private theorem eventually_eq_on_quasiCompact_source_of_baseChangeSizeBounded (i : I)
    {Y Z G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hYqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS Y)
    (r : Y ⟶ D.obj i) (a : Z ⟶ G) (b : D.obj i ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : Y ⟶ Z) (hf : f ≫ a = r ≫ b) (hg : g ≫ a = r ≫ b)
    (hfg : pullback.fst r (limit.π D i) ≫ f =
      pullback.fst r (limit.π D i) ≫ g) :
    ∃ (j : I) (e : j ⟶ i),
      pullback.fst r (D.map e) ≫ f = pullback.fst r (D.map e) ≫ g := by
  classical
  obtain ⟨U₀, q₀, hU₀, hsurj, het⟩ := exists_affine_etale_atlas B S hS Y hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hh : pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀ ≫ f =
      pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀ ≫ g := by
    let k : pullback (limit.π D i) (q₀ ≫ r) ⟶ pullback r (limit.π D i) :=
      pullback.lift (pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀)
      (pullback.fst (limit.π D i) (q₀ ≫ r))
      (by simp only [Category.assoc, pullback.condition])
    simpa [k] using congrArg (fun t => k ≫ t) hfg
  obtain ⟨j, hj⟩ := eventually_eq_on_affine_chart_over_of_baseChangeSizeBounded B S hS
      hZ D hD hAffine
    hQc hQs hSizeB hν hHomSizeB hB i U (q₀ ≫ r) hG b hZalg a ha
    (q₀ ≫ f) (q₀ ≫ g) (by simp [hf]) (by simp [hg]) hh
  refine ⟨j.left, j.hom, ?_⟩
  let C := affineStageChart B S hS D i U (q₀ ≫ r) hAffine j
  let p : yoneda.obj C.U.obj ⟶ pullback r (D.map j.hom) :=
    pullback.lift (yoneda.map C.toChart ≫ q₀) C.toStage
      (by simpa only [Category.assoc] using C.isPullback.w.symm)
  have hp : IsPullback (yoneda.map C.toChart) p q₀
      (pullback.fst r (D.map j.hom)) := by
    apply IsPullback.of_bot _ (by simp [p]) (IsPullback.of_hasPullback r (D.map j.hom))
    simpa [p] using C.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  apply hom_ext_of_surjective_etale_atlas B S hS
    (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS r (D.map j.hom) hY (hD j.left) (hD i))
    hZalg.isSheaf p
    (P.presheaf.of_isPullback hp hsurj)
    (Q.presheaf.of_isPullback hp (represented_etale_of_isEtale B S hS q₀ het))
  simpa [p, Category.assoc] using hj

private theorem exists_stage_atlas_factorization_of_baseChangeSizeBounded (i : I)
    (Y : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hYqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS Y.left)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f : pullback Y.hom (limit.π D i) ⟶ Z)
    (hf : f ≫ a = pullback.fst Y.hom (limit.π D i) ≫ Y.hom) :
    ∃ (j : Over i) (U : AlgebraicGeometry.BigAffineFppf B S hS)
      (p : yoneda.obj U.obj ⟶ pullback Y.hom (D.map j.hom))
      (g : yoneda.obj U.obj ⟶ Z),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      g ≫ a = p ≫ pullback.snd Y.hom (D.map j.hom) ≫ D.map j.hom ∧
      pullback.fst (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ≫ g =
        pullback.lift
          (pullback.fst (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ≫ p)
          (pullback.snd (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left))
          (by simpa only [Over.pullback_obj_hom, Category.assoc] using
            (pullback.condition (f := p ≫ pullback.snd Y.hom (D.map j.hom))
              (g := limit.π D j.left))) ≫
        (iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
          (limit.w D j.hom) Y).hom.left ≫ f := by
  classical
  obtain ⟨U₀, q₀, hU₀, hs, he⟩ := exists_affine_etale_atlas B S hS Y.left hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  let k : pullback (limit.π D i) (q₀ ≫ Y.hom) ⟶ pullback Y.hom (limit.π D i) :=
    pullback.lift (pullback.snd _ _ ≫ q₀) (pullback.fst _ _)
      (by simp only [Category.assoc, pullback.condition])
  obtain ⟨j, g, hg, hgf⟩ := exists_hom_on_affine_chart_of_baseChangeSizeBounded B S hS
      hZ D hD hAffine
    hQc hQs hSizeB hν hHomSizeB hB i U (q₀ ≫ Y.hom) hZalg a ha (k ≫ f) (by
      rw [Category.assoc, hf]
      simpa [k, Category.assoc] using (pullback.condition (f := limit.π D i)
        (g := q₀ ≫ Y.hom)).symm)
  let C := affineStageChart B S hS D i U (q₀ ≫ Y.hom) hAffine j
  let p : yoneda.obj C.U.obj ⟶ pullback Y.hom (D.map j.hom) :=
    pullback.lift (yoneda.map C.toChart ≫ q₀) C.toStage
      (by simpa only [Category.assoc] using C.isPullback.w.symm)
  have hp : IsPullback (yoneda.map C.toChart) p q₀
      (pullback.fst Y.hom (D.map j.hom)) := by
    apply IsPullback.of_bot _ (by simp [p]) (IsPullback.of_hasPullback Y.hom (D.map j.hom))
    simpa [p] using C.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  refine ⟨j, C.U, p, g, P.presheaf.of_isPullback hp hs,
    Q.presheaf.of_isPullback hp (represented_etale_of_isEtale B S hS q₀ he),
    by simpa [p] using hg, ?_⟩
  let v : pullback (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ⟶
      pullback (limit.π D i) (q₀ ≫ Y.hom) :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ yoneda.map C.toChart) (by
      simp only [Category.assoc]
      rw [← C.isPullback.w, ← limit.w D j.hom]
      simp only [← Category.assoc]
      congr 1
      have hpcomp : p ≫ pullback.snd Y.hom (D.map j.hom) = C.toStage := by simp [p]
      rw [← hpcomp]
      exact pullback.condition.symm)
  let l := C.isPullback.lift
    (pullback.fst (limit.π D i) (q₀ ≫ Y.hom) ≫ limit.π D j.left)
    (pullback.snd (limit.π D i) (q₀ ≫ Y.hom))
    (by rw [Category.assoc, limit.w]; exact pullback.condition)
  have hv : v ≫ l = pullback.fst _ _ := by
    apply C.isPullback.hom_ext
    · simp only [Category.assoc, l, IsPullback.lift_fst, v, pullback.lift_fst_assoc]
      simpa [p, Category.assoc] using
        (pullback.condition (f := p ≫ pullback.snd Y.hom (D.map j.hom))
          (g := limit.π D j.left)).symm
    · simp [l, v]
  conv_lhs => rw [← hv, Category.assoc, hgf]
  simp only [← Category.assoc]
  apply congrArg (fun t => t ≫ f)
  apply pullback.hom_ext
  · simp [v, k, iteratedBaseChangeIso_hom_left, p, Category.assoc]
  · simp [v, k, iteratedBaseChangeIso_hom_left, Category.assoc]

/-- **Fullness, cofinality-free.** A morphism between base changes of finite-presentation
algebraic spaces is defined at a sufficiently late stage, for a system with fewer stages than the
cutoff and uniformly bounded base changes. -/
public theorem exists_morphism_after_baseChange_of_baseChangeSizeBounded
    (i : I) (Yᵢ Zᵢ : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f : (Over.pullback (limit.π D i)).obj Yᵢ ⟶
      (Over.pullback (limit.π D i)).obj Zᵢ) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (D.map e)).obj Yᵢ ⟶
        (Over.pullback (D.map e)).obj Zᵢ)
      (α : (Over.pullback (limit.π D j)).obj
          ((Over.pullback (D.map e)).obj Yᵢ) ≅
        (Over.pullback (limit.π D i)).obj Yᵢ)
      (β : (Over.pullback (limit.π D j)).obj
          ((Over.pullback (D.map e)).obj Zᵢ) ≅
        (Over.pullback (limit.π D i)).obj Zᵢ),
      (α.hom.left ≫ pullback.fst Yᵢ.hom (limit.π D i) =
        pullback.fst ((Over.pullback (D.map e)).obj Yᵢ).hom (limit.π D j) ≫
          pullback.fst Yᵢ.hom (D.map e)) ∧
      (β.hom.left ≫ pullback.fst Zᵢ.hom (limit.π D i) =
        pullback.fst ((Over.pullback (D.map e)).obj Zᵢ).hom (limit.π D j) ≫
          pullback.fst Zᵢ.hom (D.map e)) ∧
      α.hom ≫ f = (Over.pullback (limit.π D j)).map g ≫ β.hom := by
  classical
  have hYqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS Yᵢ.hom
    (hD i) (hQc i) hYfp
  have hYqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS hZ hY (hQs i) hYfp.2.2
  let f₀ := f.left ≫ pullback.fst Zᵢ.hom (limit.π D i)
  have hf₀ : f₀ ≫ Zᵢ.hom = pullback.fst Yᵢ.hom (limit.π D i) ≫ Yᵢ.hom := by
    simp only [f₀, Category.assoc, pullback.condition]
    have hw : f.left ≫ pullback.snd Zᵢ.hom (limit.π D i) =
        pullback.snd Yᵢ.hom (limit.π D i) := f.w
    rw [← Category.assoc, hw]
  obtain ⟨j, U, p, g, hs, he, hg, hgf⟩ := exists_stage_atlas_factorization_of_baseChangeSizeBounded
    B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB i Yᵢ hY hYqc hZ' Zᵢ.hom hZfp.1 f₀ hf₀
  let Yj := (Over.pullback (D.map j.hom)).obj Yᵢ
  have hYj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom (D.map j.hom)
    hY (hD j.left) (hD i)
  have hYjqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_pullback
    B S hS hZ Yᵢ.hom (D.map j.hom) hY (hD j.left) (hD i) hYqs (hQs j.left)
  have hU := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U.obj
  have hUqc := isQuasiCompactSpace_yoneda_of_isAffine B S hS U.obj U.property
  have hR := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS p p hU hU hYj
  have hRqc := AlgebraicGeometry.Space.isQuasiCompactSpace_pullback
    B S hS hZ p p hU hYj hUqc hUqc hYjqs
  have hlim := equalizes_kernelPair_after_baseChange p Yj.hom (limit.π D j.left)
    ((iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
      (limit.w D j.hom) Yᵢ).hom.left ≫ f₀) g hgf
  obtain ⟨k, e, hkg⟩ := eventually_eq_on_quasiCompact_source_of_baseChangeSizeBounded B S hS
      hZ D hD hAffine
    hQc hQs hSizeB hν hHomSizeB hB j.left hR hZ' (hD i) hRqc
    (pullback.fst p p ≫ p ≫ Yj.hom) Zᵢ.hom (D.map j.hom) hZfp.1
    (pullback.fst p p ≫ g) (pullback.snd p p ≫ g)
    (by simpa only [Yj, Over.pullback_obj_hom, Category.assoc] using congrArg
          (fun t => pullback.fst p p ≫ t) hg)
    (by simpa only [Yj, Over.pullback_obj_hom, Category.assoc, pullback.condition_assoc] using
      congrArg (fun t => pullback.snd p p ≫ t) hg) hlim
  let K := affineStageChart B S hS D j.left U (p ≫ Yj.hom) hAffine (Over.mk e)
  let Yk := (Over.pullback (D.map e)).obj Yj
  let pK : yoneda.obj K.U.obj ⟶ Yk.left :=
    pullback.lift (yoneda.map K.toChart ≫ p) K.toStage
      (by simpa only [Category.assoc, Over.mk_hom] using K.isPullback.w.symm)
  have hpK : IsPullback (yoneda.map K.toChart) pK p (pullback.fst Yj.hom (D.map e)) := by
    apply IsPullback.of_bot _ (by simp [pK]) (IsPullback.of_hasPullback Yj.hom (D.map e))
    simpa [pK] using K.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  have hYk := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yj.hom (D.map e)
    hYj (hD k) (hD j.left)
  have hKs := P.presheaf.of_isPullback hpK hs
  have hKe := Q.presheaf.of_isPullback hpK he
  obtain ⟨gK, hgK⟩ := exists_hom_of_equalizes_atlas B S hS hYk hZ'.isSheaf pK hKs hKe
    (yoneda.map K.toChart ≫ g)
    (equalizes_kernelPair_of_baseChange_eq p Yj.hom (D.map e)
      (pullback.fst Yj.hom (D.map e)) (pullback.snd Yj.hom (D.map e)) pullback.condition
      (yoneda.map K.toChart) pK (by simp [pK]) g hkg)
  have hgKa : gK ≫ Zᵢ.hom = Yk.hom ≫ D.map e ≫ D.map j.hom := by
    apply hom_ext_of_surjective_etale_atlas B S hS hYk (hD i).isSheaf pK hKs hKe
    rw [← Category.assoc, hgK, Category.assoc, hg]
    have hw := congrArg (fun t => t ≫ D.map j.hom) K.isPullback.w
    simpa only [Yj, Yk, pK, Over.pullback_obj_hom, pullback.lift_snd_assoc,
      Over.mk_hom, Category.assoc] using hw.symm
  let d := e ≫ j.hom
  let η := iteratedBaseChangeIso (D.map j.hom) (D.map e) (D.map d)
    (D.map_comp e j.hom).symm Yᵢ
  let raw : pullback Yᵢ.hom (D.map d) ⟶ Zᵢ.left := η.inv.left ≫ gK
  have hrawa : raw ≫ Zᵢ.hom = pullback.snd Yᵢ.hom (D.map d) ≫ D.map d := by
    dsimp only [raw]
    rw [Category.assoc, hgKa]
    simpa only [d, Yk, Yj, Over.pullback_obj_hom, Functor.map_comp, Category.assoc] using
      congrArg (fun t => t ≫ D.map d) (Over.w η.inv)
  let g' : (Over.pullback (D.map d)).obj Yᵢ ⟶ (Over.pullback (D.map d)).obj Zᵢ :=
    Over.homMk (pullback.lift raw (pullback.snd Yᵢ.hom (D.map d)) hrawa) (by simp)
  let α := iteratedBaseChangeIso (D.map d) (limit.π D k) (limit.π D i) (limit.w D d) Yᵢ
  let β := iteratedBaseChangeIso (D.map d) (limit.π D k) (limit.π D i) (limit.w D d) Zᵢ
  let m : pullback Yᵢ.hom (limit.π D i) ⟶ pullback Yᵢ.hom (D.map d) :=
    pullback.lift (pullback.fst Yᵢ.hom (limit.π D i))
      (pullback.snd Yᵢ.hom (limit.π D i) ≫ limit.π D k)
      (by rw [Category.assoc, limit.w]; exact pullback.condition)
  have hraw : m ≫ raw = f₀ := by
    let A := iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
      (limit.w D j.hom) Yᵢ
    let q : pullback (p ≫ Yj.hom) (limit.π D j.left) ⟶ pullback Yj.hom (limit.π D j.left) :=
      pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _)
        (by simp only [Category.assoc, pullback.condition])
    have hq : IsPullback (pullback.fst (p ≫ Yj.hom) (limit.π D j.left)) q p
        (pullback.fst Yj.hom (limit.π D j.left)) := by
      apply IsPullback.of_bot _ (by simp [q]) (IsPullback.of_hasPullback Yj.hom (limit.π D j.left))
      simpa [q] using IsPullback.of_hasPullback (p ≫ Yj.hom) (limit.π D j.left)
    let l : pullback (p ≫ Yj.hom) (limit.π D j.left) ⟶ yoneda.obj K.U.obj :=
      K.isPullback.lift (pullback.snd _ _ ≫ limit.π D k) (pullback.fst _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition.symm)
    have hl : q ≫ A.hom.left ≫ m ≫ η.inv.left = l ≫ pK := by
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp [Yj, Yk, q, A, m, η, l, pK, iteratedBaseChangeIso_hom_left,
            iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc]
        · simp [Yj, Yk, q, A, m, η, l, pK, iteratedBaseChangeIso_hom_left,
            iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc, limit.w,
            pullback.condition]
      · simp [Yj, Yk, q, A, m, η, l, pK, iteratedBaseChangeIso_hom_left,
          iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc]
    have hEq : q ≫ A.hom.left ≫ (m ≫ raw) = q ≫ A.hom.left ≫ f₀ := by
      show q ≫ A.hom.left ≫ m ≫ η.inv.left ≫ gK = _
      have hh := congrArg (fun t => t ≫ gK) hl
      simp only [Category.assoc, hgK] at hh
      rw [hh]
      simpa [l, Category.assoc, q, A, Yj] using hgf
    obtain ⟨V, v, w, hV⟩ := isAffineHom_limitπ_of_baseChangeSizeBounded B S hS D hAffine
        hSizeB hν hHomSizeB
      hB j.left U (p ≫ Yj.hom)
    let vq := hV.flip.isoPullback.hom ≫ q
    have hEq' : A.hom.left ≫ (m ≫ raw) = A.hom.left ≫ f₀ := by
      apply hom_ext_of_surjective_etale_atlas B S hS
        (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yj.hom (limit.π D j.left)
          hYj (AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_baseChangeSizeBounded B S hS D
              hSizeB hν hHomSizeB hD hAffine hB) (hD j.left))
        hZ'.isSheaf vq
        (MorphismProperty.RespectsIso.precomp _ hV.flip.isoPullback.hom q
          (P.presheaf.of_isPullback hq hs))
        (MorphismProperty.RespectsIso.precomp _ hV.flip.isoPullback.hom q
          (Q.presheaf.of_isPullback hq he))
      simpa only [vq, Category.assoc] using
        congrArg (fun t => hV.flip.isoPullback.hom ≫ t) hEq
    let : IsIso A.hom.left :=
      inferInstanceAs (IsIso ((Over.forget (limit D)).map A.hom))
    exact (cancel_epi A.hom.left).mp hEq'
  refine ⟨k, d, g', α, β, iteratedBaseChangeIso_hom_fst _ _ _ _ _,
    iteratedBaseChangeIso_hom_fst _ _ _ _ _, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hm : α.hom.left ≫ m = pullback.fst ((Over.pullback (D.map d)).obj Yᵢ).hom
      (limit.π D k) := by
      apply pullback.hom_ext <;>
        simp [α, m, iteratedBaseChangeIso_hom_left, Category.assoc, pullback.condition]
    have hh := congrArg (fun t => α.hom.left ≫ t) hraw
    rw [← Category.assoc α.hom.left m raw, hm] at hh
    simpa [g', f₀, Category.assoc, β, iteratedBaseChangeIso_hom_left,
      iteratedBaseChangeIso_inv_left, Over.pullback_map_left] using hh.symm
  · simpa only [Over.comp_left, Over.pullback_obj_hom] using
      (Over.w (α.hom ≫ f)).trans
        (Over.w ((Over.pullback (limit.π D k)).map g' ≫ β.hom)).symm


/-- **Faithfulness, cofinality-free.** Two finite-stage morphisms that agree over the limit agree
at a sufficiently late stage, for a system with fewer stages than the cutoff and uniformly
bounded base changes. -/
public theorem eventually_eq_of_baseChange_eq_of_baseChangeSizeBounded
    (i : I) (Yᵢ Zᵢ : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f g : Yᵢ ⟶ Zᵢ)
    (hfg : (Over.pullback (limit.π D i)).map f =
      (Over.pullback (limit.π D i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (D.map e)).map f =
        (Over.pullback (D.map e)).map g := by
  classical
  have hYqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS Yᵢ.hom
    (hD i) (hQc i) hYfp
  obtain ⟨U₀, q₀, hU₀, hsurj, het⟩ := exists_affine_etale_atlas B S hS Yᵢ.left hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hf : (q₀ ≫ f.left) ≫ Zᵢ.hom = q₀ ≫ Yᵢ.hom := by simp
  have hg : (q₀ ≫ g.left) ≫ Zᵢ.hom = q₀ ≫ Yᵢ.hom := by simp
  obtain ⟨j, hj⟩ := eventually_eq_on_affine_chart_of_baseChangeSizeBounded B S hS hZ D hD hAffine
    hQc hQs hSizeB hν hHomSizeB hB i U (q₀ ≫ Yᵢ.hom) hZ' Zᵢ.hom hZfp.1
    (q₀ ≫ f.left) (q₀ ≫ g.left) hf hg
    (precomp_eq_of_baseChange_eq (limit.π D i) Yᵢ Zᵢ f g hfg q₀)
  refine ⟨j.left, j.hom, ?_⟩
  let C := affineStageChart B S hS D i U (q₀ ≫ Yᵢ.hom) hAffine j
  let p : yoneda.obj C.U.obj ⟶ pullback Yᵢ.hom (D.map j.hom) :=
    pullback.lift (yoneda.map C.toChart ≫ q₀) C.toStage
      (by simpa only [Category.assoc] using C.isPullback.w.symm)
  have hp : IsPullback (yoneda.map C.toChart) p q₀
      (pullback.fst Yᵢ.hom (D.map j.hom)) := by
    apply IsPullback.of_bot _ (by simp [p]) (IsPullback.of_hasPullback Yᵢ.hom (D.map j.hom))
    simpa [p] using C.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  have hpalgebraic := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom (D.map j.hom)
    hY (hD j.left) (hD i)
  have heq : pullback.fst Yᵢ.hom (D.map j.hom) ≫ f.left =
      pullback.fst Yᵢ.hom (D.map j.hom) ≫ g.left := by
    apply hom_ext_of_surjective_etale_atlas B S hS hpalgebraic hZ'.isSheaf p
      (P.presheaf.of_isPullback hp hsurj)
      (Q.presheaf.of_isPullback hp (represented_etale_of_isEtale B S hS q₀ het))
    simpa [p, Category.assoc] using hj
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa [Over.pullback_map_left] using heq
  · simp [Over.pullback_map_left]


/-- **Isomorphisms descend, cofinality-free.** A morphism of finite-presentation algebraic spaces
over a stage whose base change to the limit is an isomorphism is an isomorphism after base change
to a sufficiently late stage. -/
public theorem exists_isIso_after_baseChange_of_baseChangeSizeBounded
    (i : I) (Y Z : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Z.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Z.hom)
    (f : Y ⟶ Z) [IsIso ((Over.pullback (limit.π D i)).map f)] :
    ∃ (j : I) (e : j ⟶ i), IsIso ((Over.pullback (D.map e)).map f) := by
  classical
  let f₀ := (Over.pullback (limit.π D i)).map f
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ := exists_morphism_after_baseChange_of_baseChangeSizeBounded
    B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB i Z Y hZ' hY hZfp hYfp (inv f₀)
  have hα' := iteratedBaseChangeIso_unique (D.map e) (limit.π D j) (limit.π D i)
    (limit.w D e) Z α hα
  have hβ' := iteratedBaseChangeIso_unique (D.map e) (limit.π D j) (limit.π D i)
    (limit.w D e) Y β hβ
  have hn : (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map f) ≫
      α.hom = β.hom ≫ f₀ := by
    rw [hα', hβ']
    exact iteratedBaseChangeIso_naturality _ _ _ (limit.w D e) f
  let Yj := (Over.pullback (D.map e)).obj Y
  let Zj := (Over.pullback (D.map e)).obj Z
  let fj := (Over.pullback (D.map e)).map f
  have hYj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Y.hom (D.map e) hY (hD j) (hD i)
  have hZj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Z.hom (D.map e) hZ' (hD j) (hD i)
  have hYjfp := isFinitePresentation_of_isPullback B S hS hYj hY (hD j) (hD i)
    (IsPullback.of_hasPullback Y.hom (D.map e)) hYfp
  have hZjfp := isFinitePresentation_of_isPullback B S hS hZj hZ' (hD j) (hD i)
    (IsPullback.of_hasPullback Z.hom (D.map e)) hZfp
  have hfg : (Over.pullback (limit.π D j)).map (fj ≫ g) =
      (Over.pullback (limit.π D j)).map (𝟙 Yj) := by
    apply (Iso.cancel_iso_hom_right _ _ β).mp
    simp only [Yj, Functor.map_comp]
    rw [Category.assoc, ← hg, ← Category.assoc, hn, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
    rw [(Over.pullback (limit.π D j)).map_id Yj, Category.id_comp]
  have hgf : (Over.pullback (limit.π D j)).map (g ≫ fj) =
      (Over.pullback (limit.π D j)).map (𝟙 Zj) := by
    apply (Iso.cancel_iso_hom_right _ _ α).mp
    simp only [Zj, Functor.map_comp]
    rw [Category.assoc, hn, ← Category.assoc, ← hg, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]
    rw [(Over.pullback (limit.π D j)).map_id Zj, Category.id_comp]
  obtain ⟨k₁, e₁, hk₁⟩ := eventually_eq_of_baseChange_eq_of_baseChangeSizeBounded B S hS hZ D
    hD hAffine hQc hQs hSizeB hν hHomSizeB hB j Yj Yj hYj hYj hYjfp hYjfp (fj ≫ g) (𝟙 Yj) hfg
  obtain ⟨k₂, e₂, hk₂⟩ := eventually_eq_of_baseChange_eq_of_baseChangeSizeBounded B S hS hZ D
    hD hAffine hQc hQs hSizeB hν hHomSizeB hB j Zj Zj hZj hZj hZjfp hZjfp (g ≫ fj) (𝟙 Zj) hgf
  let k := IsCofiltered.min (Over.mk e₁) (Over.mk e₂)
  let a := IsCofiltered.minToLeft (Over.mk e₁) (Over.mk e₂)
  let b := IsCofiltered.minToRight (Over.mk e₁) (Over.mk e₂)
  have hk₁' := baseChange_eq_of_baseChange_eq (D.map e₁) (D.map a.left) (D.map k.hom)
    (by rw [← D.map_comp]; exact congrArg D.map a.w) (fj ≫ g) (𝟙 Yj) hk₁
  have hk₂' := baseChange_eq_of_baseChange_eq (D.map e₂) (D.map b.left) (D.map k.hom)
    (by rw [← D.map_comp]; exact congrArg D.map b.w) (g ≫ fj) (𝟙 Zj) hk₂
  let : IsIso ((Over.pullback (D.map k.hom)).map fj) :=
    ⟨⟨(Over.pullback (D.map k.hom)).map g,
      by simpa only [Functor.map_comp] using hk₁'.trans ((Over.pullback (D.map k.hom)).map_id Yj),
      by simpa only [Functor.map_comp] using hk₂'.trans ((Over.pullback (D.map k.hom)).map_id Zj)⟩⟩
  refine ⟨k.left, k.hom ≫ e, ?_⟩
  have h := iteratedBaseChangeIso_naturality (D.map e) (D.map k.hom)
    (D.map (k.hom ≫ e)) (D.map_comp _ _).symm f
  have hf' : (Over.pullback (D.map (k.hom ≫ e))).map f =
      (iteratedBaseChangeIso (D.map e) (D.map k.hom) (D.map (k.hom ≫ e))
        (D.map_comp _ _).symm Y).inv ≫
      (Over.pullback (D.map k.hom)).map fj ≫
      (iteratedBaseChangeIso (D.map e) (D.map k.hom) (D.map (k.hom ≫ e))
        (D.map_comp _ _).symm Z).hom := by
    rw [show fj = (Over.pullback (D.map e)).map f from rfl, h, Iso.inv_hom_id_assoc]
  rw [hf']
  infer_instance

private theorem exists_mono_after_baseChange_of_baseChangeSizeBounded
    (i : I) (Y Z : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Z.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Z.hom)
    (f : Y ⟶ Z) [Mono ((Over.pullback (limit.π D i)).map f)] :
    ∃ (j : I) (e : j ⟶ i), Mono ((Over.pullback (D.map e)).map f) := by
  let c := overPullbackCone f f
  have hc := overPullbackCone_isPullback f f
  have hf := isFinitePresentation_overHom B S hS hZ (hD i) (hQc i) (hQs i)
    Y Z hY hZ' hYfp hZfp f
  have hR : AlgebraicGeometry.IsAlgebraicSpace B S hS c.pt.left :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f.left f.left hY hY hZ'
  have hRfst := isFinitePresentation_of_isPullback B S hS hR hY hY hZ'
    (IsPullback.of_hasPullback f.left f.left).flip hf
  have hRfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS c.pt.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hR hY (hD i)
      (pullback.fst f.left f.left) Y.hom hRfst hYfp
  have heq : (Over.pullback (limit.π D i)).map c.fst =
      (Over.pullback (limit.π D i)).map c.snd := by
    apply (cancel_mono ((Over.pullback (limit.π D i)).map f)).mp
    rw [← Functor.map_comp, ← Functor.map_comp, c.condition]
  obtain ⟨j, e, hj⟩ := eventually_eq_of_baseChange_eq_of_baseChangeSizeBounded B S hS
      hZ D hD hAffine
    hQc hQs hSizeB hν hHomSizeB hB i c.pt Y hR hY hRfp hYfp c.fst c.snd heq
  exact ⟨j, e, IsKernelPair.mono_of_eq_fst_snd (hc.map (Over.pullback (D.map e))) hj⟩

private theorem exists_lift_pair_after_baseChange_of_baseChangeSizeBounded
    (i : I) (A R W : Over (D.obj i))
    (hA : AlgebraicGeometry.IsAlgebraicSpace B S hS A.left)
    (hR : AlgebraicGeometry.IsAlgebraicSpace B S hS R.left)
    (hW : AlgebraicGeometry.IsAlgebraicSpace B S hS W.left)
    (hAfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS A.hom)
    (hRfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS R.hom)
    (hWfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS W.hom)
    (s t : R ⟶ W) (a b : A ⟶ W)
    (u : (Over.pullback (limit.π D i)).obj A ⟶ (Over.pullback (limit.π D i)).obj R)
    (hu₁ : u ≫ (Over.pullback (limit.π D i)).map s = (Over.pullback (limit.π D i)).map a)
    (hu₂ : u ≫ (Over.pullback (limit.π D i)).map t = (Over.pullback (limit.π D i)).map b) :
    ∃ (j : I) (e : j ⟶ i)
      (v : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj R),
      v ≫ (Over.pullback (D.map e)).map s = (Over.pullback (D.map e)).map a ∧
      v ≫ (Over.pullback (D.map e)).map t = (Over.pullback (D.map e)).map b := by
  classical
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ := exists_morphism_after_baseChange_of_baseChangeSizeBounded
    B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB i A R hA hR hAfp hRfp u
  have hα' := iteratedBaseChangeIso_unique (D.map e) (limit.π D j) (limit.π D i)
    (limit.w D e) A α hα
  have hβ' := iteratedBaseChangeIso_unique (D.map e) (limit.π D j) (limit.π D i)
    (limit.w D e) R β hβ
  let γ := iteratedBaseChangeIso (D.map e) (limit.π D j) (limit.π D i) (limit.w D e) W
  have heq (v : R ⟶ W) (z : A ⟶ W)
      (hz : u ≫ (Over.pullback (limit.π D i)).map v = (Over.pullback (limit.π D i)).map z) :
      (Over.pullback (limit.π D j)).map (g ≫ (Over.pullback (D.map e)).map v) =
        (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map z) := by
    have hv : (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map v) ≫
        γ.hom = β.hom ≫ (Over.pullback (limit.π D i)).map v := by
      rw [hβ']
      exact iteratedBaseChangeIso_naturality _ _ _ (limit.w D e) v
    have hz' : (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map z) ≫
        γ.hom = α.hom ≫ (Over.pullback (limit.π D i)).map z := by
      rw [hα']
      exact iteratedBaseChangeIso_naturality _ _ _ (limit.w D e) z
    apply (Iso.cancel_iso_hom_right _ _ γ).mp
    rw [Functor.map_comp, Category.assoc, hv, ← Category.assoc, ← hg,
      Category.assoc, hz, hz']
  let Aj := (Over.pullback (D.map e)).obj A
  let Wj := (Over.pullback (D.map e)).obj W
  have hAj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS A.hom (D.map e) hA (hD j) (hD i)
  have hWj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS W.hom (D.map e) hW (hD j) (hD i)
  have hAjfp := isFinitePresentation_of_isPullback B S hS hAj hA (hD j) (hD i)
    (IsPullback.of_hasPullback A.hom (D.map e)) hAfp
  have hWjfp := isFinitePresentation_of_isPullback B S hS hWj hW (hD j) (hD i)
    (IsPullback.of_hasPullback W.hom (D.map e)) hWfp
  obtain ⟨k₁, e₁, hk₁⟩ := eventually_eq_of_baseChange_eq_of_baseChangeSizeBounded B S hS hZ D
    hD hAffine hQc hQs hSizeB hν hHomSizeB hB j Aj Wj hAj hWj hAjfp hWjfp
    (g ≫ (Over.pullback (D.map e)).map s) ((Over.pullback (D.map e)).map a) (heq s a hu₁)
  obtain ⟨k₂, e₂, hk₂⟩ := eventually_eq_of_baseChange_eq_of_baseChangeSizeBounded B S hS hZ D
    hD hAffine hQc hQs hSizeB hν hHomSizeB hB j Aj Wj hAj hWj hAjfp hWjfp
    (g ≫ (Over.pullback (D.map e)).map t) ((Over.pullback (D.map e)).map b) (heq t b hu₂)
  let k := IsCofiltered.min (Over.mk e₁) (Over.mk e₂)
  let c₁ := IsCofiltered.minToLeft (Over.mk e₁) (Over.mk e₂)
  let c₂ := IsCofiltered.minToRight (Over.mk e₁) (Over.mk e₂)
  have hk₁' := baseChange_eq_of_baseChange_eq (D.map e₁) (D.map c₁.left) (D.map k.hom)
    (by rw [← D.map_comp]; exact congrArg D.map c₁.w) _ _ hk₁
  have hk₂' := baseChange_eq_of_baseChange_eq (D.map e₂) (D.map c₂.left) (D.map k.hom)
    (by rw [← D.map_comp]; exact congrArg D.map c₂.w) _ _ hk₂
  let δ (Z : Over (D.obj i)) := iteratedBaseChangeIso (D.map e) (D.map k.hom)
    (D.map (k.hom ≫ e)) (D.map_comp _ _).symm Z
  let v := (δ A).inv ≫ (Over.pullback (D.map k.hom)).map g ≫ (δ R).hom
  have hfinal (x : R ⟶ W) (z : A ⟶ W)
      (hx : (Over.pullback (D.map k.hom)).map (g ≫ (Over.pullback (D.map e)).map x) =
        (Over.pullback (D.map k.hom)).map ((Over.pullback (D.map e)).map z)) :
      v ≫ (Over.pullback (D.map (k.hom ≫ e))).map x =
        (Over.pullback (D.map (k.hom ≫ e))).map z := by
    have hn := iteratedBaseChangeIso_naturality (D.map e) (D.map k.hom)
      (D.map (k.hom ≫ e)) (D.map_comp _ _).symm x
    have hz' := iteratedBaseChangeIso_naturality (D.map e) (D.map k.hom)
      (D.map (k.hom ≫ e)) (D.map_comp _ _).symm z
    calc
      v ≫ (Over.pullback (D.map (k.hom ≫ e))).map x =
          (δ A).inv ≫ (Over.pullback (D.map k.hom)).map g ≫
            (Over.pullback (D.map k.hom)).map ((Over.pullback (D.map e)).map x) ≫
            (δ W).hom := by
        simp only [v, Category.assoc]
        rw [← hn]
      _ = (δ A).inv ≫ (Over.pullback (D.map k.hom)).map
          ((Over.pullback (D.map e)).map z) ≫ (δ W).hom := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun z => (δ A).inv ≫ z ≫ (δ W).hom) hx
      _ = (Over.pullback (D.map (k.hom ≫ e))).map z := by
        rw [hz', Iso.inv_hom_id_assoc]
  exact ⟨k.left, k.hom ≫ e, v, hfinal s a hk₁', hfinal t b hk₂'⟩

include hZ hD hAffine hQc hQs hSizeB hν hHomSizeB hB in
/-- The étale relation presenting an algebraic space of finite presentation over the
limit, once it is defined at a stage, becomes an étale equivalence relation at a later
stage, where it presents a finite-presentation model of the space. -/
private theorem exists_model_of_stage_relation_of_baseChangeSizeBounded (nn : I)
    (hLim : AlgebraicGeometry.IsAlgebraicSpace B S hS (limit D))
    (Y : Over (limit D)) (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    {W KR : AlgebraicGeometry.BigFppfOver B S hS} (w : yoneda.obj W ⟶ Y.left)
    (hws : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (hwe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (kt ks : KR ⟶ W) (hwk : IsPullback (yoneda.map kt) (yoneda.map ks) w w)
    {Wn Rn : AlgebraicGeometry.BigFppfOver B S hS}
    (hWnAff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Wn))
    (wn : yoneda.obj Wn ⟶ D.obj nn) (sn tn : Rn ⟶ Wn)
    (htn : yoneda.map tn ≫ wn = yoneda.map sn ≫ wn)
    (hsnEtale : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sn))
    (htnEtale : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tn))
    (hWnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wn)
    (hRnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map sn ≫ wn))
    (awn : W ⟶ Wn) (arn : KR ⟶ Rn)
    (hWnlim : IsPullback (yoneda.map awn) (w ≫ Y.hom) wn (limit.π D nn))
    (hRnlim : IsPullback (yoneda.map arn) (yoneda.map kt ≫ w ≫ Y.hom)
      (yoneda.map sn ≫ wn) (limit.π D nn))
    (hsnCompat : arn ≫ sn = kt ≫ awn) (htnCompat : arn ≫ tn = ks ≫ awn) :
    ∃ (i : I) (Yᵢ : Over (D.obj i)),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D i)).obj Yᵢ) := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  set rn := yoneda.map sn ≫ wn with hrnDef
  set pW := w ≫ Y.hom with hpWDef
  set pR := yoneda.map kt ≫ pW with hpRDef
  have ht : yoneda.map kt ≫ pW = pR := rfl
  have hs : yoneda.map ks ≫ pW = pR := by
    simpa only [pR, pW, ← Category.assoc] using congrArg (fun z => z ≫ Y.hom) hwk.w.symm
  have hRnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rn
  have hWnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wn
  let Rₙ := Over.mk rn
  let Wₙ := Over.mk wn
  let sₙ : Rₙ ⟶ Wₙ := Over.homMk (yoneda.map sn) rfl
  let tₙ : Rₙ ⟶ Wₙ := Over.homMk (yoneda.map tn) htn
  let sL : Over.mk pR ⟶ Over.mk pW := Over.homMk (yoneda.map kt) ht
  let tL : Over.mk pR ⟶ Over.mk pW := Over.homMk (yoneda.map ks) hs
  let εR : Over.mk pR ≅ (Over.pullback (limit.π D nn)).obj Rₙ :=
    Over.isoMk hRnlim.isoPullback hRnlim.isoPullback_hom_snd
  let εW : Over.mk pW ≅ (Over.pullback (limit.π D nn)).obj Wₙ :=
    Over.isoMk hWnlim.isoPullback hWnlim.isoPullback_hom_snd
  have hεs : εR.hom ≫ (Over.pullback (limit.π D nn)).map sₙ = sL ≫ εW.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [εR, εW, sₙ, sL, Rₙ, Wₙ, Over.pullback_map_left,
        IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc,
        Category.assoc] using congrArg yoneda.map hsnCompat
    · simp [εR, εW, sₙ, sL, Rₙ, Wₙ, Over.pullback_map_left, Category.assoc, ht]
  have hεt : εR.hom ≫ (Over.pullback (limit.π D nn)).map tₙ = tL ≫ εW.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [εR, εW, tₙ, tL, Rₙ, Wₙ, Over.pullback_map_left,
        IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc,
        Category.assoc] using congrArg yoneda.map htnCompat
    · simp [εR, εW, tₙ, tL, Rₙ, Wₙ, Over.pullback_map_left, Category.assoc, hs]
  let rL : Over.mk pW ⟶ Over.mk pR := Over.homMk
    (hwk.lift (𝟙 _) (𝟙 _) (by simp)) (by
      dsimp only [Over.mk_hom, Over.mk_left]
      rw [← ht, IsPullback.lift_fst_assoc, Category.id_comp])
  have hrLs : rL ≫ sL = 𝟙 _ := by ext; simp [rL, sL]
  have hrLt : rL ≫ tL = 𝟙 _ := by ext; simp [rL, tL]
  let rF := εW.inv ≫ rL ≫ εR.hom
  have hrFs : rF ≫ (Over.pullback (limit.π D nn)).map sₙ =
      (Over.pullback (limit.π D nn)).map (𝟙 Wₙ) := by
    simp only [rF, Category.assoc, hεs, ← Category.assoc rL sL, hrLs,
      Category.id_comp, Iso.inv_hom_id]
    exact ((Over.pullback (limit.π D nn)).map_id Wₙ).symm
  have hrFt : rF ≫ (Over.pullback (limit.π D nn)).map tₙ =
      (Over.pullback (limit.π D nn)).map (𝟙 Wₙ) := by
    simp only [rF, Category.assoc, hεt, ← Category.assoc rL tL, hrLt,
      Category.id_comp, Iso.inv_hom_id]
    exact ((Over.pullback (limit.π D nn)).map_id Wₙ).symm
  obtain ⟨ir, er', rr, hrrs, hrrt⟩ := exists_lift_pair_after_baseChange_of_baseChangeSizeBounded
    B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB nn Wₙ Rₙ Wₙ
    hWnAlg hRnAlg hWnAlg hWnFp hRnFp hWnFp sₙ tₙ (𝟙 _) (𝟙 _) rF hrFs hrFt
  let invL : Over.mk pR ⟶ Over.mk pR := Over.homMk
    (hwk.lift (yoneda.map ks) (yoneda.map kt) hwk.w.symm) (by
      dsimp only [Over.mk_hom, Over.mk_left]
      rw [← ht, IsPullback.lift_fst_assoc, hs])
  have hiLs : invL ≫ sL = tL := by ext; simp [invL, sL, tL]
  have hiLt : invL ≫ tL = sL := by ext; simp [invL, sL, tL]
  let invF := εR.inv ≫ invL ≫ εR.hom
  have hiFs : invF ≫ (Over.pullback (limit.π D nn)).map sₙ =
      (Over.pullback (limit.π D nn)).map tₙ := by
    simp only [invF, Category.assoc, hεs, ← Category.assoc invL sL, hiLs]
    rw [← hεt, Iso.inv_hom_id_assoc]
  have hiFt : invF ≫ (Over.pullback (limit.π D nn)).map tₙ =
      (Over.pullback (limit.π D nn)).map sₙ := by
    simp only [invF, Category.assoc, hεt, ← Category.assoc invL tL, hiLt]
    rw [← hεs, Iso.inv_hom_id_assoc]
  obtain ⟨ii, ei, ri, hris, hrit⟩ := exists_lift_pair_after_baseChange_of_baseChangeSizeBounded
    B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB nn Rₙ Rₙ Wₙ
    hRnAlg hRnAlg hWnAlg hRnFp hRnFp hWnFp sₙ tₙ tₙ sₙ invF hiFs hiFt
  let cn := overPullbackCone tₙ sₙ
  have hCAlg : AlgebraicGeometry.IsAlgebraicSpace B S hS cn.pt.left :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS tₙ.left sₙ.left hRnAlg hRnAlg hWnAlg
  have hsₙfp := isFinitePresentation_overHom B S hS hZ (hD nn) (hQc nn) (hQs nn)
    Rₙ Wₙ hRnAlg hWnAlg hRnFp hWnFp sₙ
  have hCfst := isFinitePresentation_of_isPullback B S hS hCAlg hRnAlg hRnAlg hWnAlg
    (IsPullback.of_hasPullback tₙ.left sₙ.left).flip hsₙfp
  have hCFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS cn.pt.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hCAlg hRnAlg (hD nn)
      (pullback.fst tₙ.left sₙ.left) rn hCfst hRnFp
  let F := Over.pullback (limit.π D nn)
  let ca : F.obj cn.pt ⟶ Over.mk pR := F.map cn.fst ≫ εR.inv
  let cb : F.obj cn.pt ⟶ Over.mk pR := F.map cn.snd ≫ εR.inv
  have hcab : ca ≫ tL = cb ≫ sL := by
    apply (Iso.cancel_iso_hom_right _ _ εW).mp
    simp only [ca, cb, Category.assoc]
    rw [← hεt, ← hεs, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc,
      ← F.map_comp, ← F.map_comp, cn.condition]
  have hcabLeft : ca.left ≫ yoneda.map ks = cb.left ≫ yoneda.map kt :=
    congrArg (fun z => z.left) hcab
  have hcomp : (ca.left ≫ yoneda.map kt) ≫ w =
      (cb.left ≫ yoneda.map ks) ≫ w := by
    rw [Category.assoc, hwk.w, ← Category.assoc, hcabLeft,
      Category.assoc, hwk.w, Category.assoc]
  let compL : F.obj cn.pt ⟶ Over.mk pR := Over.homMk
    (hwk.lift (ca.left ≫ yoneda.map kt) (cb.left ≫ yoneda.map ks) hcomp)
    (by
      dsimp only [Over.mk_hom]
      calc hwk.lift (ca.left ≫ yoneda.map kt)
              (cb.left ≫ yoneda.map ks) hcomp ≫ pR
          = hwk.lift (ca.left ≫ yoneda.map kt)
              (cb.left ≫ yoneda.map ks) hcomp ≫ yoneda.map kt ≫ pW := by
            rw [ht]
        _ = (ca.left ≫ yoneda.map kt) ≫ pW := IsPullback.lift_fst_assoc _ _ _ _ _
        _ = ca.left ≫ pR := by rw [Category.assoc, ht]
        _ = (F.obj cn.pt).hom := ca.w)
  have hcompS : compL ≫ sL = ca ≫ sL := by ext; simp [compL, sL]
  have hcompT : compL ≫ tL = cb ≫ tL := by ext; simp [compL, tL]
  let compF := compL ≫ εR.hom
  have hcompFs : compF ≫ F.map sₙ = F.map (cn.fst ≫ sₙ) := by
    simp only [compF]
    rw [Category.assoc, hεs, ← Category.assoc, hcompS]
    simp only [ca, Category.assoc]
    rw [← hεs, Iso.inv_hom_id_assoc, F.map_comp]
  have hcompFt : compF ≫ F.map tₙ = F.map (cn.snd ≫ tₙ) := by
    simp only [compF]
    rw [Category.assoc, hεt, ← Category.assoc, hcompT]
    simp only [cb, Category.assoc]
    rw [← hεt, Iso.inv_hom_id_assoc, F.map_comp]
  obtain ⟨ic, ec, rc, hrcs, hrct⟩ := exists_lift_pair_after_baseChange_of_baseChangeSizeBounded
    B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB nn cn.pt Rₙ Wₙ
    hCAlg hRnAlg hWnAlg hCFp hRnFp hWnFp sₙ tₙ
    (cn.fst ≫ sₙ) (cn.snd ≫ tₙ) compF hcompFs hcompFt
  let KWn := atlasKernelPair B S hS wn (hD nn).diagonal_representable
  have hψcomm : yoneda.map sn ≫ wn = yoneda.map tn ≫ wn := htn.symm
  let ψ₀ : Rn ⟶ KWn.R := yoneda.preimage
    (KWn.kernelPair.lift (yoneda.map sn) (yoneda.map tn) hψcomm)
  have hψ₀ : yoneda.map ψ₀ =
      KWn.kernelPair.lift (yoneda.map sn) (yoneda.map tn) hψcomm := yoneda.map_preimage _
  have hψs : ψ₀ ≫ KWn.s = sn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hψ₀]
    exact KWn.kernelPair.lift_fst _ _ _
  have hψt : ψ₀ ≫ KWn.t = tn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hψ₀]
    exact KWn.kernelPair.lift_snd _ _ _
  let Zₙ : Over (D.obj nn) := Over.mk (yoneda.map KWn.s ≫ wn)
  let ψ : Rₙ ⟶ Zₙ := Over.homMk (yoneda.map ψ₀) (by
    show yoneda.map ψ₀ ≫ yoneda.map KWn.s ≫ wn = rn
    rw [← Category.assoc, ← yoneda.map_comp, hψs])
  have hZnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS KWn.R
  have hKWnt : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map KWn.s) :=
    isFinitePresentation_of_isPullback B S hS hZnAlg hWnAlg hWnAlg (hD nn)
      KWn.kernelPair.flip hWnFp
  have hZnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zₙ.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hZnAlg hWnAlg (hD nn)
      (yoneda.map KWn.s) wn hKWnt hWnFp
  have hψfst : (F.map ψ).left ≫ pullback.fst Zₙ.hom (limit.π D nn) =
      pullback.fst rn (limit.π D nn) ≫ yoneda.map ψ₀ := by
    simp [F, Over.pullback_map_left, ψ, Rₙ]
  have hψsnd : (F.map ψ).left ≫ pullback.snd Zₙ.hom (limit.π D nn) =
      pullback.snd rn (limit.π D nn) := by
    simp [F, Over.pullback_map_left, ψ, Rₙ]
  have e₂ : (hRnlim.isoPullback.hom ≫ (F.map ψ).left) ≫
      pullback.snd Zₙ.hom (limit.π D nn) = pR := by
    rw [Category.assoc, hψsnd, hRnlim.isoPullback_hom_snd]
  have e₁ : (hRnlim.isoPullback.hom ≫ (F.map ψ).left) ≫
      pullback.fst Zₙ.hom (limit.π D nn) ≫ yoneda.map KWn.s =
      yoneda.map kt ≫ yoneda.map awn := by
    rw [Category.assoc, reassoc_of% hψfst, hRnlim.isoPullback_hom_fst_assoc,
      ← yoneda.map_comp ψ₀ KWn.s, hψs, ← yoneda.map_comp, hsnCompat,
      yoneda.map_comp]
  have e₁' : (hRnlim.isoPullback.hom ≫ (F.map ψ).left) ≫
      pullback.fst Zₙ.hom (limit.π D nn) ≫ yoneda.map KWn.t =
      yoneda.map ks ≫ yoneda.map awn := by
    rw [Category.assoc, reassoc_of% hψfst, hRnlim.isoPullback_hom_fst_assoc,
      ← yoneda.map_comp ψ₀ KWn.t, hψt, ← yoneda.map_comp, htnCompat,
      yoneda.map_comp]
  have hμ : Mono (hRnlim.isoPullback.hom ≫ (F.map ψ).left) := by
    refine ⟨fun {T} a b hab => ?_⟩
    have hab' : (a ≫ hRnlim.isoPullback.hom) ≫ (F.map ψ).left =
        (b ≫ hRnlim.isoPullback.hom) ≫ (F.map ψ).left := by
      simpa only [← Category.assoc] using hab
    refine hwk.hom_ext (hWnlim.hom_ext ?_ ?_) (hWnlim.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ← e₁]
      simp only [← Category.assoc]
      rw [hab']
    · rw [Category.assoc, Category.assoc, ht, ← e₂]
      simp only [← Category.assoc]
      rw [hab']
    · rw [Category.assoc, Category.assoc, ← e₁']
      simp only [← Category.assoc]
      rw [hab']
    · rw [Category.assoc, Category.assoc, hs, ← e₂]
      simp only [← Category.assoc]
      rw [hab']
  have hmonoψ : Mono ((Over.pullback (limit.π D nn)).map ψ) := by
    refine Over.mono_of_mono_left _ (hk := ?_)
    have := hμ
    rw [show (F.map ψ).left = inv hRnlim.isoPullback.hom ≫
      (hRnlim.isoPullback.hom ≫ (F.map ψ).left) from by simp]
    infer_instance
  obtain ⟨jm, ejm, hjmMono⟩ := exists_mono_after_baseChange_of_baseChangeSizeBounded B S hS
      hZ D hD hAffine
    hQc hQs hSizeB hν hHomSizeB hB nn Rₙ Zₙ hRnAlg hZnAlg hRnFp hZnFp ψ
  -- a single stage carrying all of reflexivity, symmetry, transitivity and monicity
  let oo : Over nn := IsCofiltered.min
    (IsCofiltered.min (IsCofiltered.min (Over.mk er') (Over.mk ei)) (Over.mk ec))
    (Over.mk ejm)
  let aMono : oo ⟶ Over.mk ejm := IsCofiltered.minToRight _ _
  let aComp : oo ⟶ Over.mk ec :=
    IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToRight _ _
  let aRefl : oo ⟶ Over.mk er' :=
    IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft _ _
  let aSymm : oo ⟶ Over.mk ei :=
    IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToRight _ _
  obtain ⟨rrO, hrrOs, hrrOt⟩ := exists_liftPair_of_comp (D.map er') (D.map aRefl.left)
    (D.map oo.hom) (by rw [← D.map_comp]; exact congrArg D.map (Over.w aRefl))
    sₙ tₙ (𝟙 Wₙ) (𝟙 Wₙ) rr hrrs hrrt
  obtain ⟨riO, hriOs, hriOt⟩ := exists_liftPair_of_comp (D.map ei) (D.map aSymm.left)
    (D.map oo.hom) (by rw [← D.map_comp]; exact congrArg D.map (Over.w aSymm))
    sₙ tₙ tₙ sₙ ri hris hrit
  obtain ⟨rcO, hrcOs, hrcOt⟩ := exists_liftPair_of_comp (D.map ec) (D.map aComp.left)
    (D.map oo.hom) (by rw [← D.map_comp]; exact congrArg D.map (Over.w aComp))
    sₙ tₙ (cn.fst ≫ sₙ) (cn.snd ≫ tₙ) rc hrcs hrct
  have hmonoO : Mono ((Over.pullback (D.map oo.hom)).map ψ) := by
    have := mono_overPullback_map (D.map aMono.left)
      ((Over.pullback (D.map ejm)).map ψ) hjmMono
    have hcomp' : D.map aMono.left ≫ D.map ejm = D.map oo.hom := by
      rw [← D.map_comp]; exact congrArg D.map (Over.w aMono)
    rw [show (Over.pullback (D.map oo.hom)).map ψ =
        (iteratedBaseChangeIso (D.map ejm) (D.map aMono.left) (D.map oo.hom)
            hcomp' Rₙ).inv ≫
          (Over.pullback (D.map aMono.left)).map ((Over.pullback (D.map ejm)).map ψ) ≫
          (iteratedBaseChangeIso (D.map ejm) (D.map aMono.left) (D.map oo.hom)
            hcomp' Zₙ).hom from by
      rw [iteratedBaseChangeIso_naturality, Iso.inv_hom_id_assoc]]
    exact mono_comp' (IsIso.mono_of_iso _) (mono_comp' this (IsIso.mono_of_iso _))
  -- the descended relation as objects of the site
  have hoAff := ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS (D.map oo.hom)
    (hD oo.left) (hD nn)).out 2 1).mp (hAffine oo.hom)
  let WO := hoAff.1.pullback wn
  let RO := hoAff.1.pullback rn
  let wO := hoAff.1.fst wn
  let rO := hoAff.1.fst rn
  let bW : WO ⟶ Wn := hoAff.1.snd wn
  let bR : RO ⟶ Rn := hoAff.1.snd rn
  have hWO : IsPullback wO (yoneda.map bW) (D.map oo.hom) wn := hoAff.1.isPullback wn
  have hRO : IsPullback rO (yoneda.map bR) (D.map oo.hom) rn := hoAff.1.isPullback rn
  let εWO : Over.mk wO ≅ (Over.pullback (D.map oo.hom)).obj Wₙ :=
    Over.isoMk hWO.flip.isoPullback (by exact hWO.flip.isoPullback_hom_snd)
  let εRO : Over.mk rO ≅ (Over.pullback (D.map oo.hom)).obj Rₙ :=
    Over.isoMk hRO.flip.isoPullback (by exact hRO.flip.isoPullback_hom_snd)
  obtain ⟨sOO, hsOOdef⟩ : ∃ z : Over.mk rO ⟶ Over.mk wO,
      z = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map sₙ ≫ εWO.inv := ⟨_, rfl⟩
  obtain ⟨tOO, htOOdef⟩ : ∃ z : Over.mk rO ⟶ Over.mk wO,
      z = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map tₙ ≫ εWO.inv := ⟨_, rfl⟩
  let sO : RO ⟶ WO := yoneda.preimage sOO.left
  let tO : RO ⟶ WO := yoneda.preimage tOO.left
  have hsOl : yoneda.map sO = sOO.left := yoneda.map_preimage _
  have htOl : yoneda.map tO = tOO.left := yoneda.map_preimage _
  have hsOW : yoneda.map sO ≫ wO = rO := by rw [hsOl]; exact Over.w sOO
  have htOW : yoneda.map tO ≫ wO = rO := by rw [htOl]; exact Over.w tOO
  have hεWfst : εWO.hom.left ≫ pullback.fst wn (D.map oo.hom) = yoneda.map bW :=
    hWO.flip.isoPullback_hom_fst
  have hεRfst : εRO.hom.left ≫ pullback.fst rn (D.map oo.hom) = yoneda.map bR :=
    hRO.flip.isoPullback_hom_fst
  have hsoSq : sO ≫ bW = bR ≫ sn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, hsOl]
    have h1 : sOO ≫ εWO.hom = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map sₙ := by
      rw [hsOOdef]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h2 := congrArg (fun z : Over.mk rO ⟶ (Over.pullback (D.map oo.hom)).obj Wₙ =>
      z.left ≫ pullback.fst wn (D.map oo.hom)) h1
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, Rₙ, Wₙ,
      Over.mk_hom, pullback.lift_fst, hεWfst, reassoc_of% hεRfst, sₙ,
      Over.homMk_left] at h2
    exact h2
  have htoSq : tO ≫ bW = bR ≫ tn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, htOl]
    have h1 : tOO ≫ εWO.hom = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map tₙ := by
      rw [htOOdef]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h2 := congrArg (fun z : Over.mk rO ⟶ (Over.pullback (D.map oo.hom)).obj Wₙ =>
      z.left ≫ pullback.fst wn (D.map oo.hom)) h1
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, Rₙ, Wₙ,
      Over.mk_hom, pullback.lift_fst, hεWfst, reassoc_of% hεRfst, tₙ,
      Over.homMk_left] at h2
    exact h2
  have hsoSite : IsPullback bR sO sn bW := by
    apply IsPullback.of_map yoneda hsoSq.symm
    apply IsPullback.of_bot (v₂₂ := wn) ?_
      (by rw [← yoneda.map_comp, ← yoneda.map_comp, hsoSq]) hWO.flip
    rw [hsOW]
    exact hRO.flip
  have htoSite : IsPullback bR tO tn bW := by
    apply IsPullback.of_map yoneda htoSq.symm
    apply IsPullback.of_bot (v₂₂ := wn) ?_
      (by rw [← yoneda.map_comp, ← yoneda.map_comp, htoSq]) hWO.flip
    rw [htOW, htn]
    exact hRO.flip
  have hsOEtale : Etale (Q.map sO) := by
    let : Etale (Q.map sn) := hsnEtale
    exact (etale_iff_pullback_of_isPullback (hsoSite.map Q)).mpr inferInstance
  have htOEtale : Etale (Q.map tO) := by
    let : Etale (Q.map tn) := htnEtale
    exact (etale_iff_pullback_of_isPullback (htoSite.map Q)).mpr inferInstance
  have hWOAff : IsAffine (Q.obj WO) := by
    let : IsAffine (Q.obj Wn) := hWnAff
    let : _root_.AlgebraicGeometry.IsAffineHom (Q.map bW) := hoAff.2.property wn wO bW hWO
    exact isAffine_of_isAffineHom (Q.map bW)
  have hWOAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS WO
  have hROAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS RO
  have hwOFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wO :=
    isFinitePresentation_of_isPullback B S hS hWOAlg hWnAlg (hD oo.left) (hD nn)
      hWO.flip hWnFp
  have hrOFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rO :=
    isFinitePresentation_of_isPullback B S hS hROAlg hRnAlg (hD oo.left) (hD nn)
      hRO.flip hRnFp
  have hROqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS rO
    (hD oo.left) (hQc oo.left) hrOFp
  -- reflexivity, symmetry and transitivity of the descended relation
  have hsOO : εRO.hom ≫ (Over.pullback (D.map oo.hom)).map sₙ = sOO ≫ εWO.hom := by
    rw [hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have htOO : εRO.hom ≫ (Over.pullback (D.map oo.hom)).map tₙ = tOO ≫ εWO.hom := by
    rw [htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨rflO, hrflOdef⟩ : ∃ z : Over.mk wO ⟶ Over.mk rO, z = εWO.hom ≫ rrO ≫ εRO.inv :=
    ⟨_, rfl⟩
  have hrflS : rflO ≫ sOO = 𝟙 (Over.mk wO) := by
    rw [hrflOdef, hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrrOs]
    rw [show (Over.pullback (D.map oo.hom)).map (𝟙 Wₙ) = 𝟙 _ from
      (Over.pullback (D.map oo.hom)).map_id Wₙ, Category.id_comp, Iso.hom_inv_id]
  have hrflT : rflO ≫ tOO = 𝟙 (Over.mk wO) := by
    rw [hrflOdef, htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrrOt]
    rw [show (Over.pullback (D.map oo.hom)).map (𝟙 Wₙ) = 𝟙 _ from
      (Over.pullback (D.map oo.hom)).map_id Wₙ, Category.id_comp, Iso.hom_inv_id]
  obtain ⟨symO, hsymOdef⟩ : ∃ z : Over.mk rO ⟶ Over.mk rO, z = εRO.hom ≫ riO ≫ εRO.inv :=
    ⟨_, rfl⟩
  have hsymS : symO ≫ sOO = tOO := by
    rw [hsymOdef, hsOOdef, htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hriOs]
  have hsymT : symO ≫ tOO = sOO := by
    rw [hsymOdef, htOOdef, hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hriOt]
  let rflSite : WO ⟶ RO := yoneda.preimage rflO.left
  have hrflSite₁ : rflSite ≫ sO = 𝟙 WO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, hsOl, yoneda.map_id]
    simpa only [Over.comp_left, Over.id_left, Over.mk_left] using
      congrArg (fun z => z.left) hrflS
  have hrflSite₂ : rflSite ≫ tO = 𝟙 WO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, htOl, yoneda.map_id]
    simpa only [Over.comp_left, Over.id_left, Over.mk_left] using
      congrArg (fun z => z.left) hrflT
  let symSite : RO ⟶ RO := yoneda.preimage symO.left
  have hsymSite₁ : symSite ≫ sO = tO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, hsOl, htOl]
    simpa only [Over.comp_left] using congrArg (fun z => z.left) hsymS
  have hsymSite₂ : symSite ≫ tO = sO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, htOl, hsOl]
    simpa only [Over.comp_left] using congrArg (fun z => z.left) hsymT
  have hpoCond : yoneda.map (pullback.fst tO sO) ≫ yoneda.map tO =
      yoneda.map (pullback.snd tO sO) ≫ yoneda.map sO := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, pullback.condition]
  let Pₒ : Over (D.obj oo.left) := Over.mk (yoneda.map (pullback.fst tO sO) ≫ rO)
  let cfstₒ : Pₒ ⟶ Over.mk rO := Over.homMk (yoneda.map (pullback.fst tO sO)) rfl
  let csndₒ : Pₒ ⟶ Over.mk rO := Over.homMk (yoneda.map (pullback.snd tO sO)) (by
    show yoneda.map (pullback.snd tO sO) ≫ rO = yoneda.map (pullback.fst tO sO) ≫ rO
    calc yoneda.map (pullback.snd tO sO) ≫ rO
        = yoneda.map (pullback.snd tO sO) ≫ yoneda.map sO ≫ wO := by rw [hsOW]
      _ = yoneda.map (pullback.fst tO sO) ≫ yoneda.map tO ≫ wO := by
            rw [← Category.assoc, ← Category.assoc, ← hpoCond]
      _ = yoneda.map (pullback.fst tO sO) ≫ rO := by rw [htOW])
  have hcommₒ : cfstₒ ≫ tOO = csndₒ ≫ sOO := by
    apply Over.OverMorphism.ext
    simpa only [Over.comp_left, cfstₒ, csndₒ, Over.homMk_left, hsOl, htOl] using hpoCond
  have hPₒ : IsPullback cfstₒ csndₒ tOO sOO := by
    apply IsPullback.of_map (Over.forget (D.obj oo.left)) hcommₒ
    rw [show ((Over.forget (D.obj oo.left)).map tOO) = yoneda.map tO from htOl.symm,
      show ((Over.forget (D.obj oo.left)).map sOO) = yoneda.map sO from hsOl.symm]
    exact (IsPullback.of_hasPullback tO sO).map yoneda
  have hpbcn : IsPullback ((Over.pullback (D.map oo.hom)).map cn.fst)
      ((Over.pullback (D.map oo.hom)).map cn.snd)
      ((Over.pullback (D.map oo.hom)).map tₙ)
      ((Over.pullback (D.map oo.hom)).map sₙ) :=
    (overPullbackCone_isPullback tₙ sₙ).map (Over.pullback (D.map oo.hom))
  let ζ : Pₒ ⟶ (Over.pullback (D.map oo.hom)).obj cn.pt :=
    hpbcn.lift (cfstₒ ≫ εRO.hom) (csndₒ ≫ εRO.hom) (by
      simpa only [Category.assoc, ← htOO, ← hsOO] using
        congrArg (fun z : Pₒ ⟶ Over.mk wO => z ≫ εWO.hom) hcommₒ)
  have hζfst : ζ ≫ (Over.pullback (D.map oo.hom)).map cn.fst = cfstₒ ≫ εRO.hom :=
    hpbcn.lift_fst _ _ _
  have hζsnd : ζ ≫ (Over.pullback (D.map oo.hom)).map cn.snd = csndₒ ≫ εRO.hom :=
    hpbcn.lift_snd _ _ _
  obtain ⟨cmpO, hcmpOdef⟩ : ∃ z : Pₒ ⟶ Over.mk rO, z = ζ ≫ rcO ≫ εRO.inv := ⟨_, rfl⟩
  have hcmpS : cmpO ≫ sOO = cfstₒ ≫ sOO := by
    rw [hcmpOdef, hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrcOs,
      Functor.map_comp, reassoc_of% hζfst]
  have hcmpT : cmpO ≫ tOO = csndₒ ≫ tOO := by
    rw [hcmpOdef, htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrcOt,
      Functor.map_comp, reassoc_of% hζsnd]
  let cmpSite : pullback tO sO ⟶ RO := yoneda.preimage cmpO.left
  have hcmpSite₁ : cmpSite ≫ sO = pullback.fst tO sO ≫ sO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, yoneda.map_preimage, hsOl]
    simpa only [Over.comp_left, cfstₒ, Over.homMk_left] using
      congrArg (fun z => z.left) hcmpS
  have hcmpSite₂ : cmpSite ≫ tO = pullback.snd tO sO ≫ tO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, yoneda.map_preimage, htOl]
    simpa only [Over.comp_left, csndₒ, Over.homMk_left] using
      congrArg (fun z => z.left) hcmpT
  -- the atlas of the space compared with the descended relation
  let awO : W ⟶ WO := yoneda.preimage (hWO.flip.lift (yoneda.map awn)
    (pW ≫ limit.π D oo.left) (by rw [Category.assoc, limit.w]; exact hWnlim.w))
  let arO : KR ⟶ RO := yoneda.preimage (hRO.flip.lift (yoneda.map arn)
    (pR ≫ limit.π D oo.left) (by rw [Category.assoc, limit.w]; exact hRnlim.w))
  have hWOlim : IsPullback (yoneda.map awO) pW wO (limit.π D oo.left) := by
    have hh : IsPullback (yoneda.map awn) pW wn (limit.π D oo.left ≫ D.map oo.hom) := by
      rw [limit.w]
      exact hWnlim
    simpa only [awO, yoneda.map_preimage] using hh.of_right' hWO.flip
  have hROlim : IsPullback (yoneda.map arO) pR rO (limit.π D oo.left) := by
    have hh : IsPullback (yoneda.map arn) pR rn (limit.π D oo.left ≫ D.map oo.hom) := by
      rw [limit.w]
      exact hRnlim
    simpa only [arO, yoneda.map_preimage] using hh.of_right' hRO.flip
  have hawOb : awO ≫ bW = awn := by
    apply yoneda.map_injective
    simp [awO]
  have harOb : arO ≫ bR = arn := by
    apply yoneda.map_injective
    simp [arO]
  have hsOCompat : arO ≫ sO = kt ≫ awO := by
    apply yoneda.map_injective
    apply hWO.hom_ext
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, hsOW,
        hWOlim.w, hROlim.w, ← Category.assoc, ht]
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc,
        ← yoneda.map_comp sO bW, ← yoneda.map_comp awO bW, hsoSq, hawOb, yoneda.map_comp,
        ← Category.assoc, ← yoneda.map_comp arO bR, harOb, ← yoneda.map_comp, hsnCompat,
        yoneda.map_comp]
  have htOCompat : arO ≫ tO = ks ≫ awO := by
    apply yoneda.map_injective
    apply hWO.hom_ext
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, htOW,
        hWOlim.w, hROlim.w, ← Category.assoc, hs]
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc,
        ← yoneda.map_comp tO bW, ← yoneda.map_comp awO bW, htoSq, hawOb, yoneda.map_comp,
        ← Category.assoc, ← yoneda.map_comp arO bR, harOb, ← yoneda.map_comp, htnCompat,
        yoneda.map_comp]
  have hsqsO : IsPullback arO kt sO awO := by
    apply IsPullback.of_map yoneda hsOCompat
    apply IsPullback.of_bot _
      (by simpa only [Functor.map_comp] using congrArg yoneda.map hsOCompat) hWOlim
    simpa only [ht, hsOW] using hROlim
  have hsqtO : IsPullback arO ks tO awO := by
    apply IsPullback.of_map yoneda htOCompat
    apply IsPullback.of_bot _
      (by simpa only [Functor.map_comp] using congrArg yoneda.map htOCompat) hWOlim
    simpa only [hs, htOW] using hROlim
  -- joint monicity of the descended relation
  have hρcomm : yoneda.map sO ≫ wO = yoneda.map tO ≫ wO := by rw [hsOW, htOW]
  let KWO := atlasKernelPair B S hS wO (hD oo.left).diagonal_representable
  let ρ : RO ⟶ KWO.R := yoneda.preimage
    (KWO.kernelPair.lift (yoneda.map sO) (yoneda.map tO) hρcomm)
  have hρl : yoneda.map ρ =
      KWO.kernelPair.lift (yoneda.map sO) (yoneda.map tO) hρcomm := yoneda.map_preimage _
  have hρs : ρ ≫ KWO.s = sO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hρl]
    exact KWO.kernelPair.lift_fst _ _ _
  have hρt : ρ ≫ KWO.t = tO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hρl]
    exact KWO.kernelPair.lift_snd _ _ _
  have _ : IsIso εRO.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (D.obj oo.left)).map εRO.hom))
  have hνmono : Mono (εRO.hom.left ≫
      ((Over.pullback (D.map oo.hom)).map ψ).left) := by
    exact mono_comp' (IsIso.mono_of_iso _) (Over.mono_left_of_mono _)
  have hνfst : εRO.hom.left ≫ ((Over.pullback (D.map oo.hom)).map ψ).left ≫
      pullback.fst Zₙ.hom (D.map oo.hom) = yoneda.map bR ≫ yoneda.map ψ₀ := by
    simp only [Over.pullback_map_left, Rₙ, Over.mk_hom,
      pullback.lift_fst, ψ, Over.homMk_left, reassoc_of% hεRfst]
  have hνsnd : εRO.hom.left ≫ ((Over.pullback (D.map oo.hom)).map ψ).left ≫
      pullback.snd Zₙ.hom (D.map oo.hom) = rO := by
    simp only [Over.pullback_map_left, pullback.lift_snd]
    exact εRO.hom.w
  have hρmono : Mono (yoneda.map ρ) := by
    refine ⟨fun {T} a b hab => ?_⟩
    have ha : a ≫ yoneda.map sO = b ≫ yoneda.map sO := by
      rw [← hρs, yoneda.map_comp]
      simp only [← Category.assoc]
      rw [hab]
    have hb : a ≫ yoneda.map tO = b ≫ yoneda.map tO := by
      rw [← hρt, yoneda.map_comp]
      simp only [← Category.assoc]
      rw [hab]
    apply (cancel_mono (εRO.hom.left ≫ ((Over.pullback (D.map oo.hom)).map ψ).left)).mp
    apply pullback.hom_ext
    · simp only [Category.assoc, hνfst]
      apply KWn.kernelPair.hom_ext
      · simp only [Category.assoc, ← yoneda.map_comp ψ₀ KWn.s, hψs,
          ← yoneda.map_comp bR sn, ← hsoSq, yoneda.map_comp]
        simp only [← Category.assoc]
        rw [ha]
      · simp only [Category.assoc, ← yoneda.map_comp ψ₀ KWn.t, hψt,
          ← yoneda.map_comp bR tn, ← htoSq, yoneda.map_comp]
        simp only [← Category.assoc]
        rw [hb]
    · simp only [Category.assoc, hνsnd]
      rw [← hsOW]
      simp only [← Category.assoc]
      rw [ha]
  have hjmO : JointlyMono₂ ((Over.post (X := B.obj hS) B.inclusion).map sO)
      ((Over.post (X := B.obj hS) B.inclusion).map tO) :=
    jointlyMono₂_of_mono_to_kernelPair B S hS wO KWO.s KWO.t KWO.kernelPair
      sO tO ρ hρs hρt hρmono
  obtain ⟨Yᵢ, hYᵢalg, hYᵢfp, hYᵢiso⟩ := exists_model_of_descended_presentation
    B S hS hZ D oo.left hLim (hD oo.left) (hQc oo.left) (hQs oo.left) Y hY w hws hwe
    kt ks hwk hWOAff sO tO hsOEtale htOEtale hjmO rflSite hrflSite₁ hrflSite₂
    symSite hsymSite₁ hsymSite₂ cmpSite hcmpSite₁ hcmpSite₂ wO hρcomm hwOFp hROqc
    awO arO (by rw [← hpWDef]; exact hWOlim) hsqsO hsqtO
  exact ⟨oo.left, Yᵢ, hYᵢalg, hYᵢfp, hYᵢiso⟩

/-- **Essential surjectivity, cofinality-free.** Every algebraic space of finite presentation over
the limit descends to a finite stage, for a system with fewer stages than the cutoff and uniformly
bounded base changes. -/
public theorem exists_model_of_finitePresentation_of_baseChangeSizeBounded
    (Y : Over (limit D))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom) :
    ∃ (i : I) (Yᵢ : Over (D.obj i)),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
        Nonempty (Y ≅ (Over.pullback (limit.π D i)).obj Yᵢ)  := by
  classical
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨U₀, p₀, hU₀, hs₀, he₀⟩ := exists_affine_etale_atlas B S hS
    (D.obj i) (hD i) (hQc i)
  let U₀' : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hp₀ := represented_etale_of_isEtale B S hS p₀ he₀
  obtain ⟨U, p, q, hp⟩ :=
    isAffineHom_limitπ_of_baseChangeSizeBounded B S hS D hAffine hSizeB hν hHomSizeB hB i U₀' p₀
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) Q
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : E.presheaf.IsStableUnderBaseChange := E.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : E.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition E (etaleInverseImageIsStableUnderComposition _)
  have hs : P.presheaf p := P.presheaf.of_isPullback hp.flip hs₀
  have he : E.presheaf p := E.presheaf.of_isPullback hp.flip hp₀
  have hX := AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_baseChangeSizeBounded B S hS D hSizeB
      hν hHomSizeB hD hAffine hB
  have hXqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    hX (hQs i)
    (isQuasiSeparated_of_isAffineHom B S hS hX (hD i) (limit.π D i)
      (isAffineHom_limitπ_of_baseChangeSizeBounded B S hS D hAffine hSizeB hν hHomSizeB hB i))
  have hYqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS hZ hY hXqs hFp.2.2
  obtain ⟨W, w, g, hws, hwe, hw, hg⟩ :=
    exists_affine_finitePresentation_chart B S hS hX hY Y.hom hFp U p hs he
  let K := atlasKernelPair B S hS w hY.diagonal_representable
  have hKt := atlasKernelPair_target_finitePresentation B S hS hZ hY hYqs W w hwe
  have hKg : AlgebraicGeometry.FinitePresentation (Q.map (K.s ≫ g)) := by
    let : LocallyOfFinitePresentation (Q.map K.s) := hKt.1
    let : QuasiCompact (Q.map K.s) := hKt.2.1
    let : QuasiSeparated (Q.map K.s) := hKt.2.2
    let : LocallyOfFinitePresentation (Q.map g) := hg.1
    let : QuasiCompact (Q.map g) := hg.2.1
    let : QuasiSeparated (Q.map g) := hg.2.2
    rw [Q.map_comp]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W.obj) := W.property
  obtain ⟨j, Wj, wj, aw, hwj, hWjaff, hWmodel⟩ :=
      exists_affine_site_model_over_affine_chart_of_baseChangeSizeBounded
    B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB i U₀' p₀ hp₀ U p q hp W.obj g hg
  obtain ⟨k, Rk, rk, ar, hrk, hRmodel⟩ :=
      exists_site_model_over_affine_chart_of_baseChangeSizeBounded
    B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB i U₀' p₀ hp₀ U p q hp
      K.R (K.s ≫ g) hKg
  let l := IsCofiltered.min j.left k.left
  let ej : l ⟶ j.left := IsCofiltered.minToLeft _ _
  let ek : l ⟶ k.left := IsCofiltered.minToRight _ _
  let pW := yoneda.map g ≫ p
  let pR := yoneda.map (K.s ≫ g) ≫ p
  obtain ⟨WlA, wl, bl, hbl⟩ := hAffine ej ⟨Wj, hWjaff⟩ wj
  let Wl := WlA.obj
  have hwl : AlgebraicGeometry.Space.IsFinitePresentation B S hS wl :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wj)
      (hD l) (hD j.left) hbl.flip hwj
  let awl : W.obj ⟶ Wl := yoneda.preimage (hbl.flip.lift (yoneda.map aw)
    (pW ≫ limit.π D l) (by rw [Category.assoc, limit.w]; exact hWmodel.w))
  have hWl : IsPullback (yoneda.map awl) pW wl (limit.π D l) := by
    have hh : IsPullback (yoneda.map aw) pW wj (limit.π D l ≫ D.map ej) := by
      rw [limit.w]
      exact hWmodel
    simpa only [awl, yoneda.map_preimage] using hh.of_right' hbl.flip
  obtain ⟨Rl, rl, arl, hrl, hRl⟩ := advance_represented_model B S hS
    (hD l) (hD k.left) rk ar pR (limit.π D l) (D.map ek) (limit.π D k.left)
    (limit.w D ek) (hAffine ek) hrk hRmodel
  let KW := atlasKernelPair B S hS wl (hD l).diagonal_representable
  have hWlAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl
  have hKWAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS KW.R
  have hKWt : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map KW.s) :=
    isFinitePresentation_of_isPullback B S hS hKWAlg hWlAlg hWlAlg (hD l)
      KW.kernelPair.flip hwl
  let vKW := yoneda.map KW.s ≫ wl
  have hKWfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS vKW :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hKWAlg hWlAlg (hD l)
      (yoneda.map KW.s) wl hKWt hwl
  have ht : yoneda.map K.s ≫ pW = pR := by
    simp only [pW, pR, Functor.map_comp, Category.assoc]
  have hs : yoneda.map K.t ≫ pW = pR := by
    rw [← ht]
    simpa only [pW, hw, Category.assoc] using
      congrArg (fun t => t ≫ Y.hom) K.kernelPair.w.symm
  let b : yoneda.obj K.R ⟶ yoneda.obj KW.R := KW.kernelPair.lift
    (yoneda.map K.s ≫ yoneda.map awl) (yoneda.map K.t ≫ yoneda.map awl) (by
      simp only [Category.assoc, hWl.w]
      rw [← Category.assoc, ht, ← Category.assoc, hs])
  have hb : b ≫ vKW = pR ≫ limit.π D l := by
    simp only [b, vKW, IsPullback.lift_fst_assoc]
    rw [Category.assoc, hWl.w, ← Category.assoc, ht]
  let source := Over.mk rl
  let target := Over.mk vKW
  let er : Over.mk pR ≅ (Over.pullback (limit.π D l)).obj source :=
    Over.isoMk hRl.isoPullback (by exact hRl.isoPullback_hom_snd)
  let f : (Over.pullback (limit.π D l)).obj source ⟶
      (Over.pullback (limit.π D l)).obj target :=
    Over.homMk (pullback.lift (er.inv.left ≫ b)
      (pullback.snd rl (limit.π D l)) (by
        show (er.inv.left ≫ b) ≫ vKW = _
        rw [Category.assoc, hb, ← Category.assoc]
        exact congrArg (fun t => t ≫ limit.π D l) er.inv.w)) (by simp [source, target])
  obtain ⟨m, em, gm, αm, βm, hαm, hβm, hgm⟩ :=
      exists_morphism_after_baseChange_of_baseChangeSizeBounded
    B S hS hZ D hD hAffine hQc hQs hSizeB hν hHomSizeB hB l source target
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rl) hKWAlg hrl hKWfp f
  have hαmEq := iteratedBaseChangeIso_unique (D.map em) (limit.π D m) (limit.π D l)
    (limit.w D em) source αm hαm
  have hβmEq := iteratedBaseChangeIso_unique (D.map em) (limit.π D m) (limit.π D l)
    (limit.w D em) target βm hβm
  rw [hαmEq, hβmEq] at hgm
  have hmAffine := ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS (D.map em)
    (hD m) (hD l)).out 2 1).mp (hAffine em)
  let Rm := hmAffine.1.pullback rl
  let Wm := hmAffine.1.pullback wl
  let rm := hmAffine.1.fst rl
  let wm := hmAffine.1.fst wl
  have hRm : IsPullback rm (yoneda.map (hmAffine.1.snd rl)) (D.map em) rl :=
    hmAffine.1.isPullback rl
  have hWm : IsPullback wm (yoneda.map (hmAffine.1.snd wl)) (D.map em) wl :=
    hmAffine.1.isPullback wl
  have hWmAffineHom : _root_.AlgebraicGeometry.IsAffineHom (Q.map (hmAffine.1.snd wl)) :=
    hmAffine.2.property wl wm (hmAffine.1.snd wl) hWm
  have hWmAffine : IsAffine (Q.obj Wm) := by
    let : IsAffine (Q.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
        WlA)) := WlA.property
    let : _root_.AlgebraicGeometry.IsAffineHom (Q.map (hmAffine.1.snd wl)) := hWmAffineHom
    exact isAffine_of_isAffineHom (Q.map (hmAffine.1.snd wl))
  have hRmFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rm :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rm)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rl) (hD m) (hD l) hRm.flip hrl
  have hWmFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wm :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wm)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl) (hD m) (hD l) hWm.flip hwl
  let st : target ⟶ Over.mk wl := Over.homMk (yoneda.map KW.s) rfl
  let tt : target ⟶ Over.mk wl := Over.homMk (yoneda.map KW.t) KW.kernelPair.w.symm
  let sm₀ := gm ≫ (Over.pullback (D.map em)).map st
  let tm₀ := gm ≫ (Over.pullback (D.map em)).map tt
  let sm : Rm ⟶ Wm := yoneda.preimage
    (hRm.flip.isoPullback.hom ≫ sm₀.left ≫ hWm.flip.isoPullback.inv)
  let tm : Rm ⟶ Wm := yoneda.preimage
    (hRm.flip.isoPullback.hom ≫ tm₀.left ≫ hWm.flip.isoPullback.inv)
  have hsm : yoneda.map sm ≫ wm = rm := by
    simp only [sm, yoneda.map_preimage, Category.assoc, IsPullback.isoPullback_inv_snd]
    rw [show sm₀.left ≫ pullback.snd wl (D.map em) =
      pullback.snd rl (D.map em) from sm₀.w, hRm.flip.isoPullback_hom_snd]
  have htm : yoneda.map tm ≫ wm = rm := by
    simp only [tm, yoneda.map_preimage, Category.assoc, IsPullback.isoPullback_inv_snd]
    rw [show tm₀.left ≫ pullback.snd wl (D.map em) =
      pullback.snd rl (D.map em) from tm₀.w, hRm.flip.isoPullback_hom_snd]
  let arm : K.R ⟶ Rm := yoneda.preimage (hRm.flip.lift (yoneda.map arl)
    (pR ≫ limit.π D m) (by rw [Category.assoc, limit.w]; exact hRl.w))
  let awm : W.obj ⟶ Wm := yoneda.preimage (hWm.flip.lift (yoneda.map awl)
    (pW ≫ limit.π D m) (by rw [Category.assoc, limit.w]; exact hWl.w))
  have hRlim : IsPullback (yoneda.map arm) pR rm (limit.π D m) := by
    have hh : IsPullback (yoneda.map arl) pR rl (limit.π D m ≫ D.map em) := by
      rw [limit.w]
      exact hRl
    simpa only [arm, yoneda.map_preimage] using hh.of_right' hRm.flip
  have hWlim : IsPullback (yoneda.map awm) pW wm (limit.π D m) := by
    have hh : IsPullback (yoneda.map awl) pW wl (limit.π D m ≫ D.map em) := by
      rw [limit.w]
      exact hWl
    simpa only [awm, yoneda.map_preimage] using hh.of_right' hWm.flip
  have harm : yoneda.map arm ≫ yoneda.map (hmAffine.1.snd rl) = yoneda.map arl := by
    simp [arm]
  have hawm : yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl) = yoneda.map awl := by
    simp [awm]
  have harPB : yoneda.map arm ≫ hRm.flip.isoPullback.hom =
      er.hom.left ≫
        (iteratedBaseChangeIso (D.map em) (limit.π D m) (limit.π D l)
          (limit.w D em) source).inv.left ≫
          pullback.fst ((Over.pullback (D.map em)).obj source).hom (limit.π D m) := by
    apply pullback.hom_ext
    · simp [arm, er, source, iteratedBaseChangeIso, Category.assoc]
    · simp [arm, er, source, iteratedBaseChangeIso, Category.assoc]
  have hgm' : yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
      pullback.fst vKW (D.map em) = b := by
    have hh := congrArg (fun z => er.hom ≫
      (iteratedBaseChangeIso (D.map em) (limit.π D m) (limit.π D l)
        (limit.w D em) source).inv ≫ z) hgm
    simp only [Iso.inv_hom_id_assoc] at hh
    have hh' := congrArg (fun z => z.left ≫ pullback.fst vKW (limit.π D l)) hh
    have her : er.hom.left ≫ er.inv.left = 𝟙 _ :=
      congrArg (fun z => z.left) er.hom_inv_id
    simp only [Over.comp_left, Category.assoc] at hh'
    have hβfst := iteratedBaseChangeIso_hom_fst (D.map em) (limit.π D m)
      (limit.π D l) (limit.w D em) target
    change (iteratedBaseChangeIso (D.map em) (limit.π D m) (limit.π D l)
      (limit.w D em) target).hom.left ≫ pullback.fst vKW (limit.π D l) = _ at hβfst
    rw [hβfst] at hh'
    rw [reassoc_of% harPB]
    simpa only [source, target,
      Over.pullback_map_left, Over.pullback_obj_hom, Over.mk_hom, f,
      Over.homMk_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      her, reassoc_of% her, Category.id_comp] using hh'.symm
  have hsmCompat : arm ≫ sm = K.s ≫ awm := by
    apply yoneda.map_injective
    apply hWm.hom_ext
    · simp only [Functor.map_comp, Category.assoc, hsm, hRlim.w,
        hWlim.w]
      rw [← Category.assoc, ht]
    · simp only [Functor.map_comp, Category.assoc, sm, yoneda.map_preimage,
        IsPullback.isoPullback_inv_fst]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫
        (gm ≫ (Over.pullback (D.map em)).map st).left ≫
          pullback.fst wl (D.map em) =
        yoneda.map K.s ≫ yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl)
      simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, hawm, source, target, st, Over.mk_hom, Over.homMk_left]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
        pullback.fst vKW (D.map em) ≫ yoneda.map KW.s = _
      rw [reassoc_of% hgm']
      simp [b]
  have htmCompat : arm ≫ tm = K.t ≫ awm := by
    apply yoneda.map_injective
    apply hWm.hom_ext
    · simp only [Functor.map_comp, Category.assoc, htm, hRlim.w,
        hWlim.w]
      rw [← Category.assoc, hs]
    · simp only [Functor.map_comp, Category.assoc, tm, yoneda.map_preimage,
        IsPullback.isoPullback_inv_fst]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫
        (gm ≫ (Over.pullback (D.map em)).map tt).left ≫
          pullback.fst wl (D.map em) =
        yoneda.map K.t ≫ yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl)
      simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, hawm, source, target, tt, Over.mk_hom, Over.homMk_left]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
        pullback.fst vKW (D.map em) ≫ yoneda.map KW.t = _
      rw [reassoc_of% hgm']
      simp [b]
  have hsmSquare : IsPullback arm K.s sm awm := by
    apply IsPullback.of_map yoneda hsmCompat
    apply IsPullback.of_bot _ (by
      simpa only [Functor.map_comp] using congrArg yoneda.map hsmCompat) hWlim
    simpa only [hsm, ht] using hRlim
  have htmSquare : IsPullback arm K.t tm awm := by
    apply IsPullback.of_map yoneda htmCompat
    apply IsPullback.of_bot _ (by
      simpa only [Functor.map_comp] using congrArg yoneda.map htmCompat) hWlim
    simpa only [htm, hs] using hRlim
  have hRmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rm
  have hWmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wm
  have hSmFp := finitePresentation_of_yoneda B S hS sm
    (isFinitePresentation_overHom B S hS hZ (hD m) (hQc m) (hQs m)
      (Over.mk rm) (Over.mk wm) hRmAlg hWmAlg hRmFp hWmFp
      (Over.homMk (yoneda.map sm) hsm))
  have hTmFp := finitePresentation_of_yoneda B S hS tm
    (isFinitePresentation_overHom B S hS hZ (hD m) (hQc m) (hQs m)
      (Over.mk rm) (Over.mk wm) hRmAlg hWmAlg hRmFp hWmFp
      (Over.homMk (yoneda.map tm) htm))
  let WmA : AlgebraicGeometry.BigAffineFppf B S hS := ⟨Wm, hWmAffine⟩
  let : Etale ((Over.pullback (Q.map awm)).obj (Over.mk (Q.map sm))).hom :=
    (etale_iff_pullback_of_isPullback (hsmSquare.map Q)).mp
      (hwe.property w (yoneda.map K.t) K.s K.kernelPair.flip)
  let : Etale ((Over.pullback (Q.map awm)).obj (Over.mk (Q.map tm))).hom :=
    (etale_iff_pullback_of_isPullback (htmSquare.map Q)).mp
      (hwe.property w (yoneda.map K.s) K.t K.kernelPair)
  obtain ⟨js, hjs⟩ := eventually_etale_over_affine_chart_of_baseChangeSizeBounded B S hS
      hZ D hD hAffine
    hQc hQs hSizeB hν hHomSizeB hB m WmA wm W pW awm hWlim.flip (Over.mk (Q.map sm)) hSmFp
  obtain ⟨jt, hjt⟩ := eventually_etale_over_affine_chart_of_baseChangeSizeBounded B S hS
      hZ D hD hAffine
    hQc hQs hSizeB hν hHomSizeB hB m WmA wm W pW awm hWlim.flip (Over.mk (Q.map tm)) hTmFp
  let n := IsCofiltered.min js jt
  let as' := IsCofiltered.minToLeft js jt
  let at' := IsCofiltered.minToRight js jt
  let En := affineStageChartOverDiagramOfSizeBounded B S hS hZ D hD hAffine
    hQc hQs hSizeB hν hHomSizeB hB m WmA wm hAffine
  let Cn := affineStageChart B S hS D m WmA wm hAffine n
  have hsChart : Etale (pullback.snd (Q.map sm) (Q.map Cn.toChart)) := by
    let : Etale ((Over.pullback (Q.map (En.obj js).hom)).obj (Over.mk (Q.map sm))).hom := hjs
    exact etale_pullback_of_etale_pullback (Q.map (En.obj js).hom)
      (Q.map (En.map as').left) (Q.map (En.obj n).hom)
      (by rw [← Q.map_comp]; exact congrArg Q.map (En.map as').w) (Over.mk (Q.map sm))
  have htChart : Etale (pullback.snd (Q.map tm) (Q.map Cn.toChart)) := by
    let : Etale ((Over.pullback (Q.map (En.obj jt).hom)).obj (Over.mk (Q.map tm))).hom := hjt
    exact etale_pullback_of_etale_pullback (Q.map (En.obj jt).hom)
      (Q.map (En.map at').left) (Q.map (En.obj n).hom)
      (by rw [← Q.map_comp]; exact congrArg Q.map (En.map at').w) (Over.mk (Q.map tm))
  let Wn := Cn.U.obj
  let wn := Cn.toStage
  let Rn := pullback sm Cn.toChart
  let sn : Rn ⟶ Wn := pullback.snd sm Cn.toChart
  let br : Rn ⟶ Rm := pullback.fst sm Cn.toChart
  let rn := yoneda.map sn ≫ wn
  have hRn : IsPullback (yoneda.map br) rn rm (D.map n.hom) := by
    have hh := ((IsPullback.of_hasPullback sm Cn.toChart).map yoneda).paste_vert
      Cn.isPullback.flip
    simpa only [hsm] using hh
  let tn : Rn ⟶ Wn := yoneda.preimage (Cn.isPullback.lift rn
    (yoneda.map br ≫ yoneda.map tm) (by
      simp only [Category.assoc, htm]
      exact hRn.w.symm))
  have htn : yoneda.map tn ≫ wn = rn := by simp [tn, wn]
  have htnBr : br ≫ tm = tn ≫ Cn.toChart := by
    apply yoneda.map_injective
    simp [tn]
  have htnSquare : IsPullback br tn tm Cn.toChart := by
    apply IsPullback.of_map yoneda htnBr
    apply IsPullback.of_bot _ (by simpa only [Functor.map_comp] using congrArg yoneda.map htnBr)
      Cn.isPullback.flip
    simpa only [← show wn = Cn.toStage from rfl, htm, htn] using hRn
  have hsnEtale : Etale (Q.map sn) :=
    (etale_iff_pullback_of_isPullback ((IsPullback.of_hasPullback sm Cn.toChart).map Q)).mpr hsChart
  have htnEtale : Etale (Q.map tn) :=
    (etale_iff_pullback_of_isPullback (htnSquare.map Q)).mpr htChart
  have hRnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rn
  have hWnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wn
  have hRnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rn :=
    isFinitePresentation_of_isPullback B S hS hRnAlg hRmAlg (hD n.left) (hD m) hRn hRmFp
  have hWnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wn :=
    isFinitePresentation_of_isPullback B S hS hWnAlg hWmAlg (hD n.left) (hD m)
      Cn.isPullback.flip hWmFp
  let awn : W.obj ⟶ Wn := yoneda.preimage (Cn.isPullback.flip.lift (yoneda.map awm)
    (pW ≫ limit.π D n.left) (by rw [Category.assoc, limit.w]; exact hWlim.w))
  let arn : K.R ⟶ Rn := yoneda.preimage (hRn.lift (yoneda.map arm)
    (pR ≫ limit.π D n.left) (by rw [Category.assoc, limit.w]; exact hRlim.w))
  have hWnlim : IsPullback (yoneda.map awn) pW wn (limit.π D n.left) := by
    have hh : IsPullback (yoneda.map awm) pW wm (limit.π D n.left ≫ D.map n.hom) := by
      rw [limit.w]
      exact hWlim
    simpa only [awn, yoneda.map_preimage] using hh.of_right' Cn.isPullback.flip
  have hRnlim : IsPullback (yoneda.map arn) pR rn (limit.π D n.left) := by
    have hh : IsPullback (yoneda.map arm) pR rm (limit.π D n.left ≫ D.map n.hom) := by
      rw [limit.w]
      exact hRlim
    simpa only [arn, yoneda.map_preimage] using hh.of_right' hRn
  have hArnBr : yoneda.map arn ≫ yoneda.map br = yoneda.map arm := by simp [arn]
  have hAwnBw : yoneda.map awn ≫ yoneda.map Cn.toChart = yoneda.map awm := by simp [awn]
  have hsnCompat : arn ≫ sn = K.s ≫ awn := by
    apply yoneda.map_injective
    apply Cn.isPullback.hom_ext
    · simp only [Functor.map_comp, Category.assoc]
      show yoneda.map arn ≫ rn = yoneda.map K.s ≫ yoneda.map awn ≫ wn
      rw [hRnlim.w, hWnlim.w, ← Category.assoc, ht]
    · simp only [Functor.map_comp, Category.assoc]
      have hsn : sn ≫ Cn.toChart = br ≫ sm := pullback.condition.symm
      rw [← yoneda.map_comp sn Cn.toChart, hsn, yoneda.map_comp,
        ← Category.assoc, hArnBr, hAwnBw]
      exact congrArg yoneda.map hsmCompat
  have htnCompat : arn ≫ tn = K.t ≫ awn := by
    apply yoneda.map_injective
    apply Cn.isPullback.hom_ext
    · simp only [Functor.map_comp, Category.assoc]
      show yoneda.map arn ≫ yoneda.map tn ≫ wn =
        yoneda.map K.t ≫ yoneda.map awn ≫ wn
      rw [htn, hRnlim.w, hWnlim.w, ← Category.assoc, hs]
    · simp only [Functor.map_comp, Category.assoc]
      rw [← yoneda.map_comp tn Cn.toChart, ← htnBr, yoneda.map_comp,
        ← Category.assoc, hArnBr, hAwnBw]
      exact congrArg yoneda.map htmCompat
  have hsnSquare : IsPullback arn K.s sn awn := by
    apply IsPullback.of_map yoneda hsnCompat
    apply IsPullback.of_bot _ (by simpa only [Functor.map_comp] using congrArg yoneda.map hsnCompat)
      hWnlim
    simpa only [ht] using hRnlim
  have htnLimitSquare : IsPullback arn K.t tn awn := by
    apply IsPullback.of_map yoneda htnCompat
    apply IsPullback.of_bot _ (by simpa only [Functor.map_comp] using congrArg yoneda.map htnCompat)
      hWnlim
    simpa only [htn, hs] using hRnlim
  have hRnlim' : IsPullback (yoneda.map arn) (yoneda.map K.s ≫ w ≫ Y.hom)
      (yoneda.map sn ≫ wn) (limit.π D n.left) := by
    rw [show (yoneda.map K.s ≫ w ≫ Y.hom) = pR from by rw [← hw]; exact ht]
    exact hRnlim
  exact exists_model_of_stage_relation_of_baseChangeSizeBounded B S hS hZ D hD hAffine hQc hQs
      hSizeB hν hHomSizeB hB
    n.left hX Y hY w hws hwe K.s K.t K.kernelPair
    (show IsAffine (Q.obj Wn) from Cn.U.property) wn sn tn htn hsnEtale htnEtale
    hWnFp hRnFp awn arn (by rw [← hw]; exact hWnlim) hRnlim' hsnCompat htnCompat

end BaseChangeSizeBounded


/-! ### The chapter's convention on the site

The three statements of Stacks 07SK under the chapter's standing convention of Section 70.2
(tag 07SD), `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, in place of the bounds on the
index. The bounds are used above in exactly three places, each replaced here by the convention:
affineness of the projections from the limit (Stacks 07SF, part (1),
`AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits`); the limit of the
affine charts of the stages over a stage lying in the site, so that the underlying scheme functor
preserves it; and the limit being an algebraic space, which is the argument `hDlim`, supplied by
`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits`. Every
declaration below that differs from one above by this replacement carries the suffix `_conv`
(`Conv` for definitions, `_of_siteContainsBaseChangeLimits` for the three main results). -/

variable (hconv : AlgebraicGeometry.Space.SiteContainsBaseChangeLimits B S hS D)

variable (hDlim : AlgebraicGeometry.IsAlgebraicSpace B S hS (limit D))

omit hSize hHomSize in
include hconv in
private theorem affineStageChartMap_toStage_conv (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    yoneda.map (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
        (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toStage =
      (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toStage ≫ D.map e.left := by
  simp [affineStageChartMap]

omit hSize hHomSize in
include hconv in
private theorem affineStageChartMap_toChart_conv (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    yoneda.map (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toChart =
      yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart := by
  simp [affineStageChartMap]

omit hSize hHomSize in
include hconv in
private noncomputable def affineStageChartOverDiagramConv (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) :
    Over i₀ ⥤ Over ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) where
  obj j := Over.mk (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart
  map e := Over.homMk (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) (by
    apply yoneda.map_injective
    simpa only [yoneda.map_comp, Over.mk_left, Over.mk_hom] using
      affineStageChartMap_toChart_conv B S hS hZ D hD hAffine hQc hQs hconv
        i₀ U₀ q₀ hAff e)
  map_id j := by
    apply Over.OverMorphism.ext
    apply yoneda.map_injective
    apply (affineStageChart B S hS D i₀ U₀ q₀ hAff j).isPullback.hom_ext
    · simp [affineStageChartMap]
    · simp [affineStageChartMap]
  map_comp {j k l} e f := by
    apply Over.OverMorphism.ext
    apply yoneda.map_injective
    apply (affineStageChart B S hS D i₀ U₀ q₀ hAff l).isPullback.hom_ext
    · simp [affineStageChartMap, Category.assoc]
    · simp [affineStageChartMap, Category.assoc]

omit hSize hHomSize in
include hconv in
private noncomputable def affineStageChartConeConv (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) :
    Cone (affineStageChartOverDiagramConv B S hS hZ D hD hAffine hQc hQs hconv
      i₀ U₀ q₀ hAff) where
  pt := Over.mk q
  π := {
    app j := Over.homMk (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) (by
      apply yoneda.map_injective
      change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
          yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart = yoneda.map q
      simp [affineStageChartLift])
    naturality j k e := by
      simp only [Functor.const_obj_map]
      apply Over.OverMorphism.ext
      apply yoneda.map_injective
      apply (affineStageChart B S hS D i₀ U₀ q₀ hAff k).isPullback.hom_ext
      · change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h k) ≫
              (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toStage =
            yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j ≫
                affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
              (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toStage
        simp [affineStageChartLift, affineStageChartMap, Category.assoc, limit.w]
      · change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h k) ≫
              yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toChart =
            yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j ≫
                affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
              yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toChart
        simp [affineStageChartLift, affineStageChartMap, Category.assoc]
  }

omit hSize hHomSize in
include hconv in
private noncomputable def affineStageChartConeIsLimitConv (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) :
    IsLimit (affineStageChartConeConv B S hS hZ D hD hAffine hQc hQs hconv
      i₀ U₀ q₀ hAff U p q h) := by
  let E := affineStageChartOverDiagramConv B S hS hZ D hD hAffine hQc hQs hconv
    i₀ U₀ q₀ hAff
  let c := affineStageChartConeConv B S hS hZ D hD hAffine hQc hQs hconv
    i₀ U₀ q₀ hAff U p q h
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  apply isLimitOfReflects (Over.forget T)
  apply isLimitOfReflects yoneda
  let p' : (E ⋙ Over.forget T) ⋙ yoneda ⟶ Over.forget i₀ ⋙ D := {
    app j := (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toStage
    naturality j k e :=
      affineStageChartMap_toStage_conv B S hS hZ D hD hAffine hQc hQs hconv
        i₀ U₀ q₀ hAff e
  }
  let q' : (E ⋙ Over.forget T) ⋙ yoneda ⟶ (Functor.const _).obj (yoneda.obj T) := {
    app j := yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart
    naturality j k e := by
      simpa [E, T, affineStageChartOverDiagramConv] using
        (affineStageChartMap_toChart_conv B S hS hZ D hD hAffine hQc hQs hconv
          i₀ U₀ q₀ hAff e)
  }
  exact isLimit_of_cartesian_cone D i₀ (yoneda.obj T) q₀ _ _ p' q'
    (fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAff j).isPullback)
    p (yoneda.map q) h
    (fun j => by
      change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
          (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toStage = p ≫ limit.π D j.left
      simp [affineStageChartLift])
    (fun j => by
      change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
          yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart = yoneda.map q
      simp [affineStageChartLift])

omit hSize hHomSize in
include hconv in
/-- The diagram of affine charts over a stage satisfies the chapter's convention: through the
Yoneda embedding it is the diagram of base changes of the later stages along the chart, each
chart being such a base change. -/
private theorem limitInSite_affineStageChartOverDiagram_conv (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀) :
    AlgebraicGeometry.BigFppfOver.LimitInSite
      (affineStageChartOverDiagramConv B S hS hZ D hD hAffine hQc hQs hconv i₀ U₀ q₀ hAffine ⋙
        Over.forget _) := by
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let E := affineStageChartOverDiagramConv B S hS hZ D hD hAffine hQc hQs hconv i₀ U₀ q₀ hAffine
  let W : Over i₀ ⥤ AlgebraicGeometry.BigAffineFppf B S hS :=
    ObjectProperty.lift _ (E ⋙ Over.forget T)
      (fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.property)
  let e : W ⋙ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
      (Over.post (X := i₀) D ⋙ Over.pullback q₀) ⋙ Over.forget (yoneda.obj T) :=
    NatIso.ofComponents
      (fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.isoPullback)
      (fun {j k} f => by
        let Cj := affineStageChart B S hS D i₀ U₀ q₀ hAffine j
        let Ck := affineStageChart B S hS D i₀ U₀ q₀ hAffine k
        have hj₁ : Cj.isPullback.isoPullback.hom ≫ pullback.fst ((Over.post D).obj j).hom q₀ =
            Cj.toStage := Cj.isPullback.isoPullback_hom_fst
        have hj₂ : Cj.isPullback.isoPullback.hom ≫ pullback.snd ((Over.post D).obj j).hom q₀ =
            yoneda.map Cj.toChart := Cj.isPullback.isoPullback_hom_snd
        have hk₁ : Ck.isPullback.isoPullback.hom ≫ pullback.fst ((Over.post D).obj k).hom q₀ =
            Ck.toStage := Ck.isPullback.isoPullback_hom_fst
        have hk₂ : Ck.isPullback.isoPullback.hom ≫ pullback.snd ((Over.post D).obj k).hom q₀ =
            yoneda.map Ck.toChart := Ck.isPullback.isoPullback_hom_snd
        have hG₁ : ((Over.post (X := i₀) D ⋙ Over.pullback q₀) ⋙ Over.forget (yoneda.obj T)).map f ≫
            pullback.fst ((Over.post D).obj k).hom q₀ =
              pullback.fst ((Over.post D).obj j).hom q₀ ≫ D.map f.left :=
          pullback.lift_fst _ _ _
        have hG₂ : ((Over.post (X := i₀) D ⋙ Over.pullback q₀) ⋙ Over.forget (yoneda.obj T)).map f ≫
            pullback.snd ((Over.post D).obj k).hom q₀ = pullback.snd ((Over.post D).obj j).hom q₀ :=
          pullback.lift_snd _ _ _
        let Fm := (W ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙ yoneda).map f
        apply pullback.hom_ext
        · exact (Category.assoc _ _ _).trans ((congrArg (fun t => Fm ≫ t) hk₁).trans
            ((affineStageChartMap_toStage_conv B S hS hZ D hD hAffine hQc hQs hconv
              i₀ U₀ q₀ hAffine f).trans
            (((congrArg (fun t => t ≫ D.map f.left) hj₁).symm.trans
              (Category.assoc _ _ _)).trans
            ((congrArg (fun t => Cj.isPullback.isoPullback.hom ≫ t) hG₁).symm.trans
              (Category.assoc _ _ _).symm))))
        · exact (Category.assoc _ _ _).trans ((congrArg (fun t => Fm ≫ t) hk₂).trans
            ((affineStageChartMap_toChart_conv B S hS hZ D hD hAffine hQc hQs hconv
              i₀ U₀ q₀ hAffine f).trans
            (hj₂.symm.trans
            ((congrArg (fun t => Cj.isPullback.isoPullback.hom ≫ t) hG₂).symm.trans
              (Category.assoc _ _ _).symm)))))
  exact hconv i₀ U₀ q₀ W e

omit hSize hHomSize in
include hconv in
/-- The underlying scheme functor preserves the limit of the diagram of affine charts over a
stage, under the chapter's convention. -/
private noncomputable def isLimit_toScheme_affineStageChart_conv (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (c : Cone (affineStageChartOverDiagramConv B S hS hZ D hD hAffine hQc hQs hconv i₀ U₀ q₀
      hAffine ⋙ Over.forget _)) (hc : IsLimit c) :
    IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c) :=
  have := AlgebraicGeometry.BigFppfOver.preservesLimit_toScheme_of_limitInSite _
    (fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.property)
    (limitInSite_affineStageChartOverDiagram_conv B S hS hZ D hD hAffine hQc hQs hconv i₀ U₀ q₀)
  isLimitOfPreserves _ hc

omit hSize hHomSize in
include hconv in
private theorem eventually_eq_on_affine_chart_conv (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i₀)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ Z)
    (hf : f ≫ a = q₀) (hg : g ≫ a = q₀)
    (hfg : pullback.snd (limit.π D i₀) q₀ ≫ f =
      pullback.snd (limit.π D i₀) q₀ ≫ g) :
    ∃ j : Over i₀,
      yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ f =
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ g := by
  obtain ⟨U, p, q, h⟩ :=
    AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D hconv
      hAffine i₀ U₀ q₀
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let E := affineStageChartOverDiagramConv B S hS hZ D hD hAffine hQc hQs hconv
    i₀ U₀ q₀ hAffine
  let c := affineStageChartConeConv B S hS hZ D hD hAffine hQc hQs hconv
    i₀ U₀ q₀ hAffine _ p q h
  let hc := affineStageChartConeIsLimitConv B S hS hZ D hD hAffine hQc hQs hconv
    i₀ U₀ q₀ hAffine _ p q h
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
    fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.property
  have hh : yoneda.map q ≫ f = yoneda.map q ≫ g := by
    simpa using congrArg (fun k => h.isoPullback.hom ≫ k) hfg
  exact eventually_eq_homs_of_locallyOfFinitePresentation B S hS hZalg (hD i₀)
    a ha T q₀ E c
    (isLimit_toScheme_affineStageChart_conv B S hS hZ D hD hAffine hQc hQs hconv i₀ U₀ q₀
      ((Over.forget T).mapCone c)
      (isLimitOfPreserves (Over.forget T) hc))
    hE U.property f g hf hg hh

omit hSize hHomSize in
include hconv in
private theorem exists_hom_on_affine_chart_conv (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj U₀.obj ⟶ D.obj i₀)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i₀)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f : pullback (limit.π D i₀) q₀ ⟶ Z)
    (hf : f ≫ a = pullback.fst _ _ ≫ limit.π D i₀) :
    ∃ (j : Over i₀) (g : yoneda.obj
      (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.obj ⟶ Z),
      g ≫ a = (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toStage ≫ D.map j.hom ∧
      (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.lift
        (pullback.fst _ _ ≫ limit.π D j.left) (pullback.snd _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition) ≫ g = f := by
  obtain ⟨U, p, q, h⟩ :=
    AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D hconv
      hAffine i₀ U₀ q₀
  let E := affineStageChartOverDiagramConv B S hS hZ D hD hAffine hQc hQs hconv
    i₀ U₀ q₀ hAffine
  let c := affineStageChartConeConv B S hS hZ D hD hAffine hQc hQs hconv
    i₀ U₀ q₀ hAffine _ p q h
  let hc := affineStageChartConeIsLimitConv B S hS hZ D hD hAffine hQc hQs hconv
    i₀ U₀ q₀ hAffine _ p q h
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
    fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.property
  obtain ⟨j, g, hg, he⟩ := exists_hom_of_locallyOfFinitePresentation B S hS hZalg
    (hD i₀) a ha U₀.obj q₀ E c
    (isLimit_toScheme_affineStageChart_conv B S hS hZ D hD hAffine hQc hQs hconv i₀ U₀ q₀
      ((Over.forget U₀.obj).mapCone c)
      (isLimitOfPreserves (Over.forget U₀.obj) hc))
    hE U.property (h.isoPullback.hom ≫ f) (by
      show (h.isoPullback.hom ≫ f) ≫ a = yoneda.map q ≫ q₀
      rw [Category.assoc, hf, IsPullback.isoPullback_hom_fst_assoc]
      exact h.w)
  refine ⟨j, g, hg.trans (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.w.symm, ?_⟩
  apply (Iso.cancel_iso_hom_left h.isoPullback _ _).mp
  have hh : h.isoPullback.hom ≫
      (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.lift
        (pullback.fst _ _ ≫ limit.π D j.left) (pullback.snd _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition) =
      yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAffine _ p q h j) := by
    apply (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.hom_ext
    · simp [affineStageChartLift]
    · simp [affineStageChartLift]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ g) hh).trans he)

omit hSize hHomSize in
include hconv in
private theorem eventually_eq_on_affine_chart_over_conv (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    {G Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (b : D.obj i₀ ⟶ G)
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ Z)
    (hf : f ≫ a = q₀ ≫ b) (hg : g ≫ a = q₀ ≫ b)
    (hfg : pullback.snd (limit.π D i₀) q₀ ≫ f =
      pullback.snd (limit.π D i₀) q₀ ≫ g) :
    ∃ j : Over i₀,
      yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ f =
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ g := by
  obtain ⟨U, p, q, h⟩ :=
    AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D hconv
      hAffine i₀ U₀ q₀
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let E := affineStageChartOverDiagramConv B S hS hZ D hD hAffine hQc hQs hconv
    i₀ U₀ q₀ hAffine
  let c := affineStageChartConeConv B S hS hZ D hD hAffine hQc hQs hconv
    i₀ U₀ q₀ hAffine _ p q h
  let hc := affineStageChartConeIsLimitConv B S hS hZ D hD hAffine hQc hQs hconv
    i₀ U₀ q₀ hAffine _ p q h
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
    fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.property
  have hh : yoneda.map q ≫ f = yoneda.map q ≫ g := by
    simpa using congrArg (fun k => h.isoPullback.hom ≫ k) hfg
  exact eventually_eq_homs_of_locallyOfFinitePresentation B S hS hZalg hG
    a ha T (q₀ ≫ b) E c
    (isLimit_toScheme_affineStageChart_conv B S hS hZ D hD hAffine hQc hQs hconv i₀ U₀ q₀
      ((Over.forget T).mapCone c)
      (isLimitOfPreserves (Over.forget T) hc))
    hE U.property f g hf hg hh

omit hSize hHomSize in
include hconv in
private theorem exists_model_over_affine_chart_conv (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) :
    let c := affineStageChartConeConv B S hS hZ D hD hAffine hQc hQs hconv
      i U₀ p₀ hAffine U.obj p q hp
    ∃ (j : Over i) (Wj : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (affineStageChart B S hS D i U₀ p₀ hAffine j).U.obj)),
      AlgebraicGeometry.FinitePresentation Wj.hom ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
        (Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
            (c.π.app j).left)).obj Wj) := by
  dsimp only
  let E := affineStageChartOverDiagramConv B S hS hZ D hD hAffine hQc hQs hconv
    i U₀ p₀ hAffine
  let c := affineStageChartConeConv B S hS hZ D hD hAffine hQc hQs hconv
    i U₀ p₀ hAffine U.obj p q hp
  let hc := affineStageChartConeIsLimitConv B S hS hZ D hD hAffine hQc hQs hconv
    i U₀ p₀ hAffine U.obj p q hp
  let : IsConnected (Over i) := IsCofiltered.isConnected _
  let F := E ⋙ Over.forget U₀.obj
  let G := F ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hF : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (F.obj j)) :=
    fun j => (affineStageChart B S hS D i U₀ p₀ hAffine j).U.property
  let : ∀ j, IsAffine (G.obj j) := hF
  let : ∀ {j k : Over i} (e : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (G.map e) :=
      fun {_ _} _ => inferInstance
  let : ∀ j : Over i, CompactSpace (G.obj j) := fun _ => inferInstance
  let : ∀ j : Over i, QuasiSeparatedSpace (G.obj j) := fun _ => inferInstance
  let sc := (Over.forget U₀.obj ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c
  have hsc : IsLimit sc := isLimit_toScheme_affineStageChart_conv B S hS hZ D hD hAffine hQc hQs
    hconv i U₀ p₀
    ((Over.forget U₀.obj).mapCone c)
    (isLimitOfPreserves (Over.forget U₀.obj) hc)
  exact scheme_model_of_finitePresentation G sc hsc
    (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) hg

omit hSize hHomSize in
include hconv in
private theorem exists_affine_model_over_affine_chart_conv (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g))
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)] :
    let c := affineStageChartConeConv B S hS hZ D hD hAffine hQc hQs hconv
      i U₀ p₀ hAffine U.obj p q hp
    ∃ (j : Over i) (Wj : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (affineStageChart B S hS D i U₀ p₀ hAffine j).U.obj)),
      AlgebraicGeometry.FinitePresentation Wj.hom ∧ IsAffine Wj.left ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
        (Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
            (c.π.app j).left)).obj Wj) := by
  dsimp only
  let E := affineStageChartOverDiagramConv B S hS hZ D hD hAffine hQc hQs hconv
    i U₀ p₀ hAffine
  let c := affineStageChartConeConv B S hS hZ D hD hAffine hQc hQs hconv
    i U₀ p₀ hAffine U.obj p q hp
  let hc := affineStageChartConeIsLimitConv B S hS hZ D hD hAffine hQc hQs hconv
    i U₀ p₀ hAffine U.obj p q hp
  let : IsConnected (Over i) := IsCofiltered.isConnected _
  let F := E ⋙ Over.forget U₀.obj
  let G := F ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hF : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (F.obj j)) :=
    fun j => (affineStageChart B S hS D i U₀ p₀ hAffine j).U.property
  let : ∀ j, IsAffine (G.obj j) := hF
  let : ∀ {j k : Over i} (e : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (G.map e) :=
      fun {_ _} _ => inferInstance
  let : ∀ j : Over i, CompactSpace (G.obj j) := fun _ => inferInstance
  let : ∀ j : Over i, QuasiSeparatedSpace (G.obj j) := fun _ => inferInstance
  let sc := (Over.forget U₀.obj ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c
  have hsc : IsLimit sc := isLimit_toScheme_affineStageChart_conv B S hS hZ D hD hAffine hQc hQs
    hconv i U₀ p₀
    ((Over.forget U₀.obj).mapCone c)
    (isLimitOfPreserves (Over.forget U₀.obj) hc)
  exact scheme_affine_model_of_finitePresentation G sc hsc
    (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) hg
    ‹IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)›

omit hSize hHomSize in
include hconv in
private theorem exists_site_model_over_affine_chart_conv (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (hp₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p₀)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) :
    ∃ (j : Over i) (V : AlgebraicGeometry.BigFppfOver B S hS)
      (v : yoneda.obj V ⟶ D.obj j.left) (a : W ⟶ V),
      AlgebraicGeometry.Space.IsFinitePresentation B S hS v ∧
      IsPullback (yoneda.map a) (yoneda.map g ≫ p) v (limit.π D j.left) := by
  let c := affineStageChartConeConv B S hS hZ D hD hAffine hQc hQs hconv
    i U₀ p₀ hAffine U.obj p q hp
  obtain ⟨j, V₀, hV₀, ⟨e⟩⟩ := exists_model_over_affine_chart_conv B S hS hZ D hD
    hAffine hQc hQs hconv i U₀ p₀ U p q hp W g hg
  let Cj := affineStageChart B S hS D i U₀ p₀ hAffine j
  let b : U.obj ⟶ Cj.U.obj := (c.π.app j).left
  obtain ⟨V, f, a, hf, _, ha⟩ := exists_site_pullback_model B S hS b g V₀ hV₀ e
  have hbp : yoneda.map b ≫ Cj.toStage = p ≫ limit.π D j.left := by
    show yoneda.map (affineStageChartLift B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        (affineStageChart B S hS D i U₀ p₀ hAffine j).toStage = p ≫ limit.π D j.left
    simp [affineStageChartLift]
  have hbq : yoneda.map b ≫ yoneda.map Cj.toChart = yoneda.map q := by
    show yoneda.map (affineStageChartLift B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        yoneda.map (affineStageChart B S hS D i U₀ p₀ hAffine j).toChart = yoneda.map q
    simp [affineStageChartLift]
  have hU : IsPullback (yoneda.map b) p Cj.toStage (limit.π D j.left) := by
    apply IsPullback.of_right (h₂₂ := D.map j.hom) _ hbp Cj.isPullback.flip
    rw [hbq, limit.w]
    exact hp.flip
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (etaleInverseImageIsStableUnderComposition _)
  have hpc : P.presheaf Cj.toStage := P.presheaf.of_isPullback Cj.isPullback.flip hp₀
  let : IsAffine (Q.obj Cj.U.obj) := Cj.U.property
  let : LocallyOfFinitePresentation (Q.map f) := hf.1
  let : QuasiCompact (Q.map f) := hf.2.1
  let : QuasiSeparated (Q.map f) := hf.2.2
  have hVqc : CompactSpace (Q.obj V) := QuasiCompact.compactSpace_of_compactSpace (Q.map f)
  have hVqs : QuasiSeparatedSpace (Q.obj V) :=
    quasiSeparatedSpace_of_quasiSeparated (Q.map f)
  refine ⟨j, V, yoneda.map f ≫ Cj.toStage, a,
    isFinitePresentation_of_scheme_chart B S hS hZ (hD j.left) (hQs j.left)
      V Cj.U.obj hVqc hVqs f Cj.toStage hpc hf.1, ?_⟩
  exact (ha.map yoneda).paste_vert hU

omit hSize hHomSize in
include hconv in
private theorem exists_affine_site_model_over_affine_chart_conv (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (hp₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p₀)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g))
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)] :
    ∃ (j : Over i) (V : AlgebraicGeometry.BigFppfOver B S hS)
      (v : yoneda.obj V ⟶ D.obj j.left) (a : W ⟶ V),
      AlgebraicGeometry.Space.IsFinitePresentation B S hS v ∧
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V) ∧
      IsPullback (yoneda.map a) (yoneda.map g ≫ p) v (limit.π D j.left) := by
  let c := affineStageChartConeConv B S hS hZ D hD hAffine hQc hQs hconv
    i U₀ p₀ hAffine U.obj p q hp
  obtain ⟨j, V₀, hV₀, hV₀aff, ⟨e⟩⟩ := exists_affine_model_over_affine_chart_conv B S hS hZ D hD
    hAffine hQc hQs hconv i U₀ p₀ U p q hp W g hg
  let Cj := affineStageChart B S hS D i U₀ p₀ hAffine j
  let b : U.obj ⟶ Cj.U.obj := (c.π.app j).left
  obtain ⟨V, f, a, hf, ⟨eV⟩, ha⟩ := exists_site_pullback_model B S hS b g V₀ hV₀ e
  have hbp : yoneda.map b ≫ Cj.toStage = p ≫ limit.π D j.left := by
    show yoneda.map (affineStageChartLift B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        (affineStageChart B S hS D i U₀ p₀ hAffine j).toStage = p ≫ limit.π D j.left
    simp [affineStageChartLift]
  have hbq : yoneda.map b ≫ yoneda.map Cj.toChart = yoneda.map q := by
    show yoneda.map (affineStageChartLift B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        yoneda.map (affineStageChart B S hS D i U₀ p₀ hAffine j).toChart = yoneda.map q
    simp [affineStageChartLift]
  have hU : IsPullback (yoneda.map b) p Cj.toStage (limit.π D j.left) := by
    apply IsPullback.of_right (h₂₂ := D.map j.hom) _ hbp Cj.isPullback.flip
    rw [hbq, limit.w]
    exact hp.flip
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (etaleInverseImageIsStableUnderComposition _)
  have hpc : P.presheaf Cj.toStage := P.presheaf.of_isPullback Cj.isPullback.flip hp₀
  let : IsAffine (Q.obj Cj.U.obj) := Cj.U.property
  let : LocallyOfFinitePresentation (Q.map f) := hf.1
  let : QuasiCompact (Q.map f) := hf.2.1
  let : QuasiSeparated (Q.map f) := hf.2.2
  have hVqc : CompactSpace (Q.obj V) := QuasiCompact.compactSpace_of_compactSpace (Q.map f)
  have hVqs : QuasiSeparatedSpace (Q.obj V) :=
    quasiSeparatedSpace_of_quasiSeparated (Q.map f)
  refine ⟨j, V, yoneda.map f ≫ Cj.toStage, a,
    isFinitePresentation_of_scheme_chart B S hS hZ (hD j.left) (hQs j.left)
      V Cj.U.obj hVqc hVqs f Cj.toStage hpc hf.1, ?_, ?_⟩
  · let : IsAffine V₀.left := hV₀aff
    let : IsIso eV.hom.left :=
      inferInstanceAs (IsIso ((Over.forget ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
        Cj.U.obj)).map eV.hom))
    exact IsAffine.of_isIso eV.hom.left
  · exact (ha.map yoneda).paste_vert hU

omit hSize hHomSize in
include hconv in
private theorem eventually_etale_over_affine_chart_conv (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (X : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀.obj))
    (hX : AlgebraicGeometry.FinitePresentation X.hom)
    [Etale ((Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)).obj X).hom] :
    ∃ j : Over i, Etale ((Over.pullback
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (affineStageChart B S hS D i U₀ p₀ hAffine j).toChart)).obj X).hom := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let E := affineStageChartOverDiagramConv B S hS hZ D hD hAffine hQc hQs hconv
    i U₀ p₀ hAffine
  let c := affineStageChartConeConv B S hS hZ D hD hAffine hQc hQs hconv
    i U₀ p₀ hAffine U.obj p q hp
  let hc := affineStageChartConeIsLimitConv B S hS hZ D hD hAffine hQc hQs hconv
    i U₀ p₀ hAffine U.obj p q hp
  let : IsConnected (Over i) := IsCofiltered.isConnected _
  let F := E ⋙ Over.forget U₀.obj
  let E' := E ⋙ Over.post Q
  let sc := (Over.post Q).mapCone c
  have hF (j : Over i) : IsAffine (Q.obj (F.obj j)) :=
    (affineStageChart B S hS D i U₀ p₀ hAffine j).U.property
  have hsc : IsLimit ((Over.forget (Q.obj U₀.obj)).mapCone sc) :=
    isLimit_toScheme_affineStageChart_conv B S hS hZ D hD hAffine hQc hQs hconv i U₀ p₀
      ((Over.forget U₀.obj).mapCone c) (isLimitOfPreserves (Over.forget U₀.obj) hc)
  let : ∀ j, IsAffine (E'.obj j).left := hF
  let : ∀ {j k : Over i} (a : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (E'.map a).left := by
    intro j k a
    infer_instance
  let : Etale ((Over.pullback sc.pt.hom).obj X).hom :=
    ‹Etale ((Over.pullback (Q.map q)).obj X).hom›
  exact scheme_eventually_etale_pullback E' sc hsc X hX

omit hSize hHomSize in
include hconv in
private theorem eventually_eq_on_quasiCompact_source_conv (i : I)
    {Y Z G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hYqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS Y)
    (r : Y ⟶ D.obj i) (a : Z ⟶ G) (b : D.obj i ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : Y ⟶ Z) (hf : f ≫ a = r ≫ b) (hg : g ≫ a = r ≫ b)
    (hfg : pullback.fst r (limit.π D i) ≫ f =
      pullback.fst r (limit.π D i) ≫ g) :
    ∃ (j : I) (e : j ⟶ i),
      pullback.fst r (D.map e) ≫ f = pullback.fst r (D.map e) ≫ g := by
  classical
  obtain ⟨U₀, q₀, hU₀, hsurj, het⟩ := exists_affine_etale_atlas B S hS Y hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hh : pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀ ≫ f =
      pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀ ≫ g := by
    let k : pullback (limit.π D i) (q₀ ≫ r) ⟶ pullback r (limit.π D i) :=
      pullback.lift (pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀)
      (pullback.fst (limit.π D i) (q₀ ≫ r))
      (by simp only [Category.assoc, pullback.condition])
    simpa [k] using congrArg (fun t => k ≫ t) hfg
  obtain ⟨j, hj⟩ := eventually_eq_on_affine_chart_over_conv B S hS hZ D hD
    hAffine hQc hQs hconv i U (q₀ ≫ r) hG b hZalg a ha
    (q₀ ≫ f) (q₀ ≫ g) (by simp [hf]) (by simp [hg]) hh
  refine ⟨j.left, j.hom, ?_⟩
  let C := affineStageChart B S hS D i U (q₀ ≫ r) hAffine j
  let p : yoneda.obj C.U.obj ⟶ pullback r (D.map j.hom) :=
    pullback.lift (yoneda.map C.toChart ≫ q₀) C.toStage
      (by simpa only [Category.assoc] using C.isPullback.w.symm)
  have hp : IsPullback (yoneda.map C.toChart) p q₀
      (pullback.fst r (D.map j.hom)) := by
    apply IsPullback.of_bot _ (by simp [p]) (IsPullback.of_hasPullback r (D.map j.hom))
    simpa [p] using C.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  apply hom_ext_of_surjective_etale_atlas B S hS
    (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS r (D.map j.hom) hY (hD j.left) (hD i))
    hZalg.isSheaf p
    (P.presheaf.of_isPullback hp hsurj)
    (Q.presheaf.of_isPullback hp (represented_etale_of_isEtale B S hS q₀ het))
  simpa [p, Category.assoc] using hj

omit hSize hHomSize in
include hconv in
private theorem exists_stage_atlas_factorization_conv (i : I)
    (Y : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hYqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS Y.left)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f : pullback Y.hom (limit.π D i) ⟶ Z)
    (hf : f ≫ a = pullback.fst Y.hom (limit.π D i) ≫ Y.hom) :
    ∃ (j : Over i) (U : AlgebraicGeometry.BigAffineFppf B S hS)
      (p : yoneda.obj U.obj ⟶ pullback Y.hom (D.map j.hom))
      (g : yoneda.obj U.obj ⟶ Z),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      g ≫ a = p ≫ pullback.snd Y.hom (D.map j.hom) ≫ D.map j.hom ∧
      pullback.fst (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ≫ g =
        pullback.lift
          (pullback.fst (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ≫ p)
          (pullback.snd (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left))
          (by simpa only [Over.pullback_obj_hom, Category.assoc] using
            (pullback.condition (f := p ≫ pullback.snd Y.hom (D.map j.hom))
              (g := limit.π D j.left))) ≫
        (iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
          (limit.w D j.hom) Y).hom.left ≫ f := by
  classical
  obtain ⟨U₀, q₀, hU₀, hs, he⟩ := exists_affine_etale_atlas B S hS Y.left hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  let k : pullback (limit.π D i) (q₀ ≫ Y.hom) ⟶ pullback Y.hom (limit.π D i) :=
    pullback.lift (pullback.snd _ _ ≫ q₀) (pullback.fst _ _)
      (by simp only [Category.assoc, pullback.condition])
  obtain ⟨j, g, hg, hgf⟩ := exists_hom_on_affine_chart_conv B S hS hZ D hD
    hAffine hQc hQs hconv i U (q₀ ≫ Y.hom) hZalg a ha (k ≫ f) (by
      rw [Category.assoc, hf]
      simpa [k, Category.assoc] using (pullback.condition (f := limit.π D i)
        (g := q₀ ≫ Y.hom)).symm)
  let C := affineStageChart B S hS D i U (q₀ ≫ Y.hom) hAffine j
  let p : yoneda.obj C.U.obj ⟶ pullback Y.hom (D.map j.hom) :=
    pullback.lift (yoneda.map C.toChart ≫ q₀) C.toStage
      (by simpa only [Category.assoc] using C.isPullback.w.symm)
  have hp : IsPullback (yoneda.map C.toChart) p q₀
      (pullback.fst Y.hom (D.map j.hom)) := by
    apply IsPullback.of_bot _ (by simp [p]) (IsPullback.of_hasPullback Y.hom (D.map j.hom))
    simpa [p] using C.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  refine ⟨j, C.U, p, g, P.presheaf.of_isPullback hp hs,
    Q.presheaf.of_isPullback hp (represented_etale_of_isEtale B S hS q₀ he),
    by simpa [p] using hg, ?_⟩
  let v : pullback (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ⟶
      pullback (limit.π D i) (q₀ ≫ Y.hom) :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ yoneda.map C.toChart) (by
      simp only [Category.assoc]
      rw [← C.isPullback.w, ← limit.w D j.hom]
      simp only [← Category.assoc]
      congr 1
      have hpcomp : p ≫ pullback.snd Y.hom (D.map j.hom) = C.toStage := by simp [p]
      rw [← hpcomp]
      exact pullback.condition.symm)
  let l := C.isPullback.lift
    (pullback.fst (limit.π D i) (q₀ ≫ Y.hom) ≫ limit.π D j.left)
    (pullback.snd (limit.π D i) (q₀ ≫ Y.hom))
    (by rw [Category.assoc, limit.w]; exact pullback.condition)
  have hv : v ≫ l = pullback.fst _ _ := by
    apply C.isPullback.hom_ext
    · simp only [Category.assoc, l, IsPullback.lift_fst, v, pullback.lift_fst_assoc]
      simpa [p, Category.assoc] using
        (pullback.condition (f := p ≫ pullback.snd Y.hom (D.map j.hom))
          (g := limit.π D j.left)).symm
    · simp [l, v]
  conv_lhs => rw [← hv, Category.assoc, hgf]
  simp only [← Category.assoc]
  apply congrArg (fun t => t ≫ f)
  apply pullback.hom_ext
  · simp [v, k, iteratedBaseChangeIso_hom_left, p, Category.assoc]
  · simp [v, k, iteratedBaseChangeIso_hom_left, Category.assoc]

omit hSize hHomSize in
include hconv hDlim in
/-- **Stacks 07SK, fullness, under the chapter's convention.** A morphism between base changes
to the limit of algebraic spaces of finite presentation over a stage is defined at a later
stage, with the comparison isomorphisms the canonical base-change comparisons.
This is the faithful statement of the tag. The source states no condition on the index: it
assumes only the convention of Section 70.2 (tag 07SD) that every ring considered has its
spectrum in the big fppf site, which for this system is
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`. The proof is the one of
`AlgebraicGeometry.Space.exists_morphism_after_baseChange`, with each appeal to the bounds on the
index replaced by the convention: affineness of the projections from the limit is
`AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits`, the limit of the
affine charts over a stage lies in the site because that diagram is a lift of a diagram of base
changes, and the algebraicity of the limit is taken from Stacks 07SF under the convention,
`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits`, as `hDlim`. -/
public theorem exists_morphism_after_baseChange_of_siteContainsBaseChangeLimits
    (i : I) (Yᵢ Zᵢ : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f : (Over.pullback (limit.π D i)).obj Yᵢ ⟶
      (Over.pullback (limit.π D i)).obj Zᵢ) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (D.map e)).obj Yᵢ ⟶
        (Over.pullback (D.map e)).obj Zᵢ)
      (α : (Over.pullback (limit.π D j)).obj
          ((Over.pullback (D.map e)).obj Yᵢ) ≅
        (Over.pullback (limit.π D i)).obj Yᵢ)
      (β : (Over.pullback (limit.π D j)).obj
          ((Over.pullback (D.map e)).obj Zᵢ) ≅
        (Over.pullback (limit.π D i)).obj Zᵢ),
      (α.hom.left ≫ pullback.fst Yᵢ.hom (limit.π D i) =
        pullback.fst ((Over.pullback (D.map e)).obj Yᵢ).hom (limit.π D j) ≫
          pullback.fst Yᵢ.hom (D.map e)) ∧
      (β.hom.left ≫ pullback.fst Zᵢ.hom (limit.π D i) =
        pullback.fst ((Over.pullback (D.map e)).obj Zᵢ).hom (limit.π D j) ≫
          pullback.fst Zᵢ.hom (D.map e)) ∧
      α.hom ≫ f = (Over.pullback (limit.π D j)).map g ≫ β.hom := by
  classical
  have hYqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS Yᵢ.hom
    (hD i) (hQc i) hYfp
  have hYqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS hZ hY (hQs i) hYfp.2.2
  let f₀ := f.left ≫ pullback.fst Zᵢ.hom (limit.π D i)
  have hf₀ : f₀ ≫ Zᵢ.hom = pullback.fst Yᵢ.hom (limit.π D i) ≫ Yᵢ.hom := by
    simp only [f₀, Category.assoc, pullback.condition]
    have hw : f.left ≫ pullback.snd Zᵢ.hom (limit.π D i) =
        pullback.snd Yᵢ.hom (limit.π D i) := f.w
    rw [← Category.assoc, hw]
  obtain ⟨j, U, p, g, hs, he, hg, hgf⟩ := exists_stage_atlas_factorization_conv
    B S hS hZ D hD hAffine hQc hQs hconv i Yᵢ hY hYqc hZ' Zᵢ.hom hZfp.1 f₀ hf₀
  let Yj := (Over.pullback (D.map j.hom)).obj Yᵢ
  have hYj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom (D.map j.hom)
    hY (hD j.left) (hD i)
  have hYjqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_pullback
    B S hS hZ Yᵢ.hom (D.map j.hom) hY (hD j.left) (hD i) hYqs (hQs j.left)
  have hU := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U.obj
  have hUqc := isQuasiCompactSpace_yoneda_of_isAffine B S hS U.obj U.property
  have hR := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS p p hU hU hYj
  have hRqc := AlgebraicGeometry.Space.isQuasiCompactSpace_pullback
    B S hS hZ p p hU hYj hUqc hUqc hYjqs
  have hlim := equalizes_kernelPair_after_baseChange p Yj.hom (limit.π D j.left)
    ((iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
      (limit.w D j.hom) Yᵢ).hom.left ≫ f₀) g hgf
  obtain ⟨k, e, hkg⟩ := eventually_eq_on_quasiCompact_source_conv B S hS hZ D hD
    hAffine hQc hQs hconv j.left hR hZ' (hD i) hRqc
    (pullback.fst p p ≫ p ≫ Yj.hom) Zᵢ.hom (D.map j.hom) hZfp.1
    (pullback.fst p p ≫ g) (pullback.snd p p ≫ g)
    (by simpa only [Yj, Over.pullback_obj_hom, Category.assoc] using congrArg
          (fun t => pullback.fst p p ≫ t) hg)
    (by simpa only [Yj, Over.pullback_obj_hom, Category.assoc, pullback.condition_assoc] using
      congrArg (fun t => pullback.snd p p ≫ t) hg) hlim
  let K := affineStageChart B S hS D j.left U (p ≫ Yj.hom) hAffine (Over.mk e)
  let Yk := (Over.pullback (D.map e)).obj Yj
  let pK : yoneda.obj K.U.obj ⟶ Yk.left :=
    pullback.lift (yoneda.map K.toChart ≫ p) K.toStage
      (by simpa only [Category.assoc, Over.mk_hom] using K.isPullback.w.symm)
  have hpK : IsPullback (yoneda.map K.toChart) pK p (pullback.fst Yj.hom (D.map e)) := by
    apply IsPullback.of_bot _ (by simp [pK]) (IsPullback.of_hasPullback Yj.hom (D.map e))
    simpa [pK] using K.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  have hYk := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yj.hom (D.map e)
    hYj (hD k) (hD j.left)
  have hKs := P.presheaf.of_isPullback hpK hs
  have hKe := Q.presheaf.of_isPullback hpK he
  obtain ⟨gK, hgK⟩ := exists_hom_of_equalizes_atlas B S hS hYk hZ'.isSheaf pK hKs hKe
    (yoneda.map K.toChart ≫ g)
    (equalizes_kernelPair_of_baseChange_eq p Yj.hom (D.map e)
      (pullback.fst Yj.hom (D.map e)) (pullback.snd Yj.hom (D.map e)) pullback.condition
      (yoneda.map K.toChart) pK (by simp [pK]) g hkg)
  have hgKa : gK ≫ Zᵢ.hom = Yk.hom ≫ D.map e ≫ D.map j.hom := by
    apply hom_ext_of_surjective_etale_atlas B S hS hYk (hD i).isSheaf pK hKs hKe
    rw [← Category.assoc, hgK, Category.assoc, hg]
    have hw := congrArg (fun t => t ≫ D.map j.hom) K.isPullback.w
    simpa only [Yj, Yk, pK, Over.pullback_obj_hom, pullback.lift_snd_assoc,
      Over.mk_hom, Category.assoc] using hw.symm
  let d := e ≫ j.hom
  let η := iteratedBaseChangeIso (D.map j.hom) (D.map e) (D.map d)
    (D.map_comp e j.hom).symm Yᵢ
  let raw : pullback Yᵢ.hom (D.map d) ⟶ Zᵢ.left := η.inv.left ≫ gK
  have hrawa : raw ≫ Zᵢ.hom = pullback.snd Yᵢ.hom (D.map d) ≫ D.map d := by
    dsimp only [raw]
    rw [Category.assoc, hgKa]
    simpa only [d, Yk, Yj, Over.pullback_obj_hom, Functor.map_comp, Category.assoc] using
      congrArg (fun t => t ≫ D.map d) (Over.w η.inv)
  let g' : (Over.pullback (D.map d)).obj Yᵢ ⟶ (Over.pullback (D.map d)).obj Zᵢ :=
    Over.homMk (pullback.lift raw (pullback.snd Yᵢ.hom (D.map d)) hrawa) (by simp)
  let α := iteratedBaseChangeIso (D.map d) (limit.π D k) (limit.π D i) (limit.w D d) Yᵢ
  let β := iteratedBaseChangeIso (D.map d) (limit.π D k) (limit.π D i) (limit.w D d) Zᵢ
  let m : pullback Yᵢ.hom (limit.π D i) ⟶ pullback Yᵢ.hom (D.map d) :=
    pullback.lift (pullback.fst Yᵢ.hom (limit.π D i))
      (pullback.snd Yᵢ.hom (limit.π D i) ≫ limit.π D k)
      (by rw [Category.assoc, limit.w]; exact pullback.condition)
  have hraw : m ≫ raw = f₀ := by
    let A := iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
      (limit.w D j.hom) Yᵢ
    let q : pullback (p ≫ Yj.hom) (limit.π D j.left) ⟶ pullback Yj.hom (limit.π D j.left) :=
      pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _)
        (by simp only [Category.assoc, pullback.condition])
    have hq : IsPullback (pullback.fst (p ≫ Yj.hom) (limit.π D j.left)) q p
        (pullback.fst Yj.hom (limit.π D j.left)) := by
      apply IsPullback.of_bot _ (by simp [q]) (IsPullback.of_hasPullback Yj.hom (limit.π D j.left))
      simpa [q] using IsPullback.of_hasPullback (p ≫ Yj.hom) (limit.π D j.left)
    let l : pullback (p ≫ Yj.hom) (limit.π D j.left) ⟶ yoneda.obj K.U.obj :=
      K.isPullback.lift (pullback.snd _ _ ≫ limit.π D k) (pullback.fst _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition.symm)
    have hl : q ≫ A.hom.left ≫ m ≫ η.inv.left = l ≫ pK := by
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp [Yj, Yk, q, A, m, η, l, pK, iteratedBaseChangeIso_hom_left,
            iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc]
        · simp [Yj, Yk, q, A, m, η, l, pK, iteratedBaseChangeIso_hom_left,
            iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc, limit.w,
            pullback.condition]
      · simp [Yj, Yk, q, A, m, η, l, pK, iteratedBaseChangeIso_hom_left,
          iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc]
    have hEq : q ≫ A.hom.left ≫ (m ≫ raw) = q ≫ A.hom.left ≫ f₀ := by
      show q ≫ A.hom.left ≫ m ≫ η.inv.left ≫ gK = _
      have hh := congrArg (fun t => t ≫ gK) hl
      simp only [Category.assoc, hgK] at hh
      rw [hh]
      simpa [l, Category.assoc, q, A, Yj] using hgf
    obtain ⟨V, v, w, hV⟩ :=
      AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D hconv
      hAffine j.left U (p ≫ Yj.hom)
    let vq := hV.flip.isoPullback.hom ≫ q
    have hEq' : A.hom.left ≫ (m ≫ raw) = A.hom.left ≫ f₀ := by
      apply hom_ext_of_surjective_etale_atlas B S hS
        (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yj.hom (limit.π D j.left)
          hYj hDlim (hD j.left))
        hZ'.isSheaf vq
        (MorphismProperty.RespectsIso.precomp _ hV.flip.isoPullback.hom q
          (P.presheaf.of_isPullback hq hs))
        (MorphismProperty.RespectsIso.precomp _ hV.flip.isoPullback.hom q
          (Q.presheaf.of_isPullback hq he))
      simpa only [vq, Category.assoc] using
        congrArg (fun t => hV.flip.isoPullback.hom ≫ t) hEq
    let : IsIso A.hom.left :=
      inferInstanceAs (IsIso ((Over.forget (limit D)).map A.hom))
    exact (cancel_epi A.hom.left).mp hEq'
  refine ⟨k, d, g', α, β, iteratedBaseChangeIso_hom_fst _ _ _ _ _,
    iteratedBaseChangeIso_hom_fst _ _ _ _ _, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hm : α.hom.left ≫ m = pullback.fst ((Over.pullback (D.map d)).obj Yᵢ).hom
      (limit.π D k) := by
      apply pullback.hom_ext <;>
        simp [α, m, iteratedBaseChangeIso_hom_left, Category.assoc, pullback.condition]
    have hh := congrArg (fun t => α.hom.left ≫ t) hraw
    rw [← Category.assoc α.hom.left m raw, hm] at hh
    simpa [g', f₀, Category.assoc, β, iteratedBaseChangeIso_hom_left,
      iteratedBaseChangeIso_inv_left, Over.pullback_map_left] using hh.symm
  · simpa only [Over.comp_left, Over.pullback_obj_hom] using
      (Over.w (α.hom ≫ f)).trans
        (Over.w ((Over.pullback (limit.π D k)).map g' ≫ β.hom)).symm

omit hSize hHomSize in
include hconv in
/-- **Stacks 07SK, faithfulness, under the chapter's convention.** Two morphisms between
algebraic spaces of finite presentation over a stage whose base changes to the limit agree
already agree after base change to a later stage.
This is the faithful statement of the tag. The source states no condition on the index: it
assumes only the convention of Section 70.2 (tag 07SD) that every ring considered has its
spectrum in the big fppf site, which for this system is
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`. The proof is the one of
`AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq`, with each appeal to the bounds on the
index replaced by the convention: affineness of the projections from the limit is
`AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits`, the limit of the
affine charts over a stage lies in the site because that diagram is a lift of a diagram of base
changes. -/
public theorem eventually_eq_of_baseChange_eq_of_siteContainsBaseChangeLimits
    (i : I) (Yᵢ Zᵢ : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f g : Yᵢ ⟶ Zᵢ)
    (hfg : (Over.pullback (limit.π D i)).map f =
      (Over.pullback (limit.π D i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (D.map e)).map f =
        (Over.pullback (D.map e)).map g := by
  classical
  have hYqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS Yᵢ.hom
    (hD i) (hQc i) hYfp
  obtain ⟨U₀, q₀, hU₀, hsurj, het⟩ := exists_affine_etale_atlas B S hS Yᵢ.left hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hf : (q₀ ≫ f.left) ≫ Zᵢ.hom = q₀ ≫ Yᵢ.hom := by simp
  have hg : (q₀ ≫ g.left) ≫ Zᵢ.hom = q₀ ≫ Yᵢ.hom := by simp
  obtain ⟨j, hj⟩ := eventually_eq_on_affine_chart_conv B S hS hZ D hD
    hAffine hQc hQs hconv i U (q₀ ≫ Yᵢ.hom) hZ' Zᵢ.hom hZfp.1
    (q₀ ≫ f.left) (q₀ ≫ g.left) hf hg
    (precomp_eq_of_baseChange_eq (limit.π D i) Yᵢ Zᵢ f g hfg q₀)
  refine ⟨j.left, j.hom, ?_⟩
  let C := affineStageChart B S hS D i U (q₀ ≫ Yᵢ.hom) hAffine j
  let p : yoneda.obj C.U.obj ⟶ pullback Yᵢ.hom (D.map j.hom) :=
    pullback.lift (yoneda.map C.toChart ≫ q₀) C.toStage
      (by simpa only [Category.assoc] using C.isPullback.w.symm)
  have hp : IsPullback (yoneda.map C.toChart) p q₀
      (pullback.fst Yᵢ.hom (D.map j.hom)) := by
    apply IsPullback.of_bot _ (by simp [p]) (IsPullback.of_hasPullback Yᵢ.hom (D.map j.hom))
    simpa [p] using C.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  have hpalgebraic := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom (D.map j.hom)
    hY (hD j.left) (hD i)
  have heq : pullback.fst Yᵢ.hom (D.map j.hom) ≫ f.left =
      pullback.fst Yᵢ.hom (D.map j.hom) ≫ g.left := by
    apply hom_ext_of_surjective_etale_atlas B S hS hpalgebraic hZ'.isSheaf p
      (P.presheaf.of_isPullback hp hsurj)
      (Q.presheaf.of_isPullback hp (represented_etale_of_isEtale B S hS q₀ het))
    simpa [p, Category.assoc] using hj
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa [Over.pullback_map_left] using heq
  · simp [Over.pullback_map_left]

omit hSize hHomSize in
include hconv in
private theorem exists_mono_after_baseChange_conv
    (i : I) (Y Z : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Z.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Z.hom)
    (f : Y ⟶ Z) [Mono ((Over.pullback (limit.π D i)).map f)] :
    ∃ (j : I) (e : j ⟶ i), Mono ((Over.pullback (D.map e)).map f) := by
  let c := overPullbackCone f f
  have hc := overPullbackCone_isPullback f f
  have hf := isFinitePresentation_overHom B S hS hZ (hD i) (hQc i) (hQs i)
    Y Z hY hZ' hYfp hZfp f
  have hR : AlgebraicGeometry.IsAlgebraicSpace B S hS c.pt.left :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f.left f.left hY hY hZ'
  have hRfst := isFinitePresentation_of_isPullback B S hS hR hY hY hZ'
    (IsPullback.of_hasPullback f.left f.left).flip hf
  have hRfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS c.pt.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hR hY (hD i)
      (pullback.fst f.left f.left) Y.hom hRfst hYfp
  have heq : (Over.pullback (limit.π D i)).map c.fst =
      (Over.pullback (limit.π D i)).map c.snd := by
    apply (cancel_mono ((Over.pullback (limit.π D i)).map f)).mp
    rw [← Functor.map_comp, ← Functor.map_comp, c.condition]
  obtain ⟨j, e, hj⟩ := eventually_eq_of_baseChange_eq_of_siteContainsBaseChangeLimits
    B S hS hZ D hD hAffine hQc hQs hconv i c.pt Y hR hY hRfp hYfp c.fst c.snd heq
  exact ⟨j, e, IsKernelPair.mono_of_eq_fst_snd (hc.map (Over.pullback (D.map e))) hj⟩

omit hSize hHomSize in
include hconv hDlim in
private theorem exists_lift_pair_after_baseChange_conv
    (i : I) (A R W : Over (D.obj i))
    (hA : AlgebraicGeometry.IsAlgebraicSpace B S hS A.left)
    (hR : AlgebraicGeometry.IsAlgebraicSpace B S hS R.left)
    (hW : AlgebraicGeometry.IsAlgebraicSpace B S hS W.left)
    (hAfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS A.hom)
    (hRfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS R.hom)
    (hWfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS W.hom)
    (s t : R ⟶ W) (a b : A ⟶ W)
    (u : (Over.pullback (limit.π D i)).obj A ⟶ (Over.pullback (limit.π D i)).obj R)
    (hu₁ : u ≫ (Over.pullback (limit.π D i)).map s = (Over.pullback (limit.π D i)).map a)
    (hu₂ : u ≫ (Over.pullback (limit.π D i)).map t = (Over.pullback (limit.π D i)).map b) :
    ∃ (j : I) (e : j ⟶ i)
      (v : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj R),
      v ≫ (Over.pullback (D.map e)).map s = (Over.pullback (D.map e)).map a ∧
      v ≫ (Over.pullback (D.map e)).map t = (Over.pullback (D.map e)).map b := by
  classical
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ :=
    exists_morphism_after_baseChange_of_siteContainsBaseChangeLimits
    B S hS hZ D hD hAffine hQc hQs hconv hDlim i A R hA hR hAfp hRfp u
  have hα' := iteratedBaseChangeIso_unique (D.map e) (limit.π D j) (limit.π D i)
    (limit.w D e) A α hα
  have hβ' := iteratedBaseChangeIso_unique (D.map e) (limit.π D j) (limit.π D i)
    (limit.w D e) R β hβ
  let γ := iteratedBaseChangeIso (D.map e) (limit.π D j) (limit.π D i) (limit.w D e) W
  have heq (v : R ⟶ W) (z : A ⟶ W)
      (hz : u ≫ (Over.pullback (limit.π D i)).map v = (Over.pullback (limit.π D i)).map z) :
      (Over.pullback (limit.π D j)).map (g ≫ (Over.pullback (D.map e)).map v) =
        (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map z) := by
    have hv : (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map v) ≫
        γ.hom = β.hom ≫ (Over.pullback (limit.π D i)).map v := by
      rw [hβ']
      exact iteratedBaseChangeIso_naturality _ _ _ (limit.w D e) v
    have hz' : (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map z) ≫
        γ.hom = α.hom ≫ (Over.pullback (limit.π D i)).map z := by
      rw [hα']
      exact iteratedBaseChangeIso_naturality _ _ _ (limit.w D e) z
    apply (Iso.cancel_iso_hom_right _ _ γ).mp
    rw [Functor.map_comp, Category.assoc, hv, ← Category.assoc, ← hg,
      Category.assoc, hz, hz']
  let Aj := (Over.pullback (D.map e)).obj A
  let Wj := (Over.pullback (D.map e)).obj W
  have hAj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS A.hom (D.map e) hA (hD j) (hD i)
  have hWj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS W.hom (D.map e) hW (hD j) (hD i)
  have hAjfp := isFinitePresentation_of_isPullback B S hS hAj hA (hD j) (hD i)
    (IsPullback.of_hasPullback A.hom (D.map e)) hAfp
  have hWjfp := isFinitePresentation_of_isPullback B S hS hWj hW (hD j) (hD i)
    (IsPullback.of_hasPullback W.hom (D.map e)) hWfp
  obtain ⟨k₁, e₁, hk₁⟩ := eventually_eq_of_baseChange_eq_of_siteContainsBaseChangeLimits
    B S hS hZ D hD hAffine hQc hQs hconv j Aj Wj hAj hWj hAjfp hWjfp
    (g ≫ (Over.pullback (D.map e)).map s) ((Over.pullback (D.map e)).map a) (heq s a hu₁)
  obtain ⟨k₂, e₂, hk₂⟩ := eventually_eq_of_baseChange_eq_of_siteContainsBaseChangeLimits
    B S hS hZ D hD hAffine hQc hQs hconv j Aj Wj hAj hWj hAjfp hWjfp
    (g ≫ (Over.pullback (D.map e)).map t) ((Over.pullback (D.map e)).map b) (heq t b hu₂)
  let k := IsCofiltered.min (Over.mk e₁) (Over.mk e₂)
  let c₁ := IsCofiltered.minToLeft (Over.mk e₁) (Over.mk e₂)
  let c₂ := IsCofiltered.minToRight (Over.mk e₁) (Over.mk e₂)
  have hk₁' := baseChange_eq_of_baseChange_eq (D.map e₁) (D.map c₁.left) (D.map k.hom)
    (by rw [← D.map_comp]; exact congrArg D.map c₁.w) _ _ hk₁
  have hk₂' := baseChange_eq_of_baseChange_eq (D.map e₂) (D.map c₂.left) (D.map k.hom)
    (by rw [← D.map_comp]; exact congrArg D.map c₂.w) _ _ hk₂
  let δ (Z : Over (D.obj i)) := iteratedBaseChangeIso (D.map e) (D.map k.hom)
    (D.map (k.hom ≫ e)) (D.map_comp _ _).symm Z
  let v := (δ A).inv ≫ (Over.pullback (D.map k.hom)).map g ≫ (δ R).hom
  have hfinal (x : R ⟶ W) (z : A ⟶ W)
      (hx : (Over.pullback (D.map k.hom)).map (g ≫ (Over.pullback (D.map e)).map x) =
        (Over.pullback (D.map k.hom)).map ((Over.pullback (D.map e)).map z)) :
      v ≫ (Over.pullback (D.map (k.hom ≫ e))).map x =
        (Over.pullback (D.map (k.hom ≫ e))).map z := by
    have hn := iteratedBaseChangeIso_naturality (D.map e) (D.map k.hom)
      (D.map (k.hom ≫ e)) (D.map_comp _ _).symm x
    have hz' := iteratedBaseChangeIso_naturality (D.map e) (D.map k.hom)
      (D.map (k.hom ≫ e)) (D.map_comp _ _).symm z
    calc
      v ≫ (Over.pullback (D.map (k.hom ≫ e))).map x =
          (δ A).inv ≫ (Over.pullback (D.map k.hom)).map g ≫
            (Over.pullback (D.map k.hom)).map ((Over.pullback (D.map e)).map x) ≫
            (δ W).hom := by
        simp only [v, Category.assoc]
        rw [← hn]
      _ = (δ A).inv ≫ (Over.pullback (D.map k.hom)).map
          ((Over.pullback (D.map e)).map z) ≫ (δ W).hom := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun z => (δ A).inv ≫ z ≫ (δ W).hom) hx
      _ = (Over.pullback (D.map (k.hom ≫ e))).map z := by
        rw [hz', Iso.inv_hom_id_assoc]
  exact ⟨k.left, k.hom ≫ e, v, hfinal s a hk₁', hfinal t b hk₂'⟩

omit hSize hHomSize in
include hZ hconv in
private theorem exists_model_of_stage_relation_conv (nn : I)
    (hLim : AlgebraicGeometry.IsAlgebraicSpace B S hS (limit D))
    (Y : Over (limit D)) (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    {W KR : AlgebraicGeometry.BigFppfOver B S hS} (w : yoneda.obj W ⟶ Y.left)
    (hws : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (hwe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (kt ks : KR ⟶ W) (hwk : IsPullback (yoneda.map kt) (yoneda.map ks) w w)
    {Wn Rn : AlgebraicGeometry.BigFppfOver B S hS}
    (hWnAff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Wn))
    (wn : yoneda.obj Wn ⟶ D.obj nn) (sn tn : Rn ⟶ Wn)
    (htn : yoneda.map tn ≫ wn = yoneda.map sn ≫ wn)
    (hsnEtale : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sn))
    (htnEtale : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tn))
    (hWnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wn)
    (hRnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map sn ≫ wn))
    (awn : W ⟶ Wn) (arn : KR ⟶ Rn)
    (hWnlim : IsPullback (yoneda.map awn) (w ≫ Y.hom) wn (limit.π D nn))
    (hRnlim : IsPullback (yoneda.map arn) (yoneda.map kt ≫ w ≫ Y.hom)
      (yoneda.map sn ≫ wn) (limit.π D nn))
    (hsnCompat : arn ≫ sn = kt ≫ awn) (htnCompat : arn ≫ tn = ks ≫ awn) :
    ∃ (i : I) (Yᵢ : Over (D.obj i)),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D i)).obj Yᵢ) := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  set rn := yoneda.map sn ≫ wn with hrnDef
  set pW := w ≫ Y.hom with hpWDef
  set pR := yoneda.map kt ≫ pW with hpRDef
  have ht : yoneda.map kt ≫ pW = pR := rfl
  have hs : yoneda.map ks ≫ pW = pR := by
    simpa only [pR, pW, ← Category.assoc] using congrArg (fun z => z ≫ Y.hom) hwk.w.symm
  have hRnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rn
  have hWnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wn
  let Rₙ := Over.mk rn
  let Wₙ := Over.mk wn
  let sₙ : Rₙ ⟶ Wₙ := Over.homMk (yoneda.map sn) rfl
  let tₙ : Rₙ ⟶ Wₙ := Over.homMk (yoneda.map tn) htn
  let sL : Over.mk pR ⟶ Over.mk pW := Over.homMk (yoneda.map kt) ht
  let tL : Over.mk pR ⟶ Over.mk pW := Over.homMk (yoneda.map ks) hs
  let εR : Over.mk pR ≅ (Over.pullback (limit.π D nn)).obj Rₙ :=
    Over.isoMk hRnlim.isoPullback hRnlim.isoPullback_hom_snd
  let εW : Over.mk pW ≅ (Over.pullback (limit.π D nn)).obj Wₙ :=
    Over.isoMk hWnlim.isoPullback hWnlim.isoPullback_hom_snd
  have hεs : εR.hom ≫ (Over.pullback (limit.π D nn)).map sₙ = sL ≫ εW.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [εR, εW, sₙ, sL, Rₙ, Wₙ, Over.pullback_map_left,
        IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc,
        Category.assoc] using congrArg yoneda.map hsnCompat
    · simp [εR, εW, sₙ, sL, Rₙ, Wₙ, Over.pullback_map_left, Category.assoc, ht]
  have hεt : εR.hom ≫ (Over.pullback (limit.π D nn)).map tₙ = tL ≫ εW.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [εR, εW, tₙ, tL, Rₙ, Wₙ, Over.pullback_map_left,
        IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc,
        Category.assoc] using congrArg yoneda.map htnCompat
    · simp [εR, εW, tₙ, tL, Rₙ, Wₙ, Over.pullback_map_left, Category.assoc, hs]
  let rL : Over.mk pW ⟶ Over.mk pR := Over.homMk
    (hwk.lift (𝟙 _) (𝟙 _) (by simp)) (by
      dsimp only [Over.mk_hom, Over.mk_left]
      rw [← ht, IsPullback.lift_fst_assoc, Category.id_comp])
  have hrLs : rL ≫ sL = 𝟙 _ := by ext; simp [rL, sL]
  have hrLt : rL ≫ tL = 𝟙 _ := by ext; simp [rL, tL]
  let rF := εW.inv ≫ rL ≫ εR.hom
  have hrFs : rF ≫ (Over.pullback (limit.π D nn)).map sₙ =
      (Over.pullback (limit.π D nn)).map (𝟙 Wₙ) := by
    simp only [rF, Category.assoc, hεs, ← Category.assoc rL sL, hrLs,
      Category.id_comp, Iso.inv_hom_id]
    exact ((Over.pullback (limit.π D nn)).map_id Wₙ).symm
  have hrFt : rF ≫ (Over.pullback (limit.π D nn)).map tₙ =
      (Over.pullback (limit.π D nn)).map (𝟙 Wₙ) := by
    simp only [rF, Category.assoc, hεt, ← Category.assoc rL tL, hrLt,
      Category.id_comp, Iso.inv_hom_id]
    exact ((Over.pullback (limit.π D nn)).map_id Wₙ).symm
  obtain ⟨ir, er', rr, hrrs, hrrt⟩ := exists_lift_pair_after_baseChange_conv
    B S hS hZ D hD hAffine hQc hQs hconv hLim nn Wₙ Rₙ Wₙ
    hWnAlg hRnAlg hWnAlg hWnFp hRnFp hWnFp sₙ tₙ (𝟙 _) (𝟙 _) rF hrFs hrFt
  let invL : Over.mk pR ⟶ Over.mk pR := Over.homMk
    (hwk.lift (yoneda.map ks) (yoneda.map kt) hwk.w.symm) (by
      dsimp only [Over.mk_hom, Over.mk_left]
      rw [← ht, IsPullback.lift_fst_assoc, hs])
  have hiLs : invL ≫ sL = tL := by ext; simp [invL, sL, tL]
  have hiLt : invL ≫ tL = sL := by ext; simp [invL, sL, tL]
  let invF := εR.inv ≫ invL ≫ εR.hom
  have hiFs : invF ≫ (Over.pullback (limit.π D nn)).map sₙ =
      (Over.pullback (limit.π D nn)).map tₙ := by
    simp only [invF, Category.assoc, hεs, ← Category.assoc invL sL, hiLs]
    rw [← hεt, Iso.inv_hom_id_assoc]
  have hiFt : invF ≫ (Over.pullback (limit.π D nn)).map tₙ =
      (Over.pullback (limit.π D nn)).map sₙ := by
    simp only [invF, Category.assoc, hεt, ← Category.assoc invL tL, hiLt]
    rw [← hεs, Iso.inv_hom_id_assoc]
  obtain ⟨ii, ei, ri, hris, hrit⟩ := exists_lift_pair_after_baseChange_conv
    B S hS hZ D hD hAffine hQc hQs hconv hLim nn Rₙ Rₙ Wₙ
    hRnAlg hRnAlg hWnAlg hRnFp hRnFp hWnFp sₙ tₙ tₙ sₙ invF hiFs hiFt
  let cn := overPullbackCone tₙ sₙ
  have hCAlg : AlgebraicGeometry.IsAlgebraicSpace B S hS cn.pt.left :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS tₙ.left sₙ.left hRnAlg hRnAlg hWnAlg
  have hsₙfp := isFinitePresentation_overHom B S hS hZ (hD nn) (hQc nn) (hQs nn)
    Rₙ Wₙ hRnAlg hWnAlg hRnFp hWnFp sₙ
  have hCfst := isFinitePresentation_of_isPullback B S hS hCAlg hRnAlg hRnAlg hWnAlg
    (IsPullback.of_hasPullback tₙ.left sₙ.left).flip hsₙfp
  have hCFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS cn.pt.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hCAlg hRnAlg (hD nn)
      (pullback.fst tₙ.left sₙ.left) rn hCfst hRnFp
  let F := Over.pullback (limit.π D nn)
  let ca : F.obj cn.pt ⟶ Over.mk pR := F.map cn.fst ≫ εR.inv
  let cb : F.obj cn.pt ⟶ Over.mk pR := F.map cn.snd ≫ εR.inv
  have hcab : ca ≫ tL = cb ≫ sL := by
    apply (Iso.cancel_iso_hom_right _ _ εW).mp
    simp only [ca, cb, Category.assoc]
    rw [← hεt, ← hεs, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc,
      ← F.map_comp, ← F.map_comp, cn.condition]
  have hcabLeft : ca.left ≫ yoneda.map ks = cb.left ≫ yoneda.map kt :=
    congrArg (fun z => z.left) hcab
  have hcomp : (ca.left ≫ yoneda.map kt) ≫ w =
      (cb.left ≫ yoneda.map ks) ≫ w := by
    rw [Category.assoc, hwk.w, ← Category.assoc, hcabLeft,
      Category.assoc, hwk.w, Category.assoc]
  let compL : F.obj cn.pt ⟶ Over.mk pR := Over.homMk
    (hwk.lift (ca.left ≫ yoneda.map kt) (cb.left ≫ yoneda.map ks) hcomp)
    (by
      dsimp only [Over.mk_hom]
      calc hwk.lift (ca.left ≫ yoneda.map kt)
              (cb.left ≫ yoneda.map ks) hcomp ≫ pR
          = hwk.lift (ca.left ≫ yoneda.map kt)
              (cb.left ≫ yoneda.map ks) hcomp ≫ yoneda.map kt ≫ pW := by
            rw [ht]
        _ = (ca.left ≫ yoneda.map kt) ≫ pW := IsPullback.lift_fst_assoc _ _ _ _ _
        _ = ca.left ≫ pR := by rw [Category.assoc, ht]
        _ = (F.obj cn.pt).hom := ca.w)
  have hcompS : compL ≫ sL = ca ≫ sL := by ext; simp [compL, sL]
  have hcompT : compL ≫ tL = cb ≫ tL := by ext; simp [compL, tL]
  let compF := compL ≫ εR.hom
  have hcompFs : compF ≫ F.map sₙ = F.map (cn.fst ≫ sₙ) := by
    simp only [compF]
    rw [Category.assoc, hεs, ← Category.assoc, hcompS]
    simp only [ca, Category.assoc]
    rw [← hεs, Iso.inv_hom_id_assoc, F.map_comp]
  have hcompFt : compF ≫ F.map tₙ = F.map (cn.snd ≫ tₙ) := by
    simp only [compF]
    rw [Category.assoc, hεt, ← Category.assoc, hcompT]
    simp only [cb, Category.assoc]
    rw [← hεt, Iso.inv_hom_id_assoc, F.map_comp]
  obtain ⟨ic, ec, rc, hrcs, hrct⟩ := exists_lift_pair_after_baseChange_conv
    B S hS hZ D hD hAffine hQc hQs hconv hLim nn cn.pt Rₙ Wₙ
    hCAlg hRnAlg hWnAlg hCFp hRnFp hWnFp sₙ tₙ
    (cn.fst ≫ sₙ) (cn.snd ≫ tₙ) compF hcompFs hcompFt
  let KWn := atlasKernelPair B S hS wn (hD nn).diagonal_representable
  have hψcomm : yoneda.map sn ≫ wn = yoneda.map tn ≫ wn := htn.symm
  let ψ₀ : Rn ⟶ KWn.R := yoneda.preimage
    (KWn.kernelPair.lift (yoneda.map sn) (yoneda.map tn) hψcomm)
  have hψ₀ : yoneda.map ψ₀ =
      KWn.kernelPair.lift (yoneda.map sn) (yoneda.map tn) hψcomm := yoneda.map_preimage _
  have hψs : ψ₀ ≫ KWn.s = sn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hψ₀]
    exact KWn.kernelPair.lift_fst _ _ _
  have hψt : ψ₀ ≫ KWn.t = tn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hψ₀]
    exact KWn.kernelPair.lift_snd _ _ _
  let Zₙ : Over (D.obj nn) := Over.mk (yoneda.map KWn.s ≫ wn)
  let ψ : Rₙ ⟶ Zₙ := Over.homMk (yoneda.map ψ₀) (by
    show yoneda.map ψ₀ ≫ yoneda.map KWn.s ≫ wn = rn
    rw [← Category.assoc, ← yoneda.map_comp, hψs])
  have hZnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS KWn.R
  have hKWnt : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map KWn.s) :=
    isFinitePresentation_of_isPullback B S hS hZnAlg hWnAlg hWnAlg (hD nn)
      KWn.kernelPair.flip hWnFp
  have hZnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zₙ.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hZnAlg hWnAlg (hD nn)
      (yoneda.map KWn.s) wn hKWnt hWnFp
  have hψfst : (F.map ψ).left ≫ pullback.fst Zₙ.hom (limit.π D nn) =
      pullback.fst rn (limit.π D nn) ≫ yoneda.map ψ₀ := by
    simp [F, Over.pullback_map_left, ψ, Rₙ]
  have hψsnd : (F.map ψ).left ≫ pullback.snd Zₙ.hom (limit.π D nn) =
      pullback.snd rn (limit.π D nn) := by
    simp [F, Over.pullback_map_left, ψ, Rₙ]
  have e₂ : (hRnlim.isoPullback.hom ≫ (F.map ψ).left) ≫
      pullback.snd Zₙ.hom (limit.π D nn) = pR := by
    rw [Category.assoc, hψsnd, hRnlim.isoPullback_hom_snd]
  have e₁ : (hRnlim.isoPullback.hom ≫ (F.map ψ).left) ≫
      pullback.fst Zₙ.hom (limit.π D nn) ≫ yoneda.map KWn.s =
      yoneda.map kt ≫ yoneda.map awn := by
    rw [Category.assoc, reassoc_of% hψfst, hRnlim.isoPullback_hom_fst_assoc,
      ← yoneda.map_comp ψ₀ KWn.s, hψs, ← yoneda.map_comp, hsnCompat,
      yoneda.map_comp]
  have e₁' : (hRnlim.isoPullback.hom ≫ (F.map ψ).left) ≫
      pullback.fst Zₙ.hom (limit.π D nn) ≫ yoneda.map KWn.t =
      yoneda.map ks ≫ yoneda.map awn := by
    rw [Category.assoc, reassoc_of% hψfst, hRnlim.isoPullback_hom_fst_assoc,
      ← yoneda.map_comp ψ₀ KWn.t, hψt, ← yoneda.map_comp, htnCompat,
      yoneda.map_comp]
  have hμ : Mono (hRnlim.isoPullback.hom ≫ (F.map ψ).left) := by
    refine ⟨fun {T} a b hab => ?_⟩
    have hab' : (a ≫ hRnlim.isoPullback.hom) ≫ (F.map ψ).left =
        (b ≫ hRnlim.isoPullback.hom) ≫ (F.map ψ).left := by
      simpa only [← Category.assoc] using hab
    refine hwk.hom_ext (hWnlim.hom_ext ?_ ?_) (hWnlim.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ← e₁]
      simp only [← Category.assoc]
      rw [hab']
    · rw [Category.assoc, Category.assoc, ht, ← e₂]
      simp only [← Category.assoc]
      rw [hab']
    · rw [Category.assoc, Category.assoc, ← e₁']
      simp only [← Category.assoc]
      rw [hab']
    · rw [Category.assoc, Category.assoc, hs, ← e₂]
      simp only [← Category.assoc]
      rw [hab']
  have hmonoψ : Mono ((Over.pullback (limit.π D nn)).map ψ) := by
    refine Over.mono_of_mono_left _ (hk := ?_)
    have := hμ
    rw [show (F.map ψ).left = inv hRnlim.isoPullback.hom ≫
      (hRnlim.isoPullback.hom ≫ (F.map ψ).left) from by simp]
    infer_instance
  obtain ⟨jm, ejm, hjmMono⟩ := exists_mono_after_baseChange_conv B S hS hZ D hD
    hAffine hQc hQs hconv nn Rₙ Zₙ hRnAlg hZnAlg hRnFp hZnFp ψ
  -- a single stage carrying all of reflexivity, symmetry, transitivity and monicity
  let oo : Over nn := IsCofiltered.min
    (IsCofiltered.min (IsCofiltered.min (Over.mk er') (Over.mk ei)) (Over.mk ec))
    (Over.mk ejm)
  let aMono : oo ⟶ Over.mk ejm := IsCofiltered.minToRight _ _
  let aComp : oo ⟶ Over.mk ec :=
    IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToRight _ _
  let aRefl : oo ⟶ Over.mk er' :=
    IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft _ _
  let aSymm : oo ⟶ Over.mk ei :=
    IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToRight _ _
  obtain ⟨rrO, hrrOs, hrrOt⟩ := exists_liftPair_of_comp (D.map er') (D.map aRefl.left)
    (D.map oo.hom) (by rw [← D.map_comp]; exact congrArg D.map (Over.w aRefl))
    sₙ tₙ (𝟙 Wₙ) (𝟙 Wₙ) rr hrrs hrrt
  obtain ⟨riO, hriOs, hriOt⟩ := exists_liftPair_of_comp (D.map ei) (D.map aSymm.left)
    (D.map oo.hom) (by rw [← D.map_comp]; exact congrArg D.map (Over.w aSymm))
    sₙ tₙ tₙ sₙ ri hris hrit
  obtain ⟨rcO, hrcOs, hrcOt⟩ := exists_liftPair_of_comp (D.map ec) (D.map aComp.left)
    (D.map oo.hom) (by rw [← D.map_comp]; exact congrArg D.map (Over.w aComp))
    sₙ tₙ (cn.fst ≫ sₙ) (cn.snd ≫ tₙ) rc hrcs hrct
  have hmonoO : Mono ((Over.pullback (D.map oo.hom)).map ψ) := by
    have := mono_overPullback_map (D.map aMono.left)
      ((Over.pullback (D.map ejm)).map ψ) hjmMono
    have hcomp' : D.map aMono.left ≫ D.map ejm = D.map oo.hom := by
      rw [← D.map_comp]; exact congrArg D.map (Over.w aMono)
    rw [show (Over.pullback (D.map oo.hom)).map ψ =
        (iteratedBaseChangeIso (D.map ejm) (D.map aMono.left) (D.map oo.hom)
            hcomp' Rₙ).inv ≫
          (Over.pullback (D.map aMono.left)).map ((Over.pullback (D.map ejm)).map ψ) ≫
          (iteratedBaseChangeIso (D.map ejm) (D.map aMono.left) (D.map oo.hom)
            hcomp' Zₙ).hom from by
      rw [iteratedBaseChangeIso_naturality, Iso.inv_hom_id_assoc]]
    exact mono_comp' (IsIso.mono_of_iso _) (mono_comp' this (IsIso.mono_of_iso _))
  -- the descended relation as objects of the site
  have hoAff := ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS (D.map oo.hom)
    (hD oo.left) (hD nn)).out 2 1).mp (hAffine oo.hom)
  let WO := hoAff.1.pullback wn
  let RO := hoAff.1.pullback rn
  let wO := hoAff.1.fst wn
  let rO := hoAff.1.fst rn
  let bW : WO ⟶ Wn := hoAff.1.snd wn
  let bR : RO ⟶ Rn := hoAff.1.snd rn
  have hWO : IsPullback wO (yoneda.map bW) (D.map oo.hom) wn := hoAff.1.isPullback wn
  have hRO : IsPullback rO (yoneda.map bR) (D.map oo.hom) rn := hoAff.1.isPullback rn
  let εWO : Over.mk wO ≅ (Over.pullback (D.map oo.hom)).obj Wₙ :=
    Over.isoMk hWO.flip.isoPullback (by exact hWO.flip.isoPullback_hom_snd)
  let εRO : Over.mk rO ≅ (Over.pullback (D.map oo.hom)).obj Rₙ :=
    Over.isoMk hRO.flip.isoPullback (by exact hRO.flip.isoPullback_hom_snd)
  obtain ⟨sOO, hsOOdef⟩ : ∃ z : Over.mk rO ⟶ Over.mk wO,
      z = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map sₙ ≫ εWO.inv := ⟨_, rfl⟩
  obtain ⟨tOO, htOOdef⟩ : ∃ z : Over.mk rO ⟶ Over.mk wO,
      z = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map tₙ ≫ εWO.inv := ⟨_, rfl⟩
  let sO : RO ⟶ WO := yoneda.preimage sOO.left
  let tO : RO ⟶ WO := yoneda.preimage tOO.left
  have hsOl : yoneda.map sO = sOO.left := yoneda.map_preimage _
  have htOl : yoneda.map tO = tOO.left := yoneda.map_preimage _
  have hsOW : yoneda.map sO ≫ wO = rO := by rw [hsOl]; exact Over.w sOO
  have htOW : yoneda.map tO ≫ wO = rO := by rw [htOl]; exact Over.w tOO
  have hεWfst : εWO.hom.left ≫ pullback.fst wn (D.map oo.hom) = yoneda.map bW :=
    hWO.flip.isoPullback_hom_fst
  have hεRfst : εRO.hom.left ≫ pullback.fst rn (D.map oo.hom) = yoneda.map bR :=
    hRO.flip.isoPullback_hom_fst
  have hsoSq : sO ≫ bW = bR ≫ sn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, hsOl]
    have h1 : sOO ≫ εWO.hom = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map sₙ := by
      rw [hsOOdef]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h2 := congrArg (fun z : Over.mk rO ⟶ (Over.pullback (D.map oo.hom)).obj Wₙ =>
      z.left ≫ pullback.fst wn (D.map oo.hom)) h1
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, Rₙ, Wₙ,
      Over.mk_hom, pullback.lift_fst, hεWfst, reassoc_of% hεRfst, sₙ,
      Over.homMk_left] at h2
    exact h2
  have htoSq : tO ≫ bW = bR ≫ tn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, htOl]
    have h1 : tOO ≫ εWO.hom = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map tₙ := by
      rw [htOOdef]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h2 := congrArg (fun z : Over.mk rO ⟶ (Over.pullback (D.map oo.hom)).obj Wₙ =>
      z.left ≫ pullback.fst wn (D.map oo.hom)) h1
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, Rₙ, Wₙ,
      Over.mk_hom, pullback.lift_fst, hεWfst, reassoc_of% hεRfst, tₙ,
      Over.homMk_left] at h2
    exact h2
  have hsoSite : IsPullback bR sO sn bW := by
    apply IsPullback.of_map yoneda hsoSq.symm
    apply IsPullback.of_bot (v₂₂ := wn) ?_
      (by rw [← yoneda.map_comp, ← yoneda.map_comp, hsoSq]) hWO.flip
    rw [hsOW]
    exact hRO.flip
  have htoSite : IsPullback bR tO tn bW := by
    apply IsPullback.of_map yoneda htoSq.symm
    apply IsPullback.of_bot (v₂₂ := wn) ?_
      (by rw [← yoneda.map_comp, ← yoneda.map_comp, htoSq]) hWO.flip
    rw [htOW, htn]
    exact hRO.flip
  have hsOEtale : Etale (Q.map sO) := by
    let : Etale (Q.map sn) := hsnEtale
    exact (etale_iff_pullback_of_isPullback (hsoSite.map Q)).mpr inferInstance
  have htOEtale : Etale (Q.map tO) := by
    let : Etale (Q.map tn) := htnEtale
    exact (etale_iff_pullback_of_isPullback (htoSite.map Q)).mpr inferInstance
  have hWOAff : IsAffine (Q.obj WO) := by
    let : IsAffine (Q.obj Wn) := hWnAff
    let : _root_.AlgebraicGeometry.IsAffineHom (Q.map bW) := hoAff.2.property wn wO bW hWO
    exact isAffine_of_isAffineHom (Q.map bW)
  have hWOAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS WO
  have hROAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS RO
  have hwOFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wO :=
    isFinitePresentation_of_isPullback B S hS hWOAlg hWnAlg (hD oo.left) (hD nn)
      hWO.flip hWnFp
  have hrOFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rO :=
    isFinitePresentation_of_isPullback B S hS hROAlg hRnAlg (hD oo.left) (hD nn)
      hRO.flip hRnFp
  have hROqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS rO
    (hD oo.left) (hQc oo.left) hrOFp
  -- reflexivity, symmetry and transitivity of the descended relation
  have hsOO : εRO.hom ≫ (Over.pullback (D.map oo.hom)).map sₙ = sOO ≫ εWO.hom := by
    rw [hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have htOO : εRO.hom ≫ (Over.pullback (D.map oo.hom)).map tₙ = tOO ≫ εWO.hom := by
    rw [htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨rflO, hrflOdef⟩ : ∃ z : Over.mk wO ⟶ Over.mk rO, z = εWO.hom ≫ rrO ≫ εRO.inv :=
    ⟨_, rfl⟩
  have hrflS : rflO ≫ sOO = 𝟙 (Over.mk wO) := by
    rw [hrflOdef, hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrrOs]
    rw [show (Over.pullback (D.map oo.hom)).map (𝟙 Wₙ) = 𝟙 _ from
      (Over.pullback (D.map oo.hom)).map_id Wₙ, Category.id_comp, Iso.hom_inv_id]
  have hrflT : rflO ≫ tOO = 𝟙 (Over.mk wO) := by
    rw [hrflOdef, htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrrOt]
    rw [show (Over.pullback (D.map oo.hom)).map (𝟙 Wₙ) = 𝟙 _ from
      (Over.pullback (D.map oo.hom)).map_id Wₙ, Category.id_comp, Iso.hom_inv_id]
  obtain ⟨symO, hsymOdef⟩ : ∃ z : Over.mk rO ⟶ Over.mk rO, z = εRO.hom ≫ riO ≫ εRO.inv :=
    ⟨_, rfl⟩
  have hsymS : symO ≫ sOO = tOO := by
    rw [hsymOdef, hsOOdef, htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hriOs]
  have hsymT : symO ≫ tOO = sOO := by
    rw [hsymOdef, htOOdef, hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hriOt]
  let rflSite : WO ⟶ RO := yoneda.preimage rflO.left
  have hrflSite₁ : rflSite ≫ sO = 𝟙 WO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, hsOl, yoneda.map_id]
    simpa only [Over.comp_left, Over.id_left, Over.mk_left] using
      congrArg (fun z => z.left) hrflS
  have hrflSite₂ : rflSite ≫ tO = 𝟙 WO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, htOl, yoneda.map_id]
    simpa only [Over.comp_left, Over.id_left, Over.mk_left] using
      congrArg (fun z => z.left) hrflT
  let symSite : RO ⟶ RO := yoneda.preimage symO.left
  have hsymSite₁ : symSite ≫ sO = tO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, hsOl, htOl]
    simpa only [Over.comp_left] using congrArg (fun z => z.left) hsymS
  have hsymSite₂ : symSite ≫ tO = sO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, htOl, hsOl]
    simpa only [Over.comp_left] using congrArg (fun z => z.left) hsymT
  have hpoCond : yoneda.map (pullback.fst tO sO) ≫ yoneda.map tO =
      yoneda.map (pullback.snd tO sO) ≫ yoneda.map sO := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, pullback.condition]
  let Pₒ : Over (D.obj oo.left) := Over.mk (yoneda.map (pullback.fst tO sO) ≫ rO)
  let cfstₒ : Pₒ ⟶ Over.mk rO := Over.homMk (yoneda.map (pullback.fst tO sO)) rfl
  let csndₒ : Pₒ ⟶ Over.mk rO := Over.homMk (yoneda.map (pullback.snd tO sO)) (by
    show yoneda.map (pullback.snd tO sO) ≫ rO = yoneda.map (pullback.fst tO sO) ≫ rO
    calc yoneda.map (pullback.snd tO sO) ≫ rO
        = yoneda.map (pullback.snd tO sO) ≫ yoneda.map sO ≫ wO := by rw [hsOW]
      _ = yoneda.map (pullback.fst tO sO) ≫ yoneda.map tO ≫ wO := by
            rw [← Category.assoc, ← Category.assoc, ← hpoCond]
      _ = yoneda.map (pullback.fst tO sO) ≫ rO := by rw [htOW])
  have hcommₒ : cfstₒ ≫ tOO = csndₒ ≫ sOO := by
    apply Over.OverMorphism.ext
    simpa only [Over.comp_left, cfstₒ, csndₒ, Over.homMk_left, hsOl, htOl] using hpoCond
  have hPₒ : IsPullback cfstₒ csndₒ tOO sOO := by
    apply IsPullback.of_map (Over.forget (D.obj oo.left)) hcommₒ
    rw [show ((Over.forget (D.obj oo.left)).map tOO) = yoneda.map tO from htOl.symm,
      show ((Over.forget (D.obj oo.left)).map sOO) = yoneda.map sO from hsOl.symm]
    exact (IsPullback.of_hasPullback tO sO).map yoneda
  have hpbcn : IsPullback ((Over.pullback (D.map oo.hom)).map cn.fst)
      ((Over.pullback (D.map oo.hom)).map cn.snd)
      ((Over.pullback (D.map oo.hom)).map tₙ)
      ((Over.pullback (D.map oo.hom)).map sₙ) :=
    (overPullbackCone_isPullback tₙ sₙ).map (Over.pullback (D.map oo.hom))
  let ζ : Pₒ ⟶ (Over.pullback (D.map oo.hom)).obj cn.pt :=
    hpbcn.lift (cfstₒ ≫ εRO.hom) (csndₒ ≫ εRO.hom) (by
      simpa only [Category.assoc, ← htOO, ← hsOO] using
        congrArg (fun z : Pₒ ⟶ Over.mk wO => z ≫ εWO.hom) hcommₒ)
  have hζfst : ζ ≫ (Over.pullback (D.map oo.hom)).map cn.fst = cfstₒ ≫ εRO.hom :=
    hpbcn.lift_fst _ _ _
  have hζsnd : ζ ≫ (Over.pullback (D.map oo.hom)).map cn.snd = csndₒ ≫ εRO.hom :=
    hpbcn.lift_snd _ _ _
  obtain ⟨cmpO, hcmpOdef⟩ : ∃ z : Pₒ ⟶ Over.mk rO, z = ζ ≫ rcO ≫ εRO.inv := ⟨_, rfl⟩
  have hcmpS : cmpO ≫ sOO = cfstₒ ≫ sOO := by
    rw [hcmpOdef, hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrcOs,
      Functor.map_comp, reassoc_of% hζfst]
  have hcmpT : cmpO ≫ tOO = csndₒ ≫ tOO := by
    rw [hcmpOdef, htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrcOt,
      Functor.map_comp, reassoc_of% hζsnd]
  let cmpSite : pullback tO sO ⟶ RO := yoneda.preimage cmpO.left
  have hcmpSite₁ : cmpSite ≫ sO = pullback.fst tO sO ≫ sO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, yoneda.map_preimage, hsOl]
    simpa only [Over.comp_left, cfstₒ, Over.homMk_left] using
      congrArg (fun z => z.left) hcmpS
  have hcmpSite₂ : cmpSite ≫ tO = pullback.snd tO sO ≫ tO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, yoneda.map_preimage, htOl]
    simpa only [Over.comp_left, csndₒ, Over.homMk_left] using
      congrArg (fun z => z.left) hcmpT
  -- the atlas of the space compared with the descended relation
  let awO : W ⟶ WO := yoneda.preimage (hWO.flip.lift (yoneda.map awn)
    (pW ≫ limit.π D oo.left) (by rw [Category.assoc, limit.w]; exact hWnlim.w))
  let arO : KR ⟶ RO := yoneda.preimage (hRO.flip.lift (yoneda.map arn)
    (pR ≫ limit.π D oo.left) (by rw [Category.assoc, limit.w]; exact hRnlim.w))
  have hWOlim : IsPullback (yoneda.map awO) pW wO (limit.π D oo.left) := by
    have hh : IsPullback (yoneda.map awn) pW wn (limit.π D oo.left ≫ D.map oo.hom) := by
      rw [limit.w]
      exact hWnlim
    simpa only [awO, yoneda.map_preimage] using hh.of_right' hWO.flip
  have hROlim : IsPullback (yoneda.map arO) pR rO (limit.π D oo.left) := by
    have hh : IsPullback (yoneda.map arn) pR rn (limit.π D oo.left ≫ D.map oo.hom) := by
      rw [limit.w]
      exact hRnlim
    simpa only [arO, yoneda.map_preimage] using hh.of_right' hRO.flip
  have hawOb : awO ≫ bW = awn := by
    apply yoneda.map_injective
    simp [awO]
  have harOb : arO ≫ bR = arn := by
    apply yoneda.map_injective
    simp [arO]
  have hsOCompat : arO ≫ sO = kt ≫ awO := by
    apply yoneda.map_injective
    apply hWO.hom_ext
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, hsOW,
        hWOlim.w, hROlim.w, ← Category.assoc, ht]
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc,
        ← yoneda.map_comp sO bW, ← yoneda.map_comp awO bW, hsoSq, hawOb, yoneda.map_comp,
        ← Category.assoc, ← yoneda.map_comp arO bR, harOb, ← yoneda.map_comp, hsnCompat,
        yoneda.map_comp]
  have htOCompat : arO ≫ tO = ks ≫ awO := by
    apply yoneda.map_injective
    apply hWO.hom_ext
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, htOW,
        hWOlim.w, hROlim.w, ← Category.assoc, hs]
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc,
        ← yoneda.map_comp tO bW, ← yoneda.map_comp awO bW, htoSq, hawOb, yoneda.map_comp,
        ← Category.assoc, ← yoneda.map_comp arO bR, harOb, ← yoneda.map_comp, htnCompat,
        yoneda.map_comp]
  have hsqsO : IsPullback arO kt sO awO := by
    apply IsPullback.of_map yoneda hsOCompat
    apply IsPullback.of_bot _
      (by simpa only [Functor.map_comp] using congrArg yoneda.map hsOCompat) hWOlim
    simpa only [ht, hsOW] using hROlim
  have hsqtO : IsPullback arO ks tO awO := by
    apply IsPullback.of_map yoneda htOCompat
    apply IsPullback.of_bot _
      (by simpa only [Functor.map_comp] using congrArg yoneda.map htOCompat) hWOlim
    simpa only [hs, htOW] using hROlim
  -- joint monicity of the descended relation
  have hρcomm : yoneda.map sO ≫ wO = yoneda.map tO ≫ wO := by rw [hsOW, htOW]
  let KWO := atlasKernelPair B S hS wO (hD oo.left).diagonal_representable
  let ρ : RO ⟶ KWO.R := yoneda.preimage
    (KWO.kernelPair.lift (yoneda.map sO) (yoneda.map tO) hρcomm)
  have hρl : yoneda.map ρ =
      KWO.kernelPair.lift (yoneda.map sO) (yoneda.map tO) hρcomm := yoneda.map_preimage _
  have hρs : ρ ≫ KWO.s = sO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hρl]
    exact KWO.kernelPair.lift_fst _ _ _
  have hρt : ρ ≫ KWO.t = tO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hρl]
    exact KWO.kernelPair.lift_snd _ _ _
  have _ : IsIso εRO.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (D.obj oo.left)).map εRO.hom))
  have hνmono : Mono (εRO.hom.left ≫
      ((Over.pullback (D.map oo.hom)).map ψ).left) := by
    exact mono_comp' (IsIso.mono_of_iso _) (Over.mono_left_of_mono _)
  have hνfst : εRO.hom.left ≫ ((Over.pullback (D.map oo.hom)).map ψ).left ≫
      pullback.fst Zₙ.hom (D.map oo.hom) = yoneda.map bR ≫ yoneda.map ψ₀ := by
    simp only [Over.pullback_map_left, Rₙ, Over.mk_hom,
      pullback.lift_fst, ψ, Over.homMk_left, reassoc_of% hεRfst]
  have hνsnd : εRO.hom.left ≫ ((Over.pullback (D.map oo.hom)).map ψ).left ≫
      pullback.snd Zₙ.hom (D.map oo.hom) = rO := by
    simp only [Over.pullback_map_left, pullback.lift_snd]
    exact εRO.hom.w
  have hρmono : Mono (yoneda.map ρ) := by
    refine ⟨fun {T} a b hab => ?_⟩
    have ha : a ≫ yoneda.map sO = b ≫ yoneda.map sO := by
      rw [← hρs, yoneda.map_comp]
      simp only [← Category.assoc]
      rw [hab]
    have hb : a ≫ yoneda.map tO = b ≫ yoneda.map tO := by
      rw [← hρt, yoneda.map_comp]
      simp only [← Category.assoc]
      rw [hab]
    apply (cancel_mono (εRO.hom.left ≫ ((Over.pullback (D.map oo.hom)).map ψ).left)).mp
    apply pullback.hom_ext
    · simp only [Category.assoc, hνfst]
      apply KWn.kernelPair.hom_ext
      · simp only [Category.assoc, ← yoneda.map_comp ψ₀ KWn.s, hψs,
          ← yoneda.map_comp bR sn, ← hsoSq, yoneda.map_comp]
        simp only [← Category.assoc]
        rw [ha]
      · simp only [Category.assoc, ← yoneda.map_comp ψ₀ KWn.t, hψt,
          ← yoneda.map_comp bR tn, ← htoSq, yoneda.map_comp]
        simp only [← Category.assoc]
        rw [hb]
    · simp only [Category.assoc, hνsnd]
      rw [← hsOW]
      simp only [← Category.assoc]
      rw [ha]
  have hjmO : JointlyMono₂ ((Over.post (X := B.obj hS) B.inclusion).map sO)
      ((Over.post (X := B.obj hS) B.inclusion).map tO) :=
    jointlyMono₂_of_mono_to_kernelPair B S hS wO KWO.s KWO.t KWO.kernelPair
      sO tO ρ hρs hρt hρmono
  obtain ⟨Yᵢ, hYᵢalg, hYᵢfp, hYᵢiso⟩ := exists_model_of_descended_presentation
    B S hS hZ D oo.left hLim (hD oo.left) (hQc oo.left) (hQs oo.left) Y hY w hws hwe
    kt ks hwk hWOAff sO tO hsOEtale htOEtale hjmO rflSite hrflSite₁ hrflSite₂
    symSite hsymSite₁ hsymSite₂ cmpSite hcmpSite₁ hcmpSite₂ wO hρcomm hwOFp hROqc
    awO arO (by rw [← hpWDef]; exact hWOlim) hsqsO hsqtO
  exact ⟨oo.left, Yᵢ, hYᵢalg, hYᵢfp, hYᵢiso⟩

omit hSize hHomSize in
include hconv hDlim in
/-- **Stacks 07SK, essential surjectivity, under the chapter's convention.** Every algebraic
space of finite presentation over the limit of a cofiltered inverse system of quasi-compact,
quasi-separated algebraic spaces with affine transition morphisms is the base change of an
algebraic space of finite presentation over some stage.
This is the faithful statement of the tag. The source states no condition on the index: it
assumes only the convention of Section 70.2 (tag 07SD) that every ring considered has its
spectrum in the big fppf site, which for this system is
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`. The proof is the one of
`AlgebraicGeometry.Space.exists_model_of_finitePresentation`, with each appeal to the bounds on the
index replaced by the convention: affineness of the projections from the limit is
`AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits`, the limit of the
affine charts over a stage lies in the site because that diagram is a lift of a diagram of base
changes, and the algebraicity of the limit is taken from Stacks 07SF under the convention,
`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits`, as `hDlim`. -/
public theorem exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits
    (Y : Over (limit D))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom) :
    ∃ (i : I) (Yᵢ : Over (D.obj i)),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
        Nonempty (Y ≅ (Over.pullback (limit.π D i)).obj Yᵢ)  := by
  classical
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨U₀, p₀, hU₀, hs₀, he₀⟩ := exists_affine_etale_atlas B S hS
    (D.obj i) (hD i) (hQc i)
  let U₀' : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hp₀ := represented_etale_of_isEtale B S hS p₀ he₀
  obtain ⟨U, p, q, hp⟩ :=
    AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D hconv
      hAffine i U₀' p₀
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) Q
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : E.presheaf.IsStableUnderBaseChange := E.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : E.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition E (etaleInverseImageIsStableUnderComposition _)
  have hs : P.presheaf p := P.presheaf.of_isPullback hp.flip hs₀
  have he : E.presheaf p := E.presheaf.of_isPullback hp.flip hp₀
  have hX := hDlim
  have hXqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    hX (hQs i)
    (isQuasiSeparated_of_isAffineHom B S hS hX (hD i) (limit.π D i)
      (AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D hconv
        hAffine i))
  have hYqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS hZ hY hXqs hFp.2.2
  obtain ⟨W, w, g, hws, hwe, hw, hg⟩ :=
    exists_affine_finitePresentation_chart B S hS hX hY Y.hom hFp U p hs he
  let K := atlasKernelPair B S hS w hY.diagonal_representable
  have hKt := atlasKernelPair_target_finitePresentation B S hS hZ hY hYqs W w hwe
  have hKg : AlgebraicGeometry.FinitePresentation (Q.map (K.s ≫ g)) := by
    let : LocallyOfFinitePresentation (Q.map K.s) := hKt.1
    let : QuasiCompact (Q.map K.s) := hKt.2.1
    let : QuasiSeparated (Q.map K.s) := hKt.2.2
    let : LocallyOfFinitePresentation (Q.map g) := hg.1
    let : QuasiCompact (Q.map g) := hg.2.1
    let : QuasiSeparated (Q.map g) := hg.2.2
    rw [Q.map_comp]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W.obj) := W.property
  obtain ⟨j, Wj, wj, aw, hwj, hWjaff, hWmodel⟩ := exists_affine_site_model_over_affine_chart_conv
    B S hS hZ D hD hAffine hQc hQs hconv i U₀' p₀ hp₀ U p q hp W.obj g hg
  obtain ⟨k, Rk, rk, ar, hrk, hRmodel⟩ := exists_site_model_over_affine_chart_conv
    B S hS hZ D hD hAffine hQc hQs hconv i U₀' p₀ hp₀ U p q hp
      K.R (K.s ≫ g) hKg
  let l := IsCofiltered.min j.left k.left
  let ej : l ⟶ j.left := IsCofiltered.minToLeft _ _
  let ek : l ⟶ k.left := IsCofiltered.minToRight _ _
  let pW := yoneda.map g ≫ p
  let pR := yoneda.map (K.s ≫ g) ≫ p
  obtain ⟨WlA, wl, bl, hbl⟩ := hAffine ej ⟨Wj, hWjaff⟩ wj
  let Wl := WlA.obj
  have hwl : AlgebraicGeometry.Space.IsFinitePresentation B S hS wl :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wj)
      (hD l) (hD j.left) hbl.flip hwj
  let awl : W.obj ⟶ Wl := yoneda.preimage (hbl.flip.lift (yoneda.map aw)
    (pW ≫ limit.π D l) (by rw [Category.assoc, limit.w]; exact hWmodel.w))
  have hWl : IsPullback (yoneda.map awl) pW wl (limit.π D l) := by
    have hh : IsPullback (yoneda.map aw) pW wj (limit.π D l ≫ D.map ej) := by
      rw [limit.w]
      exact hWmodel
    simpa only [awl, yoneda.map_preimage] using hh.of_right' hbl.flip
  obtain ⟨Rl, rl, arl, hrl, hRl⟩ := advance_represented_model B S hS
    (hD l) (hD k.left) rk ar pR (limit.π D l) (D.map ek) (limit.π D k.left)
    (limit.w D ek) (hAffine ek) hrk hRmodel
  let KW := atlasKernelPair B S hS wl (hD l).diagonal_representable
  have hWlAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl
  have hKWAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS KW.R
  have hKWt : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map KW.s) :=
    isFinitePresentation_of_isPullback B S hS hKWAlg hWlAlg hWlAlg (hD l)
      KW.kernelPair.flip hwl
  let vKW := yoneda.map KW.s ≫ wl
  have hKWfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS vKW :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hKWAlg hWlAlg (hD l)
      (yoneda.map KW.s) wl hKWt hwl
  have ht : yoneda.map K.s ≫ pW = pR := by
    simp only [pW, pR, Functor.map_comp, Category.assoc]
  have hs : yoneda.map K.t ≫ pW = pR := by
    rw [← ht]
    simpa only [pW, hw, Category.assoc] using
      congrArg (fun t => t ≫ Y.hom) K.kernelPair.w.symm
  let b : yoneda.obj K.R ⟶ yoneda.obj KW.R := KW.kernelPair.lift
    (yoneda.map K.s ≫ yoneda.map awl) (yoneda.map K.t ≫ yoneda.map awl) (by
      simp only [Category.assoc, hWl.w]
      rw [← Category.assoc, ht, ← Category.assoc, hs])
  have hb : b ≫ vKW = pR ≫ limit.π D l := by
    simp only [b, vKW, IsPullback.lift_fst_assoc]
    rw [Category.assoc, hWl.w, ← Category.assoc, ht]
  let source := Over.mk rl
  let target := Over.mk vKW
  let er : Over.mk pR ≅ (Over.pullback (limit.π D l)).obj source :=
    Over.isoMk hRl.isoPullback (by exact hRl.isoPullback_hom_snd)
  let f : (Over.pullback (limit.π D l)).obj source ⟶
      (Over.pullback (limit.π D l)).obj target :=
    Over.homMk (pullback.lift (er.inv.left ≫ b)
      (pullback.snd rl (limit.π D l)) (by
        show (er.inv.left ≫ b) ≫ vKW = _
        rw [Category.assoc, hb, ← Category.assoc]
        exact congrArg (fun t => t ≫ limit.π D l) er.inv.w)) (by simp [source, target])
  obtain ⟨m, em, gm, αm, βm, hαm, hβm, hgm⟩ :=
    exists_morphism_after_baseChange_of_siteContainsBaseChangeLimits
    B S hS hZ D hD hAffine hQc hQs hconv hDlim l source target
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rl) hKWAlg hrl hKWfp f
  have hαmEq := iteratedBaseChangeIso_unique (D.map em) (limit.π D m) (limit.π D l)
    (limit.w D em) source αm hαm
  have hβmEq := iteratedBaseChangeIso_unique (D.map em) (limit.π D m) (limit.π D l)
    (limit.w D em) target βm hβm
  rw [hαmEq, hβmEq] at hgm
  have hmAffine := ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS (D.map em)
    (hD m) (hD l)).out 2 1).mp (hAffine em)
  let Rm := hmAffine.1.pullback rl
  let Wm := hmAffine.1.pullback wl
  let rm := hmAffine.1.fst rl
  let wm := hmAffine.1.fst wl
  have hRm : IsPullback rm (yoneda.map (hmAffine.1.snd rl)) (D.map em) rl :=
    hmAffine.1.isPullback rl
  have hWm : IsPullback wm (yoneda.map (hmAffine.1.snd wl)) (D.map em) wl :=
    hmAffine.1.isPullback wl
  have hWmAffineHom : _root_.AlgebraicGeometry.IsAffineHom (Q.map (hmAffine.1.snd wl)) :=
    hmAffine.2.property wl wm (hmAffine.1.snd wl) hWm
  have hWmAffine : IsAffine (Q.obj Wm) := by
    let : IsAffine (Q.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
        WlA)) := WlA.property
    let : _root_.AlgebraicGeometry.IsAffineHom (Q.map (hmAffine.1.snd wl)) := hWmAffineHom
    exact isAffine_of_isAffineHom (Q.map (hmAffine.1.snd wl))
  have hRmFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rm :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rm)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rl) (hD m) (hD l) hRm.flip hrl
  have hWmFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wm :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wm)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl) (hD m) (hD l) hWm.flip hwl
  let st : target ⟶ Over.mk wl := Over.homMk (yoneda.map KW.s) rfl
  let tt : target ⟶ Over.mk wl := Over.homMk (yoneda.map KW.t) KW.kernelPair.w.symm
  let sm₀ := gm ≫ (Over.pullback (D.map em)).map st
  let tm₀ := gm ≫ (Over.pullback (D.map em)).map tt
  let sm : Rm ⟶ Wm := yoneda.preimage
    (hRm.flip.isoPullback.hom ≫ sm₀.left ≫ hWm.flip.isoPullback.inv)
  let tm : Rm ⟶ Wm := yoneda.preimage
    (hRm.flip.isoPullback.hom ≫ tm₀.left ≫ hWm.flip.isoPullback.inv)
  have hsm : yoneda.map sm ≫ wm = rm := by
    simp only [sm, yoneda.map_preimage, Category.assoc, IsPullback.isoPullback_inv_snd]
    rw [show sm₀.left ≫ pullback.snd wl (D.map em) =
      pullback.snd rl (D.map em) from sm₀.w, hRm.flip.isoPullback_hom_snd]
  have htm : yoneda.map tm ≫ wm = rm := by
    simp only [tm, yoneda.map_preimage, Category.assoc, IsPullback.isoPullback_inv_snd]
    rw [show tm₀.left ≫ pullback.snd wl (D.map em) =
      pullback.snd rl (D.map em) from tm₀.w, hRm.flip.isoPullback_hom_snd]
  let arm : K.R ⟶ Rm := yoneda.preimage (hRm.flip.lift (yoneda.map arl)
    (pR ≫ limit.π D m) (by rw [Category.assoc, limit.w]; exact hRl.w))
  let awm : W.obj ⟶ Wm := yoneda.preimage (hWm.flip.lift (yoneda.map awl)
    (pW ≫ limit.π D m) (by rw [Category.assoc, limit.w]; exact hWl.w))
  have hRlim : IsPullback (yoneda.map arm) pR rm (limit.π D m) := by
    have hh : IsPullback (yoneda.map arl) pR rl (limit.π D m ≫ D.map em) := by
      rw [limit.w]
      exact hRl
    simpa only [arm, yoneda.map_preimage] using hh.of_right' hRm.flip
  have hWlim : IsPullback (yoneda.map awm) pW wm (limit.π D m) := by
    have hh : IsPullback (yoneda.map awl) pW wl (limit.π D m ≫ D.map em) := by
      rw [limit.w]
      exact hWl
    simpa only [awm, yoneda.map_preimage] using hh.of_right' hWm.flip
  have harm : yoneda.map arm ≫ yoneda.map (hmAffine.1.snd rl) = yoneda.map arl := by
    simp [arm]
  have hawm : yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl) = yoneda.map awl := by
    simp [awm]
  have harPB : yoneda.map arm ≫ hRm.flip.isoPullback.hom =
      er.hom.left ≫
        (iteratedBaseChangeIso (D.map em) (limit.π D m) (limit.π D l)
          (limit.w D em) source).inv.left ≫
          pullback.fst ((Over.pullback (D.map em)).obj source).hom (limit.π D m) := by
    apply pullback.hom_ext
    · simp [arm, er, source, iteratedBaseChangeIso, Category.assoc]
    · simp [arm, er, source, iteratedBaseChangeIso, Category.assoc]
  have hgm' : yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
      pullback.fst vKW (D.map em) = b := by
    have hh := congrArg (fun z => er.hom ≫
      (iteratedBaseChangeIso (D.map em) (limit.π D m) (limit.π D l)
        (limit.w D em) source).inv ≫ z) hgm
    simp only [Iso.inv_hom_id_assoc] at hh
    have hh' := congrArg (fun z => z.left ≫ pullback.fst vKW (limit.π D l)) hh
    have her : er.hom.left ≫ er.inv.left = 𝟙 _ :=
      congrArg (fun z => z.left) er.hom_inv_id
    simp only [Over.comp_left, Category.assoc] at hh'
    have hβfst := iteratedBaseChangeIso_hom_fst (D.map em) (limit.π D m)
      (limit.π D l) (limit.w D em) target
    change (iteratedBaseChangeIso (D.map em) (limit.π D m) (limit.π D l)
      (limit.w D em) target).hom.left ≫ pullback.fst vKW (limit.π D l) = _ at hβfst
    rw [hβfst] at hh'
    rw [reassoc_of% harPB]
    simpa only [source, target,
      Over.pullback_map_left, Over.pullback_obj_hom, Over.mk_hom, f,
      Over.homMk_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      her, reassoc_of% her, Category.id_comp] using hh'.symm
  have hsmCompat : arm ≫ sm = K.s ≫ awm := by
    apply yoneda.map_injective
    apply hWm.hom_ext
    · simp only [Functor.map_comp, Category.assoc, hsm, hRlim.w,
        hWlim.w]
      rw [← Category.assoc, ht]
    · simp only [Functor.map_comp, Category.assoc, sm, yoneda.map_preimage,
        IsPullback.isoPullback_inv_fst]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫
        (gm ≫ (Over.pullback (D.map em)).map st).left ≫
          pullback.fst wl (D.map em) =
        yoneda.map K.s ≫ yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl)
      simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, hawm, source, target, st, Over.mk_hom, Over.homMk_left]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
        pullback.fst vKW (D.map em) ≫ yoneda.map KW.s = _
      rw [reassoc_of% hgm']
      simp [b]
  have htmCompat : arm ≫ tm = K.t ≫ awm := by
    apply yoneda.map_injective
    apply hWm.hom_ext
    · simp only [Functor.map_comp, Category.assoc, htm, hRlim.w,
        hWlim.w]
      rw [← Category.assoc, hs]
    · simp only [Functor.map_comp, Category.assoc, tm, yoneda.map_preimage,
        IsPullback.isoPullback_inv_fst]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫
        (gm ≫ (Over.pullback (D.map em)).map tt).left ≫
          pullback.fst wl (D.map em) =
        yoneda.map K.t ≫ yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl)
      simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, hawm, source, target, tt, Over.mk_hom, Over.homMk_left]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
        pullback.fst vKW (D.map em) ≫ yoneda.map KW.t = _
      rw [reassoc_of% hgm']
      simp [b]
  have hsmSquare : IsPullback arm K.s sm awm := by
    apply IsPullback.of_map yoneda hsmCompat
    apply IsPullback.of_bot _ (by
      simpa only [Functor.map_comp] using congrArg yoneda.map hsmCompat) hWlim
    simpa only [hsm, ht] using hRlim
  have htmSquare : IsPullback arm K.t tm awm := by
    apply IsPullback.of_map yoneda htmCompat
    apply IsPullback.of_bot _ (by
      simpa only [Functor.map_comp] using congrArg yoneda.map htmCompat) hWlim
    simpa only [htm, hs] using hRlim
  have hRmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rm
  have hWmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wm
  have hSmFp := finitePresentation_of_yoneda B S hS sm
    (isFinitePresentation_overHom B S hS hZ (hD m) (hQc m) (hQs m)
      (Over.mk rm) (Over.mk wm) hRmAlg hWmAlg hRmFp hWmFp
      (Over.homMk (yoneda.map sm) hsm))
  have hTmFp := finitePresentation_of_yoneda B S hS tm
    (isFinitePresentation_overHom B S hS hZ (hD m) (hQc m) (hQs m)
      (Over.mk rm) (Over.mk wm) hRmAlg hWmAlg hRmFp hWmFp
      (Over.homMk (yoneda.map tm) htm))
  let WmA : AlgebraicGeometry.BigAffineFppf B S hS := ⟨Wm, hWmAffine⟩
  let : Etale ((Over.pullback (Q.map awm)).obj (Over.mk (Q.map sm))).hom :=
    (etale_iff_pullback_of_isPullback (hsmSquare.map Q)).mp
      (hwe.property w (yoneda.map K.t) K.s K.kernelPair.flip)
  let : Etale ((Over.pullback (Q.map awm)).obj (Over.mk (Q.map tm))).hom :=
    (etale_iff_pullback_of_isPullback (htmSquare.map Q)).mp
      (hwe.property w (yoneda.map K.s) K.t K.kernelPair)
  obtain ⟨js, hjs⟩ := eventually_etale_over_affine_chart_conv B S hS hZ D hD
    hAffine hQc hQs hconv m WmA wm W pW awm hWlim.flip (Over.mk (Q.map sm)) hSmFp
  obtain ⟨jt, hjt⟩ := eventually_etale_over_affine_chart_conv B S hS hZ D hD
    hAffine hQc hQs hconv m WmA wm W pW awm hWlim.flip (Over.mk (Q.map tm)) hTmFp
  let n := IsCofiltered.min js jt
  let as' := IsCofiltered.minToLeft js jt
  let at' := IsCofiltered.minToRight js jt
  let En := affineStageChartOverDiagramConv B S hS hZ D hD
    hAffine hQc hQs hconv m WmA wm hAffine
  let Cn := affineStageChart B S hS D m WmA wm hAffine n
  have hsChart : Etale (pullback.snd (Q.map sm) (Q.map Cn.toChart)) := by
    let : Etale ((Over.pullback (Q.map (En.obj js).hom)).obj (Over.mk (Q.map sm))).hom := hjs
    exact etale_pullback_of_etale_pullback (Q.map (En.obj js).hom)
      (Q.map (En.map as').left) (Q.map (En.obj n).hom)
      (by rw [← Q.map_comp]; exact congrArg Q.map (En.map as').w) (Over.mk (Q.map sm))
  have htChart : Etale (pullback.snd (Q.map tm) (Q.map Cn.toChart)) := by
    let : Etale ((Over.pullback (Q.map (En.obj jt).hom)).obj (Over.mk (Q.map tm))).hom := hjt
    exact etale_pullback_of_etale_pullback (Q.map (En.obj jt).hom)
      (Q.map (En.map at').left) (Q.map (En.obj n).hom)
      (by rw [← Q.map_comp]; exact congrArg Q.map (En.map at').w) (Over.mk (Q.map tm))
  let Wn := Cn.U.obj
  let wn := Cn.toStage
  let Rn := pullback sm Cn.toChart
  let sn : Rn ⟶ Wn := pullback.snd sm Cn.toChart
  let br : Rn ⟶ Rm := pullback.fst sm Cn.toChart
  let rn := yoneda.map sn ≫ wn
  have hRn : IsPullback (yoneda.map br) rn rm (D.map n.hom) := by
    have hh := ((IsPullback.of_hasPullback sm Cn.toChart).map yoneda).paste_vert
      Cn.isPullback.flip
    simpa only [hsm] using hh
  let tn : Rn ⟶ Wn := yoneda.preimage (Cn.isPullback.lift rn
    (yoneda.map br ≫ yoneda.map tm) (by
      simp only [Category.assoc, htm]
      exact hRn.w.symm))
  have htn : yoneda.map tn ≫ wn = rn := by simp [tn, wn]
  have htnBr : br ≫ tm = tn ≫ Cn.toChart := by
    apply yoneda.map_injective
    simp [tn]
  have htnSquare : IsPullback br tn tm Cn.toChart := by
    apply IsPullback.of_map yoneda htnBr
    apply IsPullback.of_bot _ (by simpa only [Functor.map_comp] using congrArg yoneda.map htnBr)
      Cn.isPullback.flip
    simpa only [← show wn = Cn.toStage from rfl, htm, htn] using hRn
  have hsnEtale : Etale (Q.map sn) :=
    (etale_iff_pullback_of_isPullback ((IsPullback.of_hasPullback sm Cn.toChart).map Q)).mpr hsChart
  have htnEtale : Etale (Q.map tn) :=
    (etale_iff_pullback_of_isPullback (htnSquare.map Q)).mpr htChart
  have hRnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rn
  have hWnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wn
  have hRnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rn :=
    isFinitePresentation_of_isPullback B S hS hRnAlg hRmAlg (hD n.left) (hD m) hRn hRmFp
  have hWnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wn :=
    isFinitePresentation_of_isPullback B S hS hWnAlg hWmAlg (hD n.left) (hD m)
      Cn.isPullback.flip hWmFp
  let awn : W.obj ⟶ Wn := yoneda.preimage (Cn.isPullback.flip.lift (yoneda.map awm)
    (pW ≫ limit.π D n.left) (by rw [Category.assoc, limit.w]; exact hWlim.w))
  let arn : K.R ⟶ Rn := yoneda.preimage (hRn.lift (yoneda.map arm)
    (pR ≫ limit.π D n.left) (by rw [Category.assoc, limit.w]; exact hRlim.w))
  have hWnlim : IsPullback (yoneda.map awn) pW wn (limit.π D n.left) := by
    have hh : IsPullback (yoneda.map awm) pW wm (limit.π D n.left ≫ D.map n.hom) := by
      rw [limit.w]
      exact hWlim
    simpa only [awn, yoneda.map_preimage] using hh.of_right' Cn.isPullback.flip
  have hRnlim : IsPullback (yoneda.map arn) pR rn (limit.π D n.left) := by
    have hh : IsPullback (yoneda.map arm) pR rm (limit.π D n.left ≫ D.map n.hom) := by
      rw [limit.w]
      exact hRlim
    simpa only [arn, yoneda.map_preimage] using hh.of_right' hRn
  have hArnBr : yoneda.map arn ≫ yoneda.map br = yoneda.map arm := by simp [arn]
  have hAwnBw : yoneda.map awn ≫ yoneda.map Cn.toChart = yoneda.map awm := by simp [awn]
  have hsnCompat : arn ≫ sn = K.s ≫ awn := by
    apply yoneda.map_injective
    apply Cn.isPullback.hom_ext
    · simp only [Functor.map_comp, Category.assoc]
      show yoneda.map arn ≫ rn = yoneda.map K.s ≫ yoneda.map awn ≫ wn
      rw [hRnlim.w, hWnlim.w, ← Category.assoc, ht]
    · simp only [Functor.map_comp, Category.assoc]
      have hsn : sn ≫ Cn.toChart = br ≫ sm := pullback.condition.symm
      rw [← yoneda.map_comp sn Cn.toChart, hsn, yoneda.map_comp,
        ← Category.assoc, hArnBr, hAwnBw]
      exact congrArg yoneda.map hsmCompat
  have htnCompat : arn ≫ tn = K.t ≫ awn := by
    apply yoneda.map_injective
    apply Cn.isPullback.hom_ext
    · simp only [Functor.map_comp, Category.assoc]
      show yoneda.map arn ≫ yoneda.map tn ≫ wn =
        yoneda.map K.t ≫ yoneda.map awn ≫ wn
      rw [htn, hRnlim.w, hWnlim.w, ← Category.assoc, hs]
    · simp only [Functor.map_comp, Category.assoc]
      rw [← yoneda.map_comp tn Cn.toChart, ← htnBr, yoneda.map_comp,
        ← Category.assoc, hArnBr, hAwnBw]
      exact congrArg yoneda.map htmCompat
  have hsnSquare : IsPullback arn K.s sn awn := by
    apply IsPullback.of_map yoneda hsnCompat
    apply IsPullback.of_bot _ (by simpa only [Functor.map_comp] using congrArg yoneda.map hsnCompat)
      hWnlim
    simpa only [ht] using hRnlim
  have htnLimitSquare : IsPullback arn K.t tn awn := by
    apply IsPullback.of_map yoneda htnCompat
    apply IsPullback.of_bot _ (by simpa only [Functor.map_comp] using congrArg yoneda.map htnCompat)
      hWnlim
    simpa only [htn, hs] using hRnlim
  have hRnlim' : IsPullback (yoneda.map arn) (yoneda.map K.s ≫ w ≫ Y.hom)
      (yoneda.map sn ≫ wn) (limit.π D n.left) := by
    rw [show (yoneda.map K.s ≫ w ≫ Y.hom) = pR from by rw [← hw]; exact ht]
    exact hRnlim
  exact exists_model_of_stage_relation_conv B S hS hZ D hD hAffine hQc hQs hconv
    n.left hX Y hY w hws hwe K.s K.t K.kernelPair
    (show IsAffine (Q.obj Wn) from Cn.U.property) wn sn tn htn hsnEtale htnEtale
    hWnFp hRnFp awn arn (by rw [← hw]; exact hWnlim) hRnlim' hsnCompat htnCompat

end AlgebraicGeometry.Space

end
