module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.AbelianSheaves
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.Injectives
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Derived direct image and restriction to the small pro-étale site

For a morphism of schemes, restricting the derived direct image on the big pro-étale site to the
small site agrees naturally with the derived direct image of the restriction to the small site.

## Main results

* `bigSmallDerivedPushforwardIso` is the natural comparison isomorphism on unbounded derived
  categories.

## Implementation notes

Right derived direct images are presented by a functor on derived categories together with its
universal transformation, independently of a choice of K-injective resolutions. Restriction is
the exact inverse-image functor of the small-site inclusion, hence acts directly on unbounded
derived categories.

## References

* [Stacks Project, Tag 0F68](https://stacks.math.columbia.edu/tag/0F68)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.Sites

universe u

namespace AlgebraicGeometry.ProEtale

section DerivedUnit

universe u₁ v₁ u₂ v₂ w₁ w₂ w
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  [IsGrothendieckAbelian.{w} C]

private lemma unit_isIso
    (F : C ⥤ D) [F.Additive]
    (R : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso C (.up ℤ))]
    (I : CochainComplex C ℤ) [I.IsKInjective] : IsIso (α.app I) := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  let W := HomologicalComplex.homotopyEquivalences C (.up ℤ)
  let Fh := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let e : q ⋙ Fh ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)
  let hq := Localization.fullyFaithfulWhiskeringLeft q W (DerivedCategory D)
  let β : Fh ⟶ DerivedCategory.Qh ⋙ R := hq.preimage
    (e.hom ≫ α ≫ Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).inv R)
  have hβ : Functor.whiskerLeft q β =
      e.hom ≫ α ≫ Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).inv R :=
    hq.map_preimage _
  have : Fh.IsRightDerivedFunctor e.inv W :=
    Functor.isRightDerivedFunctor_of_inverts W Fh e
  have : Fh.IsLeftKanExtension e.inv :=
    Functor.IsRightDerivedFunctor.isLeftKanExtension Fh e.inv W
  have : R.IsLeftKanExtension α :=
    Functor.IsRightDerivedFunctor.isLeftKanExtension R α (HomologicalComplex.quasiIso C (.up ℤ))
  have : R.IsRightDerivedFunctor β (HomotopyCategory.quasiIso C (.up ℤ)) := by
    constructor
    apply (Functor.isLeftKanExtension_iff_postcompose e.inv DerivedCategory.Q
      (DerivedCategory.quotientCompQhIso C) β α ?_).mpr inferInstance
    rw [hβ]
    ext K
    simp
  have hres (K : CochainComplex C ℤ) :
      ∃ (I : CochainComplex C ℤ) (f : K ⟶ I), I.IsKInjective ∧ QuasiIso f :=
    ⟨_, (Stacks.Injectives.kInjectiveResolutionInclusion C).app K, inferInstance, inferInstance⟩
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    Fh hres).2 DerivedCategory.Qh R β I inferInstance
  have hb : IsIso ((e.hom ≫ α ≫
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).inv R).app I) := by
    rw [← hβ]
    exact this
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, isIso_comp_left_iff,
    isIso_comp_right_iff] using hb

end DerivedUnit

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-- Direct image of abelian sheaves along the morphism of big pro-étale topoi given by `f`. -/
public abbrev bigPush : BigAb B T ⥤ BigAb B S :=
  (Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (BigProetaleOver.topology B S.obj S.property)
    (BigProetaleOver.topology B T.obj T.property)

/-- Direct image of abelian sheaves along the base-changed morphism of small pro-étale sites. -/
public abbrev smallPush : SmallAb B T ⥤ SmallAb B S :=
  (smallProetaleBaseChange B T S f).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (SmallProetale.topology B S.obj S.property)
    (SmallProetale.topology B T.obj T.property)

/-- Restriction of abelian sheaves from the big pro-étale site over `X` to the small
pro-étale site of `X`. -/
public abbrev restrict (X : B.Scheme) : BigAb B X ⥤ SmallAb B X :=
  abelianInverseImage (smallProetaleToBigProetaleMorphism B X X (𝟙 X))

/-- Restriction to the small pro-étale site is additive. -/
public instance restrict_additive (X : B.Scheme) : (restrict B X).Additive :=
  exactFunctor_le_additiveFunctor _ _ _
    (abelianInverseImage_exact
      (smallProetaleToBigProetaleMorphism B X X (𝟙 X)))

/-- Restriction to the small pro-étale site preserves finite limits. -/
public instance restrict_preservesFiniteLimits (X : B.Scheme) :
    PreservesFiniteLimits (restrict B X) := by
  change PreservesFiniteLimits (abelianInverseImage _)
  infer_instance

/-- Restriction to the small pro-étale site preserves finite colimits. -/
public instance restrict_preservesFiniteColimits (X : B.Scheme) :
    PreservesFiniteColimits (restrict B X) := by
  change PreservesFiniteColimits (abelianInverseImage _)
  infer_instance

private instance bigPush_additive : (bigPush B T S f).Additive where
  map_add := by intros; rfl

private instance smallPush_additive : (smallPush B T S f).Additive where
  map_add := by intros; rfl

private instance bigAb_grothendieck (X : B.Scheme) :
    IsGrothendieckAbelian.{u + 1} (BigAb B X) := by
  let : HasSheafify
      ((equivSmallModel.{u + 1} (BigProetaleOver B X.obj X.property)).inverse.inducedTopology
        (BigProetaleOver.topology B X.obj X.property)) AddCommGrpCat.{u + 1} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u + 1, 0}
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1}
    (BigProetaleOver.topology B X.obj X.property) AddCommGrpCat.{u + 1}

private instance smallAb_grothendieck (X : B.Scheme) :
    IsGrothendieckAbelian.{u + 1} (SmallAb B X) := by
  let : HasSheafify
      ((equivSmallModel.{u + 1} (SmallProetale B X.obj X.property)).inverse.inducedTopology
        (SmallProetale.topology B X.obj X.property)) AddCommGrpCat.{u + 1} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u + 1, 0}
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1}
    (SmallProetale.topology B X.obj X.property) AddCommGrpCat.{u + 1}

/-- Restriction of abelian sheaves to the small pro-étale site of `X` is the direct image
along the inclusion of the small site into the big site over `X`. -/
private noncomputable def restrictDirectIso (X : B.Scheme) :
    restrict B X ≅
      (SmallProetale.inclusion B X.obj X.property).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (SmallProetale.topology B X.obj X.property)
        (BigProetaleOver.topology B X.obj X.property) := by
  have h : smallProetaleToBigProetaleFunctor B X X (𝟙 X) =
      SmallProetale.inclusion B X.obj X.property := by
    simp [smallProetaleToBigProetaleFunctor, Over.mapId_eq, Functor.comp_id]
  refine restrictionIso (𝟙 X) ≪≫ ?_
  exact Functor.sheafPushforwardContinuousIso (eqToIso h) AddCommGrpCat.{u + 1}
    (SmallProetale.topology B X.obj X.property)
    (BigProetaleOver.topology B X.obj X.property)

private noncomputable def bigSmallPushIso :
    restrict B T ⋙ smallPush B T S f ≅ bigPush B T S f ⋙ restrict B S := by
  let q := smallProetaleBaseChange B T S f
  let iT := SmallProetale.inclusion B T.obj T.property
  let iS := SmallProetale.inclusion B S.obj S.property
  let p := Over.pullback f
  let JT := SmallProetale.topology B T.obj T.property
  let JS := SmallProetale.topology B S.obj S.property
  let KT := BigProetaleOver.topology B T.obj T.property
  let KS := BigProetaleOver.topology B S.obj S.property
  letI : (q ⋙ iT).IsContinuous JS KT := Functor.isContinuous_comp q iT JS JT KT
  letI : (iS ⋙ p).IsContinuous JS KT := Functor.isContinuous_comp iS p JS KS KT
  exact Functor.isoWhiskerRight (restrictDirectIso B T) _ ≪≫
    Functor.sheafPushforwardContinuousComp q iT AddCommGrpCat.{u + 1} JS JT KT ≪≫
    Functor.sheafPushforwardContinuousIso
      (eqToIso (smallProetaleBaseChange_comp_inclusion B T S f))
      AddCommGrpCat.{u + 1} JS KT ≪≫
    (Functor.sheafPushforwardContinuousComp iS p AddCommGrpCat.{u + 1} JS KS KT).symm ≪≫
    Functor.isoWhiskerLeft _ (restrictDirectIso B S).symm

private lemma bigSmallDerivedPushforward_nonempty
    [HasDerivedCategory (BigAb B T)] [HasDerivedCategory (BigAb B S)]
    [HasDerivedCategory (SmallAb B T)] [HasDerivedCategory (SmallAb B S)]
    (Rbig : DerivedCategory (BigAb B T) ⥤ DerivedCategory (BigAb B S))
    (Rsmall : DerivedCategory (SmallAb B T) ⥤ DerivedCategory (SmallAb B S))
    (αbig : (bigPush B T S f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rbig)
    (αsmall : (smallPush B T S f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rsmall)
    [Rbig.IsRightDerivedFunctor αbig
      (HomologicalComplex.quasiIso (BigAb B T) (ComplexShape.up ℤ))]
    [Rsmall.IsRightDerivedFunctor αsmall
      (HomologicalComplex.quasiIso (SmallAb B T) (ComplexShape.up ℤ))] :
    Nonempty (Rbig ⋙ (restrict B S).mapDerivedCategory ≅
      (restrict B T).mapDerivedCategory ⋙ Rsmall) := by
  classical
  let I := Stacks.Injectives.kInjectiveResolutionFunctor (BigAb B T)
  let t := (restrict B T).mapHomologicalComplex (.up ℤ)
  let s := (restrict B S).mapHomologicalComplex (.up ℤ)
  let b := (bigPush B T S f).mapHomologicalComplex (.up ℤ)
  let a := (smallPush B T S f).mapHomologicalComplex (.up ℤ)
  have ht (K : CochainComplex (BigAb B T) ℤ) : CochainComplex.IsKInjective (t.obj (I.obj K)) := by
    have := isKInjective_smallProetaleRestriction B T.obj T.property (I.obj K)
    exact CochainComplex.isKInjective_of_iso
      ((NatIso.mapHomologicalComplex (restrictDirectIso B T) (.up ℤ)).app (I.obj K)).symm
  have hb (K : CochainComplex (BigAb B T) ℤ) : IsIso (αbig.app (I.obj K)) :=
    unit_isIso (bigPush B T S f) Rbig αbig (I.obj K)
  have ha (K : CochainComplex (BigAb B T) ℤ) : IsIso (αsmall.app (t.obj (I.obj K))) := by
    have := ht K
    exact unit_isIso (smallPush B T S f) Rsmall αsmall (t.obj (I.obj K))
  have : ∀ K, IsIso ((Functor.whiskerLeft I αbig).app K) := hb
  have : ∀ K, IsIso ((Functor.whiskerLeft (I ⋙ t) αsmall).app K) := ha
  have : IsIso (Functor.whiskerLeft I αbig) := NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerLeft (I ⋙ t) αsmall) := NatIso.isIso_of_isIso_app _
  let eb : I ⋙ b ⋙ DerivedCategory.Q ≅ I ⋙ DerivedCategory.Q ⋙ Rbig :=
    asIso (Functor.whiskerLeft I αbig)
  let ea : I ⋙ t ⋙ a ⋙ DerivedCategory.Q ≅ I ⋙ t ⋙ DerivedCategory.Q ⋙ Rsmall :=
    asIso (Functor.whiskerLeft (I ⋙ t) αsmall)
  let ι := Functor.whiskerRight
    (Stacks.Injectives.kInjectiveResolutionInclusion (BigAb B T)) DerivedCategory.Q
  have (K : CochainComplex (BigAb B T) ℤ) : IsIso (ι.app K) := by
    dsimp [ι]
    infer_instance
  have : IsIso ι := NatIso.isIso_of_isIso_app _
  let eI : DerivedCategory.Q ≅ I ⋙ DerivedCategory.Q := asIso ι
  let eC : t ⋙ a ≅ b ⋙ s :=
    NatIso.mapHomologicalComplex (bigSmallPushIso B T S f) (.up ℤ)
  refine ⟨?_⟩
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (BigAb B T) (.up ℤ))
    (DerivedCategory (SmallAb B S))).preimageIso
  calc
    DerivedCategory.Q ⋙ Rbig ⋙ (restrict B S).mapDerivedCategory
        ≅ (I ⋙ DerivedCategory.Q ⋙ Rbig) ⋙ (restrict B S).mapDerivedCategory :=
      Functor.isoWhiskerRight (Functor.isoWhiskerRight eI Rbig) _
    _ ≅ (I ⋙ b ⋙ DerivedCategory.Q) ⋙ (restrict B S).mapDerivedCategory :=
      Functor.isoWhiskerRight eb.symm _
    _ ≅ I ⋙ b ⋙ s ⋙ DerivedCategory.Q :=
      Functor.isoWhiskerLeft (I ⋙ b) (restrict B S).mapDerivedCategoryFactors
    _ ≅ I ⋙ t ⋙ a ⋙ DerivedCategory.Q :=
      Functor.isoWhiskerLeft I (Functor.isoWhiskerRight eC.symm DerivedCategory.Q)
    _ ≅ I ⋙ t ⋙ DerivedCategory.Q ⋙ Rsmall := ea
    _ ≅ (I ⋙ DerivedCategory.Q) ⋙ (restrict B T).mapDerivedCategory ⋙ Rsmall :=
      Functor.isoWhiskerLeft I
        (Functor.isoWhiskerRight (restrict B T).mapDerivedCategoryFactors.symm Rsmall)
    _ ≅ DerivedCategory.Q ⋙ (restrict B T).mapDerivedCategory ⋙ Rsmall :=
      Functor.isoWhiskerRight eI.symm ((restrict B T).mapDerivedCategory ⋙ Rsmall)

/-- Restricting the derived direct image along `f` on the big pro-étale sites to the small
pro-étale site of `S` is naturally isomorphic to taking the derived direct image along `f` on the
small pro-étale sites of the restriction to the small pro-étale site of `T`. -/
@[stacks 0F68 "big_small_direct_image"]
public noncomputable def bigSmallDerivedPushforwardIso
    [HasDerivedCategory (BigAb B T)] [HasDerivedCategory (BigAb B S)]
    [HasDerivedCategory (SmallAb B T)] [HasDerivedCategory (SmallAb B S)]
    (Rbig : DerivedCategory (BigAb B T) ⥤ DerivedCategory (BigAb B S))
    (Rsmall : DerivedCategory (SmallAb B T) ⥤ DerivedCategory (SmallAb B S))
    (αbig : (bigPush B T S f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rbig)
    (αsmall : (smallPush B T S f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rsmall)
    [Rbig.IsRightDerivedFunctor αbig
      (HomologicalComplex.quasiIso (BigAb B T) (ComplexShape.up ℤ))]
    [Rsmall.IsRightDerivedFunctor αsmall
      (HomologicalComplex.quasiIso (SmallAb B T) (ComplexShape.up ℤ))] :
    Rbig ⋙ (restrict B S).mapDerivedCategory ≅
      (restrict B T).mapDerivedCategory ⋙ Rsmall :=
  Classical.choice (by exact bigSmallDerivedPushforward_nonempty B T S f Rbig Rsmall αbig αsmall)

end AlgebraicGeometry.ProEtale

end
