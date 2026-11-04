module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.AbelianSheaves
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.Cohomology
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.Injectives
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.BigProetaleMorphism
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Base change of a big pro-étale derived direct image

For a cartesian square of schemes, the unbounded derived direct image on the big pro-étale site
commutes with inverse image along the horizontal arrows: restricting it to the small site of the
base change gives the small-site derived direct image of the restriction, and pulling it back to
the big site of the base change gives the big-site derived direct image of the pullback.

## Main results

* `derivedBigPushforwardSmallBaseChangeIso` is the natural base-change isomorphism towards the
  small site of the base change.
* `derivedBigPushforwardBigBaseChangeIso` is the natural base-change isomorphism entirely on
  big sites.
* `nonempty_derivedPushforward_bigSmall_baseChange_iso`: the three equalities together.

## Implementation notes

The equalities in the source are expressed as natural isomorphisms. The right derived functors
are supplied with their defining comparison maps, so the assertions do not depend on a
particular choice of resolutions. Inverse image on abelian sheaves is the exact inverse image of
Tag 04JC, and the comparison of the two composites is obtained from functorial K-injective
resolutions.

K-injectivity is preserved by both inverse images because each has an exact left adjoint: for
the small site this is `isKInjective_smallProetaleInverseImage`, and for the big site the lower
shriek along the composition functor of sites, whose exactness is Tag 04BH.

## References

* [Stacks Project, Tag 0F68](https://stacks.math.columbia.edu/tag/0F68)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Sites

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u})
variable {T' T S' S : B.Scheme}
variable (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)

/-- Direct image of abelian sheaves along the cocontinuous `Over.map` of big pro-étale sites. -/
public noncomputable abbrev bigCocontPush {X Y : B.Scheme} (a : X ⟶ Y) :=
  (Over.map a).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (BigProetaleOver.topology B X.obj X.property)
    (BigProetaleOver.topology B Y.obj Y.property)

/-- Direct image of abelian sheaves along a base-changed morphism of small pro-étale sites. -/
public noncomputable abbrev smallBaseChangePush {X Y : B.Scheme} (a : X ⟶ Y) :=
  (smallProetaleBaseChange B X Y a).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (SmallProetale.topology B Y.obj Y.property)
    (SmallProetale.topology B X.obj X.property)

section Additivity

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

public noncomputable instance bigCocontPush_additive {X Y : B.Scheme} (a : X ⟶ Y) :
    (bigCocontPush B a).Additive := by
  let := ((Over.map a).sheafAdjunctionPullbackCocontinuous AddCommGrpCat.{u + 1}
    (BigProetaleOver.topology B X.obj X.property)
    (BigProetaleOver.topology B Y.obj Y.property)).isRightAdjoint
  exact Functor.additive_of_preservesBinaryBiproducts _

public noncomputable instance smallBaseChangePush_additive {X Y : B.Scheme} (a : X ⟶ Y) :
    (smallBaseChangePush B a).Additive := by
  let := ((smallProetaleBaseChange B X Y a).sheafAdjunctionContinuous
    AddCommGrpCat.{u + 1}
    (SmallProetale.topology B Y.obj Y.property)
    (SmallProetale.topology B X.obj X.property)).isRightAdjoint
  exact Functor.additive_of_preservesBinaryBiproducts _

end Additivity

/-- Comparison of the cocontinuous direct image of big sites with the pushforward of the
underlying presheaves of types. -/
private noncomputable def bigCocontPushForgetIso {X Y : B.Scheme} (a : X ⟶ Y) :
    bigCocontPush B a ⋙
        sheafCompose (BigProetaleOver.topology B Y.obj Y.property)
          (forget AddCommGrpCat.{u + 1}) ≅
      sheafCompose (BigProetaleOver.topology B X.obj X.property)
          (forget AddCommGrpCat.{u + 1}) ⋙
        (bigProetaleMorphism B X Y a).pushforward :=
  isoWhiskerRight ((Over.mapPullbackAdj a).sheafPushforwardCocontinuousIso
      AddCommGrpCat.{u + 1})
      (sheafCompose (BigProetaleOver.topology B Y.obj Y.property)
        (forget AddCommGrpCat.{u + 1})) ≪≫
    isoWhiskerLeft
      (sheafCompose (BigProetaleOver.topology B X.obj X.property)
        (forget AddCommGrpCat.{u + 1}))
      ((Over.mapPullbackAdj a).sheafPushforwardCocontinuousIso (Type (u + 1))).symm

private noncomputable def abelianBaseChangeIso (h : IsPullback g' f' f g) :
    bigCocontPush B f ⋙ restriction g ≅ restriction g' ⋙ smallBaseChangePush B f' := by
  have : (bigCocontPush B f).Additive := bigCocontPush_additive B f
  have : (restriction g).Additive := restriction_additive g
  have : (restriction g').Additive := restriction_additive g'
  have : (smallBaseChangePush B f').Additive := smallBaseChangePush_additive B f'
  exact liftSheafNatIso (SmallProetale.topology B S'.obj S'.property)
    (bigCocontPush B f ⋙ restriction g) (restriction g' ⋙ smallBaseChangePush B f')
    (isoWhiskerRight (bigCocontPushForgetIso B f)
        (smallProetaleToBigProetaleMorphism B S' S g).inverseImage ≪≫
      isoWhiskerLeft
        (sheafCompose (BigProetaleOver.topology B T.obj T.property)
          (forget AddCommGrpCat.{u + 1}))
        (smallProetaleBaseChangePushforwardIso B g' f' f g h))

private lemma restriction_isKInjective {X Y : B.Scheme} (a : X ⟶ Y)
    (I : CochainComplex (BigAb B Y) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (((restriction a).mapHomologicalComplex (.up ℤ)).obj I) := by
  have := isKInjective_smallProetaleInverseImage B X Y a I
  exact CochainComplex.isKInjective_of_iso
    ((NatIso.mapHomologicalComplex (restrictionIso a) (.up ℤ)).app I).symm

private lemma sheaf_isGrothendieckAbelian
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    IsGrothendieckAbelian.{u + 1} (Sheaf J AddCommGrpCat.{u + 1}) := by
  have : HasSheafify ((equivSmallModel.{u + 1} C).inverse.inducedTopology J)
      AddCommGrpCat.{u + 1} := by
    have smallSheafify {E : Type (u + 1)} [SmallCategory E] (K : GrothendieckTopology E) :
        HasSheafify K AddCommGrpCat.{u + 1} := inferInstance
    exact @smallSheafify (SmallModel.{u + 1} C)
      (smallCategorySmallModel.{u + 1, u, u + 1} C) _
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1}
    J AddCommGrpCat.{u + 1}

section DerivedComparison

universe w w'

variable {A D A' D' : Type*}
  [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* D] [Abelian D] [HasDerivedCategory D]
  [Category* A'] [Abelian A'] [HasDerivedCategory A']
  [Category* D'] [Abelian D'] [HasDerivedCategory D']

omit [HasDerivedCategory A] in
private lemma exists_kInjectiveResolution [IsGrothendieckAbelian.{w} A]
    (K : CochainComplex A ℤ) :
    ∃ (I : CochainComplex A ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a :=
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor A).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion A).app K, inferInstance, inferInstance⟩

private noncomputable def complexDerivedUnit
    (F : A ⥤ D) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF) :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF :=
  (isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D).symm).hom ≫
    (isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).symm _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) α ≫
    (isoWhiskerRight (DerivedCategory.quotientCompQhIso A) RF).hom

private lemma complexDerivedUnit_isIso [IsGrothendieckAbelian.{w} A]
    (F : A ⥤ D) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ))]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso ((complexDerivedUnit F RF α).app I) := by
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) exists_kInjectiveResolution).2
      DerivedCategory.Qh RF α I inferInstance
  dsimp [complexDerivedUnit]
  infer_instance

/-- Compute both composites on functorial K-injective resolutions and descend through `Q`. -/
private noncomputable def derivedComparisonIso
    [IsGrothendieckAbelian.{w} A] [IsGrothendieckAbelian.{w'} A']
    (F : A ⥤ D) (G : A' ⥤ D') (U : A ⥤ A') (V : D ⥤ D')
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e : F ⋙ V ≅ U ⋙ G)
    (hU : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      CochainComplex.IsKInjective ((U.mapHomologicalComplex (.up ℤ)).obj I))
    (RF : DerivedCategory A ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ))]
    (RG : DerivedCategory A' ⥤ DerivedCategory D')
    (β : G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG)
    [RG.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A' (.up ℤ))] :
    RF ⋙ V.mapDerivedCategory ≅ U.mapDerivedCategory ⋙ RG := by
  let R := Stacks.Injectives.kInjectiveResolutionFunctor A
  let η := Stacks.Injectives.kInjectiveResolutionInclusion A
  have : ∀ K, IsIso ((Functor.whiskerRight η DerivedCategory.Q).app K) := by
    intro K
    change IsIso (DerivedCategory.Q.map (η.app K))
    infer_instance
  have := NatIso.isIso_of_isIso_app (Functor.whiskerRight η DerivedCategory.Q)
  let eQ : DerivedCategory.Q ≅ R ⋙ DerivedCategory.Q :=
    asIso (Functor.whiskerRight η DerivedCategory.Q)
  have : ∀ K, IsIso ((Functor.whiskerLeft R (complexDerivedUnit F RF α)).app K) :=
    fun K => complexDerivedUnit_isIso F RF α (R.obj K)
  have := NatIso.isIso_of_isIso_app (Functor.whiskerLeft R (complexDerivedUnit F RF α))
  let eF := asIso (Functor.whiskerLeft R (complexDerivedUnit F RF α))
  have : ∀ K, IsIso ((Functor.whiskerLeft (R ⋙ U.mapHomologicalComplex (.up ℤ))
      (complexDerivedUnit G RG β)).app K) := by
    intro K
    have : CochainComplex.IsKInjective ((U.mapHomologicalComplex (.up ℤ)).obj (R.obj K)) :=
      hU (R.obj K) inferInstance
    exact complexDerivedUnit_isIso G RG β ((U.mapHomologicalComplex (.up ℤ)).obj (R.obj K))
  have := NatIso.isIso_of_isIso_app
    (Functor.whiskerLeft (R ⋙ U.mapHomologicalComplex (.up ℤ)) (complexDerivedUnit G RG β))
  let eG := asIso (Functor.whiskerLeft (R ⋙ U.mapHomologicalComplex (.up ℤ))
    (complexDerivedUnit G RG β))
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory D')).preimageIso
  exact isoWhiskerRight eQ (RF ⋙ V.mapDerivedCategory) ≪≫
    isoWhiskerRight eF.symm V.mapDerivedCategory ≪≫
    isoWhiskerLeft (R ⋙ F.mapHomologicalComplex (.up ℤ)) V.mapDerivedCategoryFactors ≪≫
    isoWhiskerLeft R
      (isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q) ≪≫
    eG ≪≫
    isoWhiskerLeft R (isoWhiskerRight U.mapDerivedCategoryFactors.symm RG) ≪≫
    (isoWhiskerRight eQ (U.mapDerivedCategory ⋙ RG)).symm

end DerivedComparison

/-- The derived big direct image restricted to the small site of `S'` agrees
naturally with small direct image after restriction to `T'`. -/
@[stacks 0F68 "base_changed_small_direct_image"]
public noncomputable def derivedBigPushforwardSmallBaseChangeIso
    (h : IsPullback g' f' f g)
    (RFbig : DerivedCategory (BigAb B T) ⥤ DerivedCategory (BigAb B S))
    (αbig : (bigCocontPush B f).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RFbig)
    [RFbig.IsRightDerivedFunctor αbig
      (HomotopyCategory.quasiIso (BigAb B T) (ComplexShape.up ℤ))]
    (RFsmall : DerivedCategory (SmallAb B T') ⥤ DerivedCategory (SmallAb B S'))
    (αsmall : (smallBaseChangePush B f').mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RFsmall)
    [RFsmall.IsRightDerivedFunctor αsmall
      (HomotopyCategory.quasiIso (SmallAb B T') (ComplexShape.up ℤ))] :
    RFbig ⋙ (restriction g).mapDerivedCategory ≅
      (restriction g').mapDerivedCategory ⋙ RFsmall := Classical.choice (by
  have := sheaf_isGrothendieckAbelian
    (BigProetaleOver.topology B T.obj T.property)
  have := sheaf_isGrothendieckAbelian
    (SmallProetale.topology B T'.obj T'.property)
  have : (bigCocontPush B f).Additive := bigCocontPush_additive B f
  have : (smallBaseChangePush B f').Additive := smallBaseChangePush_additive B f'
  have : (restriction g').Additive := restriction_additive g'
  have : (restriction g).Additive := restriction_additive g
  exact ⟨derivedComparisonIso (bigCocontPush B f) (smallBaseChangePush B f')
    (restriction g') (restriction g) (abelianBaseChangeIso B g' f' f g h)
    (fun I _ => restriction_isKInjective B g' I) RFbig αbig RFsmall αsmall⟩)

/-- The inverse image of abelian sheaves between two big pro-étale sites is restriction along
the composition functor of sites. -/
private noncomputable def bigInverseImageIso {X Y : B.Scheme} (q : X ⟶ Y) :
    bigInverseImage B X Y q ≅
      (Over.map (q : X ⟶ Y)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (BigProetaleOver.topology B X.obj X.property)
        (BigProetaleOver.topology B Y.obj Y.property) := by
  let F := Over.map (q : X ⟶ Y)
  let G := F.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (BigProetaleOver.topology B X.obj X.property)
    (BigProetaleOver.topology B Y.obj Y.property)
  have : G.Additive := ⟨by intros; rfl⟩
  have : (bigInverseImage B X Y q).Additive := bigInverseImage_additive B X Y q
  exact liftSheafNatIso (BigProetaleOver.topology B X.obj X.property)
    (bigInverseImage B X Y q) G
    (isoWhiskerLeft
      (sheafCompose (BigProetaleOver.topology B Y.obj Y.property)
        (forget AddCommGrpCat.{u + 1}))
      (F.sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type (u + 1))
        (BigProetaleOver.topology B X.obj X.property)
        (BigProetaleOver.topology B Y.obj Y.property)))

private lemma bigInverseImage_isKInjective {X Y : B.Scheme} (q : X ⟶ Y)
    (I : CochainComplex (BigAb B Y) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((bigInverseImage B X Y q).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  have hsite : CochainComplex.IsKInjective
      ((((Over.map (q : X ⟶ Y)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (BigProetaleOver.topology B X.obj X.property)
          (BigProetaleOver.topology B Y.obj Y.property)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
    let F := Over.map (q : X ⟶ Y)
    let JX := BigProetaleOver.topology B X.obj X.property
    let JY := BigProetaleOver.topology B Y.obj Y.property
    let push := F.sheafPushforwardContinuous AddCommGrpCat.{u + 1} JX JY
    let pull := Functor.sheafPullbackConstruction.sheafPullback F AddCommGrpCat.{u + 1} JX JY
    have : PreservesFiniteLimits pull := by
      apply Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits
    have : PreservesFiniteColimits pull :=
      Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits AddCommGrpCat.{u + 1} F JX JY
    let adj : pull ⊣ push :=
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F AddCommGrpCat.{u + 1} JX JY
    have : push.Additive := ⟨by intros; rfl⟩
    have : pull.Additive := adj.left_adjoint_additive
    exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact push pull adj I
  exact CochainComplex.isKInjective_of_iso
    ((NatIso.mapHomologicalComplex (bigInverseImageIso B q) (ComplexShape.up ℤ)).app I).symm

private noncomputable def abelianBigBaseChangeIso (h : IsPullback g' f' f g) :
    bigCocontPush B f ⋙ bigInverseImage B S' S g ≅
      bigInverseImage B T' T g' ⋙ bigCocontPush B f' := by
  have : (bigCocontPush B f).Additive := bigCocontPush_additive B f
  have : (bigCocontPush B f').Additive := bigCocontPush_additive B f'
  have : (bigInverseImage B S' S g).Additive := bigInverseImage_additive B S' S g
  have : (bigInverseImage B T' T g').Additive := bigInverseImage_additive B T' T g'
  exact liftSheafNatIso (BigProetaleOver.topology B S'.obj S'.property)
    (bigCocontPush B f ⋙ bigInverseImage B S' S g)
    (bigInverseImage B T' T g' ⋙ bigCocontPush B f')
    (isoWhiskerRight (bigCocontPushForgetIso B f) (bigProetaleMorphism B S' S g).inverseImage ≪≫
      isoWhiskerLeft
        (sheafCompose (BigProetaleOver.topology B T.obj T.property)
          (forget AddCommGrpCat.{u + 1}))
        (bigProetaleBaseChangePushforwardIso B g' f' f g h) ≪≫
      isoWhiskerLeft (bigInverseImage B T' T g') (bigCocontPushForgetIso B f').symm)

/-- The derived big direct image along `f`, pulled back to the big pro-étale site over `S'`,
agrees naturally with the derived big direct image along `f'` of the pullback to the big
pro-étale site over `T'`. -/
@[stacks 0F68 "base_changed_big_direct_image"]
public noncomputable def derivedBigPushforwardBigBaseChangeIso
    (h : IsPullback g' f' f g)
    (RFbig : DerivedCategory (BigAb B T) ⥤ DerivedCategory (BigAb B S))
    (αbig : (bigCocontPush B f).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RFbig)
    [RFbig.IsRightDerivedFunctor αbig
      (HomotopyCategory.quasiIso (BigAb B T) (ComplexShape.up ℤ))]
    (RFbig' : DerivedCategory (BigAb B T') ⥤ DerivedCategory (BigAb B S'))
    (αbig' : (bigCocontPush B f').mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RFbig')
    [RFbig'.IsRightDerivedFunctor αbig'
      (HomotopyCategory.quasiIso (BigAb B T') (ComplexShape.up ℤ))] :
    RFbig ⋙ (bigInverseImage B S' S g).mapDerivedCategory ≅
      (bigInverseImage B T' T g').mapDerivedCategory ⋙ RFbig' := Classical.choice (by
  have := sheaf_isGrothendieckAbelian
    (BigProetaleOver.topology B T.obj T.property)
  have := sheaf_isGrothendieckAbelian
    (BigProetaleOver.topology B T'.obj T'.property)
  have : (bigCocontPush B f).Additive := bigCocontPush_additive B f
  have : (bigCocontPush B f').Additive := bigCocontPush_additive B f'
  have : (bigInverseImage B S' S g).Additive := bigInverseImage_additive B S' S g
  have : (bigInverseImage B T' T g').Additive := bigInverseImage_additive B T' T g'
  exact ⟨derivedComparisonIso (bigCocontPush B f) (bigCocontPush B f')
    (bigInverseImage B T' T g') (bigInverseImage B S' S g)
    (abelianBigBaseChangeIso B g' f' f g h)
    (fun I _ => bigInverseImage_isKInjective B g' I) RFbig αbig RFbig' αbig'⟩)

/-- **Stacks 0F68.** Let `f : T ⟶ S` be a morphism of a big pro-étale site, `g : S' ⟶ S` an
object of the big pro-étale site of `S`, and `T'` the fibre product, with projections
`g' : T' ⟶ T` and `f' : T' ⟶ S'`. Then, naturally in `K` in `D((Sch/T)_proet)`,
* `(Rf_big,* K)|_{S_proet} ≅ Rf_small,* (K|_{T_proet})` in `D(S_proet)`,
* `i_g⁻¹ (Rf_big,* K) ≅ Rf'_small,* (i_g'⁻¹ K)` in `D(S'_proet)`, and
* `g_big⁻¹ (Rf_big,* K) ≅ Rf'_big,* (g'_big⁻¹ K)` in `D((Sch/S')_proet)`.

Each derived direct image is any right derived functor of the corresponding direct image of
abelian sheaves, given with its comparison transformation. The first equality is the second one
for the identity of `S`. -/
@[stacks 0F68]
public theorem nonempty_derivedPushforward_bigSmall_baseChange_iso
    (h : IsPullback g' f' f g)
    (RFbig : DerivedCategory (BigAb B T) ⥤ DerivedCategory (BigAb B S))
    (αbig : (bigCocontPush B f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RFbig)
    [RFbig.IsRightDerivedFunctor αbig
      (HomotopyCategory.quasiIso (BigAb B T) (ComplexShape.up ℤ))]
    (RFsmall : DerivedCategory (SmallAb B T) ⥤ DerivedCategory (SmallAb B S))
    (αsmall : (smallBaseChangePush B f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RFsmall)
    [RFsmall.IsRightDerivedFunctor αsmall
      (HomotopyCategory.quasiIso (SmallAb B T) (ComplexShape.up ℤ))]
    (RF'small : DerivedCategory (SmallAb B T') ⥤ DerivedCategory (SmallAb B S'))
    (α'small : (smallBaseChangePush B f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF'small)
    [RF'small.IsRightDerivedFunctor α'small
      (HomotopyCategory.quasiIso (SmallAb B T') (ComplexShape.up ℤ))]
    (RF'big : DerivedCategory (BigAb B T') ⥤ DerivedCategory (BigAb B S'))
    (α'big : (bigCocontPush B f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF'big)
    [RF'big.IsRightDerivedFunctor α'big
      (HomotopyCategory.quasiIso (BigAb B T') (ComplexShape.up ℤ))] :
    Nonempty (RFbig ⋙ (restriction (𝟙 S)).mapDerivedCategory ≅
      (restriction (𝟙 T)).mapDerivedCategory ⋙ RFsmall) ∧
    Nonempty (RFbig ⋙ (restriction g).mapDerivedCategory ≅
      (restriction g').mapDerivedCategory ⋙ RF'small) ∧
    Nonempty (RFbig ⋙ (bigInverseImage B S' S g).mapDerivedCategory ≅
      (bigInverseImage B T' T g').mapDerivedCategory ⋙ RF'big) :=
  ⟨⟨derivedBigPushforwardSmallBaseChangeIso B (𝟙 T) f f (𝟙 S) IsPullback.of_id_fst
      RFbig αbig RFsmall αsmall⟩,
    ⟨derivedBigPushforwardSmallBaseChangeIso B g' f' f g h RFbig αbig RF'small α'small⟩,
    ⟨derivedBigPushforwardBigBaseChangeIso B g' f' f g h RFbig αbig RF'big α'big⟩⟩

end AlgebraicGeometry.ProEtale

end
