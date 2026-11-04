module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.AbelianSheaves
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Limits
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.BigProetaleMorphism
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallProjection
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# Comparison of big and small pro-étale cohomology

For a morphism of schemes, pro-étale hypercohomology on the big site agrees with hypercohomology
on the small site after restriction. The comparison also applies to complexes pulled back from
the small site. The inverse images are the abelian inverse images of the corresponding morphisms
of topoi.

## Main definitions

* `mapAbelianSheaf` transports a left-exact functor between categories of sheaves of types to
  one between the corresponding categories of abelian sheaves.
* `cohomology` is hypercohomology, represented by derived maps from the constant integer sheaf.

## Main results

* `bigProetaleCohomology_inclusionInverseImage` compares a complex on the big site with its
  restriction to the small pro-étale site of an object.
* `bigProetaleCohomology_projectionInverseImage` gives the comparison for a complex pulled back
  from the small pro-étale site of the base.
* `bigProetaleCohomology_projectionInverseImage_self` gives the comparison over the base itself.

## References

* [Stacks Project, Tag 0F69](https://stacks.math.columbia.edu/tag/0F69)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sites CategoryTheory.Sites.AbelianSheaf

universe u v w

namespace AlgebraicGeometry.ProEtale

section AbelianSheafComparison

open CategoryTheory.MonoidalCategory CategoryTheory.Functor

universe u' v' w' u'' v'' w''

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The cartesian monoidal structure on sheaves of types given by finite products. -/
noncomputable local instance : CartesianMonoidalCategory (Sheaf J (Type w)) :=
  .ofHasFiniteProducts
/-- The symmetric braiding of the cartesian monoidal structure on sheaves of types. -/
noncomputable local instance : BraidedCategory (Sheaf J (Type w)) :=
  .ofCartesianMonoidalCategory
/-- The forgetful functor from sheaves of types to presheaves is braided. -/
noncomputable local instance : (sheafToPresheaf J (Type w)).Braided :=
  .ofChosenFiniteProducts _

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
variable {E : Type u''} [Category.{v''} E] {L : GrothendieckTopology E}
variable {J}

/-- Transport a left-exact functor between categories of sheaves of types to the corresponding
categories of abelian sheaves, by applying it to the group operations. -/
public noncomputable abbrev mapAbelianSheaf (F : Sheaf J (Type w) ⥤ Sheaf K (Type w'))
    [PreservesFiniteLimits F] : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w'} :=
  letI : F.Braided := .ofChosenFiniteProducts _
  internalSheaf J ⋙ F.mapCommGrp ⋙ externalSheaf K

/-- Isomorphic left-exact functors of sheaves of types induce isomorphic functors of abelian
sheaves. -/
public noncomputable def mapAbelianSheafIso
    {F G : Sheaf J (Type w) ⥤ Sheaf K (Type w')}
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] (e : F ≅ G) :
    mapAbelianSheaf F ≅ mapAbelianSheaf G := by
  letI : F.Braided := .ofChosenFiniteProducts _
  letI : G.Braided := .ofChosenFiniteProducts _
  exact isoWhiskerLeft _ (isoWhiskerRight (Functor.mapCommGrpNatIso e) _)

/-- An adjunction between left-exact functors of sheaves of types induces one between the
corresponding functors of abelian sheaves. -/
public noncomputable def mapAbelianSheafAdjunction
    {F : Sheaf J (Type w) ⥤ Sheaf K (Type w')}
    {G : Sheaf K (Type w') ⥤ Sheaf J (Type w)}
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] (adj : F ⊣ G) :
    mapAbelianSheaf F ⊣ mapAbelianSheaf G := by
  letI : F.Braided := .ofChosenFiniteProducts _
  letI : G.Braided := .ofChosenFiniteProducts _
  exact (AbelianSheaf.equivalence J).toAdjunction.comp
    (adj.mapCommGrp.comp (AbelianSheaf.equivalence K).symm.toAdjunction)

/-- The induced functor on commutative group objects does not depend on the chosen braiding. -/
public noncomputable def mapCommGrpChange
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w')) (b₁ b₂ : F.Braided) :
    (letI := b₁; F.mapCommGrp) ≅ (letI := b₂; F.mapCommGrp) :=
  @Functor.mapCommGrpNatIso _ _ _ _ _ _ _ _ F F b₁ b₂ (Iso.refl _)

/-- The transport of `mapAbelianSheaf` is compatible with composition. -/
public noncomputable def mapAbelianSheafCompIso
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w'))
    (G : Sheaf K (Type w') ⥤ Sheaf L (Type w''))
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    mapAbelianSheaf F ⋙ mapAbelianSheaf G ≅ mapAbelianSheaf (F ⋙ G) := by
  letI : F.Braided := .ofChosenFiniteProducts _
  letI : G.Braided := .ofChosenFiniteProducts _
  let e := (Functor.mapCommGrpCompIso (F := F) (G := G)).symm ≪≫
    mapCommGrpChange (F ⋙ G) inferInstance (.ofChosenFiniteProducts _)
  exact isoWhiskerLeft (internalSheaf J ⋙ F.mapCommGrp)
      (isoWhiskerRight (AbelianSheaf.externalInternalIso K)
        (G.mapCommGrp ⋙ externalSheaf L)) ≪≫
    isoWhiskerLeft (internalSheaf J)
      (isoWhiskerRight e (externalSheaf L))

/-- The transport of `mapAbelianSheaf` takes the identity to the identity. -/
public noncomputable def mapAbelianSheafIdIso :
    mapAbelianSheaf (𝟭 (Sheaf J (Type w))) ≅ 𝟭 _ :=
  isoWhiskerLeft _ (isoWhiskerRight
    (mapCommGrpChange (𝟭 (Sheaf J (Type w))) (.ofChosenFiniteProducts _) inferInstance ≪≫
      Functor.mapCommGrpIdIso) _) ≪≫ AbelianSheaf.internalExternalIso J

/-- On direct images along a continuous functor of sites, the transport of `mapAbelianSheaf` is
the direct image of abelian sheaves. -/
public noncomputable def mapAbelianSheafRestrictionIso (U : C ⥤ D) [U.IsContinuous J K]
    [PreservesFiniteLimits (U.sheafPushforwardContinuous (Type w) J K)] :
    mapAbelianSheaf (U.sheafPushforwardContinuous (Type w) J K) ≅
      U.sheafPushforwardContinuous AddCommGrpCat.{w} J K := by
  let H := U.sheafPushforwardContinuous (Type w) J K
  let P := sheafToPresheaf J (Type w)
  let Q := sheafToPresheaf K (Type w)
  let W := (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj U.op
  letI : H.Braided := .ofChosenFiniteProducts _
  letI : W.Braided := { braided X Y := by ext Z x; rfl }
  let e : H ⋙ P ≅ Q ⋙ W := Iso.refl _
  let ei : H.mapCommGrp ⋙ P.mapCommGrp ≅ Q.mapCommGrp ⋙ W.mapCommGrp :=
    Functor.mapCommGrpCompIso.symm ≪≫ Functor.mapCommGrpNatIso e ≪≫
      Functor.mapCommGrpCompIso
  refine NatIso.ofComponents (fun R => ?_) ?_
  · refine (fullyFaithfulSheafToPresheaf J AddCommGrpCat).preimageIso
      ((abelianPresheaves).mapIso (ei.app ((internalSheaf K).obj R)) ≪≫ ?_)
    exact (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat).obj U.op |>.mapIso
      ((sheafToPresheaf K AddCommGrpCat).mapIso
        ((AbelianSheaf.internalExternalIso K).app R))
  · intro R S f
    ext X x
    rfl

end AbelianSheafComparison

attribute [local instance] HasDerivedCategory.standard

/-- Transporting a group of morphisms in a preadditive category along isomorphisms of its
source and target is additive. -/
public def homAddEquivOfIso {A : Type*} [Category A] [Preadditive A]
    {X Y X' Y' : A} (eX : X ≅ X') (eY : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toEquiv := eX.homCongr eY
  map_add' f g := by
    simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- An isomorphism of a composite of exact functors with a third one descends to the unbounded
derived categories. -/
public noncomputable def derivedCompIso
    {A : Type*} [Category A] [Abelian A] {D : Type*} [Category D] [Abelian D]
    {E : Type*} [Category E] [Abelian E]
    {F : A ⥤ D} {G : D ⥤ E} {H : A ⥤ E}
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory := by
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        G.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
    ⟨Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactors⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _ _ _ _
    (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- The identity functor's action on the unbounded derived category is the identity. -/
public noncomputable def derivedIdIso {A : Type*} [Category A] [Abelian A] :
    (𝟭 A).mapDerivedCategory ≅ 𝟭 (DerivedCategory A) := by
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (𝟭 (CochainComplex A ℤ) ⋙ DerivedCategory.Q) (𝟭 (DerivedCategory A)) :=
    ⟨Iso.refl _⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _ _ _ _
    (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)) DerivedCategory.Q)

section AbelianInverseComposite

universe u' v' w' u'' v'' w''

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
variable {E : Type u''} [Category.{v''} E] {L : GrothendieckTopology E}

/-- Abelian inverse image turns a factorisation of direct images into one of inverse images. -/
public noncomputable def abelianInverseCompOfPushforwardIso
    (f : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf J (Type w)))
    (g : MorphismOfTopoi (Sheaf L (Type w'')) (Sheaf K (Type w')))
    (h : MorphismOfTopoi (Sheaf L (Type w'')) (Sheaf J (Type w)))
    (e : h.pushforward ≅ g.pushforward ⋙ f.pushforward) :
    abelianInverseImage f ⋙ abelianInverseImage g ≅ abelianInverseImage h := by
  letI := f.preservesFiniteLimits
  letI := g.preservesFiniteLimits
  letI := h.preservesFiniteLimits
  exact mapAbelianSheafCompIso _ _ ≪≫
    mapAbelianSheafIso ((f.adj.comp g.adj).leftAdjointUniq (h.adj.ofNatIsoRight e))

/-- Abelian inverse image along two morphisms of topoi whose direct images compose to the
identity composes to the identity. -/
public noncomputable def abelianInverseCompIdIso
    (f : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf J (Type w)))
    (g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (e : g.pushforward ⋙ f.pushforward ≅ 𝟭 _) :
    abelianInverseImage f ⋙ abelianInverseImage g ≅ 𝟭 _ := by
  letI := f.preservesFiniteLimits
  letI := g.preservesFiniteLimits
  exact mapAbelianSheafCompIso _ _ ≪≫
    mapAbelianSheafIso (((f.adj.comp g.adj).ofNatIsoRight e).leftAdjointUniq
      Adjunction.id) ≪≫ mapAbelianSheafIdIso

end AbelianInverseComposite

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-- Hypercohomology of an unbounded complex of abelian sheaves, represented
by maps from the constant integer sheaf in the derived category. -/
public abbrev cohomology {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    (K : DerivedCategory (Sheaf J AddCommGrpCat.{u + 1})) (n : ℤ) : Type _ :=
  let Z := (constantSheaf J AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift ℤ))
  (DerivedCategory.singleFunctor (Sheaf J AddCommGrpCat.{u + 1}) n).obj Z ⟶ K

/-- Inverse image of abelian sheaves from the big pro-étale site over `S` to the small
pro-étale site of `T`. -/
public abbrev inclusionInverseImage : BigAb B S ⥤ SmallAb B T :=
  abelianInverseImage (smallProetaleToBigProetaleMorphism B T S f)

/-- Inverse image of abelian sheaves along the projection from the big pro-étale topos over `S`
to the small pro-étale topos of `S`. -/
public abbrev projectionInverseImage : SmallAb B S ⥤ BigAb B S :=
  abelianInverseImage (bigProetaleToSmallProetaleMorphism B S.obj S.property)

/-- Inverse image of abelian sheaves along the morphism of small pro-étale topoi induced
by `f`. -/
public abbrev smallInverseImage : SmallAb B S ⥤ SmallAb B T :=
  abelianInverseImage (smallProetaleMorphism B T S f)

/-- Inverse image of abelian sheaves along the morphism of big pro-étale topoi induced
by `f`. -/
public abbrev bigInverseImage : BigAb B S ⥤ BigAb B T :=
  abelianInverseImage (bigProetaleMorphism B T S f)

/-- The inverse image `inclusionInverseImage B T S f` is additive. -/
public noncomputable instance inclusionInverseImage_additive :
    (inclusionInverseImage B T S f).Additive :=
  exactFunctor_le_additiveFunctor _ _ _
    (abelianInverseImage_exact _)

/-- The inverse image `projectionInverseImage B S` is additive. -/
public noncomputable instance projectionInverseImage_additive :
    (projectionInverseImage B S).Additive :=
  exactFunctor_le_additiveFunctor _ _ _
    (abelianInverseImage_exact _)

/-- The inverse image `smallInverseImage B T S f` is additive. -/
public noncomputable instance smallInverseImage_additive :
    (smallInverseImage B T S f).Additive :=
  exactFunctor_le_additiveFunctor _ _ _
    (abelianInverseImage_exact _)

/-- The inverse image `bigInverseImage B T S f` is additive. -/
public noncomputable instance bigInverseImage_additive :
    (bigInverseImage B T S f).Additive :=
  exactFunctor_le_additiveFunctor _ _ _
    (abelianInverseImage_exact _)

section Comparison

/-- The projection from the big pro-étale topos over `S` to the small pro-étale topos of `S`
has inverse image left adjoint to restriction along the inclusion of sites. -/
public noncomputable def projectionRestrictionAdjunction :
    projectionInverseImage B S ⊣
      (SmallProetale.inclusion B S.obj S.property).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (SmallProetale.topology B S.obj S.property)
        (BigProetaleOver.topology B S.obj S.property) := by
  let π := bigProetaleToSmallProetaleMorphism B S.obj S.property
  letI := π.preservesFiniteLimits
  letI : PreservesLimitsOfSize.{0, 0} π.pushforward := π.adj.rightAdjoint_preservesLimits
  letI := (smallProetaleInclusion_isMorphismOfSites B S.obj S.property).toIsContinuous
  letI : PreservesFiniteLimits
      ((SmallProetale.inclusion B S.obj S.property).sheafPushforwardContinuous
        (Type (u + 1)) (SmallProetale.topology B S.obj S.property)
        (BigProetaleOver.topology B S.obj S.property)) :=
    (inferInstance : PreservesFiniteLimits π.pushforward)
  exact (mapAbelianSheafAdjunction π.adj).ofNatIsoRight
    (mapAbelianSheafRestrictionIso (SmallProetale.inclusion B S.obj S.property))

/-- The projection's inverse image is left adjoint to the inverse image of the inclusion of the
small pro-étale topos of `S` at the identity of `S`. -/
public noncomputable def projectionInclusionAdjunction :
    projectionInverseImage B S ⊣ inclusionInverseImage B S S (𝟙 S) := by
  let π := bigProetaleToSmallProetaleMorphism B S.obj S.property
  let i := smallProetaleToBigProetaleMorphism B S S (𝟙 S)
  letI := π.preservesFiniteLimits
  letI := i.preservesFiniteLimits
  letI : PreservesLimitsOfSize.{0, 0} π.pushforward := π.adj.rightAdjoint_preservesLimits
  exact (mapAbelianSheafAdjunction π.adj).ofNatIsoRight
    (mapAbelianSheafIso
      (inclusionInverseImageIsoProjectionPushforward B S.obj S.property).symm)

/-- The projection's inverse image takes the constant sheaf on the small pro-étale site of `S`
to the constant sheaf on the big pro-étale site over `S`. -/
public noncomputable def projectionConstantIso :
    constantSheaf (SmallProetale.topology B S.obj S.property) AddCommGrpCat.{u + 1} ⋙
      projectionInverseImage B S ≅
      constantSheaf (BigProetaleOver.topology B S.obj S.property) AddCommGrpCat.{u + 1} :=
  ((constantSheafAdj (SmallProetale.topology B S.obj S.property) AddCommGrpCat.{u + 1}
      (smallIdentity_isTerminal B S.obj S.property)).comp
    (projectionRestrictionAdjunction B S)).leftAdjointUniq
      (constantSheafAdj (BigProetaleOver.topology B S.obj S.property) AddCommGrpCat.{u + 1}
        Over.mkIdTerminal)

/-- Big pro-étale cohomology over `S` agrees with small pro-étale cohomology of the
restriction. -/
public noncomputable def bigSmallCohomologyEquiv
    (M : DerivedCategory (BigAb B S)) (n : ℤ) :
    cohomology (BigProetaleOver.topology B S.obj S.property) M n ≃+
      cohomology (SmallProetale.topology B S.obj S.property)
        ((inclusionInverseImage B S S (𝟙 S)).mapDerivedCategory.obj M) n := by
  let Z := (constantSheaf (SmallProetale.topology B S.obj S.property)
    AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))
  let e := ((projectionInverseImage B S).mapDerivedCategorySingleFunctor n).app Z ≪≫
    (DerivedCategory.singleFunctor (BigAb B S) n).mapIso
      ((projectionConstantIso B S).app (AddCommGrpCat.of (ULift ℤ)))
  exact (homAddEquivOfIso e.symm (Iso.refl M)).trans
    ((Adjunction.mapDerivedCategory (projectionInclusionAdjunction B S)).homAddEquiv _ M)

/-- Restricting a big pro-étale complex to `T` factors the big inverse image along `f` through
the restriction to the small pro-étale site of `T`. -/
public noncomputable def bigInclusionDerivedIso :
    (bigInverseImage B T S f).mapDerivedCategory ⋙
      (inclusionInverseImage B T T (𝟙 T)).mapDerivedCategory ≅
        (inclusionInverseImage B T S f).mapDerivedCategory :=
  derivedCompIso (abelianInverseCompOfPushforwardIso
    (bigProetaleMorphism B T S f)
    (smallProetaleToBigProetaleMorphism B T T (𝟙 T))
    (smallProetaleToBigProetaleMorphism B T S f)
    (inclusionBigBaseChangePushforwardIso B T S f))

/-- The projection followed by the restriction to the small pro-étale site of `T` is the small
pro-étale inverse image along `f`. -/
public noncomputable def projectionInclusionDerivedIso :
    (projectionInverseImage B S).mapDerivedCategory ⋙
      (inclusionInverseImage B T S f).mapDerivedCategory ≅
        (smallInverseImage B T S f).mapDerivedCategory :=
  derivedCompIso (abelianInverseCompOfPushforwardIso
    (bigProetaleToSmallProetaleMorphism B S.obj S.property)
    (smallProetaleToBigProetaleMorphism B T S f)
    (smallProetaleMorphism B T S f)
    (smallProetaleMorphismInclusionFactorizationIso B T S f))

/-- Pulling a small pro-étale complex back to the big site over `S` and restricting it again
recovers it. -/
public noncomputable def projectionInclusionSelfDerivedIso :
    (projectionInverseImage B S).mapDerivedCategory ⋙
      (inclusionInverseImage B S S (𝟙 S)).mapDerivedCategory ≅
        𝟭 (DerivedCategory (SmallAb B S)) :=
  derivedCompIso (abelianInverseCompIdIso
    (bigProetaleToSmallProetaleMorphism B S.obj S.property)
    (smallProetaleToBigProetaleMorphism B S S (𝟙 S))
    (projectionCompInclusionPushforwardIso B S.obj S.property)) ≪≫ derivedIdIso

end Comparison

/-- The big pro-étale cohomology over `T` of the inverse image of `M` along `f` agrees with the
small pro-étale cohomology of `T` with coefficients in the restriction of `M` along `f`. -/
@[stacks 0F69 "part (3)"]
public noncomputable def bigProetaleCohomology_inclusionInverseImage
    (M : DerivedCategory (BigAb B S)) (n : ℤ) :
    cohomology (BigProetaleOver.topology B T.obj T.property)
        ((bigInverseImage B T S f).mapDerivedCategory.obj M) n ≃+
      cohomology (SmallProetale.topology B T.obj T.property)
        ((inclusionInverseImage B T S f).mapDerivedCategory.obj M) n :=
  (bigSmallCohomologyEquiv B T ((bigInverseImage B T S f).mapDerivedCategory.obj M) n).trans
    (homAddEquivOfIso (Iso.refl _) ((bigInclusionDerivedIso B T S f).app M))

/-- Pulling a small-site complex back to the big site and then computing
cohomology over `T` agrees with its small-site pullback along `f`. -/
@[stacks 0F69 "part (2)"]
public noncomputable def bigProetaleCohomology_projectionInverseImage
    (K : DerivedCategory (SmallAb B S)) (n : ℤ) :
    cohomology (BigProetaleOver.topology B T.obj T.property)
        ((bigInverseImage B T S f).mapDerivedCategory.obj
          ((projectionInverseImage B S).mapDerivedCategory.obj K)) n ≃+
      cohomology (SmallProetale.topology B T.obj T.property)
        ((smallInverseImage B T S f).mapDerivedCategory.obj K) n :=
  (bigProetaleCohomology_inclusionInverseImage B T S f
      ((projectionInverseImage B S).mapDerivedCategory.obj K) n).trans
    (homAddEquivOfIso (Iso.refl _) ((projectionInclusionDerivedIso B T S f).app K))

/-- The big pro-étale cohomology over `S` of the inverse image of a small pro-étale complex `K`
along the projection agrees with the small pro-étale cohomology of `K`. -/
@[stacks 0F69 "part (1)"]
public noncomputable def bigProetaleCohomology_projectionInverseImage_self
    (K : DerivedCategory (SmallAb B S)) (n : ℤ) :
    cohomology (BigProetaleOver.topology B S.obj S.property)
        ((projectionInverseImage B S).mapDerivedCategory.obj K) n ≃+
      cohomology (SmallProetale.topology B S.obj S.property) K n :=
  (bigSmallCohomologyEquiv B S
      ((projectionInverseImage B S).mapDerivedCategory.obj K) n).trans
    (homAddEquivOfIso (Iso.refl _) ((projectionInclusionSelfDerivedIso B S).app K))

end AlgebraicGeometry.ProEtale

end
