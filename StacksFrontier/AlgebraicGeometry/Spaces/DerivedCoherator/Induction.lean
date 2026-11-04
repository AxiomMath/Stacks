module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedCoherator.EtalePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Coreflective objects in the derived category of an algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space. The coherator
`DQ_X : D(𝒪_X) ⥤ D_QCoh(𝒪_X)`, the right adjoint of the inclusion, exists as soon as every object
of `D(𝒪_X)` is *coreflective*, i.e. sits in a distinguished triangle `E ⟶ K ⟶ Q ⟶ E[1]` with `E`
in `D_QCoh(𝒪_X)` and `Q` right orthogonal to `D_QCoh(𝒪_X)` ([Stacks, Tag 0CQS]). This module
proves, for the algebraic spaces `j : W ⟶ X` étale over `X`, the property

  `P(W, j)`: for every K-injective complex `I` of `𝒪_W`-modules, `Rj_*I = j_*I` is coreflective
  in `D(𝒪_X)`,

across elementary distinguished squares and on affine charts, and deduces that every object of
`D(𝒪_X)` is coreflective, granted the affine case.

## Main definitions

* `AlgebraicGeometry.Space.complexPushforward f`: the degreewise direct image of complexes.
* `AlgebraicGeometry.Space.CoreflectivePushforward X Y j`: the property `P(Y, j)` above.

## Main results

* `AlgebraicGeometry.Space.coreflectivePushforward_of_isElementaryDistinguishedSquare`: the
  property `P` across an elementary distinguished square.
* `AlgebraicGeometry.Space.spaceCoreflective_of_affineCase`: every object of `D(𝒪_X)` is
  coreflective, granted the affine case.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.PushforwardMayerVietoris

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] isGrothendieckAbelian_modules enoughInjectives_modules
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The degreewise direct image of cochain complexes of modules along a morphism of algebraic
spaces. -/
abbrev complexPushforward {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X) :
    CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ ⥤
      CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ :=
  (modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The degreewise étale restriction of cochain complexes of modules. -/
abbrev complexEtalePullback {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) :
    CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ ⥤
      CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ :=
  (etaleModulePullback.{u, u} B S hS f hf).mapHomologicalComplex (ComplexShape.up ℤ)

/-- For an algebraic space `X` and a morphism `j : Y ⟶ X` from a presheaf `Y`: if `Y` is an
algebraic space and `j` is étale, then for every K-injective complex `I` of `𝒪_Y`-modules the
direct image `j_*I` is coreflective in `D(𝒪_X)`. -/
def CoreflectivePushforward (X : AlgebraicSpaces B S hS) (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (j : Y ⟶ X.1) : Prop :=
  ∀ (hY : IsAlgebraicSpace B S hS Y), IsEtale B S hS j →
    ∀ (I : CochainComplex (Modules.{u, u} B S hS Y hY) ℤ), I.IsKInjective →
      spaceCoreflective B S hS X ((spaceDerivedQ B S hS X).obj
        ((complexPushforward B S hS
          (ObjectProperty.homMk j : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj I))

variable {B S hS}

/-- Étale restriction preserves K-injective complexes. -/
theorem isKInjective_complexEtalePullback {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    [I.IsKInjective] : ((complexEtalePullback B S hS f hf).obj I).IsKInjective :=
  Stacks.Injectives.isKInjective_mapHomologicalComplex_of_adjunction _ _
    (etaleModuleLowerShriekAdjunction B S hS f hf) I

/-- Direct image along an étale morphism preserves K-injective complexes. -/
theorem isKInjective_complexPushforward_of_isEtale {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
    [I.IsKInjective] : ((complexPushforward B S hS f).obj I).IsKInjective :=
  Stacks.Injectives.isKInjective_mapHomologicalComplex_of_adjunction _ _
    (etaleModulePullbackAdjunction B S hS f hf) I

/-- The coreflective objects are closed under isomorphism. -/
instance (X : AlgebraicSpaces B S hS) :
    (spaceCoreflective B S hS X).IsClosedUnderIsomorphisms := by
  infer_instance

/-- The coreflective objects are closed under binary biproducts. -/
theorem spaceCoreflective_biprod {X : AlgebraicSpaces B S hS} {A C : spaceDerivedCategory B S hS X}
    (hA : spaceCoreflective B S hS X A) (hC : spaceCoreflective B S hS X C) :
    spaceCoreflective B S hS X (A ⊞ C) :=
  (spaceCoreflective B S hS X).ext_of_isTriangulatedClosed₂ _
    (binaryBiproductTriangle_distinguished _ _) hA hC

/-- For a K-injective complex `I`, `Rj_*I` is coreflective iff `j_*I` is. -/
private theorem spaceCoreflective_derivedPushforward_iff {X Y : AlgebraicSpaces B S hS}
    (j : Y ⟶ X) (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) [hI : I.IsKInjective] :
    spaceCoreflective B S hS X ((spaceDerivedPushforward B S hS j).obj
      ((spaceDerivedQ B S hS Y).obj I)) ↔
    spaceCoreflective B S hS X
      ((spaceDerivedQ B S hS X).obj ((complexPushforward B S hS j).obj I)) :=
  ObjectProperty.prop_iff_of_iso _ (spaceDerivedPushforwardQIso B S hS j I hI)

/-- The direct image along `jW` of `jT,* jT^* I`, for `jT : T ⟶ W` étale and `I` K-injective,
is coreflective as soon as `P(T, jT ≫ jW)` holds. -/
theorem spaceCoreflective_spaceDerivedPushforward_restrictPush {X W T : AlgebraicSpaces B S hS}
    (jW : W ⟶ X) (hjW : IsEtale B S hS jW.hom) (jT : T ⟶ W) (hjT : IsEtale B S hS jT.hom)
    (hT : CoreflectivePushforward B S hS X T.1 (jT.hom ≫ jW.hom))
    (I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) [I.IsKInjective] :
    spaceCoreflective B S hS X ((spaceDerivedPushforward B S hS jW).obj
      ((spaceDerivedQ B S hS W).obj ((complexPushforward B S hS jT).obj
        ((complexEtalePullback B S hS jT hjT).obj I)))) := by
  have := isKInjective_complexEtalePullback jT hjT I
  have := isKInjective_complexPushforward_of_isEtale jT hjT
    ((complexEtalePullback B S hS jT hjT).obj I)
  refine (spaceCoreflective_derivedPushforward_iff jW _).2 ?_
  refine ObjectProperty.prop_of_iso _ ((spaceDerivedQ B S hS X).mapIso
    ((NatIso.mapHomologicalComplex (modulePushforwardCompIso B S hS jT jW)
      (ComplexShape.up ℤ)).app ((complexEtalePullback B S hS jT hjT).obj I)).symm) ?_
  exact hT T.2 (isEtale_comp B S hS hjT hjW) _ inferInstance

/-- Let `(U ⊆ W, f : V ⟶ W)` be an elementary distinguished square and let `jW : W ⟶ X` be étale.
If `P(Y, j)` holds for `U`, `V` and `U ×_W V` with their composite morphisms to `X`, then for every
K-injective complex `I` of `𝒪_W`-modules the direct image `jW,* I` is coreflective in `D(𝒪_X)`. -/
theorem coreflectivePushforward_of_isElementaryDistinguishedSquare
    {X W : AlgebraicSpaces B S hS} (jW : W ⟶ X) (hjW : IsEtale B S hS jW.hom)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : Subfunctor W.1} {f : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 U f)
    (hU : CoreflectivePushforward B S hS X U.toFunctor (U.ι ≫ jW.hom))
    (hV : CoreflectivePushforward B S hS X V (f ≫ jW.hom))
    (hP : CoreflectivePushforward B S hS X (pullback U.ι f) ((pullback.fst U.ι f ≫ U.ι) ≫ jW.hom))
    (I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) [I.IsKInjective] :
    spaceCoreflective B S hS X
      ((spaceDerivedQ B S hS X).obj ((complexPushforward B S hS jW).obj I)) := by
  let := spaceHasDerivedCategory B S hS W
  let := spaceHasDerivedCategory B S hS X
  have := smallEtaleRingedSite_hasSheafify_addCommGrpCat B S hS W
  have := smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat B S hS W
  obtain ⟨δ, hT⟩ := mem_distTriang_unitBiprod_of_natural_shortExact
    (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit _ _
    (zero_edsRestrictPushMayerVietorisLowerShriek B S hS hsq)
    (shortExact_edsRestrictPushMayerVietorisLowerShriek B S hS hsq) I
  have hUc := spaceCoreflective_spaceDerivedPushforward_restrictPush jW hjW
    (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) hU I
  have hVc := spaceCoreflective_spaceDerivedPushforward_restrictPush jW hjW
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq) hV I
  have hPc := spaceCoreflective_spaceDerivedPushforward_restrictPush jW hjW
    (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq) hP I
  have hT' := (spaceDerivedPushforward B S hS jW).map_distinguished _ hT
  have : (spaceDerivedPushforward B S hS jW).Additive := inferInstance
  let A := DerivedCategory.Q.obj ((edsRestrictPushOpen B S hS hsq).mapHomologicalComplex
    (ComplexShape.up ℤ) |>.obj I)
  let C := DerivedCategory.Q.obj ((edsRestrictPushEtale B S hS hsq).mapHomologicalComplex
    (ComplexShape.up ℤ) |>.obj I)
  have hmid : spaceCoreflective B S hS X ((spaceDerivedPushforward B S hS jW).obj (A ⊞ C)) :=
    ObjectProperty.prop_of_iso _ ((spaceDerivedPushforward B S hS jW).biprodIsoOfAdditive A C).symm
      (spaceCoreflective_biprod hUc hVc)
  exact (spaceCoreflective_derivedPushforward_iff jW I).1
    ((spaceCoreflective B S hS X).ext_of_isTriangulatedClosed₁ _ hT' hmid hPc)

/-- **`Rf_*` of a complex of quasi-coherent modules along an affine morphism has quasi-coherent
cohomology.** For `f` affine and `C` a complex of quasi-coherent `𝒪_X`-modules, `Rf_*C` lies in
`D_QCoh`. -/
theorem spaceQuasicoherentProp_spaceDerivedPushforward_of_isAffineHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (C : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hC : ∀ n, (C.X n).IsQuasicoherentOnSite) :
    spaceQuasicoherentProp B S hS Y
      ((spaceDerivedPushforward B S hS f).obj ((spaceDerivedQ B S hS X).obj C)) := by
  let := spaceHasDerivedCategory B S hS X
  let := spaceHasDerivedCategory B S hS Y
  have : IsIso ((spaceDerivedPushforwardUnit B S hS f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) :=
    isIso_derivedModulePushforwardUnit_app_of_isQuasicoherentOnSite B S hS f hf _ _ C hC
  have hqc : ∀ n, (((complexPushforward B S hS f).obj C).X n).IsQuasicoherentOnSite :=
    fun n => isQuasicoherentOnSite_modulePushforward_isAffineHom B S hS f hf _ (hC n)
  refine ObjectProperty.prop_of_iso _
    ((DerivedCategory.quotientCompQhIso _).app ((complexPushforward B S hS f).obj C)).symm ?_ |>
    fun h => ObjectProperty.prop_of_iso _
      (asIso ((spaceDerivedPushforwardUnit B S hS f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) ≪≫
        (spaceDerivedPushforward B S hS f).mapIso
          ((DerivedCategory.quotientCompQhIso _).app C)) h
  exact isQuasicoherentOnSite_derived_homology B S hS _ hqc

/-- Let `j : V ⟶ X` be étale and affine, and suppose that on `V` every object of `D(𝒪_V)` is
coreflective and every object of `D_QCoh(𝒪_V)` is represented by a complex of quasi-coherent
modules. Then for every K-injective complex `I` of `𝒪_V`-modules the direct image `j_*I` is
coreflective in `D(𝒪_X)`. -/
theorem spaceCoreflective_complexPushforward_of_isAffineHom {X V : AlgebraicSpaces B S hS}
    (j : V ⟶ X) (hj : IsEtale B S hS j.hom) (haff : IsAffineHom B S hS j.hom)
    (hV : ∀ K, spaceCoreflective B S hS V K)
    (hrep : ∀ E, spaceQuasicoherentProp B S hS V E →
      ∃ (C : CochainComplex (Modules.{u, u} B S hS V.1 V.2) ℤ)
        (_ : ∀ n, (C.X n).IsQuasicoherentOnSite), Nonempty ((spaceDerivedQ B S hS V).obj C ≅ E))
    (I : CochainComplex (Modules.{u, u} B S hS V.1 V.2) ℤ) [I.IsKInjective] :
    spaceCoreflective B S hS X
      ((spaceDerivedQ B S hS X).obj ((complexPushforward B S hS j).obj I)) := by
  obtain ⟨E, Q', a, b, c, hT, hE, hQ'⟩ := hV ((spaceDerivedQ B S hS V).obj I)
  obtain ⟨C, hC, ⟨e⟩⟩ := hrep E hE
  have hE' : spaceQuasicoherentProp B S hS X ((spaceDerivedPushforward B S hS j).obj E) :=
    ObjectProperty.prop_of_iso _ ((spaceDerivedPushforward B S hS j).mapIso e)
      (spaceQuasicoherentProp_spaceDerivedPushforward_of_isAffineHom j haff C hC)
  have hQ'' := rightOrthogonal_spaceDerivedPushforward B S hS j hj Q' hQ'
  exact (spaceCoreflective_derivedPushforward_iff j I).1
    ⟨_, _, _, _, _, (spaceDerivedPushforward B S hS j).map_distinguished _ hT, hE', hQ''⟩

/-- **Every object of `D(𝒪_X)` is coreflective**, for a quasi-compact quasi-separated algebraic
space `X` all of whose affine étale objects map to `X` by affine morphisms, granted the affine
case: on an affine algebraic space every object is coreflective and every object of `D_QCoh` is
represented by a complex of quasi-coherent modules ([Stacks, Tag 0CR4]). -/
theorem spaceCoreflective_of_affineCase (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hdiag : ∀ V : SpacesEtale B S hS X, IsAffineSpace B S hS V.1.left.1 →
      IsAffineHom B S hS V.1.hom.hom)
    (haffine : ∀ Y : AlgebraicSpaces B S hS, IsAffineSpace B S hS Y.1 →
      (∀ K, spaceCoreflective B S hS Y K) ∧
      ∀ E, spaceQuasicoherentProp B S hS Y E →
        ∃ (C : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
          (_ : ∀ n, (C.X n).IsQuasicoherentOnSite), Nonempty ((spaceDerivedQ B S hS Y).obj C ≅ E))
    (K : spaceDerivedCategory B S hS X) : spaceCoreflective B S hS X K := by
  have hself : CoreflectivePushforward B S hS X X.1 (𝟙 X.1) := by
    refine qcqs_induction_on_self B S hS hZ X hXqc hXqs (CoreflectivePushforward B S hS X)
      ?_ ?_
    · intro V hVaff hY hj I hI
      have := hI
      exact spaceCoreflective_complexPushforward_of_isAffineHom
        (ObjectProperty.homMk V.1.hom.hom : (⟨V.1.left.1, hY⟩ : AlgebraicSpaces B S hS) ⟶ X) hj
        (hdiag V hVaff) (haffine ⟨_, hY⟩ hVaff).1 (haffine ⟨_, hY⟩ hVaff).2 I
    · intro W V U f hf hsq _ _ _ _ hU hV hP hY hj I hI
      have := hI
      have hV' : CoreflectivePushforward B S hS X V.1.left.1 (f ≫ W.1.hom.hom) := by
        rw [hf]; exact hV
      have hP' : CoreflectivePushforward B S hS X (pullback U.ι f)
          ((pullback.fst U.ι f ≫ U.ι) ≫ W.1.hom.hom) := by
        rw [Category.assoc]; exact hP
      exact coreflectivePushforward_of_isElementaryDistinguishedSquare (X := X)
        (W := ⟨W.1.left.1, hY⟩) (ObjectProperty.homMk W.1.hom.hom) hj hsq hU hV' hP' I
  let := spaceHasDerivedCategory B S hS X
  obtain ⟨I, g, hI, hg⟩ := exists_quasiIso_isKInjective_modules B S hS X.1 X.2
    (DerivedCategory.Q.objPreimage K)
  have := hI
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hg
  have h := hself X.2 (isEtale_id B S hS X.1) I hI
  refine ObjectProperty.prop_of_iso _ ?_ h
  exact (spaceDerivedQ B S hS X).mapIso
      ((NatIso.mapHomologicalComplex (modulePushforwardIdIso B S hS X) (ComplexShape.up ℤ)).app I ≪≫
        (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app I) ≪≫
    (asIso (DerivedCategory.Q.map g)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K

end AlgebraicGeometry.Space

end
