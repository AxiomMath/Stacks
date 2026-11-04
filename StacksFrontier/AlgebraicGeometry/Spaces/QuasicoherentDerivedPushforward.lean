module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestrictionNoShriekData
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated

/-!
# The derived direct image of a quasi-compact quasi-separated morphism on `D_QCoh`

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over a scheme
`S` contained in a big fppf site `B`. Then `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`.

## Main definitions

* `AlgebraicGeometry.Space.PreservesQuasicoherentCohomology`: the direct image along a morphism
  carries a K-injective complex with quasi-coherent cohomology to a complex with quasi-coherent
  cohomology.
* `AlgebraicGeometry.Space.QcohDerived`: the objects of the derived category with quasi-coherent
  cohomology sheaves.

## Main results

* `AlgebraicGeometry.Space.preservesQuasicoherentCohomology_of_isElementaryDistinguishedSquare`:
  the property passes across an elementary distinguished square.
* `AlgebraicGeometry.Space.preservesQuasicoherentCohomology`: the property holds for every
  quasi-compact quasi-separated morphism.
* `AlgebraicGeometry.Space.qcohDerived_rightDerived_obj`: every right derived functor of the
  direct image along a quasi-compact quasi-separated morphism carries `D_QCoh(𝒪_X)` into
  `D_QCoh(𝒪_Y)`.

## References

* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated
open CategoryTheory.PushforwardMayerVietoris

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The direct image of modules along `g` carries every K-injective complex of `𝒪_W`-modules with
quasi-coherent cohomology sheaves to a complex with quasi-coherent cohomology sheaves. -/
def PreservesQuasicoherentCohomology {W Y : AlgebraicSpaces B S hS} (g : W ⟶ Y) : Prop :=
  ∀ I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ, I.IsKInjective →
    (∀ q : ℤ, (I.homology q).IsQuasicoherentOnSite) → ∀ q : ℤ,
      ((((modulePushforward B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology
        q).IsQuasicoherentOnSite

/-! ### Étale pullbacks and pushforwards of K-injective complexes -/

/-- Restriction along an étale morphism keeps quasi-coherence of the cohomology sheaves of a
complex. -/
theorem isQuasicoherentOnSite_homology_etaleModulePullback {W Z : AlgebraicSpaces B S hS}
    (j : W ⟶ Z) (hj : IsEtale B S hS j.hom)
    (I : CochainComplex (Modules.{u, u} B S hS Z.1 Z.2) ℤ)
    (hqc : ∀ q : ℤ, (I.homology q).IsQuasicoherentOnSite) (q : ℤ) :
    ((((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology q).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso ((I.sc q).mapHomologyIso
      (etaleModulePullback.{u, u} B S hS j hj)).symm
    (isQuasicoherentOnSite_etaleModulePullback B S hS j hj _ (hqc q))

/-- The direct image along an étale morphism carries K-injective complexes to K-injective
complexes. -/
theorem isKInjective_modulePushforward_of_isEtale {W Z : AlgebraicSpaces B S hS}
    (j : W ⟶ Z) (hj : IsEtale B S hS j.hom)
    (I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  let := hI
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact (modulePushforward B S hS j)
    (etaleModulePullback.{u, u} B S hS j hj) (etaleModulePullbackAdjunction B S hS j hj) I

/-! ### From complexes to the derived category -/

/-- Having quasi-coherent cohomology sheaves, as a property of objects of `D(𝒪_Y)`. -/
abbrev QcohDerived (Y : AlgebraicSpaces B S hS) :
    ObjectProperty (DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :=
  DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))

/-- Having quasi-coherent cohomology sheaves is invariant under isomorphism in `D(𝒪_Y)`. -/
instance (Y : AlgebraicSpaces B S hS) : (QcohDerived B S hS Y).IsClosedUnderIsomorphisms :=
  ⟨fun e h n => SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso e) (h n)⟩

/-- A cochain complex has quasi-coherent cohomology sheaves exactly when its image in the derived
category lies in `D_QCoh`. -/
theorem qcohDerived_Q_obj_iff {Y : AlgebraicSpaces B S hS}
    (K : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) :
    QcohDerived B S hS Y (DerivedCategory.Q.obj K) ↔
      ∀ q : ℤ, (K.homology q).IsQuasicoherentOnSite :=
  ⟨fun h q => SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.homologyFunctorFactors _ q).app K) (h q),
    fun h q => SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.homologyFunctorFactors _ q).app K).symm (h q)⟩

/-- If every right derived functor of the direct image along `g` carries a K-injective complex `I`
into `D_QCoh`, then the direct image of `I` itself has quasi-coherent cohomology. -/
private theorem qcohDerived_Q_obj_pushforward_of_forall_rightDerived
    {W Y : AlgebraicSpaces B S hS} (g : W ⟶ Y)
    (I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) (hI : I.IsKInjective)
    (h : ∀ (RF : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
      (α : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
      [RF.IsRightDerivedFunctor α
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))],
      QcohDerived B S hS Y (RF.obj (DerivedCategory.Q.obj I))) :
    QcohDerived B S hS Y (DerivedCategory.Q.obj
      (((modulePushforward B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
  have := hasRightDerivedFunctor_modulePushforward B S hS g
  let RF := ((modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
  let α := ((modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
  obtain ⟨e⟩ := nonempty_rightDerived_obj_iso_of_isKInjective B S hS g RF α I hI
  exact (QcohDerived B S hS Y).prop_of_iso e (h RF α)

/-! ### The Mayer–Vietoris step -/

section MayerVietoris

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W Y : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

include hsq in
/-- Let `(U ⊆ W, V → W)` be an elementary distinguished square and `g : W ⟶ Y` a morphism. If the
direct images along `U ⟶ Y`, `V ⟶ Y` and `U ×_W V ⟶ Y` preserve quasi-coherence of the cohomology
of K-injective complexes, so does the direct image along `g`. -/
theorem preservesQuasicoherentCohomology_of_isElementaryDistinguishedSquare (g : W ⟶ Y)
    (hU : PreservesQuasicoherentCohomology B S hS (edsOpenHom B S hS hsq ≫ g))
    (hV : PreservesQuasicoherentCohomology B S hS (edsEtaleHom B S hS hsq ≫ g))
    (hP : PreservesQuasicoherentCohomology B S hS (edsInterHom B S hS hsq ≫ g)) :
    PreservesQuasicoherentCohomology B S hS g := by
  intro I hI hqc
  rw [← qcohDerived_Q_obj_iff]
  refine qcohDerived_Q_obj_pushforward_of_forall_rightDerived B S hS g I hI fun RF α _ => ?_
  obtain ⟨δ, hT⟩ := mem_distTriang_unitBiprod_of_natural_shortExact
    (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit
    (conjugateEquiv ((edsAdjOpen B S hS hsq).comp (edsLowerShriekAdjOpen B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (zero_edsRestrictPushMayerVietorisLowerShriek B S hS hsq)
    (shortExact_edsRestrictPushMayerVietorisLowerShriek B S hS hsq) I
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS g) RF α
  have hT' := RF.map_distinguished _ hT
  have key : ∀ (Z : AlgebraicSpaces B S hS) (j : Z ⟶ W) (hj : IsEtale B S hS j.hom),
      PreservesQuasicoherentCohomology B S hS (j ≫ g) →
      QcohDerived B S hS Y (RF.obj (DerivedCategory.Q.obj
        (((etaleModulePullback.{u, u} B S hS j hj ⋙
          modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) := by
    intro Z j hj hZ
    let J := ((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I
    have hJ : CochainComplex.IsKInjective J :=
      isKInjective_etaleModulePullback_of_isEtale B S hS j hj I hI
    let e₁ : ((etaleModulePullback.{u, u} B S hS j hj ⋙
          modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ≅
        ((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj J :=
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j))
        (ComplexShape.up ℤ)).app I).symm
    have hK := isKInjective_modulePushforward_of_isEtale B S hS j hj J hJ
    obtain ⟨e₂⟩ := nonempty_rightDerived_obj_iso_of_isKInjective B S hS g RF α _ hK
    let e₃ : ((modulePushforward B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≅
        ((modulePushforward B S hS (j ≫ g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J :=
      (Functor.mapHomologicalComplexCompIso (modulePushforwardCompIso B S hS j g)
        (ComplexShape.up ℤ)).app J
    refine (QcohDerived B S hS Y).prop_of_iso
      ((RF.mapIso (DerivedCategory.Q.mapIso e₁) ≪≫ e₂ ≪≫ DerivedCategory.Q.mapIso e₃).symm) ?_
    rw [qcohDerived_Q_obj_iff]
    exact hZ J hJ (fun q => isQuasicoherentOnSite_homology_etaleModulePullback B S hS j hj I hqc q)
  have h₁ := (QcohDerived B S hS Y).ext_of_isTriangulatedClosed₁ _ hT'
    ((QcohDerived B S hS Y).ext_of_isTriangulatedClosed₂
      (RF.mapTriangle.obj (binaryBiproductTriangle
        (DerivedCategory.Q.obj (((edsRestrictPushOpen B S hS hsq).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))
        (DerivedCategory.Q.obj (((edsRestrictPushEtale B S hS hsq).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))))
      (RF.map_distinguished _ (binaryBiproductTriangle_distinguished _ _))
      (key _ _ (isEtale_edsOpenHom B S hS hsq) hU) (key _ _ (isEtale_edsEtaleHom B S hS hsq) hV))
    (key _ _ (isEtale_edsInterHom B S hS hsq) hP)
  exact h₁

end MayerVietoris

/-! ### An affine source over an affine base -/

/-- The direct image along an affine morphism preserves quasi-coherence of the cohomology of
K-injective complexes. -/
theorem preservesQuasicoherentCohomology_of_isAffineHom {W Y : AlgebraicSpaces B S hS}
    (g : W ⟶ Y) (hg : IsAffineHom B S hS g.hom) : PreservesQuasicoherentCohomology B S hS g := by
  intro I hI hqc
  rw [← qcohDerived_Q_obj_iff]
  refine qcohDerived_Q_obj_pushforward_of_forall_rightDerived B S hS g I hI fun RF α _ => ?_
  exact isQuasicoherentOnSite_homology_rightDerived_modulePushforward_of_isAffineHom B S hS g RF α
    hg _ ((qcohDerived_Q_obj_iff B S hS I).2 hqc)

/-! ### The induction over a quasi-compact quasi-separated source -/

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- If `X₀` is quasi-compact and quasi-separated and `Y₀` is affine, the direct image along any
`f₀ : X₀ ⟶ Y₀` preserves quasi-coherence of the cohomology of K-injective complexes. -/
theorem preservesQuasicoherentCohomology_of_isAffineSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    {X₀ Y₀ : AlgebraicSpaces B S hS} (f₀ : X₀ ⟶ Y₀) (hY₀ : IsAffineSpace B S hS Y₀.1)
    (hqc : IsQuasiCompactSpace B S hS X₀.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X₀.1) :
    PreservesQuasicoherentCohomology B S hS f₀ := by
  have key := qcqs_induction_on_self B S hS hZ X₀ hqc hqs
    (fun Z z => ∀ hZ' : IsAlgebraicSpace B S hS Z, PreservesQuasicoherentCohomology B S hS
      ((ObjectProperty.homMk z : (⟨Z, hZ'⟩ : AlgebraicSpaces B S hS) ⟶ X₀) ≫ f₀))
    (fun V hV hV' => preservesQuasicoherentCohomology_of_isAffineHom B S hS _
      (isAffineHom_of_isAffineSpace B S hS _ hV hY₀))
    (fun W V U f hf hsq _ _ _ _ hPU hPV hPP hW' => by
      refine preservesQuasicoherentCohomology_of_isElementaryDistinguishedSquare B S hS hsq _
        ?_ ?_ ?_
      · have e : edsOpenHom B S hS hsq ≫ (ObjectProperty.homMk W.1.hom.hom ≫ f₀) =
            ObjectProperty.homMk (U.ι ≫ W.1.hom.hom) ≫ f₀ :=
          ObjectProperty.hom_ext _ rfl
        rw [e]
        exact hPU _
      · have e : edsEtaleHom B S hS hsq ≫ (ObjectProperty.homMk W.1.hom.hom ≫ f₀) =
            ObjectProperty.homMk V.1.hom.hom ≫ f₀ :=
          ObjectProperty.hom_ext _ (by
            simp only [ObjectProperty.FullSubcategory.comp_hom, ← hf]; rfl)
        rw [e]
        exact hPV _
      · have e : edsInterHom B S hS hsq ≫ (ObjectProperty.homMk W.1.hom.hom ≫ f₀) =
            ObjectProperty.homMk (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) ≫ f₀ :=
          ObjectProperty.hom_ext _ rfl
        rw [e]
        exact hPP _)
  have e : (ObjectProperty.homMk (𝟙 X₀.1) : X₀ ⟶ X₀) ≫ f₀ = f₀ :=
    ObjectProperty.hom_ext _ (by simp)
  exact e ▸ key X₀.2

/-! ### An arbitrary base -/

/-- The direct image along a quasi-compact quasi-separated morphism preserves quasi-coherence of
the cohomology of K-injective complexes. -/
theorem preservesQuasicoherentCohomology {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    PreservesQuasicoherentCohomology B S hS f := by
  intro I hI hqc q
  refine isQuasicoherentOnSite_of_forall_affine_chart B S hS _ fun A hA => ?_
  let j := chartToSpace B S hS Y A
  have hj : IsEtale B S hS j.hom := isEtale_chartToSpace B S hS Y A
  have sq := isPullback_chartBaseChangeInclusion B S hS f A
  let i := chartBaseChangeInclusion B S hS f A
  have hi : IsEtale B S hS i.hom := isEtale_chartBaseChangeInclusion B S hS f A
  let f' := chartBaseChangeProjection B S hS f A
  let J := ((etaleModulePullback.{u, u} B S hS i hi).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  have hJ : CochainComplex.IsKInjective J :=
    isKInjective_etaleModulePullback_of_isEtale B S hS i hi I hI
  have hJqc := isQuasicoherentOnSite_homology_etaleModulePullback B S hS i hi I hqc
  have hZ := B.contains_terminal
  have h' := preservesQuasicoherentCohomology_of_isAffineSpace B S hS hZ f'
    (isAffineSpace_chartSpace B S hS Y A hA)
    (isQuasiCompactSpace_chartBaseChange B S hS f A hA hfqc)
    (isAbsolutelyQuasiSeparated_chartBaseChangeSpace B S hS hZ f A hA hfqs) J hJ hJqc q
  let HC := HomologicalComplex.homologyFunctor (Modules.{u, u} B S hS (chartSpace B S hS Y A).1
    (chartSpace B S hS Y A).2) (ComplexShape.up ℤ) q
  let HH := HomotopyCategory.homologyFunctor (Modules.{u, u} B S hS (chartSpace B S hS Y A).1
    (chartSpace B S hS Y A).2) (ComplexShape.up ℤ) q
  let Qt := HomotopyCategory.quotient (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)
  let e₁ : HH.obj (((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleModulePullback.{u, u} B S hS j hj).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (Qt.obj I)) ≅
      HC.obj (((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    HH.mapIso (((etaleModulePullback.{u, u} B S hS j hj).mapHomotopyCategory
        (ComplexShape.up ℤ)).mapIso
          (((modulePushforward B S hS f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I) ≪≫
        ((etaleModulePullback.{u, u} B S hS j hj).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).app _) ≪≫
      (HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) q).app _
  let e₂ : HH.obj (((etaleModulePullback.{u, u} B S hS i hi).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
        (modulePushforward B S hS f').mapHomotopyCategory (ComplexShape.up ℤ)).obj (Qt.obj I)) ≅
      HC.obj (((modulePushforward B S hS f').mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    HH.mapIso (((modulePushforward B S hS f').mapHomotopyCategory (ComplexShape.up ℤ)).mapIso
          (((etaleModulePullback.{u, u} B S hS i hi).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).app I) ≪≫
        ((modulePushforward B S hS f').mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app _) ≪≫
      (HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) q).app _
  let e₃ := HH.mapIso ((etaleModulePushforwardRestrictHomotopyIso B S hS sq hj).app (Qt.obj I))
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((e₂.symm ≪≫ e₃.symm ≪≫ e₁) ≪≫
      (((((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).sc
        q).mapHomologyIso (etaleModulePullback.{u, u} B S hS j hj))) h'

/-! ### The derived direct image -/

section Derived

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- Let `f` be quasi-compact and quasi-separated, and let `G` be a functor equal to the direct
image `AlgebraicGeometry.Space.modulePushforward` along `f`. A functor `D(𝒪_X) ⥤ D(𝒪_Y)` computed
by `G` on K-injective complexes carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`. -/
theorem qcohDerived_obj_of_isKInjective_iso (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (G : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2)
    (hG : G = modulePushforward B S hS f) [G.PreservesZeroMorphisms]
    (RF : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hcomp : ∀ I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ, I.IsKInjective →
      Nonempty (RF.obj (DerivedCategory.Q.obj I) ≅
        DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E) :
    QcohDerived B S hS Y (RF.obj E) := by
  subst hG
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_iso_modules B S hS E
  obtain ⟨e'⟩ := hcomp I hI
  refine (QcohDerived B S hS Y).prop_of_iso (RF.mapIso e ≪≫ e').symm ?_
  rw [qcohDerived_Q_obj_iff]
  refine preservesQuasicoherentCohomology B S hS f hfqc hfqs I hI ?_
  rw [← qcohDerived_Q_obj_iff]
  exact (QcohDerived B S hS X).prop_of_iso e hE

/-- For a quasi-compact quasi-separated `f` and `E` in `D_QCoh(𝒪_X)`, every right derived functor
`Rf_*` of the direct image of modules carries `E` into `D_QCoh(𝒪_Y)`. This is part (1) of Stacks
08FA. -/
theorem qcohDerived_rightDerived_obj (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (RF : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E) :
    QcohDerived B S hS Y (RF.obj E) :=
  qcohDerived_obj_of_isKInjective_iso B S hS f hfqc hfqs _ rfl RF
    (fun I hI => nonempty_rightDerived_obj_iso_of_isKInjective B S hS f RF α I hI) E hE

end Derived

end AlgebraicGeometry.Space

end
