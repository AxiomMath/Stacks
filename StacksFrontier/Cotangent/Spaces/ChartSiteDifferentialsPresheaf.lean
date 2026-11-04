module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsLocalIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedExistence
public import StacksFrontier.Cotangent.Spaces.ChartSiteFlatDifferentials

/-!
# `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` on the chart site of an algebraic space is a sheafified presheaf

On the site `C_{X/Λ}` of polynomial charts of an algebraic space `X` over a ring `Λ`
(Tag 08VK), the sheaf of `π⁻¹𝒪_X`-modules `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` of Tag 08VM is the
sheafification of the presheaf `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A, 𝒪_A)} Ω_{Γ(A, 𝒪_A)/Λ}`, along a
canonical map of presheaves of modules.

The module `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` is read over the restriction `𝒪̲_X` of the structure sheaf of
the small étale site of `X` along the forgetful functor `C_{X/Λ} ⥤ X_étale`, which is the sheaf
of rings `π⁻¹𝒪_X` of the fibred category situation of Tag 08VL on which the derived lower shriek
is formed; it is identified with the topos-theoretic inverse image `π⁻¹𝒪_X` of Tag 08VK by
`AlgebraicGeometry.Space.PolynomialChart.liftedRestrictionIso`.

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart.chartStructureRing`: `𝒪̲_X`, the restriction of the
  structure sheaf of `X_étale`, as a sheaf of rings on the chart site.
* `AlgebraicGeometry.Space.PolynomialChart.chartDifferentialsBaseChangeRestricted`:
  `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` read over `𝒪̲_X`.
* `AlgebraicGeometry.Space.PolynomialChart.chartBaseChangePresheaf`: the presheaf of
  `𝒪̲_X`-modules `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}`.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.toSheafify_comp_horizontalCoefficientMap`: on the
  affine functions of a chart, `i♯ : 𝒪 ⟶ π⁻¹𝒪_X` is evaluation along the chart.
* `AlgebraicGeometry.Space.PolynomialChart.chartBaseChangePresheafSheafifyIso`:
  `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` is the sheafification of `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}`.
* `AlgebraicGeometry.Space.PolynomialChart.W_chartBaseChangePresheafMap`: the canonical map from
  that presheaf to the sections of `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` is inverted by sheafification.

## References

* [Stacks Project, Tag 08VM](https://stacks.math.columbia.edu/tag/08VM)
* [Stacks Project, Tag 08VK](https://stacks.math.columbia.edu/tag/08VK)
* [Stacks Project, Tag 08VL](https://stacks.math.columbia.edu/tag/08VL)
* [Stacks Project, Tag 08TP](https://stacks.math.columbia.edu/tag/08TP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

attribute [-instance] CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

attribute [local instance] hasSheafify_addCommGrpCat_topology wEqualsLocallyBijective_topology

/-! ### `i♯` on the affine functions of a chart -/

/-- Sectionwise, the inverse of an isomorphism of sheaves of commutative rings undoes it. -/
private theorem iso_inv_hom_app_hom_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J CommRingCat.{u + 1}} (e : F ≅ G) (P : Cᵒᵖ) (x : F.obj.obj P) :
    e.inv.hom.app P (e.hom.hom.app P x) = x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun f => f.hom) e.hom_inv_id) P) x

/-- **On the affine functions of a chart, `i♯` is evaluation.** The structure map
`i♯ : 𝒪 ⟶ π⁻¹𝒪_X` of the horizontal arrow of Tag 08VK, restricted to the presheaf
`(U ⟶ A) ↦ Γ(A, 𝒪_A)` whose sheafification is `𝒪`, is pullback of functions along `U ⟶ A`
followed by the identification of `π⁻¹𝒪_X` with the restriction of `𝒪_X`. -/
theorem toSheafify_comp_horizontalCoefficientMap :
    toSheafify (topology Λ B hS X hX) (liftedAffinePresheaf Λ B hS X hX) ≫
        (horizontalCoefficientMap Λ B hS X hX).hom =
      liftedEvaluation Λ B hS X hX ≫
        (liftedRestrictionIso Λ B hS X hX).inv.hom := by
  ext P x
  have hb := Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_homEquiv
    (liftedIdentityTopos Λ B hS X hX) (liftedAffineSheaf Λ B hS X hX)
    (chartStructureSheaf Λ B hS X hX)
    (liftedHorizontalMapInverse Λ B hS X hX)
  have h1 : (horizontalCoefficientMap Λ B hS X hX).hom.app P
      ((toSheafify (topology Λ B hS X hX)
        (liftedAffinePresheaf Λ B hS X hX)).app P x) =
      (liftedHorizontalMapInverse Λ B hS X hX).hom.app P
        ((toSheafify (topology Λ B hS X hX)
          (liftedAffinePresheaf Λ B hS X hX)).app P x) :=
    congrFun (congrArg (fun φ => φ.hom.app P) hb) _
  refine h1.trans ?_
  have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (topology Λ B hS X hX)
      (liftedEvaluation Λ B hS X hX)) P) x
  have h3 := iso_inv_hom_app_hom_app (sheafificationIso (liftedEtaleSheaf Λ B hS X hX)) P
    ((liftedEvaluation Λ B hS X hX).app P x)
  exact (congrArg ((liftedRestrictionIso Λ B hS X hX).inv.hom.app P ∘
      (sheafificationIso (liftedEtaleSheaf Λ B hS X hX)).inv.hom.app P)
        h2.symm).trans
    (congrArg ((liftedRestrictionIso Λ B hS X hX).inv.hom.app P) h3)

/-! ### The sheaf of rings `𝒪̲_X` -/

/-- `𝒪̲_X`: the structure sheaf of the small étale site of `X` restricted along the forgetful
functor of the chart site, as a sheaf of rings. This is `π⁻¹𝒪_X` in the presentation of the fibred
category situation of Tag 08VL. -/
abbrev chartStructureRing : Sheaf (topology Λ B hS X hX) RingCat.{u + 1} :=
  Stacks.Cohomology.DerivedLowerShriek.inverseImageRing (topology Λ B hS X hX)
    (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX))
    (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩))

/-- The two presentations of `π⁻¹𝒪_X` on the chart site agree as sheaves of rings: the
topos-theoretic inverse image of Tag 08VK and the restriction `𝒪̲_X`. -/
def chartStructureRingIso :
    ringSheaf (chartStructureSheaf Λ B hS X hX) ≅
      chartStructureRing Λ B hS X hX :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight ((sheafToPresheaf _ _).mapIso
      (liftedRestrictionIso Λ B hS X hX)) (forget₂ CommRingCat RingCat))

/-! ### `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` over `𝒪̲_X`, and the presheaf it sheafifies -/

attribute [local instance] isRightAdjoint_pushforward_horizontalSiteHom_fSharpRing

/-- `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`, read over `𝒪̲_X` through `chartStructureRingIso`. -/
def chartDifferentialsBaseChangeRestricted :
    SheafOfModules.{u + 1} (chartStructureRing Λ B hS X hX) :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (chartStructureRingIso Λ B hS X hX)).functor.obj
      (chartDifferentialsBaseChange Λ B hS X hX)

/-- The presheaf of `𝒪̲_X`-modules `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A, 𝒪_A)} Ω_{Γ(A, 𝒪_A)/Λ}` on the chart
site: the objectwise Kähler differentials of the affine functions over `Λ`, with scalars
extended along evaluation. -/
def chartBaseChangePresheaf :
    PresheafOfModules.{u + 1} (chartStructureRing Λ B hS X hX).obj :=
  (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
    (liftedEvaluation Λ B hS X hX)).obj
      (AlgebraicGeometry.SheafOfModules.objectwiseRelativeDifferentials.{u, u}
        (liftedBasePresheafMap Λ B hS X hX))


/-- The left adjoint `P ↦ (𝒪̲_X ⊗_{Γ} P)^#` on presheaves of modules over the affine functions:
extension of scalars along evaluation, then sheafification over `𝒪̲_X`. -/
def chartBaseChangeSheafifyAdjunction :=
  Stacks.PresheafOfModules.ChangeOfRings.sheafifyChangeOfRingsAdjunction
    (J := topology Λ B hS X hX) (liftedEvaluation Λ B hS X hX)
    (chartStructureRing Λ B hS X hX).property

/-- The left adjoint `P ↦ (P^# ⊗_𝒪 π⁻¹𝒪_X)` read over `𝒪̲_X`, on presheaves of modules over the
affine functions: sheafification over `𝒪`, extension of scalars along `i♯`, and restriction of
scalars along `𝒪̲_X ≅ π⁻¹𝒪_X`. -/
def chartSheafifyBaseChangeAdjunction :=
  (PresheafOfModules.sheafificationAdjunction
      (Stacks.SheafOfModules.toAssociatedRingSheaf (topology Λ B hS X hX)
        (liftedAffinePresheaf Λ B hS X hX))).comp
    ((SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
        (F := 𝟭 (PolynomialChart Λ B hS X hX))
        (horizontalSiteHom Λ B hS X hX).fSharpRing).comp
      (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
        (chartStructureRingIso Λ B hS X hX)).toAdjunction)


/-- The scalar action of the affine functions of a chart on a sheaf of `𝒪̲_X`-modules, through
`i♯` followed by `π⁻¹𝒪_X ≅ 𝒪̲_X`, is the one through evaluation. -/
theorem chartStructureRingIso_horizontalCoefficientMap_apply
    (P : (PolynomialChart Λ B hS X hX)ᵒᵖ)
    (r : (liftedAffinePresheaf Λ B hS X hX).obj P) :
    (chartStructureRingIso Λ B hS X hX).hom.hom.app P
        ((horizontalSiteHom Λ B hS X hX).fSharpRing.hom.app P
          ((Stacks.SheafOfModules.toAssociatedRingSheaf (topology Λ B hS X hX)
            (liftedAffinePresheaf Λ B hS X hX)).app P r)) =
      (liftedEvaluation Λ B hS X hX).app P r := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_comp_horizontalCoefficientMap Λ B hS X hX) P) r
  exact (congrArg ((liftedRestrictionIso Λ B hS X hX).hom.hom.app P) h).trans
    (iso_inv_hom_app_hom_app (liftedRestrictionIso Λ B hS X hX).symm P _)

/-- Restriction of a sheaf of `𝒪̲_X`-modules to the affine functions through `π⁻¹𝒪_X` and `𝒪`. -/
abbrev chartRestrictThroughAffine :
    SheafOfModules.{u + 1} (chartStructureRing Λ B hS X hX) ⥤
      Stacks.PresheafOfModules.ChangeOfRings.PMod (liftedAffinePresheaf Λ B hS X hX) :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (chartStructureRingIso Λ B hS X hX)).inverse ⋙
    SheafOfModules.pushforward.{u + 1} (F := 𝟭 (PolynomialChart Λ B hS X hX))
      (horizontalSiteHom Λ B hS X hX).fSharpRing ⋙
    SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
      (Stacks.SheafOfModules.toAssociatedRingSheaf (topology Λ B hS X hX)
        (liftedAffinePresheaf Λ B hS X hX))

/-- Restriction of a sheaf of `𝒪̲_X`-modules to the affine functions along evaluation. -/
abbrev chartRestrictAlongEvaluation :
    SheafOfModules.{u + 1} (chartStructureRing Λ B hS X hX) ⥤
      Stacks.PresheafOfModules.ChangeOfRings.PMod (liftedAffinePresheaf Λ B hS X hX) :=
  (SheafOfModules.forget (chartStructureRing Λ B hS X hX) ⋙
      PresheafOfModules.restrictScalars (𝟙 _)) ⋙
    Stacks.PresheafOfModules.ChangeOfRings.restrictScalars
      (liftedEvaluation Λ B hS X hX)

/-- The isomorphism between the restrictions `chartRestrictThroughAffine` and
`chartRestrictAlongEvaluation`, the identity on sections. -/
def chartRestrictScalarsIso :
    chartRestrictThroughAffine Λ B hS X hX ≅ chartRestrictAlongEvaluation Λ B hS X hX :=
  NatIso.ofComponents (fun G => PresheafOfModules.isoMk (fun P =>
      (ModuleCat.restrictScalars _).mapIso
          (ModuleCat.restrictScalarsComp'App _ _ _ rfl (G.val.obj P)).symm ≪≫
        (ModuleCat.restrictScalarsComp'App _ _ _ rfl (G.val.obj P)).symm ≪≫
        (ModuleCat.restrictScalarsCongr (by
          ext r
          exact chartStructureRingIso_horizontalCoefficientMap_apply Λ B hS X hX P r)).app
          (G.val.obj P) ≪≫
        ModuleCat.restrictScalarsComp'App _ _ _ rfl (G.val.obj P))
      (fun _ _ _ => rfl)) (fun _ => by ext; rfl)

/-- The isomorphism between the left adjoints of `chartBaseChangeSheafifyAdjunction` and
`chartSheafifyBaseChangeAdjunction`. -/
def chartBaseChangeSheafifyIso :=
  Adjunction.leftAdjointUniq (chartBaseChangeSheafifyAdjunction Λ B hS X hX)
    ((chartSheafifyBaseChangeAdjunction Λ B hS X hX).ofNatIsoRight
      (chartRestrictScalarsIso Λ B hS X hX))

/-- **`Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` is the sheafification of `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}`**,
as a sheaf of `𝒪̲_X`-modules. -/
def chartBaseChangePresheafSheafifyIso :
    (PresheafOfModules.sheafification (𝟙 (chartStructureRing Λ B hS X hX).obj)).obj
        (chartBaseChangePresheaf Λ B hS X hX) ≅
      chartDifferentialsBaseChangeRestricted Λ B hS X hX :=
  have := CategoryTheory.Sheaf.wEqualsLocallyBijective_commRingCat.{u + 1, u, u + 1}
    (topology Λ B hS X hX)
  (chartBaseChangeSheafifyIso Λ B hS X hX).app
      (AlgebraicGeometry.SheafOfModules.objectwiseRelativeDifferentials.{u, u}
        (liftedBasePresheafMap Λ B hS X hX)) ≪≫
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (chartStructureRingIso Λ B hS X hX)).functor.mapIso
      ((SheafOfModules.pullback.{u + 1} (F := 𝟭 (PolynomialChart Λ B hS X hX))
        (horizontalSiteHom Λ B hS X hX).fSharpRing).mapIso
          (AlgebraicGeometry.SheafOfModules.differentialsSheafificationIso.{u, u}
            (topology Λ B hS X hX) _ _ (liftedBasePresheafMap Λ B hS X hX)).symm)


/-- The canonical map from `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}` to the sections of
`Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`, the transpose of `chartBaseChangePresheafSheafifyIso`. -/
def chartBaseChangePresheafMap :
    chartBaseChangePresheaf Λ B hS X hX ⟶
      (PresheafOfModules.restrictScalars (𝟙 (chartStructureRing Λ B hS X hX).obj)).obj
        (chartDifferentialsBaseChangeRestricted Λ B hS X hX).val :=
  PresheafOfModules.sheafificationHomEquiv _
    (chartBaseChangePresheafSheafifyIso Λ B hS X hX).hom

/-- **The canonical map is inverted by sheafification**: its underlying map of presheaves of
abelian groups lies in `W`. -/
theorem W_chartBaseChangePresheafMap :
    (topology Λ B hS X hX).W
      ((PresheafOfModules.toPresheaf _).map (chartBaseChangePresheafMap Λ B hS X hX)) := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (α := 𝟙 (chartStructureRing Λ B hS X hX).obj)
    (chartBaseChangePresheafSheafifyIso Λ B hS X hX).hom
  refine (congrArg (fun g => (topology Λ B hS X hX).W g) h).mpr ?_
  let e := (PresheafOfModules.toPresheaf (chartStructureRing Λ B hS X hX).obj).mapIso
    ((SheafOfModules.forget _).mapIso (chartBaseChangePresheafSheafifyIso Λ B hS X hX))
  exact MorphismProperty.comp_mem _ _ _ ((topology Λ B hS X hX).W_toSheafify _)
    (ObjectProperty.isLocal_of_isIso _ e.hom)


end AlgebraicGeometry.Space.PolynomialChart
