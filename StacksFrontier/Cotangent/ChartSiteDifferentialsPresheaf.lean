module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsLocalIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedExistence
public import StacksFrontier.Cotangent.ChartSiteFlatDifferentials

/-!
# `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` on the chart site is a sheafified presheaf

On the site `C_{X/Λ}` of polynomial charts of Tag 08VA, the sheaf of `π⁻¹𝒪_X`-modules
`Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` of Tag 08T9 is the sheafification of the presheaf
`(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A, 𝒪_A)} Ω_{Γ(A, 𝒪_A)/Λ}`, along a canonical map of presheaves of
modules. This is what makes its values on the charts `A_{n,U}` of the standard resolution
computable after sheafification on `X`, which is the first step of the proof of Tag 08T9.

The module `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` is read over the restriction `𝒪̲_X` of the lifted structure sheaf
of `X` along the forgetful functor `C_{X/Λ} ⥤ X_Zar`, which is the sheaf of rings `π⁻¹𝒪_X` of the
fibred category situation of Tag 08P8 on which the derived lower shriek is formed; it is
identified with the topos-theoretic inverse image `π⁻¹𝒪_X` of Tag 08VA by
`AlgebraicGeometry.PolynomialChart.restrictionIso`.

## Main definitions

* `AlgebraicGeometry.PolynomialChart.chartStructureRing`: `𝒪̲_X`, the restriction of the lifted
  structure sheaf of `X`, as a sheaf of rings on the chart site.
* `AlgebraicGeometry.PolynomialChart.chartDifferentialsBaseChangeRestricted`:
  `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` read over `𝒪̲_X`.
* `AlgebraicGeometry.PolynomialChart.chartBaseChangePresheaf`: the presheaf of `𝒪̲_X`-modules
  `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}`.

## Main results

* `AlgebraicGeometry.PolynomialChart.toSheafify_comp_horizontalCoefficientMap`: on the affine
  functions of a chart, `i♯ : 𝒪 ⟶ π⁻¹𝒪_X` is evaluation along the chart.
* `AlgebraicGeometry.PolynomialChart.chartBaseChangePresheafSheafifyIso`: `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`
  is the sheafification of `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}`.
* `AlgebraicGeometry.PolynomialChart.W_chartBaseChangePresheafMap`: the canonical map from that
  presheaf to the sections of `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` is inverted by sheafification.

## References

* [Stacks Project, Tag 08T9](https://stacks.math.columbia.edu/tag/08T9)
* [Stacks Project, Tag 08VA](https://stacks.math.columbia.edu/tag/08VA)
* [Stacks Project, Tag 08TP](https://stacks.math.columbia.edu/tag/08TP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
  (structureMap : X ⟶ Spec (CommRingCat.of Λ))

/-- Presheaves of commutative rings on the chart site admit sheafification in the universe
`u + 1` of its objects. -/
theorem hasWeakSheafify_commRingCat_topology_succ :
    HasWeakSheafify (topology Λ X structureMap) CommRingCat.{u + 1} :=
  hasWeakSheafify_topology.{u, u + 1} Λ X structureMap

attribute [local instance] hasWeakSheafify_commRingCat_topology_succ
  hasSheafify_addCommGrpCat_topology_succ wEqualsLocallyBijective_topology_succ

/-! ### `i♯` on the affine functions of a chart -/

/-- An isomorphism of sheaves of commutative rings is the identity on sections, hom then inv. -/
private theorem sheaf_iso_hom_inv_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J CommRingCat.{u + 1}} (e : F ≅ G) (P : Cᵒᵖ) (y : F.obj.obj P) :
    e.inv.hom.app P (e.hom.hom.app P y) = y :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun f => f.hom) e.hom_inv_id) P) y

/-- **On the affine functions of a chart, `i♯` is evaluation.** The structure map
`i♯ : 𝒪 ⟶ π⁻¹𝒪_X` of the horizontal arrow of Tag 08VA, restricted to the presheaf
`(U ⟶ A) ↦ Γ(A, 𝒪_A)` whose sheafification is `𝒪`, is pullback of functions along `U ⟶ A`
followed by the identification of `π⁻¹𝒪_X` with the restriction of `𝒪_X`. -/
theorem toSheafify_comp_horizontalCoefficientMap :
    toSheafify (topology Λ X structureMap) (affinePresheaf.{u, u + 1} Λ X structureMap) ≫
        (horizontalCoefficientMap Λ X structureMap).hom =
      evaluation.{u, u + 1} Λ X structureMap ≫
        (restrictionIso.{u, u + 1} Λ X structureMap).inv.hom := by
  ext P x
  have hb := Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_homEquiv
    (identityTopos.{u, u + 1} Λ X structureMap) (affineSheaf.{u, u + 1} Λ X structureMap)
    (chartStructureSheaf.{u, u + 1} Λ X structureMap)
    (horizontalMapInverse.{u, u + 1} Λ X structureMap)
  have h1 : (horizontalCoefficientMap Λ X structureMap).hom.app P
      ((toSheafify (topology Λ X structureMap)
        (affinePresheaf.{u, u + 1} Λ X structureMap)).app P x) =
      (horizontalMapInverse.{u, u + 1} Λ X structureMap).hom.app P
        ((toSheafify (topology Λ X structureMap)
          (affinePresheaf.{u, u + 1} Λ X structureMap)).app P x) :=
    congrFun (congrArg (fun φ => φ.hom.app P) hb) _
  refine h1.trans ?_
  have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (topology Λ X structureMap)
      (evaluation.{u, u + 1} Λ X structureMap)) P) x
  have h3 := sheaf_iso_hom_inv_app_apply
    (sheafificationIso (zariskiSheaf.{u, u + 1} Λ X structureMap)) P
      ((evaluation.{u, u + 1} Λ X structureMap).app P x)
  exact (congrArg ((restrictionIso.{u, u + 1} Λ X structureMap).inv.hom.app P ∘
      (sheafificationIso (zariskiSheaf.{u, u + 1} Λ X structureMap)).inv.hom.app P)
        h2.symm).trans
    (congrArg ((restrictionIso.{u, u + 1} Λ X structureMap).inv.hom.app P) h3)

/-! ### The sheaf of rings `𝒪̲_X` -/

/-- `𝒪̲_X`: the lifted structure sheaf of `X` restricted along the forgetful functor of the chart
site, as a sheaf of rings. This is `π⁻¹𝒪_X` in the presentation of the fibred category situation
of Tag 08P8 on which the derived lower shriek of sheaves of modules is formed. -/
abbrev chartStructureRing : Sheaf (topology Λ X structureMap) RingCat.{u + 1} :=
  Stacks.Cohomology.DerivedLowerShriek.inverseImageRing (topology Λ X structureMap)
    (Opens.grothendieckTopology X) (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap))
    (ringSheaf (liftedStructureSheaf.{u, u} X))

/-- The two presentations of `π⁻¹𝒪_X` on the chart site agree as sheaves of rings: the
topos-theoretic inverse image of Tag 08VA and the restriction `𝒪̲_X`. -/
def chartStructureRingIso :
    ringSheaf (chartStructureSheaf.{u, u + 1} Λ X structureMap) ≅
      chartStructureRing Λ X structureMap :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight ((sheafToPresheaf _ _).mapIso
      (restrictionIso.{u, u + 1} Λ X structureMap)) (forget₂ CommRingCat RingCat))

/-! ### `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` over `𝒪̲_X`, and the presheaf it sheafifies -/

attribute [local instance] isRightAdjoint_pushforward_horizontalSiteHom_fSharpRing

/-- `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`, read over `𝒪̲_X` through `chartStructureRingIso`. -/
def chartDifferentialsBaseChangeRestricted :
    SheafOfModules.{u + 1} (chartStructureRing Λ X structureMap) :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (chartStructureRingIso Λ X structureMap)).functor.obj
      (chartDifferentialsBaseChange Λ X structureMap)

/-- The presheaf of `𝒪̲_X`-modules `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A, 𝒪_A)} Ω_{Γ(A, 𝒪_A)/Λ}` on the chart
site: the objectwise Kähler differentials of the affine functions over `Λ`, with scalars
extended along evaluation. -/
def chartBaseChangePresheaf :
    PresheafOfModules.{u + 1} (chartStructureRing Λ X structureMap).obj :=
  (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
    (evaluation.{u, u + 1} Λ X structureMap)).obj
      (AlgebraicGeometry.SheafOfModules.objectwiseRelativeDifferentials.{u, u}
        (basePresheafMap.{u, u + 1} Λ X structureMap))


/-- The left adjoint `P ↦ (𝒪̲_X ⊗_{Γ} P)^#` on presheaves of modules over the affine functions:
extension of scalars along evaluation, then sheafification over `𝒪̲_X`. -/
def chartBaseChangeSheafifyAdjunction :=
  Stacks.PresheafOfModules.ChangeOfRings.sheafifyChangeOfRingsAdjunction
    (J := topology Λ X structureMap) (evaluation.{u, u + 1} Λ X structureMap)
    (chartStructureRing Λ X structureMap).property

/-- The left adjoint `P ↦ (P^# ⊗_𝒪 π⁻¹𝒪_X)` read over `𝒪̲_X`, on presheaves of modules over the
affine functions: sheafification over `𝒪`, extension of scalars along `i♯`, and restriction of
scalars along `𝒪̲_X ≅ π⁻¹𝒪_X`. -/
def chartSheafifyBaseChangeAdjunction :=
  (PresheafOfModules.sheafificationAdjunction
      (Stacks.SheafOfModules.toAssociatedRingSheaf (topology Λ X structureMap)
        (affinePresheaf.{u, u + 1} Λ X structureMap))).comp
    ((SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
        (F := 𝟭 (PolynomialChart Λ X structureMap))
        (horizontalSiteHom Λ X structureMap).fSharpRing).comp
      (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
        (chartStructureRingIso Λ X structureMap)).toAdjunction)


/-- The scalar action of the affine functions of a chart on a sheaf of `𝒪̲_X`-modules, through
`i♯` followed by `π⁻¹𝒪_X ≅ 𝒪̲_X`, is the one through evaluation. -/
theorem chartStructureRingIso_horizontalCoefficientMap_apply
    (P : (PolynomialChart Λ X structureMap)ᵒᵖ)
    (r : (affinePresheaf.{u, u + 1} Λ X structureMap).obj P) :
    (chartStructureRingIso Λ X structureMap).hom.hom.app P
        ((horizontalSiteHom Λ X structureMap).fSharpRing.hom.app P
          ((Stacks.SheafOfModules.toAssociatedRingSheaf (topology Λ X structureMap)
            (affinePresheaf.{u, u + 1} Λ X structureMap)).app P r)) =
      (evaluation.{u, u + 1} Λ X structureMap).app P r := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_comp_horizontalCoefficientMap Λ X structureMap) P) r
  have h' := sheaf_iso_hom_inv_app_apply
    (restrictionIso.{u, u + 1} Λ X structureMap).symm P
      ((evaluation.{u, u + 1} Λ X structureMap).app P r)
  exact (congrArg ((restrictionIso.{u, u + 1} Λ X structureMap).hom.hom.app P) h).trans h'

/-- Restriction of a sheaf of `𝒪̲_X`-modules to the affine functions through `π⁻¹𝒪_X` and `𝒪`. -/
abbrev chartRestrictThroughAffine :
    SheafOfModules.{u + 1} (chartStructureRing Λ X structureMap) ⥤
      Stacks.PresheafOfModules.ChangeOfRings.PMod (affinePresheaf.{u, u + 1} Λ X structureMap) :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (chartStructureRingIso Λ X structureMap)).inverse ⋙
    SheafOfModules.pushforward.{u + 1} (F := 𝟭 (PolynomialChart Λ X structureMap))
      (horizontalSiteHom Λ X structureMap).fSharpRing ⋙
    SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
      (Stacks.SheafOfModules.toAssociatedRingSheaf (topology Λ X structureMap)
        (affinePresheaf.{u, u + 1} Λ X structureMap))

/-- Restriction of a sheaf of `𝒪̲_X`-modules to the affine functions along evaluation. -/
abbrev chartRestrictAlongEvaluation :
    SheafOfModules.{u + 1} (chartStructureRing Λ X structureMap) ⥤
      Stacks.PresheafOfModules.ChangeOfRings.PMod (affinePresheaf.{u, u + 1} Λ X structureMap) :=
  (SheafOfModules.forget (chartStructureRing Λ X structureMap) ⋙
      PresheafOfModules.restrictScalars (𝟙 _)) ⋙
    Stacks.PresheafOfModules.ChangeOfRings.restrictScalars
      (evaluation.{u, u + 1} Λ X structureMap)

/-- The two restrictions agree, by `chartStructureRingIso_horizontalCoefficientMap_apply`; the
isomorphism is the identity on sections. -/
def chartRestrictScalarsIso :
    chartRestrictThroughAffine Λ X structureMap ≅ chartRestrictAlongEvaluation Λ X structureMap :=
  NatIso.ofComponents (fun G => PresheafOfModules.isoMk (fun P =>
      (ModuleCat.restrictScalars _).mapIso
          (ModuleCat.restrictScalarsComp'App _ _ _ rfl (G.val.obj P)).symm ≪≫
        (ModuleCat.restrictScalarsComp'App _ _ _ rfl (G.val.obj P)).symm ≪≫
        (ModuleCat.restrictScalarsCongr (by
          ext r
          exact chartStructureRingIso_horizontalCoefficientMap_apply Λ X structureMap P r)).app
          (G.val.obj P) ≪≫
        ModuleCat.restrictScalarsComp'App _ _ _ rfl (G.val.obj P))
      (fun _ _ _ => rfl)) (fun _ => by ext; rfl)

/-- The two left adjoints agree, being left adjoint to the same restriction of scalars. -/
def chartBaseChangeSheafifyIso :=
  Adjunction.leftAdjointUniq (chartBaseChangeSheafifyAdjunction Λ X structureMap)
    ((chartSheafifyBaseChangeAdjunction Λ X structureMap).ofNatIsoRight
      (chartRestrictScalarsIso Λ X structureMap))

/-- **`Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` is the sheafification of `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}`**,
as a sheaf of `𝒪̲_X`-modules. By Tag 08TP `Ω_{𝒪/Λ̲}` is the sheafification of the objectwise
Kähler differentials, and extension of scalars commutes with sheafification. -/
def chartBaseChangePresheafSheafifyIso :
    (PresheafOfModules.sheafification (𝟙 (chartStructureRing Λ X structureMap).obj)).obj
        (chartBaseChangePresheaf Λ X structureMap) ≅
      chartDifferentialsBaseChangeRestricted Λ X structureMap :=
  have := CategoryTheory.Sheaf.wEqualsLocallyBijective_commRingCat.{u + 1, u, u + 1}
    (topology Λ X structureMap)
  (chartBaseChangeSheafifyIso Λ X structureMap).app
      (AlgebraicGeometry.SheafOfModules.objectwiseRelativeDifferentials.{u, u}
        (basePresheafMap.{u, u + 1} Λ X structureMap)) ≪≫
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (chartStructureRingIso Λ X structureMap)).functor.mapIso
      ((SheafOfModules.pullback.{u + 1} (F := 𝟭 (PolynomialChart Λ X structureMap))
        (horizontalSiteHom Λ X structureMap).fSharpRing).mapIso
          (AlgebraicGeometry.SheafOfModules.differentialsSheafificationIso.{u, u}
            (topology Λ X structureMap) _ _ (basePresheafMap.{u, u + 1} Λ X structureMap)).symm)


/-- The canonical map from `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}` to the sections of
`Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`, the transpose of `chartBaseChangePresheafSheafifyIso`. -/
def chartBaseChangePresheafMap :
    chartBaseChangePresheaf Λ X structureMap ⟶
      (PresheafOfModules.restrictScalars (𝟙 (chartStructureRing Λ X structureMap).obj)).obj
        (chartDifferentialsBaseChangeRestricted Λ X structureMap).val :=
  PresheafOfModules.sheafificationHomEquiv _
    (chartBaseChangePresheafSheafifyIso Λ X structureMap).hom

/-- **The canonical map is inverted by sheafification**: on underlying presheaves of abelian
groups it is the sheafification unit followed by an isomorphism. -/
theorem W_chartBaseChangePresheafMap :
    (topology Λ X structureMap).W
      ((PresheafOfModules.toPresheaf _).map (chartBaseChangePresheafMap Λ X structureMap)) := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (α := 𝟙 (chartStructureRing Λ X structureMap).obj)
    (chartBaseChangePresheafSheafifyIso Λ X structureMap).hom
  refine (congrArg (fun g => (topology Λ X structureMap).W g) h).mpr ?_
  let e := (PresheafOfModules.toPresheaf (chartStructureRing Λ X structureMap).obj).mapIso
    ((SheafOfModules.forget _).mapIso (chartBaseChangePresheafSheafifyIso Λ X structureMap))
  exact MorphismProperty.comp_mem _ _ _ ((topology Λ X structureMap).W_toSheafify _)
    (ObjectProperty.isLocal_of_isIso _ e.hom)


end AlgebraicGeometry.PolynomialChart
