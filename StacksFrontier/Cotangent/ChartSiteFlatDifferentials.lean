module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ObjectwiseFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionFactsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsSheafification
public import StacksFrontier.Cotangent.ChartSiteHorizontalDerivedPullback
public import StacksFrontier.Cotangent.DirectedColimit
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteDifferentials
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafification

/-!
# The differentials on the site of polynomial charts are flat

Let `Λ` be a ring and `X` a scheme over `Λ`, and let `C_{X/Λ}` be the site of polynomial charts
of Tag 08VA, with its sheaf of affine functions `𝒪`, the constant sheaf `Λ̲` and the horizontal
arrow `i : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(C_{X/Λ}), 𝒪)` with structure map `i♯ : 𝒪 ⟶ π⁻¹𝒪_X`.
Tag 08T9 identifies the cotangent complex of `X` over `Λ` with

`Lπ_!(Li^*Ω_{𝒪/Λ̲}) = Lπ_!(i^*Ω_{𝒪/Λ̲}) = Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X)`.

This file proves the two equalities on the right, before `Lπ_!` is applied.

The first holds because `Ω_{𝒪/Λ̲}` is flat. The source's reason is that every value of `𝒪`
is a polynomial algebra over `Λ`: `𝒪` is the sheafification of `(U ⟶ A) ↦ Γ(A, 𝒪_A)` and
`Γ(A, 𝒪_A)` is a polynomial algebra, so by Tag 08TP `Ω_{𝒪/Λ̲}` is the sheafification of the
presheaf `(U ⟶ A) ↦ Ω_{Γ(A, 𝒪_A)/Λ}` of free modules, and the sheafification of a flat
presheaf of modules is flat (Tag 03ET). A flat module placed in degree zero is K-flat with
flat terms, and on such a complex the comparison `Li^* ⟶ i^*` of Tag 06YY is invertible.

The second holds because the module pullback along `i` is extension of scalars along `i♯`:
both are left adjoints of `i_*`, which is restriction of scalars along `i♯`.

## Main definitions

* `AlgebraicGeometry.PolynomialChart.affineSectionsAlgEquiv`: the ring of functions on the
  affine space of a chart is the polynomial algebra presenting it, as a `Λ`-algebra.
* `AlgebraicGeometry.PolynomialChart.chartDifferentialsBaseChange`: `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`,
  the image of `Ω_{𝒪/Λ̲}` under Mathlib's `SheafOfModules.pullback` along the identity functor
  of the chart site at the ring map `i♯`, that is under the left adjoint of restriction of
  scalars along `i♯`.

## Main results

* `AlgebraicGeometry.PolynomialChart.isFlat_chartDifferentials`: `Ω_{𝒪/Λ̲}` is a flat sheaf
  of `𝒪`-modules.
* `AlgebraicGeometry.PolynomialChart.derivedHorizontalInverseImageDifferentialsIso`:
  `Li^*Ω_{𝒪/Λ̲} ≅ i^*Ω_{𝒪/Λ̲}` in `D(π⁻¹𝒪_X)`.
* `AlgebraicGeometry.PolynomialChart.horizontalModuleInverseImageIsoPullback`: `i^*` is
  extension of scalars along `i♯`.
* `AlgebraicGeometry.PolynomialChart.pulledBackDifferentialsIsoBaseChange`:
  `i^*Ω_{𝒪/Λ̲} ≅ Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`.
* `AlgebraicGeometry.PolynomialChart.chartDifferentialsBaseChangeIsoExtendScalars`:
  `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` is the sheafification of the sectionwise tensor product
  `U ↦ π⁻¹𝒪_X(U) ⊗_{𝒪(U)} Ω_{𝒪/Λ̲}(U)`.

## Implementation notes

The flatness statement is at the free coefficient universe `max w (u + 1)` of Tag 08VA; the
derived and base-change statements are at `u + 1`, the universe of `Li^*` in
`StacksFrontier/Cotangent/ChartSiteHorizontalDerivedPullback.lean`. The comparison `Li^* ⟶ i^*` is
the counit of the total left derived functor, and it is invertible on the K-flat complexes with
flat terms by the resolution and exactness halves of Tag 06YY for a morphism of ringed topoi,
which hold at the universes of the chart site itself, with no passage to its small model.

The structure map of `SheafOfModules.pullback` is the structure map of
`AlgebraicGeometry.PolynomialChart.horizontalSiteHom`, read over the identity functor of the chart
site, which is written out so that its continuity is found by instance search.

## References

* [Stacks Project, Tag 08T9](https://stacks.math.columbia.edu/tag/08T9)
* [Stacks Project, Tag 08VA](https://stacks.math.columbia.edu/tag/08VA)
* [Stacks Project, Tag 08TP](https://stacks.math.columbia.edu/tag/08TP)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
    (structureMap : X ⟶ Spec (CommRingCat.of Λ))

attribute [local instance] hasSheafify_addCommGrpCat_topology wEqualsLocallyBijective_topology

/-- The ring of functions on the affine space of a chart is the polynomial algebra it is
presented by, as an algebra over `Λ` through the structure map of the chart. -/
def affineSectionsAlgEquiv (P : PolynomialChart Λ X structureMap) :
    letI : Algebra Λ ((affineSectionsPresheaf Λ X structureMap).obj (Opposite.op P)) :=
      RingHom.toAlgebra (((baseSectionsMap Λ X structureMap).app (Opposite.op P)).hom :)
    (affineSectionsPresheaf Λ X structureMap).obj (Opposite.op P) ≃ₐ[Λ]
      MvPolynomial P.variableIndex Λ :=
  letI : Algebra Λ ((affineSectionsPresheaf Λ X structureMap).obj (Opposite.op P)) :=
    RingHom.toAlgebra (((baseSectionsMap Λ X structureMap).app (Opposite.op P)).hom :)
  AlgEquiv.ofRingEquiv
    (f := (({ hom := P.affineEquiv.inv.appTop
              inv := P.affineEquiv.hom.appTop
              hom_inv_id := by
                rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
              inv_hom_id := by
                rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop] } :
            Γ(P.affineSpace, ⊤) ≅
              Γ(Spec (CommRingCat.of (MvPolynomial P.variableIndex Λ)), ⊤)) ≪≫
      Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial P.variableIndex Λ))).commRingCatIsoToRingEquiv)
    (fun x => by
      have hc : P.affineEquiv.hom.appTop ≫ P.affineEquiv.inv.appTop = 𝟙 _ := by
        rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
      have key : (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
          (Spec.map (CommRingCat.ofHom
            (MvPolynomial.C : Λ →+* MvPolynomial P.variableIndex Λ))).appTop ≫
            P.affineEquiv.hom.appTop ≫ P.affineEquiv.inv.appTop ≫
              (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial P.variableIndex Λ))).hom =
          CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial P.variableIndex Λ) := by
        rw [reassoc_of% hc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
      exact ConcreteCategory.congr_hom key x)

/-- **`Ω_{𝒪/Λ̲}` is a flat sheaf of `𝒪`-modules**. By Tag 08TP it is the sheafification of
`(U ⟶ A) ↦ Ω_{Γ(A, 𝒪_A)/Λ}`, whose values are free because `Γ(A, 𝒪_A)` is a polynomial algebra
over `Λ`, and a sheafified flat presheaf is flat. -/
theorem isFlat_chartDifferentials :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := affineSheaf.{u, w} Λ X structureMap)
      (chartDifferentials.{u, w} Λ X structureMap) := by
  have := CategoryTheory.Sheaf.wEqualsLocallyBijective_commRingCat.{u + 1, u, w}
    (topology Λ X structureMap)
  refine Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize
    (affineSheaf.{u, w} Λ X structureMap)
    (AlgebraicGeometry.SheafOfModules.differentialsSheafificationIso.{u, u}
      (topology Λ X structureMap) _ _ (basePresheafMap.{u, w} Λ X structureMap)).symm ?_
  refine Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification
    (topology Λ X structureMap) _ _ ?_
  refine AlgebraicGeometry.SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat _
    (fun P => ?_)
  let : Algebra Λ ((affineSectionsPresheaf Λ X structureMap).obj P) :=
    RingHom.toAlgebra (((baseSectionsMap Λ X structureMap).app P).hom :)
  have := KaehlerDifferential.flat_ulift_of_free.{u, max w (u + 1)} Λ
    ((affineSectionsPresheaf Λ X structureMap).obj P) (.of_basis
      (KaehlerDifferential.basisOfMvPolynomialAlgEquiv
        (affineSectionsAlgEquiv Λ X structureMap P.unop)))
  have : Module.Flat ((Stacks.ringPresheaf (affinePresheaf.{u, w} Λ X structureMap)).obj P)
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
        (basePresheafMap.{u, w} Λ X structureMap)).obj P) := this
  exact Module.Flat.of_linearEquiv ULift.moduleEquiv

/-! ### `Li^*Ω_{𝒪/Λ̲} = i^*Ω_{𝒪/Λ̲}` -/

section Derived

attribute [local instance] HasDerivedCategory.standard
  hasSheafify_addCommGrpCat_topology_succ wEqualsLocallyBijective_topology_succ
  horizontalModuleInverseImage_additive hasLeftDerivedFunctor_horizontalModuleInverseImage
  Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize

/-- `Ω_{𝒪/Λ̲}`, placed in degree zero, is a K-flat complex with flat terms: its one nonzero term
is flat by `isFlat_chartDifferentials`, and a flat module in a single degree is K-flat. -/
theorem isKFlat_singleChartDifferentials :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := ⟨PolynomialChart Λ X structureMap, topology Λ X structureMap,
        affineSheaf.{u, u + 1} Λ X structureMap⟩)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (chartDifferentials.{u, u + 1} Λ X structureMap))) := by
  have hf := isFlat_chartDifferentials.{u, u + 1} Λ X structureMap
  refine ⟨Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat_ofSize _ _ hf 0,
    fun i => ?_⟩
  obtain rfl | h := eq_or_ne i 0
  · exact Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize
      (affineSheaf.{u, u + 1} Λ X structureMap)
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm hf
  · exact Stacks.SheafOfModules.KFlatOfSize.isFlat_of_isZero_ofSize _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i h)

/-- The comparison `Li^* ⟶ i^*` of the total left derived functor with degreewise `i^*` is
invertible at `Ω_{𝒪/Λ̲}[0]`. -/
theorem isIso_totalLeftDerivedCounit_singleChartDifferentials :
    IsIso ((((horizontalModuleInverseImage.{u, u + 1} Λ X structureMap).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (chartDifferentials.{u, u + 1} Λ X structureMap)))) := by
  have := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (horizontalHom.{u, u + 1} Λ X structureMap)
  exact Stacks.Cohomology.DerivedPullbackOfToposHom.isIso_derivedPullbackComparison_app
    (horizontalHom.{u, u + 1} Λ X structureMap)
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := ⟨PolynomialChart Λ X structureMap, topology Λ X structureMap,
        affineSheaf.{u, u + 1} Λ X structureMap⟩))
    (fun N ↦ by
      obtain ⟨K, hK, t, ht⟩ :=
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat N
      exact ⟨K, hK, t, ht⟩)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat
      (horizontalHom.{u, u + 1} Λ X structureMap)) _
    (isKFlat_singleChartDifferentials Λ X structureMap)

/-- **`Li^*Ω_{𝒪/Λ̲} = i^*Ω_{𝒪/Λ̲}`**, the middle identification of Tag 08T9: on the chart site
the total left derived functor of the module pullback along the horizontal arrow, evaluated at
`Ω_{𝒪/Λ̲}` in degree zero, is the underived pullback in degree zero. This is the comparison
`Li^* ⟶ i^*` at the K-flat complex `Ω_{𝒪/Λ̲}[0]`, read between the two single-degree
embeddings. -/
def derivedHorizontalInverseImageDifferentialsIso :
    (derivedHorizontalInverseImage Λ X structureMap).obj
        ((DerivedCategory.singleFunctor _ 0).obj (chartDifferentials.{u, u + 1} Λ X structureMap)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (pulledBackDifferentials.{u, u + 1} Λ X structureMap) :=
  (derivedHorizontalInverseImage Λ X structureMap).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
        ((DerivedCategory.quotientCompQhIso _).app _).symm) ≪≫
    @asIso _ _ _ _ _ (isIso_totalLeftDerivedCounit_singleChartDifferentials Λ X structureMap) ≪≫
    DerivedCategory.Qh.mapIso
      (((horizontalModuleInverseImage.{u, u + 1} Λ X structureMap).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app _) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (horizontalModuleInverseImage.{u, u + 1} Λ X structureMap) (ComplexShape.up ℤ) 0).app _) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm

end Derived

/-! ### `i^*Ω_{𝒪/Λ̲} = Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` -/

section BaseChange

attribute [local instance] hasSheafify_addCommGrpCat_topology_succ
  wEqualsLocallyBijective_topology_succ

/-- Restriction of scalars along `i♯ : 𝒪 ⟶ π⁻¹𝒪_X` is a right adjoint: it is the direct image
`i_*` of sheaves of modules along the horizontal arrow of Tag 08VA, whose left adjoint is
`i^*`. -/
theorem isRightAdjoint_pushforward_horizontalSiteHom_fSharpRing :
    (SheafOfModules.pushforward.{u + 1} (F := 𝟭 (PolynomialChart Λ X structureMap))
      (horizontalSiteHom Λ X structureMap).fSharpRing).IsRightAdjoint := by
  have := (RingedToposHom.pullbackAdjPushforwardModules
    (horizontalHom.{u, u + 1} Λ X structureMap)).isRightAdjoint
  exact Functor.isRightAdjoint_of_iso (horizontalPushforwardModulesIso Λ X structureMap)

attribute [local instance] isRightAdjoint_pushforward_horizontalSiteHom_fSharpRing

/-- `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`: the differentials of the affine-functions sheaf, with scalars extended
along `i♯ : 𝒪 ⟶ π⁻¹𝒪_X`, that is their image under the left adjoint of restriction of scalars
along `i♯`. -/
def chartDifferentialsBaseChange :
    SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (chartStructureSheaf.{u, u + 1} Λ X structureMap)) :=
  (SheafOfModules.pullback.{u + 1} (F := 𝟭 (PolynomialChart Λ X structureMap))
      (horizontalSiteHom Λ X structureMap).fSharpRing).obj
    (chartDifferentials.{u, u + 1} Λ X structureMap)

/-- **`i^*` is extension of scalars along `i♯`.** The module pullback along the horizontal arrow
of Tag 08VA and the left adjoint of restriction of scalars along `i♯` are both left adjoints of
`i_*`, which is restriction of scalars along `i♯` by `horizontalPushforwardModulesIso`. -/
def horizontalModuleInverseImageIsoPullback :
    horizontalModuleInverseImage.{u, u + 1} Λ X structureMap ≅
      SheafOfModules.pullback.{u + 1} (F := 𝟭 (PolynomialChart Λ X structureMap))
        (horizontalSiteHom Λ X structureMap).fSharpRing :=
  Adjunction.leftAdjointUniq
    ((RingedToposHom.pullbackAdjPushforwardModules
      (horizontalHom.{u, u + 1} Λ X structureMap)).ofNatIsoRight
        (horizontalPushforwardModulesIso Λ X structureMap))
    (SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
      (F := 𝟭 (PolynomialChart Λ X structureMap))
      (horizontalSiteHom Λ X structureMap).fSharpRing)

/-- **`i^*Ω_{𝒪/Λ̲} = Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`**, the last identification of Tag 08T9. -/
def pulledBackDifferentialsIsoBaseChange :
    pulledBackDifferentials.{u, u + 1} Λ X structureMap ≅
      chartDifferentialsBaseChange Λ X structureMap :=
  (horizontalModuleInverseImageIsoPullback Λ X structureMap).app
    (chartDifferentials.{u, u + 1} Λ X structureMap)

/-- **`Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` is a sheafified tensor product.** It is the sheaf associated to the
presheaf `U ↦ π⁻¹𝒪_X(U) ⊗_{𝒪(U)} Ω_{𝒪/Λ̲}(U)`, the extension of scalars of Tag 03CZ. -/
def chartDifferentialsBaseChangeIsoExtendScalars :
    chartDifferentialsBaseChange Λ X structureMap ≅
      (Stacks.Sheaves.RingedToposModules.extendScalars (topology Λ X structureMap)
        (horizontalCoefficientMap Λ X structureMap).hom
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineSheaf.{u, u + 1} Λ X structureMap)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (chartStructureSheaf.{u, u + 1} Λ X structureMap)).property).obj
        (chartDifferentials.{u, u + 1} Λ X structureMap) :=
  (Adjunction.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
      (F := 𝟭 (PolynomialChart Λ X structureMap))
      (horizontalSiteHom Λ X structureMap).fSharpRing)
    (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
      (topology Λ X structureMap) (horizontalCoefficientMap Λ X structureMap).hom
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineSheaf.{u, u + 1} Λ X structureMap)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (chartStructureSheaf.{u, u + 1} Λ X structureMap)).property)).app
    (chartDifferentials.{u, u + 1} Λ X structureMap)

end BaseChange

end AlgebraicGeometry.PolynomialChart

end
