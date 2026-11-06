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
public import StacksFrontier.Cotangent.Spaces.ChartSiteHorizontalDerivedPullback
public import StacksFrontier.Cotangent.DirectedColimit
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteDifferentials
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafification

/-!
# The differentials on the site of polynomial charts of an algebraic space are flat

Let `Λ` be a ring and `X` an algebraic space over `Λ`, and let `C_{X/Λ}` be the site of
polynomial charts of Tag 08VK, with its sheaf of affine functions `𝒪`, the constant sheaf `Λ̲`
and the horizontal arrow `i : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(C_{X/Λ}), 𝒪)` with structure map
`i♯ : 𝒪 ⟶ π⁻¹𝒪_X`. Tag 08VM identifies the cotangent complex of `X` over `Λ` with

`Lπ_!(Li^*Ω_{𝒪/Λ̲}) = Lπ_!(i^*Ω_{𝒪/Λ̲}) = Lπ_!(Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X)`.

This file proves the two equalities on the right, before `Lπ_!` is applied.

The first holds because `Ω_{𝒪/Λ̲}` is flat: `𝒪` is the sheafification of `(U ⟶ A) ↦ Γ(A, 𝒪_A)`
and `Γ(A, 𝒪_A)` is a polynomial algebra, so by Tag 08TP `Ω_{𝒪/Λ̲}` is the sheafification of the
presheaf `(U ⟶ A) ↦ Ω_{Γ(A, 𝒪_A)/Λ}` of free modules, and the sheafification of a flat presheaf
of modules is flat (Tag 03ET). A flat module placed in degree zero is K-flat with flat terms, and
on such a complex the comparison `Li^* ⟶ i^*` of Tag 06YY is invertible.

The second holds because the module pullback along `i` is extension of scalars along `i♯`: both
are left adjoints of `i_*`, which is restriction of scalars along `i♯`.

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart.affineSectionsAlgEquiv`: the ring of functions on the
  affine space of a chart is the polynomial algebra presenting it, as a `Λ`-algebra.
* `AlgebraicGeometry.Space.PolynomialChart.chartDifferentialsBaseChange`:
  `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`, the image of `Ω_{𝒪/Λ̲}` under Mathlib's `SheafOfModules.pullback` along
  the identity functor of the chart site at the ring map `i♯`, that is under the left adjoint of
  restriction of scalars along `i♯`.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.isFlat_chartDifferentials`: `Ω_{𝒪/Λ̲}` is a flat
  sheaf of `𝒪`-modules.
* `AlgebraicGeometry.Space.PolynomialChart.derivedHorizontalInverseImageDifferentialsIso`:
  `Li^*Ω_{𝒪/Λ̲} ≅ i^*Ω_{𝒪/Λ̲}` in `D(π⁻¹𝒪_X)`.
* `AlgebraicGeometry.Space.PolynomialChart.horizontalModuleInverseImageIsoPullback`: `i^*` is
  extension of scalars along `i♯`.
* `AlgebraicGeometry.Space.PolynomialChart.pulledBackDifferentialsIsoBaseChange`:
  `i^*Ω_{𝒪/Λ̲} ≅ Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`.
* `AlgebraicGeometry.Space.PolynomialChart.chartDifferentialsBaseChangeIsoExtendScalars`:
  `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` is the sheafification of the sectionwise tensor product
  `U ↦ π⁻¹𝒪_X(U) ⊗_{𝒪(U)} Ω_{𝒪/Λ̲}(U)`.

## Implementation notes

All statements are in the coefficient universe `u + 1` of the chart site. The comparison
`Li^* ⟶ i^*` is the counit of the total left derived functor, and it is invertible on the
K-flat complexes with flat terms by the resolution and exactness halves of Tag 06YY for a
morphism of ringed topoi, which hold at the universes of the chart site itself, with no passage
to its small model.

The structure map of `SheafOfModules.pullback` is the structure map of
`AlgebraicGeometry.Space.PolynomialChart.horizontalSiteHom`, read over the identity functor of
the chart site, which is written out so that its continuity is found by instance search.

## References

* [Stacks Project, Tag 08VM](https://stacks.math.columbia.edu/tag/08VM)
* [Stacks Project, Tag 08VK](https://stacks.math.columbia.edu/tag/08VK)
* [Stacks Project, Tag 08TP](https://stacks.math.columbia.edu/tag/08TP)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

attribute [-instance] CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

attribute [local instance] hasSheafify_addCommGrpCat_topology wEqualsLocallyBijective_topology

/-- The ring of functions on the affine space of a chart is the polynomial algebra it is
presented by, as an algebra over `Λ` through the structure map of the chart. -/
def affineSectionsAlgEquiv (P : PolynomialChart Λ B hS X hX) :
    letI : Algebra Λ ((affinePresheaf Λ B hS X hX).obj (Opposite.op P)) :=
      RingHom.toAlgebra (((basePresheafMap Λ B hS X hX).app (Opposite.op P)).hom :)
    (affinePresheaf Λ B hS X hX).obj (Opposite.op P) ≃ₐ[Λ]
      MvPolynomial P.variableIndex Λ :=
  letI : Algebra Λ ((affinePresheaf Λ B hS X hX).obj (Opposite.op P)) :=
    RingHom.toAlgebra (((basePresheafMap Λ B hS X hX).app (Opposite.op P)).hom :)
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

/-- **`Ω_{𝒪/Λ̲}` is a flat sheaf of `𝒪`-modules**, the flatness on which Tag 08VM rests. By
Tag 08TP it is the sheafification of `(U ⟶ A) ↦ Ω_{Γ(A, 𝒪_A)/Λ}`, whose values are free because
`Γ(A, 𝒪_A)` is a polynomial algebra over `Λ`, and a sheafified flat presheaf is flat. -/
theorem isFlat_chartDifferentials :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := liftedAffineSheaf Λ B hS X hX)
      (chartDifferentials Λ B hS X hX) := by
  have := CategoryTheory.Sheaf.wEqualsLocallyBijective_commRingCat.{u + 1, u, u + 1}
    (topology Λ B hS X hX)
  refine Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize
    (liftedAffineSheaf Λ B hS X hX)
    (AlgebraicGeometry.SheafOfModules.differentialsSheafificationIso.{u, u}
      (topology Λ B hS X hX) _ _ (liftedBasePresheafMap Λ B hS X hX)).symm ?_
  refine Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification
    (topology Λ B hS X hX) (O := liftedAffinePresheaf Λ B hS X hX)
      (Osharp := liftedAffineSheaf Λ B hS X hX)
    _ _ ?_
  refine AlgebraicGeometry.SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat _
    (fun P => ?_)
  let : Algebra Λ ((affinePresheaf Λ B hS X hX).obj P) :=
    RingHom.toAlgebra (((basePresheafMap Λ B hS X hX).app P).hom :)
  have hfree : Module.Free ((affinePresheaf Λ B hS X hX).obj P)
      Ω[(affinePresheaf Λ B hS X hX).obj P⁄Λ] :=
    Module.Free.of_basis
      (KaehlerDifferential.basisOfMvPolynomialAlgEquiv
        (affineSectionsAlgEquiv Λ B hS X hX P.unop))
  have := KaehlerDifferential.flat_ulift_of_free.{u, u + 1} Λ
    ((affinePresheaf Λ B hS X hX).obj P) hfree
  have : Module.Flat ((Stacks.ringPresheaf (liftedAffinePresheaf Λ B hS X hX)).obj P)
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
        (liftedBasePresheafMap Λ B hS X hX)).obj P) := this
  exact Module.Flat.of_linearEquiv ULift.moduleEquiv

/-! ### `Li^*Ω_{𝒪/Λ̲} = i^*Ω_{𝒪/Λ̲}` -/

section Derived

attribute [local instance] HasDerivedCategory.standard
  hasSheafify_addCommGrpCat_topology wEqualsLocallyBijective_topology
  horizontalModuleInverseImage_additive hasLeftDerivedFunctor_horizontalModuleInverseImage
  Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize

/-- `Ω_{𝒪/Λ̲}`, placed in degree zero, is a K-flat complex with flat terms: its one nonzero term
is flat by `isFlat_chartDifferentials`, and a flat module in a single degree is K-flat. -/
theorem isKFlat_singleChartDifferentials :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := ⟨PolynomialChart Λ B hS X hX, topology Λ B hS X hX,
        liftedAffineSheaf Λ B hS X hX⟩)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (chartDifferentials Λ B hS X hX))) := by
  refine ⟨Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat_ofSize _ _
    (isFlat_chartDifferentials Λ B hS X hX) 0, fun i => ?_⟩
  by_cases h : i = 0
  · subst h
    exact Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize
      (liftedAffineSheaf Λ B hS X hX)
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm
      (isFlat_chartDifferentials Λ B hS X hX)
  · exact Stacks.SheafOfModules.KFlatOfSize.isFlat_of_isZero_ofSize _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i h)

/-- The comparison `Li^* ⟶ i^*` of the total left derived functor with degreewise `i^*` is
invertible at `Ω_{𝒪/Λ̲}[0]`. -/
theorem isIso_totalLeftDerivedCounit_singleChartDifferentials :
    IsIso ((((horizontalModuleInverseImage Λ B hS X hX).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (chartDifferentials Λ B hS X hX)))) := by
  have := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (liftedHorizontalHom Λ B hS X hX)
  exact Stacks.Cohomology.DerivedPullbackOfToposHom.isIso_derivedPullbackComparison_app
    (liftedHorizontalHom Λ B hS X hX)
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := ⟨PolynomialChart Λ B hS X hX, topology Λ B hS X hX,
        liftedAffineSheaf Λ B hS X hX⟩))
    (fun N ↦ by
      obtain ⟨K, hK, t, ht⟩ :=
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat N
      exact ⟨K, hK, t, ht⟩)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat
      (liftedHorizontalHom Λ B hS X hX)) _
    (isKFlat_singleChartDifferentials Λ B hS X hX)

/-- **`Li^*Ω_{𝒪/Λ̲} = i^*Ω_{𝒪/Λ̲}`**, the middle identification of Tag 08VM: on the chart site
the total left derived functor of the module pullback along the horizontal arrow, evaluated at
`Ω_{𝒪/Λ̲}` in degree zero, is the underived pullback in degree zero. This is the comparison
`Li^* ⟶ i^*` at the K-flat complex `Ω_{𝒪/Λ̲}[0]`, read between the two single-degree
embeddings. -/
def derivedHorizontalInverseImageDifferentialsIso :
    (derivedHorizontalInverseImage Λ B hS X hX).obj
        ((DerivedCategory.singleFunctor _ 0).obj (chartDifferentials Λ B hS X hX)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (pulledBackDifferentials Λ B hS X hX) :=
  (derivedHorizontalInverseImage Λ B hS X hX).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
        ((DerivedCategory.quotientCompQhIso _).app _).symm) ≪≫
    @asIso _ _ _ _ _ (isIso_totalLeftDerivedCounit_singleChartDifferentials Λ B hS X hX) ≪≫
    DerivedCategory.Qh.mapIso
      (((horizontalModuleInverseImage Λ B hS X hX).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app _) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (horizontalModuleInverseImage Λ B hS X hX) (ComplexShape.up ℤ) 0).app _) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm

end Derived

/-! ### `i^*Ω_{𝒪/Λ̲} = Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` -/

section BaseChange

attribute [local instance] hasSheafify_addCommGrpCat_topology
  wEqualsLocallyBijective_topology

/-- Restriction of scalars along `i♯ : 𝒪 ⟶ π⁻¹𝒪_X` is a right adjoint: it is the direct image
`i_*` of sheaves of modules along the horizontal arrow of Tag 08VK, whose left adjoint is
`i^*`. -/
theorem isRightAdjoint_pushforward_horizontalSiteHom_fSharpRing :
    (SheafOfModules.pushforward.{u + 1} (F := 𝟭 (PolynomialChart Λ B hS X hX))
      (horizontalSiteHom Λ B hS X hX).fSharpRing).IsRightAdjoint := by
  have := (RingedToposHom.pullbackAdjPushforwardModules
    (liftedHorizontalHom Λ B hS X hX)).isRightAdjoint
  exact Functor.isRightAdjoint_of_iso (horizontalPushforwardModulesIso Λ B hS X hX)

attribute [local instance] isRightAdjoint_pushforward_horizontalSiteHom_fSharpRing

/-- `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`: the differentials of the affine-functions sheaf, with scalars extended
along `i♯ : 𝒪 ⟶ π⁻¹𝒪_X`, that is their image under the left adjoint of restriction of scalars
along `i♯`. -/
def chartDifferentialsBaseChange :
    SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (chartStructureSheaf Λ B hS X hX)) :=
  (SheafOfModules.pullback.{u + 1} (F := 𝟭 (PolynomialChart Λ B hS X hX))
      (horizontalSiteHom Λ B hS X hX).fSharpRing).obj
    (chartDifferentials Λ B hS X hX)

/-- **`i^*` is extension of scalars along `i♯`.** The module pullback along the horizontal arrow
of Tag 08VK and the left adjoint of restriction of scalars along `i♯` are both left adjoints of
`i_*`, which is restriction of scalars along `i♯` by `horizontalPushforwardModulesIso`. -/
def horizontalModuleInverseImageIsoPullback :
    horizontalModuleInverseImage Λ B hS X hX ≅
      SheafOfModules.pullback.{u + 1} (F := 𝟭 (PolynomialChart Λ B hS X hX))
        (horizontalSiteHom Λ B hS X hX).fSharpRing :=
  Adjunction.leftAdjointUniq
    ((RingedToposHom.pullbackAdjPushforwardModules
      (liftedHorizontalHom Λ B hS X hX)).ofNatIsoRight
        (horizontalPushforwardModulesIso Λ B hS X hX))
    (SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
      (F := 𝟭 (PolynomialChart Λ B hS X hX))
      (horizontalSiteHom Λ B hS X hX).fSharpRing)

/-- **`i^*Ω_{𝒪/Λ̲} = Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`**, the last identification of Tag 08VM. -/
def pulledBackDifferentialsIsoBaseChange :
    pulledBackDifferentials Λ B hS X hX ≅
      chartDifferentialsBaseChange Λ B hS X hX :=
  (horizontalModuleInverseImageIsoPullback Λ B hS X hX).app
    (chartDifferentials Λ B hS X hX)

/-- **`Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` is a sheafified tensor product.** It is the sheaf associated to the
presheaf `U ↦ π⁻¹𝒪_X(U) ⊗_{𝒪(U)} Ω_{𝒪/Λ̲}(U)`, the extension of scalars of Tag 03CZ. -/
def chartDifferentialsBaseChangeIsoExtendScalars :
    chartDifferentialsBaseChange Λ B hS X hX ≅
      (Stacks.Sheaves.RingedToposModules.extendScalars (topology Λ B hS X hX)
        (horizontalCoefficientMap Λ B hS X hX).hom
        (Stacks.SheafOfModules.Tensor.ringSheaf (liftedAffineSheaf Λ B hS X hX)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (chartStructureSheaf Λ B hS X hX)).property).obj
        (chartDifferentials Λ B hS X hX) :=
  (Adjunction.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
      (F := 𝟭 (PolynomialChart Λ B hS X hX))
      (horizontalSiteHom Λ B hS X hX).fSharpRing)
    (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
      (topology Λ B hS X hX) (horizontalCoefficientMap Λ B hS X hX).hom
      (Stacks.SheafOfModules.Tensor.ringSheaf (liftedAffineSheaf Λ B hS X hX)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (chartStructureSheaf Λ B hS X hX)).property)).app
    (chartDifferentials Λ B hS X hX)

end BaseChange

end AlgebraicGeometry.Space.PolynomialChart

end
