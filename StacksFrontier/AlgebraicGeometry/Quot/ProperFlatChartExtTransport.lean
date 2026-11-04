module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartExtComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.ShiftedHomEquivalenceCoefficient

/-!
# `Ext^i(E, 𝒪_X ⊗ f^*M~) = Ext^i(L_{X/A}, 𝒪_X ⊗_A M)` at a chart of `Spaces'_{fp, flat, proper}`

Let `x` be a flat, proper, finitely presented algebraic space `f : X → Spec A`, and let
`T^i(M) = Ext^i(L_{X/A}, 𝒪_X ⊗_A M)` be the functors of [Stacks, Remark 0D1P], formed on the
`Type u` model of the small étale site of `X` (`AlgebraicGeometry.Space.cotangentExtFunctor`).
For `E ∈ D(𝒪_X)` on the small étale site itself and an isomorphism `ι : Φ(E) ≅ L_{X/A}`, `Φ` the
model equivalence on derived categories, this file identifies the groups
`Ext^i_{𝒪_X}(E, 𝒪_X ⊗ f^*M~)` of [Stacks, Tag 08JR]
(`AlgebraicGeometry.Space.tensorPullbackExtGroup` at `𝒢^• = 𝒪_X[0]`) with `T^i(M)`, naturally in
`M` and carrying the boundary map of 08JR to the connecting map
`AlgebraicGeometry.Space.ProperFlatLift.chartExtConnecting` of `T^•`.

## Main definitions

* `AlgebraicGeometry.Space.ProperFlatLift.chartExtTransport`: the isomorphism
  `Ext^i_{𝒪_X}(E, 𝒪_X ⊗ f^*M~) ≃+ T^i(M)` determined by `ι`.

## Main results

* `AlgebraicGeometry.Space.ProperFlatLift.chartExtTransport_naturality`: `chartExtTransport` is
  natural in `M`.
* `AlgebraicGeometry.Space.ProperFlatLift.chartExtTransport_delta`: `chartExtTransport` carries
  the boundary map of 08JR to the connecting map of `T^•`.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
-- `AlgebraicGeometry.Space.tensorPullbackExtGroup` and
-- `AlgebraicGeometry.Space.tensorPullbackComplexDerived` are stated in the model
-- `HasDerivedCategory.standard`.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleRingedTopos

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)

attribute [local instance high] smallEtaleModules_abelian

/-- The coefficient functor `M ↦ 𝒪_X[0] ⊗ f^*(M~[0])` of 08JR at a chart. -/
abbrev chartCoefficientFunctor :
    ModuleCat.{u} A ⥤ CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS x.obj.obj.left)) ℤ :=
  affineBaseTilde A B S hS toS hA ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙
    tensorPullbackComplex (chartStructureMap x hx) (structureSingleComplex x.obj.obj.left)

/-- `chartCoefficientIso` as an isomorphism of functors. -/
def chartCoefficientNatIso :
    chartCoefficientFunctor x hx ≅ chartTensorModule x hx ⋙
      HomologicalComplex.single _ (ComplexShape.up ℤ) 0 :=
  NatIso.ofComponents (chartCoefficientIso x hx)
    (fun g => chartCoefficientIso_hom_naturality x hx g)

/-- The model equivalence `Mod(𝒪_X) ≌ Mod(𝒪_model)`, as a functor into the coefficients of
`AlgebraicGeometry.Space.cotangentExtFunctor`. -/
abbrev chartModelFunctor :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS x.obj.obj.left) ⥤
      modelModules x.obj.obj.left :=
  (smallEtaleModelModulesEquiv B S hS x.obj.obj.left).functor

/-- `chartModelFunctor x` is an equivalence of categories. -/
instance isEquivalence_chartModelFunctor : (chartModelFunctor x).IsEquivalence :=
  inferInstanceAs (smallEtaleModelModulesEquiv B S hS x.obj.obj.left).functor.IsEquivalence

/-- `chartModelFunctor x` is additive. -/
instance additive_chartModelFunctor : (chartModelFunctor x).Additive :=
  Functor.additive_of_isEquivalence _

/-- The isomorphism `Φ(𝒪_X ⊗_A M) ≅ 𝒪_X ⊗_A M` on the model: the counit of the model equivalence,
the module `𝒪_X ⊗_A M` on `X` being by definition the inverse of the model equivalence applied to
`AlgebraicGeometry.Space.modelTensorFunctor`. -/
def chartModelTensorIso :
    chartTensorModule x hx ⋙ chartModelFunctor x ≅ modelTensorFunctor (chartBaseRingHom x hx) :=
  Functor.isoWhiskerLeft (modelTensorFunctor (chartBaseRingHom x hx))
      (smallEtaleModelModulesEquiv B S hS x.obj.obj.left).counitIso ≪≫
    Functor.rightUnitor _

variable [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]

/-- The isomorphism `Ext^i_{𝒪_X}(E, 𝒪_X ⊗ f^*M~) ≃+ T^i(M)` for `ι : Φ(E) ≅ L_{X/A}`:
`CategoryTheory.ShiftedHom.coefficientAddEquiv` for the model equivalence, the coefficient
identification `chartCoefficientIso` and the counit of the model equivalence at `𝒪_X ⊗_A M`. -/
def chartExtTransport (E : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS x.obj.obj.left)))
    (ι : (chartModelFunctor x).mapDerivedCategory.obj E ≅
      (modelRingedToposHom (chartStructureMap x hx)).cotangentComplexDerived)
    (M : ModuleCat.{u} A) (i : ℤ) :
    tensorPullbackExtGroup B S hS E (chartStructureMap x hx)
        (structureSingleComplex x.obj.obj.left) ((affineBaseTilde A B S hS toS hA).obj M) i ≃+
      (cotangentExtFunctor (chartStructureMap x hx) (chartBaseRingHom x hx) i).obj M :=
  (ShiftedHom.coefficientAddEquiv (chartModelFunctor x) (chartCoefficientNatIso x hx)
      (chartModelTensorIso x hx) ι M i).trans
    (cotangentExtFunctorObjEquiv (chartStructureMap x hx) (chartBaseRingHom x hx) i M).symm

/-- Composed with `cotangentExtFunctorObjEquiv`, `chartExtTransport` is
`CategoryTheory.ShiftedHom.coefficientAddEquiv`. -/
theorem cotangentExtFunctorObjEquiv_chartExtTransport (E : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS x.obj.obj.left)))
    (ι : (chartModelFunctor x).mapDerivedCategory.obj E ≅
      (modelRingedToposHom (chartStructureMap x hx)).cotangentComplexDerived)
    (M : ModuleCat.{u} A) (i : ℤ)
    (y : tensorPullbackExtGroup B S hS E (chartStructureMap x hx)
        (structureSingleComplex x.obj.obj.left) ((affineBaseTilde A B S hS toS hA).obj M) i) :
    cotangentExtFunctorObjEquiv (chartStructureMap x hx) (chartBaseRingHom x hx) i M
        (chartExtTransport x hx E ι M i y) =
      ShiftedHom.coefficientAddEquiv (chartModelFunctor x) (chartCoefficientNatIso x hx)
        (chartModelTensorIso x hx) ι M i y :=
  AddEquiv.apply_symm_apply
    (cotangentExtFunctorObjEquiv (chartStructureMap x hx) (chartBaseRingHom x hx) i M) _

omit [HasDerivedCategory.{t} (modelModules x.obj.obj.left)] in
/-- The map of `Ext` groups of 08JR induced by `M ⟶ N`, as postcomposition. -/
theorem tensorPullbackExtGroupMap_affineBaseTilde_apply (E : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS x.obj.obj.left)))
    {M N : ModuleCat.{u} A} (g : M ⟶ N) (i : ℤ)
    (y : tensorPullbackExtGroup B S hS E (chartStructureMap x hx)
        (structureSingleComplex x.obj.obj.left) ((affineBaseTilde A B S hS toS hA).obj M) i) :
    (tensorPullbackExtGroupMap B S hS E (chartStructureMap x hx)
        (structureSingleComplex x.obj.obj.left) ((affineBaseTilde A B S hS toS hA).map g) i) y =
      (y : ShiftedHom E (DerivedCategory.Q.obj ((chartCoefficientFunctor x hx).obj M)) i) ≫
        (DerivedCategory.Q.map ((chartCoefficientFunctor x hx).map g))⟦i⟧' :=
  rfl

/-- `chartExtTransport` is natural in the `A`-module `M`. -/
theorem chartExtTransport_naturality (E : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS x.obj.obj.left)))
    (ι : (chartModelFunctor x).mapDerivedCategory.obj E ≅
      (modelRingedToposHom (chartStructureMap x hx)).cotangentComplexDerived)
    {M N : ModuleCat.{u} A} (g : M ⟶ N) (i : ℤ)
    (y : tensorPullbackExtGroup B S hS E (chartStructureMap x hx)
        (structureSingleComplex x.obj.obj.left) ((affineBaseTilde A B S hS toS hA).obj M) i) :
    chartExtTransport x hx E ι N i ((tensorPullbackExtGroupMap B S hS E (chartStructureMap x hx)
        (structureSingleComplex x.obj.obj.left) ((affineBaseTilde A B S hS toS hA).map g) i) y) =
      (cotangentExtFunctor (chartStructureMap x hx) (chartBaseRingHom x hx) i).map g
        (chartExtTransport x hx E ι M i y) := by
  apply (cotangentExtFunctorObjEquiv (chartStructureMap x hx) (chartBaseRingHom x hx) i N).injective
  refine (congrArg (fun w => cotangentExtFunctorObjEquiv (chartStructureMap x hx)
    (chartBaseRingHom x hx) i N (chartExtTransport x hx E ι N i w))
      (tensorPullbackExtGroupMap_affineBaseTilde_apply x hx E g i y)).trans ?_
  exact (cotangentExtFunctorObjEquiv_chartExtTransport x hx E ι N i _).trans
    ((ShiftedHom.coefficientAddEquiv_naturality (chartModelFunctor x) (chartCoefficientNatIso x hx)
      (chartModelTensorIso x hx) ι g i y).trans
      ((congrArg (fun z => z ≫ ((DerivedCategory.singleFunctor (modelModules x.obj.obj.left) 0).map
          ((modelTensorFunctor (chartBaseRingHom x hx)).map g))⟦i⟧')
        (cotangentExtFunctorObjEquiv_chartExtTransport x hx E ι M i y).symm).trans
        (cotangentExtFunctorObjEquiv_map (chartStructureMap x hx) (chartBaseRingHom x hx) i g
          (chartExtTransport x hx E ι M i y)).symm))

omit [HasDerivedCategory.{t} (modelModules x.obj.obj.left)] in
/-- The boundary map of 08JR at `M~`, as a composition of shifted morphisms. -/
theorem tensorPullbackExtGroupDelta_affineBaseTilde_apply (E : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS x.obj.obj.left)))
    {Sq : ShortComplex (ModuleCat.{u} A)}
    (hT : ((ShortComplex.mk ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (schemeSpace (algebraOver A B S hS toS hA))))
          (ComplexShape.up ℤ) 0).map (Sq.map (affineBaseTilde A B S hS toS hA)).f)
      ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (schemeSpace (algebraOver A B S hS toS hA))))
          (ComplexShape.up ℤ) 0).map (Sq.map (affineBaseTilde A B S hS toS hA)).g)
        (single_map_comp_map_eq_zero B S hS (Sq.map (affineBaseTilde A B S hS toS hA)))).map
          (tensorPullbackComplex (chartStructureMap x hx)
            (structureSingleComplex x.obj.obj.left))).ShortExact)
    (y : tensorPullbackExtGroup B S hS E (chartStructureMap x hx)
        (structureSingleComplex x.obj.obj.left) ((affineBaseTilde A B S hS toS hA).obj Sq.X₃) 1) :
    (tensorPullbackExtGroupDelta B S hS E (chartStructureMap x hx)
        (structureSingleComplex x.obj.obj.left) (Sq.map (affineBaseTilde A B S hS toS hA)) hT
        1 2 rfl) y =
      ShiftedHom.comp (y : ShiftedHom E (DerivedCategory.Q.obj
          ((chartCoefficientFunctor x hx).obj Sq.X₃)) (1 : ℤ))
        (DerivedCategory.triangleOfSESδ (S := Sq.map (chartCoefficientFunctor x hx)) hT)
        (show (1 : ℤ) + 1 = 2 by norm_num) :=
  rfl

/-- The functor `M ↦ 𝒪_X ⊗_A M` preserves zero morphisms. -/
instance chartTensorModule_preservesZeroMorphisms :
    (chartTensorModule x hx).PreservesZeroMorphisms :=
  baseRingTensorModule_preservesZeroMorphisms _ _

/-- `chartExtTransport` carries the boundary map of 08JR to the connecting map of `T^•`. -/
theorem chartExtTransport_delta (E : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS x.obj.obj.left)))
    (ι : (chartModelFunctor x).mapDerivedCategory.obj E ≅
      (modelRingedToposHom (chartStructureMap x hx)).cotangentComplexDerived)
    (hf : IsLocallyOfFiniteType B S hS (chartStructureMap x hx).hom)
    (hG : FlatProperSupportComplex B S hS (chartStructureMap x hx) hf
      (structureSingleComplex x.obj.obj.left))
    {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact)
    (hexact : (Sq.map (affineBaseTilde A B S hS toS hA)).ShortExact)
    (y : tensorPullbackExtGroup B S hS E (chartStructureMap x hx)
        (structureSingleComplex x.obj.obj.left) ((affineBaseTilde A B S hS toS hA).obj Sq.X₃) 1) :
    chartExtTransport x hx E ι Sq.X₁ 2
        ((tensorPullbackExtGroupDelta B S hS E (chartStructureMap x hx)
          (structureSingleComplex x.obj.obj.left) (Sq.map (affineBaseTilde A B S hS toS hA))
          (shortExact_tensorPullbackComplex_map_single
            (FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG) hexact) 1 2 rfl) y) =
      chartExtConnecting x hx hSq (chartExtTransport x hx E ι Sq.X₃ 1 y) := by
  have hQ := shortExact_map_modelTensorFunctor_chartBaseRingHom x hx hSq
  have hT : ((ShortComplex.mk ((HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (schemeSpace (algebraOver A B S hS toS hA))))
        (ComplexShape.up ℤ) 0).map (Sq.map (affineBaseTilde A B S hS toS hA)).f)
      ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (schemeSpace (algebraOver A B S hS toS hA))))
          (ComplexShape.up ℤ) 0).map (Sq.map (affineBaseTilde A B S hS toS hA)).g)
        (single_map_comp_map_eq_zero B S hS (Sq.map (affineBaseTilde A B S hS toS hA)))).map
          (tensorPullbackComplex (chartStructureMap x hx)
            (structureSingleComplex x.obj.obj.left))).ShortExact :=
    shortExact_tensorPullbackComplex_map_single
      (FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG) hexact
  have hS₁ : (Sq.map (chartCoefficientFunctor x hx)).ShortExact := hT
  apply (cotangentExtFunctorObjEquiv (chartStructureMap x hx) (chartBaseRingHom x hx) 2
    Sq.X₁).injective
  refine (congrArg (fun w => cotangentExtFunctorObjEquiv (chartStructureMap x hx)
    (chartBaseRingHom x hx) 2 Sq.X₁ (chartExtTransport x hx E ι Sq.X₁ 2 w))
      (tensorPullbackExtGroupDelta_affineBaseTilde_apply x hx E _ y)).trans ?_
  exact (cotangentExtFunctorObjEquiv_chartExtTransport x hx E ι Sq.X₁ 2 _).trans
    ((ShiftedHom.coefficientAddEquiv_comp_triangleOfSESδ (chartModelFunctor x)
      (chartCoefficientNatIso x hx) (chartModelTensorIso x hx) ι hS₁ hQ 1 2
        (by norm_num) y).trans
      ((congrArg (fun z => ShiftedHom.comp z hQ.singleδ (show (1 : ℤ) + 1 = 2 by norm_num))
        (cotangentExtFunctorObjEquiv_chartExtTransport x hx E ι Sq.X₃ 1 y).symm).trans
        (cotangentExtFunctorObjEquiv_cotangentExtConnecting (chartStructureMap x hx)
          (chartBaseRingHom x hx) hQ (chartExtTransport x hx E ι Sq.X₃ 1 y)).symm))

end AlgebraicGeometry.Space.ProperFlatLift

end
