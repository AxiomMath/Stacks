module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicCodimensionZeroProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicCodimensionZeroPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSections
public import StacksFrontier.LinearAlgebra.TensorProduct.PiCofinitelyTrivial

/-!
# The comparison of the meromorphic sections of a module with the direct images at a point

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `P` be a
presentation of its schematic locus at the codimension-zero points, let `η` be such a point and
let `F` be an `𝒪_X`-module.  This file builds the comparison of presheaves of `𝒦_X`-modules

`𝒦_X ⊗_{𝒪_X} F ⟶ j_{η, *}j_η^*F`,  `a ⊗ s ↦ a · s|_{U ×_X Spec(𝒪_{X, η})}`,

and proves that, for a *quasi-coherent* `F` and under hypotheses (a) and (b) of Stacks 0ENA, the
family of these comparisons over all codimension-zero points is jointly bijective on the sections
over every **affine** étale chart of `X`.

The direct image `j_{η, *}j_η^*F` is taken along small-chart base change with the canonical
comparison `𝒦_X ⟶ j_{η, *}𝒪_{X, η}` of
`AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointComparison` as its structure
map, so that it is a sheaf of `𝒦_X`-modules whose sections over an étale chart `U` of `X` are,
on the nose, the sections of `j_η^*F` over the base-changed chart `U ×_X Spec(𝒪_{X, η})`.  The
comparison is the transpose along the change-of-rings adjunction of Stacks 03CU of the canonical
map `F ⟶ j_{η, *}j_η^*F`, whose value over `U` is the chart component of the unit of the
Stacks 03D7 adjunction at the cartesian square defining `U ×_X Spec(𝒪_{X, η})`.

Over an affine chart `U`, write `A = 𝒪_X(U)`, `K = 𝒦_X(U)`, `M = F(U)` and
`A_η = (j_{η, *}𝒪_{X, η})(U)`.  The source of the comparison is `K ⊗_A M` and its `η`-th target
is `A_η ⊗_A M`, by the chart bijectivity of Stacks 083K; the comparison is then the base change
along the ring comparison `K ⟶ ∏_η A_η`, which is bijective by the first conclusion of
Stacks 0ENA on sections, followed by the canonical map `(∏_η A_η) ⊗_A M ⟶ ∏_η (A_η ⊗_A M)`.
The last map is bijective because `A_η` is the zero ring for all but the finitely many `η` in
the image of `U`, their number being bounded by hypothesis (b).

## Main definitions

* `AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointMeromorphicModule`:
  `j_{η, *}j_η^*F` as a sheaf of `𝒦_X`-modules.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointSection`: the chart component
  of the canonical map `F ⟶ j_{η, *}j_η^*F`.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointMeromorphicComparison`: the
  comparison `𝒦_X ⊗_{𝒪_X} F ⟶ j_{η, *}j_η^*F`.

## Main results

* `AlgebraicGeometry.Space.CodimensionZeroPresentation.isAffine_genericPointChart`: the base
  change of an affine étale chart to `Spec(𝒪_{X, η})` is affine.
* `…CodimensionZeroPresentation.bijective_modulePullbackChartBaseChange_genericPoint`: the chart
  bijectivity of Stacks 083K at that base change.
* `…CodimensionZeroPresentation.bijective_pi_genericPointMeromorphicComparison_app`: **the family
  of comparisons is jointly bijective over an affine étale chart.**

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

namespace CodimensionZeroPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (P : CodimensionZeroPresentation B S hS X.1) {x : points B S hS X.1}
    (hx : localRingDimension B S hS x = 0)

/-- The comparison `𝒦_X ⟶ j_{η, *}𝒪_{X, η}` as a morphism of sheaves of (not necessarily
commutative) rings. -/
noncomputable def genericPointComparisonRing :
    (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O) ⟶
      ((smallBaseChange B S hS (P.genericMorphism hx X.2)
            (P.representable_genericMorphism hx)).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS (P.specStalkSpace hx).1)).obj
        (smallEtaleRingSheaf B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2) :=
  (sheafCompose (SmallEtale.topology B S hS X.1)
    (forget₂ CommRingCat.{u} RingCat.{u})).map (P.genericPointComparison hx)

/-- **The contribution `j_{η, *}j_η^*F` of a codimension-zero point to the meromorphic sections
of `F`, as a sheaf of `𝒦_X`-modules.** -/
noncomputable def genericPointMeromorphicModule (F : Modules.{u, u} B S hS X.1 X.2) :
    SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O) :=
  (SheafOfModules.pushforward (P.genericPointComparisonRing hx)).obj
    (P.genericPointPullback hx F)

/-- The sections of `j_{η, *}j_η^*F` over an étale chart `U` of `X` are the sections of `j_η^*F`
over the base-changed chart `U ×_X Spec(𝒪_{X, η})`, on the nose. -/
theorem genericPointMeromorphicModule_obj (F : Modules.{u, u} B S hS X.1 X.2)
    (U : SmallEtale B S hS X.1) :
    ((P.genericPointMeromorphicModule hx F).val.obj (op U) : Type u) =
      ((P.genericPointPullback hx F).val.obj (op (P.genericPointChart hx U)) : Type u) :=
  rfl

/-! ### The canonical map `F ⟶ j_{η, *}j_η^*F` -/

/-- The value over an étale chart `U` of `X` of the canonical map `F ⟶ j_{η, *}j_η^*F`: the
chart component of the unit of the Stacks 03D7 adjunction at the cartesian square defining the
base-changed chart `U ×_X Spec(𝒪_{X, η})`. -/
noncomputable abbrev genericPointSection (F : Modules.{u, u} B S hS X.1 X.2)
    (U : SmallEtale B S hS X.1) (s : F.val.obj (op U)) :
    (P.genericPointPullback hx F).val.obj (op (P.genericPointChart hx U)) :=
  modulePullbackChartSection B S hS (P.genericMorphism hx X.2) F
    (P.genericPointChartDiagram hx U) s

/-- The chart component of the unit is compatible with étale restriction of the chart: the
cartesian projections `U ×_X Spec(𝒪_{X, η}) ⟶ U` are natural in `U`. -/
theorem genericPointSection_map (F : Modules.{u, u} B S hS X.1 X.2)
    {U U' : SmallEtale B S hS X.1} (k : U' ⟶ U) (s : F.val.obj (op U)) :
    P.genericPointSection hx F U' (F.val.map k.op s) =
      (P.genericPointPullback hx F).val.map
        ((smallBaseChange B S hS (P.genericMorphism hx X.2)
          (P.representable_genericMorphism hx)).map k).op (P.genericPointSection hx F U s) := by
  have hnat := (modulePullbackChartFMap B S hS (P.genericMorphism hx X.2) F).naturality
    (P.genericPointChartDiagram hx U) (P.genericPointChartDiagram hx U')
    ((smallBaseChange B S hS (P.genericMorphism hx X.2)
      (P.representable_genericMorphism hx)).map k) k
    ((smallBaseChangeProjection B S hS (P.genericMorphism hx X.2)
      (P.representable_genericMorphism hx)).naturality k) s
  refine (modulePullbackChartFMap_app B S hS (P.genericMorphism hx X.2) F
    (P.genericPointChartDiagram hx U') (F.val.map k.op s)).symm.trans (hnat.trans ?_)
  exact congrArg
    (fun z => (P.genericPointPullback hx F).val.map
      ((smallBaseChange B S hS (P.genericMorphism hx X.2)
        (P.representable_genericMorphism hx)).map k).op z)
    (modulePullbackChartFMap_app B S hS (P.genericMorphism hx X.2) F
      (P.genericPointChartDiagram hx U) s)

/-- **The canonical map `F ⟶ j_{η, *}j_η^*F`**, as a morphism of presheaves of `𝒪_X`-modules
into the restriction of scalars of the sheaf of `𝒦_X`-modules `j_{η, *}j_η^*F`: over an étale
chart `U` of `X` it is the chart component of the unit of the Stacks 03D7 adjunction at the
cartesian square defining `U ×_X Spec(𝒪_{X, η})`.

It is semilinear for the structure map `𝒪_X ⟶ j_{η, *}𝒪_{X, η}`, which is the composite of
`𝒪_X ⟶ 𝒦_X` with the comparison `𝒦_X ⟶ j_{η, *}𝒪_{X, η}`; that is what makes it a morphism of
`𝒪_X`-modules into the restriction of scalars along `𝒪_X ⟶ 𝒦_X`. -/
noncomputable def genericPointMeromorphicUnit (F : Modules.{u, u} B S hS X.1 X.2) :
    F.val ⟶ (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars
        (toMeromorphicFunctionSheaf B S hS X.1 X.2).hom).obj
      (P.genericPointMeromorphicModule hx F).val :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun s => P.genericPointSection hx F U.unop s)
          fun s t => modulePullbackChartSection_add B S hS (P.genericMorphism hx X.2) F
            (P.genericPointChartDiagram hx U.unop) s t)
      naturality := fun U U' k => by
        ext s
        exact P.genericPointSection_map hx F k.unop s }
    fun U r s => by
      refine Eq.trans (modulePullbackChartSection_smul B S hS (P.genericMorphism hx X.2) F
        (P.genericPointChartDiagram hx U.unop) r s) ?_
      exact congrArg
        (fun a : chartRing B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2
            (P.genericPointChart hx U.unop) => a • P.genericPointSection hx F U.unop s)
        (P.genericPointComparison_app_toMeromorphicFunctionSheaf hx U.unop r).symm

/-- On sections the canonical map is the chart component of the unit. -/
theorem genericPointMeromorphicUnit_app (F : Modules.{u, u} B S hS X.1 X.2)
    (U : SmallEtale B S hS X.1) (s : F.val.obj (op U)) :
    PresheafOfModules.Hom.app (P.genericPointMeromorphicUnit hx F) (op U) s =
      P.genericPointSection hx F U s :=
  rfl

/-! ### The comparison of presheaves of `𝒦_X`-modules -/

/-- **The comparison `𝒦_X ⊗_{𝒪_X} F ⟶ j_{η, *}j_η^*F`**, the transpose of the canonical map
`F ⟶ j_{η, *}j_η^*F` along the change-of-rings adjunction of Stacks 03CU: it sends `a ⊗ s` to
`a` times the chart component of the unit at `s`. -/
noncomputable def genericPointMeromorphicComparison (F : Modules.{u, u} B S hS X.1 X.2) :
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
        (toMeromorphicFunctionSheaf B S hS X.1 X.2).hom).obj F.val ⟶
      (P.genericPointMeromorphicModule hx F).val :=
  Stacks.PresheafOfModules.ChangeOfRings.counitHom _ (P.genericPointMeromorphicUnit hx F)

/-- The comparison carries `a ⊗ s` to the image of `a` under `𝒦_X ⟶ j_{η, *}𝒪_{X, η}` times the
chart component of the unit at `s`. -/
theorem genericPointMeromorphicComparison_tmul (F : Modules.{u, u} B S hS X.1 X.2)
    (U : SmallEtale B S hS X.1)
    (a : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U))
    (s : F.val.obj (op U)) :
    letI := ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom.toAlgebra
    letI : Module ((structureSheaf B S hS X.1 X.2).obj.obj (op U)) (F.val.obj (op U)) :=
      inferInstanceAs (Module (chartRing B S hS X.1 X.2 U) (F.val.obj (op U)))
    PresheafOfModules.Hom.app (P.genericPointMeromorphicComparison hx F) (op U)
        (TensorProduct.tmul ((structureSheaf B S hS X.1 X.2).obj.obj (op U)) a s) =
      (show chartRing B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2
          (P.genericPointChart hx U) from
        ((P.genericPointComparisonRing hx).hom.app (op U)).hom a) •
        P.genericPointSection hx F U s :=
  Stacks.PresheafOfModules.ChangeOfRings.counitApp_tmul _
    (P.genericPointMeromorphicUnit hx F) (op U) a s

/-! ### Vanishing and affineness over a chart -/

/-- **A chart no point of which lies over `η` has no nonzero regular functions on its base
change.** -/
theorem subsingleton_genericPointStructureSheaf_obj (V : SmallEtale B S hS X.1)
    (hV : ∀ z : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)),
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.1.hom z ≠ x) :
    Subsingleton ((P.genericPointStructureSheaf hx).obj.obj (op V)) := by
  have : IsEmpty ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (P.specStalkSpace hx).1).obj (P.genericPointChart hx V))) :=
    ⟨fun z => hV _ ((P.mem_range_genericPointProjection_iff hx V _).mp ⟨z, rfl⟩)⟩
  exact inferInstanceAs (Subsingleton Γ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS (P.specStalkSpace hx).1).obj (P.genericPointChart hx V)), ⊤))

/-- **The base change of an affine étale chart to `Spec(𝒪_{X, η})` is affine.** -/
theorem isAffine_genericPointChart (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (U : SmallEtale B S hS X.1) (hU : IsAffine (smallEtaleScheme B S hS X.1 U)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (P.specStalkSpace hx).1).obj (P.genericPointChart hx U))) := by
  have := P.flat_genericPointProjection hx U
  have := P.isPreimmersion_genericPointProjection hx U
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hU
  obtain ⟨_, _⟩ := finite_and_discreteTopology_of_flat_isPreimmersion
    ((BigFppfOver.toScheme B S hS).map (P.genericPointProjection hx U))
    (P.ringKrullDim_stalk_specStalkChart hx X.2 (P.genericPointChart hx U))
    (genericPoints.finite
      (finite_irreducibleComponents_chart_of_hasLocallyFiniteIrreducibleComponents
        B S hS hfin U.1.left U.1.hom (isEtale_of_presheaf_etale B S hS U.2)))
  infer_instance

/-- **The base-change comparison `𝒪_{X, η}(U) ⊗_{𝒪_X(U)} F(U) ⟶ (j_η^*F)(U ×_X Spec(𝒪_{X, η}))`
at a quasi-coherent module over an affine étale chart is bijective.** -/
theorem bijective_modulePullbackChartBaseChange_genericPoint
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS X.1) (hU : IsAffine (smallEtaleScheme B S hS X.1 U)) :
    letI := chartDiagramAlgebra B S hS (P.genericMorphism hx X.2)
      (P.genericPointChartDiagram hx U)
    Function.Bijective (modulePullbackChartBaseChange B S hS (P.genericMorphism hx X.2) F
      (P.genericPointChartDiagram hx U)) :=
  bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS
    (P.genericMorphism hx X.2) F hF (P.genericPointChartDiagram hx U)
    (P.isAffine_genericPointChart hx hfin U hU) hU


/-! ### Bijectivity over an affine chart -/

/-- **The family of comparisons `𝒦_X ⊗_{𝒪_X} F ⟶ j_{η, *}j_η^*F` is jointly bijective on the
sections over an affine étale chart.** -/
theorem bijective_pi_genericPointMeromorphicComparison_app
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS X.1) (hU : IsAffine (smallEtaleScheme B S hS X.1 U)) :
    Function.Bijective fun z : ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
          (toMeromorphicFunctionSheaf B S hS X.1 X.2).hom).obj F.val).obj (op U) =>
      fun η : CodimensionZeroPoints B S hS X.1 =>
        PresheafOfModules.Hom.app (P.genericPointMeromorphicComparison η.2 F) (op U) z := by
  classical
  let := ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom.toAlgebra
  let : Module ((structureSheaf B S hS X.1 X.2).obj.obj (op U)) (F.val.obj (op U)) :=
    inferInstanceAs (Module (chartRing B S hS X.1 X.2 U) (F.val.obj (op U)))
  let algη : ∀ η : CodimensionZeroPoints B S hS X.1,
      Algebra ((structureSheaf B S hS X.1 X.2).obj.obj (op U))
        (chartRing B S hS (P.specStalkSpace η.2).1 (P.specStalkSpace η.2).2
          (P.genericPointChart η.2 U)) := fun η =>
    chartDiagramAlgebra B S hS (P.genericMorphism η.2 X.2) (P.genericPointChartDiagram η.2 U)
  set cp : ∀ η : CodimensionZeroPoints B S hS X.1,
      (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) →ₗ[
          (structureSheaf B S hS X.1 X.2).obj.obj (op U)]
        chartRing B S hS (P.specStalkSpace η.2).1 (P.specStalkSpace η.2).2
          (P.genericPointChart η.2 U) := fun η =>
    AlgHom.toLinearMap
      { toRingHom := ((P.genericPointComparison η.2).hom.app (op U)).hom
        commutes' := P.genericPointComparison_app_toMeromorphicFunctionSheaf η.2 U }
  have hsub : ∀ η ∉ (finite_codimensionZeroPoints_mem_range (X := X) hfin U hU).toFinset,
      Subsingleton (chartRing B S hS (P.specStalkSpace η.2).1 (P.specStalkSpace η.2).2
        (P.genericPointChart η.2 U)) := by
    intro η hη
    refine P.subsingleton_genericPointStructureSheaf_obj η.2 U fun z hz => hη ?_
    exact (Set.Finite.mem_toFinset _).mpr ⟨z, hz⟩
  have hmid := Stacks.bijective_pi_rTensor_of_bijective_pi (M := F.val.obj (op U)) cp
    (P.bijective_pi_genericPointComparison_app hwa hfin U hU)
    (finite_codimensionZeroPoints_mem_range (X := X) hfin U hU).toFinset hsub
  have hid : ∀ (η : CodimensionZeroPoints B S hS X.1)
      (z : TensorProduct ((structureSheaf B S hS X.1 X.2).obj.obj (op U))
        ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) (F.val.obj (op U))),
      PresheafOfModules.Hom.app (P.genericPointMeromorphicComparison η.2 F) (op U) z =
        modulePullbackChartBaseChange B S hS (P.genericMorphism η.2 X.2) F
          (P.genericPointChartDiagram η.2 U)
          (LinearMap.rTensor (F.val.obj (op U)) (cp η) z) := by
    intro η
    have h : (PresheafOfModules.Hom.app (P.genericPointMeromorphicComparison η.2 F)
          (op U)).hom.toAddMonoidHom =
        (modulePullbackChartBaseChange B S hS (P.genericMorphism η.2 X.2) F
          (P.genericPointChartDiagram η.2 U)).toAddMonoidHom.comp
          (LinearMap.rTensor (F.val.obj (op U)) (cp η)).toAddMonoidHom := by
      refine AddMonoidHom.ext fun z => ?_
      induction z using TensorProduct.induction_on with
      | zero => exact (AddMonoidHom.map_zero _).trans (AddMonoidHom.map_zero _).symm
      | tmul a s =>
        refine Eq.trans (P.genericPointMeromorphicComparison_tmul η.2 F U a s) ?_
        exact (modulePullbackChartBaseChange_tmul B S hS (P.genericMorphism η.2 X.2) F
          (P.genericPointChartDiagram η.2 U) (cp η a) s).symm
      | add z w hz hw =>
        exact (AddMonoidHom.map_add _ z w).trans
          ((congrArg₂ (· + ·) hz hw).trans (AddMonoidHom.map_add _ z w).symm)
    exact fun z => DFunLike.congr_fun h z
  exact (congrArg Function.Bijective (funext fun z => funext fun η => hid η z)).mpr
    ((Function.Bijective.piMap fun η =>
      P.bijective_modulePullbackChartBaseChange_genericPoint η.2 hfin F hF U hU).comp hmid)

end CodimensionZeroPresentation

end AlgebraicGeometry.Space

end
