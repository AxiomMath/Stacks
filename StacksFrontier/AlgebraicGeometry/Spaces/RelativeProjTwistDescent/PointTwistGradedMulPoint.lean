module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistGradedMul

/-!
# The base change identification of `𝒪_P(n)` to a scheme point is multiplicative and unital

In Situation 0849 let `P = Proj_X(𝒜)` be the relative homogeneous spectrum of Stacks 084B with
twists `𝒪_P(n)` (Stacks 084D), and let `f : T ⟶ X` be a scheme point.  This file shows that the
identifications `(T ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)^a` of
`AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso` carry the
multiplication and the unit of the twists of `P` to the multiplication and the unit of the twists
of Stacks 01NR on `T ×_X P`: the base change of `⨁_n 𝒪_P(n)` is the graded algebra of Stacks 01NR,
as graded algebras.  The final statements use the twists, their multiplication and unit and the
identifications themselves.

## Main results

* `AlgebraicGeometry.Space.modulePullbackTensorIso_inv_comp_map_comp_of_forall_ofIsoYoneda_spec`:
  families of identifications `h^*𝒯_n ≅ N_n^a` described on the atlas carry multiplications to
  multiplications.
* `AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso_twistAlgebraMul`,
  `AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso_twistAlgebraUnit`:
  **the base change identification of Stacks 084D is multiplicative and unital.**

## Implementation notes

The multiplicative square is assembled in steps, each its own declaration
(`…RelativeProjSituation.fibreToSpaceTwistModuleIso_mul_of_charts`,
`…RelativeProjSituation.fibreToSpaceTwistModuleIso_mul_of_comparisons`,
`…RelativeProjSituation.fibreToSpaceTwistModuleIso_mul_of_pointComparison`), every argument named
in the spelling of `…RelativeProjSituation.fibreToSpaceTwistModuleIso_spec`; the identification
is folded only at the end, through `…RelativeProjSituation.fibreToSpaceTwistModuleIso_eq`.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

section OfIsoYonedaMulFamily

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  (P0 : Presentation B S hS F hF) {W : BigFppfOver B S hS} (e : F ≅ yoneda.obj W)
  (c : P0.U ⟶ W) (hc : yoneda.map c = P0.toSpace ≫ e.hom)
  {XA : AlgebraicSpaces B S hS} (Pb : Presentation B S hS XA.obj XA.property)
  (hA : representedAlgebraicSpace B S hS W ⟶ XA) (yU : (P0.ofIsoYoneda e c hc).U ⟶ Pb.U)
  (hY : presentationAtlas (P0.ofIsoYoneda e c hc) ≫ hA =
    representedSpaceMap B S hS yU ≫ presentationAtlas Pb)
  (Tm : ℤ → QuasicoherentSheaves.{u, u} B S hS XA.obj XA.property)
  {M : ℤ → (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj Pb.U).ringCatSheaf).FullSubcategory}
  (κ : ∀ n, (modulePullback B S hS (presentationAtlas Pb)).obj (Tm n).obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS Pb.U).functor.obj (M n)).obj)
  {M'' : ℤ → (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (P0.ofIsoYoneda e c hc).U).ringCatSheaf).FullSubcategory}
  (Θ : ∀ n, quasicoherentPullbackObj B S hS yU (M n) ≅ M'' n)
  {N : ℤ → (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
  (ΘB : ∀ n, quasicoherentPullbackObj B S hS c (N n) ≅ M'' n)
  (ι : ∀ n, (modulePullback B S hS hA).obj (Tm n).obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj (N n)).obj)
  (hι : ∀ n, (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).map (ι n).hom ≫
      (ofIsoYonedaChartIso P0 e c hc (N n) (ΘB n)).hom =
    (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY (Tm n) (κ n) (Θ n)).hom)

include hY hι in
/-- `AlgebraicGeometry.Space.modulePullbackTensorIso_inv_comp_map_comp_of_ofIsoYoneda_spec` for a
family of identifications `ι_n : hA^*𝒯_n ≅ N_n^a` indexed by the degree: if the chart
identifications `κ` carry a multiplication `μ : 𝒯_i ⊗ 𝒯_j ⟶ 𝒯_(i + j)` to an attached
multiplication `m^a`, and `Θ`, `Θ_B` carry `m` and `m_N` to the same multiplication `m''` (through
Stacks 03EL), then the `ι_n` carry the inverse image of `μ` to `m_N^a`. -/
theorem modulePullbackTensorIso_inv_comp_map_comp_of_forall_ofIsoYoneda_spec (i j : ℤ)
    (μ : (Tm i).obj ⊗ (Tm j).obj ⟶ (Tm (i + j)).obj)
    (m : quasicoherentTensorObj B S hS Pb.U (M i) (M j) ⟶ M (i + j))
    (m'' : quasicoherentTensorObj B S hS (P0.ofIsoYoneda e c hc).U (M'' i) (M'' j) ⟶ M'' (i + j))
    (mN : quasicoherentTensorObj B S hS W (N i) (N j) ⟶ N (i + j))
    (hμ : (modulePullback B S hS (presentationAtlas Pb)).map μ ≫ (κ (i + j)).hom =
      (modulePullbackTensorIso B S hS (presentationAtlas Pb) (Tm i).obj (Tm j).obj).hom ≫
        ((κ i).hom ⊗ₘ (κ j).hom) ≫ representedTensorChartMul B S hS m)
    (hbU : RepresentedC3TensorCompat B S hS yU (M i) (M j))
    (hm : (quasicoherentPullbackTensorIso B S hS yU (M i) (M j)).inv ≫
        quasicoherentPullbackMap B S hS yU m ≫ (Θ (i + j)).hom =
      quasicoherentTensorHom B S hS (P0.ofIsoYoneda e c hc).U (Θ i).hom (Θ j).hom ≫ m'')
    (hbW : RepresentedC3TensorCompat B S hS c (N i) (N j))
    (hmN : (quasicoherentPullbackTensorIso B S hS c (N i) (N j)).inv ≫
        quasicoherentPullbackMap B S hS c mN ≫ (ΘB (i + j)).hom =
      quasicoherentTensorHom B S hS P0.U (ΘB i).hom (ΘB j).hom ≫ m'') :
    (modulePullbackTensorIso B S hS hA (Tm i).obj (Tm j).obj).inv ≫
        (modulePullback B S hS hA).map μ ≫ (ι (i + j)).hom =
      ((ι i).hom ⊗ₘ (ι j).hom) ≫ representedTensorChartMul B S hS mN :=
  modulePullbackTensorIso_inv_comp_map_comp_of_ofIsoYoneda_spec P0 e c hc Pb hA yU hY (κ i) (κ j)
    (κ (i + j)) (Θ i) (Θ j) (Θ (i + j)) (ΘB i) (ΘB j) (ΘB (i + j)) (ι i) (ι j) (ι (i + j)) (hι i)
    (hι j) (hι (i + j)) μ m m'' mN hμ hbU hm hbW hmN

end OfIsoYonedaMulFamily

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

section Point

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)

/-- **The base change identification of Stacks 084D is unital**: for a scheme point
`f : T ⟶ X`, the identification `(T ×_X P ⟶ P)^*𝒪_P(0) ≅ 𝒪(0)^a` of
`AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso` carries the inverse
image of the unit `𝒪_P ⟶ 𝒪_P(0)` of
`AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraUnit`, read through Stacks 03LU, to the
unit of the twists of Stacks 01NR on `T ×_X P`. -/
theorem fibreToSpaceTwistModuleIso_twistAlgebraUnit :
    (modulePullbackUnitIso s.site s.base s.containsBase (s.fibreToSpaceHom T f)).inv ≫
      (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).map
        (s.twistAlgebraUnit Px) ≫ (s.fibreToSpaceTwistModuleIso Px T f 0).hom =
      representedUnitChartHom s.site s.base s.containsBase (s.twistPieceUnit T f) :=
  modulePullbackUnitIso_inv_comp_map_comp_eq_of_heq (s.fibreToSpaceTwistModuleIso_unit Px T f)
    (s.fibreToSpaceHom T f) (s.twistAlgebraUnit Px) (s.fibreToSpaceTwistModuleIso Px T f 0).hom
    (representedUnitChartHom s.site s.base s.containsBase (s.twistPieceUnit T f)) rfl rfl
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl
    (heq_of_eq (congrArg Iso.hom (s.fibreToSpaceTwistModuleIso_eq Px T f 0)).symm) HEq.rfl

/-- `AlgebraicGeometry.Space.modulePullbackTensorIso_inv_comp_map_comp_of_forall_ofIsoYoneda_spec`
for the base change identifications `…RelativeProjSituation.fibreToSpaceTwistModuleIso` of
Stacks 084D at a scheme point, described on the étale cover by
`…RelativeProjSituation.fibreToSpaceTwistModuleIso_spec`. -/
theorem fibreToSpaceTwistModuleIso_mul_of_charts (i j : ℤ) :
    type_of% (modulePullbackTensorIso_inv_comp_map_comp_of_forall_ofIsoYoneda_spec
        (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := representedAlgebraicSpace s.site s.base s.containsBase T)
          (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
          (s.isAlgebraicSpace_pointRelativeProjFunctor T f))
        (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.fibreToSpaceHom T f)
        (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
          (Px.map_alongPointToAtlas_comp_toSpace' f))
        (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
        (fun n => presentationDescendedModule
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
          (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
          (s.presentationSchemeCocycle_twistTransition Px n)
          (s.presentationSchemeUnit_twistTransition Px n))
        (fun n => presentationDescendedModuleChartIso
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
          (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
          (s.presentationSchemeCocycle_twistTransition Px n)
          (s.presentationSchemeUnit_twistTransition Px n))
        (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
          (Px.map_alongPointToAtlas_comp_toSpace' f))
        (s.pointChartTwistComparison Px T f)
        (fun n => RelativeProjPoints.pullbackTransitionCompatibleIso
          (XA' := representedAlgebraicSpace s.site s.base s.containsBase T)
          (dA := s.relativeProjPoints)
          (dA' := (s.pullback (s.schemePointHom T f)).relativeProjPoints)
          (hA := s.relativeProjBaseChangeHom (s.schemePointHom T f)) Px (Px.alongPoint f)
          s.isAlgebraicSpace_relativeProjFunctor
            (s.isAlgebraicSpace_pointRelativeProjFunctor T f)
          (Px.alongPointRelationMap_comp_target f) (Px.alongPointRelationMap_comp_source f)
          (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
            (Px.map_alongPointToAtlas_comp_toSpace' f))
          (s.liesOverAlong_pointChartBaseChangeMap Px T f)
          (s.relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f)
            (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
            (Px.alongPointRelationMap_comp_target f))
          (s.liesOverAlong_pointRelationBaseChangeMap Px T f)
          (presentationDescendedModule
            (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
            (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
            (s.presentationSchemeCocycle_twistTransition Px n)
            (s.presentationSchemeUnit_twistTransition Px n))
          (s.twistTransition Px n)
          (presentationDescendedModuleChartIso
            (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
            (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
            (s.presentationSchemeCocycle_twistTransition Px n)
            (s.presentationSchemeUnit_twistTransition Px n))
          (s.presentationDescendedModuleChartIso_comm_twistTransition Px n)
          ((s.pullback (s.schemePointHom T f)).twistTransition (Px.alongPoint f) n)
          (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f)
            (Px.map_alongPointToAtlas_comp_toSpace' f) n)
          (s.pullbackTransitionCompatible_pointChartBaseChangeMap Px T f n)
          (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)
          (s.fibreToSpaceHom T f) (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
          (s.twistPieceQcoh T f n) (s.pointChartTwistComparison Px T f n)
          (s.canonicalSchemeTransition_pointChartTwistComparison Px T f n))
        (s.fibreToSpaceTwistModuleIso_spec Px T f) i j) :=
  modulePullbackTensorIso_inv_comp_map_comp_of_forall_ofIsoYoneda_spec
    (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base) (hS := s.containsBase)
      (X := representedAlgebraicSpace s.site s.base s.containsBase T)
      (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
      (s.isAlgebraicSpace_pointRelativeProjFunctor T f))
    (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)
    (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
    (s.fibreToSpaceHom T f)
    (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
      (Px.map_alongPointToAtlas_comp_toSpace' f))
    (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
    (fun n => presentationDescendedModule
      (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
      (s.presentationSchemeCocycle_twistTransition Px n)
      (s.presentationSchemeUnit_twistTransition Px n))
    (fun n => presentationDescendedModuleChartIso
      (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
      (s.presentationSchemeCocycle_twistTransition Px n)
      (s.presentationSchemeUnit_twistTransition Px n))
    (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
      (Px.map_alongPointToAtlas_comp_toSpace' f))
    (s.pointChartTwistComparison Px T f) _
    (s.fibreToSpaceTwistModuleIso_spec Px T f) i j

/-- `…RelativeProjSituation.fibreToSpaceTwistModuleIso_mul_of_charts` for the multiplication of the
twists of the relative Proj (`…RelativeProjSituation.twistAlgebraMul_spec`). -/
theorem fibreToSpaceTwistModuleIso_mul_of_comparisons (i j : ℤ) :
    type_of% (s.fibreToSpaceTwistModuleIso_mul_of_charts Px T f i j _
        (s.twistPieceMul Px.U Px.toSpace i j)
        ((s.pullback (s.schemePointHom T f)).twistPieceMul (Px.alongPoint f).U
          (Px.alongPoint f).toSpace i j)
        (s.twistPieceMul T f i j) (s.twistAlgebraMul_spec Px i j)) :=
  s.fibreToSpaceTwistModuleIso_mul_of_charts Px T f i j _
    (s.twistPieceMul Px.U Px.toSpace i j)
    ((s.pullback (s.schemePointHom T f)).twistPieceMul (Px.alongPoint f).U
      (Px.alongPoint f).toSpace i j)
    (s.twistPieceMul T f i j) (s.twistAlgebraMul_spec Px i j)

/-- `…RelativeProjSituation.fibreToSpaceTwistModuleIso_mul_of_comparisons` with the comparisons of
twists along `T_U ×_T P' ⟶ U ×_X P` carrying the multiplications of the twists
(`…RelativeProjSituation.baseChangeTwistPieceComparison_mul`). -/
theorem fibreToSpaceTwistModuleIso_mul_of_pointComparison (i j : ℤ) :
    type_of% (s.fibreToSpaceTwistModuleIso_mul_of_comparisons Px T f i j
        (representedC3TensorCompat s.site s.base s.containsBase _ _ _)
        (quasicoherentPullbackTensorIso_inv_comp_map_comp_eq_of_heq
          (ΘM := (s.baseChangeTwistPieceComparison (s.schemePointHom T f) (Px.alongPointToAtlas f)
            (Px.map_alongPointToAtlas_comp_toSpace' f)
            (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
              (Px.alongPointToAtlas f)
              (Px.map_alongPointToAtlas_comp_toSpace' f))
            (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
              (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) i).hom)
          (ΘN := (s.baseChangeTwistPieceComparison (s.schemePointHom T f) (Px.alongPointToAtlas f)
            (Px.map_alongPointToAtlas_comp_toSpace' f)
            (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
              (Px.alongPointToAtlas f)
              (Px.map_alongPointToAtlas_comp_toSpace' f))
            (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
              (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) j).hom)
          (s.baseChangeTwistPieceComparison_mul (s.schemePointHom T f) (Px.alongPointToAtlas f)
            (Px.map_alongPointToAtlas_comp_toSpace' f) _
            (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
              (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) i j)
          rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
          HEq.rfl HEq.rfl)) :=
  s.fibreToSpaceTwistModuleIso_mul_of_comparisons Px T f i j
      (representedC3TensorCompat s.site s.base s.containsBase _ _ _)
      (quasicoherentPullbackTensorIso_inv_comp_map_comp_eq_of_heq
        (ΘM := (s.baseChangeTwistPieceComparison (s.schemePointHom T f) (Px.alongPointToAtlas f)
          (Px.map_alongPointToAtlas_comp_toSpace' f)
          (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
            (Px.map_alongPointToAtlas_comp_toSpace' f))
          (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) i).hom)
        (ΘN := (s.baseChangeTwistPieceComparison (s.schemePointHom T f) (Px.alongPointToAtlas f)
          (Px.map_alongPointToAtlas_comp_toSpace' f)
          (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
            (Px.map_alongPointToAtlas_comp_toSpace' f))
          (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) j).hom)
        (s.baseChangeTwistPieceComparison_mul (s.schemePointHom T f) (Px.alongPointToAtlas f)
          (Px.map_alongPointToAtlas_comp_toSpace' f) _
          (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) i j)
        rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
        HEq.rfl HEq.rfl)

/-- **The base change identification of Stacks 084D is multiplicative**: for a scheme point
`f : T ⟶ X`, the identifications `(T ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)^a` of
`AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso` carry the inverse image
of the multiplication `𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` of
`AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul`, read through Stacks 03EL, to the
multiplication of the twists of Stacks 01NR on `T ×_X P = Proj_T(f^*𝒜)`. -/
theorem fibreToSpaceTwistModuleIso_twistAlgebraMul (i j : ℤ) :
    (modulePullbackTensorIso s.site s.base s.containsBase (s.fibreToSpaceHom T f)
        (s.twistModule Px i).obj (s.twistModule Px j).obj).inv ≫
      (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).map
        (s.twistAlgebraMul Px i j) ≫ (s.fibreToSpaceTwistModuleIso Px T f (i + j)).hom =
      ((s.fibreToSpaceTwistModuleIso Px T f i).hom ⊗ₘ
        (s.fibreToSpaceTwistModuleIso Px T f j).hom) ≫
        representedTensorChartMul s.site s.base s.containsBase (s.twistPieceMul T f i j) :=
  modulePullbackTensorIso_inv_comp_map_comp_eq_of_heq
    (s.fibreToSpaceTwistModuleIso_mul_of_pointComparison Px T f i j
      (representedC3TensorCompat s.site s.base s.containsBase _ _ _)
        (quasicoherentPullbackTensorIso_inv_comp_map_comp_eq_of_heq
          (ΘM := (s.baseChangeTwistPieceComparison (s.schemePointHom T f)
            (Px.alongPointToPoint f) rfl
            (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T f) i).hom)
          (ΘN := (s.baseChangeTwistPieceComparison (s.schemePointHom T f)
            (Px.alongPointToPoint f) rfl
            (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T f) j).hom)
          (s.baseChangeTwistPieceComparison_mul (s.schemePointHom T f)
            (Px.alongPointToPoint f) rfl _
            (s.liesOverAlong_pointChartMap Px T f) i j)
          rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
          HEq.rfl HEq.rfl))
    (s.fibreToSpaceHom T f) (s.twistAlgebraMul Px i j) (s.fibreToSpaceTwistModuleIso Px T f i).hom
    (s.fibreToSpaceTwistModuleIso Px T f j).hom (s.fibreToSpaceTwistModuleIso Px T f (i + j)).hom
    (representedTensorChartMul s.site s.base s.containsBase (s.twistPieceMul T f i j)) rfl rfl
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
    (heq_of_eq (congrArg Iso.hom (s.fibreToSpaceTwistModuleIso_eq Px T f i)).symm)
    (heq_of_eq (congrArg Iso.hom (s.fibreToSpaceTwistModuleIso_eq Px T f j)).symm)
    (heq_of_eq (congrArg Iso.hom (s.fibreToSpaceTwistModuleIso_eq Px T f (i + j))).symm) HEq.rfl

end Point

end RelativeProjSituation

end AlgebraicGeometry.Space

end
