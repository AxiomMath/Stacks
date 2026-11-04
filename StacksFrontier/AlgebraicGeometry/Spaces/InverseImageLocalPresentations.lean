module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpaceGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsAlongIso
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringSummandModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFree
public import StacksFrontier.Topology.Simplicial.QcComparisonSquare

/-!
# The inverse image of a quasi-coherent module is locally presented

Let `f : X ⟶ Y` be a morphism of algebraic spaces.  The quasi-coherent clause of Stacks 03DO,
read on the morphism of small étale ringed topoi of Stacks 03G8, factors through its
inverse-image half: the inverse image `f⁻¹F` of Stacks 03D2 of a quasi-coherent `𝒪_Y`-module is
locally presented as an `f⁻¹𝒪_Y`-module.  This is
`AlgebraicGeometry.Space.HasLocalInverseImagePresentations`, and this file proves it for every
morphism of algebraic spaces.

## The proof

The proof is the localization of `f` of Section 03DG, carried out on charts.  The étale charts
`W` of `X` for which the composite `W ⟶ X ⟶ Y` factors through an étale chart `V` of `Y` whose
underlying scheme is affine cover `X`
(`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`).  On such a `W`, with
`k : W ⟶ V` the factorization, four identifications of functors of sheaves of sets combine to
`AlgebraicGeometry.Space.inverseImageOverPullbackIso`:

* restriction to the slice `X_étale/W` is restriction to the chart space of `W` read through
  the comparison of Stacks 04M0 (`AlgebraicGeometry.Space.overPullbackIsoChartRestriction`);
* along the étale structure morphisms of the charts, the inverse image is restriction, by
  Stacks 03LQ (`AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso`);
* the inverse images of a composite are the composites of the inverse images, by uniqueness of
  left adjoints from Stacks 03G2, part (3)
  (`AlgebraicGeometry.Space.smallToposInverseImageCompIso`);
* the two composites `W ⟶ X ⟶ Y` and `W ⟶ V ⟶ Y` agree.

So `(f⁻¹F)|_W` is the transport of `F|_V` along the inverse image of a morphism of topoi, namely
of `k` followed by the comparison of Stacks 04M0.  By Stacks 03DX, `F|_V` has a presentation, and
the inverse image along a morphism of topoi carries presentations to presentations, being a left
adjoint that carries the structure sheaf to the structure sheaf.  What remains is bookkeeping of
the transported sheaves of rings, all of whose comparisons are isomorphisms, and along which
restriction of scalars carries presentations
(`Stacks.SheafOfModules.presentationRestrictScalars`).

## Main results

* `Stacks.SheafOfModules.presentationRestrictScalars` and
  `Stacks.SheafOfModules.presentationOfRestrictScalars`: presentations transport across
  restriction of scalars along an isomorphism of sheaves of rings.
* `AlgebraicGeometry.Space.nonempty_presentation_inverseImage_over`: the inverse image of a
  quasi-coherent module has a presentation on every chart of `X` whose composite to `Y` factors
  through an affine étale chart of `Y`.
* `AlgebraicGeometry.Space.hasLocalInverseImagePresentations`: **the inverse-image half of the
  quasi-coherent clause of Stacks 03DO**, for every morphism of algebraic spaces.  In particular
  `fun g ↦ hasLocalInverseImagePresentations B S hS g` is a term of the hypothesis
  `AlgebraicGeometry.Space.PullbackPreservesQuasicoherenceEverywhere` of
  `StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorSourceSheaf.lean`.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe v₁ u₁ w

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {R R' : Sheaf J RingCat.{w}}

/-- **A presentation is carried by restriction of scalars along an isomorphism of sheaves of
rings.**  Restriction of scalars along an isomorphism is an equivalence, hence preserves
colimits, and it carries the structure sheaf to the structure sheaf. -/
def presentationRestrictScalars (θ : R ≅ R') {M : _root_.SheafOfModules.{w} R'}
    (P : M.Presentation) :
    ((_root_.SheafOfModules.restrictScalars θ.hom).obj M).Presentation :=
  haveI : (_root_.SheafOfModules.restrictScalars.{w} θ.hom).IsEquivalence :=
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso θ).isEquivalence_inverse
  P.map (_root_.SheafOfModules.restrictScalars θ.hom)
    (Stacks.SheafOfModules.ChangeOfRings.unitRestrictScalarsIso θ.hom)

/-- **A presentation of a module read by restriction of scalars along an isomorphism is a
presentation of the module.** -/
def presentationOfRestrictScalars (θ : R ≅ R') {M : _root_.SheafOfModules.{w} R'}
    (P : ((_root_.SheafOfModules.restrictScalars θ.hom).obj M).Presentation) :
    M.Presentation :=
  (presentationRestrictScalars θ.symm P).ofIsIso
    ((Stacks.Sheaves.RingedPoint.sheafRestrictScalarsCompIsoId θ.hom θ.inv
      θ.inv_hom_id).hom.app M)

end Stacks.SheafOfModules

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (O : Sheaf K RingCat.{ww'})
  {Φ Φ' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)} [PreservesFiniteProducts Φ]
  [PreservesFiniteProducts Φ']

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Inverse images of sheaves of sets along composites -/

/-- **The inverse images of sheaves of sets along a composite**, for the morphisms of small
étale topoi of Stacks 03G2, part (3): `g⁻¹ ⋙ f⁻¹ ≅ (f ≫ g)⁻¹`.

Both are left adjoint to `f_* ⋙ g_*`, the right-hand side through the comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of the direct images. -/
def smallToposInverseImageCompIso {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallToposMorphismTypeU B S hS g).inverseImage ⋙
        (smallToposMorphismTypeU B S hS f).inverseImage ≅
      (smallToposMorphismTypeU B S hS (f ≫ g)).inverseImage :=
  (MorphismOfTopoi.comp (smallToposMorphismTypeU B S hS g)
      (smallToposMorphismTypeU B S hS f)).adj.leftAdjointUniq
    ((smallToposMorphismTypeU B S hS (f ≫ g)).adj.ofNatIsoRight
      (smallToposMorphismTypeU_comp B S hS f g).symm)

/-! ### The comparison of Stacks 04M0 for sheaves of sets at the universe of the rings -/

variable (X : AlgebraicSpaces B S hS)

/-- **Stacks 04M0 for sheaves of sets valued in `Type u`**: the sheaves on the slice of the small
étale site of `X` at an étale chart `W` are the sheaves on the small étale site of the chart
space of `W`. -/
def chartSliceSheafEquivTypeU (W : SmallEtale B S hS X.1) :
    Sheaf ((SmallEtale.topology B S hS X.1).over W) (Type u) ≌
      Sheaf (SmallEtale.topology B S hS (chartSpace B S hS X W).1) (Type u) :=
  haveI : (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).symm.inverse.IsDenseSubsite
      (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
      ((SmallEtale.topology B S hS X.1).over W) :=
    SmallEtale.isDenseSubsite_chartLocalization B S hS X.1 W
  Equivalence.sheafCongr ((SmallEtale.topology B S hS X.1).over W)
    (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).symm (Type u)

/-- The comparison of Stacks 04M0, followed by the slice projection, is postcomposition with the
structure morphism of the chart; after the inverse comparison it is the slice projection. -/
def chartLocalizationInverseComparison (W : SmallEtale B S hS X.1) :
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).inverse ⋙
        smallEtalePostcomp B S hS (chartToSpace B S hS X W) (isEtale_chartToSpace B S hS X W) ≅
      Over.forget W :=
  Functor.isoWhiskerRight (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).counitIso
      (Over.forget W) ≪≫ Functor.leftUnitor _

/-- **Restriction to a slice is restriction to the chart space**, read through the comparison
of Stacks 04M0: for an étale chart `W` of `X`, restricting a sheaf of sets to `X_étale/W` is
restricting it to the small étale site of the chart space of `W` and transporting it back. -/
def overPullbackIsoChartRestriction (W : SmallEtale B S hS X.1) :
    (SmallEtale.topology B S hS X.1).overPullback (Type u) W ≅
      smallEtaleSetRestriction B S hS (chartToSpace B S hS X W)
          (isEtale_chartToSpace B S hS X W) ⋙
        (chartSliceSheafEquivTypeU B S hS X W).inverse :=
  NatIso.ofComponents
    (fun G ↦ ObjectProperty.isoMk _ (Functor.isoWhiskerRight
      (NatIso.op (chartLocalizationInverseComparison B S hS X W)) G.obj))
    (fun φ ↦ ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U ↦ (φ.hom.naturality
      ((chartLocalizationInverseComparison B S hS X W).hom.app U.unop).op).symm)))

/-- The morphism of topoi `Sh(X_étale/W) ⟶ Sh(W_étale)` of the comparison of Stacks 04M0, whose
inverse image is the transport back to the slice. -/
abbrev chartSliceToposHom (W : SmallEtale B S hS X.1) :
    MorphismOfTopoi (Sheaf ((SmallEtale.topology B S hS X.1).over W) (Type u))
      (Sheaf (SmallEtale.topology B S hS (chartSpace B S hS X W).1) (Type u)) :=
  MorphismOfTopoi.ofEquivalence (chartSliceSheafEquivTypeU B S hS X W).symm

variable {X} {Y : AlgebraicSpaces B S hS}

/-- **The localization of `f` at a chart diagram**: the morphism of topoi
`Sh(X_étale/W) ⟶ Sh(V_étale)` attached to an étale chart `W` of `X`, an étale chart `V` of `Y`
and a morphism `q : W ⟶ V` over `f`, namely the morphism of small étale topoi of the represented
morphism `W ⟶ V` of chart spaces, preceded by the comparison of Stacks 04M0. -/
abbrev localizedToposHom {W : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    (q : W.1.left ⟶ V.1.left) :
    MorphismOfTopoi (Sheaf ((SmallEtale.topology B S hS X.1).over W) (Type u))
      (Sheaf (SmallEtale.topology B S hS (chartSpace B S hS Y V).1) (Type u)) :=
  MorphismOfTopoi.comp (smallToposMorphismTypeU B S hS (chartSpaceMapOver B S hS q))
    (chartSliceToposHom B S hS X W)

/-- **The inverse image of `f`, restricted to a chart, is the localized inverse image of the
restriction.**  For an étale chart `W` of `X`, an étale chart `V` of `Y` and `q : W ⟶ V` over
`f`, restricting `f⁻¹G` to the slice `X_étale/W` is restricting `G` to the chart space of `V` and
taking the inverse image along `AlgebraicGeometry.Space.localizedToposHom`. -/
def inverseImageOverPullbackIso (f : X ⟶ Y) {W : SmallEtale B S hS X.1}
    {V : SmallEtale B S hS Y.1} (q : W.1.left ⟶ V.1.left)
    (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ f.hom) :
    (smallToposMorphismTypeU B S hS f).inverseImage ⋙
        (SmallEtale.topology B S hS X.1).overPullback (Type u) W ≅
      smallEtaleSetRestriction B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V) ⋙
        (localizedToposHom B S hS q).inverseImage :=
  let T := (chartSliceSheafEquivTypeU B S hS X W).inverse
  let fi := (smallToposMorphismTypeU B S hS f).inverseImage
  let ki := (smallToposMorphismTypeU B S hS (chartSpaceMapOver B S hS q)).inverseImage
  have hk : chartSpaceMapOver B S hS q ≫ chartToSpace B S hS Y V =
      chartToSpace B S hS X W ≫ f :=
    chartSpaceMapOver_comp_chartToSpace B S hS f q hq
  Functor.isoWhiskerLeft fi (overPullbackIsoChartRestriction B S hS X W) ≪≫
    (Functor.associator fi _ T).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft fi
      (smallToposMorphismTypeU_inverseImageIso B S hS (chartToSpace B S hS X W)
        (isEtale_chartToSpace B S hS X W)).symm) T ≪≫
    Functor.isoWhiskerRight (smallToposInverseImageCompIso B S hS (chartToSpace B S hS X W) f)
      T ≪≫
    Functor.isoWhiskerRight (eqToIso (congrArg
      (fun m ↦ (smallToposMorphismTypeU B S hS m).inverseImage) hk.symm)) T ≪≫
    Functor.isoWhiskerRight (smallToposInverseImageCompIso B S hS (chartSpaceMapOver B S hS q)
      (chartToSpace B S hS Y V)).symm T ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (smallToposMorphismTypeU_inverseImageIso B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)) ki) T ≪≫
    Functor.associator _ ki T

/-! ### Presentations of the inverse image on charts -/

/-- **The inverse image of a quasi-coherent module is presented on a chart carrying an affine
chart diagram.**  For an étale chart `W` of `X`, an étale chart `V` of `Y` whose underlying
scheme is affine and `q : W ⟶ V` over `f`, the restriction of `f⁻¹F` to the slice `X_étale/W`
has a presentation over `f⁻¹𝒪_Y`.

The restriction is the inverse image of `F|_V` along the localization of `f`
(`AlgebraicGeometry.Space.inverseImageOverPullbackIso`), `F|_V` has a presentation by
Stacks 03DX, and the inverse image along a morphism of topoi carries presentations; the rest is
the comparison of the transported sheaves of rings. -/
theorem nonempty_presentation_inverseImage_over (f : X ⟶ Y) {W : SmallEtale B S hS X.1}
    {V : SmallEtale B S hS Y.1} (q : W.1.left ⟶ V.1.left)
    (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ f.hom)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)))
    (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite) :
    Nonempty ((restrictionModules ((SmallEtale.topology B S hS X.1).over W)
      (SmallEtale.topology B S hS X.1) (Over.forget W)
      (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
        (smallToposMorphismTypeU B S hS f).inverseImage (structureRingSheaf B S hS Y))).obj
      ((pullbackModuleFunctor.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
        (smallToposMorphismTypeU B S hS f).inverseImage (structureRingSheaf B S hS Y)).obj
          F)).Presentation := by
  let O := structureRingSheaf B S hS Y
  let φV := chartToSpace B S hS Y V
  let hφV := isEtale_chartToSpace B S hS Y V
  let JX := SmallEtale.topology B S hS X.1
  let JY := SmallEtale.topology B S hS Y.1
  let JcV := SmallEtale.topology B S hS (chartSpace B S hS Y V).1
  let resV := smallEtaleSetRestriction B S hS φV hφV
  let L := localizedToposHom B S hS q
  have := L.preservesFiniteLimits
  obtain ⟨Pc⟩ := nonempty_presentation_modulePullback_chartToSpace_of_isAffine B S hS Y F hF V hV
  let Pe : ((etaleModulePullback B S hS φV hφV).obj F).Presentation :=
    Pc.ofIsIso ((modulePullbackIsoEtaleModulePullback B S hS φV hφV).app F).hom
  let P0 : ((pullbackModuleFunctor.{u, u, u, u + 1, u, u + 1} JcV resV O).obj F).Presentation :=
    (Stacks.SheafOfModules.presentationRestrictScalars
      (restrictionRingIso JcV JY (smallEtalePostcomp B S hS φV hφV) O) Pe).ofIsIso
      ((restrictionModuleIso JcV JY (smallEtalePostcomp B S hS φV hφV) O).app F).inv
  let RV := pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} JcV resV O
  have : PreservesColimitsOfSize.{u, u} (inverseImageModules L RV) :=
    (inverseImageAdjDirectImageModules L RV).leftAdjoint_preservesColimits
  let P1 := P0.map (inverseImageModules L RV) (pullbackModuleUnitIso (JX.over W) L.inverseImage RV)
  let c1 := pullbackRingSheafCompIso (JX.over W) JcV L.inverseImage resV O
  let i1 := (pullbackModuleCompIso (JX.over W) JcV L.inverseImage resV O).app F
  let P2 := Stacks.SheafOfModules.presentationOfRestrictScalars c1 (P1.ofIsIso i1.hom)
  let Θ := inverseImageOverPullbackIso B S hS f q hq
  let βI := pullbackRingSheafIsoOfNatIso (JX.over W) O Θ
  let i2 := (pullbackModuleFunctorIsoOfNatIso (JX.over W) O Θ βI.hom
    (ringSheafMap_pullbackRingSheafMapOfNatTrans (JX.over W) O Θ.hom)).app F
  let P3 := (Stacks.SheafOfModules.presentationRestrictScalars βI P2).ofIsIso i2.inv
  let fi := (smallToposMorphismTypeU B S hS f).inverseImage
  let c2 := pullbackRingSheafCompIso (JX.over W) JX (JX.overPullback (Type u) W) fi O
  let i3 := (pullbackModuleCompIso (JX.over W) JX (JX.overPullback (Type u) W) fi O).app F
  let P4 := (Stacks.SheafOfModules.presentationRestrictScalars c2 P3).ofIsIso i3.inv
  let RX := pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} JX fi O
  let i4 := (restrictionModuleIso (JX.over W) JX (Over.forget W) RX).app
    ((pullbackModuleFunctor.{u, u, u, u + 1, u, u + 1} JX fi O).obj F)
  exact ⟨Stacks.SheafOfModules.presentationOfRestrictScalars
    (restrictionRingIso (JX.over W) JX (Over.forget W) RX) (P4.ofIsIso i4.hom)⟩

/-- A presentation of the restriction along the slice projection is a presentation of the
restriction to the slice. -/
theorem nonempty_presentation_over_of_restrictionModules {X : AlgebraicSpaces B S hS}
    {R : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}} (W : SmallEtale B S hS X.1)
    (M : SheafOfModules.{u} R)
    (h : Nonempty ((restrictionModules ((SmallEtale.topology B S hS X.1).over W)
      (SmallEtale.topology B S hS X.1) (Over.forget W) R).obj M).Presentation) :
    Nonempty (M.over W).Presentation :=
  h

/-- **The inverse-image half of the quasi-coherent clause of Stacks 03DO**, for an arbitrary
morphism `f : X ⟶ Y` of algebraic spaces: the inverse image `f⁻¹F` of a quasi-coherent
`𝒪_Y`-module is locally presented as an `f⁻¹𝒪_Y`-module on the small étale site of `X`.

Over an étale chart `U` of `X`, the charts `W ⟶ U` whose composite to `Y` factors through an
affine étale chart of `Y` form a covering sieve
(`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`), and on each of them `f⁻¹F`
is presented by `AlgebraicGeometry.Space.nonempty_presentation_inverseImage_over`. -/
theorem hasLocalInverseImagePresentations (f : X ⟶ Y) :
    HasLocalInverseImagePresentations B S hS f := by
  intro F hF U
  let R : Sieve U :=
    { arrows := fun W _ ↦ ∃ (V : SmallEtale B S hS Y.1) (q : W.1.left ⟶ V.1.left),
        yoneda.map q ≫ V.1.hom = W.1.hom ≫ f.hom ∧
          IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V))
      downward_closed := by
        rintro W W' a ⟨V, q, hq, hV⟩ b
        refine ⟨V, b.hom.left ≫ q, ?_, hV⟩
        rw [Functor.map_comp, Category.assoc, hq, ← Category.assoc, CostructuredArrow.w] }
  exact ⟨⟨R, mem_topology_of_hasAffineChartDiagram B S hS f U R fun _ _ hW ↦ hW.2⟩,
    fun W _ ⟨_, q, hq, hV⟩ ↦ nonempty_presentation_over_of_restrictionModules B S hS W _
      (nonempty_presentation_inverseImage_over B S hS f q hq hV F hF)⟩

end AlgebraicGeometry.Space

end
