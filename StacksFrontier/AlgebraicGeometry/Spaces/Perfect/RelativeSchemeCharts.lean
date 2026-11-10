module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleInDimensionsGE
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedRelativePerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectAffineSections
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDerivedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InverseImageSliceTensor

/-!
# Relative perfectness of algebraic spaces read on scheme charts

Let `f : X ⟶ Y` be a morphism of algebraic spaces which is flat and locally of finite
presentation, and let `E ∈ D_QCoh(𝒪_X)`. For a commutative square of étale scheme charts
`U ⟶ V` over `f`, the restriction `E|_U` corresponds under Stacks 071Q to the object
`E_0 = Rε_*(E|_U)` of `D_QCoh(𝒪_{U_0})`, and `E` is `Y`-perfect exactly when every such `E_0`
is `V_0`-perfect in the sense of schemes, exactly when one such `E_0` is for a square whose
chart of `X` is surjective, exactly when `RΓ(U, E)` is `𝒪_Y(V)`-perfect on every such square
with `U` and `V` affine.

## Main results

* `AlgebraicGeometry.Space.chartObject`: the object `E_0` of a chart square.
* `AlgebraicGeometry.Space.isPerfectRelativeTo_chartObject_of_isPerfectRelativeToCanonical`
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_isPerfectRelativeTo_chartObject`
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_tfae_chartDiagram`: **Stacks 0DKQ**.

## References

* [Stacks Project, Tag 0DKQ](https://stacks.math.columbia.edu/tag/0DKQ)
-/

@[expose] public noncomputable section

attribute [local instance] AlgebraicGeometry.Space.sheafTensor_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.sheafTensor_obj_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_inverseImageRingedSite_over

attribute [local instance] AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y)

/-- The tensor bifunctor on a slice of the inverse-image ringed site of the represented morphism
of a chart diagram is additive. -/
local instance sheafTensor_additive_chartDiagram (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (U : (inverseImageRingedSite B S hS (representedSpaceMap B S hS d.g)).C) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((inverseImageRingedSite B S hS (representedSpaceMap B S hS d.g)).over U).O).Additive :=
  sheafTensor_additive_inverseImageRingedSite_over _ U

/-- The tensor product with a fixed module on a slice of the inverse-image ringed site of the
represented morphism of a chart diagram is additive. -/
local instance sheafTensor_obj_additive_chartDiagram (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (U : (inverseImageRingedSite B S hS (representedSpaceMap B S hS d.g)).C)
    (M : RingedSite.Modules.{u + 1, u, u}
      ((inverseImageRingedSite B S hS (representedSpaceMap B S hS d.g)).over U)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((inverseImageRingedSite B S hS (representedSpaceMap B S hS d.g)).over U).O).obj
        M).Additive :=
  sheafTensor_obj_additive_inverseImageRingedSite_over _ U M

/-- The total tensor complexes on a slice of the inverse-image ringed site of the represented
morphism of a chart diagram exist. -/
local instance hasMapBifunctor_sheafTensor_chartDiagram (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (U : (inverseImageRingedSite B S hS (representedSpaceMap B S hS d.g)).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u}
      ((inverseImageRingedSite B S hS (representedSpaceMap B S hS d.g)).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS (representedSpaceMap B S hS d.g)).over U).O)
      (ComplexShape.up ℤ) :=
  hasMapBifunctor_sheafTensor_inverseImageRingedSite_over _ U K L

/-- The morphism of schemes underlying a square of étale scheme charts of a flat morphism of
algebraic spaces is flat (Stacks 03ML). -/
theorem flat_chartDiagram_g (hfl : IsFlat B S hS f.hom) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    Flat ((BigFppfOver.toScheme B S hS).map d.g) :=
  hfl _ _ d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm

/-- The morphism of schemes underlying a square of étale scheme charts of a morphism of algebraic
spaces locally of finite presentation is locally of finite presentation (Stacks 03XP). -/
theorem locallyOfFinitePresentation_chartDiagram_g
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map d.g) :=
  hlfp _ _ d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm

/-- The square of algebraic spaces underlying a square of étale scheme charts commutes. -/
theorem chartToSpace_comp_eq (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    chartToSpace B S hS X d.U ≫ f = representedSpaceMap B S hS d.g ≫ chartToSpace B S hS Y d.V :=
  ObjectProperty.hom_ext _ d.comm

/-- **The object `E_0` of a square of étale scheme charts.** For a chart `U` of `X`, the object
`Rε_*(E|_U)` of `D(𝒪_{U_0})`, which corresponds to `E|_U` under Stacks 071Q. -/
abbrev chartObject (U : SmallEtale B S hS X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    DerivedCategory (representedSchemeRepresentedZariskiRingedToposHom B S hS
      ((SmallEtale.toOver B S hS X.1).obj U)).Modules :=
  (representedZariskiDerivedPushforward B S hS ((SmallEtale.toOver B S hS X.1).obj U)).obj
    ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X U)).obj E)

/-- For `E ∈ D_QCoh(𝒪_X)`, the counit `Lε^* Rε_*(E|_U) ⟶ E|_U` is an isomorphism. -/
def chartObjectIso (U : SmallEtale B S hS X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E) :
    (representedZariskiDerivedPullback B S hS ((SmallEtale.toOver B S hS X.1).obj U)).obj
        (chartObject U E) ≅
      (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X U)).obj E :=
  have := isIso_representedZariskiDerivedAdjunction_counit_app B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)
    ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X U)).obj E)
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (chartToSpace B S hS X U) E hE)
  asIso ((representedZariskiDerivedAdjunction B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).counit.app
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X U)).obj E))

variable (hfl : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)

/-- Relative perfectness is invariant under isomorphism. -/
theorem isPerfectRelativeToCanonical_of_iso {K L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)}
    (e : K ≅ L) (h : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp K) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp L :=
  (isClosedUnderIsomorphisms_isPerfectRelativeToCanonical B S hS f hfl hlfp).of_iso e h

/-- On a square of étale scheme charts, `E|_U` is `V`-perfect along the represented morphism
exactly when `E_0` is `V_0`-perfect in the sense of schemes. -/
theorem isPerfectRelativeToCanonical_chart_iff (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS (representedSpaceMap B S hS d.g)
        (isFlat_yoneda_map B S hS d.g (flat_chartDiagram_g f hfl d))
        (isLocallyOfFinitePresentation_yoneda_map B S hS d.g
          (locallyOfFinitePresentation_chartDiagram_g f hlfp d))
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X d.U)).obj E) ↔
      haveI := flat_chartDiagram_g f hfl d
      haveI := locallyOfFinitePresentation_chartDiagram_g f hlfp d
      ((BigFppfOver.toScheme B S hS).map d.g).IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u}
          (RingedSpace.inverseImage
            (representedSchemeRepresentedZariskiRingedToposHom B S hS
              ((SmallEtale.toOver B S hS Y.1).obj d.V)).toRingedSpace
            ((BigFppfOver.toScheme B S hS).map d.g).base))
        (chartObject d.U E) := by
  have := flat_chartDiagram_g f hfl d
  have := locallyOfFinitePresentation_chartDiagram_g f hlfp d
  refine Iff.trans ?_ (isPerfectRelativeToCanonical_representedZariskiDerivedPullback_iff d.g
    (isFlat_yoneda_map B S hS d.g (flat_chartDiagram_g f hfl d))
    (isLocallyOfFinitePresentation_yoneda_map B S hS d.g
      (locallyOfFinitePresentation_chartDiagram_g f hlfp d)) (chartObject d.U E))
  exact ⟨isPerfectRelativeToCanonical_of_iso _ _ _ (chartObjectIso d.U E hE).symm,
    isPerfectRelativeToCanonical_of_iso _ _ _ (chartObjectIso d.U E hE)⟩

/-- **(1) ⇒ (2) of Stacks 0DKQ.** If `E ∈ D_QCoh(𝒪_X)` is `Y`-perfect, then for every square of
étale scheme charts `U ⟶ V` over `f` the object `E_0` of `D(𝒪_{U_0})` is `V_0`-perfect. -/
theorem isPerfectRelativeTo_chartObject_of_isPerfectRelativeToCanonical
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E)
    (hK : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp E)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    haveI := flat_chartDiagram_g f hfl d
    haveI := locallyOfFinitePresentation_chartDiagram_g f hlfp d
    ((BigFppfOver.toScheme B S hS).map d.g).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u}
        (RingedSpace.inverseImage
          (representedSchemeRepresentedZariskiRingedToposHom B S hS
            ((SmallEtale.toOver B S hS Y.1).obj d.V)).toRingedSpace
          ((BigFppfOver.toScheme B S hS).map d.g).base))
      (chartObject d.U E) :=
  (isPerfectRelativeToCanonical_chart_iff f hfl hlfp d E hE).1
    (isPerfectRelativeToCanonical_smallEtaleDerivedModulePullback_of_isEtale
      (chartToSpace B S hS X d.U) (representedSpaceMap B S hS d.g) f (chartToSpace B S hS Y d.V)
      hfl hlfp _ _ (isEtale_chartToSpace B S hS X d.U) (isEtale_chartToSpace B S hS Y d.V)
      (chartToSpace_comp_eq f d) E hK)

/-- **(3) ⇒ (1) of Stacks 0DKQ.** If for one square of étale scheme charts `U ⟶ V` over `f` whose
chart of `X` is surjective the object `E_0` is `V_0`-perfect, then `E ∈ D_QCoh(𝒪_X)` is
`Y`-perfect. -/
theorem isPerfectRelativeToCanonical_of_isPerfectRelativeTo_chartObject
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (hsurj : IsSurjective B S hS d.U.1.hom)
    (h : haveI := flat_chartDiagram_g f hfl d
      haveI := locallyOfFinitePresentation_chartDiagram_g f hlfp d
      ((BigFppfOver.toScheme B S hS).map d.g).IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u}
          (RingedSpace.inverseImage
            (representedSchemeRepresentedZariskiRingedToposHom B S hS
              ((SmallEtale.toOver B S hS Y.1).obj d.V)).toRingedSpace
            ((BigFppfOver.toScheme B S hS).map d.g).base))
        (chartObject d.U E)) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp E :=
  isPerfectRelativeToCanonical_of_isEtale_of_isSurjective
    (chartToSpace B S hS X d.U) (representedSpaceMap B S hS d.g) f (chartToSpace B S hS Y d.V)
    hfl hlfp _ _ (isEtale_chartToSpace B S hS X d.U) hsurj (isEtale_chartToSpace B S hS Y d.V)
    (chartToSpace_comp_eq f d) E ((isPerfectRelativeToCanonical_chart_iff f hfl hlfp d E hE).2 h)

omit hfl hlfp in
/-- The object `E_0` of a chart has quasi-coherent cohomology sheaves. -/
theorem isQuasicoherent_homology_chartObject (U : SmallEtale B S hS X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E) (q : ℤ) :
    ((DerivedCategory.homologyFunctor _ q).obj (chartObject U E)).IsQuasicoherent :=
  isQuasicoherent_homology_representedZariskiDerivedPushforward_obj B S hS _ _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (chartToSpace B S hS X U) E hE) q

/-- **(2) ⇔ (4) of Stacks 0DKQ on one affine square.** For a square of étale scheme charts
`U ⟶ V` over `f` with `U` and `V` affine, `E_0` is `V_0`-perfect exactly when `RΓ(U, E)` is
`𝒪_Y(V)`-perfect: pseudo-coherent over `Γ(U, 𝒪_U)` and of finite Tor dimension over
`Γ(V, 𝒪_V)`. -/
theorem isPerfectRelativeTo_chartObject_iff_of_isAffine (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj d.U))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj d.V))]
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E) :
    (haveI := flat_chartDiagram_g f hfl d;
      haveI := locallyOfFinitePresentation_chartDiagram_g f hlfp d
      ((BigFppfOver.toScheme B S hS).map d.g).IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u}
          (RingedSpace.inverseImage
            (representedSchemeRepresentedZariskiRingedToposHom B S hS
              ((SmallEtale.toOver B S hS Y.1).obj d.V)).toRingedSpace
            ((BigFppfOver.toScheme B S hS).map d.g).base))
        (chartObject d.U E)) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj d.U)).obj
            ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X d.U)).obj E)) ∧
        StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical
          Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj d.V), ⊤)
          ((ModuleCat.restrictScalars
            ((BigFppfOver.toScheme B S hS).map d.g).appTop.hom).mapDerivedCategory.obj
            ((representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj d.U)).obj
              ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X d.U)).obj E))) := by
  have := flat_chartDiagram_g f hfl d
  have := locallyOfFinitePresentation_chartDiagram_g f hlfp d
  obtain ⟨e⟩ := nonempty_representedAffineDerivedSections_representedZariskiDerivedPullback_iso
    ((SmallEtale.toOver B S hS X.1).obj d.U) (chartObject d.U E)
    (isQuasicoherent_homology_chartObject d.U E hE)
  let e' := (representedAffineDerivedSections B S hS
      ((SmallEtale.toOver B S hS X.1).obj d.U)).mapIso (chartObjectIso d.U E hE).symm ≪≫ e
  refine ((BigFppfOver.toScheme B S hS).map d.g).isPerfectRelativeTo_iff_derivedSections_of_isAffine
    (chartObject d.U E) (isQuasicoherent_homology_chartObject d.U E hE) |>.trans
    (and_congr ⟨fun h => h.ofIso e'.symm, fun h => h.ofIso e'⟩ ?_)
  have key : ∀ {K L : DerivedCategory (ModuleCat.{u}
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj d.V), ⊤))},
      (K ≅ L) → StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical _ K →
        StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical _ L := fun e h =>
    (StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical
      _ _).2
      (((StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical
      _ _).1 h).imp fun a => Exists.imp fun b hab =>
        AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b hab)
  exact ⟨key ((ModuleCat.restrictScalars
      ((BigFppfOver.toScheme B S hS).map d.g).appTop.hom).mapDerivedCategory.mapIso e'.symm),
    key ((ModuleCat.restrictScalars
      ((BigFppfOver.toScheme B S hS).map d.g).appTop.hom).mapDerivedCategory.mapIso e')⟩

omit hfl hlfp in
/-- **Affine squares of étale scheme charts pass through every point.** For every point `x` of
`|X|` there is a square of étale scheme charts `U ⟶ V` over `f` with `U` and `V` affine and `x`
in the image of `U`: restrict a square whose chart of `X` is surjective to an affine open
neighbourhood of a point over `x`, inside the inverse image of an affine open of `V`. -/
theorem exists_affine_chartDiagram (x : points B S hS X.1) :
    ∃ d : ChartDiagram B S hS X.1 Y.1 f.hom,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj d.U)) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj d.V)) ∧
          ∃ y : points B S hS (chartSpace B S hS X d.U).1,
            pointsMap B S hS _ (chartToSpace B S hS X d.U).hom y = x := by
  obtain ⟨d₀, hsurj, -⟩ := exists_surjective_chartDiagram B S hS f
  obtain ⟨y₀, hy₀⟩ := hsurj x
  set u := pointsToScheme B S hS d₀.U.obj.left y₀
  set g₀ := (BigFppfOver.toScheme B S hS).map d₀.g
  obtain ⟨V', hV', hgu, -⟩ := exists_isAffineOpen_mem_and_subset (x := g₀ u)
    (U := (⊤ : (etaleChartScheme B S hS d₀.V).Opens)) trivial
  obtain ⟨U', hU', huU', hU'le'⟩ := exists_isAffineOpen_mem_and_subset (x := u)
    (U := g₀ ⁻¹ᵁ V') hgu
  have hU'le : U' ≤ g₀ ⁻¹ᵁ V' := hU'le'
  let g' : chartOpenOver B S hS d₀.U U' ⟶ chartOpenOver B S hS d₀.V V' :=
    Over.homMk (ObjectProperty.homMk (g₀.resLE V' U' hU'le)) (by
      apply ObjectProperty.hom_ext
      change g₀.resLE V' U' hU'le ≫ V'.ι ≫ _ = U'.ι ≫ _
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
      exact congrArg (U'.ι ≫ ·) (congrArg (fun φ => φ.hom) (Over.w d₀.g)))
  have hg' : g' ≫ chartOpenOverι B S hS d₀.V V' = chartOpenOverι B S hS d₀.U U' ≫ d₀.g :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.Hom.resLE_comp_ι _ _))
  refine ⟨⟨(chartOpens B S hS d₀.U).obj U', (chartOpens B S hS d₀.V).obj V', g', ?_⟩, hU', hV',
    ?_⟩
  · change (yoneda.map (chartOpenOverι B S hS d₀.U U') ≫ d₀.U.obj.hom) ≫ f.hom =
      yoneda.map g' ≫ yoneda.map (chartOpenOverι B S hS d₀.V V') ≫ d₀.V.obj.hom
    rw [Category.assoc, d₀.comm, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, hg']
  · refine ⟨(pointsEquivScheme B S hS (chartOpenOver B S hS d₀.U U')).symm ⟨u, huU'⟩, ?_⟩
    change pointsMap B S hS _ (yoneda.map (chartOpenOverι B S hS d₀.U U') ≫ d₀.U.obj.hom) _ = x
    rw [pointsMap_comp, Function.comp_apply, ← hy₀]
    congr 1
    apply injective_pointsToScheme B S hS
    rw [pointsToScheme_pointsMap_yoneda]
    change (BigFppfOver.toScheme B S hS).map (chartOpenOverι B S hS d₀.U U')
      ((pointsEquivScheme B S hS (chartOpenOver B S hS d₀.U U')) _) = u
    rw [(pointsEquivScheme B S hS (chartOpenOver B S hS d₀.U U')).apply_symm_apply ⟨u, huU'⟩]
    rfl

/-- **(3) ⇒ (1) of Stacks 0DKQ**, in the existential form. -/
theorem isPerfectRelativeToCanonical_of_exists_chartDiagram
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E)
    (h : ∃ d : ChartDiagram B S hS X.1 Y.1 f.hom, IsSurjective B S hS d.U.1.hom ∧
      haveI := flat_chartDiagram_g f hfl d
      haveI := locallyOfFinitePresentation_chartDiagram_g f hlfp d
      ((BigFppfOver.toScheme B S hS).map d.g).IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u}
          (RingedSpace.inverseImage
            (representedSchemeRepresentedZariskiRingedToposHom B S hS
              ((SmallEtale.toOver B S hS Y.1).obj d.V)).toRingedSpace
            ((BigFppfOver.toScheme B S hS).map d.g).base))
        (chartObject d.U E)) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp E := by
  obtain ⟨d, hd, h⟩ := h
  exact isPerfectRelativeToCanonical_of_isPerfectRelativeTo_chartObject f hfl hlfp E hE d hd h

/-- **(4) ⇒ (1) of Stacks 0DKQ.** If `RΓ(U, E)` is `𝒪_Y(V)`-perfect for every square of étale
scheme charts `U ⟶ V` over `f` with `U` and `V` affine, then `E ∈ D_QCoh(𝒪_X)` is `Y`-perfect:
such squares pass through every point of `|X|`, and on each of them `E|_U` is `V`-perfect. -/
theorem isPerfectRelativeToCanonical_of_forall_isAffine_chartDiagram
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E)
    (h : ∀ (d : ChartDiagram B S hS X.1 Y.1 f.hom)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj d.U))]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj d.V))],
      StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj d.U)).obj
            ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X d.U)).obj E)) ∧
        StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical
          Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj d.V), ⊤)
          ((ModuleCat.restrictScalars
            ((BigFppfOver.toScheme B S hS).map d.g).appTop.hom).mapDerivedCategory.obj
            ((representedAffineDerivedSections B S hS
              ((SmallEtale.toOver B S hS X.1).obj d.U)).obj
              ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X d.U)).obj E)))) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp E := by
  refine isPerfectRelativeToCanonical_of_forall_isEtale f hfl hlfp
    (ι := {d : ChartDiagram B S hS X.1 Y.1 f.hom //
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj d.U)) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj d.V))})
    (fun d => chartToSpace B S hS X d.1.U) (fun d => representedSpaceMap B S hS d.1.g)
    (fun d => chartToSpace B S hS Y d.1.V)
    (fun d => isFlat_yoneda_map B S hS d.1.g (flat_chartDiagram_g f hfl d.1))
    (fun d => isLocallyOfFinitePresentation_yoneda_map B S hS d.1.g
      (locallyOfFinitePresentation_chartDiagram_g f hlfp d.1))
    (fun d => isEtale_chartToSpace B S hS X d.1.U) (fun x => ?_)
    (fun d => isEtale_chartToSpace B S hS Y d.1.V) (fun d => chartToSpace_comp_eq f d.1) E
    (fun d => ?_)
  · obtain ⟨d, hU, hV, y, hy⟩ := exists_affine_chartDiagram f x
    exact ⟨⟨d, hU, hV⟩, y, hy⟩
  · obtain ⟨d, hU, hV⟩ := d
    exact (isPerfectRelativeToCanonical_chart_iff f hfl hlfp d E hE).2
      ((isPerfectRelativeTo_chartObject_iff_of_isAffine f hfl hlfp d E hE).2 (h d))

/-- **Relative perfectness of algebraic spaces read on scheme charts.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces which is flat and locally of finite presentation, and let
`E ∈ D_QCoh(𝒪_X)`. For a commutative square of étale scheme charts `U ⟶ V` over `f`, write `E_0`
for the object `Rε_*(E|_U)` of `D_QCoh(𝒪_{U_0})` corresponding to `E|_U` (Stacks 071Q). The
following are equivalent:
1. `E` is `Y`-perfect;
2. for every such square, `E_0` is `V_0`-perfect in the sense of schemes;
3. for some such square whose chart of `X` is surjective, `E_0` is `V_0`-perfect;
4. for every such square with `U` and `V` affine, `RΓ(U, E)` is `𝒪_Y(V)`-perfect, that is,
   pseudo-coherent over `Γ(U, 𝒪_U)` and of finite Tor dimension over `Γ(V, 𝒪_V)`. -/
@[stacks 0DKQ]
theorem isPerfectRelativeToCanonical_tfae_chartDiagram
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E) :
    List.TFAE
      [IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp E,
        ∀ d : ChartDiagram B S hS X.1 Y.1 f.hom,
          haveI := flat_chartDiagram_g f hfl d
          haveI := locallyOfFinitePresentation_chartDiagram_g f hlfp d
          ((BigFppfOver.toScheme B S hS).map d.g).IsPerfectRelativeTo
            (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u}
              (RingedSpace.inverseImage
                (representedSchemeRepresentedZariskiRingedToposHom B S hS
                  ((SmallEtale.toOver B S hS Y.1).obj d.V)).toRingedSpace
                ((BigFppfOver.toScheme B S hS).map d.g).base))
            (chartObject d.U E),
        ∃ d : ChartDiagram B S hS X.1 Y.1 f.hom, IsSurjective B S hS d.U.1.hom ∧
          haveI := flat_chartDiagram_g f hfl d
          haveI := locallyOfFinitePresentation_chartDiagram_g f hlfp d
          ((BigFppfOver.toScheme B S hS).map d.g).IsPerfectRelativeTo
            (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u}
              (RingedSpace.inverseImage
                (representedSchemeRepresentedZariskiRingedToposHom B S hS
                  ((SmallEtale.toOver B S hS Y.1).obj d.V)).toRingedSpace
                ((BigFppfOver.toScheme B S hS).map d.g).base))
            (chartObject d.U E),
        ∀ (d : ChartDiagram B S hS X.1 Y.1 f.hom)
          [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj d.U))]
          [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj d.V))],
          StacksDraft.PseudoCoherence.IsPseudoCoherent
              ((representedAffineDerivedSections B S hS
                ((SmallEtale.toOver B S hS X.1).obj d.U)).obj
                ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X d.U)).obj E)) ∧
            StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical
              Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj d.V), ⊤)
              ((ModuleCat.restrictScalars
                ((BigFppfOver.toScheme B S hS).map d.g).appTop.hom).mapDerivedCategory.obj
                ((representedAffineDerivedSections B S hS
                  ((SmallEtale.toOver B S hS X.1).obj d.U)).obj
                  ((smallEtaleDerivedModulePullback B S hS
                    (chartToSpace B S hS X d.U)).obj E)))] := by
  tfae_have 1 → 2 := fun h d =>
    isPerfectRelativeTo_chartObject_of_isPerfectRelativeToCanonical f hfl hlfp E hE h d
  tfae_have 2 → 3 := fun h => by
    obtain ⟨d, hd, -⟩ := exists_surjective_chartDiagram B S hS f
    exact ⟨d, hd, h d⟩
  tfae_have 3 → 1 := isPerfectRelativeToCanonical_of_exists_chartDiagram f hfl hlfp E hE
  tfae_have 2 → 4 := fun h d _ _ =>
    (isPerfectRelativeTo_chartObject_iff_of_isAffine f hfl hlfp d E hE).1 (h d)
  tfae_have 4 → 1 :=
    isPerfectRelativeToCanonical_of_forall_isAffine_chartDiagram f hfl hlfp E hE
  tfae_finish

end AlgebraicGeometry.Space

end
