module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtCompactSet
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartZeroLocusEndgame
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRingLevelZeroLocusOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapRingLevelZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapTargetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapZeroLocusSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedEtaleLocalDescent
public import StacksCore.Tactic.StacksAttribute

/-!
# Limit preservation of the vanishing locus of a map of quasi-coherent modules

In the situation of Stacks 083F — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
and a map `u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules — clause (2) of Stacks 083J asserts that
the vanishing locus `F_zero` is limit preserving when `ℱ` is of finite type with
scheme-theoretic support quasi-compact over `B`. This file proves clause (2) from the chart case
at the affine stages, transports it to relative limit preservation of the inclusion of the
vanishing subfunctor of `Y`, and deduces the finite-presentation clause of Stacks 0CWC.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.HasAffineChartZeroDescent`: the chart case of
  clause (2): limit preservation of the vanishing locus of `g^*u` for every flat morphism `g` from
  an affine scheme whose image contains the support of `ℱ`.
* `AlgebraicGeometry.Space.ModuleMapSituation.HasAffineStageChartZeroDescent`: the chart case
  for the situation base changed to each affine test scheme.
* `AlgebraicGeometry.Space.ModuleMapSituation.HasQuasiCompactSupportOverTarget`: the inverse
  image of the support of `ℱ` in `X ×_Y T` is compact for every affine test scheme `T`.
* `AlgebraicGeometry.Space.ModuleMapSituation.overTargetSection`,
  `AlgebraicGeometry.Space.ModuleMapSituation.stageDiagram`,
  `AlgebraicGeometry.Space.ModuleMapSituation.stageCone`: a test scheme over a stage `T₀` as a
  test scheme of the situation base changed to `T₀`, and the diagram and cone of the stages of a
  cofiltered diagram over a chosen stage.
* `AlgebraicGeometry.Space.ModuleMapSituation.zeroDiagram`: a diagram of objects of the big fppf
  category over `U` as a diagram of test schemes, along a section of `Y` over `U`.

## Main results

* `ModuleMapSituation.limitPreserving_zeroFunctor_of_hasQuasiCompactSupportOverTarget`: clause (2)
  of Stacks 083J, given the chart case at the affine stages.
* `ModuleMapSituation.limitPreserving_zeroFunctor_of_isCompact_of_hasAffineChartZeroDescent`:
  `F_zero` is limit preserving when `ℱ` is of finite type with compact support, given the chart
  case.
* `AlgebraicGeometry.Space.ModuleMapSituation.hasQuasiCompactSupportOverTarget_of_isQuasiCompact`:
  the support hypothesis holds when `f` is quasi-compact.
* `AlgebraicGeometry.Space.ModuleMapSituation.relativelyLimitPreserving_zeroSubfunctor_ι`: limit
  preservation of `F_zero` implies relative limit preservation of the inclusion of the vanishing
  subfunctor of `Y`.
* `AlgebraicGeometry.Space.ModuleMapSituation.isFinitePresentation_zeroSubfunctor_ι_of_devissage`:
  the finite-presentation clause of Stacks 0CWC.

## References

* [Stacks Project, Tag 083J](https://stacks.math.columbia.edu/tag/083J)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 083I](https://stacks.math.columbia.edu/tag/083I)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w w'

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace ModuleMapSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Clause (2): the vanishing locus of a finite-type module -/

/-- The chart case of clause (2) of Stacks 083J: if `ℱ` is of finite type, then for every affine
object `W` of the big fppf category over `S` and every flat morphism `g : W ⟶ X` of algebraic
spaces whose image on points contains the support of `ℱ`, the vanishing locus of the inverse
image `g^*u` is limit preserving. -/
def HasAffineChartZeroDescent (D : ModuleMapSituation.{u, u} B S hS) : Prop :=
  SheafOfModules.IsFiniteTypeOnSite D.F →
  ∀ W : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
    ∀ g : schemeSpace W ⟶ D.X, IsFlat B S hS g.hom →
      supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) ⊆
          Set.range (pointsMap B S hS (schemeSpace W).1 g.hom) →
        ∀ (hF : ((modulePullback B S hS g).obj D.F).IsQuasicoherentOnSite)
          (hG : ((modulePullback B S hS g).obj D.G).IsQuasicoherentOnSite),
          LimitPreserving.{u, u, w, w'} (D.pullbackSituation g hF hG).testScheme
            ((D.pullbackSituation g hF hG).zeroFunctor (modulePullbackSystem B S hS))

/-- If `ℱ` is of finite type and its support is compact in the points of `X`, and the chart case
`AlgebraicGeometry.Space.ModuleMapSituation.HasAffineChartZeroDescent` holds, then the vanishing
locus `F_zero` is limit preserving. -/
theorem limitPreserving_zeroFunctor_of_isCompact_of_hasAffineChartZeroDescent
    (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hFcompact : IsCompact
      (supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F)))
    (hchart : D.HasAffineChartZeroDescent.{u, w, w'}) :
    LimitPreserving.{u, u, w, w'} D.testScheme
      (D.zeroFunctor (modulePullbackSystem B S hS)) := by
  obtain ⟨W, c, hWaffine, hWetale, hWsupp⟩ :=
    exists_affine_etale_chart_of_isCompact B S hS D.X.1 D.X.2 hFcompact
  let g : schemeSpace W ⟶ D.X := ObjectProperty.homMk c
  have hgflat : IsFlat B S hS g.hom := isFlat_of_presheafEtale B S hS hWetale
  have hF : ((modulePullback B S hS g).obj D.F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g D.F
      D.quasicoherent_F
  have hG : ((modulePullback B S hS g).obj D.G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g D.G
      D.quasicoherent_G
  rw [(D.injFunctor_and_zeroFunctor_pullbackSituation_eq g hF hG hgflat hFft hWsupp).2]
  exact hchart hFft W hWaffine g hgflat hWsupp hF hG

/-! ### Reading the stages beyond a chosen stage as test schemes of the base change -/

section Stage

variable (D : ModuleMapSituation.{u, u} B S hS)

/-- A test scheme of `D` over a chosen test scheme `T₀`, read as a test scheme of the situation
base changed to `T₀`: the underlying object of the big fppf category is unchanged, and the
structure morphism to `T₀` is the one carried by the slice. -/
def overTargetSection (T₀ : D.SchemesOver) :
    Over T₀ ⥤ (D.baseChangeTestScheme T₀).SchemesOver where
  obj A := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map A.hom.left)
  map {A A'} k := CostructuredArrow.homMk k.left.left (by
    have h : k.left.left ≫ A'.hom.left = A.hom.left :=
      congrArg (fun g : A.left ⟶ T₀ => g.left) (Over.w k)
    change (schemeSpaceFunctor B S hS).map k.left.left ≫
      (schemeSpaceFunctor B S hS).map A'.hom.left =
        (schemeSpaceFunctor B S hS).map A.hom.left
    rw [← Functor.map_comp, h])
  map_id A := by apply CostructuredArrow.hom_ext; rfl
  map_comp k k' := by apply CostructuredArrow.hom_ext; rfl

/-- The underlying object of the big fppf category of `(D.overTargetSection T₀).obj A` is that of
`A`. -/
@[simp]
theorem overTargetSection_obj_left (T₀ : D.SchemesOver) (A : Over T₀) :
    ((D.overTargetSection T₀).obj A).left = A.left.left :=
  rfl

/-- Reading a test scheme over `T₀` as a test scheme of the base change and then back over `Y`
returns it unchanged. -/
theorem overTarget_obj_overTargetSection_obj (T₀ : D.SchemesOver) (A : Over T₀) :
    (D.overTarget T₀.hom).obj ((D.overTargetSection T₀).obj A) = A.left :=
  congrArg (fun h => (CostructuredArrow.mk h : D.SchemesOver)) (CostructuredArrow.w A.hom)

/-- Vanishing at a test scheme over `T₀` is the same condition for the situation and for its base
change to `T₀`. -/
theorem isZeroAt_overTargetSection_iff (T₀ : D.SchemesOver) (A : Over T₀) :
    (D.baseChangeTestScheme T₀).IsZeroAt (modulePullbackSystem B S hS)
        ((D.overTargetSection T₀).obj A) ↔
      D.IsZeroAt (modulePullbackSystem B S hS) A.left := by
  rw [D.isZeroAt_baseChangeTarget_iff T₀.hom ((D.overTargetSection T₀).obj A),
    D.overTarget_obj_overTargetSection_obj T₀ A]

variable {I : Type*} [Category I] (E : I ⥤ D.SchemesOver)

/-- The diagram of the stages of `E` that lie over a chosen stage `i₀`, indexed by the slice
`Over i₀`, read as a diagram of test schemes of the situation base changed to that stage. -/
def stageDiagram (i₀ : I) :
    Over i₀ ⥤ (D.baseChangeTestScheme (E.obj i₀)).SchemesOver :=
  Over.post E ⋙ D.overTargetSection (E.obj i₀)

/-- A cone on `E` gives a cone on the diagram of stages over `i₀` in the slice over the stage
`E.obj i₀`: the cone point is the cone point of `E` with the structure morphism `c.π.app i₀`,
and the projections are those of `c`. -/
def stageOverCone (c : Cone E) (i₀ : I) : Cone (Over.post E : Over i₀ ⥤ Over (E.obj i₀)) where
  pt := Over.mk (c.π.app i₀)
  π :=
    { app := fun A => Over.homMk (c.π.app A.left) (c.w A.hom)
      naturality := fun A A' k => by
        apply Over.OverMorphism.ext
        change 𝟙 c.pt ≫ c.π.app A'.left = c.π.app A.left ≫ E.map k.left
        rw [Category.id_comp, c.w k.left] }

/-- The cone on the diagram of stages over `i₀`, read in the test schemes of the base change to
that stage. -/
def stageCone (c : Cone E) (i₀ : I) : Cone (D.stageDiagram E i₀) :=
  (D.overTargetSection (E.obj i₀)).mapCone (D.stageOverCone E c i₀)

/-- The cone point of `D.stageCone E c i₀` is the cone point of `c`, with structure morphism
`c.π.app i₀` to the stage `E.obj i₀`. -/
@[simp]
theorem stageCone_pt (c : Cone E) (i₀ : I) :
    (D.stageCone E c i₀).pt =
      (D.overTargetSection (E.obj i₀)).obj (Over.mk (c.π.app i₀)) :=
  rfl

/-- If `E` is cofiltered and `c` is a limit cone, then the cone on the diagram of stages over `i₀`
is again a limit cone. -/
def isLimitStageCone [IsCofiltered I] (c : Cone E) (i₀ : I)
    (hc : IsLimit (D.testScheme.mapCone c)) :
    IsLimit ((D.baseChangeTestScheme (E.obj i₀)).testScheme.mapCone (D.stageCone E c i₀)) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) (D.testScheme.mapCone c)).symm hc

end Stage

/-! ### Clause (2) under compactness of the support over the target -/

/-- The support hypothesis of clause (2) of Stacks 083J at the affine stages: for every affine
test scheme `T` over `Y`, the inverse image of the support of `ℱ` in the points of the
base-change space `X ×_Y T` is compact. -/
def HasQuasiCompactSupportOverTarget (D : ModuleMapSituation.{u, u} B S hS) : Prop :=
  ∀ T : D.SchemesOver, IsAffine (D.testScheme.obj T) →
    IsCompact (pointsMap B S hS (D.baseChangeTestScheme T).X.1
        (D.baseChangeTargetProjection T.hom).hom ⁻¹'
      supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F))

/-- The support of the inverse image of `ℱ` on the base-change space `X ×_Y T` is the inverse image
of the support of `ℱ`. -/
private theorem supportOfSheaf_baseChangeTestScheme_eq
    (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F) (T : D.SchemesOver) :
    supportOfSheaf B S hS (D.baseChangeTestScheme T).X.1
        ((SheafOfModules.toSheaf _).obj (D.baseChangeTestScheme T).F) =
      pointsMap B S hS (D.baseChangeTestScheme T).X.1
          (D.baseChangeTargetProjection T.hom).hom ⁻¹'
        supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) :=
  supportOfSheaf_modulePullback_eq B S hS (D.baseChangeTargetProjection T.hom) D.F
    D.quasicoherent_F hFft

/-- Under the support hypothesis, if `ℱ` is of finite type then the support of the inverse image
of `ℱ` on the base-change space `X ×_Y T` at an affine test scheme `T` is compact. -/
theorem isCompact_supportOfSheaf_baseChangeTestScheme
    (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hFqc : D.HasQuasiCompactSupportOverTarget)
    (T : D.SchemesOver) (hT : IsAffine (D.testScheme.obj T)) :
    IsCompact (supportOfSheaf B S hS (D.baseChangeTestScheme T).X.1
      ((SheafOfModules.toSheaf _).obj (D.baseChangeTestScheme T).F)) := by
  rw [supportOfSheaf_baseChangeTestScheme_eq D hFft T]
  exact hFqc T hT

/-- If `ℱ` is of finite type and the base-change spaces at the affine test schemes are compact,
then the support hypothesis of clause (2) holds. -/
theorem hasQuasiCompactSupportOverTarget_of_compactSpace
    (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hcompact : ∀ T : D.SchemesOver, IsAffine (D.testScheme.obj T) →
      CompactSpace (points B S hS (D.baseChangeTestScheme T).X.1)) :
    D.HasQuasiCompactSupportOverTarget := by
  intro T hT
  have := hcompact T hT
  rw [← supportOfSheaf_baseChangeTestScheme_eq D hFft T]
  exact (isClosed_supportOfSheaf_modulePullback B S hS
    (D.baseChangeTargetProjection T.hom) D.F hFft).isCompact

/-- If `ℱ` is of finite type and the structure morphism `f` is quasi-compact, then the support
hypothesis of clause (2) holds. -/
theorem hasQuasiCompactSupportOverTarget_of_isQuasiCompact
    (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hfqc : IsQuasiCompact B S hS D.f.hom) :
    D.HasQuasiCompactSupportOverTarget := by
  refine D.hasQuasiCompactSupportOverTarget_of_compactSpace hFft fun T hT => ?_
  have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left) := hT
  have haffine : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ D.Y.1),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
        IsQuasiCompactSpace B S hS (pullback g D.f.hom) :=
    ((isQuasiCompact_tfae B S hS D.X.2 D.Y.2 D.f.hom).out 1 3).mp hfqc
  have hbc : IsQuasiCompactSpace B S hS (pullback T.hom.hom D.f.hom) :=
    haffine T.left T.hom.hom haff
  exact (isQuasiCompactSpace_iff_compactSpace_points B S hS _
    (D.baseChangeTestScheme T).X.2).mp
      (isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry T.hom.hom D.f.hom) hbc)

/-- The chart case of clause (2) of Stacks 083J at the affine stages:
`AlgebraicGeometry.Space.ModuleMapSituation.HasAffineChartZeroDescent` for the situation base
changed to each affine test scheme. -/
def HasAffineStageChartZeroDescent (D : ModuleMapSituation.{u, u} B S hS) : Prop :=
  ∀ T : D.SchemesOver, IsAffine (D.testScheme.obj T) →
    (D.baseChangeTestScheme T).HasAffineChartZeroDescent.{u, w, w'}

/-- **Stacks 083J, clause (2).** In the situation of Stacks 083F, if `ℱ` is of finite type, the
support hypothesis `AlgebraicGeometry.Space.ModuleMapSituation.HasQuasiCompactSupportOverTarget`
holds and the chart case holds at the affine stages, then the vanishing locus `F_zero` is limit
preserving. -/
theorem limitPreserving_zeroFunctor_of_hasQuasiCompactSupportOverTarget
    (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hFqc : D.HasQuasiCompactSupportOverTarget)
    (hchart : D.HasAffineStageChartZeroDescent.{u, w, w'}) :
    LimitPreserving.{u, u, w, w'} D.testScheme
      (D.zeroFunctor (modulePullbackSystem B S hS)) := by
  rw [D.limitPreserving_zeroFunctor_iff (modulePullbackSystem B S hS)]
  intro I _ _ E c hc hE hpt hzero
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have hlp := limitPreserving_zeroFunctor_of_isCompact_of_hasAffineChartZeroDescent
    (D.baseChangeTestScheme (E.obj i₀))
    (isFiniteTypeOnSite_modulePullback B S hS
      (D.baseChangeTargetProjection (E.obj i₀).hom) D.F hFft)
    (D.isCompact_supportOfSheaf_baseChangeTestScheme hFft hFqc (E.obj i₀) (hE i₀))
    (hchart (E.obj i₀) (hE i₀))
  have hstage := ((D.baseChangeTestScheme (E.obj i₀)).limitPreserving_zeroFunctor_iff
    (modulePullbackSystem B S hS)).mp hlp
  obtain ⟨A, hA⟩ := hstage (Over i₀) (D.stageDiagram E i₀) (D.stageCone E c i₀)
    (D.isLimitStageCone E c i₀ hc) (fun A => hE A.left) hpt
    ((D.isZeroAt_overTargetSection_iff (E.obj i₀) (Over.mk (c.π.app i₀))).mpr hzero)
  exact ⟨A.left, (D.isZeroAt_overTargetSection_iff (E.obj i₀) ((Over.post E).obj A)).mp hA⟩

/-! ### The transport to the vanishing subfunctor of the base -/

/-- A diagram of objects of the big fppf category over an object `U`, read as a diagram of test
schemes of the situation along a section `y` of `Y` over `U`: the object `V ⟶ U` is sent to the
test scheme `V` whose structure morphism to `Y` is the restriction of `y` along `V ⟶ U`. -/
def zeroDiagram (D : ModuleMapSituation.{u, u} B S hS) (U : BigFppfOver B S hS)
    (y : D.Y.1.obj (op U)) : Over U ⥤ D.SchemesOver where
  obj V := CostructuredArrow.mk (ObjectProperty.homMk (yoneda.map V.hom ≫ yonedaEquiv.symm y))
  map {V V'} k := CostructuredArrow.homMk k.left (by
    apply ObjectProperty.hom_ext
    change yoneda.map k.left ≫ yoneda.map V'.hom ≫ yonedaEquiv.symm y =
      yoneda.map V.hom ≫ yonedaEquiv.symm y
    rw [← Category.assoc, ← yoneda.map_comp, Over.w k])
  map_id V := by apply CostructuredArrow.hom_ext; rfl
  map_comp {V V' V''} k k' := by apply CostructuredArrow.hom_ext; rfl

/-- The underlying object of the big fppf category of `(D.zeroDiagram U y).obj V` is that of
`V`. -/
@[simp]
theorem zeroDiagram_obj_left (D : ModuleMapSituation.{u, u} B S hS) (U : BigFppfOver B S hS)
    (y : D.Y.1.obj (op U)) (V : Over U) : ((D.zeroDiagram U y).obj V).left = V.left :=
  rfl

/-- Composing the diagram of test schemes with the underlying-scheme functor on the test
category gives the underlying-scheme functor on the slice over `U`. -/
theorem zeroDiagram_comp_testScheme (D : ModuleMapSituation.{u, u} B S hS)
    (U : BigFppfOver B S hS) (y : D.Y.1.obj (op U)) :
    D.zeroDiagram U y ⋙ D.testScheme = Over.forget U ⋙ BigFppfOver.toScheme B S hS :=
  rfl

/-- A test scheme of the diagram is the test scheme named by the restricted section, so the
vanishing condition at it is membership of the restricted section in the vanishing
subfunctor. -/
theorem zeroDiagram_obj_eq_zeroTest (D : ModuleMapSituation.{u, u} B S hS)
    (U : BigFppfOver B S hS) (y : D.Y.1.obj (op U)) (V : Over U) :
    (D.zeroDiagram U y).obj V = D.zeroTest V.left (D.Y.1.map V.hom.op y) := by
  have key : (ObjectProperty.homMk (yoneda.map V.hom ≫ yonedaEquiv.symm y) :
        schemeSpace V.left ⟶ D.Y) =
      (ObjectProperty.homMk (yonedaEquiv.symm (D.Y.1.map V.hom.op y)) :
        schemeSpace V.left ⟶ D.Y) := by
    apply ObjectProperty.hom_ext
    show yoneda.map V.hom ≫ yonedaEquiv.symm y = yonedaEquiv.symm (D.Y.1.map V.hom.op y)
    apply yonedaEquiv.injective
    simpa using (yonedaEquiv_naturality (yonedaEquiv.symm y) V.hom).symm
  exact congrArg (fun h => (CostructuredArrow.mk h : D.SchemesOver)) key

/-- Vanishing at a test scheme of the diagram is membership of the restricted section in the
vanishing subfunctor of `Y`. -/
theorem isZeroAt_zeroDiagram_obj_iff (D : ModuleMapSituation.{u, u} B S hS)
    (U : BigFppfOver B S hS) (y : D.Y.1.obj (op U)) (V : Over U) :
    D.IsZeroAt (modulePullbackSystem B S hS) ((D.zeroDiagram U y).obj V) ↔
      D.Y.1.map V.hom.op y ∈ D.zeroSubfunctor.obj (op V.left) := by
  rw [D.zeroDiagram_obj_eq_zeroTest U y V]
  exact (D.mem_zeroSubfunctor_iff V.left _).symm

/-- The presheaf of lifts of a section of `Y` through the inclusion of the vanishing subfunctor
has at most one section over every object: a lift through a monomorphism is determined by the
section it lifts. -/
theorem subsingleton_sectionFiber_zeroSubfunctor_ι (D : ModuleMapSituation.{u, u} B S hS)
    (U : BigFppfOver B S hS) (y : D.Y.1.obj (op U)) (V : (Over U)ᵒᵖ) :
    Subsingleton ((sectionFiber B S hS D.zeroSubfunctor.ι U y).obj V) := by
  refine ⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩
  simpa using a.2.trans b.2.symm

/-- The presheaf of lifts is nonempty over an object of the slice exactly when the vanishing
condition holds at the corresponding test scheme. -/
theorem nonempty_sectionFiber_zeroSubfunctor_ι_iff (D : ModuleMapSituation.{u, u} B S hS)
    (U : BigFppfOver B S hS) (y : D.Y.1.obj (op U)) (V : Over U) :
    Nonempty ((sectionFiber B S hS D.zeroSubfunctor.ι U y).obj (op V)) ↔
      D.IsZeroAt (modulePullbackSystem B S hS) ((D.zeroDiagram U y).obj V) := by
  rw [D.isZeroAt_zeroDiagram_obj_iff U y V]
  refine ⟨fun ⟨x⟩ => ?_, fun h => ⟨⟨⟨_, h⟩, ?_⟩⟩⟩
  · have hx : (x.1 : D.Y.1.obj (op V.left)) = D.Y.1.map V.hom.op y := by simpa using x.2
    exact hx ▸ x.1.2
  · rfl

/-- Limit preservation of the subterminal presheaf `F_zero` on the test schemes over `Y` implies
relative limit preservation of the inclusion of the vanishing subfunctor of `Y`. -/
theorem relativelyLimitPreserving_zeroSubfunctor_ι (D : ModuleMapSituation.{u, u} B S hS)
    (h : LimitPreserving.{u, u, w, w'} D.testScheme
      (D.zeroFunctor (modulePullbackSystem B S hS))) :
    RelativelyLimitPreserving.{u, u, w, w'} B S hS D.zeroSubfunctor.ι := by
  have hdesc := (D.limitPreserving_zeroFunctor_iff (modulePullbackSystem B S hS)).mp h
  intro U y I _ _ E c hc hE hpt
  have : ∀ V : (Over U)ᵒᵖ,
      Subsingleton ((sectionFiber B S hS D.zeroSubfunctor.ι U y).obj V) :=
    D.subsingleton_sectionFiber_zeroSubfunctor_ι U y
  refine (nonempty_isColimit_mapCocone_op_iff_of_subsingleton
    (sectionFiber B S hS D.zeroSubfunctor.ι U y) E c).mpr fun hne => ?_
  obtain ⟨i, hi⟩ := hdesc I (E ⋙ D.zeroDiagram U y) ((D.zeroDiagram U y).mapCone c) hc hE hpt
    ((D.nonempty_sectionFiber_zeroSubfunctor_ι_iff U y c.pt).mp hne)
  exact ⟨i, (D.nonempty_sectionFiber_zeroSubfunctor_ι_iff U y (E.obj i)).mpr hi⟩

/-- If `ℱ` is of finite type, the support hypothesis holds and the chart case holds at the affine
stages, then the inclusion of the vanishing subfunctor of `Y` is relatively limit preserving. -/
theorem relativelyLimitPreserving_zeroSubfunctor_ι_of_chart
    (D : ModuleMapSituation.{u, u} B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hFqc : D.HasQuasiCompactSupportOverTarget)
    (hchart : D.HasAffineStageChartZeroDescent.{u, w, w'}) :
    RelativelyLimitPreserving.{u, u, w, w'} B S hS D.zeroSubfunctor.ι :=
  D.relativelyLimitPreserving_zeroSubfunctor_ι
    (D.limitPreserving_zeroFunctor_of_hasQuasiCompactSupportOverTarget hFft hFqc hchart)

/-! ### Stacks 0CWC, the finite-presentation clause -/

/-- **Stacks 0CWC, the finite-presentation clause.** In the situation of Stacks 083F under the
hypotheses of the closed-immersion clause, if moreover `ℱ` is of finite type and the chart case
holds at the affine stages, then `F_zero ⟶ B` is of finite presentation. -/
theorem isFinitePresentation_zeroSubfunctor_ι (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGflat : _root_.AlgebraicGeometry.Space.IsFlatOver B S hS D.X.2 D.f.hom D.G)
    (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
    (hpure : ∀ y : points B S hS D.Y.1,
      IsPureRelative (D.targetPrePureSituation hft hdec hGft y))
    (hdev : DevissageInput B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hchart : D.HasAffineStageChartZeroDescent.{u, u, u}) :
    IsFinitePresentation B S hS D.zeroSubfunctor.ι := by
  have hclosed : IsClosedSubspace B S hS D.zeroSubfunctor :=
    D.isClosedSubspace_zeroSubfunctor hf hGfp hGft hGflat hft hdec hpure hdev
      (zeroLocusClosedEtaleLocalOnBase B S hS)
  exact ⟨_root_.AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_relativelyLimitPreserving
      B S hS
      (D.relativelyLimitPreserving_zeroSubfunctor_ι_of_chart hFft
        (D.hasQuasiCompactSupportOverTarget_of_isQuasiCompact hFft hf.2.1) hchart),
    isQuasiCompact_of_isClosedImmersion' B S hS hclosed.2,
    isQuasiSeparated_of_isClosedImmersion B S hS hclosed.2⟩

/-! ### The chart case from a ring-level reading of the vanishing locus -/

/-- The ring-level reading of the vanishing locus of the chart situations implies the chart case
of clause (2) at the universe of the schemes. -/
theorem hasAffineChartZeroDescent_of_ringLevelZeroLocus
    (D : ModuleMapSituation.{u, u} B S hS) (h : D.HasAffineChartRingLevelZeroLocus) :
    D.HasAffineChartZeroDescent.{u, u, u} := fun hFft W hW g hgflat hsupp hF hG =>
  ((D.pullbackSituation g hF hG).limitPreserving_zeroFunctor_iff
      (modulePullbackSystem B S hS)).mpr
    ((D.pullbackSituation g hF hG).descendsAlongAffineLimits_isZeroAt_of_ringLevelZeroLocus
      (h hFft W hW g hgflat hsupp hF hG))

/-- The ring-level reading of the vanishing locus at the affine stages implies the chart case of
clause (2) at the affine stages, at the universe of the schemes. -/
theorem hasAffineStageChartZeroDescent_of_ringLevelZeroLocus
    (D : ModuleMapSituation.{u, u} B S hS) (h : D.HasAffineStageChartRingLevelZeroLocus) :
    D.HasAffineStageChartZeroDescent.{u, u, u} := fun T hT =>
  (D.baseChangeTestScheme T).hasAffineChartZeroDescent_of_ringLevelZeroLocus (h T hT)

/-- **Stacks 0CWC, the finite-presentation clause**, with the chart case replaced by the ring-level
reading `AlgebraicGeometry.Space.ModuleMapSituation.HasAffineStageChartRingLevelZeroLocus`. -/
theorem isFinitePresentation_zeroSubfunctor_ι_of_ringLevelZeroLocus
    (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGflat : _root_.AlgebraicGeometry.Space.IsFlatOver B S hS D.X.2 D.f.hom D.G)
    (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
    (hpure : ∀ y : points B S hS D.Y.1,
      IsPureRelative (D.targetPrePureSituation hft hdec hGft y))
    (hdev : DevissageInput B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hring : D.HasAffineStageChartRingLevelZeroLocus) :
    IsFinitePresentation B S hS D.zeroSubfunctor.ι :=
  D.isFinitePresentation_zeroSubfunctor_ι hf hGfp hGft hGflat hft hdec hpure hdev
    hFft (D.hasAffineStageChartZeroDescent_of_ringLevelZeroLocus hring)

/-- **Stacks 0CWC, the finite-presentation clause.** In the situation of Stacks 083F under the
hypotheses of the closed-immersion clause, if moreover `ℱ` is of finite type then `F_zero ⟶ B`
is of finite presentation. -/
theorem isFinitePresentation_zeroSubfunctor_ι_of_devissage
    (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGflat : _root_.AlgebraicGeometry.Space.IsFlatOver B S hS D.X.2 D.f.hom D.G)
    (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
    (hpure : ∀ y : points B S hS D.Y.1,
      IsPureRelative (D.targetPrePureSituation hft hdec hGft y))
    (hdev : DevissageInput B S hS)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F) :
    IsFinitePresentation B S hS D.zeroSubfunctor.ι :=
  D.isFinitePresentation_zeroSubfunctor_ι_of_ringLevelZeroLocus hf hGfp hGft hGflat hft hdec
    hpure hdev hFft (hasAffineStageChartRingLevelZeroLocus B S hS D)

end ModuleMapSituation

end AlgebraicGeometry.Space

end
