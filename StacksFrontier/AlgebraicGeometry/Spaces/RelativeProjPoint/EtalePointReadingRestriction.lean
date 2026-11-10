module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ChartReading
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtalePointSections
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.TwistKerRestrict
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.RestrictionDatum
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtalePointReadingAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointComparisonModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceDictionarySquares
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackChartSection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackUnitSectionMul

/-!
# The restriction of an étale scheme point reading along a morphism of test objects

Let `f : T ⟶ X` be an étale scheme point of an algebraic space and `k : T' ⟶ T` a morphism of test
objects with `f ∘ k` étale, and `φ` the represented morphism of `k`. This file reads the
restriction map `f^*M ⟶ φ_*((f ∘ k)^*M)` of pulled-back modules and graded algebras on étale
charts, through the identification of Stacks 03LW of the pullback along an étale morphism with
the étale restriction, and its coherence with the composition comparison of Stacks 03LU.

## Main results

* `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_chartProjection_unit`: the
  unit of `h^* ⊣ h_*` on chart projections, through Stacks 03LW.
* `AlgebraicGeometry.Space.modulePullbackIso_hom_compIso_val_app`: the coherence of Stacks 03LU
  against Stacks 03LW, on sections.
* `AlgebraicGeometry.Space.modulePullbackIso_hom_directImageSelfOpensSection_restriction`: the
  restriction of pulled-back modules along `k`, over the chart of `k⁻¹(W)`, is the restriction in
  `M` of the reading along the chart morphism `f ∘ (k⁻¹W ⟶ W)`.
* `AlgebraicGeometry.Space.etalePointPieceReading_pointRestriction`: the same for the restricted
  graded algebras.
* `AlgebraicGeometry.Space.RelativeProjSituation.etalePointReading_pointRestriction`: the
  restriction map of the restricted algebras of a relative Proj situation along `k`, read on the
  chart of `k⁻¹(W)`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush)

universe u

namespace AlgebraicGeometry.Space

section ChartUnit

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- A morphism of modules commutes with the chart projection of the direct image, at any
index. -/
theorem val_app_moduleChartProjection_index (f : X ⟶ Y)
    {N N' : Modules.{u, u} B S hS X.1 X.2} (ψ : N ⟶ N') (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (x : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    ψ.val.app j.right ((moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X N) x) =
      (moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X N')
        (((modulePushforward B S hS f).map ψ).val.app (op V) x) :=
  (Functor.natTrans_app_map_apply (moduleChartProjection B S hS f V j)
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map ψ) x).symm

/-- **Stacks 03LW on the chart projection of the unit of Stacks 03LU.**  For an étale morphism
`h : X ⟶ Y`, a chart `V` of `Y`, an index `j` above `X ×_Y V` and the morphism of charts
`ν : h ∘ j ⟶ V` it induces, the comparison of Stacks 03LW sends the chart projection at `j` of
the unit of `h^* ⊣ h_*` applied to a section `x` over `V` to the restriction of `x` along `ν`. -/
theorem modulePullbackIsoEtaleModulePullback_hom_chartProjection_unit (h : X ⟶ Y)
    (hh : IsEtale B S hS h.hom) (G : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS h V)) (comparisonFunctor B S hS X).op)
    (x : G.val.obj (op V)) (nu : (smallEtalePostcomp B S hS h hh).obj j.right.unop ⟶ V)
    (hnu : (comparisonFunctor B S hS Y).map nu =
      (spacesEtalePostcomp B S hS h hh).map j.hom.unop ≫
        (spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app
          ((comparisonFunctor B S hS Y).obj V)) :
    ((modulePullbackIsoEtaleModulePullback B S hS h hh).hom.app G).val.app j.right
        ((moduleChartProjection B S hS h V j).app
          (moduleSetSheaf B S hS X ((modulePullback B S hS h).obj G))
          (((modulePullbackAdjunction B S hS h).unit.app G).val.app (op V) x)) =
      G.val.map nu.op x := by
  refine Eq.trans (val_app_moduleChartProjection_index h
    ((modulePullbackIsoEtaleModulePullback B S hS h hh).hom.app G) V j
    (((modulePullbackAdjunction B S hS h).unit.app G).val.app (op V) x)) ?_
  refine Eq.trans (congrArg ((moduleChartProjection B S hS h V j).app
      (moduleSetSheaf B S hS X ((etaleModulePullback B S hS h hh).obj G)))
    (congrArg (fun m : G ⟶ (modulePushforward B S hS h).obj
        ((etaleModulePullback B S hS h hh).obj G) ↦ m.val.app (op V) x)
      (etaleModulePullbackAdjunction_unit_app B S hS h hh G).symm)) ?_
  refine Eq.trans (congrArg ((moduleChartProjection B S hS h V j).app
      (moduleSetSheaf B S hS X ((etaleModulePullback B S hS h hh).obj G)))
    (etaleModulePullbackAdjunction_unit_val_app_eq_setRestriction B S hS h hh G (op V) x)) ?_
  exact moduleChartProjection_smallEtaleSetRestrictionAdjunction_unit B S hS h hh
    (moduleSetSheaf B S hS Y G) V j x nu hnu

/-- A composite through an étale restriction and the strict composition of étale restrictions,
on sections, at abstract morphisms. -/
theorem etaleModulePullbackComp_comp_val_app {D A C : AlgebraicSpaces B S hS} (h : D ⟶ A)
    (g : A ⟶ C) (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom) {N : Modules.{u, u} B S hS D.1 D.2}
    {M : Modules.{u, u} B S hS A.1 A.2} {G : Modules.{u, u} B S hS C.1 C.2}
    (a : N ⟶ (etaleModulePullback.{u, u} B S hS h hh).obj M)
    (b : M ⟶ (etaleModulePullback.{u, u} B S hS g hg).obj G) (U : SmallEtale B S hS D.1)
    (w : N.val.obj (op U)) :
    (a ≫ (etaleModulePullback.{u, u} B S hS h hh).map b ≫
        (etaleModulePullbackComp B S hS h g hh hg hhg).hom.app G).val.app (op U) w =
      b.val.app (op ((smallEtalePostcomp B S hS h hh).obj U)) (a.val.app (op U) w) :=
  rfl

/-- The étale restriction of a morphism followed by the strict composition of étale restrictions,
on sections, at abstract morphisms. -/
theorem etaleModulePullback_map_comp_etaleModulePullbackComp_val_app
    {D A C : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C) (hh : IsEtale B S hS h.hom)
    (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom) {M : Modules.{u, u} B S hS A.1 A.2}
    {G : Modules.{u, u} B S hS C.1 C.2} (b : M ⟶ (etaleModulePullback.{u, u} B S hS g hg).obj G)
    (U : SmallEtale B S hS D.1)
    (w : ((etaleModulePullback.{u, u} B S hS h hh).obj M).val.obj (op U)) :
    ((etaleModulePullback.{u, u} B S hS h hh).map b ≫
        (etaleModulePullbackComp B S hS h g hh hg hhg).hom.app G).val.app (op U) w =
      ((etaleModulePullback.{u, u} B S hS h hh).map b).val.app (op U) w :=
  rfl

/-- A morphism of charts out of a postcomposition, postcomposed further, read as a morphism out
of the postcomposition along a morphism `g'` equal to the composite. -/
noncomputable def postcompCompHomOfEq {D A C : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
    (g' : D ⟶ C) (e : h ≫ g = g') (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hg' : IsEtale B S hS g'.hom) {U : SmallEtale B S hS D.1} {V : SmallEtale B S hS A.1}
    (m : (smallEtalePostcomp B S hS h hh).obj U ⟶ V) :
    (smallEtalePostcomp B S hS g' hg').obj U ⟶ (smallEtalePostcomp B S hS g hg).obj V :=
  ObjectProperty.homMk (CostructuredArrow.homMk m.hom.left (by
    have hw := CostructuredArrow.w m.hom
    subst e
    change yoneda.map m.hom.left ≫ (V.1.hom ≫ g.hom) = U.1.hom ≫ (h.hom ≫ g.hom)
    rw [← Category.assoc, hw]
    rfl))

/-- The strict composition of étale restrictions followed by the restriction along a postcomposed
morphism is the restriction along `AlgebraicGeometry.Space.postcompCompHomOfEq`. -/
theorem etaleModulePullbackComp_val_app_map {D A C : AlgebraicSpaces B S hS} (h : D ⟶ A)
    (g : A ⟶ C) (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom) (G : Modules.{u, u} B S hS C.1 C.2)
    {U : SmallEtale B S hS D.1} {V : SmallEtale B S hS A.1}
    (m : (smallEtalePostcomp B S hS h hh).obj U ⟶ V)
    (y : G.val.obj (op ((smallEtalePostcomp B S hS g hg).obj V))) :
    ((etaleModulePullbackComp B S hS h g hh hg hhg).hom.app G).val.app (op U)
        (G.val.map ((smallEtalePostcomp B S hS g hg).map m).op y) =
      G.val.map (postcompCompHomOfEq h g (h ≫ g) rfl hh hg hhg m).op y :=
  rfl

/-- The section of a composite through an étale restriction and the strict composition of
étale restrictions, in nested form, at abstract morphisms. -/
theorem comp_etaleModulePullback_map_comp_val_app {D A C : AlgebraicSpaces B S hS} (h : D ⟶ A)
    (g : A ⟶ C) (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom) {N : Modules.{u, u} B S hS D.1 D.2}
    {M : Modules.{u, u} B S hS A.1 A.2} {G : Modules.{u, u} B S hS C.1 C.2}
    (a : N ⟶ (etaleModulePullback.{u, u} B S hS h hh).obj M)
    (b : M ⟶ (etaleModulePullback.{u, u} B S hS g hg).obj G) (U : SmallEtale B S hS D.1)
    (w : N.val.obj (op U)) :
    (a ≫ (etaleModulePullback.{u, u} B S hS h hh).map b ≫
        (etaleModulePullbackComp B S hS h g hh hg hhg).hom.app G).val.app (op U) w =
      ((etaleModulePullbackComp B S hS h g hh hg hhg).hom.app G).val.app (op U)
        (((etaleModulePullback.{u, u} B S hS h hh).map b).val.app (op U) (a.val.app (op U) w)) :=
  rfl

/-- **The coherence of Stacks 03LU against Stacks 03LW, on sections**, for étale representable
morphisms `h : D ⟶ A` and `g : A ⟶ C`, in the nested spelling of the iterated pullback. -/
theorem modulePullbackIso_hom_compIso_val_app {D A C : AlgebraicSpaces B S hS} (h : D ⟶ A)
    (g : A ⟶ C) (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom) (G : Modules.{u, u} B S hS C.1 C.2)
    (U : SmallEtale B S hS D.1)
    (w : ((modulePullback B S hS h).obj ((modulePullback B S hS g).obj G)).val.obj (op U)) :
    ((modulePullbackIsoEtaleModulePullback B S hS (h ≫ g) hhg).hom.app G).val.app (op U)
        (((modulePullbackCompIso B S hS h g).hom.app G).val.app (op U) w) =
      ((etaleModulePullbackComp B S hS h g hh hg hhg).hom.app G).val.app (op U)
        (((etaleModulePullback.{u, u} B S hS h hh).map
            ((modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app G)).val.app (op U)
          (((modulePullbackIsoEtaleModulePullback B S hS h hh).hom.app
            ((modulePullback B S hS g).obj G)).val.app (op U) w)) :=
  congrArg (fun t => (t.app G).val.app (op U) w)
    (modulePullbackCompIso_hom_comp_etaleRestriction_of_representable B S hS h g hh hg hhg)

end ChartUnit

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

section PointRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {T T' : BigFppfOver B S hS} (k : T' ⟶ T)
  (hk : IsEtale B S hS (representedSpaceMap B S hS k).hom)
  (W : (chartScheme (idEtaleChart B S hS T)).Opens)

/-- The morphism of charts of `yoneda.obj T` from the postcomposed base change of the chart of
`W` to the chart of `W`: the counit of postcomposition against base change, read through the
fullness of the comparison functor of Stacks 03G1. -/
noncomputable def selfOpensBaseChangeCounit :
    (smallEtalePostcomp B S hS (representedSpaceMap B S hS k) hk).obj
        ((smallBaseChange B S hS (representedSpaceMap B S hS k)
          (relativelyRepresentable_yoneda_map B S hS k)).obj
          ((selfOpensFunctor B S hS T).obj W)) ⟶
      (selfOpensFunctor B S hS T).obj W :=
  haveI := comparisonFunctor_full B S hS (yonedaSpace B S hS T)
  (comparisonFunctor B S hS (yonedaSpace B S hS T)).preimage
    ((spacesEtalePostcomp B S hS (representedSpaceMap B S hS k) hk).map
        (smallBaseChangeIndex B S hS (representedSpaceMap B S hS k)
          (relativelyRepresentable_yoneda_map B S hS k)
          ((selfOpensFunctor B S hS T).obj W)).hom.unop ≫
      (spacesEtalePostcompBaseChangeAdjunction B S hS (representedSpaceMap B S hS k) hk).counit.app
        ((comparisonFunctor B S hS (yonedaSpace B S hS T)).obj
          ((selfOpensFunctor B S hS T).obj W)))

/-- The morphism of charts of `yoneda.obj T` from the postcomposition of the chart of `k⁻¹(W)`
to the chart of `W`. -/
noncomputable def selfOpensPreimageChartHom :
    (smallEtalePostcomp B S hS (representedSpaceMap B S hS k) hk).obj
        ((selfOpensFunctor B S hS T').obj (preimageOpens k W)) ⟶
      (selfOpensFunctor B S hS T).obj W :=
  (smallEtalePostcomp B S hS (representedSpaceMap B S hS k) hk).map
      (baseChangeSelfOpensIso k W).inv ≫ selfOpensBaseChangeCounit k hk W

/-- The sections over a Zariski open of a direct image along a morphism of test objects, read
through the chart projection at the base-changed index. -/
theorem directImageSelfOpensSection_eq_moduleChartProjection
    (G : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
    (y : ((modulePushforward B S hS (representedSpaceMap B S hS k)).obj G).val.obj
      (op ((selfOpensFunctor B S hS T).obj W))) :
    directImageSelfOpensSection k W (moduleSetSheaf B S hS (yonedaSpace B S hS T') G) y =
      G.val.map (baseChangeSelfOpensIso k W).inv.op
        ((moduleChartProjection B S hS (representedSpaceMap B S hS k)
            ((selfOpensFunctor B S hS T).obj W)
            (smallBaseChangeIndex B S hS (representedSpaceMap B S hS k)
              (relativelyRepresentable_yoneda_map B S hS k)
              ((selfOpensFunctor B S hS T).obj W))).app
          (moduleSetSheaf B S hS (yonedaSpace B S hS T') G) y) :=
  congrArg (G.val.map (baseChangeSelfOpensIso k W).inv.op)
    (moduleChartProjection_app B S hS (representedSpaceMap B S hS k)
      ((selfOpensFunctor B S hS T).obj W) _
      (moduleSetSheaf B S hS (yonedaSpace B S hS T') G) y).symm

/-- The comparison functor sends `selfOpensBaseChangeCounit k hk W` to the composite of the
postcomposed base-change index morphism with the counit of postcomposition against base change at
the chart of `W`. -/
theorem comparisonFunctor_map_selfOpensBaseChangeCounit :
    (comparisonFunctor B S hS (yonedaSpace B S hS T)).map (selfOpensBaseChangeCounit k hk W) =
      (spacesEtalePostcomp B S hS (representedSpaceMap B S hS k) hk).map
          (smallBaseChangeIndex B S hS (representedSpaceMap B S hS k)
            (relativelyRepresentable_yoneda_map B S hS k)
            ((selfOpensFunctor B S hS T).obj W)).hom.unop ≫
        (spacesEtalePostcompBaseChangeAdjunction B S hS (representedSpaceMap B S hS k)
          hk).counit.app
          ((comparisonFunctor B S hS (yonedaSpace B S hS T)).obj
            ((selfOpensFunctor B S hS T).obj W)) := by
  have := comparisonFunctor_full B S hS (yonedaSpace B S hS T)
  exact (comparisonFunctor B S hS (yonedaSpace B S hS T)).map_preimage _

/-- **Stacks 03LW on the direct image of the unit, at the chart of a Zariski open.**  For the
étale represented morphism `φ` of `k : T' ⟶ T`, a module `N` on `yoneda.obj T` and a section `x`
over the chart of `W`, the section of `φ^*N` over the chart of `k⁻¹(W)` read off the unit of
`φ^* ⊣ φ_*` at `x` is, through Stacks 03LW, the restriction of `x` along the chart morphism
`AlgebraicGeometry.Space.selfOpensPreimageChartHom`. -/
theorem modulePullbackIso_hom_directImageSelfOpensSection_unit
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (x : N.val.obj (op ((selfOpensFunctor B S hS T).obj W))) :
    ((modulePullbackIsoEtaleModulePullback B S hS (representedSpaceMap B S hS k) hk).hom.app
        N).val.app (op ((selfOpensFunctor B S hS T').obj (preimageOpens k W)))
      (directImageSelfOpensSection k W
        (moduleSetSheaf B S hS (yonedaSpace B S hS T')
          ((modulePullback B S hS (representedSpaceMap B S hS k)).obj N))
        (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS k)).unit.app N).val.app
          (op ((selfOpensFunctor B S hS T).obj W)) x)) =
      N.val.map (selfOpensPreimageChartHom k hk W).op x := by
  have hA : directImageSelfOpensSection k W
      (moduleSetSheaf B S hS (yonedaSpace B S hS T')
        ((modulePullback B S hS (representedSpaceMap B S hS k)).obj N))
      (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS k)).unit.app N).val.app
          (op ((selfOpensFunctor B S hS T).obj W)) x) =
      ((modulePullback B S hS (representedSpaceMap B S hS k)).obj N).val.map
        (baseChangeSelfOpensIso k W).inv.op
        ((moduleChartProjection B S hS (representedSpaceMap B S hS k)
            ((selfOpensFunctor B S hS T).obj W)
            (smallBaseChangeIndex B S hS (representedSpaceMap B S hS k)
              (relativelyRepresentable_yoneda_map B S hS k)
              ((selfOpensFunctor B S hS T).obj W))).app
          (moduleSetSheaf B S hS (yonedaSpace B S hS T')
            ((modulePullback B S hS (representedSpaceMap B S hS k)).obj N))
          (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS k)).unit.app N).val.app
            (op ((selfOpensFunctor B S hS T).obj W)) x)) :=
    directImageSelfOpensSection_eq_moduleChartProjection k W _ _
  have hB := PresheafOfModules.naturality_apply
    ((modulePullbackIsoEtaleModulePullback B S hS (representedSpaceMap B S hS k) hk).hom.app
      N).val (baseChangeSelfOpensIso k W).inv.op
    ((moduleChartProjection B S hS (representedSpaceMap B S hS k)
        ((selfOpensFunctor B S hS T).obj W)
        (smallBaseChangeIndex B S hS (representedSpaceMap B S hS k)
          (relativelyRepresentable_yoneda_map B S hS k) ((selfOpensFunctor B S hS T).obj W))).app
      (moduleSetSheaf B S hS (yonedaSpace B S hS T')
        ((modulePullback B S hS (representedSpaceMap B S hS k)).obj N))
      (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS k)).unit.app N).val.app
        (op ((selfOpensFunctor B S hS T).obj W)) x))
  have hC := modulePullbackIsoEtaleModulePullback_hom_chartProjection_unit
    (representedSpaceMap B S hS k) hk N ((selfOpensFunctor B S hS T).obj W)
    (smallBaseChangeIndex B S hS (representedSpaceMap B S hS k)
      (relativelyRepresentable_yoneda_map B S hS k) ((selfOpensFunctor B S hS T).obj W)) x
    (selfOpensBaseChangeCounit k hk W) (comparisonFunctor_map_selfOpensBaseChangeCounit k hk W)
  refine (congrArg (((modulePullbackIsoEtaleModulePullback B S hS (representedSpaceMap B S hS k)
    hk).hom.app N).val.app (op ((selfOpensFunctor B S hS T').obj (preimageOpens k W)))) hA).trans ?_
  refine hB.trans ?_
  refine (congrArg (((etaleModulePullback B S hS (representedSpaceMap B S hS k) hk).obj N).val.map
    (baseChangeSelfOpensIso k W).inv.op) hC).trans ?_
  exact (CategoryTheory.congr_fun (N.val.presheaf.map_comp _ _) x).symm

/-- `AlgebraicGeometry.Space.modulePullbackIso_hom_directImageSelfOpensSection_unit` followed by a
morphism into an étale restriction, at an abstract module. -/
theorem val_app_modulePullbackIso_hom_directImageSelfOpensSection_unit
    {Y : AlgebraicSpaces B S hS} (g : yonedaSpace B S hS T ⟶ Y) (hg : IsEtale B S hS g.hom)
    {M : Modules.{u, u} B S hS Y.1 Y.2}
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (ψ : N ⟶ (etaleModulePullback.{u, u} B S hS g hg).obj M)
    (x : N.val.obj (op ((selfOpensFunctor B S hS T).obj W))) :
    ((etaleModulePullback.{u, u} B S hS (representedSpaceMap B S hS k) hk).map ψ).val.app
        (op ((selfOpensFunctor B S hS T').obj (preimageOpens k W)))
      (((modulePullbackIsoEtaleModulePullback B S hS (representedSpaceMap B S hS k) hk).hom.app
        N).val.app (op ((selfOpensFunctor B S hS T').obj (preimageOpens k W)))
      (directImageSelfOpensSection k W
        (moduleSetSheaf B S hS (yonedaSpace B S hS T')
          ((modulePullback B S hS (representedSpaceMap B S hS k)).obj N))
        (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS k)).unit.app N).val.app
          (op ((selfOpensFunctor B S hS T).obj W)) x))) =
      M.val.map ((smallEtalePostcomp B S hS g hg).map (selfOpensPreimageChartHom k hk W)).op
        (ψ.val.app (op ((selfOpensFunctor B S hS T).obj W)) x) :=
  (congrArg (ψ.val.app (op ((smallEtalePostcomp B S hS (representedSpaceMap B S hS k) hk).obj
      ((selfOpensFunctor B S hS T').obj (preimageOpens k W)))))
    (modulePullbackIso_hom_directImageSelfOpensSection_unit k hk W N x)).trans
    (PresheafOfModules.naturality_apply ψ.val (selfOpensPreimageChartHom k hk W).op x)

/-- **The restriction of pulled-back modules along a morphism of test objects, read through
Stacks 03LW.**  For étale scheme points `f` of `X` at `T` and `yoneda.map k ≫ f` at `T'`, a module
`M` on `X` and a section `x` of `f^*M` over the chart of `W`, the restriction map
`f^*M ⟶ φ_*((f ∘ k)^*M)` (the unit of `φ^* ⊣ φ_*` followed by the composition comparison of
Stacks 03LU), read over the chart of `k⁻¹(W)` and through Stacks 03LW, is the restriction in `M` of
the reading of `x` along the chart morphism `f ∘ (k⁻¹W ⟶ W)`. -/
theorem modulePullbackIso_hom_directImageSelfOpensSection_restriction
    (f : yoneda.obj T ⟶ X.1) (hf : IsEtale B S hS (pointHom (X := X) f).hom)
    (hf' : IsEtale B S hS (representedSpaceMap B S hS k ≫ pointHom (X := X) f).hom)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (x : ((modulePullback B S hS (pointHom (X := X) f)).obj M).val.obj
      (op ((selfOpensFunctor B S hS T).obj W))) :
    ((modulePullbackIsoEtaleModulePullback B S hS
        (representedSpaceMap B S hS k ≫ pointHom (X := X) f) hf').hom.app M).val.app
        (op ((selfOpensFunctor B S hS T').obj (preimageOpens k W)))
      (directImageSelfOpensSection k W
        (moduleSetSheaf B S hS (yonedaSpace B S hS T')
          ((modulePullback B S hS (representedSpaceMap B S hS k ≫ pointHom (X := X) f)).obj M))
        (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS k)).unit.app
            ((modulePullback B S hS (pointHom (X := X) f)).obj M) ≫
          (modulePushforward B S hS (representedSpaceMap B S hS k)).map
            ((modulePullbackCompIso B S hS (representedSpaceMap B S hS k)
              (pointHom (X := X) f)).hom.app M)).val.app
          (op ((selfOpensFunctor B S hS T).obj W)) x)) =
      M.val.map (postcompCompHomOfEq (representedSpaceMap B S hS k) (pointHom (X := X) f)
          (representedSpaceMap B S hS k ≫ pointHom (X := X) f) rfl hk hf hf'
          (selfOpensPreimageChartHom k hk W)).op
        (((modulePullbackIsoEtaleModulePullback B S hS (pointHom (X := X) f) hf).hom.app M).val.app
          (op ((selfOpensFunctor B S hS T).obj W)) x) := by
  have h2 := directImageSelfOpensSection_eq_moduleChartProjection k W
    ((modulePullback B S hS (representedSpaceMap B S hS k ≫ pointHom (X := X) f)).obj M)
    (((modulePushforward B S hS (representedSpaceMap B S hS k)).map
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS k)
        (pointHom (X := X) f)).hom.app M)).val.app (op ((selfOpensFunctor B S hS T).obj W))
      (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS k)).unit.app
        ((modulePullback B S hS (pointHom (X := X) f)).obj M)).val.app
        (op ((selfOpensFunctor B S hS T).obj W)) x))
  have h3 := (val_app_moduleChartProjection_index (representedSpaceMap B S hS k)
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS k)
        (pointHom (X := X) f)).hom.app M) ((selfOpensFunctor B S hS T).obj W)
    (smallBaseChangeIndex B S hS (representedSpaceMap B S hS k)
      (relativelyRepresentable_yoneda_map B S hS k) ((selfOpensFunctor B S hS T).obj W))
    (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS k)).unit.app
        ((modulePullback B S hS (pointHom (X := X) f)).obj M)).val.app
        (op ((selfOpensFunctor B S hS T).obj W)) x)).symm
  have h4 := (PresheafOfModules.naturality_apply
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS k)
        (pointHom (X := X) f)).hom.app M).val (baseChangeSelfOpensIso k W).inv.op
    ((moduleChartProjection B S hS (representedSpaceMap B S hS k)
        ((selfOpensFunctor B S hS T).obj W)
        (smallBaseChangeIndex B S hS (representedSpaceMap B S hS k)
          (relativelyRepresentable_yoneda_map B S hS k) ((selfOpensFunctor B S hS T).obj W))).app
      (moduleSetSheaf B S hS (yonedaSpace B S hS T')
        ((modulePullback B S hS (representedSpaceMap B S hS k)).obj
          ((modulePullback B S hS (pointHom (X := X) f)).obj M)))
      (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS k)).unit.app
        ((modulePullback B S hS (pointHom (X := X) f)).obj M)).val.app
        (op ((selfOpensFunctor B S hS T).obj W)) x))).symm
  have h5 := (directImageSelfOpensSection_eq_moduleChartProjection k W
    ((modulePullback B S hS (representedSpaceMap B S hS k)).obj
      ((modulePullback B S hS (pointHom (X := X) f)).obj M))
    (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS k)).unit.app
        ((modulePullback B S hS (pointHom (X := X) f)).obj M)).val.app
        (op ((selfOpensFunctor B S hS T).obj W)) x)).symm
  have hcoh := modulePullbackIso_hom_compIso_val_app (representedSpaceMap B S hS k)
    (pointHom (X := X) f) hk hf hf' M
    ((selfOpensFunctor B S hS T').obj (preimageOpens k W))
    (directImageSelfOpensSection k W
        (moduleSetSheaf B S hS (yonedaSpace B S hS T')
          ((modulePullback B S hS (representedSpaceMap B S hS k)).obj
            ((modulePullback B S hS (pointHom (X := X) f)).obj M)))
        (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS k)).unit.app
          ((modulePullback B S hS (pointHom (X := X) f)).obj M)).val.app
          (op ((selfOpensFunctor B S hS T).obj W)) x))
  refine (congrArg (((modulePullbackIsoEtaleModulePullback B S hS
    (representedSpaceMap B S hS k ≫ pointHom (X := X) f) hf').hom.app M).val.app
      (op ((selfOpensFunctor B S hS T').obj (preimageOpens k W)))) (h2.trans
        ((congrArg (((modulePullback B S hS
          (representedSpaceMap B S hS k ≫ pointHom (X := X) f)).obj M).val.map
          (baseChangeSelfOpensIso k W).inv.op) h3).trans (h4.trans
            (congrArg (((modulePullbackCompIso B S hS (representedSpaceMap B S hS k)
              (pointHom (X := X) f)).hom.app M).val.app
                (op ((selfOpensFunctor B S hS T').obj (preimageOpens k W)))) h5))))).trans ?_
  refine hcoh.trans ?_
  have hfin := val_app_modulePullbackIso_hom_directImageSelfOpensSection_unit k hk W
      (pointHom (X := X) f) hf ((modulePullback B S hS (pointHom (X := X) f)).obj M)
      ((modulePullbackIsoEtaleModulePullback B S hS (pointHom (X := X) f) hf).hom.app M) x
  have hfin2 := congrArg (((etaleModulePullbackComp B S hS (representedSpaceMap B S hS k)
    (pointHom (X := X) f) hk hf hf').hom.app M).val.app
      (op ((selfOpensFunctor B S hS T').obj (preimageOpens k W)))) hfin
  have hfin3 := etaleModulePullbackComp_val_app_map _ _ hk hf hf' M
    (selfOpensPreimageChartHom k hk W)
    (((modulePullbackIsoEtaleModulePullback B S hS (pointHom (X := X) f) hf).hom.app M).val.app
      (op ((selfOpensFunctor B S hS T).obj W)) x)
  convert hfin2.trans hfin3 using 2

/-- The two spellings of the unit of `φ^* ⊣ φ_*` and of the direct image give the same sections
over the chart of `k⁻¹(W)`, at abstract modules. -/
theorem directImageSelfOpensSection_viaComparison_unit_comp
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (N₂ : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
    (c : (modulePullback B S hS (representedSpaceMap B S hS k)).obj N ⟶ N₂)
    (x : N.val.obj (op ((selfOpensFunctor B S hS T).obj W))) :
    directImageSelfOpensSection k W (moduleSetSheaf B S hS (yonedaSpace B S hS T') N₂)
        (((smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS k)).pullbackAdjPushforwardModulesViaComparison.unit.app N ≫
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS k)).pushforwardModules.map
            c).val.app (op ((selfOpensFunctor B S hS T).obj W)) x) =
      directImageSelfOpensSection k W (moduleSetSheaf B S hS (yonedaSpace B S hS T') N₂)
        (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS k)).unit.app N ≫
          (modulePushforward B S hS (representedSpaceMap B S hS k)).map c).val.app
            (op ((selfOpensFunctor B S hS T).obj W)) x) := by
  have hu := open Stacks.Sheaves.GradedAlgebraEssentiallySmall in
    (pullbackAdjPushforwardModulesViaComparison_unit_app_val_app
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS k)) N
      (op ((selfOpensFunctor B S hS T).obj W)) x).trans
    (modulePullbackAdjunction_unit_val_app B S hS (representedSpaceMap B S hS k) N
      (op ((selfOpensFunctor B S hS T).obj W)) x).symm
  exact congrArg (fun z => directImageSelfOpensSection k W
    (moduleSetSheaf B S hS (yonedaSpace B S hS T') N₂)
    (((modulePushforward B S hS (representedSpaceMap B S hS k)).map c).val.app
      (op ((selfOpensFunctor B S hS T).obj W)) z)) hu

/-- **The restriction map of pulled-back graded algebras along a morphism of test objects, read
through Stacks 03LW**, for an arbitrary spelling `g'` of the composite scheme point. -/
theorem modulePullbackIso_hom_directImageSelfOpensSection_gradedPullRestrictionApp
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ)
    (f : yoneda.obj T ⟶ X.1) (hf : IsEtale B S hS (pointHom (X := X) f).hom)
    (g' : yonedaSpace B S hS T' ⟶ X) (e : representedSpaceMap B S hS k ≫ pointHom (X := X) f = g')
    (hg' : IsEtale B S hS g'.hom)
    (x : (((gradedPull (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS
          (pointHom (X := X) f))).obj A).piece n).val.obj
      (op ((selfOpensFunctor B S hS T).obj W))) :
    ((modulePullbackIsoEtaleModulePullback B S hS g' hg').hom.app (A.piece n)).val.app
        (op ((selfOpensFunctor B S hS T').obj (preimageOpens k W)))
      (directImageSelfOpensSection k W
        (moduleSetSheaf B S hS (yonedaSpace B S hS T') ((modulePullback B S hS g').obj (A.piece n)))
        ((gradedPullRestrictionApp (representedSpaceMap B S hS k) (pointHom (X := X) f) g' e A
          n).val.app (op ((selfOpensFunctor B S hS T).obj W)) x)) =
      (A.piece n).val.map (postcompCompHomOfEq (representedSpaceMap B S hS k)
          (pointHom (X := X) f) g' e hk hf hg' (selfOpensPreimageChartHom k hk W)).op
        (((modulePullbackIsoEtaleModulePullback B S hS (pointHom (X := X) f) hf).hom.app
          (A.piece n)).val.app (op ((selfOpensFunctor B S hS T).obj W)) x) := by
  subst e
  have hg := congrArg (fun t => t.val.app (op ((selfOpensFunctor B S hS T).obj W)) x)
    (gradedPullRestrictionApp_comp_rfl_eq (representedSpaceMap B S hS k) (pointHom (X := X) f) A n)
  have hm := modulePullbackIso_hom_directImageSelfOpensSection_restriction k hk W f hf hg'
    (A.piece n) x
  refine Eq.trans ?_ (hm.trans rfl)
  have hb := directImageSelfOpensSection_viaComparison_unit_comp k W
    ((modulePullback B S hS (pointHom (X := X) f)).obj (A.piece n))
    ((modulePullback B S hS (representedSpaceMap B S hS k ≫ pointHom (X := X) f)).obj (A.piece n))
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS k)
        (pointHom (X := X) f)).hom.app (A.piece n)) x
  have hc := congrArg (directImageSelfOpensSection k W
        (moduleSetSheaf B S hS (yonedaSpace B S hS T')
          ((modulePullback B S hS (representedSpaceMap B S hS k ≫ pointHom (X := X) f)).obj
            (A.piece n)))) hg
  have hd := congrArg (((modulePullbackIsoEtaleModulePullback B S hS
    (representedSpaceMap B S hS k ≫ pointHom (X := X) f) hg').hom.app (A.piece n)).val.app
      (op ((selfOpensFunctor B S hS T').obj (preimageOpens k W)))) (hc.trans hb)
  convert hd using 2

/-- **The restriction map of the restricted algebras along a morphism of test objects, read
through Stacks 03LW**, at an abstract graded algebra, in the form of
`AlgebraicGeometry.Space.etalePointPieceReading`. -/
theorem etalePointPieceReading_pointRestriction
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ)
    (f : yoneda.obj T ⟶ X.1) (hf : IsEtale B S hS (pointHom (X := X) f).hom)
    (f' : yoneda.obj T' ⟶ X.1) (hkf : yoneda.map k ≫ f = f')
    (hf' : IsEtale B S hS (pointHom (X := X) f').hom)
    (x : ((zariskiReading T (etalePointAlgebra A T f)).piece n).val.obj (op W)) :
    etalePointPieceReading A f' hf' n ((selfOpensFunctor B S hS T').obj (preimageOpens k W))
        (((pointRestriction A k f f' hkf).app n).val.app (op W) x) =
      (A.piece n).val.map (postcompCompHomOfEq (representedSpaceMap B S hS k)
          (pointHom (X := X) f) (pointHom (X := X) f') (pointHom_comp k hkf) hk hf hf'
          (selfOpensPreimageChartHom k hk W)).op
        (etalePointPieceReading A f hf n ((selfOpensFunctor B S hS T).obj W) x) := by
  have h2 : ((pointRestriction A k f f' hkf).app n).val.app (op W) x =
      directImageSelfOpensSection k W
        (moduleSetSheaf B S hS (yonedaSpace B S hS T')
          ((modulePullback B S hS (pointHom (X := X) f')).obj (A.piece n)))
        ((gradedPullRestrictionApp (representedSpaceMap B S hS k) (pointHom (X := X) f)
          (pointHom (X := X) f') (pointHom_comp k hkf) A n).val.app
          (op ((selfOpensFunctor B S hS T).obj W)) x) :=
    (pointRestriction_app_val_app A k f f' hkf n W x).trans rfl
  have h3 := modulePullbackIso_hom_directImageSelfOpensSection_gradedPullRestrictionApp k hk W A n
    f hf (pointHom (X := X) f') (pointHom_comp k hkf) hf' x
  have h4 := congrArg (etalePointPieceReading A f' hf' n
    ((selfOpensFunctor B S hS T').obj (preimageOpens k W))) h2
  exact h4.trans h3

end PointRestriction

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, u}) {T T' : BigFppfOver s.site s.base s.containsBase}
  (k : T' ⟶ T) (hk : IsEtale s.site s.base s.containsBase (representedSpaceMap s.site s.base
    s.containsBase k).hom)
  (f : yoneda.obj T ⟶ s.space.1)
  (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)
  (hf' : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) (yoneda.map k ≫ f)).hom)

/-- **The chart morphism along which the restriction of `f^*𝒜` to `(f ∘ k)^*𝒜` is read**: from
the chart `W₁ ⟶ T' ⟶ X` to the chart `W ⟶ T ⟶ X`, for `W₁ ≤ k⁻¹(W)`. -/
noncomputable def etalePointChartRestrict
    {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T').Opens}
    (hW : W₁ ≤ preimageOpens k W) :
    s.etalePointChart (yoneda.map k ≫ f) hf' W₁ ⟶ s.etalePointChart f hf W :=
  (smallEtalePostcomp s.site s.base s.containsBase (pointHom (X := s.space) (yoneda.map k ≫ f))
      hf').map ((selfOpensFunctor s.site s.base s.containsBase T').map (homOfLE hW)) ≫
    postcompCompHomOfEq (representedSpaceMap s.site s.base s.containsBase k)
      (pointHom (X := s.space) f) (pointHom (X := s.space) (yoneda.map k ≫ f))
      (pointHom_comp k rfl) hk hf hf' (selfOpensPreimageChartHom k hk W)

/-- The inverse of the restriction of the restriction datum is the comparison of restricted
algebras. -/
theorem inv_quadrupleRestriction_restrict_app (n : ℤ) :
    haveI := s.quadrupleRestriction.isIso_restrict_app k f (yoneda.map k ≫ f) rfl n
    inv ((s.quadrupleRestriction.restrict k f (yoneda.map k ≫ f) rfl).app n) =
      (pointComparison s.shrink.algebra k f (yoneda.map k ≫ f) rfl).app n := by
  have := s.quadrupleRestriction.isIso_restrict_app k f (yoneda.map k ≫ f) rfl n
  have := isIso_pointComparison_app s.shrink.algebra s.shrink.isQuasicoherent k f
    (yoneda.map k ≫ f) rfl n
  refine IsIso.inv_eq_of_hom_inv_id ?_
  exact IsIso.inv_hom_id ((pointComparison s.shrink.algebra k f (yoneda.map k ≫ f) rfl).app n)

/-- The comparison of restricted algebras on a pulled-back section is the restriction map, read
over `W₁ ≤ k⁻¹(W)`. -/
theorem pointComparison_app_pullbackSection (n : ℤ)
    {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T').Opens}
    (hW : W₁ ≤ preimageOpens k W) (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    ((pointComparison s.shrink.algebra k f (yoneda.map k ≫ f) rfl).app n).val.app (op W₁)
        (Scheme.Modules.pullbackSection ((BigFppfOver.toScheme s.site s.base s.containsBase).map k)
          ((s.relativeProjPoints.algebra T f).piece n) W W₁ hW a) =
      ((s.relativeProjPoints.algebra T' (yoneda.map k ≫ f)).piece n).val.map (homOfLE hW).op
        (((pointRestriction s.shrink.algebra k f (yoneda.map k ≫ f) rfl).app n).val.app (op W) a) :=
  (PresheafOfModules.naturality_apply
    ((pointComparison s.shrink.algebra k f (yoneda.map k ≫ f) rfl).app n).val (homOfLE hW).op
    _).trans
    (congrArg (((s.relativeProjPoints.algebra T' (yoneda.map k ≫ f)).piece n).val.map
      (homOfLE hW).op)
      (Stacks.RingedSpace.transposeHomApp_pullbackUnit _
        (pointRestriction s.shrink.algebra k f (yoneda.map k ≫ f) rfl) n W a))

/-- The reading of a section of `f^*𝒜_n` over `W` on the chart `W ⟶ T ⟶ X`, unfolded. -/
theorem etalePointSectionsEquiv_eq (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    s.etalePointSectionsEquiv f hf n W a =
      SheafOfModules.GradedAlgebra.smallPieceEquiv s.algebra n (op (s.etalePointChart f hf W))
        (((modulePullbackIsoEtaleModulePullback s.site s.base s.containsBase
          (pointHom (X := s.space) f) hf).hom.app (s.smallAlgebra.piece n)).val.app
          (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W))
          (s.etalePointSectionsUnfold f n W a)) :=
  rfl

/-- The restriction map of the restricted algebras of the shrunk situation is that of the small
presentation of the algebra. -/
theorem pointRestriction_shrink_algebra (f' : yoneda.obj T' ⟶ s.space.1)
    (hkf : yoneda.map k ≫ f = f') :
    HEq (pointRestriction s.shrink.algebra k f f' hkf)
      (pointRestriction s.smallAlgebra k f f' hkf) :=
  HEq.rfl

/-- The first two steps of `etalePointSectionsUnfold`: the sections of `f^*𝒜_n` over `W` as the
sections of the Zariski reading of the pullback of the small presentation. -/
def etalePointSectionsZariski (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens) :
    Γ((s.relativeProjPoints.algebra T f).piece n, W) ≃
      ((zariskiReading T (etalePointAlgebra s.smallAlgebra T f)).piece n).val.obj (op W) :=
  (Equiv.refl _ : Γ((s.relativeProjPoints.algebra T f).piece n, W) ≃
      (((s.shrink.pointAlgebra T f).piece n).val.obj (op W) : Type u)).trans
    (Equiv.refl _ : (((s.shrink.pointAlgebra T f).piece n).val.obj (op W) : Type u) ≃
      (((SheafOfModules.pushforward.{u} (selfOpensStructureMap s.site s.base s.containsBase T)).obj
        ((etalePointAlgebra s.smallAlgebra T f).piece n)).val.obj (op W) : Type u))

/-- `AlgebraicGeometry.Space.RelativeProjSituation.etalePointReading_eq` with the site of the
situation itself, rather than that of the shrunk situation, in the reading. -/
theorem etalePointReading_eq_site (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    s.etalePointReading f hf n W a =
      SheafOfModules.GradedAlgebra.smallPieceEquiv s.algebra n (op (s.etalePointChart f hf W))
        (etalePointPieceReading (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
          (s.shrink.algebra : SheafOfModules.GradedAlgebra.{u, u}
            (structureRingSheaf s.site s.base s.containsBase s.space)) f hf n
          ((selfOpensFunctor s.site s.base s.containsBase T).obj W) a) :=
  (s.etalePointReading_eq f hf n W a).trans rfl

/-- The restriction map of the restricted algebras along `k`, read on the chart of `k⁻¹(W)`. -/
theorem etalePointReading_pointRestriction (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    s.etalePointReading (yoneda.map k ≫ f) hf' n (preimageOpens k W)
        (((pointRestriction (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
          (s.shrink.algebra : SheafOfModules.GradedAlgebra.{u, u}
            (structureRingSheaf s.site s.base s.containsBase s.space))
          k f (yoneda.map k ≫ f) rfl).app n).val.app (op W) a) =
      (s.algebra.piece n).val.map (postcompCompHomOfEq
          (representedSpaceMap s.site s.base s.containsBase k)
          (pointHom (X := s.space) f) (pointHom (X := s.space) (yoneda.map k ≫ f))
          (pointHom_comp k rfl) hk hf hf' (selfOpensPreimageChartHom k hk W)).op
        (s.etalePointReading f hf n W a) := by
  have h1 := s.etalePointReading_eq_site (yoneda.map k ≫ f) hf' n (preimageOpens k W)
    (((pointRestriction (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
          (s.shrink.algebra : SheafOfModules.GradedAlgebra.{u, u}
            (structureRingSheaf s.site s.base s.containsBase s.space))
          k f (yoneda.map k ≫ f) rfl).app n).val.app (op W) a)
  have h2 := etalePointPieceReading_pointRestriction (B := s.site) (S := s.base)
    (hS := s.containsBase) (X := s.space) k hk W
    (s.shrink.algebra : SheafOfModules.GradedAlgebra.{u, u}
      (structureRingSheaf s.site s.base s.containsBase s.space)) n f hf
    (yoneda.map k ≫ f) rfl hf' a
  have h3 := congrArg (SheafOfModules.GradedAlgebra.smallPieceEquiv s.algebra n
      (op (s.etalePointChart (yoneda.map k ≫ f) hf' (preimageOpens k W)))) h2
  have h4 :=
    (h3.trans (SheafOfModules.GradedAlgebra.smallPieceEquiv_naturality s.algebra n _ _)).trans
    (congrArg ((s.algebra.piece n).val.map (postcompCompHomOfEq
          (representedSpaceMap s.site s.base s.containsBase k)
          (pointHom (X := s.space) f) (pointHom (X := s.space) (yoneda.map k ≫ f))
          (pointHom_comp k rfl) hk hf hf' (selfOpensPreimageChartHom k hk W)).op)
      (s.etalePointReading_eq_site f hf n W a).symm)
  exact h1.trans h4

end AlgebraicGeometry.Space.RelativeProjSituation


end
