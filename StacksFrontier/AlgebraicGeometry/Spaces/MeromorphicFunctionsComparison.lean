module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicStalks
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of sheaves of meromorphic functions

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` for which pullbacks of
meromorphic functions are defined (Stacks 0EN8). This file builds the comparison

`𝒦_Y ⟶ f_*𝒦_X`

of sheaves of meromorphic functions, for an arbitrary `f`.

The sections of the direct image over an étale chart `V` of `Y` are the limit of the sections
of `𝒦_X` over the étale charts of `X` above `X ×_Y V`, and each such chart is the source of a
chart diagram over `V`. The chartwise fraction rule `a/b ↦ f^♯a/f^♯b` of
`AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions` assembles into a map from the
presheaf of sectionwise localizations `𝒮_Y⁻¹𝒪_Y` into the direct image, and `𝒦_Y` is the
sheafification of that presheaf.

## Main definitions

* `AlgebraicGeometry.Space.meromorphicFunctionSheafDirectImage` is `f_*𝒦_X`.
* `AlgebraicGeometry.Space.meromorphicFunctionSheafComparison` is `𝒦_Y ⟶ f_*𝒦_X`.

## Main results

* `AlgebraicGeometry.Space.chartProjection_meromorphicLocalizationMapApp`: the chart
  projections of the comparison are the chartwise fraction rule.
* `AlgebraicGeometry.Space.toSheafify_comp_meromorphicFunctionSheafComparison`: the comparison
  restricts along the sheafification map to the chartwise fraction rule.

## Implementation notes

`AlgebraicGeometry.Space.meromorphicFunctionSheafPullback` is a comparison with a different
target: there the direct image is restriction along base change of étale charts, which exists
only for a *representable* `f`. The comparison here is over the direct image of Stacks 03G8,
for an arbitrary `f`.

## References

* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback (pullbackCommRingSheaf pullbackCommRingSheafMapOfNatTrans
  commRingSheaf_mul_comm)
open Stacks.Sheaves.RingedToposModules (inverseImageSectionsCommRing)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheaf of meromorphic functions of an algebraic space, as a sheaf of rings. -/
noncomputable abbrev meromorphicRingSheaf (Z : AlgebraicSpaces B S hS) :
    Sheaf (SmallEtale.topology B S hS Z.1) RingCat.{u} :=
  (sheafCompose (SmallEtale.topology B S hS Z.1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (meromorphicFunctionSheaf B S hS Z.1 Z.2)

/-- The sheaf of sets underlying the sheaf of meromorphic functions. -/
noncomputable abbrev meromorphicSetSheaf (Z : AlgebraicSpaces B S hS) :
    Sheaf (SmallEtale.topology B S hS Z.1) (Type u) :=
  (sheafCompose (SmallEtale.topology B S hS Z.1) (forget RingCat.{u})).obj
    (meromorphicRingSheaf B S hS Z)

variable {X Y : AlgebraicSpaces B S hS}

/-- The chart projections of the direct image, for an arbitrary sheaf of sets, are the
projections of the limit cone. -/
theorem chartProjection_app (f : X ⟶ Y) (A : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (a : ((comparisonFunctor B S hS X).op.ran.obj A.obj).obj
      (op (chartBaseChange B S hS f V))) :
    (chartProjection B S hS f V j).app A a =
      (ranChartCone B S hS X A.obj (chartBaseChange B S hS f V)).π.app j a := by
  have h : (((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app A).hom =
      (comparisonFunctor B S hS X).op.ranCounit.app A.obj := by
    rw [Functor.sheafAdjunctionCocontinuous_counit_app_hom, Functor.ranAdjunction_counit]
  show (((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app A).hom.app
      j.right (((comparisonFunctor B S hS X).op.ran.obj A.obj).map j.hom a) = _
  rw [h]
  rfl

variable (f : X ⟶ Y) (hf : PullbacksMeromorphicSections B S hS f.hom)

/-- The chartwise fraction rule `a/b ↦ f^♯a/f^♯b` over the chart diagram attached to an étale
chart of `X` above `X ×_Y V`, followed by the map into the sheaf of meromorphic functions. -/
noncomputable def chartMeromorphicPullback (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (regularLocalizationPresheaf B S hS Y).obj (op V) →+*
      (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj j.right :=
  ((toSheafify (SmallEtale.topology B S hS X.1)
        (regularLocalizationPresheaf B S hS X)).app j.right).hom.comp
    (chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf (chartDiagramOfIndex B S hS f V j))

/-- The chartwise fraction rule is compatible with morphisms of charts of `X` above
`X ×_Y V`. -/
theorem chartMeromorphicPullback_comp (V : SmallEtale B S hS Y.1)
    {j₁ j₂ : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op}
    (φ : j₁ ⟶ j₂) (s : (regularLocalizationPresheaf B S hS Y).obj (op V)) :
    chartMeromorphicPullback B S hS f hf V j₂ s =
      (meromorphicSetSheaf B S hS X).obj.map φ.right
        (chartMeromorphicPullback B S hS f hf V j₁ s) := by
  have hcond : (SmallEtale.toOver B S hS X.1).map φ.right.unop ≫
      (chartDiagramOfIndex B S hS f V j₁).g =
      (chartDiagramOfIndex B S hS f V j₂).g ≫ (SmallEtale.toOver B S hS Y.1).map (𝟙 V) :=
    (chartBaseChangeMap_comp B S hS f V φ).symm.trans
      ((Category.comp_id (chartBaseChangeMap B S hS f V j₂)).symm.trans
        (congrArg (fun q ↦ chartBaseChangeMap B S hS f V j₂ ≫ q)
          ((SmallEtale.toOver B S hS Y.1).map_id V).symm))
  have hcomp := congrArg (fun k : _ →+* _ ↦ k s)
    (chartPullbackMeromorphicFunctions_comp B S hS X.2 Y.2 hf
      (chartDiagramOfIndex B S hS f V j₁) (chartDiagramOfIndex B S hS f V j₂)
      φ.right.unop (𝟙 V) hcond)
  have hid : ((regularLocalizationPresheaf B S hS Y).map (𝟙 (op V))).hom s = s := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hfrac : chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf
        (chartDiagramOfIndex B S hS f V j₂) s =
      ((regularLocalizationPresheaf B S hS X).map φ.right).hom
        (chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf
          (chartDiagramOfIndex B S hS f V j₁) s) :=
    (congrArg (chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf
      (chartDiagramOfIndex B S hS f V j₂)) hid).symm.trans hcomp
  have hnat := ConcreteCategory.congr_hom
    ((toSheafify (SmallEtale.topology B S hS X.1)
      (regularLocalizationPresheaf B S hS X)).naturality φ.right)
    (chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf
      (chartDiagramOfIndex B S hS f V j₁) s)
  show ((toSheafify (SmallEtale.topology B S hS X.1)
      (regularLocalizationPresheaf B S hS X)).app j₂.right).hom
        (chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf
          (chartDiagramOfIndex B S hS f V j₂) s) = _
  rw [hfrac]
  exact hnat

/-- The cone of chartwise fraction rules over an étale chart `V` of `Y`, whose limit is the
sections of the direct image of the sheaf of meromorphic functions over `V`. -/
noncomputable def meromorphicChartCone (V : SmallEtale B S hS Y.1) :
    Limits.Cone (StructuredArrow.proj (op (chartBaseChange B S hS f V))
      (comparisonFunctor B S hS X).op ⋙ (meromorphicSetSheaf B S hS X).obj) where
  pt := ToType ((regularLocalizationPresheaf B S hS Y).obj (op V))
  π :=
    { app := fun j ↦ TypeCat.ofHom fun s ↦ chartMeromorphicPullback B S hS f hf V j s
      naturality := fun _ _ φ ↦ (Category.id_comp _).trans
        (ConcreteCategory.hom_ext _ _ fun s ↦ chartMeromorphicPullback_comp B S hS f hf _ φ s) }

/-- The section of the direct image of the sheaf of meromorphic functions over an étale chart
`V` of `Y` attached to a fraction over `V`: the family of its chartwise pullbacks. -/
noncomputable def meromorphicLocalizationMapApp (V : SmallEtale B S hS Y.1) :
    ToType ((regularLocalizationPresheaf B S hS Y).obj (op V)) ⟶
      ((comparisonFunctor B S hS X).op.ran.obj (meromorphicSetSheaf B S hS X).obj).obj
        (op (chartBaseChange B S hS f V)) :=
  (ranChartIsLimit B S hS X (meromorphicSetSheaf B S hS X).obj
    (chartBaseChange B S hS f V)).lift (meromorphicChartCone B S hS f hf V)

/-- The chart projections of `AlgebraicGeometry.Space.meromorphicLocalizationMapApp` are the
chartwise fraction rules. -/
theorem chartProjection_meromorphicLocalizationMapApp (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (s : ToType ((regularLocalizationPresheaf B S hS Y).obj (op V))) :
    (chartProjection B S hS f V j).app (meromorphicSetSheaf B S hS X)
        (meromorphicLocalizationMapApp B S hS f hf V s) =
      chartMeromorphicPullback B S hS f hf V j s :=
  (chartProjection_app B S hS f (meromorphicSetSheaf B S hS X) V j _).trans
    (congrArg (fun φ ↦ φ s)
      ((ranChartIsLimit B S hS X (meromorphicSetSheaf B S hS X).obj
        (chartBaseChange B S hS f V)).fac (meromorphicChartCone B S hS f hf V) j))

/-! ### The comparison of sheaves of meromorphic functions -/

/-- The chartwise fraction rule over a base-changed chart is restriction to the smaller chart
of `Y` followed by the fraction rule there. -/
theorem chartMeromorphicPullback_map {V₁ V₂ : SmallEtale B S hS Y.1} (m : V₁ ⟶ V₂)
    (j : StructuredArrow (op (chartBaseChange B S hS f V₁)) (comparisonFunctor B S hS X).op)
    (x : ToType ((regularLocalizationPresheaf B S hS Y).obj (op V₂))) :
    chartMeromorphicPullback B S hS f hf V₂ (StructuredArrow.mk
        (((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map m)).op ≫ j.hom)) x =
      chartMeromorphicPullback B S hS f hf V₁ j
        (((regularLocalizationPresheaf B S hS Y).map m.op).hom x) := by
  have hcond : (SmallEtale.toOver B S hS X.1).map (𝟙 j.right.unop) ≫
      (chartDiagramOfIndex B S hS f V₂ (StructuredArrow.mk
        (((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map m)).op ≫ j.hom))).g =
      (chartDiagramOfIndex B S hS f V₁ j).g ≫ (SmallEtale.toOver B S hS Y.1).map m := by
    simp only [CategoryTheory.Functor.map_id]
    exact chartBaseChangeMap_map B S hS f m j
  have hcomp := congrArg (fun k : _ →+* _ ↦ k x)
    (chartPullbackMeromorphicFunctions_comp B S hS X.2 Y.2 hf
      (chartDiagramOfIndex B S hS f V₂ (StructuredArrow.mk
        (((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map m)).op ≫ j.hom)))
      (chartDiagramOfIndex B S hS f V₁ j) (𝟙 j.right.unop) m hcond)
  have hid : ∀ z : (regularLocalizationPresheaf B S hS X).obj j.right,
      ((regularLocalizationPresheaf B S hS X).map (𝟙 j.right.unop).op).hom z = z := fun z ↦ by
    rw [op_id, CategoryTheory.Functor.map_id]
    rfl
  exact congrArg
    (((toSheafify (SmallEtale.topology B S hS X.1)
      (regularLocalizationPresheaf B S hS X)).app j.right).hom)
    ((hid _).symm.trans hcomp.symm)

/-- Two sections of the direct image of a sheaf of sets over `V` agree as soon as all their
chart projections agree. -/
theorem chartProjection_ext' (A : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (V : SmallEtale B S hS Y.1)
    {a b : ((comparisonFunctor B S hS X).op.ran.obj A.obj).obj
      (op (chartBaseChange B S hS f V))}
    (h : ∀ j, (chartProjection B S hS f V j).app A a =
      (chartProjection B S hS f V j).app A b) :
    a = b :=
  ranChartCone_π_ext B S hS X A.obj (chartBaseChange B S hS f V) fun j ↦
    (chartProjection_app B S hS f A V j a).symm.trans
      ((h j).trans (chartProjection_app B S hS f A V j b))

/-- Restricting a section of the direct image of a sheaf of sets along a morphism of charts of
`Y` and projecting to a chart of `X` is projecting to the base-changed chart. -/
theorem chartProjection_map' (A : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    {V₁ V₂ : SmallEtale B S hS Y.1} (m : V₁ ⟶ V₂)
    (j : StructuredArrow (op (chartBaseChange B S hS f V₁)) (comparisonFunctor B S hS X).op)
    (a : ((comparisonFunctor B S hS X).op.ran.obj A.obj).obj
      (op (chartBaseChange B S hS f V₂))) :
    (chartProjection B S hS f V₁ j).app A
        (((comparisonFunctor B S hS X).op.ran.obj A.obj).map
          ((spacesBaseChange B S hS f).functor.map
            ((comparisonFunctor B S hS Y).map m)).op a) =
      (chartProjection B S hS f V₂ (StructuredArrow.mk
        (((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map m)).op ≫ j.hom))).app A a := by
  rw [chartProjection_app, chartProjection_app]
  simp only [Functor.RightExtension.coneAt_π_app, types_comp_apply,
    Functor.RightExtension.mk_left, Functor.RightExtension.mk_hom, StructuredArrow.mk_right,
    StructuredArrow.mk_hom_eq_self, ← Functor.map_comp_apply]
  rfl

/-- The map on sections is additive for the transported addition. -/
theorem meromorphicLocalizationMapApp_add (V : SmallEtale B S hS Y.1)
    (x y : ToType ((regularLocalizationPresheaf B S hS Y).obj (op V))) :
    meromorphicLocalizationMapApp B S hS f hf V (x + y) =
      ringAddObj (meromorphicRingSheaf B S hS X) (directImageSections B S hS f V)
        (meromorphicLocalizationMapApp B S hS f hf V x)
        (meromorphicLocalizationMapApp B S hS f hf V y) := by
  refine chartProjection_ext' B S hS f (meromorphicSetSheaf B S hS X) V (fun j ↦ ?_)
  refine (chartProjection_meromorphicLocalizationMapApp B S hS f hf V j (x + y)).trans ?_
  refine ((chartMeromorphicPullback B S hS f hf V j).map_add x y).trans ?_
  refine (congrArg₂ (· + ·)
    (chartProjection_meromorphicLocalizationMapApp B S hS f hf V j x).symm
    (chartProjection_meromorphicLocalizationMapApp B S hS f hf V j y).symm).trans ?_
  exact (sectionsFunctor_map_ringAddHom (meromorphicRingSheaf B S hS X) j.right _ _).symm.trans
    (ringAddObj_naturality (meromorphicRingSheaf B S hS X)
      (chartProjection B S hS f V j) _ _).symm

/-- The map on sections is multiplicative for the transported multiplication. -/
theorem meromorphicLocalizationMapApp_mul (V : SmallEtale B S hS Y.1)
    (x y : ToType ((regularLocalizationPresheaf B S hS Y).obj (op V))) :
    meromorphicLocalizationMapApp B S hS f hf V (x * y) =
      ringMulObj (meromorphicRingSheaf B S hS X) (directImageSections B S hS f V)
        (meromorphicLocalizationMapApp B S hS f hf V x)
        (meromorphicLocalizationMapApp B S hS f hf V y) := by
  refine chartProjection_ext' B S hS f (meromorphicSetSheaf B S hS X) V (fun j ↦ ?_)
  refine (chartProjection_meromorphicLocalizationMapApp B S hS f hf V j (x * y)).trans ?_
  refine ((chartMeromorphicPullback B S hS f hf V j).map_mul x y).trans ?_
  refine (congrArg₂ (· * ·)
    (chartProjection_meromorphicLocalizationMapApp B S hS f hf V j x).symm
    (chartProjection_meromorphicLocalizationMapApp B S hS f hf V j y).symm).trans ?_
  exact (sectionsFunctor_map_ringMulHom (meromorphicRingSheaf B S hS X) j.right _ _).symm.trans
    (ringMulObj_naturality (meromorphicRingSheaf B S hS X)
      (chartProjection B S hS f V j) _ _).symm

/-- The map on sections preserves the zero section. -/
theorem meromorphicLocalizationMapApp_zero (V : SmallEtale B S hS Y.1) :
    meromorphicLocalizationMapApp B S hS f hf V
        (0 : ToType ((regularLocalizationPresheaf B S hS Y).obj (op V))) =
      ringZeroObj (meromorphicRingSheaf B S hS X) (directImageSections B S hS f V) := by
  refine chartProjection_ext' B S hS f (meromorphicSetSheaf B S hS X) V (fun j ↦ ?_)
  refine (chartProjection_meromorphicLocalizationMapApp B S hS f hf V j 0).trans ?_
  refine (chartMeromorphicPullback B S hS f hf V j).map_zero.trans ?_
  exact (sectionsFunctor_map_ringZeroHom (meromorphicRingSheaf B S hS X) j.right _).symm.trans
    (ringZeroObj_naturality (meromorphicRingSheaf B S hS X)
      (chartProjection B S hS f V j)).symm

/-- The map on sections preserves the unit section. -/
theorem meromorphicLocalizationMapApp_one (V : SmallEtale B S hS Y.1) :
    meromorphicLocalizationMapApp B S hS f hf V
        (1 : ToType ((regularLocalizationPresheaf B S hS Y).obj (op V))) =
      ringOneObj (meromorphicRingSheaf B S hS X) (directImageSections B S hS f V) := by
  refine chartProjection_ext' B S hS f (meromorphicSetSheaf B S hS X) V (fun j ↦ ?_)
  refine (chartProjection_meromorphicLocalizationMapApp B S hS f hf V j 1).trans ?_
  refine (chartMeromorphicPullback B S hS f hf V j).map_one.trans ?_
  exact (sectionsFunctor_map_ringOneHom (meromorphicRingSheaf B S hS X) j.right _).symm.trans
    (ringOneObj_naturality (meromorphicRingSheaf B S hS X)
      (chartProjection B S hS f V j)).symm

/-- The map on sections is natural in the étale chart of `Y`. -/
theorem meromorphicLocalizationMapApp_naturality {V₁ V₂ : SmallEtale B S hS Y.1} (m : V₁ ⟶ V₂)
    (x : ToType ((regularLocalizationPresheaf B S hS Y).obj (op V₂))) :
    meromorphicLocalizationMapApp B S hS f hf V₁
        (((regularLocalizationPresheaf B S hS Y).map m.op).hom x) =
      ((comparisonFunctor B S hS X).op.ran.obj (meromorphicSetSheaf B S hS X).obj).map
        ((spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS Y).map m)).op
        (meromorphicLocalizationMapApp B S hS f hf V₂ x) := by
  refine chartProjection_ext' B S hS f (meromorphicSetSheaf B S hS X) V₁ (fun j ↦ ?_)
  refine (chartProjection_meromorphicLocalizationMapApp B S hS f hf V₁ j _).trans (Eq.symm ?_)
  refine (chartProjection_map' B S hS f (meromorphicSetSheaf B S hS X) m j _).trans ?_
  exact (chartProjection_meromorphicLocalizationMapApp B S hS f hf V₂ _ x).trans
    (chartMeromorphicPullback_map B S hS f hf m j x)

/-- The map `𝒮_Y⁻¹𝒪_Y ⟶ f_*𝒦_X` of presheaves of commutative rings, with the direct image
taken in its right Kan extension form: over an étale chart `V` of `Y` it sends a fraction to
the family of its chartwise pullbacks. -/
noncomputable def meromorphicLocalizationMapRan :
    regularLocalizationPresheaf B S hS Y ⟶
      (pullbackCommRingSheaf (SmallEtale.topology B S hS Y.1)
        (smallEtaleDirectImageRan B S hS f)
        (meromorphicFunctionSheaf B S hS X.1 X.2)).obj where
  app Z :=
    letI := inverseImageSectionsCommRing (SmallEtale.topology B S hS Y.1)
      (smallEtaleDirectImageRan B S hS f)
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicFunctionSheaf B S hS X.1 X.2))
      (commRingSheaf_mul_comm (meromorphicFunctionSheaf B S hS X.1 X.2)) Z
    CommRingCat.ofHom
      { toFun := meromorphicLocalizationMapApp B S hS f hf Z.unop
        map_add' := meromorphicLocalizationMapApp_add B S hS f hf Z.unop
        map_mul' := meromorphicLocalizationMapApp_mul B S hS f hf Z.unop
        map_zero' := meromorphicLocalizationMapApp_zero B S hS f hf Z.unop
        map_one' := meromorphicLocalizationMapApp_one B S hS f hf Z.unop }
  naturality := fun _ _ g ↦
    CommRingCat.hom_ext (RingHom.ext fun x ↦
      meromorphicLocalizationMapApp_naturality B S hS f hf g.unop x)

/-- The direct image `f_*𝒦_X` of the sheaf of meromorphic functions of `X`, as a sheaf of
commutative rings on the small étale site of `Y`. -/
noncomputable abbrev meromorphicFunctionSheafDirectImage :
    Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u} :=
  pullbackCommRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
    (smallEtaleDirectImage B S hS f) (meromorphicFunctionSheaf B S hS X.1 X.2)

/-- **The comparison `𝒦_Y ⟶ f_*𝒦_X` of sheaves of meromorphic functions.** When pullbacks of
meromorphic functions are defined for `f`, the chartwise fraction rule `a/b ↦ f^♯a/f^♯b`
assembles into a map from the presheaf of sectionwise localizations into the direct image, and
`𝒦_Y` is the sheafification of that presheaf. -/
noncomputable def meromorphicFunctionSheafComparison :
    meromorphicFunctionSheaf B S hS Y.1 Y.2 ⟶ meromorphicFunctionSheafDirectImage B S hS f :=
  ((sheafificationAdjunction (SmallEtale.topology B S hS Y.1) CommRingCat.{u}).homEquiv
      (regularLocalizationPresheaf B S hS Y) _).symm
    (meromorphicLocalizationMapRan B S hS f hf ≫
      (sheafToPresheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}).map
        (pullbackCommRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
          (smallEtaleDirectImageRanIso B S hS f).inv
          (meromorphicFunctionSheaf B S hS X.1 X.2)))

/-- The comparison restricts along the sheafification map to the chartwise fraction rule. -/
theorem toSheafify_comp_meromorphicFunctionSheafComparison :
    (sheafificationAdjunction (SmallEtale.topology B S hS Y.1) CommRingCat.{u}).unit.app
          (regularLocalizationPresheaf B S hS Y) ≫
        (sheafToPresheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}).map
          (meromorphicFunctionSheafComparison B S hS f hf) =
      meromorphicLocalizationMapRan B S hS f hf ≫
        (sheafToPresheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}).map
          (pullbackCommRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
            (smallEtaleDirectImageRanIso B S hS f).inv
            (meromorphicFunctionSheaf B S hS X.1 X.2)) :=
  ((sheafificationAdjunction (SmallEtale.topology B S hS Y.1) CommRingCat.{u}).homEquiv_unit
      (f := meromorphicFunctionSheafComparison B S hS f hf)).symm.trans
    (Equiv.apply_symm_apply _ _)

end AlgebraicGeometry.Space

end
