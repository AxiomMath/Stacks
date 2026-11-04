module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLciOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesNodalLciPlus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPlusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmooth
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal

/-!
# Condition (o) for the open substacks of curves of Sections 0DZT to 0DSX

The properties of families of curves cutting out `Curves^{lci}` (Tag 0DZV), `Curves^{+}`
(Tag 0DZW), `Curves^{lci+}` (Tag 0DZX), `Curves^{smooth}` (Tag 0DZZ) and `Curves^{nodal}`
(Tag 0DSY) satisfy condition (o) of Section 0E0E, `AlgebraicGeometry.IsOpenCurvesLocus`. By
Tag 0E0E they therefore cut out open substacks of the stack of curves.

## Main results

* `AlgebraicGeometry.isOpenCurvesLocus_isLciFamily`: `Curves^{lci}`.
* `AlgebraicGeometry.isOpenCurvesLocus_isFiniteNonSmoothLocus`: `Curves^{+}`.
* `AlgebraicGeometry.isOpenCurvesLocus_lciPlus`: `Curves^{lci+} = Curves^{lci} ∩ Curves^{+}`.
* `AlgebraicGeometry.isOpenCurvesLocus_isSmoothFamily`: `Curves^{smooth}`.
* `AlgebraicGeometry.isOpenCurvesLocus_isAtWorstNodal`: `Curves^{nodal}`.
* `AlgebraicGeometry.isAtWorstNodal_le_lciPlus` and `AlgebraicGeometry.isSmoothFamily_le_lciPlus`:
  `Curves^{nodal} ⊂ Curves^{lci+}` and `Curves^{smooth} ⊂ Curves^{lci+}`.

## Implementation notes

Each open locus in the base was produced earlier in exactly the form of condition (o): by
Tag 06CE for local complete intersections, by Tag 0A4Y and the base change of the quasi-finite
locus for `Curves^{+}`, by Tag 0DZI for smoothness, and by Tag 0DSH for at-worst-nodal families
(a private lemma of `StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal`, reached by `import all`).

## References

* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0DZX](https://stacks.math.columbia.edu/tag/0DZX)
* [Stacks Project, Tag 0E00](https://stacks.math.columbia.edu/tag/0E00)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Condition (o) for families of curves with a local complete intersection structure
morphism: the property cutting out `Curves^{lci}`. -/
theorem isOpenCurvesLocus_isLciFamily : IsOpenCurvesLocus B hZ (IsLciFamily B hZ) :=
  fun G => CurveFamily.exists_isOpenSubspace_lci B hZ G

/-- Condition (o) for families of curves whose reduced non-smooth locus is finite over the base:
the property cutting out `Curves^{+}`. -/
theorem isOpenCurvesLocus_isFiniteNonSmoothLocus :
    IsOpenCurvesLocus B hZ (IsFiniteNonSmoothLocus B hZ) :=
  fun G => CurveFamily.exists_isOpenSubspace_finiteNonSmoothLocus B hZ G

/-- Condition (o) for the property cutting out `Curves^{lci+} = Curves^{lci} ∩ Curves^{+}`. -/
theorem isOpenCurvesLocus_lciPlus :
    IsOpenCurvesLocus B hZ (fun F => IsLciFamily B hZ F ∧ IsFiniteNonSmoothLocus B hZ F) :=
  (isOpenCurvesLocus_isLciFamily B hZ).and (isOpenCurvesLocus_isFiniteNonSmoothLocus B hZ)

/-- Condition (o) for smooth families of curves: the property cutting out `Curves^{smooth}`. -/
theorem isOpenCurvesLocus_isSmoothFamily : IsOpenCurvesLocus B hZ (IsSmoothFamily B hZ) :=
  fun G => CurveFamily.exists_isOpenSubspace_smooth B hZ G

/-- Condition (o) for families of curves which are at-worst-nodal of relative dimension one: the
property cutting out `Curves^{nodal}`. -/
theorem isOpenCurvesLocus_isAtWorstNodal :
    IsOpenCurvesLocus B hZ (fun F : CurveFamily B hZ =>
      Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom) :=
  fun G => exists_nodal_baseOpen B hZ G

/-- `Curves^{nodal} ⊂ Curves^{lci+}`: an at-worst-nodal family of relative dimension one has a
local complete intersection structure morphism and finite reduced non-smooth locus. -/
theorem isAtWorstNodal_le_lciPlus (F : CurveFamily B hZ)
    (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom) :
    IsLciFamily B hZ F ∧ IsFiniteNonSmoothLocus B hZ F :=
  ⟨CurveFamily.isLciFamily_of_isAtWorstNodal B hZ F hF,
    CurveFamily.isFiniteNonSmoothLocus_of_isAtWorstNodal B hZ F hF⟩

attribute [local instance] Space.pointTopology

/-- `Curves^{smooth} ⊂ Curves^{lci+}`: a smooth family of curves has a local complete intersection
structure morphism, and its reduced non-smooth locus, being empty, is finite over the base. -/
theorem isSmoothFamily_le_lciPlus (F : CurveFamily B hZ) (hF : IsSmoothFamily B hZ F) :
    IsLciFamily B hZ F ∧ IsFiniteNonSmoothLocus B hZ F := by
  classical
  refine ⟨(isLciFamily_iff_isSyntomicFamily B hZ F).mpr
    (Space.holdsOnEveryEtaleChart_mono B integerBase hZ
      (fun g hg => by have := hg; exact syntomic_of_smooth g) hF), ?_⟩
  let X := F.total.1
  have hX : IsAlgebraicSpace B integerBase hZ X := F.total.2
  let f : X ⟶ yoneda.obj F.base := F.toBase.hom
  have hY : IsAlgebraicSpace B integerBase hZ (yoneda.obj F.base) :=
    isAlgebraicSpace_yoneda B integerBase hZ F.base
  have hall : ∀ x, Space.IsSmoothAt B integerBase hZ f x :=
    ((Space.isSmooth_tfae B integerBase hZ hX hY f).out 1 2).mp hF
  let T : Set (Space.points B integerBase hZ X) :=
    {x | ¬ Space.IsSmoothAt B integerBase hZ f x}
  have hT : IsClosed T := (Space.isOpen_setOf_isSmoothAt B integerBase hZ hX f).isClosed_compl
  let Z := Space.reducedClosedSubspace B integerBase hZ X hX T hT
  have hZcl : Space.IsClosedSubspace B integerBase hZ Z :=
    Space.isClosedSubspace_reducedClosedSubspace B integerBase hZ X hX T hT
  have hrange := Space.range_pointsMap_ι_reducedClosedSubspace B integerBase hZ X hX T hT
  refine ⟨Z, hZcl, hrange,
    Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B integerBase hZ X hX T hT, ?_⟩
  have hZa : IsAlgebraicSpace B integerBase hZ Z.toFunctor := hZcl.1
  have hproper : Space.IsProper B integerBase hZ (Z.ι ≫ f) :=
    Space.isProper_comp B integerBase hZ hZa hX hY Z.ι f
      (Space.isProper_ι_reducedClosedSubspace B integerBase hZ X hX T hT) F.proper
  refine Space.isFinite_of_isProper_of_isLocallyQuasiFinite B integerBase hZ hZa hY _ hproper
    ((Space.isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B integerBase hZ hZa hY _).mpr
      fun z => ?_)
  have hz : Space.pointsMap B integerBase hZ Z.toFunctor Z.ι z ∈ T := hrange ▸ ⟨z, rfl⟩
  exact absurd (hall _) hz

end AlgebraicGeometry

end
