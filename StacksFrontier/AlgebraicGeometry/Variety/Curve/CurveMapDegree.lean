module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.FibreDegreeAdd
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardLocallyTrivial

/-!
# The degree of an endomorphism of a proper curve, and the degree of a pulled-back line bundle

Let `f : C ⟶ Spec k` be a proper curve over a field and `φ : C ⟶ C` a morphism over `k`. The
degree `deg φ` of [Stacks, Tag 03U1] is the degree `[R(C) : φ^* R(C)]` of the extension of
function fields when `φ` is not constant ([Stacks, Tag 02NY], `AlgebraicGeometry.degreeOver`),
and `0` when `φ` is constant: a constant map contracts `C` to a point, and its graph meets a
fibre `C × {c}` in no point, or in all of `C`.

Pulling a line bundle back along a nonconstant `φ` multiplies its degree by `deg φ`: this is
[Stacks, Tag 0AYZ] in rank one, transported to the Picard group.

## Main definitions

* `AlgebraicGeometry.CurveGraph.curveMapDegree`: `deg φ`.

## Main results

* `AlgebraicGeometry.CurveGraph.picardDegree_eq_invertibleCurveDegree_rep`: the degree of a
  Picard class is the degree of its chosen representative.
* `AlgebraicGeometry.CurveGraph.picardDegree_schemePullbackClass_of_not_constant`:
  `deg(φ^* L) = deg φ · deg L` for nonconstant `φ`.
* `AlgebraicGeometry.CurveGraph.schemePullbackClass_eq_zero_of_constant`: a constant morphism
  pulls every line bundle back to the trivial one.
* `AlgebraicGeometry.CurveGraph.picardDegree_schemePullbackClass`: `deg(φ^* L) = deg φ · deg L`
  for every `φ` over `k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.PicardCurve
open AlgebraicGeometry.SmallEtale (zariskiStructureIsSheaf)

universe u

namespace AlgebraicGeometry.CurveGraph

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))

open Classical in
/-- **The degree `deg φ`** of a morphism `φ : C ⟶ C` over `k` of a curve: the degree of the
extension of function fields when `φ` is nonconstant, and `0` when it is constant. -/
def curveMapDegree [IsCurve k f] (φ : C ⟶ C) (w : φ ≫ f = f) : ℕ :=
  if hnc : ¬ ∃ y : C, ∀ x : C, φ.base x = y then
    @degreeOver C C φ _ _ (locallyOfFiniteType_of_isCurve_comp k f f φ w)
      (isDominant_of_not_constant k f f φ hnc)
  else 0

/-- For a nonconstant `φ`, `deg φ` is the degree of the extension of function fields. -/
theorem curveMapDegree_of_not_constant [IsCurve k f] (φ : C ⟶ C) (w : φ ≫ f = f)
    (hnc : ¬ ∃ y : C, ∀ x : C, φ.base x = y) :
    curveMapDegree f φ w = @degreeOver C C φ _ _ (locallyOfFiniteType_of_isCurve_comp k f f φ w)
      (isDominant_of_not_constant k f f φ hnc) := by
  rw [curveMapDegree, dite_eq_left hnc]

/-- For a constant `φ`, `deg φ = 0`. -/
theorem curveMapDegree_of_constant [IsCurve k f] (φ : C ⟶ C) (w : φ ≫ f = f)
    (hc : ∃ y : C, ∀ x : C, φ.base x = y) : curveMapDegree f φ w = 0 := by
  rw [curveMapDegree, dite_eq_right (not_not.mpr hc)]

/-- **The degree of a Picard class is the degree of its chosen representative.** -/
theorem picardDegree_eq_invertibleCurveDegree_rep [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim C ≤ 1) (y : Stacks.Picard.ofScheme C) :
    picardDegree k f hdim (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace y) =
      letI := isInvertible_of_stacks_isInvertible C (rep y)
        (Stacks.Picard.picardRepresentative C.toRingedSpace y).property
      invertibleCurveDegree k f hdim (rep y) := by
  have hS : Stacks.SheafOfModules.IsInvertible C.presheaf (zariskiStructureIsSheaf C) (rep y) :=
    (Stacks.Picard.picardRepresentative C.toRingedSpace y).property
  have hy : Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace y =
      schemePicardClassOf C (rep y) hS :=
    (congrArg (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace)
      (Stacks.Picard.classOf_picardRepresentative C.toRingedSpace y)).symm.trans
      (Stacks.GluePicard.picardModelAddEquiv_classOf _ _ hS)
  rw [hy, picardDegree_classOf]

/-- **Pulling back along a nonconstant endomorphism multiplies degrees by `deg φ`**
([Stacks, Tag 0AYZ] in rank one): `deg(φ^* L) = deg φ · deg L`. -/
theorem picardDegree_schemePullbackClass_of_not_constant [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim C ≤ 1) (φ : C ⟶ C) (w : φ ≫ f = f)
    (hnc : ¬ ∃ y : C, ∀ x : C, φ.base x = y) (y : Stacks.Picard.ofScheme C) :
    picardDegree k f hdim (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace
        (Stacks.Picard.schemePullbackClass φ y)) =
      (curveMapDegree f φ w : ℤ) *
        picardDegree k f hdim (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace y) := by
  obtain ⟨e⟩ := nonempty_rep_schemePullbackClass_iso φ y
  let := isInvertible_of_stacks_isInvertible C (rep y)
    (Stacks.Picard.picardRepresentative C.toRingedSpace y).property
  let := isInvertible_of_stacks_isInvertible C (rep (Stacks.Picard.schemePullbackClass φ y))
    (Stacks.Picard.picardRepresentative C.toRingedSpace
      (Stacks.Picard.schemePullbackClass φ y)).property
  let : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback φ).obj (rep y)) :=
    isInvertible_of_stacks_isInvertible C _
      (Stacks.Picard.isInvertible_of_iso e
        (Stacks.Picard.picardRepresentative C.toRingedSpace
          (Stacks.Picard.schemePullbackClass φ y)).property)
  rw [picardDegree_eq_invertibleCurveDegree_rep, picardDegree_eq_invertibleCurveDegree_rep,
    invertibleCurveDegree_eq_of_iso k f hdim e, invertibleCurveDegree_eq_curveDegree_one,
    invertibleCurveDegree_eq_curveDegree_one, curveMapDegree_of_not_constant f φ w hnc]
  exact curveDegree_pullback_eq_degreeOver_mul k f f φ w hnc (rep y) 1

/-- **Pulling back along a constant morphism kills every Picard class.** -/
theorem schemePullbackClass_eq_zero_of_constant {Y : Scheme.{u}} (φ : Y ⟶ C)
    (hc : ∃ y : C, ∀ x : Y, φ.base x = y) (L : Stacks.Picard.ofScheme C) :
    Stacks.Picard.schemePullbackClass φ L = 0 := by
  obtain ⟨y, hy⟩ := hc
  obtain ⟨U, hyU, hU⟩ := Stacks.Picard.exists_mem_schemePullbackClass_eq_zero L y
  have hrange : Set.range φ.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨x, rfl⟩
    rwa [Scheme.Opens.range_ι, hy x]
  have hfac : IsOpenImmersion.lift U.ι φ hrange ≫ U.ι = φ := IsOpenImmersion.lift_fac _ _ _
  rw [← hfac, ← Stacks.Picard.schemePullbackClass_comp, hU,
    Stacks.PicardFunctor.schemePullbackClass_zero]

/-- **Pulling back along any endomorphism over `k` multiplies degrees by `deg φ`**:
`deg(φ^* L) = deg φ · deg L`, including a constant `φ`, for which both sides vanish. -/
theorem picardDegree_schemePullbackClass [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim C ≤ 1) (φ : C ⟶ C) (w : φ ≫ f = f)
    (y : Stacks.Picard.ofScheme C) :
    picardDegree k f hdim (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace
        (Stacks.Picard.schemePullbackClass φ y)) =
      (curveMapDegree f φ w : ℤ) *
        picardDegree k f hdim (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace y) := by
  by_cases hnc : ¬ ∃ y : C, ∀ x : C, φ.base x = y
  · exact picardDegree_schemePullbackClass_of_not_constant f hdim φ w hnc y
  · have hc := not_not.mp hnc
    rw [schemePullbackClass_eq_zero_of_constant φ hc, curveMapDegree_of_constant f φ w hc,
      map_zero, map_zero, Nat.cast_zero, zero_mul]

end AlgebraicGeometry.CurveGraph

end
