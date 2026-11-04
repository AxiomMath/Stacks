module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletionDiscreteValuation
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus

/-!
# Regular and smooth projective compactifications of a regular curve

Let `k` be a field and let `X` be a regular curve over `k`. [Stacks, Tag 0H1F] records that `X`
has a *nonsingular projective* compactification: an open immersion `j : X ⟶ X̄` over `k` into a
regular projective curve whose complement is a finite set of closed points, and that over a
perfect field both `X` and `X̄` are then smooth over `k`. This file proves both assertions.

## Main results

* `AlgebraicGeometry.smooth_of_isRegular_of_perfectField`: a regular scheme locally of finite
  type over a perfect field is smooth over that field.
* `AlgebraicGeometry.isRegular_of_isOpenImmersion_of_isDiscreteValuationRing_stalk_compl`: a
  scheme containing a regular scheme as an open subscheme and having discrete valuation rings at
  the points outside it is regular.
* `AlgebraicGeometry.topologicalKrullDim_le_one_of_isOpenImmersion_of_isDVR_stalk_compl`: the same
  configuration has dimension at most one as soon as the open subscheme does.
* `AlgebraicGeometry.exists_isRegular_isProjectiveMorphism_compactification`: the first assertion
  of the remark, the nonsingular projective compactification.
* `AlgebraicGeometry.exists_smooth_isProjectiveMorphism_compactification_of_perfectField`: the
  second assertion, smoothness of both curves over a perfect field.

## Implementation notes

The compactification is the one of [Stacks, Tag 0BXW], in the form
`Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced`.

"Nonsingular" is `AlgebraicGeometry.IsRegular` and "projective" is
`AlgebraicGeometry.IsProjectiveMorphism`, the H-projective predicate of [Stacks, Tag 01W8].
"Curve over `k`" is `AlgebraicGeometry.IsCurve`.

## References

* [Stacks Project, Tag 0H1F](https://stacks.math.columbia.edu/tag/0H1F)
* [Stacks Project, Tag 0BXW](https://stacks.math.columbia.edu/tag/0BXW)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 0B8X](https://stacks.math.columbia.edu/tag/0B8X)
* [Stacks Project, Tag 04MU](https://stacks.math.columbia.edu/tag/04MU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Smoothness over a perfect field -/

/-- **A regular scheme locally of finite type over a perfect field is smooth over it.** -/
@[ega "0 19.0.2" "IV",
  ega "IV 17.15.1" "special case",
  ega "IV 17.15.2" "Over a perfect field",
  ega "IV 17.15.5" "special case", sga "1 II 5.4" "more general", sga "6 XIV 4.2" "Clause"]
public theorem smooth_of_isRegular_of_perfectField (k : Type u) [Field k] [PerfectField k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (hX : IsRegular X) :
    Smooth f := by
  have : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  intro x _
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).2 x
  exact InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap f x
    ((Set.ext_iff.mp (smoothAt_locus_eq_regular_locus k f) x).2 hreg)

/-! ### Regularity, dimension and irreducibility of a completion -/

/-- **A scheme with a regular open subscheme and discrete valuation rings at the points outside
it is regular.** -/
public theorem isRegular_of_isOpenImmersion_of_isDiscreteValuationRing_stalk_compl
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (j : X ⟶ Y) [IsOpenImmersion j]
    (hX : IsRegular X)
    (hdvr : ∀ y : Y, y ∉ Set.range j.base → ∃ _ : IsDomain (Y.presheaf.stalk y),
      IsDiscreteValuationRing (Y.presheaf.stalk y)) :
    IsRegular Y := by
  refine ((isRegular_tfae Y).out 1 2 rfl rfl).mpr ⟨inferInstance, fun y => ?_⟩
  by_cases hy : y ∈ Set.range (j.base : X → Y)
  · obtain ⟨x, rfl⟩ := hy
    have hx : IsRegularLocalRing (X.presheaf.stalk x) :=
      (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).2 x
    exact IsRegularLocalRing.of_ringEquiv
      (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.symm
  · obtain ⟨_, _⟩ := hdvr y hy
    infer_instance

/-- **A scheme with an open subscheme of dimension at most one and discrete valuation rings at
the points outside it has dimension at most one.** -/
public theorem topologicalKrullDim_le_one_of_isOpenImmersion_of_isDVR_stalk_compl
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1)
    (hdvr : ∀ y : Y, y ∉ Set.range j.base → ∃ _ : IsDomain (Y.presheaf.stalk y),
      IsDiscreteValuationRing (Y.presheaf.stalk y)) :
    topologicalKrullDim (Y : Type u) ≤ 1 := by
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk Y]
  refine iSup_le fun y => ?_
  by_cases hy : y ∈ Set.range (j.base : X → Y)
  · obtain ⟨x, rfl⟩ := hy
    have he : ringKrullDim (Y.presheaf.stalk (j.base x)) = ringKrullDim (X.presheaf.stalk x) :=
      ringKrullDim_eq_of_ringEquiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
    rw [he]
    refine le_trans (le_iSup (fun z : X => ringKrullDim (X.presheaf.stalk z)) x) ?_
    rw [← topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
    exact hdim
  · obtain ⟨_, _⟩ := hdvr y hy
    exact (IsDiscreteValuationRing.ringKrullDim_eq_one (Y.presheaf.stalk y)).le

/-- **The target of a dominant morphism with irreducible source is irreducible.** -/
public theorem irreducibleSpace_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IsDominant f] : IrreducibleSpace Y := by
  have hrange : IsIrreducible (Set.range (f.base : X → Y)) := by
    have h := (IrreducibleSpace.isIrreducible_univ X).image (f.base : X → Y)
      (Continuous.continuousOn (by fun_prop))
    rwa [Set.image_univ] at h
  have hcl : closure (Set.range (f.base : X → Y)) = Set.univ :=
    (IsDominant.denseRange (f := f)).closure_eq
  refine (irreducibleSpace_def Y).mpr ?_
  rw [Set.top_eq_univ, ← hcl]
  exact hrange.closure

/-! ### The two assertions of the remark -/

/-- Let `k` be a field and let `X` be a regular curve over `k`. Then there is a nonsingular
projective curve `X̄` over `k` and an open immersion `j : X ⟶ X̄` over `k` whose complement is a
finite set of closed points of `X̄`. -/
@[stacks 0H1F "the regular projective compactification"]
public theorem exists_isRegular_isProjectiveMorphism_compactification
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsCurve k p]
    (hX : IsRegular X) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k)) (j : X ⟶ Y) (hj : IsOpenImmersion j),
      letI : IsOpenImmersion j := hj
      j ≫ q = p ∧ IsCurve k q ∧ IsProjectiveMorphism q ∧ IsRegular Y ∧
        ((Set.range j.base)ᶜ).Finite ∧
        ∀ y : Y, y ∉ Set.range j.base → IsClosed ({y} : Set Y) := by
  have hdimX : topologicalKrullDim (X : Type u) = 1 :=
    IsCurve.topologicalKrullDim_eq_one (k := k) (f := p)
  obtain ⟨Y, q, j, hj, hjq, hproj, hdom, -, hfin, hbdry⟩ :=
    Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced
      k p hdimX.le
  have _ : IsProper q := isProper_of_isProjectiveMorphism q hproj
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have hdvr : ∀ y : Y, y ∉ Set.range j.base → ∃ _ : IsDomain (Y.presheaf.stalk y),
      IsDiscreteValuationRing (Y.presheaf.stalk y) := fun y hy => (hbdry y hy).2
  have hregY : IsRegular Y :=
    isRegular_of_isOpenImmersion_of_isDiscreteValuationRing_stalk_compl j hX hdvr
  have hnormalY : IsNormal Y := isNormal_of_isRegular Y hregY
  have _ : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := fun y => by
    have := hnormalY.stalk_isDomain y
    infer_instance
  have : AlgebraicGeometry.IsReduced Y := isReduced_of_isReduced_stalk Y
  have : IrreducibleSpace Y := irreducibleSpace_of_isDominant j
  have : AlgebraicGeometry.IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  have hdimY : topologicalKrullDim (Y : Type u) = 1 :=
    le_antisymm
      (topologicalKrullDim_le_one_of_isOpenImmersion_of_isDVR_stalk_compl j hdimX.le hdvr)
      (hdimX ▸ Topology.IsInducing.topologicalKrullDim_le
        (f := (j.base : X → Y)) j.isOpenEmbedding.isEmbedding.isInducing)
  have : IsCurve k q :=
    { toIsVariety := { }
      topologicalKrullDim_eq_one := hdimY }
  exact ⟨Y, q, j, hj, hjq, inferInstance, hproj, hregY, hfin, fun y hy => (hbdry y hy).1⟩

/-- Let `k` be a perfect field and let `X` be a regular curve over `k`. Then `X` is smooth over
`k`, and there is a nonsingular projective curve `X̄` over `k`, smooth over `k`, with an open
immersion `j : X ⟶ X̄` over `k` whose complement is a finite set of closed points of `X̄`. -/
@[stacks 0H1F "the smooth projective compactification over a perfect field"]
public theorem exists_smooth_isProjectiveMorphism_compactification_of_perfectField
    (k : Type u) [Field k] [PerfectField k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsCurve k p] (hX : IsRegular X) :
    Smooth p ∧ ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k)) (j : X ⟶ Y) (hj : IsOpenImmersion j),
      letI : IsOpenImmersion j := hj
      j ≫ q = p ∧ IsCurve k q ∧ IsProjectiveMorphism q ∧ IsRegular Y ∧ Smooth q ∧
        ((Set.range j.base)ᶜ).Finite ∧
        ∀ y : Y, y ∉ Set.range j.base → IsClosed ({y} : Set Y) := by
  obtain ⟨Y, q, j, hj, hjq, hcurve, hproj, hregY, hfin, hbdry⟩ :=
    exists_isRegular_isProjectiveMorphism_compactification k p hX
  exact ⟨smooth_of_isRegular_of_perfectField k p hX, Y, q, j, hj, hjq, hcurve, hproj, hregY,
    smooth_of_isRegular_of_perfectField k q hregY, hfin, hbdry⟩

end AlgebraicGeometry

end
