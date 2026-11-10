module

public import StacksFrontier.AlgebraicGeometry.Duality.C1590Private.RelativeDualizingSheafInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableLocusOpen

/-!
# The relative dualizing sheaf of an at-worst-nodal family of curves

An at-worst-nodal morphism of relative dimension one (Stacks 0C5A) is syntomic of relative
dimension one, so its fibres are Gorenstein (Stacks 0C15) and have dimension one at every point,
hence are equidimensional of dimension one. Over an affine base, a proper such morphism therefore
has an invertible relative dualizing sheaf `ω_{X/S}` whose restriction to every fibre is the
dualizing sheaf of the fibre (Stacks 0E6R, 0E6Q); this is the property
`AlgebraicGeometry.C1590Private.HasNodalRelativeDualizingSheaf`.

## Main results

* `AlgebraicGeometry.C1590Private.hasGorensteinCurveFibres_of_syntomicOfRelativeDimension` and
  `AlgebraicGeometry.C1590Private.hasGorensteinCurveFibres_of_isAtWorstNodal`.
* `AlgebraicGeometry.C1590Private.hasNodalRelativeDualizingSheaf`.

## References

* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
* [Stacks Project, Tag 0C5A](https://stacks.math.columbia.edu/tag/0C5A)
* [Stacks Project, Tag 0C15](https://stacks.math.columbia.edu/tag/0C15)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.C1590Private

/-- If the fibres of `f` have dimension `d` at every point of `X`, then every fibre has dimension
`d` at each of its points. -/
theorem topologicalKrullDimAt_fiber_eq_of_forall {X S : Scheme.{u}} (f : X ⟶ S) {d : WithBot ℕ∞}
    (h : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = d) (s : S)
    (w : f.fiber s) : topologicalKrullDimAt (f.fiber s) w = d := by
  let z := f.fiberι s w
  have hz : f z = s := (f.fiberHomeo s w).2
  rw [topologicalKrullDimAt_fiber_eq_preimage f s w, ← h z,
    topologicalKrullDimAt_fiber_asFiber_eq_preimage f z]
  exact topologicalKrullDimAt_preimage_congr f hz.symm z hz rfl

/-- **The fibres of a syntomic morphism of relative dimension one are Gorenstein curves**: each
fibre through a point is a Gorenstein scheme, equidimensional of dimension one. -/
theorem hasGorensteinCurveFibres_of_syntomicOfRelativeDimension {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : SyntomicOfRelativeDimension 1 f) : HasGorensteinCurveFibres f := by
  intro x
  have hloc : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (f x)))
    infer_instance
  have hd := topologicalKrullDimAt_fiber_eq_of_forall f hf.2 (f x)
  refine ⟨isGorenstein_fiber_of_syntomic hf.1 (f x),
    equidimensional_of_topologicalKrullDimAt_eq (S.residueField (f x)) (f.fiber (f x))
      (f.fiberToSpecResidueField (f x)) hd, ?_⟩
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  simp_rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim, hd]
  have : Nonempty (f.fiber (f x)) := ⟨f.asFiber x⟩
  exact ciSup_const

/-- **The fibres of an at-worst-nodal morphism of relative dimension one are Gorenstein curves.**
-/
theorem hasGorensteinCurveFibres_of_isAtWorstNodal {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) : HasGorensteinCurveFibres f :=
  hasGorensteinCurveFibres_of_syntomicOfRelativeDimension hf.1

/-- **The relative dualizing sheaf of an at-worst-nodal family of curves** (Stacks 0E6R, 0E6Q):
every proper flat morphism of finite presentation to an affine scheme which is at-worst-nodal of
relative dimension one has an invertible relative dualizing sheaf `ω_{X/S}` whose restriction to
every fibre is the dualizing sheaf of the fibre (Stacks 0BS2). -/
theorem hasNodalRelativeDualizingSheaf : HasNodalRelativeDualizingSheaf.{u} :=
  fun _ _ q _ _ _ _ hq =>
    have h := hasGorensteinCurveFibres_of_isAtWorstNodal hq
    ⟨relativeDualizingSheaf q, isInvertible_relativeDualizingSheaf q h,
      fun u => ⟨relativeDualizingSheafFibreIso q h u⟩⟩

end AlgebraicGeometry.C1590Private

end
