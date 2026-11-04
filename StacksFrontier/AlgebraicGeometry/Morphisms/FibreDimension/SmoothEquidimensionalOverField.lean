module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness

/-!
# Smooth schemes over a field which are equidimensional of dimension `d`

A scheme `X` locally of finite type over a field `k` which is equidimensional of dimension `d`
has relative dimension `d` over `k` in the sense of [Stacks, Tag 02NJ]: the unique fibre of
`X ⟶ Spec k` is homeomorphic to `X`. If `X` is moreover smooth over `k`, it is smooth of relative
dimension `d`, the dimension of the fibre through every point being `d`.

## Main results

* `AlgebraicGeometry.relativeDimension_of_equidimensional`: relative dimension `d`.
* `AlgebraicGeometry.smoothOfRelativeDimension_of_equidimensional`: smooth of relative
  dimension `d`.

## References

* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A scheme over a field, equidimensional of dimension `d`, is of relative dimension `d`.**
The unique fibre of the structure morphism is homeomorphic to the scheme itself, so both clauses
of `AlgebraicGeometry.RelativeDimension` transport from the scheme to the fibre. -/
theorem relativeDimension_of_equidimensional (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (hequi : Equidimensional X) (d : ℕ)
    (hdim : topologicalKrullDim X = d) : RelativeDimension f d := by
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  intro s _
  have hpre : f.base ⁻¹' {s} = (Set.univ : Set X) := by
    ext y
    simp [Subsingleton.elim (f.base y) s]
  let e : f.fiber s ≃ₜ X :=
    (f.fiberHomeo s).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ X))
  exact ⟨Equidimensional.of_homeomorph e hequi,
    (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).trans hdim⟩

/-- **A smooth scheme over a field which is equidimensional of dimension `d` is smooth of
relative dimension `d`.** -/
theorem smoothOfRelativeDimension_of_equidimensional (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (hequi : Equidimensional X) (d : ℕ)
    (hdim : topologicalKrullDim X = d) : SmoothOfRelativeDimension d f :=
  Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq f d fun x =>
    topologicalKrullDimAt_fiber_eq_of_relativeDimension f ⊤ d
      (RelativeDimension.comp_isOpenImmersion (⊤ : X.Opens).ι f
        (relativeDimension_of_equidimensional k f hequi d hdim)) x trivial

end AlgebraicGeometry
