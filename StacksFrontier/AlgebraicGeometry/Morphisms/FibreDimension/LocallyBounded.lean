module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded

/-!
# The dimensions of the fibres are locally bounded on the target

For a morphism of schemes `f : X ⟶ Y` locally of finite type and quasi-compact, every point of
`Y` has a neighbourhood over which the fibres of `f` have uniformly bounded dimension: over an
affine open neighbourhood the restriction of `f` is a finite-type morphism to a quasi-compact
scheme, whose fibres are uniformly bounded by
`AlgebraicGeometry.exists_topologicalKrullDim_fiber_le`, and the fibres of the restriction are
the fibres of `f`.

## Main results

* `AlgebraicGeometry.exists_mem_nhds_topologicalKrullDim_fiber_le`: the dimensions of the fibres
  of a quasi-compact morphism locally of finite type are locally bounded on the target.

## References

* [Stacks Project, Tag 0A3V](https://stacks.math.columbia.edu/tag/0A3V)
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry

/-- **The dimensions of the fibres of a quasi-compact morphism locally of finite type are locally
bounded on the target.** -/
theorem exists_mem_nhds_topologicalKrullDim_fiber_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (y : Y) :
    ∃ U ∈ 𝓝 y, ∃ n : ℕ, ∀ y' ∈ U, topologicalKrullDim (f.fiber y') ≤ n := by
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top y)
  have : IsAffine V := hV
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_fiber_le (f ∣_ V)
  refine ⟨V, V.isOpen.mem_nhds hyV, n, fun y' hy' => ?_⟩
  let y'' : (V : Scheme.{u}) := ⟨y', hy'⟩
  refine le_trans ?_ (hn y'')
  rw [IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y').isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ ((f ∣_ V).fiberHomeo y'').isHomeomorph]
  let φ : f ⁻¹' {y'} → (f ∣_ V) ⁻¹' {y''} := fun x =>
    ⟨⟨x.1, show f x.1 ∈ V by rw [show f x.1 = y' from x.2]; exact hy'⟩,
      Subtype.ext ((morphismRestrict_base_coe f V _).trans x.2)⟩
  have hind : IsInducing φ :=
    .of_comp (Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _)
      (continuous_subtype_val.comp continuous_subtype_val) .subtypeVal
  exact hind.topologicalKrullDim_le

end AlgebraicGeometry
