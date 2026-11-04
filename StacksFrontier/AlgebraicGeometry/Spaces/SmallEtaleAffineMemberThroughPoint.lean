module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement

/-!
# A covering sieve has an affine member through every point

A covering sieve of an étale chart `x` of an algebraic space contains, through each point of the
scheme underlying `x`, a member whose own underlying scheme is affine: the sieve contains a
covering family of charts, whose family of underlying schemes is étale-surjective, so one member
has the point in its image, and refining that member by the affine opens of its scheme
(`AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows`) keeps the point in the image
and lands inside the sieve, which is downward closed.

This is the pointwise companion of
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le`, which refines the
whole sieve at once and therefore needs the chart itself to be affine in order to extract a
finite family. Nothing here is finite and nothing is assumed about `x`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.exists_affine_mem_range_of_mem_topology`: the statement
  above.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **A covering sieve of an étale chart contains an affine member through every point of the
chart.** The sieve contains a covering family of charts whose underlying schemes cover, so some
member's underlying scheme hits the point; refining that member by the affine opens of its
scheme keeps the point in the image and stays inside the sieve.

No affineness and no finiteness: unlike
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le` this asks nothing of
`x`, because it produces one member rather than a family covering everything. -/
theorem exists_affine_mem_range_of_mem_topology {x : SmallEtale B S hS F} {T : Sieve x}
    (hT : T ∈ SmallEtale.topology B S hS F x)
    (p : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj x)) :
    ∃ (Q : SmallEtale B S hS F) (φ : Q ⟶ x), T φ ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Q)) ∧
      p ∈ Set.range ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map φ)) := by
  obtain ⟨R, hR, hRT⟩ := (mem_topology_iff B S hS F).1 hT
  obtain ⟨E, rfl, hE⟩ := (SmallEtale.mem_precoverage_iff B S hS F).1 hR
  have hEet : Presieve.ofArrows
      (fun i ↦ (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (E.X i)))
      (fun i ↦ (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (E.f i))) ∈
      Scheme.etalePrecoverage
        ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj x)) := by
    have h := hE.2
    rwa [IsEtaleCovering, PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀,
      Presieve.map_ofArrows] at h
  obtain ⟨i, y, hy⟩ := (Scheme.ofArrows_mem_etalePrecoverage_iff.1 hEet).1 p
  obtain ⟨J, Y, a, haff, -, haet⟩ := exists_affine_etale_ofArrows B S hS F (E.X i)
  obtain ⟨j, z, hz⟩ := (Scheme.ofArrows_mem_etalePrecoverage_iff.1 haet).1 y
  refine ⟨Y j, a j ≫ E.f i,
    T.downward_closed (hRT _ _ (Presieve.ofArrows.mk i)) _, haff j, z, ?_⟩
  rw [Functor.map_comp, Functor.map_comp]
  exact (congrArg ((BigFppfOver.toScheme B S hS).map
    ((SmallEtale.toOver B S hS F).map (E.f i))) hz).trans hy

end AlgebraicGeometry.Space.SmallEtale

end
