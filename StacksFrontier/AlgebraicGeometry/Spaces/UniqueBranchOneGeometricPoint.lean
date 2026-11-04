module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BranchCount

/-!
# One geometric point suffices for the unique-branch criterion

Condition (5) of [Stacks Project, Tag 06DK] at a point `x` of an algebraic space `F` asks that
the étale local ring of `F` at *every* geometric point above `x` have a unique minimal prime.
The number of minimal primes of that étale local ring is however the same at every geometric
point above `x`, being the number of geometric branches of any étale scheme chart of `F` at any
point above `x` ([Stacks Project, Tag 0DQ3], conditions (4) and (5), together with the étale
locality of that count, [Stacks Project, Tag 04N2]).  So the condition only has to be checked at
*one* geometric point above `x`.

## Main results

* `AlgebraicGeometry.Space.hasUniqueMinimalPrimeAtGeometricPoints_of_geometricPoint`: if the
  étale local ring of `F` at a single geometric point above `x` has a unique minimal prime, then
  it does at every geometric point above `x`.

## Implementation notes

The passage between the two quantifications goes through the branch counts of
`AlgebraicGeometry.Space.BranchCount`: a unique minimal prime at the given geometric point is
`AlgebraicGeometry.Space.HasEtaleLocalRingMinimalPrimeCount` with `n = 1` *at that point*, which
Tag 0DQ3 turns into the count of geometric branches of the chart of a small étale neighbourhood
of it, which Tag 04N2 propagates to every chart above `x`, which Tag 0DQ3 turns back into the
count at every geometric point above `x`.

## References

* [Stacks Project, Tag 06DK](https://stacks.math.columbia.edu/tag/06DK)
* [Stacks Project, Tag 0DQ3](https://stacks.math.columbia.edu/tag/0DQ3)
* [Stacks Project, Tag 04N2](https://stacks.math.columbia.edu/tag/04N2)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

/-- A set has exactly one element exactly when it has a unique member. -/
private theorem encard_eq_one_iff_existsUnique {α : Type*} (s : Set α) :
    s.encard = 1 ↔ ∃! a, a ∈ s := by
  rw [Set.encard_eq_one]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl, fun _ hy => hy⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, Set.eq_singleton_iff_unique_mem.mpr ⟨ha, h⟩⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Condition (5) of Stacks 06DK is checked at a single geometric point.**  If the étale local
ring of an algebraic space `F` at one geometric point above a point `x` has a unique minimal
prime, then so does the étale local ring at every geometric point above `x`.

The number of minimal primes of the étale local ring is the number of geometric branches of an
étale scheme chart (Tag 0DQ3, conditions (4) and (5)), and that number is the same on every
chart above `x` (Tag 04N2). -/
theorem hasUniqueMinimalPrimeAtGeometricPoints_of_geometricPoint
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F)
    (g : GeometricPoint B S hS F) (hg : GeometricPoint.LiesOver g x)
    (h : ∃! q : Ideal (etaleLocalRing B S hS F g), q ∈ minimalPrimes _) :
    HasUniqueMinimalPrimeAtGeometricPoints B S hS F x := by
  obtain ⟨U, a, hsurj, hetale⟩ := hF.exists_atlas
  obtain ⟨⟨V, -⟩⟩ := exists_pointed_smallEtaleNeighborhood B S hS F hF g a hsurj hetale
  have hV : numberOfGeometricBranches (chartScheme V.chart)
      ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField)) =
        ((1 : ℕ) : ℕ∞) := by
    rw [← encard_minimalPrimes_etaleLocalRing_eq B S hS hF V, Nat.cast_one]
    exact (encard_eq_one_iff_existsUnique _).mpr h
  have hall := (forall_etale_chart_iff_exists_etale_chart B S hS F hF x
    (fun G : GermOfScheme.{u} ↦ numberOfGeometricBranches G.scheme G.point = ((1 : ℕ) : ℕ∞))
    (GermOfScheme.isEtaleLocal_numberOfGeometricBranches_eq ((1 : ℕ) : ℕ∞))).mpr
    ⟨V.chart.obj.left, V.chart.obj.hom, V.chart.property, chartFieldValuedPoint V,
      (chartFieldValuedPoint_pointsMap V).trans hg, hV⟩
  have hcount : HasGeometricBranchCount B S hS x 1 := by
    intro W b w hb hw
    obtain ⟨q, rfl, hq⟩ := hw
    exact hall W b ((isEtale_iff_presheaf_of_yoneda B S hS b).mp hb) q hq
  intro p hp
  refine (encard_eq_one_iff_existsUnique _).mp ?_
  rw [← Nat.cast_one]
  exact (geometricBranchCount_iff_etaleLocalRingMinimalPrimeCount B S hS hF x 1).mp hcount p hp

end AlgebraicGeometry.Space

end
