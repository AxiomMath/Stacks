module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import StacksCore.Tactic.StacksAttribute

/-!
# Lifting a geometric point through an étale covering of an étale neighborhood

Let `s : Spec Ω ⟶ S` be a geometric point of a scheme `S`, with `Ω` separably closed, and let
`(U, u)` be an étale neighborhood of `s`: an étale morphism `f : U ⟶ S` together with a lift
`u : Spec Ω ⟶ U` of `s`. Every étale covering `{φᵢ : Uᵢ ⟶ U}` of `U` has a member `Uᵢ` to which
`u` lifts, so that `φᵢ` is a morphism of étale neighborhoods of `s`.

## Main results

* `AlgebraicGeometry.Scheme.Cover.exists_etaleNeighborhood_lift`: a member of an étale covering
  of an étale neighborhood of a geometric point carries a lift of the geometric point making
  it a morphism of étale neighborhoods.

## Implementation notes

Geometric points are taken with values in a separably closed field, which is more general than
the algebraically closed fields of Stacks 03PO.

## References

* [Stacks Project, Tag 03PR](https://stacks.math.columbia.edu/tag/03PR)
-/

@[expose] public section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.Scheme.Cover

/-- Let `s : Spec Ω ⟶ S` be a geometric point of `S`, with `Ω` separably closed, and let
`(U, u)` be an étale neighborhood of `s`, that is `f : U ⟶ S` is étale and `u ≫ f = s`. Then
for every étale covering `𝒰` of `U` there are an index `i` and a lift `uᵢ` of `u` to `𝒰.X i`,
so that `(𝒰.X i, uᵢ)` is an étale neighborhood of `s` and `𝒰.f i` is a morphism of étale
neighborhoods `(𝒰.X i, uᵢ) ⟶ (U, u)`. -/
@[stacks 03PR]
theorem exists_etaleNeighborhood_lift {S U : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (f : U ⟶ S) [Etale f] (u : Spec (.of Ω) ⟶ U) (hu : u ≫ f = s)
    (𝒰 : U.Cover.{v} etalePrecoverage) :
    ∃ (i : 𝒰.I₀) (uᵢ : Spec (.of Ω) ⟶ 𝒰.X i),
      Etale (𝒰.f i ≫ f) ∧ uᵢ ≫ 𝒰.f i ≫ f = s ∧ uᵢ ≫ 𝒰.f i = u := by
  have : JointlySurjective etalePrecoverage := by
    refine ⟨fun R hR x => ?_⟩
    change R ∈ Scheme.precoverage @Etale _ at hR
    rcases hR with ⟨hJ, -⟩
    change R ∈ Scheme.jointlySurjectivePrecoverage _ at hJ
    rw [Scheme.jointlySurjectivePrecoverage,
      Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hJ
    exact hJ x
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (u default)
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨uᵢ, huᵢ, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) u y hy
  exact ⟨i, uᵢ, inferInstance, by rw [← Category.assoc, huᵢ, hu], huᵢ⟩

end AlgebraicGeometry.Scheme.Cover
