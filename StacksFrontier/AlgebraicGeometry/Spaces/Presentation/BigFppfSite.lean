module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Covering sieves and subcanonicity of a big fppf site

Two facts about a big fppf site `B` that the theory of algebraic spaces over a scheme rests
on. First, every covering sieve of `B` is refined by one of the chosen covering families of
`B`: the covering sieves are generated inductively from those families, and each of the three
inductive steps can be realized by a family again. Second, the topology of `B` is
subcanonical, so the representable presheaf of an object of `B` — and hence of an object of
any slice of `B` — is a sheaf.

## Main results

* `AlgebraicGeometry.Space.exists_covering_refining_sieve` refines a covering sieve by a
  covering family.
* `AlgebraicGeometry.BigFppfSite.subcanonical_topology` is subcanonicity of the topology of a big
  fppf site.

## Implementation notes

Subcanonicity is deduced from Mathlib's
`CategoryTheory.GrothendieckTopology.subcanonical_of_full_of_faithful`, applied to the fully
faithful inclusion of `B` into all schemes. The topology comparison that result needs is set
up on the precoverage obtained by comparing along the inclusion: the fppf precoverage of
schemes pulled back to `B` generates a topology above that of `B`, is continuous for the
inclusion because the inclusion preserves the relevant fibre products, and is subcanonical;
subcanonicity then descends to the smaller topology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Every covering sieve of a big fppf site is refined by one of its chosen covering
families. -/
theorem exists_covering_refining_sieve (B : BigFppfSite.{u}) {X : B.Schemes} {R : Sieve X}
    (hR : R ∈ B.topology X) :
    ∃ E : PreZeroHypercover X, B.IsCovering ⟨X, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [BigFppfSite.topology, Precoverage.mem_toGrothendieck_iff] at hR
  induction hR with
  | of X P hP =>
      obtain ⟨E, hEq, hE⟩ := hP
      refine ⟨E, hE, ?_⟩
      rw [hEq]
      exact Sieve.le_generate _
  | top X =>
      exact ⟨PreZeroHypercover.singleton (𝟙 X), B.coverings_isSite.1 (𝟙 X), fun _ _ _ ↦ trivial⟩
  | pullback X R hR Y f ih =>
      obtain ⟨E, hE, hle⟩ := ih
      obtain ⟨P, p₁, p₂, hpb, hP⟩ := B.coverings_isSite.2.2 ⟨X, E⟩ hE Y f
      let F : PreZeroHypercover Y := ⟨E.I₀, P, p₂⟩
      refine ⟨F, hP, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      intro i
      rw [Sieve.pullback_apply, ← (hpb i).w]
      exact R.downward_closed (hle _ _ ⟨i⟩) (p₁ i)
  | transitive X R Q hR hRQ ihR ihRQ =>
      obtain ⟨E, hE, hle⟩ := ihR
      choose G hG hGle using fun i : E.I₀ ↦ ihRQ (hle _ _ ⟨i⟩)
      refine ⟨E.bind G,
        B.coverings_isSite.2.1 ⟨X, E⟩ hE (fun i ↦ ⟨E.X i, G i⟩) hG (fun _ ↦ rfl), ?_⟩
      rw [Presieve.ofArrows_le_iff]
      rintro ⟨i, j⟩
      show Q ((G i).f j ≫ E.f i)
      exact hGle i _ _ ⟨j⟩

end AlgebraicGeometry.Space

end
