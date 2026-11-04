module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.Constructible

/-!
# Constructible stratifications of an open subscheme

A finite partition of an open subscheme into constructible locally closed subschemes. This is the
data that constructibility of a sheaf quantifies over, both for the étale and for the pro-étale
topology, so it is stated once here, free of either site.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A finite partition of an open subscheme into constructible locally closed subschemes. -/
public structure Scheme.ConstructibleStratification (X : Scheme.{u}) (U : X.Opens) where
  /-- The number of strata. -/
  n : ℕ
  /-- The strata. -/
  piece : Fin n → Scheme.{u}
  /-- The immersion of each stratum into `X`. -/
  inclusion : ∀ i, piece i ⟶ X
  /-- Each stratum is locally closed in `X`. -/
  isImmersion : ∀ i, IsImmersion (inclusion i)
  /-- Each stratum lies inside `U`. -/
  contained : ∀ i, Set.range (inclusion i).base ⊆ (U : Set X)
  /-- Each stratum is constructible as a subset of `U`. -/
  constructible : ∀ i, Topology.IsConstructible
    (U.ι.base ⁻¹' Set.range (inclusion i).base)
  /-- Distinct strata are disjoint. -/
  pairwise_disjoint : ∀ i j, i ≠ j → Disjoint
    (Set.range (inclusion i).base) (Set.range (inclusion j).base)
  /-- The strata cover `U`. -/
  covers : (U : Set X) = ⋃ i, Set.range (inclusion i).base

end AlgebraicGeometry

end
