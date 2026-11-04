module

public import StacksCore.Topology.Sober.Indiscrete

/-!
# A space that is neither Kolmogorov nor quasi-sober (Stacks 0B34)

Let `X` be the indiscrete space with at least two points of Example 0B32 and let `Y` be an
infinite set with the cofinite topology (Example 0B33). Stacks 0B34 observes that the
disjoint union `X ⊕ Y` is neither Kolmogorov nor quasi-sober, so neither property is
inherited from a covering by open subspaces having it.

Both statements are proved here for an arbitrary such pair, the hypotheses on `X` and `Y`
being carried by the classes `IndiscreteTopology`, `Nontrivial` and `Infinite`; instantiating
`X := Bool` with the indiscrete topology and `Y := ℕ` recovers the example verbatim.

* Not Kolmogorov: `Sum.inl` is an embedding, so `T0Space (X ⊕ Y)` would make `X` Kolmogorov,
  contradicting Example 0B32 (`not_t0Space_of_indiscreteTopology`).
* Not quasi-sober: the range of `Sum.inr` is irreducible (being the continuous image of the
  irreducible space `Y`) and closed, but a generic point for it would have to be some
  `Sum.inr y₀`, whose closure is the closed singleton `{Sum.inr y₀}` — and the range of
  `Sum.inr` is infinite.
-/

@[expose] public section

/-- **Stacks 0B34.** The disjoint union of an indiscrete space with at least two points and
an infinite set with the cofinite topology is not Kolmogorov. -/
@[stacks 0B34]
theorem not_t0Space_sum_cofiniteTopology (X : Type*) [TopologicalSpace X]
    [IndiscreteTopology X] [Nontrivial X] (Y : Type*) [Infinite Y] :
    ¬ T0Space (X ⊕ CofiniteTopology Y) := fun _ =>
  not_t0Space_of_indiscreteTopology X
    (Topology.IsEmbedding.inl (X := X) (Y := CofiniteTopology Y)).t0Space

/-- **Stacks 0B34.** The disjoint union of an indiscrete space with at least two points and
an infinite set with the cofinite topology is not quasi-sober. -/
@[stacks 0B34]
theorem not_quasiSober_sum_cofiniteTopology (X : Type*) [TopologicalSpace X]
    [IndiscreteTopology X] [Nontrivial X] (Y : Type*) [Infinite Y] :
    ¬ QuasiSober (X ⊕ CofiniteTopology Y) := by
  intro _
  have : Infinite (CofiniteTopology Y) :=
    Infinite.of_injective CofiniteTopology.of CofiniteTopology.of.injective
  -- The range of `Sum.inr` is irreducible and closed; a generic point would
  -- force this infinite set to equal a closed singleton.
  have hC_irred :
      IsIrreducible (Set.range (Sum.inr : CofiniteTopology Y → X ⊕ _)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image Sum.inr
      continuous_inr.continuousOn
  obtain ⟨z, hz⟩ := QuasiSober.sober hC_irred isClosed_range_inr
  have hzeq : closure ({z} : Set (X ⊕ CofiniteTopology Y)) = Set.range Sum.inr := hz
  obtain ⟨y₀, rfl⟩ : z ∈ Set.range (Sum.inr : CofiniteTopology Y → X ⊕ _) :=
    hzeq ▸ subset_closure rfl
  have hcl : IsClosed ({Sum.inr y₀} : Set (X ⊕ CofiniteTopology Y)) := by
    simpa using Topology.IsClosedEmbedding.inr.isClosedMap {y₀} isClosed_singleton
  rw [hcl.closure_eq] at hzeq
  have hCinf : (Set.range (Sum.inr : CofiniteTopology Y → X ⊕ _)).Infinite :=
    Set.infinite_range_of_injective Sum.inr_injective
  rw [← hzeq] at hCinf
  exact hCinf (Set.finite_singleton _)
