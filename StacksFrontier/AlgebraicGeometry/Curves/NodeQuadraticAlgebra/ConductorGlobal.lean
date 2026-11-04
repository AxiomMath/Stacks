module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.ConductorRegularLocus
public import StacksFrontier.RingTheory.Localization.SmulTopLeRange

/-!
# The conductor of a nodal curve contains the product of its nodes

Let `k` be a field, let `A` be a reduced Noetherian `k`-algebra and let
`A' = integralClosure A (FractionRing A)` be its normalization inside its total ring of
fractions. Suppose given a finite family of ideals `𝔪₁, …, 𝔪ᵤ` of `A` which accounts for all the
singularities of `A`, in the sense that at every maximal ideal `P`:

* if `P` is one of the `𝔪ᵢ`, then `A_P` is a nodal `k`-algebra; and
* otherwise `A_P` is a regular local ring.

Then the product of the `𝔪ᵢ` carries `A'` into `A`:

`(∏ᵢ 𝔪ᵢ) • A' ≤ A`.

This is the `hann` hypothesis of
`Stacks.CyclicComaximal.exists_sup_span_singleton_eq_top_of_isCoatom_sup`, the local-to-global
step that produces a single generator for `A'` over `A`, and it is the one hypothesis of that
step which is not a computation at a single node.

The proof is the decomposition the two hypotheses describe, run through
`Submodule.smul_top_le_range_algebraLinearMap_of_localization_maximal`, which reduces the
containment to one maximal ideal at a time. At a node `P = 𝔪ᵢ` the product is contained in the
factor `𝔪ᵢ`, so its extension to `A_P` lies in the maximal ideal, and
`Stacks.Curves.map_maximalIdeal_le_range_algebraMap_localization_integralClosure` says that the
maximal ideal already carries the localized normalization into `A_P`. At a maximal ideal that is
not one of the `𝔪ᵢ` the local ring is regular, hence integrally closed, so by
`Stacks.Curves.range_algebraMap_localization_integralClosure_eq_top_of_isRegularLocalRing` the
image of `A_P` is the whole localized normalization and the containment is vacuous.

## Main results

* `Stacks.Curves.prod_smul_top_le_range_algebraMap_integralClosure_of_isNodalAlgebra`: the
  product of the nodes lies in the conductor of `A` in its normalization.

## Implementation notes

Neither the comaximality of the `𝔪ᵢ` nor their maximality is assumed, and neither is any
hypothesis on the dimension of `A`. The node case uses only that a product of ideals is
contained in each of its factors, and the regular case uses only that a regular local ring is
integrally closed, which holds in every dimension. The consumer does assume comaximality, but
for its own reasons — the Chinese remainder step — and that is where the hypothesis belongs.

The family is given as a function `𝔪 : ι → Ideal A` together with a `Finset ι`, matching the
shape in which `Stacks.CyclicComaximal.exists_sup_span_singleton_eq_top_of_isCoatom_sup` takes
it, so that the two fit together with no reindexing.

Both hypotheses are quantified over the maximal ideals `P` of `A` rather than over the index
`i`, with `P.IsMaximal` an instance binder. This is what makes `Localization.AtPrime P`
elaborate without the caller having to produce a primality instance for each `𝔪 i`, and it is
the form in which the hypotheses are discharged: `A` is reduced of dimension one and its singular
locus is a finite set of nodes, which is a statement about points of `Spec A`.

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-- **The product of the nodes lies in the conductor.** Let `A` be a reduced Noetherian algebra
over a field `k` and `A'` its integral closure in its total ring of fractions. Let
`𝔪 : ι → Ideal A` be a family of ideals, indexed by a finite set `s`, such that every maximal
ideal of `A` which occurs in the family is a node and every maximal ideal which does not is
regular. Then the product `∏ i ∈ s, 𝔪 i` carries `A'` into the image of `A`. -/
public theorem prod_smul_top_le_range_algebraMap_integralClosure_of_isNodalAlgebra
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsReduced A] [IsNoetherianRing A]
    [Algebra k A] {ι : Type*} (𝔪 : ι → Ideal A) (s : Finset ι)
    (hnodal : ∀ (P : Ideal A) [P.IsMaximal], (∃ i ∈ s, 𝔪 i = P) →
      IsNodalAlgebra k (Localization.AtPrime P))
    (hreg : ∀ (P : Ideal A) [P.IsMaximal], (∀ i ∈ s, 𝔪 i ≠ P) →
      IsRegularLocalRing (Localization.AtPrime P)) :
    (∏ i ∈ s, 𝔪 i) • (⊤ : Submodule A ↥(integralClosure A (FractionRing A))) ≤
      LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) := by
  refine Submodule.smul_top_le_range_algebraLinearMap_of_localization_maximal fun P hP => ?_
  by_cases hnode : ∃ i ∈ s, 𝔪 i = P
  · obtain ⟨i, hi, hiP⟩ := hnode
    have hle : (∏ i ∈ s, 𝔪 i).map (algebraMap A (Localization.AtPrime P)) ≤
        maximalIdeal (Localization.AtPrime P) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono (hiP ▸ Ideal.prod_le_inf.trans (Finset.inf_le hi))
    rw [Ideal.smul_top_eq_map]
    exact fun t ht => map_maximalIdeal_le_range_algebraMap_localization_integralClosure
      k A P (hnodal P ⟨i, hi, hiP⟩) t (Ideal.map_mono hle ht)
  · rw [range_algebraMap_localization_integralClosure_eq_top_of_isRegularLocalRing A P
      (hreg P fun i hi hiP => hnode ⟨i, hi, hiP⟩)]
    exact le_top

end Stacks.Curves

end
