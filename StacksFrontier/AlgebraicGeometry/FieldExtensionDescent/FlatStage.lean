module

public import StacksFrontier.RingTheory.Flat.FieldOverDomain
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# `Spec K ⟶ Spec Aᵢ` is flat for every finite-type stage of a field extension

In the limit presentation that the proofs of [Stacks Project, Tags 0BDC, 0BDD and 0BDE] build —
`K` the union of its finitely generated `k`-subalgebras `Aᵢ`, and `X_K = lim (X ×_{Spec k}
Spec Aᵢ)` — the base change `Spec K ⟶ Spec Aᵢ` is **flat**, because `Aᵢ` is a domain sitting
inside the field `K`.

That is the hypothesis `[Flat q]` of
`Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange`
(`StacksFrontier/AlgebraicGeometry/PullbackSections/Qcqs.lean`, [Stacks Project, Tag 02KH] part
(2) in degree zero).

## Main results

* `AlgebraicGeometry.FieldExtensionDescent.flat_specMap_subalgebra`: for a subalgebra `A` of a
  field `K` over a field `k`, the morphism `Spec K ⟶ Spec A` is flat.

## Implementation notes

The subalgebra is not assumed finitely generated: flatness needs only that `A` is a domain inside
`K`, which is `Module.Flat.of_subalgebra_of_field`.

## References

* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 09MT](https://stacks.math.columbia.edu/tag/09MT)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.FieldExtensionDescent

/-- For a subalgebra `A` of a field `K` over a field `k`, the morphism of spectra
`Spec K ⟶ Spec A` is flat: `A` is a domain inside the field `K`, so `K` is flat over `A`. -/
theorem flat_specMap_subalgebra {k : Type u} (K : Type u) [Field k] [Field K] [Algebra k K]
    (A : Subalgebra k K) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_subalgebra_of_field K A)

end AlgebraicGeometry.FieldExtensionDescent

end
