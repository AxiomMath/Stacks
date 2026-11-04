module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.Flatness.RaynaudGruson.Structure

/-!
# Flatness at the distinguished prime of the Raynaud--Gruson construction

For the finite type map `A → B` of the Raynaud--Gruson construction, the localization of `B` at
its distinguished prime `q_B` is flat over `A`.

The localization of `B` at `q_B` is the localization of `C` at `q_C`, and `A → C` is étale,
hence flat; composing with the flat localization map `C → C_{q_C}` gives the claim.

## Main results

* `Stacks.Examples.RaynaudGruson.aToB_localization_flat`: the composite of `A → B` with the
  localization of `B` at `q_B` is a flat ring map.

## Implementation notes

The map to the localization is the composite of the construction's `A → B` and the canonical
localization map `B → B_{q_B}`. Flatness of that ring map is flatness of `B_{q_B}` as an
`A`-module, with no auxiliary choice of algebra structure.

This is the flat-at-the-prime clause of Stacks 05G2. The two negative clauses — that no
principal neighbourhood of `q_B` is flat, or of finite presentation, over `A` — are proved in
`StacksFrontier.Examples.Flatness.RaynaudGruson.NoFlatNeighborhood`, which also assembles the whole
lemma as `Stacks.Examples.RaynaudGruson.exists_flat_at_prime_not_flat_on_neighborhood`.

## References

* [Stacks Project, Tag 05G2](https://stacks.math.columbia.edu/tag/05G2)
-/

@[expose] public section

noncomputable section

namespace Stacks.Examples.RaynaudGruson

universe u

/-- The localization of `B` at its distinguished prime is flat over `A`. -/
theorem aToB_localization_flat (k : Type u) [Field k] :
    ((algebraMap (ringB k) (bAtQB k)).comp (aToB k)).Flat := by
  obtain ⟨e, he⟩ := bAtQB_equiv_cAtQC k
  have h : e.toRingHom.comp ((algebraMap (ringB k) (bAtQB k)).comp (aToB k)) =
      (algebraMap (ringC k) (cAtQC k)).comp (aToC k) :=
    RingHom.ext fun x => he ((aToC k) x)
  exact (RingHom.Flat.comp_iff_of_bijective_left e.bijective).mp
    (h.symm ▸ RingHom.Flat.comp
      ((RingHom.Etale.iff_flat_and_formallyUnramified.mp (aToC_etale k)).1)
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (cAtQC k) (awayFromQC k))))

end Stacks.Examples.RaynaudGruson
