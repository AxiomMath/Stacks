module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalIsomorphism
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ProfiniteSpectrum
public import StacksFrontier.Topology.Profinite.Defs

/-!
# Profinite spectra along maps identifying local rings

A ring map identifying local rings induces isomorphisms on the local rings at every prime of
its target and at the contracted prime of its source. In particular every residue field
extension it induces is an isomorphism, hence algebraic, so profiniteness of the prime
spectrum goes up along such a map.

## Main results

* `AlgebraicGeometry.ProEtale.isProfiniteStacks_primeSpectrum_of_identifiesLocalRings'`: if the
  prime spectrum of `A` is profinite and `f : A → B` identifies local rings, then the prime
  spectrum of `B` is profinite.  The primed name marks the weaker hypotheses: an arbitrary
  ring homomorphism, and `A` and `B` in possibly different universes.

## Implementation notes

The local-ring condition is `Algebra.IdentifiesLocalRings` for the algebra structure induced by the
given ring homomorphism, and profiniteness is `IsProfiniteStacks`, the Stacks definition by a
limit of finite discrete spaces. The proof passes to the property form of profiniteness
(compact, Hausdorff, totally disconnected) and feeds the surjectivity of the residue field map
— a consequence of surjectivity of the map on local rings — into the algebraic-residue-field
criterion.

## References

* [Stacks Project, Tag 0978](https://stacks.math.columbia.edu/tag/0978)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

/-- A ring map identifying local rings preserves profiniteness of prime spectra.

This is the form for an arbitrary ring homomorphism between commutative rings in possibly
different universes.  The unprimed
`isProfiniteStacks_primeSpectrum_of_identifiesLocalRings` is the form for an `Algebra`
instance in a single universe. -/
@[stacks 0978 "identifies_local_rings"]
theorem isProfiniteStacks_primeSpectrum_of_identifiesLocalRings'
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hA : IsProfiniteStacks (PrimeSpectrum A))
    (hf : letI := f.toAlgebra; Algebra.IdentifiesLocalRings A B) :
    IsProfiniteStacks (PrimeSpectrum B) := by
  let := f.toAlgebra
  apply (isProfiniteStacks_iff_compact_t2_totallyDisconnected _).2
  apply primeSpectrum_isProfinite_of_isAlgebraic_residueField f
    ((isProfiniteStacks_iff_compact_t2_totallyDisconnected _).mp hA)
  intro q hq
  have hres : Function.Surjective (Ideal.ResidueField.map (q.comap f) q f rfl) := by
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨z, rfl⟩ := (hf q).2 y
    exact ⟨IsLocalRing.residue _ z, IsLocalRing.ResidueField.map_residue _ z⟩
  let := (Ideal.ResidueField.map (q.comap f) q f rfl).toAlgebra
  refine ⟨fun x => ?_⟩
  obtain ⟨y, rfl⟩ := hres x
  exact isAlgebraic_algebraMap y

end AlgebraicGeometry.ProEtale

end
