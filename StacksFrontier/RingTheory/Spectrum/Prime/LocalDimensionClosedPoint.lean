module

public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension

@[expose] public section

/-!
# Local dimension of an affine finite type scheme over a field at a closed point

Let `k` be a field, let `S` be a finite type `k`-algebra, let `X = Spec S`, and let `x ∈ X` be the
closed point of a maximal ideal `𝔪 ⊆ S`. This file proves Stacks 00OU: the dimension `dim_x X` of
the topological space `X` at `x` (Topology, Definition 0055 (4), the infimum of `dim U` over the
open neighbourhoods `U` of `x`) is the Krull dimension of `S_𝔪`.

As in the source this is a special case of Lemma 00OT
(`PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height`): `dim_x X` is the
infimum of the heights of the maximal ideals containing `𝔪`, and `𝔪` is the only one, of height
`dim S_𝔪`.

## Main results

* `PrimeSpectrum.localKrullDim_eq_ringKrullDim_localization_of_isMaximal`: Stacks 00OU on the
  prime spectrum `PrimeSpectrum S`.
* `AlgebraicGeometry.Scheme.topologicalLocalKrullDim_specClosedPoint`: the same statement on the
  underlying space of the scheme `Spec S`, at the point `specClosedPoint 𝔪`.

## References

* [StacksProject 00OU](https://stacks.math.columbia.edu/tag/00OU)
-/

namespace PrimeSpectrum

/-- **Stacks 00OU.** Let `k` be a field, let `S` be a finite type `k`-algebra, and let `𝔪 ⊆ S` be
a maximal ideal, with associated closed point `x` of `X = Spec S`. Then `dim_x X = dim S_𝔪`. -/
@[stacks 00OU "`X = Spec S` is `PrimeSpectrum S`, `x` is the point `⟨𝔪, _⟩`, `dim_x X` is the
topological local dimension `TopologicalSpace.localKrullDim` of Topology, Definition 0055 (4), and
`dim(S_𝔪)` is `ringKrullDim (Localization.AtPrime 𝔪)`. The same statement on the scheme `Spec S`
is `AlgebraicGeometry.Scheme.topologicalLocalKrullDim_specClosedPoint`."]
theorem localKrullDim_eq_ringKrullDim_localization_of_isMaximal (k : Type*) [Field k]
    {S : Type*} [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (𝔪 : Ideal S)
    [h𝔪 : 𝔪.IsMaximal] :
    TopologicalSpace.localKrullDim (PrimeSpectrum S) ⟨𝔪, h𝔪.isPrime⟩ =
      ringKrullDim (Localization.AtPrime 𝔪) := by
  have hset : {I : Ideal S | I.IsMaximal ∧ 𝔪 ≤ I} = {𝔪} :=
    Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨h𝔪, le_rfl⟩, fun _ h => (h𝔪.eq_of_le h.1.ne_top h.2).symm⟩
  rw [(localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k
    (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum S)).2, hset]
  simp only [Set.mem_singleton_iff, iInf_iInf_eq_left]
  exact (IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪 _).symm

end PrimeSpectrum

namespace AlgebraicGeometry.Scheme

/-- **Stacks 00OU, on the scheme `Spec S`.** For a finite type algebra `S` over a field `k` and a
maximal ideal `𝔪 ⊆ S`, the topological dimension of `Spec S` at the closed point of `𝔪` is the
Krull dimension of `S_𝔪`. This is
`PrimeSpectrum.localKrullDim_eq_ringKrullDim_localization_of_isMaximal`, the underlying space of
`Spec S` being `PrimeSpectrum S`. -/
theorem topologicalLocalKrullDim_specClosedPoint (k : Type*) [Field k]
    (S : Type*) [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (𝔪 : Ideal S)
    [𝔪.IsMaximal] :
    TopologicalSpace.localKrullDim (Spec (CommRingCat.of S)) (specClosedPoint 𝔪) =
      ringKrullDim (Localization.AtPrime 𝔪) :=
  PrimeSpectrum.localKrullDim_eq_ringKrullDim_localization_of_isMaximal k 𝔪

end AlgebraicGeometry.Scheme

end
