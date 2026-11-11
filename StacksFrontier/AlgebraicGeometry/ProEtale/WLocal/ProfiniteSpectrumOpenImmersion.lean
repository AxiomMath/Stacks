module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ProfiniteSpectrum

/-!
# Profiniteness of a spectrum goes up along local isomorphisms

Let `A → B` be a homomorphism of commutative rings whose source has profinite prime spectrum,
and suppose it is a local isomorphism in the sense of Tag 096E part (1): for every prime `𝔮` of
`B` some `g ∉ 𝔮` makes `Spec(B_g) → Spec(A)` an open immersion. Then `Spec(B)` is profinite.

## Main results

* `AlgebraicGeometry.ProEtale.primeSpectrum_isProfinite_of_forall_exists_isOpenImmersion`:
  a local isomorphism over a ring with profinite spectrum has profinite spectrum.

## Implementation notes

The open immersion is `IsOpenImmersion` of `Spec.map` on the canonical map `A → B_g`, so `A`
and `B` live in one universe, as `Spec.map` requires. As in `spec_profinite_tfae`, profiniteness
is stated in property form: compactness, Hausdorffness, and total disconnectedness. The proof
uses only that the open immersion is injective on points, which rules out a strict inclusion of
primes of `B` in a fibre (the argument of the source's case (1)).

For the same statement with Mathlib's `Algebra.IsLocalIso`, which asks that `B_g` be a
localization of `A` away from an element, see `primeSpectrum_isProfinite_of_isLocalIso`.

## References

* [Stacks Project, Tag 0978](https://stacks.math.columbia.edu/tag/0978)
* [Stacks Project, Tag 096E](https://stacks.math.columbia.edu/tag/096E)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u

/-- A local isomorphism over a ring with profinite prime spectrum has target with profinite
prime spectrum. The local isomorphism is in the sense of Tag 096E part (1): for every prime `𝔮`
of `B` there is `g ∉ 𝔮` such that `A → B_g` induces an open immersion
`Spec(B_g) → Spec(A)`.

Given primes `𝔮 ⊆ 𝔮'` of `B`, choose such a `g ∉ 𝔮'`. Both primes extend to primes of `B_g`,
whose images in `Spec(A)` are comparable primes of `A`, hence equal. The open immersion is
injective on points, so the two primes of `B_g` agree, and contracting back to `B` gives
`𝔮 = 𝔮'`. -/
@[stacks 0978 "local_isomorphism"]
theorem primeSpectrum_isProfinite_of_forall_exists_isOpenImmersion
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (hloc : ∀ q : Ideal B, q.IsPrime → ∃ g : B, g ∉ q ∧
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))))
    (hA : CompactSpace (PrimeSpectrum A) ∧ T2Space (PrimeSpectrum A) ∧
      TotallyDisconnectedSpace (PrimeSpectrum A)) :
    CompactSpace (PrimeSpectrum B) ∧ T2Space (PrimeSpectrum B) ∧
      TotallyDisconnectedSpace (PrimeSpectrum B) := by
  refine ((spec_profinite_tfae B).out 5 1).mp ?_
  intro q q' hq hq' hle
  obtain ⟨g, hg', hoi⟩ := hloc q' hq'
  have hg : g ∉ q := fun h => hg' (hle h)
  have hd : Disjoint (Submonoid.powers g : Set B) q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hg
  have hd' : Disjoint (Submonoid.powers g : Set B) q' :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hg'
  let L := Localization.Away g
  have hP := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) L q hq hd
  have hP' := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) L q' hq' hd'
  have hPq : (q.map (algebraMap B L)).comap (algebraMap B L) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) L hq hd
  have hPq' : (q'.map (algebraMap B L)).comap (algebraMap B L) = q' :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) L hq' hd'
  have hinc : ∀ p p' : Ideal A, p.IsPrime → p'.IsPrime → p ≤ p' → p = p' :=
    ((spec_profinite_tfae A).out 1 5).mp hA
  have hcomap : ∀ I : Ideal L,
      I.comap (algebraMap A L) = (I.comap (algebraMap B L)).comap (algebraMap A B) := by
    intro I
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  have hinj : Function.Injective (PrimeSpectrum.comap (algebraMap A L)) :=
    (Spec.map (CommRingCat.ofHom (algebraMap A L))).isOpenEmbedding.injective
  have hpt : (⟨_, hP⟩ : PrimeSpectrum L) = ⟨_, hP'⟩ := by
    refine hinj (PrimeSpectrum.ext ?_)
    change Ideal.comap _ _ = Ideal.comap _ _
    rw [hcomap, hcomap]
    dsimp only
    rw [hPq, hPq']
    exact hinc _ _ (Ideal.comap_isPrime _ q) (Ideal.comap_isPrime _ q') (Ideal.comap_mono hle)
  have hPP : q.map (algebraMap B L) = q'.map (algebraMap B L) :=
    congrArg PrimeSpectrum.asIdeal hpt
  rw [← hPq, ← hPq', hPP]

end AlgebraicGeometry.ProEtale
