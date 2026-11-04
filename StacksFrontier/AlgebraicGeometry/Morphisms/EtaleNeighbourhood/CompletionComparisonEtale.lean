module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.CompletionIsomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ArtinApproximationMorphism
public import StacksFrontier.RingTheory.AdicCompletion.AdicCompletionMapUniqueness
public import StacksFrontier.RingTheory.Etale.LocalRingPropertyList

/-!
# The completion comparison of an elementary étale extension, at a prime of a general ring

Let `A → A'` be an étale ring map, let `𝔭'` be a prime of `A'` contracting to a prime `𝔭` of
`A`, and suppose the residue field extension `κ(𝔭) → κ(𝔭')` is bijective. Then the comparison
map of completed local rings `(A_𝔭)^∧ → (A'_{𝔭'})^∧` is bijective.

`StacksDraft.ArtinApproximation.bijective_localCompletionComparison` is this statement when `A`
is local and `𝔭` is its maximal ideal. The form below asks nothing of `A` beyond
Noetherianness.

## Main results

* `StacksDraft.ArtinApproximation.bijective_completionComparison`: the comparison map
  `(A_𝔭)^∧ → (A'_{𝔭'})^∧` of an étale `A → A'` with trivial residue field extension at `𝔭'` is
  bijective.

## Implementation notes

`StacksDraft.flat_formallyUnramified_essFiniteType_localRingHom_of_etale` makes the induced
homomorphism of local rings `A_𝔭 → A'_{𝔭'}` flat, formally unramified and essentially of finite
type, which on Noetherian local rings is `RingHom.IsEtaleLocalHom`; and
`RingHom.bijective_adicCompletionMap_of_isEtaleLocalHom` makes the induced map of `𝔪`-adic
completions of such a homomorphism bijective once the residue field extension is.

The comparison map is that induced map by `eq_adicCompletionMap_of_apply_algebraMap`: a ring
homomorphism out of an adic completion along a finitely generated ideal which agrees with the
base on the image of the base is the canonical one, and
`StacksDraft.ArtinApproximation.completionComparison_ofLocalization` is that agreement for the
comparison map. So the bijective map is the canonical comparison itself, not an abstract
equivalence of completions.

The residue field hypothesis is stated with `Ideal.ResidueField.map`. Mathlib's
`Ideal.ResidueField.map p p' f h` is by definition
`IsLocalRing.ResidueField.map (Localization.localRingHom p p' f h)`, the form
`RingHom.bijective_adicCompletionMap_of_isEtaleLocalHom` asks for.

## References

* [Stacks Project, Tag 07QZ](https://stacks.math.columbia.edu/tag/07QZ)
* [Stacks Project, Tag 039H](https://stacks.math.columbia.edu/tag/039H)
* [Stacks Project, Tag 0C4G](https://stacks.math.columbia.edu/tag/0C4G)
-/

@[expose] public section

open IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-- **The comparison map of completed local rings of an elementary étale extension is
bijective.** Let `A` be a Noetherian ring, let `A'` be an étale `A`-algebra, and let `𝔭'` be a
prime of `A'` contracting to a prime `𝔭` of `A` with bijective residue field extension
`κ(𝔭) → κ(𝔭')`. Then `completionComparison : (A_𝔭)^∧ → (A'_{𝔭'})^∧` is bijective.

This is `bijective_localCompletionComparison` with the base no longer assumed local: the
induced homomorphism of local rings `A_𝔭 → A'_{𝔭'}` is still étale as a local homomorphism, and
the comparison map is still the map it induces on completions. -/
theorem bijective_completionComparison {A A' : Type u} [CommRing A] [CommRing A']
    [IsNoetherianRing A] [Algebra A A'] [Algebra.Etale A A'] (p : Ideal A) [p.IsPrime]
    (p' : Ideal A') [p'.IsPrime] (hp : p = p'.comap (algebraMap A A'))
    (hres : Function.Bijective (Ideal.ResidueField.map p p' (algebraMap A A') hp)) :
    Function.Bijective (completionComparison p p' (algebraMap A A') hp) := by
  have hA'noeth : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing A A'
  have hpnoeth : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl (Localization.AtPrime p) inferInstance
  have hp'noeth : IsNoetherianRing (Localization.AtPrime p') :=
    IsLocalization.isNoetherianRing p'.primeCompl (Localization.AtPrime p') hA'noeth
  have hlocalhom : IsLocalHom (Localization.localRingHom p p' (algebraMap A A') hp) :=
    Localization.isLocalHom_localRingHom p p' (algebraMap A A') hp
  have hetale : RingHom.IsEtaleLocalHom
      (Localization.localRingHom p p' (algebraMap A A') hp) :=
    flat_formallyUnramified_essFiniteType_localRingHom_of_etale p p' hp.symm
  have heq : completionComparison p p' (algebraMap A A') hp
      = adicCompletionMap (Localization.localRingHom p p' (algebraMap A A') hp)
        (maximalIdeal (Localization.AtPrime p)) (maximalIdeal (Localization.AtPrime p'))
        (map_maximalIdeal_le (Localization.localRingHom p p' (algebraMap A A') hp)) :=
    eq_adicCompletionMap_of_apply_algebraMap _ _ _ _
      (maximalIdeal (Localization.AtPrime p)).fg_of_isNoetherianRing _
      (completionComparison_ofLocalization p p' (algebraMap A A') hp)
  rw [heq]
  exact RingHom.bijective_adicCompletionMap_of_isEtaleLocalHom _ hetale hres

end StacksDraft.ArtinApproximation

end
