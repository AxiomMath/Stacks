module

public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.Smoothing.PopescuTheorem
public import StacksFrontier.RingTheory.Smoothing.ReductionToBaseField

/-!
# Ind-smoothness of the completed local ring at a prime

Let `R` be a Noetherian ring, let `p` be a prime of `R`, write `R_p` for the local ring of `R` at
`p` and `Λ` for the completion of `R_p` at its maximal ideal. If `R_p` is a G-ring, then `Λ` is a
filtered colimit of smooth `R`-algebras — not merely of smooth `R_p`-algebras.

## Main results

* `Stacks.Smoothing.indSmooth_adicCompletion_atPrime`: for a Noetherian ring `R` and a prime `p`
  such that the local ring `R_p` is a G-ring, the completion of `R_p` at its maximal ideal is a
  filtered colimit of smooth `R`-algebras.

## Implementation notes

The G-ring hypothesis on `R_p` makes `R_p → Λ` a regular ring map (Lemma `0AH2`,
`isRegularRingHom_algebraMap_adicCompletion`), and Popescu's theorem (Tag `07GC`,
`Stacks.Smoothing.indSmooth_of_isRegularRingMap`) turns a regular ring map of Noetherian rings
into an ind-smooth one. The work is therefore to pass from the regularity of `R_p → Λ` to that of
the composite `R → R_p → Λ`.

That passage does not need the fibres of `R → Λ` to be computed. Regularity of a ring map with
Noetherian target can be tested on the local homomorphisms at the maximal ideals of the target
and their contractions (Tag `07C0`, `isRegularRingHom_tfae_localizations`), and `Λ` is local, so
there is exactly one such test. Its contraction to `R` is `p`, because `R_p → Λ` is a local
homomorphism (`AdicCompletion.algebraMap_isLocalHom_of_fg`) and the maximal ideal of `R_p` lies
over `p` (`Localization.AtPrime.under_maximalIdeal`); and `Λ`, being local, is its own
localization at its maximal ideal (`IsLocalization.atUnits`). So the single homomorphism to be
tested is `R_p → Λ` itself, up to that isomorphism, and regularity transports across it by
`IsRegularRingHom.comp_ringEquiv`.

## References

* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
* [Stacks Project, Tag 07C0](https://stacks.math.columbia.edu/tag/07C0)
* [Stacks Project, Tag 0AH2](https://stacks.math.columbia.edu/tag/0AH2)
* [Stacks Project, Tag 07GH](https://stacks.math.columbia.edu/tag/07GH)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.Smoothing

/-- **Regularity of a map out of a local ring at a prime descends to the base.** Let `Λ` be a
Noetherian local ring which is an algebra over the local ring `R_p` of `R` at a prime `p`, in such
a way that `R_p → Λ` is a local homomorphism and the structure map `R → Λ` factors through it. If
`R_p → Λ` is regular, then so is `R → Λ`. -/
private theorem isRegularRingHom_algebraMap_of_atPrime
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    [Algebra R Λ] [Algebra (Localization.AtPrime p) Λ]
    [IsScalarTower R (Localization.AtPrime p) Λ]
    [IsLocalHom (algebraMap (Localization.AtPrime p) Λ)]
    (h : IsRegularRingHom (algebraMap (Localization.AtPrime p) Λ)) :
    IsRegularRingHom (algebraMap R Λ) := by
  refine ((isRegularRingHom_tfae_localizations (algebraMap R Λ)).out 3 1).mp ?_
  intro m _ m' hm' hmm'
  obtain rfl : m' = maximalIdeal Λ := eq_maximalIdeal hm'
  have hcontract : (maximalIdeal Λ).comap (algebraMap R Λ) = p := by
    rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime p) Λ, ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap (algebraMap (Localization.AtPrime p) Λ)]
    exact Localization.AtPrime.under_maximalIdeal
  obtain rfl : p = m := (hmm'.trans hcontract).symm
  let e : Λ ≃ₐ[Λ] Localization.AtPrime (maximalIdeal Λ) :=
    IsLocalization.atUnits Λ (maximalIdeal Λ).primeCompl
      (fun x hx => (IsUnit.mem_submonoid_iff x).mpr (notMem_maximalIdeal.mp hx))
  have hfactor : Localization.localRingHom p (maximalIdeal Λ) (algebraMap R Λ) hmm' =
      e.toRingEquiv.toRingHom.comp (algebraMap (Localization.AtPrime p) Λ) := by
    refine IsLocalization.ringHom_ext p.primeCompl (RingHom.ext fun x => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, Localization.localRingHom_to_map]
    change _ = e (algebraMap (Localization.AtPrime p) Λ (algebraMap R (Localization.AtPrime p) x))
    rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p) Λ]
    exact (e.commutes _).symm
  rw [hfactor]
  exact h.comp_ringEquiv e.toRingEquiv

/-- **The completion of a local ring at a prime is ind-smooth over the base.** Let `R` be a
Noetherian ring and `p` a prime of `R` whose local ring `R_p` is a G-ring. Then the completion of
`R_p` at its maximal ideal is a filtered colimit of smooth `R`-algebras. -/
public theorem indSmooth_adicCompletion_atPrime
    (R : Type u) [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (hG : IsGRing (Localization.AtPrime p)) :
    IndSmooth R (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p)) := by
  have : IsNoetherianRing (Localization.AtPrime p) := hG.1
  have : IsScalarTower R (Localization.AtPrime p)
      (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact indSmooth_of_isRegularRingMap R _
    (isRegularRingMap_of_regularRingHom R _
      (isRegularRingHom_algebraMap_of_atPrime p
        (isRegularRingHom_algebraMap_adicCompletion hG
          (maximalIdeal (Localization.AtPrime p)))))

end Stacks.Smoothing

end
