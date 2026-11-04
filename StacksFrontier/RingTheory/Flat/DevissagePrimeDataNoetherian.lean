module

public import StacksFrontier.AlgebraicGeometry.Flatness.FinitePresentationStalk05I7
public import StacksFrontier.RingTheory.Flat.DevissageDecompositionNoetherian

/-!
# Stacks 05I4 from prime data, over a Noetherian base

`Module.CompleteDevissage.PrimeData` records the nine of the twelve conditions that
`Module.NonemptyCompleteDevissageAt` adds to a `Module.CompleteDevissage` which the conclusions of
Stacks 05I4 actually consume; it is the form in which a dévissage with compatible stage primes is
transported and recursed over, by `Module.CompleteDevissage.PrimeData.localize`,
`Module.CompleteDevissage.PrimeData.ofStage` and `Module.CompleteDevissage.PrimeData.cons`.

`Module.CompleteDevissage.finitePresentation_of_flat` draws the finite-presentation conclusion of
Stacks 05I4 from that data, granted the hypothesis `hConstr`: constructibility of the
geometrically integral fibre locus of a flat finite type algebra over a Noetherian ring, which is
the one remaining argument of Stacks 05FT. **Over a Noetherian base that hypothesis is not
needed**, by `Module.CompleteDevissage.projective_lowerAlgebra_of_isNoetherianRing`; this file
records the three conclusions of Stacks 05I4 in prime-data form with no hypothesis beyond the
dévissage, the prime data, and flatness at `q`.

The decomposition and the freeness in prime-data form are new here: only finite presentation was
available in this shape, and only conditionally.

## Main results

* `Module.CompleteDevissage.injective_alpha_of_primeData_of_isNoetherianRing`: every map `alphaᵢ`
  is injective.
* `Module.CompleteDevissage.nonempty_linearEquiv_directSum_of_primeData_of_isNoetherianRing`: the
  decomposition.
* `Module.CompleteDevissage.finitePresentation_of_primeData_of_isNoetherianRing`: finite
  presentation over `S`.
* `Module.CompleteDevissage.free_of_primeData_of_isNoetherianRing`: freeness over `R`.

## Implementation notes

Nothing here carries a `@[stacks 05I4]` attribute: Stacks 05I4 assumes nothing about the base
beyond locality, so every statement below carries one hypothesis the tag does not.

No hypothesis relates `q` to the maximal ideal of `R`: it follows from the prime data, by
`Module.CompleteDevissage.PrimeData.under_eq`.

## References

* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
* [Stacks Project, Tag 05FS](https://stacks.math.columbia.edu/tag/05FS)
* [Stacks Project, Tag 05I3](https://stacks.math.columbia.edu/tag/05I3)
-/

@[expose] public section

open scoped DirectSum

universe u v w

namespace Module.CompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]

/-- **The injectivity hypothesis of Stacks 05I4, from prime data over a Noetherian local base.**
Every map `alpha i` of a complete dévissage over the maximal ideal carrying prime data over a
prime `q` of `S` is injective as soon as `N_𝔮` is flat over `R`.

The projectivity input of `Module.CompleteDevissage.injective_alpha` and of the downward recursion
`Module.CompleteDevissage.flat_localizedModule_stage` is supplied by
`Module.CompleteDevissage.projective_lowerAlgebra_of_isNoetherianRing`, so no form of Stacks 05FT
beyond the proved Noetherian case is used. -/
public theorem injective_alpha_of_primeData_of_isNoetherianRing [IsNoetherianRing R]
    [IsLocalRing R] [Module R N] [IsScalarTower R S N]
    (D : CompleteDevissage R S N (IsLocalRing.maximalIdeal R))
    {q : Ideal S} [q.IsPrime] (pd : D.PrimeData q)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N))
    (i : Fin (D.stepCount + 1)) :
    letI : Module (D.B i) (D.M i) := Module.compHom (D.M i) (D.toLeft i).toRingHom
    Function.Injective (D.alpha i) :=
  D.injective_alpha rfl D.projective_lowerAlgebra_of_isNoetherianRing
    pd.lowerPrime pd.lowerPrime_isPrime pd.lowerPrime_under
    (fun j => D.flat_localizedModule_stage rfl
      D.projective_lowerAlgebra_of_isNoetherianRing q
      pd.lowerPrime pd.lowerPrime_isPrime pd.lowerPrime_under
      pd.upperPrime pd.upperPrime_isPrime pd.upperPrime_under pd.upperPrime_unique
      pd.initial_under pd.transition_under hflat j) i

/-- **Stacks Project, Tag 05I4, the decomposition, from prime data over a Noetherian local base.**
A finite module over a finite type algebra of a Noetherian local ring which is flat over the base
after localizing at a prime `q` and which carries a complete dévissage over the maximal ideal
together with prime data over `q` decomposes as an `R`-module into the finite free modules
`Bᵢ^(⊕ rᵢ)` of that dévissage. -/
public theorem nonempty_linearEquiv_directSum_of_primeData_of_isNoetherianRing [IsNoetherianRing R]
    [IsLocalRing R] [Module R N] [IsScalarTower R S N]
    (D : CompleteDevissage R S N (IsLocalRing.maximalIdeal R))
    {q : Ideal S} [q.IsPrime] (pd : D.PrimeData q)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Nonempty (N ≃ₗ[R] ⨁ i : Fin (D.stepCount + 1), (Fin (D.multiplicity i) →₀ D.B i)) :=
  D.nonempty_linearEquiv_directSum
    (D.injective_alpha_of_primeData_of_isNoetherianRing pd hflat)
    D.projective_lowerAlgebra_of_isNoetherianRing

/-- **Stacks Project, Tag 05I4, finite presentation, from prime data over a Noetherian local
base.** This is `Module.CompleteDevissage.finitePresentation_of_flat` with its hypothesis
`hConstr` removed. -/
public theorem finitePresentation_of_primeData_of_isNoetherianRing [IsNoetherianRing R]
    [IsLocalRing R] [Module R N] [IsScalarTower R S N] [Algebra.FinitePresentation R S]
    (D : CompleteDevissage R S N (IsLocalRing.maximalIdeal R))
    {q : Ideal S} [q.IsPrime] (pd : D.PrimeData q)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Module.FinitePresentation S N :=
  D.finitePresentation_of_injective_alpha
    (D.injective_alpha_of_primeData_of_isNoetherianRing pd hflat)

/-- **Stacks Project, Tag 05I4, freeness over the base, from prime data over a Noetherian local
base.** The lower algebras are projective over `R` by the Noetherian case of Stacks 05FT, hence
free over the local ring `R`, hence so is the direct sum the module decomposes into. -/
public theorem free_of_primeData_of_isNoetherianRing [IsNoetherianRing R]
    [IsLocalRing R] [Module R N] [IsScalarTower R S N]
    (D : CompleteDevissage R S N (IsLocalRing.maximalIdeal R))
    {q : Ideal S} [q.IsPrime] (pd : D.PrimeData q)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Module.Free R N := by
  obtain ⟨e⟩ := D.nonempty_linearEquiv_directSum_of_primeData_of_isNoetherianRing pd hflat
  let : ∀ i, Module.Projective R (D.B i) := D.projective_lowerAlgebra_of_isNoetherianRing
  let : ∀ i, Module.Free R (D.B i) := fun _ => Module.free_of_projective_of_isLocalRing
  exact Module.Free.of_equiv e.symm

end Module.CompleteDevissage

end
