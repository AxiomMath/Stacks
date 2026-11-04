module

public import StacksFrontier.RingTheory.Flat.FlatteningDevissageVocabulary

/-!
# Flatness at the primes of a base change above a prime and a closed point

Let `A` be a ring, `C` an `A`-algebra, `Q` a prime of `C` and `N` a `C`-module. For a local
`A`-algebra `R`, the base change `(C ⊗[A] R) ⊗[C] N` of `N` is tested for flatness over `R` at
every prime of `C ⊗[A] R` which contains the extension of the maximal ideal of `R` and contracts
to `Q` in `C`. This is the flatness condition of Stacks Tag 05ML for the local situation
`(C_Q, N_Q)`, read on `C` itself.

## Main definitions

* `Module.IsFlatAtPrimesAbove A C Q N R`: the condition above.

## Main results

* `Module.FlatAtPointSituation.conditionOn_iff_isFlatAtPrimesAbove`: the flatness condition of
  Stacks Tag 05ML for `(C_Q, N_Q)` is `Module.IsFlatAtPrimesAbove` for `(C, Q, N)`.

## References

* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u v w x

namespace Module

/-- The base change of the `C`-module `N` to the local `A`-algebra `R` is flat over `R` at every
prime of `C ⊗[A] R` which contains the extension of the maximal ideal of `R` and contracts to the
prime `Q` of `C`. For `C` local with maximal ideal `Q` this is the flatness condition of Stacks
Tag 05ML. -/
def IsFlatAtPrimesAbove (A : Type u) [CommRing A] (C : Type v) [CommRing C] [Algebra A C]
    (Q : Ideal C) (N : Type w) [AddCommGroup N] [Module C N] (R : Type x) [CommRing R]
    [IsLocalRing R] [Algebra A R] : Prop :=
  letI : Algebra R (C ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  ∀ (𝔮 : Ideal (C ⊗[A] R)) (_ : 𝔮.IsPrime),
    Ideal.map (algebraMap R (C ⊗[A] R)) (maximalIdeal R) ≤ 𝔮 →
    𝔮.comap (algebraMap C (C ⊗[A] R)) = Q →
      Module.Flat R (LocalizedModule 𝔮.primeCompl ((C ⊗[A] R) ⊗[C] N))

/-- The flatness condition of Stacks Tag 05ML for a localization `S.B = C_Q` of an `A`-algebra
`C` and a localization `S.M = N_Q` of a `C`-module `N` is `Module.IsFlatAtPrimesAbove` for
`(C, Q, N)`. -/
theorem FlatAtPointSituation.conditionOn_iff_isFlatAtPrimesAbove
    {S : FlatAtPointSituation.{u, v, w}} {C : Type x} [CommRing C] [Algebra S.A C]
    [Algebra C S.B] [IsScalarTower S.A C S.B] (Q : Ideal C) [Q.IsPrime]
    [IsLocalization Q.primeCompl S.B] {N : Type*} [AddCommGroup N] [Module C N]
    [Module C S.M] [IsScalarTower C S.B S.M] (g : N →ₗ[C] S.M)
    [IsLocalizedModule Q.primeCompl g] (R : Type*) [CommRing R] [IsLocalRing R]
    [Algebra S.A R] :
    S.ConditionOn R ↔ IsFlatAtPrimesAbove S.A C Q N R :=
  FlatAtPointSituation.conditionOn_iff_forall_prime_comap Q g R

end Module

end
