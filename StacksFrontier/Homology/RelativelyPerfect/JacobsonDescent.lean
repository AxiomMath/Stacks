module

public import StacksCore.RingTheory.Jacobson.Ideal
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.Perfect

/-!
# Perfectness descends along a quotient by an ideal in the Jacobson radical

Let `R` be a ring and `I` an ideal contained in the Jacobson radical of `R`. If `K` is a
pseudo-coherent object of `D(R)` whose base change `R/I ⊗^𝐋_R K` is perfect, then `K` is perfect.

`StacksDraft.DerivedInverseLimit.isPerfect_of_surjective_baseChange` is the same statement for an
arbitrary surjection detecting units; what is added here is the translation of that condition into
the Jacobson-radical hypothesis the source states, in both of the spellings the library uses for
the Jacobson radical.

## Main results

* `StacksDraft.Perfect.isPerfect_of_isPerfect_quotientBaseChange_of_jacobson`: the statement, with
  the hypothesis written `I ≤ Ring.jacobson R`.
* `StacksDraft.Perfect.isPerfect_of_isPerfect_quotientBaseChange_of_jacobson_bot`: the same with
  the hypothesis written `I ≤ (⊥ : Ideal R).jacobson`, which is the spelling the scheme-level
  statements of Stacks 0DJZ use.

## Implementation notes

The unit-detection hypothesis of
`StacksDraft.DerivedInverseLimit.isPerfect_of_surjective_baseChange` is discharged by
`Ideal.isUnit_of_isUnit_quotient_mk`, Stacks 0AME in this library. The two spellings of the
Jacobson radical are interchanged by `Ideal.jacobson_bot`.

## References

* [Stacks Project, Lemma 37.71.3 (0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
* [Stacks Project, Lemma 10.19.1 (0AME)](https://stacks.math.columbia.edu/tag/0AME)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.Perfect

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- **Perfectness descends along a quotient by an ideal in the Jacobson radical.** Let `I` be an
ideal of `R` contained in the Jacobson radical and let `K` be a pseudo-coherent object of `D(R)`.
If `R/I ⊗^𝐋_R K` is a perfect object of `D(R/I)`, then `K` is perfect. -/
public theorem isPerfect_of_isPerfect_quotientBaseChange_of_jacobson {R : Type u} [CommRing R]
    (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : PseudoCoherence.IsPseudoCoherent K)
    (hperf : StacksDraft.Perfect.IsPerfect
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
        (Ideal.Quotient.mk I : R →+* R ⧸ I)).functor.obj K)) :
    StacksDraft.Perfect.IsPerfect K :=
  StacksDraft.DerivedInverseLimit.isPerfect_of_surjective_baseChange.{u, v}
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (fun x hx => Ideal.isUnit_of_isUnit_quotient_mk I hI x hx) K hK hperf

/-- **Perfectness descends along a quotient by an ideal in the Jacobson radical**, with the
hypothesis in the spelling `I ≤ (⊥ : Ideal R).jacobson`. -/
public theorem isPerfect_of_isPerfect_quotientBaseChange_of_jacobson_bot {R : Type u} [CommRing R]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : PseudoCoherence.IsPseudoCoherent K)
    (hperf : StacksDraft.Perfect.IsPerfect
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
        (Ideal.Quotient.mk I : R →+* R ⧸ I)).functor.obj K)) :
    StacksDraft.Perfect.IsPerfect K :=
  isPerfect_of_isPerfect_quotientBaseChange_of_jacobson.{u, v} I
    (Ideal.jacobson_bot (R := R) ▸ hI) K hK hperf

end StacksDraft.Perfect

end
