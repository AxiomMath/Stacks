module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusTagInjectivity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.CohomologicalDimension
public import StacksFrontier.Topology.Dimension.DimensionFunction

/-!
# Algebraizing formal sections under an `S₁`-or-small-dimension alternative

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `F` be a
coherent module on `U`. Stacks 0EIF asserts that the comparison map
`Stacks.Algebraization.comparisonMap A I 𝔞 F`, from the sections of `F` on arbitrarily small
open neighbourhoods of `U ∩ V(I)` to the compatible families of sections of `F / Iⁿ F` on all
of `U`, is an isomorphism provided

1. `A` is `I`-adically complete and has a dualizing complex,
2. whenever `x` is an associated point of `F` outside `V(I)` whose closure meets `V(I)` outside
   `V(𝔞)`, every `z ∈ closure {x} ∩ V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1`, and
3. either `F` restricted to `U ∖ V(I)` satisfies Serre's condition `(S₁)`, or the dimension of
   `V(𝔞)` is at most `2`, in the sense that the values of some dimension function on `Spec(A)`
   differ by at most `2` on `V(𝔞)`.

The comparison map is injective without further hypotheses, so it is an isomorphism exactly when
every compatible family of sections of `F / Iⁿ F` on `U` comes from a section of `F` on a single
open neighbourhood of `U ∩ V(I)`.

## Main definitions

* `Stacks.Algebraization.opensOffVanishing` — the open `U ∖ V(I)` of `U`.
* `Stacks.Algebraization.IsSerreOneOffVanishing` — condition (3)(a): the restriction of `F` to
  `U ∖ V(I)` satisfies Serre's condition `(S₁)`.
* `Stacks.Algebraization.VanishingLocusDimensionAtMostTwo` — condition (3)(b): some dimension
  function on `Spec(A)` varies by at most `2` on `V(𝔞)`.
* `Stacks.Algebraization.AssociatedPointsClosureDimensionBound` — condition (2).
* `Stacks.Algebraization.FormalSectionsHypotheses` — conditions (1), (2) and (3) together.

## Main results

* `Stacks.Algebraization.mem_opensOffVanishing` — a point of `U` lies in `U ∖ V(I)` exactly when
  its prime does not contain `I`.
* `Stacks.Algebraization.isIso_comparisonMap_iff_realized` — the comparison map is an
  isomorphism exactly when every compatible family of sections of `F / Iⁿ F` on `U` is the
  comparison of a single section of `F` on a single neighbourhood of `U ∩ V(I)`. No hypothesis
  beyond Noetherian and coherent is needed.

## Implementation notes

The attribute on `Stacks.Algebraization.isIso_comparisonMap_iff_realized` registers the
equivalence with the realization of every formal section, not Stacks 0EIF itself; the realization,
and with it the conclusion of 0EIF, is `Stacks.Algebraization.serreOneAlternativeComparison`.

Condition (3)(a) is `AlgebraicGeometry.SheafHasPropertySk` at `k = 1` for the restriction of `F`
to the open subscheme `U ∖ V(I)`. Condition (2) measures `dim(𝒪_{closure {x}, z})` by
`Stacks.Algebraization.closureLocalDimension`, the Krull dimension of the interval of primes
between `x` and `z`, compared with `cd(A, I) + 1` in `EInt` through
`Stacks.Algebraization.krullDimToEInt`; the hypothesis that `closure {x}` meets `V(I)` outside
`V(𝔞)` is the existence of a prime containing `x` and `I` but not `𝔞`. Condition (3)(b) is
written as the pairwise inequality `δ x ≤ δ z + 2` for `x, z ∈ V(𝔞)`, which needs no maximum to
exist.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-- The open `U ∖ V(I)` of `U = Spec(A) ∖ V(𝔞)`, as the preimage of `Spec(A) ∖ V(I)` under the
inclusion of `U`. -/
public def opensOffVanishing : (complementZeroLocus A a : Scheme).Opens :=
  (complementZeroLocus A a).ι ⁻¹ᵁ complementZeroLocus A I

/-- A point of `U = Spec(A) ∖ V(𝔞)` lies in `U ∖ V(I)` exactly when its prime does not
contain `I`. -/
@[simp]
public theorem mem_opensOffVanishing (x : (complementZeroLocus A a : Scheme)) :
    x ∈ opensOffVanishing A I a ↔ ¬ I ≤ x.1.asIdeal :=
  Iff.rfl

/-- Condition (3)(a): the restriction of `F` to `U ∖ V(I)` satisfies Serre's
condition `(S₁)`, where `U = Spec(A) ∖ V(𝔞)`. -/
public def IsSerreOneOffVanishing : Prop :=
  SheafHasPropertySk (opensOffVanishing A I a).toScheme
    ((Scheme.Modules.restrictFunctor (opensOffVanishing A I a).ι).obj F) 1

/-- Condition (3)(b): the dimension of `V(𝔞)` is at most `2`, in the sense that some dimension
function on `Spec(A)` takes values on `V(𝔞)` whose maximum and minimum differ by at most `2`. -/
public def VanishingLocusDimensionAtMostTwo : Prop :=
  ∃ δ : DimensionFunction (PrimeSpectrum A),
    ∀ x z : PrimeSpectrum A, a ≤ x.asIdeal → a ≤ z.asIdeal → δ x ≤ δ z + 2

/-- Condition (2): let `x` be an associated point of `F` whose prime does not
contain `I` and whose closure meets `V(I)` outside `V(𝔞)`; then every point `z` of
`closure {x} ∩ V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1`. -/
public def AssociatedPointsClosureDimensionBound [IsNoetherianRing A] : Prop :=
  ∀ x : (complementZeroLocus A a : Scheme),
    x ∈ Stacks.Divisors.associatedPoints F →
    ¬ I ≤ x.1.asIdeal →
    (∃ y : PrimeSpectrum A, x.1.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
    ∀ z : PrimeSpectrum A, x.1.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (closureLocalDimension A x.1 z)

/-- The hypotheses of the algebraization of formal sections: for ideals `I ⊆ 𝔞` of a Noetherian
ring `A` and a coherent module `F` on `U = Spec(A) ∖ V(𝔞)`, the ring is `I`-adically complete and
has a dualizing complex, the associated points of `F` satisfy the dimension bound of
condition (2), and one of the two alternatives of condition (3) holds. -/
public structure FormalSectionsHypotheses [IsNoetherianRing A] : Prop where
  /-- Condition (1), completeness: `A` is `I`-adically complete. -/
  adicComplete : IsAdicComplete I A
  /-- Condition (1), duality: `A` has a dualizing complex. -/
  dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K
  /-- Condition (2): the dimension bound at the associated points of `F`. -/
  associatedPointsDimension : AssociatedPointsClosureDimensionBound A I a F
  /-- Condition (3): either `F` is `(S₁)` off `V(I)`, or `V(𝔞)` has dimension at most `2`. -/
  serreOneOrSmallDimension :
    IsSerreOneOffVanishing A I a F ∨ VanishingLocusDimensionAtMostTwo A a

/-- The comparison map is an isomorphism exactly when every compatible family of sections of
`F / Iⁿ F` on `U` is the comparison of a section of `F` over a single open `V ⊆ U` containing
`U ∩ V(I)`. -/
@[stacks 0EIF "REDUCED, not proved: the conclusion holds exactly when every formal section is \
realized on one neighbourhood. Injectivity is proved outright here; the realization half is NOT \
proved and NOT assumed — it is the right-hand side of this equivalence. See the coverage note"]
public theorem isIso_comparisonMap_iff_realized [IsNoetherianRing A] [F.IsCoherent] :
    IsIso (comparisonMap A I a F) ↔
      ∀ s : ToType (limit (formalSections A I a F)),
        ∃ (V : OpensNearVanishing A I a) (t : ToType ((sectionsNearVanishing A I a F).obj V)),
          ConcreteCategory.hom (comparisonAt A I a F V) t = s := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun h ↦ (surjective_comparisonMap_iff A I a F).1 h.2, fun hreal => ⟨?_, ?_⟩⟩
  · exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1
      (mono_comparisonMap A I a F)
  · exact (surjective_comparisonMap_iff A I a F).2 hreal

end Stacks.Algebraization

end
