module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.Homology.Tor.DerivedTensor

/-!
# The four inverse systems of Stacks 0GA5 are pro-isomorphic

Let `I = (f₁, …, f_r)` be an ideal of a Noetherian ring `A`, let `Kₙ ∈ D(A)` be the Koszul
complex on `f₁ⁿ, …, f_rⁿ` and let `M•` be a bounded complex of finite `A`-modules.  The remark
considers four inverse systems in `D(A)`:

1. `M•/IⁿM•`, the complex with terms `Mⁱ/IⁿMⁱ`;
2. `M ⊗ᴸ_A A/Iⁿ`;
3. `M ⊗ᴸ_A Kₙ`;
4. `M ⊗ᴸ_P P/Jⁿ`, for a Noetherian `P → A` and an ideal `J ⊆ P` with `I = JA`,

and asserts that all four are isomorphic as pro-objects.

This file proves that (2) and (3) are pro-isomorphic: over a Noetherian ring the Koszul-power
system is pro-isomorphic to the system of quotients `A/Iⁿ` ([Stacks, Tag 0921]), and a
pro-isomorphism stays one after applying the functor `M ⊗ᴸ_A -`.  The comparison between (1)
and (2) is [Stacks, Tag 0G9M].

## Main results

* `Stacks.LocalCohomology.UniformityII.derivedTensorKoszulSystem_hasEventualInverses`:
  **systems (2) and (3) are pro-isomorphic** — the system `M ⊗ᴸ Kₙ` and the system
  `M ⊗ᴸ A/Iⁿ` are pro-isomorphic, by the comparison `M ⊗ᴸ (Kₙ → A/Iⁿ)`.
* `Stacks.LocalCohomology.UniformityII.derivedTensorKoszulSystem_hasEventualInverses_canonical`:
  the same for the canonical derived tensor product of [Stacks, Tag 0BYI].

## Implementation notes

"Pro-isomorphic" is `NoetherianAdicCompletion.HasEventualInverses`: for every level `n` some
later level `m ≥ n` carries a map backwards whose two composites with the comparison are the
transition maps of the two systems.

The derived tensor product is an argument, a `CochainComplex.DerivedTensor.DerivedTensorProduct`,
so the statement holds for any derived tensor product, in particular for the canonical one.  No
hypothesis on `M` is needed for this comparison: the finiteness and boundedness of `M•` enter
only in the comparison of (1) with (2), where they are the hypotheses of Stacks 0G9M.

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
* [Stacks Project, Tag 0921](https://stacks.math.columbia.edu/tag/0921)
* [Stacks Project, Tag 0G9M](https://stacks.math.columbia.edu/tag/0G9M)
-/

@[expose] public section

open CategoryTheory Opposite

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomology.UniformityII

universe u

variable {A : Type u} [CommRing A]

/-- **Systems (2) and (3) are pro-isomorphic.**  For an ideal `I = (f₀, …, f_{r-1})` of a
Noetherian ring `A`, the inverse system `n ↦ M ⊗ᴸ K_{n+1}` of derived tensor products with the
Koszul complexes on the positive powers of the generators is pro-isomorphic to the inverse
system `n ↦ M ⊗ᴸ A/Iⁿ⁺¹`, via the derived tensor product with `M` of the comparison
`Kₙ → A/Iⁿ` of [Stacks, Tag 0921]. -/
@[stacks 0GA5 "the pro-isomorphism between the systems (2) and (3), via Lemma 15.96.1"]
public theorem derivedTensorKoszulSystem_hasEventualInverses
    [IsNoetherianRing A] {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hI : I = Ideal.span (Set.range f))
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    NoetherianAdicCompletion.HasEventualInverses
      (Functor.whiskerRight (NoetherianAdicCompletion.koszulIdealPowerComparison f I hI)
        (T.tensor.obj (DerivedCategory.Q.obj M))) :=
  (NoetherianAdicCompletion.koszulIdealPowerComparison_hasEventualInverses f I hI).whiskerRight _

/-- `derivedTensorKoszulSystem_hasEventualInverses` for the canonical derived tensor product
of [Stacks, Tag 0BYI]. -/
@[stacks 0GA5 "the pro-isomorphism between the systems (2) and (3), for the canonical derived \
tensor product"]
public theorem derivedTensorKoszulSystem_hasEventualInverses_canonical
    [IsNoetherianRing A] {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hI : I = Ideal.span (Set.range f))
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    NoetherianAdicCompletion.HasEventualInverses
      (Functor.whiskerRight (NoetherianAdicCompletion.koszulIdealPowerComparison f I hI)
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
          (DerivedCategory.Q.obj M))) :=
  derivedTensorKoszulSystem_hasEventualInverses f I hI _ M

end Stacks.LocalCohomology.UniformityII

end
