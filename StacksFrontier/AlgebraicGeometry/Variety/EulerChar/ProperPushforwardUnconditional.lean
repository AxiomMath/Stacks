module

public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.AdditivityUnconditional
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree

/-!
# The Euler characteristic of a coherent module and its higher direct images, unconditionally

Let `k` be a field, let `f : Y ⟶ X` be a morphism of schemes proper over `k` and let `G` be a
coherent `𝒪_Y`-module. Then `χ(Y, G) = ∑ᵢ (-1)ⁱ χ(X, Rⁱf_*G)`, with no hypothesis.

## Main results

* `AlgebraicGeometry.eulerCharacteristic_eq_finsum_higherDirectImage`: **[Stacks, Tag 0BEK]**,
  `χ(Y, G) = ∑ᵢ (-1)ⁱ χ(X, Rⁱf_*G)` for a morphism `f` of schemes proper over a field.

## Implementation notes

`AlgebraicGeometry.eulerCharacteristic_eq_finsum_higherDirectImage_of_hypotheses` proves the
identity from two hypotheses, and both are theorems of this repository. Coherence of the higher
direct images is [Stacks, Tag 02O5] in the form
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherent`. Finite dimensionality of
the cohomology of a coherent module on a scheme proper over a field is [Stacks, Tag 02O6] in the
form `AlgebraicGeometry.cohomologyFiniteDimensionalOverField_of_isProper`.

Coherence of `Rⁱf_*G` is not merely a step of the proof: it is the instance the Euler
characteristic `χ(X, Rⁱf_*G)` needs in order to be written down at all. The conclusion
therefore names [Stacks, Tag 02O5] where the hypothesis form named `h02O5`. Since
`SheafOfModules.IsCoherent` is a `Prop`, the choice of that proof is immaterial to the identity
being asserted.

**Why this is a separate file.** The proof of the conditional form is carried out against the
locally small derived categories of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`,
while the two witnesses are proved against `CategoryTheory.HasDerivedCategory.standard`, which
their files raise to the front of instance search. Importing them into
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/ProperPushforward.lean` would re-elaborate the
Leray spectral sequence there at the other derived category; taking the finished statement
across a module boundary does not.

## References

* [Stacks Project, Tag 0BEK](https://stacks.math.columbia.edu/tag/0BEK)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

-- The statement below spells out `Rⁱf_*G`, so it is elaborated at the same derived category as
-- `AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherent` and
-- `AlgebraicGeometry.eulerCharacteristic_eq_finsum_higherDirectImage_of_hypotheses`, both of
-- which are stated with `CategoryTheory.HasDerivedCategory.standard` as a local instance.
attribute [local instance 10001] HasDerivedCategory.standard

/-- **[Stacks, Tag 0BEK].** Let `k` be a field, let `f : Y ⟶ X` be a morphism of schemes proper
over `k` and let `G` be a coherent `𝒪_Y`-module. Then `χ(Y, G) = ∑ᵢ (-1)ⁱ χ(X, Rⁱf_*G)`, the
sum being over the nonnegative degrees, with no hypothesis.

The coherence of `Rⁱf_*G` that the right-hand side needs in order to name `χ(X, Rⁱf_*G)` is
[Stacks, Tag 02O5], in the form
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherent`. -/
@[stacks 0BEK]
public theorem eulerCharacteristic_eq_finsum_higherDirectImage
    (k : Type u) [Field k] {Y X : Scheme.{u}}
    (f : Y ⟶ X) (g : X ⟶ Spec (.of k))
    [IsProper g] [IsProper (f ≫ g)]
    (G : Y.Modules) [G.IsCoherent] :
    eulerCharacteristic k (f ≫ g) G =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        @eulerCharacteristic k _ X g _
          (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj G)
          (ProperCoherenceWitness.higherDirectImageIsCoherent Y X f
            (LocallyOfFiniteType.isLocallyNoetherian g) (IsProper.of_comp f g) G
            inferInstance i) :=
  eulerCharacteristic_eq_finsum_higherDirectImage_of_hypotheses
    ProperCoherenceWitness.higherDirectImageIsCoherent
    cohomologyFiniteDimensionalOverField_of_isProper k f g G

end AlgebraicGeometry

end
