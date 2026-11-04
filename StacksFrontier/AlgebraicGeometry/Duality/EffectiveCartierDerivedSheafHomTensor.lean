module

public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierIdealDualTensor

/-!
# The normal-sheaf formula for derived sheaf Hom, after derived pushforward

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor, with closed immersion
`i : D ⟶ X`, ideal sheaf `ℐ_D`, associated invertible sheaf `𝒪_X(D) = ℐ_D^∨` and normal sheaf
`𝒩 = i^* 𝒪_X(D)`. [Stacks, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4) asserts that
the canonical map

`Li^*K ⊗^L_{𝒪_D} 𝒩[-1] ⟶ R ℰom(𝒪_D, K)`

of [Stacks, Tag 0B4C] is an isomorphism for every `K` in `D(𝒪_X)`, where `R ℰom(𝒪_D, -)` is the
right adjoint of derived pushforward of [Stacks, Tag 0A76]. The source proves this by applying
`Ri_*`, where the right-hand side becomes `R ℰom_{𝒪_X}(i_* 𝒪_D, K)` by [Stacks, Tag 0A77] and
then `K ⊗^L_{𝒪_X} (i_* 𝒩)[-1]` by the tensor-dual clause of [Stacks, Tag 08DQ], the complex
`(i_* 𝒪_D)[0]` being perfect.

**This file performs that computation**, for every `K` and with no hypothesis: it is
`Stacks.Divisors.pushforwardDerivedSheafHomExactSupportTensorIso`,

`Ri_* R ℰom(𝒪_D, K) ≅ K ⊗^L_{𝒪_X} (i_* 𝒩)[-1]`.

At `K = 𝒪_X` it is `Stacks.Divisors.pushforwardDerivedSheafHomExactSupportIso`, which is
[Stacks, Tag 0B4B] pushed forward to `X`; this is the same statement with the structure sheaf
replaced by an arbitrary complex, which is exactly the generalisation [Stacks, Tag 0AA4] makes
of [Stacks, Tag 0B4B].

## Main results

* `Stacks.Divisors.pushforwardDerivedSheafHomExactSupportTensorIso`: the computation above.

## Implementation notes

The two inputs are proved. `Stacks.Divisors.divisorQuotientDualTensorIso` is
`R ℰom_{𝒪_X}(i_* 𝒪_D, K) ≅ K ⊗^L_{𝒪_X} (i_* 𝒩)[-1]`, proved from perfectness of
`(i_* 𝒪_D)[0]`; the bifunctor model
`…ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportPushforwardNatIso` of
[Stacks, Tag 0A77] identifies `Ri_* R ℰom(𝒪_D, -)` with `R ℰom_{𝒪_X}(Ri_* 𝒪_D, -)`, and
`Stacks.Divisors.pushforwardStructureSheafIso` identifies `Ri_* 𝒪_D` with `(i_* 𝒪_D)[0]`,
pushforward along a closed immersion being exact. The composite is the computation.

**What this does not give.** The descent of the computation from `X` to `D` is not performed
here, and is not performed anywhere in the tree: derived pushforward along a closed immersion
*reflects* isomorphisms
(`…ClosedQuotientMorphismOfRingedSpaces.reflectsIsomorphisms_mapDerivedCategory_modulePushforward`)
but is not full, so an isomorphism between the two pushforwards does not by itself produce one
between the two objects of `D(𝒪_D)`, and the isomorphism recorded here is not identified with
`Ri_*` of the canonical map of [Stacks, Tag 0B4C]. At `K = 𝒪_X` that descent is carried out in
`StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHomIso`, by
`CategoryTheory.Functor.isoSingleOfFullyFaithful`: there both sides are concentrated in a single
degree, so full faithfulness of `i_*` on *modules* suffices. For a general `K` neither side is
concentrated in a single degree, and that route is unavailable.

## References

* [Stacks Project, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0B4C](https://stacks.math.columbia.edu/tag/0B4C)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- **[Stacks, Tag 0AA4], the computation the source's proof performs on `X`:**

`Ri_* R ℰom(𝒪_D, K) ≅ K ⊗^L_{𝒪_X} (i_* 𝒩)[-1]`,

for every `K` in `D(𝒪_X)`, where `𝒩 = i^* 𝒪_X(D)` is the normal sheaf of the effective Cartier
divisor `D ⊆ X` and `R ℰom(𝒪_D, -)` is the right adjoint of derived pushforward of
[Stacks, Tag 0A76].

The bifunctor model of [Stacks, Tag 0A77] identifies the left-hand side with
`R ℰom_{𝒪_X}(Ri_* 𝒪_D, K)`; `Stacks.Divisors.pushforwardStructureSheafIso` identifies `Ri_* 𝒪_D`
with `(i_* 𝒪_D)[0]`, derived pushforward along a closed immersion being pushforward, which is
exact; and `Stacks.Divisors.divisorQuotientDualTensorIso` is the tensor-dual clause of
[Stacks, Tag 08DQ] at the perfect complex `(i_* 𝒪_D)[0]`.

At `K = 𝒪_X` this is `Stacks.Divisors.pushforwardDerivedSheafHomExactSupportIso`, that is,
[Stacks, Tag 0B4B] pushed forward to `X`.

[Stacks, Tag 0AA4] (not registered here: this is not the whole statement of the tag): the
isomorphism after derived pushforward along the closed immersion of D: Ri_* R ℰom(𝒪_D, K) ≅ K ⊗ᴸ
(i_*𝒩)[-1] for every K in D(𝒪_X), which is the computation the source's proof performs on X
-/
def pushforwardDerivedSheafHomExactSupportTensorIso (K : DerivedCategory X.Modules) :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        ((closedQuotient D).derivedSheafHomExactSupport.obj K) ≅
      ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (Stacks.SheafOfModules.ringedSite X.sheaf)).obj K).obj
        ((DerivedCategory.singleFunctor X.Modules 1).obj (normalShortComplex D).X₃) :=
  (closedQuotient D).derivedSheafHomExactSupportPushforwardNatIso.app K ≪≫
    (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).mapIso
      (pushforwardStructureSheafIso D).op).app K).symm ≪≫
    divisorQuotientDualTensorIso D K

end Stacks.Divisors

end
