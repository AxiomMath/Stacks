module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictCounit

/-!
# `Rj_*` detects zero objects for an open immersion

Let `j : X ⟶ Y` be an open immersion of schemes. If `K` is an object of `D(𝒪_X)` with `Rj_*K = 0`
then `K = 0`, with no hypothesis on the cohomology sheaves of `K` and at an arbitrary model of
the two derived categories. This is the first of the three equivalent conditions of
[Stacks, Tag 0BQT] for an open immersion, and it is the input
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/GeneratorClauses.lean` turns into the
remark's clause that the conditions hold for an open immersion.

The proof is one line of the adjunction `j^* ⊣ Rj_*` of
`StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/DerivedRestrictAdjunction.lean`: its counit
is invertible, so `K ≅ j^*(Rj_*K)`, and an additive functor carries a zero object to a zero
object.

## Main results

* `Stacks.Duality.DerivedPushforward.isZero_of_isZero_derivedPushforward_of_isOpenImmersion` —
  **condition (1) of [Stacks, Tag 0BQT] for an open immersion.**

## Implementation notes

*No `@[stacks]` attribute is placed here.* The clause of [Stacks, Tag 0BQT] this serves is
registered on the declaration stating it in full, in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/GeneratorClauses.lean`; this is a
component of its proof.

## References

* [Stacks Project, Tag 0BQT](https://stacks.math.columbia.edu/tag/0BQT)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w u

namespace Stacks.Duality.DerivedPushforward

/-- **Condition (1) of [Stacks, Tag 0BQT] for an open immersion.** Let `j : X ⟶ Y` be an open
immersion of schemes and let `K` be an object of `D(𝒪_X)`. If `Rj_*K` is a zero object then so is
`K`.

Restriction along an open immersion is left adjoint to direct image and the counit of the derived
adjunction `j^* ⊣ Rj_*` is invertible
(`Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_counit_app`), so `K` is
isomorphic to `j^*(Rj_*K)`; `j^*` is additive, so it carries the zero object `Rj_*K` to a zero
object. No quasi-coherence of the cohomology sheaves of `K` is needed. -/
theorem isZero_of_isZero_derivedPushforward_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
    (K : DerivedCategory X.Modules)
    (h : IsZero ((Stacks.Duality.derivedPushforward j).obj K)) : IsZero K :=
  (Functor.map_isZero (Stacks.Duality.OpenImmersion.derivedRestrict j) h).of_iso
    (asIso
      ((Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction j).counit.app K)).symm

end Stacks.Duality.DerivedPushforward

end
