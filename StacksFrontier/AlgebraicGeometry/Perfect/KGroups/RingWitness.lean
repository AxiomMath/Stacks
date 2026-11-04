module

public import StacksFrontier.AlgebraicGeometry.Perfect.KGroups.Ring

/-!
# The multiplication of `K₀(D_{Z, perf}(𝒪_X))` at a concrete closed subscheme

`AlgebraicGeometry.exists_supportedPerfect_nonUnitalCommRing` — the Tag 0FDN multiplication —
has a scheme, a closed subscheme, a closed immersion between them and a derived-category model
among its binders. This file instantiates all of them by closed terms, at a closed subscheme
that is neither empty nor the whole scheme, and reaches the conclusion. That makes the tagged
statement non-vacuous as a machine-checked fact rather than as an argument.

## Main results

* `AlgebraicGeometry.exists_supportedPerfect_nonUnitalCommRing_specTwo`: the multiplication for
  `Z = Spec(ℤ/2)` inside `X = Spec ℤ`.
* `AlgebraicGeometry.exists_supportedPerfect_nonUnitalCommRing_specZ`: the multiplication for
  the identity closed immersion of `Spec ℤ`, where `D_{Z, perf}(𝒪_X) = D_perf(𝒪_X)` by
  Tag 0FEU and the ring is the one of Tag 0FDK.

Neither carries a `@[stacks]` attribute: each is a single instance of Tag 0FDN, not a clause of
it.

## Implementation notes

`Spec (ℤ/2) ⟶ Spec ℤ` is a closed immersion by `IsClosedImmersion.spec_of_surjective`; the
Mathlib instance `IsClosedImmersion.spec_of_quotient_mk` does not fire here because its key is
stated for an ideal of the `CommRingCat` object rather than of `ℤ`, so the instance is supplied
by name.

Why the group these multiplications live on is not the zero group by the Eilenberg swindle:
every object of `D_{Z, perf}(𝒪_X)` is *perfect*, and a countable direct sum of nonzero perfect
objects is not perfect, so the subcategory does not admit the countable coproducts the swindle
needs — unlike `D(𝒪_X)` itself. For the identity immersion the group is `K₀(X)` of Tag 0FDK,
whose unit is the class of `𝒪_X`.

## References

* [Stacks Project, Tag 0FDN](https://stacks.math.columbia.edu/tag/0FDN)
* [Stacks Project, Tag 0FEU](https://stacks.math.columbia.edu/tag/0FEU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry StrictlyPerfect

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- The ideal `(2)` of `ℤ`, read in `CommRingCat`. -/
abbrev intIdealTwo : Ideal (CommRingCat.of ℤ) := Ideal.span {(2 : CommRingCat.of ℤ)}

/-- The closed immersion `Spec(ℤ/2) ⟶ Spec ℤ`: a nonempty closed subscheme which is not the
whole scheme. -/
abbrev specTwo := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk intIdealTwo))

/-- The morphism `specTwo : Spec(ℤ/2) ⟶ Spec ℤ` is a closed immersion. -/
instance isClosedImmersion_specTwo : IsClosedImmersion specTwo :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- **Tag 0FDN's multiplication, at a nonempty proper closed subscheme.**
`AlgebraicGeometry.exists_supportedPerfect_nonUnitalCommRing` for `Z = Spec(ℤ/2)` inside
`X = Spec ℤ`, with every binder of that statement instantiated by a closed term. -/
theorem exists_supportedPerfect_nonUnitalCommRing_specTwo :
    ∃ r : NonUnitalCommRing (K0 (supportedPerfectDerivedCategory specTwo)),
      r.toAddCommGroup =
          (inferInstance : AddCommGroup (K0 (supportedPerfectDerivedCategory specTwo))) ∧
        ∀ K L : supportedPerfectDerivedCategory specTwo,
          r.mul (K0.cls K) (K0.cls L) = K0.cls (supportedPerfectTensorObj specTwo K L) :=
  exists_supportedPerfect_nonUnitalCommRing specTwo

/-- **Tag 0FDN's multiplication, at the identity closed immersion of `Spec ℤ`**, where
`D_{Z, perf}(𝒪_X)` is `D_perf(𝒪_X)` by Tag 0FEU. -/
theorem exists_supportedPerfect_nonUnitalCommRing_specZ :
    ∃ r : NonUnitalCommRing
        (K0 (supportedPerfectDerivedCategory (𝟙 (Spec (CommRingCat.of ℤ))))),
      r.toAddCommGroup = (inferInstance : AddCommGroup
          (K0 (supportedPerfectDerivedCategory (𝟙 (Spec (CommRingCat.of ℤ)))))) ∧
        ∀ K L : supportedPerfectDerivedCategory (𝟙 (Spec (CommRingCat.of ℤ))),
          r.mul (K0.cls K) (K0.cls L) =
            K0.cls (supportedPerfectTensorObj (𝟙 (Spec (CommRingCat.of ℤ))) K L) :=
  exists_supportedPerfect_nonUnitalCommRing _

end AlgebraicGeometry

end
