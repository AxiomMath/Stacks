module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSupportedLift

/-!
# Stacks 0869: the strict transforms of a short exact sequence are short exact

Let `b : A' ⟶ A` be the blowup of an algebraic space `A` over a scheme `S` in a closed subspace
`Z ⊆ A`, let `f : X ⟶ A` be an algebraic space over `A`, and let
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a sequence of quasi-coherent `𝒪_X`-modules which stays short exact
after every base change `Y ⟶ A`.  Then the strict transforms `Fᵢ'` of the `Fᵢ` form a short
exact sequence `0 ⟶ F₁' ⟶ F₂' ⟶ F₃' ⟶ 0`.

## Main results

* `AlgebraicGeometry.Space.exists_strictTransformSheaf_shortComplex` is **Stacks 0869**: the
  strict transforms form a short complex whose two maps are determined by the quotient maps onto
  the strict transforms, the left-hand map is a monomorphism, the right-hand map is an
  epimorphism, and the complex is exact in the middle.

## The argument

The strict transform of a module is the quotient of its pullback to `X ×_A A'` by the subsheaf
of sections supported on the exceptional preimage `|pr_{A'}^{-1}E|`, so the three assertions are
three questions about that quotient.  Monomorphy on the left and epimorphy on the right are the
unconditional
`AlgebraicGeometry.Space.mono_supportedQuotientMapLeft` and
`AlgebraicGeometry.Space.epi_supportedQuotientMapRight` of
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformShortExact.lean`, and exactness in the
middle is equivalent there to epimorphy of the morphism induced on the subsheaves of supported
sections.  That epimorphy is
`AlgebraicGeometry.Space.epi_supportedSectionsMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformSupportedLift.lean`, which runs the
argument of the scheme-level Stacks 080W on the affine étale charts of `X ×_A A'`: over a chart
lying above an affine chart of `A'` on which the exceptional divisor has a local equation, a
supported section is annihilated by a power of that equation (Stacks 0859, part (2)), lifts
through the right-hand map because the sections of a short exact sequence of quasi-coherent
modules over an affine chart are exact and surjective, and the lift is corrected to a supported
one by the divisibility that the universal short exactness supplies after base change along the
corresponding multiple of the exceptional divisor.

The exceptional divisor of a blowup is an effective Cartier divisor,
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor`, and an effective Cartier
divisor has a local equation on an étale chart through every point by Stacks 083C, which is what
makes those charts cover.

Quasi-coherence of the three terms is the source's own hypothesis and is used in exactly two
places: to read the supported sections over an affine chart as ideal-power torsion, and to make
the sections functor of an affine chart right exact on the sequence.

## References

* [Stacks Project, Tag 0869](https://stacks.math.columbia.edu/tag/0869)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 080W](https://stacks.math.columbia.edu/tag/080W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A)

/-- **Stacks 0869.**  In the situation of Stacks 0862 — a blowup `b : A' ⟶ A` of an algebraic
space `A` in a closed subspace `Z`, with exceptional divisor `E = b^{-1}Z`, and an algebraic
space `f : X ⟶ A` over `A` — let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a sequence of quasi-coherent
`𝒪_X`-modules which is short exact after every base change `Y ⟶ A`.  Then the strict transforms
of the `Fᵢ` form a short complex whose two maps are determined by the quotient maps onto the
strict transforms, the left-hand map is a monomorphism, the right-hand map is an epimorphism,
and the complex is exact in the middle: the strict transforms form a short exact sequence.

The strict transform is the one of Stacks 0862,
`AlgebraicGeometry.Space.strictTransformSheaf`, and "being the blowup of `A` in `Z`" is
`AlgebraicGeometry.Space.IsBlowupAlong`, the universal property of Stacks 085U, since Stacks
085Q constructs no blowup of an algebraic space in this library. -/
@[stacks 0869 "the strict transforms of a short exact sequence of quasi-coherent modules which \
stays short exact after every base change again form a short exact sequence, with its two maps \
pinned down by the quotient maps onto the strict transforms"]
theorem exists_strictTransformSheaf_shortComplex_of_isBlowupAlong {Z : ClosedSubspaces B S hS A.1}
    {b : A' ⟶ A}
    (hb : IsBlowupAlong B S hS Z b) (C : ShortComplex (Modules.{u, u} B S hS X.1 X.2))
    (hqc₁ : C.X₁.IsQuasicoherentOnSite) (hqc₂ : C.X₂.IsQuasicoherentOnSite)
    (hqc₃ : C.X₃.IsQuasicoherentOnSite)
    (hC : ∀ (Y P : AlgebraicSpaces B S hS) (t : Y ⟶ A) (pX : P ⟶ X) (pY : P ⟶ Y),
      IsPullback pX pY f t → (C.map (modulePullback B S hS pX)).ShortExact) :
    ∃ (f' : strictTransformSheaf B S hS f b (Z.1.preimage b.hom) C.X₁ ⟶
          strictTransformSheaf B S hS f b (Z.1.preimage b.hom) C.X₂)
      (g' : strictTransformSheaf B S hS f b (Z.1.preimage b.hom) C.X₂ ⟶
          strictTransformSheaf B S hS f b (Z.1.preimage b.hom) C.X₃)
      (w : f' ≫ g' = 0),
      Mono f' ∧ Epi g' ∧
      (strictTransformSheafQuotient B S hS f b (Z.1.preimage b.hom) C.X₁ ≫ f' =
        (modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map C.f ≫
          strictTransformSheafQuotient B S hS f b (Z.1.preimage b.hom) C.X₂) ∧
      (strictTransformSheafQuotient B S hS f b (Z.1.preimage b.hom) C.X₂ ≫ g' =
        (modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map C.g ≫
          strictTransformSheafQuotient B S hS f b (Z.1.preimage b.hom) C.X₃) ∧
      (ShortComplex.mk f' g' w).Exact := by
  have hD : (strictTransformPullbackShortComplex B S hS f b C).ShortExact :=
    hC A' (strictTransformPullback B S hS f b) b _ _
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
  have hE : HasEffectiveCartierEtalePullbacks B S hS A' (preimageClosedSubspace b Z) :=
    hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS A' _
      (isEffectiveCartierDivisor_exceptionalDivisor hb)
  refine ⟨strictTransformSheafMapLeft B S hS f b (Z.1.preimage b.hom) C,
    strictTransformSheafMapRight B S hS f b (Z.1.preimage b.hom) C,
    strictTransformSheafMapLeft_comp_mapRight B S hS f b (Z.1.preimage b.hom) C,
    mono_supportedQuotientMapLeft _ _ hD, epi_supportedQuotientMapRight _ _ hD,
    strictTransformSheafQuotient_comp_mapLeft B S hS f b (Z.1.preimage b.hom) C,
    strictTransformSheafQuotient_comp_mapRight B S hS f b (Z.1.preimage b.hom) C, ?_⟩
  exact exact_supportedQuotientShortComplex_of_epi _ _ hD
    (epi_supportedSectionsMap B S hS f b (preimageClosedSubspace b Z) hE C hC
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ C.X₁ hqc₁)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ C.X₂ hqc₂)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ C.X₃ hqc₃))

end AlgebraicGeometry.Space

end
