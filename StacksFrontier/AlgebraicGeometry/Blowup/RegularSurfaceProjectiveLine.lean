module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalTwistComparison

/-!
# The blowup of a regular local surface in its closed point, inside `𝐏¹`

Let `(A, 𝔪, κ)` be a regular local ring of dimension two, let `f : X ⟶ S = Spec A` be the blowing
up of `A` in `𝔪`, and let `E` be its exceptional divisor. This file states Stacks tag 0AGQ: there
is one closed immersion `r : X ⟶ 𝐏¹_S` over `S` such that

1. `r|_E : E ⟶ 𝐏¹_κ` is an isomorphism,
2. `𝒪_X(E) = 𝒪_X(-1) = r^*𝒪_{𝐏¹}(-1)`, and
3. `𝒞_{E/X} = (r|_E)^*𝒪_{𝐏¹}(1)` and `𝒩_{E/X} = (r|_E)^*𝒪_{𝐏¹}(-1)`.

## Main results

* `Stacks.Blowup.exists_isClosedImmersion_blowUpSpec_maximalIdeal_exceptional_projectiveLine`:
  the closed immersion `r : X ⟶ 𝐏¹_S` over `S` with properties (1)–(3) above.

## Implementation notes

The closed immersion is `Stacks.Blowup.blowUpSpecToProjSpace` attached to a generating pair `x, y`
of `𝔪` (`Stacks.Blowup.exists_range_eq_maximalIdeal`), as in the source; all three parts hold for
every such pair, and are proved for it:

* the closed immersion over `S` is `Stacks.Blowup.isClosedImmersion_blowUpSpecToProjSpace` and
  `Stacks.Blowup.blowUpSpecToProjSpace_comp_projSpaceToSpec`;
* part (1) is `Stacks.Blowup.exists_iso_exceptional_projectiveLine`;
* part (2) is `Stacks.Blowup.nonempty_invertibleSheaf_comap_toSpec_iso_twistingSheaf_neg_one`
  (Tag 02OS) and `Stacks.Blowup.blowUpSpecToProjSpacePullbackTwistIso` (Tag 01N1);
* part (3) is `Stacks.Blowup.nonempty_conormalSheaf_iso_pullback_specialFibreTwist_one` and
  `Stacks.Blowup.nonempty_normalSheaf_iso_pullback_specialFibreTwist_neg_one`: Tag 0B3P describes
  the two sheaves as pullbacks along `E ⟶ X ⟶ 𝐏¹_S`
  (`Stacks.Blowup.nonempty_conormalSheaf_iso_pullback_twistingSheaf_one` and
  `Stacks.Blowup.nonempty_normalSheaf_iso_pullback_twistingSheaf_neg_one`), and the factorization
  of part (1) carries them to pullbacks along `E ≅ 𝐏¹_κ`
  (`Stacks.Blowup.restrictionPullbackTwistIso`).

`r|_E` is recorded as in the source: `E ⟶ 𝐏¹_κ` is an isomorphism `ρ` whose composite with the
inclusion of the special fibre `𝐏¹_κ ⟶ 𝐏¹_S` (the morphism `Proj` of the coefficient change
`A[T₀, T₁] ⟶ κ[T₀, T₁]`) is the restriction `E ⟶ X ⟶ 𝐏¹_S` of `r`; that inclusion is a
monomorphism, so `ρ` is `r|_E` with its target cut down to the special fibre. Accordingly, in
part (3), `(r|_E)^*𝒪_{𝐏¹}(±1)` is the pullback along `ρ` of the Serre twist `𝒪_{𝐏¹_κ}(±1)`.

The projective line over `S` is `Proj A[T₀, T₁]` and `𝐏¹_κ` is `Proj κ[T₀, T₁]`, with `κ = A ⧸ 𝔪`;
`𝒪_X(n)` is the Serre twist of `X = Proj (⨁ₙ 𝔪ⁿ)`; `E` is `Stacks.Blowup.exceptionalIdealData 𝔪`,
the inverse image of the closed point; `𝒪_X(E)` is `Stacks.Divisors.invertibleSheaf'`, `𝒞_{E/X}` is
`Stacks.Conormal.conormalSheaf` and `𝒩_{E/X}` is `Stacks.Divisors.normalSheaf` of the inclusion of
`E`. The equalities of invertible modules in (2) and (3) are isomorphisms, stated as `Nonempty` of
the isomorphism type.

## References

* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Blowup

/-- **The blowup of a regular local surface in its closed point embeds in `𝐏¹`.** Let `(A, 𝔪, κ)`
be a regular local ring of dimension `2`, let `f : X = Proj (⨁ₙ 𝔪ⁿ) ⟶ S = Spec A` be the blowing up
of `A` in `𝔪` and let `E ⊆ X` be its exceptional divisor. There is a closed immersion
`r : X ⟶ 𝐏¹_S = Proj A[T₀, T₁]` over `S` such that

1. `r|_E : E ⟶ 𝐏¹_κ = Proj κ[T₀, T₁]` is an isomorphism: there is an isomorphism `ρ : E ≅ 𝐏¹_κ`
   whose composite with the inclusion of the special fibre `𝐏¹_κ ⟶ 𝐏¹_S` is the restriction
   `E ⟶ X ⟶ 𝐏¹_S` of `r`;
2. `𝒪_X(E) ≅ 𝒪_X(-1)` and `r^*𝒪_{𝐏¹_S}(-1) ≅ 𝒪_X(-1)`;
3. `𝒞_{E/X} ≅ ρ^*𝒪_{𝐏¹_κ}(1)` and `𝒩_{E/X} ≅ ρ^*𝒪_{𝐏¹_κ}(-1)`, with `ρ = r|_E` of (1). -/
@[stacks 0AGQ "for the blowup X of Spec A in the maximal ideal of a regular local ring \
(A, m, kappa) of dimension 2, with exceptional divisor E: there is a closed immersion \
r : X -> P^1_S = Proj A[T_0, T_1] over S = Spec A, and an isomorphism rho : E -> P^1_kappa = \
Proj kappa[T_0, T_1] whose composite with the inclusion of the special fibre P^1_kappa -> P^1_S \
is r restricted to E, such that O_X(E) = O_X(-1) = r^* O_{P^1_S}(-1), C_{E/X} = \
rho^* O_{P^1_kappa}(1) and N_{E/X} = rho^* O_{P^1_kappa}(-1)"]
theorem exists_isClosedImmersion_blowUpSpec_maximalIdeal_exceptional_projectiveLine
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    ∃ r : blowUpSpec (maximalIdeal A) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) A),
      IsClosedImmersion r ∧
      r ≫ projSpaceToSpec A 2 = toSpec (maximalIdeal A) ∧
      ∃ ρ : (exceptionalIdealData (maximalIdeal A)).subscheme ≅
          Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (A ⧸ maximalIdeal A)),
        (exceptionalIdealData (maximalIdeal A)).subschemeι ≫ r =
          ρ.hom ≫ Proj.map
            (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2)
              (Ideal.Quotient.mk (maximalIdeal A)))
            (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
              (Ideal.Quotient.mk (maximalIdeal A))) ∧
        Nonempty (Stacks.Divisors.invertibleSheaf' (exceptionalIdealData (maximalIdeal A)) ≅
          twistingSheaf (reesGrading (maximalIdeal A)) (-1)) ∧
        Nonempty ((Scheme.Modules.pullback r).obj
            (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) A) (-1)) ≅
          twistingSheaf (reesGrading (maximalIdeal A)) (-1)) ∧
        Nonempty (Stacks.Conormal.conormalSheaf
            (exceptionalIdealData (maximalIdeal A)).subschemeι ≅
          (Scheme.Modules.pullback ρ.hom).obj
            (twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin 2) (A ⧸ maximalIdeal A)) 1)) ∧
        Nonempty (Stacks.Divisors.normalSheaf
            (exceptionalIdealData (maximalIdeal A)).subschemeι ≅
          (Scheme.Modules.pullback ρ.hom).obj
            (twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin 2) (A ⧸ maximalIdeal A)) (-1))) := by
  obtain ⟨x, hspan⟩ := exists_range_eq_maximalIdeal A hdim
  have hx : ∀ i, x i ∈ maximalIdeal A := fun i ↦ by
    rw [hspan]; exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨ρ, hcomp⟩ := exists_iso_exceptional_projectiveLine A hdim x hx hspan
  exact ⟨blowUpSpecToProjSpace _ x hx hspan, inferInstance,
    blowUpSpecToProjSpace_comp_projSpaceToSpec _ x hx hspan, ρ, hcomp,
    nonempty_invertibleSheaf_comap_toSpec_iso_twistingSheaf_neg_one _,
    ⟨blowUpSpecToProjSpacePullbackTwistIso _ x hx hspan (-1)⟩,
    nonempty_conormalSheaf_iso_pullback_specialFibreTwist_one _ x hx hspan ρ hcomp,
    nonempty_normalSheaf_iso_pullback_specialFibreTwist_neg_one _ x hx hspan ρ hcomp⟩

end Stacks.Blowup

end
