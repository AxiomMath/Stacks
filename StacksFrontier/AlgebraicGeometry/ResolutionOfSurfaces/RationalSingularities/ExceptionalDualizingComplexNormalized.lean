module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDuality
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ClosedPointNormalizedDualizing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalTwistedInverseImageSquare
import StacksCore.Tactic.StacksAttribute

/-!
# `i^!(f^!(ω_A^•))` is the dualizing complex of the exceptional curve over `κ`

In Situation [Stacks, Tag 0B4W] let `X` be the blowup of `Spec(A)` in the maximal ideal,
`i : E ⟶ X` its exceptional divisor, `f : X ⟶ Spec(A)` the blowup morphism, `j : Spec(κ) ⟶ Spec(A)`
the closed point and `g : E ⟶ Spec(κ)` the structure morphism of `E` over the centre. Let `ω_A` be
a dualizing module for `A` and `ω_A^• = ω_A[-2]` the normalized dualizing complex, which the
dimension pins because `A` is Cohen–Macaulay.

**This file proves `i^!(f^!(ω_A^•)) ≅ g^!(𝒪_{Spec κ})`**, the right-hand side being
`Stacks.Duality.dualizingComplexOverField` of `g`, the dualizing complex of `E` as a proper curve
over `κ`. This is the whole of the source's propagation of the normalization of
[Stacks, Remark 0B4R] from `Spec(A)` to `E`, and it is what the module documentation of
`…/RationalSingularities/BlowUpExceptionalDualizing.lean` describes as the composition
`i^!(f^!(ω_A[2])) = (g ∘ j)^!(ω_A[2]) = g^!(j^!(ω_A[2]))` across the square of
`exceptionalDivisorToCentre_comp`.

No shift appears anywhere, because the statement is read at the source's own normalization: the
source's `ω_A[2]` *is* `ω_A` in degree `-2 = -dim(A)`, and its `ω_E^• = ω_E[1]` is `ω_E` in degree
`-1`, which is the degree `Stacks.Duality.dualizingSheafOverField` reads off
`Stacks.Duality.dualizingComplexOverField`.

## Main definitions

* `AlgebraicGeometry.derivedTildeSingleUliftSelfIsoStructureSheaf` — `R-tilde` of `R` in degree
  zero is the structure sheaf of `Spec(R)` in degree zero, as an object of `D_QCoh`.

## Main results

* `AlgebraicGeometry.RationalSingularitySituation`
  `.nonempty_twistedInverseImage_exceptional_iso_dualizingComplexOverField` — the isomorphism
  above, with nothing assumed beyond a dualizing module for `A`.

## The three steps, and what is left

* `AlgebraicGeometry.BlowUpDualizing.twistedInverseImageExceptionalSquareIso` is
  [Stacks, Tag 0ATX] around the square: `i^!(f^!(-)) ≅ g^!(j^!(-))`.
* `AlgebraicGeometry.RationalSingularitySituation`
  `.nonempty_twistedInverseImage_residuePoint_iso_single` evaluates `j^!(ω_A[-2])` as
  `𝒪_{Spec κ}`: it is [Stacks, Tag 0A9F] at the twisted inverse image composed with the
  normalization convention of [Stacks, Tag 0A7M], carried across the two models of `D(Mod A)` by
  `Dualizing.AnyModel.derivedHomModelIso`.
* `g^!` of the structure sheaf in degree zero *is* `Stacks.Duality.dualizingComplexOverField g`,
  by definition.

What is **not** here is the passage from this complex-level statement to `ecan`, the module-level
isomorphism `exceptionalDualizingModule A ω_X ≅ dualizingSheafOverField g` that the proofs of
clauses (2) and (3) of [Stacks, Tag 0B64] run through. Two things separate them:

* the normalization `ω_X ≅ f^!(ω_A)` of
  `AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization` is stated with `ω_A` in
  degree *zero*, so relating it to `ω_A[-2]` costs the shift `⟦2⟧` — which `i^!` and `f^!` carry,
  being right adjoints of shift-compatible functors, and which turns `H^{-1}` on the right into
  `H^1` on the left, exactly the degree `exceptionalDualizingModule` is taken in;
* `exceptionalDualizingModule` is `H¹` of **derived sheaf Hom with exact support** at
  `CategoryTheory.HasDerivedCategory.standard`, not `H¹` of `i^!` at the locally small model. That
  identification is [Stacks, Tag 0A9X] read at the locally small model, and is proved; see the
  module documentation of `…/RationalSingularities/ClosedPointNormalizedDualizing.lean`.

Both are carried out, and `ecan` is `AlgebraicGeometry.BlowUpDualizing`
`.nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField` of
`…/Duality/ExceptionalDualizingSheafIdentification.lean`.

No `@[stacks]` attribute is attached: [Stacks, Tag 0ATX] is registered on
`Stacks.Duality.twistedInverseImageCompIso` and [Stacks, Tag 0A7M] on the normalization
convention; what is assembled here is the source's *proof* of a clause of [Stacks, Tag 0B64], not
a separate assertion, so no clause is stated in this file. Clause (2) is registered on
`…isZero_firstCohomology_dualizingTwist_of_isDualizingRingModule` of that same `Duality/` file.

## References

* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **`R-tilde` of `R` in degree zero is the structure sheaf of `Spec(R)` in degree zero.**
Derived sheafification carries a module in degree zero to its sheafification in degree zero, by
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` for the exact functor `~`, and the
sheafification of `R` itself is the structure sheaf. The universe lift on the left is the one the
normalization convention of [Stacks, Tag 0A7M] places the residue field in. -/
def derivedTildeSingleUliftSelfIsoStructureSheaf (R : CommRingCat.{u}) :
    (derivedTilde R).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.uliftFunctor.{0} R).obj (ModuleCat.of R R))) ≅
      Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec R) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((derivedTildeCompι R).app _ ≪≫
      ((tilde.functor R).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor (Spec R).Modules 0).mapIso
        ((tilde.functor R).mapIso (ULift.moduleEquiv (R := R) (M := R)).toModuleIso))

namespace RationalSingularitySituation

/-- **`i^!(f^!(ω_A^•)) ≅ g^!(𝒪_{Spec κ})`.** In Situation [Stacks, Tag 0B4W], for `ω_A` a
dualizing module for `A`, the exceptional inverse image along `i : E ⟶ X` of the relative
dualizing complex `f^!(ω_A[-2])` of the blowup is the dualizing complex of the exceptional curve
as a proper curve over the residue field.

The degree `-dim(A)` is where the normalized dualizing complex of `A` sits, which the dimension
pins because a two-dimensional normal Noetherian local ring is Cohen–Macaulay
(`AlgebraicGeometry.RationalSingularitySituation.isCohenMacaulayLocalRing`); the degree `n` in
which `ω_A` is a dualizing complex is the existential of `Stacks.Duality.IsDualizingRingModule`
and is not assumed known.

The proof is the square of [Stacks, Tag 0ATX]
(`AlgebraicGeometry.BlowUpDualizing.twistedInverseImageExceptionalSquareIso`) followed by the
evaluation of `j^!` at the normalized complex
(`…nonempty_twistedInverseImage_residuePoint_iso_single`); `g^!` of the structure sheaf in degree
zero is `Stacks.Duality.dualizingComplexOverField g` by definition. -/
theorem nonempty_twistedInverseImage_exceptional_iso_dualizingComplexOverField
    (S : RationalSingularitySituation.{u}) (ωA : ModuleCat.{u} S.A) (n : ℤ)
    (hn : @Dualizing.IsDualizingComplex S.A _ _ (HasDerivedCategory.standard (ModuleCat.{u} S.A))
      ((@DerivedCategory.singleFunctor (ModuleCat.{u} S.A) _ _
        (HasDerivedCategory.standard (ModuleCat.{u} S.A)) n).obj ωA)) :
    letI : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) :=
      (cohenMacaulayCurveSituationExceptionalDivisor S).proper
    letI := BlowUpDualizing.compactSpace_blowUpScheme S
    letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (BlowUpDualizing.exceptionalImmersion S.A)
    letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (blowUpToBase (BlowUpDualizing.centre S.A))
    Nonempty ((Stacks.Duality.twistedInverseImage (BlowUpDualizing.exceptionalImmersion S.A)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
        ((Stacks.Duality.twistedInverseImage (blowUpToBase (BlowUpDualizing.centre S.A))
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          ((derivedTilde (CommRingCat.of S.A)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A)
              (-(Dualizing.localRingDimension S.A : ℤ))).obj ωA))) ≅
      Stacks.Duality.dualizingComplexOverField
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))) := by
  let : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) :=
    (cohenMacaulayCurveSituationExceptionalDivisor S).proper
  let := BlowUpDualizing.compactSpace_blowUpScheme S
  obtain ⟨d⟩ := S.nonempty_twistedInverseImage_residuePoint_iso_single ωA n hn
  refine ⟨(BlowUpDualizing.twistedInverseImageExceptionalSquareIso S).app _ ≪≫ ?_⟩
  exact (Stacks.Duality.twistedInverseImage
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).mapIso
    (d ≪≫ derivedTildeSingleUliftSelfIsoStructureSheaf _)

end RationalSingularitySituation

end AlgebraicGeometry

end
