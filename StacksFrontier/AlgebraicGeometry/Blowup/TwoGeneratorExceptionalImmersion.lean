module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorPullback
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk

/-!
# The exceptional line of the two-generator square is the closed subscheme cut out by `ℐ`

For elements `f₁, f₂` of a commutative ring `A` the two-generator almost blowup square of
`StacksFrontier/AlgebraicGeometry/TwoGeneratorSquare.lean` has modification
`b : X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁)) ⟶ X = Spec A`, centre `Z = Spec (A/(f₁,f₂))` cut out by
`ℐ = Stacks.AlmostBlowUp.centerIdealSheaf A f₁ f₂`, and exceptional line
`E = Proj ((A/(f₁,f₂))[T₀,T₁])` sitting inside `X'` by
`Stacks.AlmostBlowUp.exceptionalToModification`. This file proves the two facts about that
inclusion that the cohomological half of [Stacks, Tag 0EXD] needs:

* it is a closed immersion;
* its ideal sheaf is the inverse image `ℐ ∘ b` of the centre.

Both come from the square being cartesian,
`Stacks.AlmostBlowUp.twoGenerator_isPullback`: a closed immersion is stable under base change,
and the kernel of the first projection of a pullback along a closed immersion is the inverse
image of that immersion's kernel
(`AlgebraicGeometry.Scheme.IdealSheafData.ker_fst_of_isClosedImmersion`).

## Main definitions

* `Stacks.AlmostBlowUp.exceptionalIsoComapSubscheme`: the identification of `E` with the
  closed subscheme of `X'` cut out by `ℐ ∘ b`, over `X'`.

## Main results

* `Stacks.AlmostBlowUp.ker_centerToBase`: the ideal sheaf of the centre is `ℐ`.
* `Stacks.AlmostBlowUp.isClosedImmersion_exceptionalToModification`: **`E ⟶ X'` is a closed
  immersion**, as an instance.
* `Stacks.AlmostBlowUp.ker_exceptionalToModification`: **the ideal sheaf of `E ⊆ X'` is the
  inverse image of the centre**, `(E ⟶ X').ker = ℐ.comap b`.
* `Stacks.AlmostBlowUp.ker_app_exceptionalToModification`: the same read on an affine open — a
  section of `𝒪_{X'}` dies on `E` exactly when it lies in `ℐ.comap b`. This is the spelling
  consumed by
  `Stacks.Cohomology.ClosedImmersion.exists_isCoherent_pushforward_iso_isZero_of_smul_eq_zero`,
  whose hypothesis is annihilation by the sections killed by `E ⟶ X'`.

## Implementation notes

The centre is `Spec` of the quotient map `A ⟶ A/(f₁,f₂)`, so its ideal sheaf is read off by
`AlgebraicGeometry.Scheme.ker_SpecMap` together with `Ideal.mk_ker`; the result is literally the
definition of `Stacks.AlmostBlowUp.centerIdealSheaf`, which is why
`Stacks.AlmostBlowUp.ker_centerToBase` closes by `rfl` after those two rewrites.

No chart computation is needed for either fact, in contrast with
`Stacks.AlmostBlowUp.isLocallyPrincipal_comap_centerIdealSheaf` of
`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorConditions.lean`: the cartesian square
transports both statements from the centre, where they are statements about the ring map
`A ⟶ A/(f₁,f₂)`.

No `@[stacks]` attribute: the two facts are the shape of the exceptional fibre of the square of
[Stacks, Tag 0EVH], already registered at
`Stacks.AlmostBlowUp.twoGenerator_isPullback`, read through the ideal-sheaf dictionary.

## References

* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlmostBlowUp

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-! ### The centre -/

/-- The centre `Spec (A/(f₁,f₂)) ⟶ Spec A` of the two-generator square is a closed immersion,
being `Spec` of a quotient map. -/
public instance isClosedImmersion_centerToBase : IsClosedImmersion (centerToBase A f₁ f₂) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- **The ideal sheaf of the centre is `ℐ`.** The centre is `Spec` of the quotient map
`A ⟶ A/(f₁,f₂)`, whose kernel is `(f₁,f₂)`, and `Stacks.AlmostBlowUp.centerIdealSheaf` is by
definition the ideal sheaf attached to that ideal on `Spec A`. -/
public theorem ker_centerToBase :
    (centerToBase A f₁ f₂).ker = centerIdealSheaf A f₁ f₂ := by
  rw [centerToBase, Scheme.ker_SpecMap, CommRingCat.hom_ofHom, Ideal.mk_ker]
  rfl

/-! ### The exceptional line as a closed subscheme of the modification -/

/-- **The exceptional line is a closed subscheme of the modification.** `E ⟶ X'` is the base
change of the centre `Z ⟶ X` along the modification `b`, by
`Stacks.AlmostBlowUp.twoGenerator_isPullback`, and a closed immersion is stable under base
change. -/
public instance isClosedImmersion_exceptionalToModification :
    IsClosedImmersion (exceptionalToModification A f₁ f₂) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (twoGenerator_isPullback A f₁ f₂).flip (isClosedImmersion_centerToBase A f₁ f₂)

/-- **The exceptional line is the zero locus of `ℐ`.** The ideal sheaf of `E` inside `X'` is the
inverse image under the modification of the ideal sheaf of the centre.

The square is cartesian, so `E ⟶ X'` is the first projection of the pullback of the centre along
`b` up to an isomorphism of its source, and the kernel of such a projection is the inverse image
of the kernel of the closed immersion being based-changed. -/
public theorem ker_exceptionalToModification :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    (exceptionalToModification A f₁ f₂).ker =
      (centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  rw [← ker_centerToBase A f₁ f₂, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
    (centerToBase A f₁ f₂) (modificationToBase A f₁ f₂),
    ← (twoGenerator_isPullback A f₁ f₂).isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

/-- **A section of `𝒪_{X'}` over an affine open dies on the exceptional line exactly when it
lies in the inverse image of the centre.** This is
`Stacks.AlmostBlowUp.ker_exceptionalToModification` read through
`AlgebraicGeometry.Scheme.Hom.ker_apply`, which applies because a closed immersion is
quasi-compact.

It is the form in which
`Stacks.Cohomology.ClosedImmersion.exists_isCoherent_pushforward_iso_isZero_of_smul_eq_zero`
consumes the identification: that lemma asks that the module be annihilated by every section
killed by `E ⟶ X'`, and the graded pieces of the `ℐ`-adic filtration are annihilated by
`ℐ.comap b`. -/
public theorem ker_app_exceptionalToModification
    (U : (letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).affineOpens) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    RingHom.ker ((exceptionalToModification A f₁ f₂).app U).hom =
      ((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).ideal U := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  rw [← Scheme.Hom.ker_apply, ker_exceptionalToModification]

/-- **The exceptional line, identified with the closed subscheme of the modification cut out by
`ℐ`.** Two closed immersions with the same ideal sheaf differ by an isomorphism of their sources,
and `Stacks.AlmostBlowUp.ker_exceptionalToModification` says the two ideal sheaves agree. -/
public def exceptionalIsoComapSubscheme :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    AlgebraicGeometry.Proj (exceptionalGrading A f₁ f₂) ≅
      ((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).subscheme :=
  letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
  haveI := IsClosedImmersion.isIso_lift
    ((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).subschemeι
    (exceptionalToModification A f₁ f₂)
    ((Scheme.IdealSheafData.ker_subschemeι _).trans
      (ker_exceptionalToModification A f₁ f₂).symm)
  asIso (IsClosedImmersion.lift
    ((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).subschemeι
    (exceptionalToModification A f₁ f₂)
    ((Scheme.IdealSheafData.ker_subschemeι _).trans
      (ker_exceptionalToModification A f₁ f₂).symm).le)

/-- The identification of the exceptional line with the subscheme cut out by `ℐ` is an
identification **over the modification**. -/
public theorem exceptionalIsoComapSubscheme_hom_comp_subschemeι :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    (exceptionalIsoComapSubscheme A f₁ f₂).hom ≫
        ((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).subschemeι =
      exceptionalToModification A f₁ f₂ :=
  IsClosedImmersion.lift_fac _ _ _

end Stacks.AlmostBlowUp

end
