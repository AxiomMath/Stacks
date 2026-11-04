module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjOfPolynomialOneVariable
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace

/-!
# Projective `0`-space over a scheme is that scheme

Relative projective `n`-space `ℙⁿ_S` is defined as the base change of the integral model
`ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ]` along the structure morphism of `S`. At `n = 0` the integral model is
`Proj ℤ[T₀]`, the `Proj` of a polynomial ring in one variable, which is `Spec ℤ`; and `Spec ℤ` is
a terminal scheme, so the base change is `S` itself. This file records that:
**the structure morphism `ℙ⁰_S ⟶ S` is an isomorphism**, and `ℙ⁰_S ≅ S` is the isomorphism it
determines, an isomorphism over `S` by construction.

## Main definitions

* `AlgebraicGeometry.isTerminal_projectiveSpaceAtUniverse_zero`: the integral model `ℙ⁰_ℤ` is a
  terminal scheme.
* `AlgebraicGeometry.projectiveSpaceOver.zeroIsoBase`: **`ℙ⁰_S ≅ S`.**

## Main results

* `AlgebraicGeometry.projectiveSpaceOver.isIso_zero_over`: the structure morphism `ℙ⁰_S ⟶ S` is
  an isomorphism.
* `AlgebraicGeometry.projectiveSpaceOver.zeroIsoBase_hom`: the forward direction of `ℙ⁰_S ≅ S` is
  that structure morphism, which is what makes the isomorphism one over `S`.

## Implementation notes

**The input is the absolute statement, not an affine-local argument.**
`AlgebraicGeometry.ProjectiveSpace.oneVariableProjIsoSpec` identifies `Proj A[T]` with `Spec A` for
every coefficient ring `A`, and `ℙ⁰_S` is a base change of the single instance `A = ULift ℤ`, so
nothing has to be glued over an affine cover of `S`: the whole content at the level of schemes is
that a base change along an isomorphism is an isomorphism, which is
`CategoryTheory.Limits.pullback_fst_iso_of_right_iso`.

**`ℙ⁰_ℤ` is terminal rather than merely affine.** The integral model used by
`AlgebraicGeometry.projectiveSpaceOver` is `AlgebraicGeometry.projectiveSpaceAtUniverse`, whose
coefficients are `ULift ℤ`; Mathlib's `AlgebraicGeometry.specULiftZIsTerminal` says
`Spec (ULift ℤ)` is terminal, and terminality transports along an isomorphism. Terminality, not
affineness, is what makes `terminal.from ℙ⁰_ℤ` an isomorphism, which is the hypothesis the pullback
lemma needs.

**The isomorphism is stated as `asIso` of the structure morphism**, so that
`AlgebraicGeometry.projectiveSpaceOver.zeroIsoBase_hom` is `rfl` and a consumer that needs the
isomorphism to be one over `S` — every consumer does — can rewrite with it rather than carry a
separate compatibility datum.

## References

* [Stacks Project, Tag 01MI](https://stacks.math.columbia.edu/tag/01MI)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- **The integral model of projective `0`-space is a terminal scheme.** It is
`Proj (ULift ℤ)[T₀]`, the `Proj` of a polynomial ring in one variable, which is the spectrum of
the coefficient ring by `AlgebraicGeometry.ProjectiveSpace.oneVariableProjIsoSpec`; and
`Spec (ULift ℤ)` is terminal. -/
public noncomputable def isTerminal_projectiveSpaceAtUniverse_zero :
    IsTerminal (projectiveSpaceAtUniverse.{u} 0) :=
  specULiftZIsTerminal.{u}.ofIso
    (ProjectiveSpace.oneVariableProjIsoSpec (ULift.{u} ℤ)).symm

/-- The morphism from the integral model of projective `0`-space to the terminal scheme is an
isomorphism, both being terminal. -/
public instance isIso_terminalFrom_projectiveSpaceAtUniverse_zero :
    IsIso (terminal.from (projectiveSpaceAtUniverse.{u} 0)) :=
  isIso_of_isTerminal isTerminal_projectiveSpaceAtUniverse_zero terminalIsTerminal _

namespace projectiveSpaceOver

/-- **The structure morphism `ℙ⁰_S ⟶ S` is an isomorphism.** Projective `0`-space over `S` is the
base change of the integral model `ℙ⁰_ℤ` along the structure morphism of `S`, and `ℙ⁰_ℤ` is
terminal, so the morphism being base changed is an isomorphism. -/
public instance isIso_zero_over (S : Scheme.{u}) : IsIso (projectiveSpaceOver 0 S ↘ S) :=
  pullback_fst_iso_of_right_iso _ _

/-- **`ℙ⁰_S ≅ S`**: projective `0`-space over a scheme is that scheme, by its own structure
morphism. -/
public noncomputable def zeroIsoBase (S : Scheme.{u}) : projectiveSpaceOver 0 S ≅ S :=
  asIso (projectiveSpaceOver 0 S ↘ S)

/-- The isomorphism `ℙ⁰_S ≅ S` is the structure morphism, so it is an isomorphism over `S`. -/
@[simp] public theorem zeroIsoBase_hom (S : Scheme.{u}) :
    (zeroIsoBase S).hom = projectiveSpaceOver 0 S ↘ S :=
  rfl

/-- The inverse of `ℙ⁰_S ≅ S` is a section of the structure morphism. -/
@[simp] public theorem zeroIsoBase_inv_comp_over (S : Scheme.{u}) :
    (zeroIsoBase S).inv ≫ projectiveSpaceOver 0 S ↘ S = 𝟙 S := by
  rw [← zeroIsoBase_hom S, Iso.inv_hom_id]

end projectiveSpaceOver

end AlgebraicGeometry

end
