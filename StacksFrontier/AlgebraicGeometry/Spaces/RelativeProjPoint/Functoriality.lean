module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.AlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.HomPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Space

/-!
# The open subspace `U(ψ)` and the morphism `r_ψ` for the relative Proj of Situation 0849

Let `ψ : 𝒜₁ ⟶ 𝒜₂` be a map of quasi-coherent graded `𝒪_X`-algebras on an algebraic space `X`, with
relative Projs `P = Proj_X(𝒜₁)` and `Q = Proj_X(𝒜₂)` of Stacks 084B.  The map `ψ` read over the
scheme points of `X` is `AlgebraicGeometry.Space.RelativeProjSituation.homPoints`; it cuts out the
subfunctor `U(ψ) ⊆ Q` and the morphism `r_ψ : U(ψ) ⟶ P` of Stacks 085F.  This file shows that
`U(ψ)` is an open subspace of `Q` with no hypothesis, `Q` being an algebraic space by Stacks 084B,
and packages `U(ψ)`, its inclusion and `r_ψ` in the category of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.relativeMapSpace`: `U(ψ)` as an algebraic space.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeMapSpaceι`: its inclusion into `Q`.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeMapSpaceMor`: `r_ψ : U(ψ) ⟶ P`.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeMapPresentation`: the étale presentation
  `U(ψ) = U(ψ)_U / U(ψ)_R` over an étale presentation `X = U/R`, restricted from the presentation
  `Q = Q_U / Q_R` along which the twists of `Q` are descended.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.isOpenSubspace_homPoints_relativeMapSubfunctor`:
  `U(ψ)` is an open subspace of `Q`.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeMapSpaceMor_comp_π`: `r_ψ` lies over `X`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {𝒜₁ 𝒜₂ : SheafOfModules.GradedAlgebra.{u, m, u, u + 1} (structureRingSheaf B S hS X)}
  (h₁c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₁.piece i).val.obj U)
    (b : (𝒜₁.piece j).val.obj U), HEq ((𝒜₁.mul i j).app U a b) ((𝒜₁.mul j i).app U b a))
  (h₁n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₁.piece n))
  (h₁q : ∀ n : ℤ, (𝒜₁.piece n).IsQuasicoherentOnSite)
  (h₁k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₁.piece n).val.obj U) B.cutoff)
  (h₂c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₂.piece i).val.obj U)
    (b : (𝒜₂.piece j).val.obj U), HEq ((𝒜₂.mul i j).app U a b) ((𝒜₂.mul j i).app U b a))
  (h₂n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₂.piece n))
  (h₂q : ∀ n : ℤ, (𝒜₂.piece n).IsQuasicoherentOnSite)
  (h₂k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₂.piece n).val.obj U) B.cutoff)
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂)

local notation "𝔰₁" => RelativeProjSituation.mk B S hS X 𝒜₁ h₁c h₁n h₁q h₁k
local notation "𝔰₂" => RelativeProjSituation.mk B S hS X 𝒜₂ h₂c h₂n h₂q h₂k
local notation "𝔥" => homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ

/-- **`U(ψ)` is an open subspace of `Q = Proj_X(𝒜₂)`**, with no hypothesis: `Q` is an algebraic
space by Stacks 084B. -/
theorem isOpenSubspace_homPoints_relativeMapSubfunctor :
    IsOpenSubspace B S hS (𝔥).relativeMapSubfunctor :=
  (𝔥).isOpenSubspace_relativeMapSubfunctor (𝔰₂).isAlgebraicSpace_relativeProjFunctor

/-- **`U(ψ)` as an algebraic space.** -/
abbrev relativeMapSpace : AlgebraicSpaces B S hS :=
  ⟨(𝔥).relativeMapSubfunctor.toFunctor,
    (isOpenSubspace_homPoints_relativeMapSubfunctor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).1⟩

/-- `P = Proj_X(𝒜₁)` as an algebraic space. -/
abbrev projSpace₁ : AlgebraicSpaces B S hS :=
  ⟨(𝔰₁).relativeProjFunctor, (𝔰₁).isAlgebraicSpace_relativeProjFunctor⟩

/-- `Q = Proj_X(𝒜₂)` as an algebraic space. -/
abbrev projSpace₂ : AlgebraicSpaces B S hS :=
  ⟨(𝔰₂).relativeProjFunctor, (𝔰₂).isAlgebraicSpace_relativeProjFunctor⟩

/-- **The inclusion `U(ψ) ⟶ Q`**, a morphism of algebraic spaces. -/
abbrev relativeMapSpaceι :
    relativeMapSpace h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ ⟶ projSpace₂ h₂c h₂n h₂q h₂k :=
  ObjectProperty.homMk (𝔥).relativeMapSubfunctor.ι

/-- **The morphism `r_ψ : U(ψ) ⟶ P`**, a morphism of algebraic spaces. -/
abbrev relativeMapSpaceMor :
    relativeMapSpace h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ ⟶ projSpace₁ h₁c h₁n h₁q h₁k :=
  ObjectProperty.homMk (𝔥).relativeMapSpaceHom

/-- The inclusion `U(ψ) ⟶ Q` is an open immersion. -/
theorem isOpenImmersion_relativeMapSpaceι :
    IsOpenImmersion B S hS (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).hom :=
  (isOpenSubspace_homPoints_relativeMapSubfunctor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).2

/-- **`r_ψ` lies over `X`.** -/
theorem relativeMapSpaceMor_comp_π :
    (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).hom ≫ (𝔰₁).relativeProjπ =
      (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).hom ≫ (𝔰₂).relativeProjπ :=
  (𝔥).relativeMapSpaceHom_comp

/-- **The étale presentation of `U(ψ)` over an étale presentation `X = U/R` of the base**:
`U(ψ)_U = U(ψ) ×_X U`, `U(ψ)_R = U(ψ) ×_X R`, with the projections restricted from the comparison
morphisms `Q_R ⇉ Q_U` of Stacks 084B (3) presenting `Q = Q_U / Q_R`
(`AlgebraicGeometry.Space.RelativeProjPoints.presentation`, along which the twists `𝒪_Q(n)` are
descended). -/
def relativeMapPresentation (Px : Presentation B S hS X.1 X.2) :
    Presentation B S hS (relativeMapSpace h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).1
      (relativeMapSpace h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).2 :=
  (𝔥).presentationOfBase Px (relativeMapSpace h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).2

/-- The chart scheme of the presentation of `U(ψ)` is the chart `U(ψ) ×_X U`. -/
theorem relativeMapPresentation_U (Px : Presentation B S hS X.1 X.2) :
    (relativeMapPresentation h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px).U =
      (𝔥).chartObj Px.U Px.toSpace := rfl

/-- The chart morphism of the presentation of `U(ψ)` is the chart map `U(ψ) ×_X U ⟶ U(ψ)`. -/
theorem relativeMapPresentation_toSpace (Px : Presentation B S hS X.1 X.2) :
    (relativeMapPresentation h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px).toSpace =
      (𝔥).chartToSubfunctor Px.U Px.toSpace := rfl

end AlgebraicGeometry.Space.RelativeProjSituation

end
