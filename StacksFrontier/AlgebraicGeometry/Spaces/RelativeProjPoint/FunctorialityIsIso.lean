module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctorialityEventual
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistGluedSurjective

/-!
# Maps of graded algebras bijective in high degree, on the canonical relative Proj

In Situation 0849 let `ψ : 𝒜₁ ⟶ 𝒜₂` be a map of quasi-coherent graded `𝒪_X`-algebras on an
algebraic space `X` such that `ψ_d : 𝒜₁,d ⟶ 𝒜₂,d` is an isomorphism for `d ≫ 0`. Write
`P = Proj_X(𝒜₁)` and `Q = Proj_X(𝒜₂)`. This file proves Stacks 085I for `ψ` itself:

1. `U(ψ) = Q`;
2. `r_ψ : Q ⟶ P` is an isomorphism of algebraic spaces;
3. the maps `θ : r_ψ^*𝒪_P(n) ⟶ 𝒪_Q(n)` of Stacks 085F are isomorphisms.

Every restriction `f^*ψ` of `ψ` to a scheme point `f : T ⟶ X` is an isomorphism in the same
degrees (`isIso_restrictHom_app`, in
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityClosedImmersion`), so the
per-point results of `StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctorialityEventual`
apply to the morphism `homPoints ψ` of relative Projs that `ψ` induces, and the glued `θ_n` is
read on the chart of a presentation of `X`, where it is the scheme-level `θ_n` of Stacks 07ZG, an
isomorphism by Stacks 07ZJ (3).

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.eventually_isIso_restrictHom_app`: every
  restriction of `ψ` to a scheme point of `X` is an isomorphism in all large degrees.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeMapSubfunctor_homPoints_eq_top_of_isIso`:
  Stacks 085I (1).
* `AlgebraicGeometry.Space.RelativeProjSituation.isIso_relativeMapSpaceHom_homPoints`:
  Stacks 085I (2).
* `AlgebraicGeometry.Space.RelativeProjSituation.isIso_twistMap_of_eventually_isIso`:
  Stacks 085I (3).

## References

* [Stacks Project, Tag 085I](https://stacks.math.columbia.edu/tag/085I)
* [Stacks Project, Tag 085F](https://stacks.math.columbia.edu/tag/085F)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Filter
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

universe u m

namespace AlgebraicGeometry.Space.RelativeProjSituation

attribute [local irreducible] CategoryTheory.yoneda

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

/-- Bijectivity of `ψ_d` for `d ≫ 0` makes every restriction of `ψ` an isomorphism in all large
degrees. -/
theorem eventually_isIso_restrictHom_app (hiso : ∀ᶠ d : ℕ in atTop, IsIso (ψ.app (d : ℤ)))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) :
    ∀ᶠ d : ℕ in atTop, IsIso ((restrictHom h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ T f).app (d : ℤ)) :=
  hiso.mono fun d hd => isIso_restrictHom_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ d hd T f

/-- **Stacks 085I (1): `U(ψ) = Q`.** If `ψ_d : 𝒜₁,d ⟶ 𝒜₂,d` is an isomorphism for `d ≫ 0`, the
open subspace `U(ψ)` of Stacks 085F is all of `Q = Proj_X(𝒜₂)`. -/
@[stacks 085I "(1): U(ψ) = Q, for ψ_d : A_d → B_d an isomorphism for d ≫ 0"]
theorem relativeMapSubfunctor_homPoints_eq_top_of_isIso
    (hiso : ∀ᶠ d : ℕ in atTop, IsIso (ψ.app (d : ℤ))) :
    (homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).relativeMapSubfunctor = ⊤ :=
  RelativeProjHomPoints.relativeMapSubfunctor_eq_top_of_eventually_isIso _ <|
    eventually_isIso_restrictHom_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ hiso

/-- **Stacks 085I (2): `r_ψ : Q ⟶ P` is an isomorphism.** If `ψ_d : 𝒜₁,d ⟶ 𝒜₂,d` is an
isomorphism for `d ≫ 0`, the morphism `r_ψ : U(ψ) ⟶ Proj_X(𝒜₁)` of Stacks 085F, whose source is
all of `Q = Proj_X(𝒜₂)` by `relativeMapSubfunctor_homPoints_eq_top_of_isIso`, is an isomorphism
of algebraic spaces. -/
@[stacks 085I "(2): r_ψ : Q → P is an isomorphism, for ψ_d an isomorphism for d ≫ 0"]
theorem isIso_relativeMapSpaceHom_homPoints
    (hiso : ∀ᶠ d : ℕ in atTop, IsIso (ψ.app (d : ℤ))) :
    IsIso (homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).relativeMapSpaceHom :=
  RelativeProjHomPoints.isIso_relativeMapSpaceHom _ <|
    eventually_isIso_restrictHom_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ hiso

/-- **Stacks 085I (3): the maps `θ : r_ψ^*𝒪_P(n) ⟶ 𝒪_Q(n)` are isomorphisms** when `ψ_d` is an
isomorphism for `d ≫ 0`. Here `θ_n` is the glued map of Stacks 085F (`twistMap`), built along a
presentation `Px` of `X`; it is read on the chart of `Px`, where it is the `θ_n` of Stacks 07ZG for
the restriction of `ψ`, an isomorphism by Stacks 07ZJ (3). -/
@[stacks 085I "(3): the maps θ : r_ψ^*O_P(n) → O_Q(n) are isomorphisms (θ the glued map of 085F,
twistMap), for ψ_d an isomorphism for d ≫ 0"]
theorem isIso_twistMap_of_eventually_isIso
    (hiso : ∀ᶠ d : ℕ in atTop, IsIso (ψ.app (d : ℤ)))
    (Px : Presentation B S hS X.1 X.2) (n : ℤ) :
    IsIso (twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n) := by
  have hχ := isDescendedChartHom_twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n
  unfold RelativeProjHomPoints.IsDescendedChartHom RelativeProjHomPoints.IsChartHom at hχ
  refine (@Presentation.IsAtlasMapComp.isIso_iff _ _ _ _ _ _ _ _ _ _ _ _ _ hχ
    (Iso.isIso_hom _)).2 ?_
  exact RelativeProjHomPoints.isIso_equivalence_map_chartTwistMap _ Px.U Px.toSpace n _ _ _ _ _ _
    (Stacks.AlgebraicGeometry.Tag07ZGTwist.isIso_relativeTwistMap_of_eventually_isIso _
      (eventually_isIso_restrictHom_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ hiso Px.U Px.toSpace)
      n)

end AlgebraicGeometry.Space.RelativeProjSituation

end
