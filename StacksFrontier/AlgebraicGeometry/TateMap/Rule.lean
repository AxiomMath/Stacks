module

public import StacksFrontier.AlgebraicGeometry.TateMap.Objects
public import StacksFrontier.AlgebraicGeometry.TateMap.DetNLSheaf
public import StacksFrontier.AlgebraicGeometry.TateMap.Glue
public import StacksFrontier.RingTheory.TateMap.Pullback

/-!
# Tate rules

A *Tate rule* assigns to every locally quasi-finite syntomic morphism `f : Y ⟶ X` with `X`
locally Noetherian an isomorphism `c_{Y/X} : det(NL_{Y/X}) ≅ ω_{Y/X}` of `𝒪_Y`-modules. It
satisfies the two properties of Stacks 0FKD if

1. `c_{Y/X}` carries `δ(NL_{Y/X})` to `τ_{Y/X}`, and
2. it is compatible with restriction to opens and with base change: for every morphism
   `b/a : Y'/X' → Y/X` of the category of Section 0FKB (`OpenBaseChangeSquare`) and every
   compatible quadruple of affine charts `U ⊆ X`, `V ⊆ Y`, `U' ⊆ X'`, `V' ⊆ Y'` on which the
   coordinate ring of `V'` is a principal localization of `Γ(U') ⊗_{Γ(U)} Γ(V)`, the value of
   `c_{Y'/X'}` on `(U', V')` is the base change of the value of `c_{Y/X}` on `(U, V)`, through the
   canonical base-change isomorphisms of `det(NL)` and of `ω` (`Stacks.TateMap.pullbackTate`).
   This is the affine-local form of `b^* c_{Y/X} = c_{Y'/X'}`.

## Main definitions

* `AlgebraicGeometry.TateMap.chartValue`: the value of an isomorphism
  `det(NL_{Y/X}) ≅ ω_{Y/X}` on an affine chart, as an isomorphism `det(NL_{B/A}) ≅ ω_{B/A}`.
* `AlgebraicGeometry.TateMap.TateRule`: a candidate rule, an isomorphism `det(NL_{Y/X}) ≅ ω_{Y/X}`
  for every locally quasi-finite syntomic `f : Y ⟶ X`.
* `AlgebraicGeometry.TateMap.IsTateRuleOnCharts`: the two properties, read on affine charts.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Discriminant
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.TateMap

section ChartValue

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] {f : Y ⟶ X} {hf : IsQuasiFiniteSyntomic f}

/-- The value of an isomorphism `c : det(NL_{Y/X}) ≅ ω_{Y/X}` on an affine chart `(U, V)` of
`f`: the isomorphism `det(NL_{B/A}) ≅ ω_{B/A}`, `A = Γ(X, U)`, `B = Γ(Y, V)`, induced by `c` on
sections over `V` through the chart identifications of `det(NL_{Y/X})` and of `ω_{Y/X}`. -/
def chartValue (c : detNL f hf ≅ omega f hf) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (F : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    Stacks.TateMap.detNL Γ(X, U.1) Γ(Y, V.1) ≃ₗ[Γ(Y, V.1)] dualizingModule F :=
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  haveI := algebra_syntomic_appLE hf.2 U V hVU
  letI := isLocallyNoetherian_source f hf
  letI := hf.1
  (detNLChartEquiv f hf U V hVU).symm ≪≫ₗ sectionsLinearEquiv_of_iso c V.1 ≪≫ₗ
    (omegaData f hf).localEquiv U V hVU F

end ChartValue

/-- A candidate rule: an isomorphism `det(NL_{Y/X}) ≅ ω_{Y/X}` for every locally quasi-finite
syntomic morphism `Y ⟶ X` with `X` locally Noetherian. -/
abbrev TateRule :=
  ∀ (X Y : Scheme.{u}) [IsLocallyNoetherian X] (f : Y ⟶ X) (hf : IsQuasiFiniteSyntomic f),
    detNL f hf ≅ omega f hf

/-- The two properties of Stacks 0FKD in their affine-local form: `δ(NL_{Y/X})` is carried to
`τ_{Y/X}`, and the value of the rule on a chart of `Y'` is the base change of its value on a chart
of `Y`, for every morphism `Y'/X' → Y/X` of the category of Section 0FKB and every compatible
quadruple of affine charts. -/
def IsTateRuleOnCharts (c : TateRule.{u}) : Prop :=
  (∀ (X Y : Scheme.{u}) [IsLocallyNoetherian X] (f : Y ⟶ X) (hf : IsQuasiFiniteSyntomic f),
    (c X Y f hf).hom.app ⊤ (deltaNL f hf) = tau f hf) ∧
  (∀ (X Y X' Y' : Scheme.{u}) [IsLocallyNoetherian X] [IsLocallyNoetherian X']
      (f : Y ⟶ X) (f' : Y' ⟶ X') (hf : IsQuasiFiniteSyntomic f)
      (hf' : IsQuasiFiniteSyntomic f') (sq : OpenBaseChangeSquare f f')
      (U : X.affineOpens) (V : Y.affineOpens) (U' : X'.affineOpens) (V' : Y'.affineOpens)
      (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
      (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1),
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
    letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := algebra_syntomic_appLE hf'.2 U' V' hV'U'
    haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
    ∀ (D : Stacks.TateMap.ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X', U'.1) Γ(Y', V'.1)),
      Stacks.TateMap.pullbackTate D (chartValue (c X Y f hf) U V hVU F) G =
        chartValue (c X' Y' f' hf') U' V' hV'U' G)

end AlgebraicGeometry.TateMap
