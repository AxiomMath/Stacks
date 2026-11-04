module

public import StacksFrontier.AlgebraicGeometry.TateMap.PullbackComparisonOmegaRestrict
public import StacksFrontier.AlgebraicGeometry.TateMap.PullbackCharts

/-!
# The pullback comparison `b^* ω_{Y/X} ≅ ω_{Y'/X'}`

For a morphism `b/a : Y'/X' → Y/X` of the category of Stacks, Section 0FKB, the chart comparisons
`AlgebraicGeometry.TateMap.omegaChartPullbackEquiv` on the charts of the square agree on principal
refinements, so they glue to an isomorphism `b^* ω_{Y/X} ≅ ω_{Y'/X'}` of `𝒪_{Y'}`-modules: on every
chart on which the square is a chart base change, it is the base change of the affine dualizing
modules of Tag 0BVB.

## Main definitions

* `AlgebraicGeometry.TateMap.omegaPullbackIso`: the comparison.

## Main results

* `AlgebraicGeometry.TateMap.omegaPullbackIso_pullbackSection`: its value on pulled-back sections
  over a chart base change.

## References

* [Stacks Project, Section 0FKB](https://stacks.math.columbia.edu/tag/0FKB)
* [Stacks Project, Tag 0BVB](https://stacks.math.columbia.edu/tag/0BVB)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct
open Stacks.Discriminant Stacks.TateMap

universe u

namespace AlgebraicGeometry.TateMap

variable {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} (hf : IsQuasiFiniteSyntomic f)
  (hf' : IsQuasiFiniteSyntomic f') (sq : OpenBaseChangeSquare f f') [IsLocallyNoetherian X]
  [IsLocallyNoetherian X']

/-- A chosen finite-open factorization of the chart `Γ(U) → Γ(V)` of a locally quasi-finite
syntomic morphism. -/
def omegaFactorization {X Y : Scheme.{u}} [IsLocallyNoetherian X] {f : Y ⟶ X}
    (hf : IsQuasiFiniteSyntomic f) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
  letI := isLocallyNoetherian_source f hf
  letI := hf.1
  ((omegaData f hf).factorization U V hVU).some

/-- The chart comparison on a chart of the square. -/
abbrev OpenBaseChangeSquare.Chart.omegaEquiv {sq : OpenBaseChangeSquare f f'} (k : sq.Chart) :
    Γ((Scheme.Modules.pullback sq.cover).obj (omega f hf), k.V'.1) ≃ₗ[Γ(Y', k.V'.1)]
      Γ(omega f' hf', k.V'.1) :=
  omegaChartPullbackEquiv hf hf' sq k.U k.V k.U' k.V' k.hVU k.hU'U k.hV'U' k.hV'V k.D
    (omegaFactorization hf k.U k.V k.hVU) (omegaFactorization hf' k.U' k.V' k.hV'U')

/-- The isomorphism `b^* ω_{Y/X} ≅ ω_{Y'/X'}` exists, with the chart comparisons as its sections
over the charts. -/
theorem exists_omegaPullbackIso :
    ∃ c : (Scheme.Modules.pullback sq.cover).obj (omega f hf) ≅ omega f' hf',
      ∀ (k : sq.Chart) (s : Γ((Scheme.Modules.pullback sq.cover).obj (omega f hf), k.V'.1)),
        c.hom.app k.V'.1 s = k.omegaEquiv hf hf' s :=
  sq.exists_iso_of_chart (fun k ↦ k.omegaEquiv hf hf')
    fun k m a b a' b' ha hb ha' hb' hle s ↦
      omegaChartPullbackEquiv_restrict_of_eq hf hf' sq k.U k.V k.U' k.V' k.hVU k.hU'U k.hV'U'
        k.hV'V m.U m.V m.U' m.V' m.hVU m.hU'U m.hV'U' m.hV'V a b a' b' ha hb ha' hb' hle k.D m.D
        _ _ _ _ s

/-- **The pullback of `ω_{Y/X}` along a morphism `b/a : Y'/X' → Y/X` of the category of Section
0FKB is `ω_{Y'/X'}`**: on charts on which the square is a chart base change, it is the base change
of the affine dualizing modules. -/
def omegaPullbackIso : (Scheme.Modules.pullback sq.cover).obj (omega f hf) ≅ omega f' hf' :=
  (exists_omegaPullbackIso hf hf' sq).choose

/-- **The pullback comparison of `ω` on a chart base change**: the affine dualizing module image of
the comparison of the pullback of a section `t` over `V` is the base change of the image of `t`. -/
theorem omegaPullbackIso_pullbackSection (U : X.affineOpens) (V : Y.affineOpens)
    (U' : X'.affineOpens) (V' : Y'.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
    (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1) :
    letI := isLocallyNoetherian_source f hf
    letI := isLocallyNoetherian_source f' hf'
    letI := hf.1
    letI := hf'.1
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
    letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
    haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
    haveI : Flat f := AlgebraicGeometry.flat hf.2
    haveI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    ∀ (D : ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X', U'.1) Γ(Y', V'.1)) (t : Γ(omega f hf, V.1)),
      (omegaData f' hf').localEquiv U' V' hV'U' G
          ((omegaPullbackIso hf hf' sq).hom.app V'.1
            (Scheme.Modules.pullbackSection sq.cover (omega f hf) V.1 V'.1 hV'V t)) =
        omegaBaseChange D F G (1 ⊗ₜ (omegaData f hf).localEquiv U V hVU F t) := by
  intro D F G t
  let := isLocallyNoetherian_source f hf
  let := isLocallyNoetherian_source f' hf'
  let := hf.1
  let := hf'.1
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
  let : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
  have : Flat f := AlgebraicGeometry.flat hf.2
  have : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  set F₀ := omegaFactorization hf U V hVU
  set G₀ := omegaFactorization hf' U' V' hV'U'
  have hk : (omegaPullbackIso hf hf' sq).hom.app V'.1
      (Scheme.Modules.pullbackSection sq.cover (omega f hf) V.1 V'.1 hV'V t) =
      omegaChartPullbackEquiv hf hf' sq U V U' V' hVU hU'U hV'U' hV'V D F₀ G₀
        (Scheme.Modules.pullbackSection sq.cover (omega f hf) V.1 V'.1 hV'V t) :=
    (exists_omegaPullbackIso hf hf' sq).choose_spec ⟨U, V, U', V', hVU, hU'U, hV'U', hV'V, D⟩ _
  rw [hk, (omegaData f' hf').localEquiv_natural U' V' hV'U' G₀ G,
    omegaChartPullbackEquiv_pullbackSection, omegaBaseChange_natural_right,
    (omegaData f hf).localEquiv_natural U V hVU F F₀, omegaBaseChange_one_tmul_natural_left]

end AlgebraicGeometry.TateMap
