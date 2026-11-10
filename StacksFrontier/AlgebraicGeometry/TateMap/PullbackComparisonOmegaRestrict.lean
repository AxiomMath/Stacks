module

public import StacksFrontier.AlgebraicGeometry.TateMap.PullbackComparisonOmega
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineGenerators

/-!
# The chart comparison of `b^* ω_{Y/X}` with `ω_{Y'/X'}` commutes with restriction

For a morphism `b/a : Y'/X' → Y/X` of the category of Stacks, Section 0FKB, the comparison
`AlgebraicGeometry.TateMap.omegaChartPullbackEquiv` of the sections of `b^* ω_{Y/X}` and of
`ω_{Y'/X'}` over a chart quadruple `(U, V, U', V')` commutes with restriction to a quadruple of
principal opens `(D(a), D(b), D(a'), D(b'))` inside it.

## Main results

* `AlgebraicGeometry.TateMap.omegaChartPullbackEquiv_restrict`: the statement above, and
  `AlgebraicGeometry.TateMap.omegaChartPullbackEquiv_restrict_of_eq` with the smaller quadruple
  given by equations.

## Implementation notes

Sections of `b^* ω_{Y/X}` over `V'` are generated over `Γ(V')` by the pullbacks of sections of
`ω_{Y/X}` over `V`, so it suffices to compare the two sides on those. There both sides are base
changes of the image of the section in `ω_{Γ(V)/Γ(U)}`, along the two paths around the square
of chart base changes from `(U, V)` to `(D(a'), D(b'))`, which agree by the composition law of
`Stacks.TateMap.omegaBaseChange`.

## References

* [Stacks Project, Section 0FKB](https://stacks.math.columbia.edu/tag/0FKB)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings
open Stacks.Discriminant Stacks.TateMap Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace AlgebraicGeometry.TateMap

variable {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} (hf : IsQuasiFiniteSyntomic f)
  (hf' : IsQuasiFiniteSyntomic f') (sq : OpenBaseChangeSquare f f') [IsLocallyNoetherian X]
  [IsLocallyNoetherian X']

/-- **The chart comparison commutes with restriction to principal opens.** For a chart quadruple
`(U, V, U', V')` of the square and principal opens `D(a) ⊆ U`, `D(b) ⊆ V`, `D(a') ⊆ U'`,
`D(b') ⊆ V'` forming a chart quadruple again, the comparison over `D(b')` of the restriction of
a section of `b^* ω_{Y/X}` over `V'` is the restriction of its comparison over `V'`, for any chart
base change data and factorizations on the two quadruples. -/
theorem omegaChartPullbackEquiv_restrict (U : X.affineOpens) (V : Y.affineOpens)
    (U' : X'.affineOpens) (V' : Y'.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
    (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1) (a : Γ(X, U.1)) (b : Γ(Y, V.1)) (a' : Γ(X', U'.1))
    (b' : Γ(Y', V'.1)) (hba : Y.basicOpen b ≤ f ⁻¹ᵁ X.basicOpen a)
    (ha'a : X'.basicOpen a' ≤ sq.base ⁻¹ᵁ X.basicOpen a)
    (hb'a' : Y'.basicOpen b' ≤ f' ⁻¹ᵁ X'.basicOpen a')
    (hb'b : Y'.basicOpen b' ≤ sq.cover ⁻¹ᵁ Y.basicOpen b) :
    let Ua : X.affineOpens := ⟨X.basicOpen a, U.2.basicOpen a⟩
    let Vb : Y.affineOpens := ⟨Y.basicOpen b, V.2.basicOpen b⟩
    let Ua' : X'.affineOpens := ⟨X'.basicOpen a', U'.2.basicOpen a'⟩
    let Vb' : Y'.affineOpens := ⟨Y'.basicOpen b', V'.2.basicOpen b'⟩
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
    letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
    letI : Algebra Γ(X, Ua.1) Γ(Y, Vb.1) := (f.appLE Ua.1 Vb.1 hba).hom.toAlgebra
    letI : Algebra Γ(X, Ua.1) Γ(X', Ua'.1) := (sq.base.appLE Ua.1 Ua'.1 ha'a).hom.toAlgebra
    letI : Algebra Γ(X', Ua'.1) Γ(Y', Vb'.1) := (f'.appLE Ua'.1 Vb'.1 hb'a').hom.toAlgebra
    letI : Algebra Γ(Y, Vb.1) Γ(Y', Vb'.1) := (sq.cover.appLE Vb.1 Vb'.1 hb'b).hom.toAlgebra
    ∀ (D : ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1))
      (D₀ : ChartBaseChange Γ(X, Ua.1) Γ(Y, Vb.1) Γ(X', Ua'.1) Γ(Y', Vb'.1))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X', U'.1) Γ(Y', V'.1))
      (F₀ : FiniteOpenFactorization.{u, u, u} Γ(X, Ua.1) Γ(Y, Vb.1))
      (G₀ : FiniteOpenFactorization.{u, u, u} Γ(X', Ua'.1) Γ(Y', Vb'.1))
      (s : Γ((Scheme.Modules.pullback sq.cover).obj (omega f hf), V'.1)),
      omegaChartPullbackEquiv hf hf' sq Ua Vb Ua' Vb' hba ha'a hb'a' hb'b D₀ F₀ G₀
          (((Scheme.Modules.pullback sq.cover).obj (omega f hf)).presheaf.map
            (homOfLE (Y'.basicOpen_le b')).op s) =
        (omega f' hf').presheaf.map (homOfLE (Y'.basicOpen_le b')).op
          (omegaChartPullbackEquiv hf hf' sq U V U' V' hVU hU'U hV'U' hV'V D F G s) := by
  intro Ua Vb Ua' Vb' D D₀ F G F₀ G₀ s
  let := isLocallyNoetherian_source f hf
  let := isLocallyNoetherian_source f' hf'
  let := hf.1
  let := hf'.1
  have : Flat f := AlgebraicGeometry.flat hf.2
  have : Flat f' := AlgebraicGeometry.flat hf'.2
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
  let : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
  let : Algebra Γ(X, Ua.1) Γ(Y, Vb.1) := (f.appLE Ua.1 Vb.1 hba).hom.toAlgebra
  let : Algebra Γ(X, Ua.1) Γ(X', Ua'.1) := (sq.base.appLE Ua.1 Ua'.1 ha'a).hom.toAlgebra
  let : Algebra Γ(X', Ua'.1) Γ(Y', Vb'.1) := (f'.appLE Ua'.1 Vb'.1 hb'a').hom.toAlgebra
  let : Algebra Γ(Y, Vb.1) Γ(Y', Vb'.1) := (sq.cover.appLE Vb.1 Vb'.1 hb'b).hom.toAlgebra
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
  have : IsNoetherianRing Γ(X, Ua.1) := IsLocallyNoetherian.component_noetherian Ua
  have : IsNoetherianRing Γ(X', Ua'.1) := IsLocallyNoetherian.component_noetherian Ua'
  have : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  have : Module.Flat Γ(X', U'.1) Γ(Y', V'.1) :=
    RingHom.flat_algebraMap_iff.mp (f'.flat_appLE U'.2 V'.2 hV'U')
  have : Module.Flat Γ(X, Ua.1) Γ(Y, Vb.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE Ua.2 Vb.2 hba)
  -- reduction to pulled-back sections
  have hkey : ∀ t : Γ(omega f hf, V.1),
      omegaChartPullbackEquiv hf hf' sq Ua Vb Ua' Vb' hba ha'a hb'a' hb'b D₀ F₀ G₀
          (((Scheme.Modules.pullback sq.cover).obj (omega f hf)).presheaf.map
            (homOfLE (Y'.basicOpen_le b')).op
            (Scheme.Modules.pullbackSection sq.cover (omega f hf) V.1 V'.1 hV'V t)) =
        (omega f' hf').presheaf.map (homOfLE (Y'.basicOpen_le b')).op
          (omegaChartPullbackEquiv hf hf' sq U V U' V' hVU hU'U hV'U' hV'V D F G
            (Scheme.Modules.pullbackSection sq.cover (omega f hf) V.1 V'.1 hV'V t)) := by
    intro t
    have h₁ : ((Scheme.Modules.pullback sq.cover).obj (omega f hf)).presheaf.map
        (homOfLE (Y'.basicOpen_le b')).op
          (Scheme.Modules.pullbackSection sq.cover (omega f hf) V.1 V'.1 hV'V t) =
        Scheme.Modules.pullbackSection sq.cover (omega f hf) Vb.1 Vb'.1 hb'b
          ((omega f hf).presheaf.map (homOfLE (Y.basicOpen_le b)).op t) :=
      (Stacks.Conormal.pullbackSection_restrict_target sq.cover (omega f hf) V.1 V'.1 Vb'.1 hV'V
        (Y'.basicOpen_le b') t).trans
        (Stacks.Conormal.pullbackSection_restrict_source sq.cover (omega f hf) V.1 Vb.1
          (Y.basicOpen_le b) Vb'.1 hb'b t)
    apply ((omegaData f' hf').localEquiv Ua' Vb' hb'a' G₀).injective
    rw [h₁, omegaChartPullbackEquiv_pullbackSection]
    let DY := chartBaseChangeBasicOpen f U V hVU Ua.1 Vb.1 a b rfl rfl (X.basicOpen_le a)
      (Y.basicOpen_le b) hba
    let DY' := chartBaseChangeBasicOpen f' U' V' hV'U' Ua'.1 Vb'.1 a' b' rfl rfl
      (X'.basicOpen_le a') (Y'.basicOpen_le b') hb'a'
    have hY := localEquiv_restrict_eq_omegaBaseChange (omegaData f hf) U V hVU a b hba DY F F₀ t
    have hY' := localEquiv_restrict_eq_omegaBaseChange (omegaData f' hf') U' V' hV'U' a' b' hb'a'
      DY' G G₀ (omegaChartPullbackEquiv hf hf' sq U V U' V' hVU hU'U hV'U' hV'V D F G
        (Scheme.Modules.pullbackSection sq.cover (omega f hf) V.1 V'.1 hV'V t))
    have hD := omegaChartPullbackEquiv_pullbackSection hf hf' sq U V U' V' hVU hU'U hV'U' hV'V
      D F G t
    change omegaBaseChange D₀ F₀ G₀ (1 ⊗ₜ (omegaData f hf).localEquiv Ua Vb hba F₀
      (restrictₗ (omegaData f hf).sheaf (Y.basicOpen_le b) t)) = (omegaData f' hf').localEquiv
        Ua' Vb' hb'a' G₀ (restrictₗ (omegaData f' hf').sheaf (Y'.basicOpen_le b') _)
    rw [hY, hY', hD]
    -- the two paths around the square of chart base changes
    have hUa' : Ua'.1 ≤ sq.base ⁻¹ᵁ U.1 := ha'a.trans (sq.base.preimage_mono (X.basicOpen_le a))
    have hVb' : Vb'.1 ≤ sq.cover ⁻¹ᵁ V.1 := hb'b.trans (sq.cover.preimage_mono (Y.basicOpen_le b))
    let : Algebra Γ(X, U.1) Γ(X', Ua'.1) := (sq.base.appLE U.1 Ua'.1 hUa').hom.toAlgebra
    let : Algebra Γ(Y, V.1) Γ(Y', Vb'.1) := (sq.cover.appLE V.1 Vb'.1 hVb').hom.toAlgebra
    let : Algebra Γ(X, U.1) Γ(X, Ua.1) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
    let : Algebra Γ(Y, V.1) Γ(Y, Vb.1) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom.toAlgebra
    let : Algebra Γ(X', U'.1) Γ(X', Ua'.1) :=
      (X'.presheaf.map (homOfLE (X'.basicOpen_le a')).op).hom.toAlgebra
    let : Algebra Γ(Y', V'.1) Γ(Y', Vb'.1) :=
      (Y'.presheaf.map (homOfLE (Y'.basicOpen_le b')).op).hom.toAlgebra
    have : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) Γ(X', Ua'.1) := IsScalarTower.of_algebraMap_eq' (by
      change (sq.base.appLE U.1 Ua'.1 hUa').hom = (sq.base.appLE Ua.1 Ua'.1 ha'a).hom.comp
        (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
      rw [← CommRingCat.hom_comp, Scheme.Hom.map_appLE])
    have : IsScalarTower Γ(Y, V.1) Γ(Y, Vb.1) Γ(Y', Vb'.1) := IsScalarTower.of_algebraMap_eq' (by
      change (sq.cover.appLE V.1 Vb'.1 hVb').hom = (sq.cover.appLE Vb.1 Vb'.1 hb'b).hom.comp
        (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom
      rw [← CommRingCat.hom_comp, Scheme.Hom.map_appLE])
    have : IsScalarTower Γ(X, U.1) Γ(X', U'.1) Γ(X', Ua'.1) := IsScalarTower.of_algebraMap_eq' (by
      change (sq.base.appLE U.1 Ua'.1 hUa').hom =
        (X'.presheaf.map (homOfLE (X'.basicOpen_le a')).op).hom.comp
          (sq.base.appLE U.1 U'.1 hU'U).hom
      rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_map])
    have : IsScalarTower Γ(Y, V.1) Γ(Y', V'.1) Γ(Y', Vb'.1) := IsScalarTower.of_algebraMap_eq' (by
      change (sq.cover.appLE V.1 Vb'.1 hVb').hom =
        (Y'.presheaf.map (homOfLE (Y'.basicOpen_le b')).op).hom.comp
          (sq.cover.appLE V.1 V'.1 hV'V).hom
      rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_map])
    let D₃ := D₀.comp DY
    have h₃ : omegaBaseChange D₃ F G₀ (1 ⊗ₜ (omegaData f hf).localEquiv U V hVU F t) =
        omegaBaseChange D₀ F₀ G₀ (1 ⊗ₜ omegaBaseChange DY F F₀
          (1 ⊗ₜ (omegaData f hf).localEquiv U V hVU F t)) := by
      rw [omegaBaseChange_comp DY D₀ D₃ F F₀ G₀]
      rfl
    have h₄ : omegaBaseChange D₃ F G₀ (1 ⊗ₜ (omegaData f hf).localEquiv U V hVU F t) =
        omegaBaseChange DY' G G₀ (1 ⊗ₜ omegaBaseChange D F G
          (1 ⊗ₜ (omegaData f hf).localEquiv U V hVU F t)) := by
      rw [omegaBaseChange_comp D DY' D₃ F G G₀]
      rfl
    exact h₃.symm.trans h₄
  -- sections of the pullback are combinations of pulled-back sections
  obtain ⟨z, rfl⟩ :=
    (pullbackSectionsTensorEquiv sq.cover (omega f hf) V V' hV'V).surjective s
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul y t =>
      have h1 : pullbackSectionsTensorEquiv sq.cover (omega f hf) V V' hV'V
          ((1 : Γ(Y', V'.1)) ⊗ₜ t) =
          Scheme.Modules.pullbackSection sq.cover (omega f hf) V.1 V'.1 hV'V t :=
        pullbackSectionsTensorEquiv_one_tmul sq.cover (omega f hf) V V' hV'V t
      rw [show y ⊗ₜ[Γ(Y, V.1)] t = y • ((1 : Γ(Y', V'.1)) ⊗ₜ t) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, h1]
      set p : Γ((Scheme.Modules.pullback sq.cover).obj (omega f hf), V'.1) :=
        Scheme.Modules.pullbackSection sq.cover (omega f hf) V.1 V'.1 hV'V t
      have e₁ := Scheme.Modules.map_smul ((Scheme.Modules.pullback sq.cover).obj (omega f hf))
        (homOfLE (Y'.basicOpen_le b')) y p
      have e₂ := (omegaChartPullbackEquiv hf hf' sq U V U' V' hVU hU'U hV'U' hV'V D F G).map_smul
        y p
      have e₃ := Scheme.Modules.map_smul (omega f' hf') (homOfLE (Y'.basicOpen_le b')) y
        (omegaChartPullbackEquiv hf hf' sq U V U' V' hVU hU'U hV'U' hV'V D F G p)
      calc _ = omegaChartPullbackEquiv hf hf' sq Ua Vb Ua' Vb' hba ha'a hb'a' hb'b D₀ F₀ G₀
            (Y'.presheaf.map (homOfLE (Y'.basicOpen_le b')).op y •
              ((Scheme.Modules.pullback sq.cover).obj (omega f hf)).presheaf.map
                (homOfLE (Y'.basicOpen_le b')).op p) := congrArg _ e₁
        _ = Y'.presheaf.map (homOfLE (Y'.basicOpen_le b')).op y •
            omegaChartPullbackEquiv hf hf' sq Ua Vb Ua' Vb' hba ha'a hb'a' hb'b D₀ F₀ G₀
              (((Scheme.Modules.pullback sq.cover).obj (omega f hf)).presheaf.map
                (homOfLE (Y'.basicOpen_le b')).op p) := map_smul _ _ _
        _ = Y'.presheaf.map (homOfLE (Y'.basicOpen_le b')).op y •
            (omega f' hf').presheaf.map (homOfLE (Y'.basicOpen_le b')).op
              (omegaChartPullbackEquiv hf hf' sq U V U' V' hVU hU'U hV'U' hV'V D F G p) := by
          rw [hkey t]
        _ = _ := e₃.symm
        _ = _ := congrArg _ e₂.symm

/-- **The chart comparison commutes with restriction to principal opens**, with the smaller chart
quadruple `(U₀, V₀, U'₀, V'₀)` given by equations `U₀ = D(a)`, `V₀ = D(b)`, `U'₀ = D(a')`,
`V'₀ = D(b')`. -/
theorem omegaChartPullbackEquiv_restrict_of_eq (U : X.affineOpens) (V : Y.affineOpens)
    (U' : X'.affineOpens) (V' : Y'.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
    (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1) (U₀ : X.affineOpens) (V₀ : Y.affineOpens)
    (U'₀ : X'.affineOpens) (V'₀ : Y'.affineOpens) (hV₀U₀ : V₀.1 ≤ f ⁻¹ᵁ U₀.1)
    (hU'₀U₀ : U'₀.1 ≤ sq.base ⁻¹ᵁ U₀.1) (hV'₀U'₀ : V'₀.1 ≤ f' ⁻¹ᵁ U'₀.1)
    (hV'₀V₀ : V'₀.1 ≤ sq.cover ⁻¹ᵁ V₀.1) (a : Γ(X, U.1)) (b : Γ(Y, V.1)) (a' : Γ(X', U'.1))
    (b' : Γ(Y', V'.1)) (ha : U₀.1 = X.basicOpen a) (hb : V₀.1 = Y.basicOpen b)
    (ha' : U'₀.1 = X'.basicOpen a') (hb' : V'₀.1 = Y'.basicOpen b') (hle : V'₀.1 ≤ V'.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
    letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
    letI : Algebra Γ(X, U₀.1) Γ(Y, V₀.1) := (f.appLE U₀.1 V₀.1 hV₀U₀).hom.toAlgebra
    letI : Algebra Γ(X, U₀.1) Γ(X', U'₀.1) := (sq.base.appLE U₀.1 U'₀.1 hU'₀U₀).hom.toAlgebra
    letI : Algebra Γ(X', U'₀.1) Γ(Y', V'₀.1) := (f'.appLE U'₀.1 V'₀.1 hV'₀U'₀).hom.toAlgebra
    letI : Algebra Γ(Y, V₀.1) Γ(Y', V'₀.1) := (sq.cover.appLE V₀.1 V'₀.1 hV'₀V₀).hom.toAlgebra
    ∀ (D : ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1))
      (D₀ : ChartBaseChange Γ(X, U₀.1) Γ(Y, V₀.1) Γ(X', U'₀.1) Γ(Y', V'₀.1))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X', U'.1) Γ(Y', V'.1))
      (F₀ : FiniteOpenFactorization.{u, u, u} Γ(X, U₀.1) Γ(Y, V₀.1))
      (G₀ : FiniteOpenFactorization.{u, u, u} Γ(X', U'₀.1) Γ(Y', V'₀.1))
      (s : Γ((Scheme.Modules.pullback sq.cover).obj (omega f hf), V'.1)),
      omegaChartPullbackEquiv hf hf' sq U₀ V₀ U'₀ V'₀ hV₀U₀ hU'₀U₀ hV'₀U'₀ hV'₀V₀ D₀ F₀ G₀
          (((Scheme.Modules.pullback sq.cover).obj (omega f hf)).presheaf.map
            (homOfLE hle).op s) =
        (omega f' hf').presheaf.map (homOfLE hle).op
          (omegaChartPullbackEquiv hf hf' sq U V U' V' hVU hU'U hV'U' hV'V D F G s) := by
  obtain ⟨U₀, hU₀⟩ := U₀
  obtain ⟨V₀, hV₀⟩ := V₀
  obtain ⟨U'₀, hU'₀⟩ := U'₀
  obtain ⟨V'₀, hV'₀⟩ := V'₀
  simp only at ha hb ha' hb'
  subst ha hb ha' hb'
  exact omegaChartPullbackEquiv_restrict hf hf' sq U V U' V' hVU hU'U hV'U' hV'V a b a' b'
    hV₀U₀ hU'₀U₀ hV'₀U'₀ hV'₀V₀

end AlgebraicGeometry.TateMap
