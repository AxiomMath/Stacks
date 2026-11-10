module

public import StacksFrontier.AlgebraicGeometry.TateMap.PullbackCharts
public import StacksFrontier.AlgebraicGeometry.TateMap.DetNLSheaf
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineGenerators

/-!
# The pullback of `det(NL_{Y/X})` along a morphism of the category of Section 0FKB

Let `b/a : Y'/X' → Y/X` be a morphism of the category of Stacks, Section 0FKB, between locally
quasi-finite syntomic morphisms `f : Y ⟶ X` and `f' : Y' ⟶ X'`. The pullback `b^* det(NL_{Y/X})`
is canonically `det(NL_{Y'/X'})`: on affine charts `U, V, U', V'` on which the square is a chart
base change, the sections of the pullback over `V'` are `Γ(V') ⊗_{Γ(V)} det(NL_{Γ(V)/Γ(U)})`, which
the base change of the determinant identifies with `det(NL_{Γ(V')/Γ(U')})`.

## Main definitions

* `AlgebraicGeometry.TateMap.detNLPullbackIso`: the isomorphism
  `b^* det(NL_{Y/X}) ≅ det(NL_{Y'/X'})`.

## Main results

* `AlgebraicGeometry.TateMap.detNLPullbackIso_pullbackSection`: on every chart base change, the
  isomorphism sends the pullback of a section to the base change of the section.

## References

* [Stacks Project, Section 0FKB](https://stacks.math.columbia.edu/tag/0FKB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.TateMap

/-- The composition law of the base change of `det(NL)`, read on `1 ⊗ x`. -/
theorem detNLBaseChange_comp_one_tmul {A B A' B' A'' B'' : Type u} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] [CommRing A''] [CommRing B''] [Algebra A B] [Algebra A A']
    [Algebra A' B'] [Algebra B B'] [Algebra A' A''] [Algebra B' B''] [Algebra A A'']
    [Algebra B B''] [Algebra A'' B''] [IsScalarTower A A' A''] [IsScalarTower B B' B'']
    [Algebra.Syntomic A B] [Algebra.Syntomic A' B'] [Algebra.Syntomic A'' B'']
    (D₁ : ChartBaseChange A B A' B') (D₂ : ChartBaseChange A' B' A'' B'')
    (D₃ : ChartBaseChange A B A'' B'') (x : detNL A B) :
    detNLBaseChange D₃ ((1 : B'') ⊗ₜ x) =
      detNLBaseChange D₂ ((1 : B'') ⊗ₜ detNLBaseChange D₁ ((1 : B') ⊗ₜ x)) := by
  rw [detNLBaseChange_comp D₁ D₂ D₃, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul]

end Stacks.TateMap

namespace AlgebraicGeometry.TateMap

open Stacks.TateMap (ChartBaseChange detNLBaseChange)

/-- `AlgebraicGeometry.TateMap.detNLChartEquiv_restrict` with the two principal opens given by
equations `U₀ = D(a)` and `V₀ = D(b)`. -/
private theorem detNLChartEquiv_restrict_of_eq' {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsQuasiFiniteSyntomic f) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (U₀ : X.affineOpens) (V₀ : Y.affineOpens) (a : Γ(X, U.1))
    (b : Γ(Y, V.1)) (ha : U₀.1 = X.basicOpen a) (hb : V₀.1 = Y.basicOpen b) (hU₀ : U₀.1 ≤ U.1)
    (hV₀ : V₀.1 ≤ V.1) (hV₀U₀ : V₀.1 ≤ f ⁻¹ᵁ U₀.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, U₀.1) Γ(Y, V₀.1) := (f.appLE U₀ V₀ hV₀U₀).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X, U₀.1) := (X.presheaf.map (homOfLE hU₀).op).hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y, V₀.1) := (Y.presheaf.map (homOfLE hV₀).op).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := algebra_syntomic_appLE hf.2 U₀ V₀ hV₀U₀
    ∀ (D : ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X, U₀.1) Γ(Y, V₀.1)) (t : Γ(detNL f hf, V.1)),
      detNLChartEquiv f hf U₀ V₀ hV₀U₀ ((detNL f hf).presheaf.map (homOfLE hV₀).op t) =
        detNLBaseChange D ((1 : Γ(Y, V₀.1)) ⊗ₜ detNLChartEquiv f hf U V hVU t) := by
  obtain ⟨U₀, hU₀'⟩ := U₀
  obtain ⟨V₀, hV₀'⟩ := V₀
  simp only at ha hb
  subst ha hb
  exact detNLChartEquiv_restrict f hf U V hVU a b hV₀U₀

variable {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'}

variable (hf : IsQuasiFiniteSyntomic f) (hf' : IsQuasiFiniteSyntomic f')
  (sq : OpenBaseChangeSquare f f')

/-- **The comparison on a chart base change.** For affine charts `U, V, U', V'` on which the square
is a chart base change `D`, the sections over `V'` of the pullback of `det(NL_{Y/X})` are
`Γ(V') ⊗_{Γ(V)} det(NL_{Γ(V)/Γ(U)})`, identified by `D` with `det(NL_{Γ(V')/Γ(U')})`. -/
def detNLPullbackChartEquiv (U : X.affineOpens) (V : Y.affineOpens) (U' : X'.affineOpens)
    (V' : Y'.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1)
    (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1) (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
    letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := algebra_syntomic_appLE hf'.2 U' V' hV'U'
    ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1) →
      (Γ((Scheme.Modules.pullback sq.cover).obj (detNL f hf), V'.1) ≃ₗ[Γ(Y', V'.1)]
        Γ(detNL f' hf', V'.1)) := fun D ↦
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
  letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
  letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
  haveI := algebra_syntomic_appLE hf.2 U V hVU
  haveI := algebra_syntomic_appLE hf'.2 U' V' hV'U'
  haveI := isQuasicoherent_detNL f hf
  (pullbackSectionsTensorEquiv sq.cover (detNL f hf) V V' hV'V).symm ≪≫ₗ
    (detNLChartEquiv f hf U V hVU).baseChange Γ(Y, V.1) Γ(Y', V'.1) ≪≫ₗ
    detNLBaseChange D ≪≫ₗ (detNLChartEquiv f' hf' U' V' hV'U').symm

/-- The comparison on a chart base change sends the pullback of a section `s` to the base change
of `s`. -/
theorem detNLPullbackChartEquiv_pullbackSection (U : X.affineOpens) (V : Y.affineOpens)
    (U' : X'.affineOpens) (V' : Y'.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
    (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
    letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := algebra_syntomic_appLE hf'.2 U' V' hV'U'
    ∀ (D : ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1))
      (s : Γ(detNL f hf, V.1)),
      detNLPullbackChartEquiv hf hf' sq U V U' V' hVU hU'U hV'U' hV'V D
          (Scheme.Modules.pullbackSection sq.cover (detNL f hf) V.1 V'.1 hV'V s) =
        (detNLChartEquiv f' hf' U' V' hV'U').symm
          (detNLBaseChange D ((1 : Γ(Y', V'.1)) ⊗ₜ detNLChartEquiv f hf U V hVU s)) := by
  intro D s
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
  let : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 U V hVU
  have := algebra_syntomic_appLE hf'.2 U' V' hV'U'
  have := isQuasicoherent_detNL f hf
  have h := (LinearEquiv.symm_apply_eq _).mpr
    (pullbackSectionsTensorEquiv_one_tmul sq.cover (detNL f hf) V V' hV'V s).symm
  change (detNLChartEquiv f' hf' U' V' hV'U').symm (detNLBaseChange D
    (LinearEquiv.baseChange Γ(Y, V.1) Γ(Y', V'.1) _ _ (detNLChartEquiv f hf U V hVU)
      ((pullbackSectionsTensorEquiv sq.cover (detNL f hf) V V' hV'V).symm
        (Scheme.Modules.pullbackSection sq.cover (detNL f hf) V.1 V'.1 hV'V s)))) = _
  rw [h, LinearEquiv.baseChange_tmul]

namespace OpenBaseChangeSquare.Chart

variable {sq}

/-- The comparison `AlgebraicGeometry.TateMap.detNLPullbackChartEquiv` on a chart base change. -/
abbrev equiv (k : sq.Chart) :
    Γ((Scheme.Modules.pullback sq.cover).obj (detNL f hf), k.V'.1) ≃ₗ[Γ(Y', k.V'.1)]
      Γ(detNL f' hf', k.V'.1) :=
  detNLPullbackChartEquiv hf hf' sq k.U k.V k.U' k.V' k.hVU k.hU'U k.hV'U' k.hV'V k.D

/-- **The comparisons on two chart base changes agree on pullbacks of sections**, when the second
is a principal-open refinement of the first. -/
theorem equiv_restrict_pullbackSection (k m : sq.Chart) (a : Γ(X, k.U.1)) (b : Γ(Y, k.V.1))
    (a' : Γ(X', k.U'.1)) (b' : Γ(Y', k.V'.1)) (ha : m.U.1 = X.basicOpen a)
    (hb : m.V.1 = Y.basicOpen b) (ha' : m.U'.1 = X'.basicOpen a')
    (hb' : m.V'.1 = Y'.basicOpen b') (hle : m.V'.1 ≤ k.V'.1) (x : Γ(detNL f hf, k.V.1)) :
    m.equiv hf hf' (((Scheme.Modules.pullback sq.cover).obj (detNL f hf)).presheaf.map
        (homOfLE hle).op (Scheme.Modules.pullbackSection sq.cover (detNL f hf) k.V.1 k.V'.1
          k.hV'V x)) =
      (detNL f' hf').presheaf.map (homOfLE hle).op
        (k.equiv hf hf' (Scheme.Modules.pullbackSection sq.cover (detNL f hf) k.V.1 k.V'.1
          k.hV'V x)) := by
  have hU : m.U.1 ≤ k.U.1 := ha ▸ X.basicOpen_le a
  have hV : m.V.1 ≤ k.V.1 := hb ▸ Y.basicOpen_le b
  have hU' : m.U'.1 ≤ k.U'.1 := ha' ▸ X'.basicOpen_le a'
  have hV' : m.V'.1 ≤ k.V'.1 := hb' ▸ Y'.basicOpen_le b'
  let : Algebra Γ(X, k.U.1) Γ(Y, k.V.1) := (f.appLE k.U.1 k.V.1 k.hVU).hom.toAlgebra
  let : Algebra Γ(X, k.U.1) Γ(X', k.U'.1) := (sq.base.appLE k.U.1 k.U'.1 k.hU'U).hom.toAlgebra
  let : Algebra Γ(X', k.U'.1) Γ(Y', k.V'.1) := (f'.appLE k.U'.1 k.V'.1 k.hV'U').hom.toAlgebra
  let : Algebra Γ(Y, k.V.1) Γ(Y', k.V'.1) := (sq.cover.appLE k.V.1 k.V'.1 k.hV'V).hom.toAlgebra
  let : Algebra Γ(X, m.U.1) Γ(Y, m.V.1) := (f.appLE m.U.1 m.V.1 m.hVU).hom.toAlgebra
  let : Algebra Γ(X, m.U.1) Γ(X', m.U'.1) := (sq.base.appLE m.U.1 m.U'.1 m.hU'U).hom.toAlgebra
  let : Algebra Γ(X', m.U'.1) Γ(Y', m.V'.1) := (f'.appLE m.U'.1 m.V'.1 m.hV'U').hom.toAlgebra
  let : Algebra Γ(Y, m.V.1) Γ(Y', m.V'.1) := (sq.cover.appLE m.V.1 m.V'.1 m.hV'V).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 k.U k.V k.hVU
  have := algebra_syntomic_appLE hf'.2 k.U' k.V' k.hV'U'
  have := algebra_syntomic_appLE hf.2 m.U m.V m.hVU
  have := algebra_syntomic_appLE hf'.2 m.U' m.V' m.hV'U'
  let : Algebra Γ(X, k.U.1) Γ(X, m.U.1) := (X.presheaf.map (homOfLE hU).op).hom.toAlgebra
  let : Algebra Γ(Y, k.V.1) Γ(Y, m.V.1) := (Y.presheaf.map (homOfLE hV).op).hom.toAlgebra
  let : Algebra Γ(X', k.U'.1) Γ(X', m.U'.1) := (X'.presheaf.map (homOfLE hU').op).hom.toAlgebra
  let : Algebra Γ(Y', k.V'.1) Γ(Y', m.V'.1) := (Y'.presheaf.map (homOfLE hV').op).hom.toAlgebra
  let : Algebra Γ(X, k.U.1) Γ(X', m.U'.1) :=
    (sq.base.appLE k.U.1 m.U'.1 (hU'.trans k.hU'U)).hom.toAlgebra
  let : Algebra Γ(Y, k.V.1) Γ(Y', m.V'.1) :=
    (sq.cover.appLE k.V.1 m.V'.1 (hV'.trans k.hV'V)).hom.toAlgebra
  have : IsScalarTower Γ(X, k.U.1) Γ(X', k.U'.1) Γ(X', m.U'.1) :=
    isScalarTower_appLE_restrict sq.base k.hU'U hU'
  have : IsScalarTower Γ(Y, k.V.1) Γ(Y', k.V'.1) Γ(Y', m.V'.1) :=
    isScalarTower_appLE_restrict sq.cover k.hV'V hV'
  have : IsScalarTower Γ(X, k.U.1) Γ(X, m.U.1) Γ(X', m.U'.1) :=
    isScalarTower_restrict_appLE sq.base hU m.hU'U
  have : IsScalarTower Γ(Y, k.V.1) Γ(Y, m.V.1) Γ(Y', m.V'.1) :=
    isScalarTower_restrict_appLE sq.cover hV m.hV'V
  let E := chartBaseChangeBasicOpen f k.U k.V k.hVU m.U.1 m.V.1 a b ha hb hU hV m.hVU
  let E' := chartBaseChangeBasicOpen f' k.U' k.V' k.hV'U' m.U'.1 m.V'.1 a' b' ha' hb' hU' hV'
    m.hV'U'
  let D₃ := E'.comp k.D
  have h₁ : ((Scheme.Modules.pullback sq.cover).obj (detNL f hf)).presheaf.map (homOfLE hle).op
      (Scheme.Modules.pullbackSection sq.cover (detNL f hf) k.V.1 k.V'.1 k.hV'V x) =
      Scheme.Modules.pullbackSection sq.cover (detNL f hf) m.V.1 m.V'.1 m.hV'V
        ((detNL f hf).presheaf.map (homOfLE hV).op x) :=
    (Stacks.Conormal.pullbackSection_restrict_target sq.cover (detNL f hf) k.V.1 k.V'.1 m.V'.1
      k.hV'V hle x).trans
      (Stacks.Conormal.pullbackSection_restrict_source sq.cover (detNL f hf) k.V.1 m.V.1 hV
        m.V'.1 m.hV'V x)
  have hm := detNLPullbackChartEquiv_pullbackSection hf hf' sq m.U m.V m.U' m.V' m.hVU m.hU'U
    m.hV'U' m.hV'V m.D ((detNL f hf).presheaf.map (homOfLE hV).op x)
  have hk := detNLPullbackChartEquiv_pullbackSection hf hf' sq k.U k.V k.U' k.V' k.hVU k.hU'U
    k.hV'U' k.hV'V k.D x
  have hE := detNLChartEquiv_restrict_of_eq' f hf k.U k.V k.hVU m.U m.V a b ha hb hU hV m.hVU E x
  have hE' := detNLChartEquiv_restrict_of_eq' f' hf' k.U' k.V' k.hV'U' m.U' m.V' a' b' ha' hb' hU'
    hV' m.hV'U' E'
  have c₁ := Stacks.TateMap.detNLBaseChange_comp_one_tmul E m.D D₃
    (detNLChartEquiv f hf k.U k.V k.hVU x)
  have c₂ := Stacks.TateMap.detNLBaseChange_comp_one_tmul k.D E' D₃
    (detNLChartEquiv f hf k.U k.V k.hVU x)
  rw [h₁, equiv, hm, equiv, hk, LinearEquiv.symm_apply_eq, hE', LinearEquiv.apply_symm_apply, hE,
    ← c₁, c₂]

/-- **The comparisons on two chart base changes agree**, when the second is a principal-open
refinement of the first. -/
theorem equiv_restrict (k m : sq.Chart) (a : Γ(X, k.U.1)) (b : Γ(Y, k.V.1))
    (a' : Γ(X', k.U'.1)) (b' : Γ(Y', k.V'.1)) (ha : m.U.1 = X.basicOpen a)
    (hb : m.V.1 = Y.basicOpen b) (ha' : m.U'.1 = X'.basicOpen a')
    (hb' : m.V'.1 = Y'.basicOpen b') (hle : m.V'.1 ≤ k.V'.1)
    (s : Γ((Scheme.Modules.pullback sq.cover).obj (detNL f hf), k.V'.1)) :
    m.equiv hf hf' (((Scheme.Modules.pullback sq.cover).obj (detNL f hf)).presheaf.map
        (homOfLE hle).op s) =
      (detNL f' hf').presheaf.map (homOfLE hle).op (k.equiv hf hf' s) := by
  have := isQuasicoherent_detNL f hf
  let : Algebra Γ(Y, k.V.1) Γ(Y', k.V'.1) := (sq.cover.appLE k.V.1 k.V'.1 k.hV'V).hom.toAlgebra
  obtain ⟨z, rfl⟩ :=
    (pullbackSectionsTensorEquiv sq.cover (detNL f hf) k.V k.V' k.hV'V).surjective s
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add] at hz hw ⊢; rw [hz, hw]
  | tmul t x =>
    rw [pullbackSectionsTensorEquiv_tmul]
    have hM := ((Scheme.Modules.pullback sq.cover).obj (detNL f hf)).val.map_smul
      (homOfLE hle).op t (pullbackSectionHom sq.cover (detNL f hf) k.V.1 k.V'.1 k.hV'V x)
    have hN := (detNL f' hf').val.map_smul (homOfLE hle).op t
      (k.equiv hf hf' (pullbackSectionHom sq.cover (detNL f hf) k.V.1 k.V'.1 k.hV'V x))
    have e₁ := (m.equiv hf hf').map_smul (Y'.presheaf.map (homOfLE hle).op t)
      (((Scheme.Modules.pullback sq.cover).obj (detNL f hf)).presheaf.map (homOfLE hle).op
        (pullbackSectionHom sq.cover (detNL f hf) k.V.1 k.V'.1 k.hV'V x))
    have e₂ := (k.equiv hf hf').map_smul t
      (pullbackSectionHom sq.cover (detNL f hf) k.V.1 k.V'.1 k.hV'V x)
    have hc := equiv_restrict_pullbackSection hf hf' k m a b a' b' ha hb ha' hb' hle x
    exact (congrArg (m.equiv hf hf') hM).trans (e₁.trans
      ((congrArg (Y'.presheaf.map (homOfLE hle).op t • ·) hc).trans
        (hN.symm.trans (congrArg ((detNL f' hf').presheaf.map (homOfLE hle).op) e₂.symm))))

end OpenBaseChangeSquare.Chart

/-- The isomorphism `b^* det(NL_{Y/X}) ≅ det(NL_{Y'/X'})` exists, with the chart comparisons as
its sections over the charts. -/
theorem exists_detNLPullbackIso :
    ∃ c : (Scheme.Modules.pullback sq.cover).obj (detNL f hf) ≅ detNL f' hf',
      ∀ (k : sq.Chart) (s : Γ((Scheme.Modules.pullback sq.cover).obj (detNL f hf), k.V'.1)),
        c.hom.app k.V'.1 s = k.equiv hf hf' s :=
  sq.exists_iso_of_chart (fun k ↦ k.equiv hf hf') (OpenBaseChangeSquare.Chart.equiv_restrict hf hf')

/-- **The pullback of `det(NL_{Y/X})` along a morphism `b/a : Y'/X' → Y/X` of the category of
Section 0FKB is `det(NL_{Y'/X'})`**: on charts on which the square is a chart base change, it is
the base change of the determinant of the naive cotangent complex. -/
def detNLPullbackIso : (Scheme.Modules.pullback sq.cover).obj (detNL f hf) ≅ detNL f' hf' :=
  (exists_detNLPullbackIso hf hf' sq).choose

/-- **The pullback comparison of `det(NL)` on a chart base change**: it sends the pullback of a
section `s` over `V` to the base change of `s` along the chart base change. -/
theorem detNLPullbackIso_pullbackSection (U : X.affineOpens) (V : Y.affineOpens)
    (U' : X'.affineOpens) (V' : Y'.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
    (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
    letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := algebra_syntomic_appLE hf'.2 U' V' hV'U'
    ∀ (D : ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1))
      (s : Γ(detNL f hf, V.1)),
      (detNLPullbackIso hf hf' sq).hom.app V'.1
          (Scheme.Modules.pullbackSection sq.cover (detNL f hf) V.1 V'.1 hV'V s) =
        (detNLChartEquiv f' hf' U' V' hV'U').symm
          (detNLBaseChange D ((1 : Γ(Y', V'.1)) ⊗ₜ detNLChartEquiv f hf U V hVU s)) := fun D s ↦
  ((exists_detNLPullbackIso hf hf' sq).choose_spec
    ⟨U, V, U', V', hVU, hU'U, hV'U', hV'V, D⟩ _).trans
    (detNLPullbackChartEquiv_pullbackSection hf hf' sq U V U' V' hVU hU'U hV'U' hV'V D s)

end AlgebraicGeometry.TateMap
