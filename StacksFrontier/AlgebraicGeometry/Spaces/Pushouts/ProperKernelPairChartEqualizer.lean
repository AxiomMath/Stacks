module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartBijectivePropagation
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctionsNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairAffineDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# Equalizers of global functions over the étale charts of a base

Let `p₀ : C₀ ⟶ X'` and `p₁ : C₁ ⟶ X'` be quasi-compact and quasi-separated morphisms of
algebraic spaces and `δ₀, δ₁ : C₁ ⟶ C₀` two morphisms over `X'`.  For an étale chart `W` of `X'`
consider the diagram of global functions

`Γ(W) ⟶ Γ(C₀ ×_{X'} W) ⇉ Γ(C₁ ×_{X'} W)`.

This file shows that if it is an equalizer for an affine chart `W`, then it is one for every
affine chart `W'` lying over `W`.  This is the étale base change of the last paragraph of the
proof of Stacks 0AGG: the source says that `𝒪_{X'}` is the equalizer of `π_* 𝒪_Y ⇉ π_* 𝒪_{R}`
and reads off the global functions of `U ×_{X'} Y` over an affine `U` étale over `X'`.

## Main definitions

* `AlgebraicGeometry.Space.ChartGlobalFunctionsEqualizer`: the diagram above is an equalizer.

## Main results

* `AlgebraicGeometry.Space.GlobalFunctionsEqualizer.of_iso`: the equalizer property is invariant
  under isomorphisms of diagrams.
* `AlgebraicGeometry.Space.chartGlobalFunctionsEqualizer_iff_bijective`: at a chart `W` the
  diagram is an equalizer exactly when `𝒪_{X'}(W)` maps bijectively onto the equalizer of
  `p₀_* 𝒪 ⇉ p₁_* 𝒪` over `W`.
* `AlgebraicGeometry.Space.ChartGlobalFunctionsEqualizer.of_hom`: the equalizer property passes
  from an affine chart to the affine charts above it.

## Implementation notes

The three rings are identified with the sections over `W` of `𝒪_{X'}`, `p₀_* 𝒪_{C₀}` and
`p₁_* 𝒪_{C₁}` (`AlgebraicGeometry.Space.directImageSectionsGlobalFunctionsEquiv`), naturally in
the morphisms (`AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions_pushforwardAlgebraMap`
and `AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions_algebraMap_eq`).  The equalizer
of `p₀_* 𝒪 ⇉ p₁_* 𝒪` is a quasi-coherent algebra (Stacks 03M1, Stacks 03M9), so the comparison
`𝒪_{X'} ⟶ Eq` is a morphism of modules cartesian on affine charts, and bijectivity of such a
morphism on the sections over an affine chart passes to the affine charts above it
(`AlgebraicGeometry.Space.bijective_val_app_of_bijective_of_cartesian`).

## References

* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Equalizer diagrams of functions -/

/-- **Equalizer diagrams of functions transfer along bijections.**  If `ι, φ, ψ` and `ι', φ', ψ'`
are related by bijections `eR, eA` and an injection `eQ` commuting with them, then `ι` is an
injection onto the equalizer of `φ, ψ` exactly when `ι'` is one onto the equalizer of
`φ', ψ'`. -/
theorem isEqualizerDiagram_iff_of_bijective {R A Q R' A' Q' : Type*} (ι : R → A) (φ ψ : A → Q)
    (ι' : R' → A') (φ' ψ' : A' → Q') (eR : R → R') (eA : A → A') (eQ : Q → Q')
    (hR : Function.Bijective eR) (hA : Function.Bijective eA) (hQ : Function.Injective eQ)
    (h₁ : ∀ r, eA (ι r) = ι' (eR r)) (h₂ : ∀ a, eQ (φ a) = φ' (eA a))
    (h₃ : ∀ a, eQ (ψ a) = ψ' (eA a)) :
    (Function.Injective ι ∧ ∀ a, φ a = ψ a → ∃ r, ι r = a) ↔
      (Function.Injective ι' ∧ ∀ a, φ' a = ψ' a → ∃ r, ι' r = a) := by
  constructor
  · rintro ⟨hι, hex⟩
    refine ⟨fun x y hxy => ?_, fun a ha => ?_⟩
    · obtain ⟨x, rfl⟩ := hR.2 x
      obtain ⟨y, rfl⟩ := hR.2 y
      rw [← h₁, ← h₁] at hxy
      exact congrArg eR (hι (hA.1 hxy))
    · obtain ⟨a, rfl⟩ := hA.2 a
      obtain ⟨r, hr⟩ := hex a (hQ (by rw [h₂, h₃, ha]))
      exact ⟨eR r, by rw [← h₁, hr]⟩
  · rintro ⟨hι, hex⟩
    refine ⟨fun x y hxy => hR.1 (hι ?_), fun a ha => ?_⟩
    · rw [← h₁, ← h₁, hxy]
    · obtain ⟨r', hr'⟩ := hex (eA a) (by rw [← h₂, ← h₃, ha])
      obtain ⟨r, rfl⟩ := hR.2 r'
      exact ⟨r, hA.1 (by rw [h₁, hr'])⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pulling back global functions along a morphism commutes with the inverses of the
pullback isomorphisms of a commuting square. -/
private theorem globalFunctionsMapEquiv_symm_globalFunctionsMap
    {P Q P' Q' : AlgebraicSpaces B S hS} {k : P ⟶ Q} {k' : P' ⟶ Q'} (eQ : Q ≅ Q') (eP : P ≅ P')
    (hk : k ≫ eQ.hom = eP.hom ≫ k') (x : globalFunctions' B S hS Q.1) :
    (globalFunctionsMapEquiv B S hS eP).symm (globalFunctionsMap B S hS k x) =
      globalFunctionsMap B S hS k' ((globalFunctionsMapEquiv B S hS eQ).symm x) := by
  have hcomp : ∀ y, globalFunctionsMapEquiv B S hS eP (globalFunctionsMap B S hS k' y) =
      globalFunctionsMap B S hS (eP.hom ≫ k') y := fun y => by
    rw [globalFunctionsMap_comp]
    rfl
  apply (globalFunctionsMapEquiv B S hS eP).injective
  rw [RingEquiv.apply_symm_apply, hcomp, ← hk, globalFunctionsMap_comp, RingHom.comp_apply]
  exact congrArg _ ((globalFunctionsMapEquiv B S hS eQ).apply_symm_apply x).symm

/-- **The equalizer property of global functions is invariant under isomorphisms of
diagrams.** -/
theorem GlobalFunctionsEqualizer.of_iso {U E₀ E₁ U' E₀' E₁' : AlgebraicSpaces B S hS}
    {q : E₀ ⟶ U} {d₀ d₁ : E₁ ⟶ E₀} {q' : E₀' ⟶ U'} {d₀' d₁' : E₁' ⟶ E₀'}
    (eU : U ≅ U') (e₀ : E₀ ≅ E₀') (e₁ : E₁ ≅ E₁') (hq : q ≫ eU.hom = e₀.hom ≫ q')
    (hd₀ : d₀ ≫ e₀.hom = e₁.hom ≫ d₀') (hd₁ : d₁ ≫ e₀.hom = e₁.hom ≫ d₁')
    (h : GlobalFunctionsEqualizer q' d₀' d₁') : GlobalFunctionsEqualizer q d₀ d₁ := by
  unfold GlobalFunctionsEqualizer at h ⊢
  exact (isEqualizerDiagram_iff_of_bijective (globalFunctionsMap B S hS q)
    (globalFunctionsMap B S hS d₀) (globalFunctionsMap B S hS d₁) (globalFunctionsMap B S hS q')
    (globalFunctionsMap B S hS d₀') (globalFunctionsMap B S hS d₁')
    (globalFunctionsMapEquiv B S hS eU).symm (globalFunctionsMapEquiv B S hS e₀).symm
    (globalFunctionsMapEquiv B S hS e₁).symm
    (globalFunctionsMapEquiv B S hS eU).symm.bijective
    (globalFunctionsMapEquiv B S hS e₀).symm.bijective
    (globalFunctionsMapEquiv B S hS e₁).symm.injective
    (globalFunctionsMapEquiv_symm_globalFunctionsMap eU e₀ hq)
    (globalFunctionsMapEquiv_symm_globalFunctionsMap e₀ e₁ hd₀)
    (globalFunctionsMapEquiv_symm_globalFunctionsMap e₀ e₁ hd₁)).2 h

/-! ### The equalizer over a chart of the base -/

section Chart

variable {X' C₀ C₁ : AlgebraicSpaces B S hS} {p₀ : C₀ ⟶ X'} {p₁ : C₁ ⟶ X'}
  (δ₀ δ₁ : Over.mk p₁ ⟶ Over.mk p₀)

/-- **`Γ(W) ⟶ Γ(C₀ ×_{X'} W) ⇉ Γ(C₁ ×_{X'} W)` is an equalizer** at an étale chart `W` of `X'`,
the two maps being pullback along the morphisms induced by `δ₀, δ₁`. -/
def ChartGlobalFunctionsEqualizer (W : SmallEtale B S hS X'.1) : Prop :=
  GlobalFunctionsEqualizer (chartBaseChangeProjection B S hS p₀ W)
    (chartBaseChangeSpaceMap B S hS δ₀.left (Over.w δ₀) W)
    (chartBaseChangeSpaceMap B S hS δ₁.left (Over.w δ₁) W)

/-- The comparison `𝒪_{X'} ⟶ Eq(p₀_* 𝒪 ⇉ p₁_* 𝒪)`, as a morphism of `𝒪_{X'}`-modules. -/
abbrev chartEqualizerComparison :
    AlgebraSheaf.underlyingModule (unitAlgebra B S hS X') ⟶
      AlgebraSheaf.underlyingModule (AlgebraSheaf.equalizerAlgebra
        (pushforwardAlgebraMap B S hS δ₀) (pushforwardAlgebraMap B S hS δ₁)) :=
  AlgebraSheaf.underlyingModuleMap (unitAlgebraHom B S hS X' _)

/-- On sections, the comparison `𝒪_{X'} ⟶ Eq(p₀_* 𝒪 ⇉ p₁_* 𝒪)` is the structure-algebra map
of the equalizer. -/
theorem bijective_chartEqualizerComparison_iff_algebraMap (W : SmallEtale B S hS X'.1) :
    Function.Bijective ((chartEqualizerComparison δ₀ δ₁).val.app (op W)) ↔
      Function.Bijective ((AlgebraSheaf.equalizerAlgebra (pushforwardAlgebraMap B S hS δ₀)
        (pushforwardAlgebraMap B S hS δ₁)).algebraMap (op W)) :=
  Iff.rfl

/-- The comparison `𝒪_{X'} ⟶ Eq(p₀_* 𝒪 ⇉ p₁_* 𝒪)` is bijective on the sections over `W` exactly
when the structure-algebra map of `p₀_* 𝒪` over `W` is injective with image the equalizer of
the two direct-image maps. -/
theorem bijective_chartEqualizerComparison_iff (W : SmallEtale B S hS X'.1) :
    Function.Bijective ((chartEqualizerComparison δ₀ δ₁).val.app (op W)) ↔
      (Function.Injective ((pushforwardAlgebra B S hS (Over.mk p₀)).algebraMap (op W)) ∧
        ∀ a, ((pushforwardAlgebraMap B S hS δ₀).right.hom.app (op W)).hom a =
            ((pushforwardAlgebraMap B S hS δ₁).right.hom.app (op W)).hom a →
          ∃ r, (pushforwardAlgebra B S hS (Over.mk p₀)).algebraMap (op W) r = a) := by
  rw [bijective_chartEqualizerComparison_iff_algebraMap]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun x y hxy => hinj (Subtype.ext hxy), fun a ha => ?_⟩
    obtain ⟨r, hr⟩ := hsurj ⟨a, ha⟩
    exact ⟨r, congrArg Subtype.val hr⟩
  · rintro ⟨hinj, hex⟩
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun y => ?_⟩
    obtain ⟨r, hr⟩ := hex y.1 y.2
    exact ⟨r, Subtype.ext hr⟩

/-- At a chart, the diagram of global functions is an equalizer exactly when the
structure-algebra map of `p₀_* 𝒪` over `W` is injective with image the equalizer of the two
direct-image maps. -/
theorem chartGlobalFunctionsEqualizer_iff (W : SmallEtale B S hS X'.1) :
    ChartGlobalFunctionsEqualizer δ₀ δ₁ W ↔
      (Function.Injective ((pushforwardAlgebra B S hS (Over.mk p₀)).algebraMap (op W)) ∧
        ∀ a, ((pushforwardAlgebraMap B S hS δ₀).right.hom.app (op W)).hom a =
            ((pushforwardAlgebraMap B S hS δ₁).right.hom.app (op W)).hom a →
          ∃ r, (pushforwardAlgebra B S hS (Over.mk p₀)).algebraMap (op W) r = a) := by
  unfold ChartGlobalFunctionsEqualizer GlobalFunctionsEqualizer
  exact (isEqualizerDiagram_iff_of_bijective _ _ _ _ _ _
    (comparisonGlobalFunctionsRingEquiv B S hS X' W).symm
    (directImageSectionsToGlobalFunctions B S hS p₀ W)
    (directImageSectionsToGlobalFunctions B S hS p₁ W)
    (comparisonGlobalFunctionsRingEquiv B S hS X' W).symm.bijective
    (bijective_directImageSectionsToGlobalFunctions B S hS p₀ W)
    (injective_directImageSectionsToGlobalFunctions B S hS p₁ W)
    (directImageSectionsToGlobalFunctions_algebraMap_eq B S hS W)
    (directImageSectionsToGlobalFunctions_pushforwardAlgebraMap B S hS δ₀ W)
    (directImageSectionsToGlobalFunctions_pushforwardAlgebraMap B S hS δ₁ W)).symm

/-- **At a chart, the diagram of global functions is an equalizer exactly when the comparison
`𝒪_{X'} ⟶ Eq(p₀_* 𝒪 ⇉ p₁_* 𝒪)` is bijective on sections.** -/
theorem chartGlobalFunctionsEqualizer_iff_bijective (W : SmallEtale B S hS X'.1) :
    ChartGlobalFunctionsEqualizer δ₀ δ₁ W ↔
      Function.Bijective ((chartEqualizerComparison δ₀ δ₁).val.app (op W)) :=
  (chartGlobalFunctionsEqualizer_iff δ₀ δ₁ W).trans
    (bijective_chartEqualizerComparison_iff δ₀ δ₁ W).symm

/-- **The equalizer of global functions passes from an affine chart to the affine charts above
it**, for quasi-compact and quasi-separated `p₀, p₁`: the comparison
`𝒪_{X'} ⟶ Eq(p₀_* 𝒪 ⇉ p₁_* 𝒪)` is a morphism of quasi-coherent modules (Stacks 03M9 for the
direct images, Stacks 03M1 for the equalizer), so bijectivity on the sections over an affine chart
passes to the affine charts above it (Stacks 03DX). -/
theorem ChartGlobalFunctionsEqualizer.of_hom (hqc₀ : IsQuasiCompact B S hS p₀.hom)
    (hqs₀ : IsQuasiSeparated B S hS p₀.hom) (hqc₁ : IsQuasiCompact B S hS p₁.hom)
    (hqs₁ : IsQuasiSeparated B S hS p₁.hom) {W W' : SmallEtale B S hS X'.1}
    (hW : IsAffine (chartScheme W)) (hW' : IsAffine (chartScheme W')) (f : W' ⟶ W)
    (h : ChartGlobalFunctionsEqualizer δ₀ δ₁ W) : ChartGlobalFunctionsEqualizer δ₀ δ₁ W' := by
  rw [chartGlobalFunctionsEqualizer_iff_bijective] at h ⊢
  have hE := AlgebraSheaf.isQuasicoherent_equalizerAlgebra (pushforwardAlgebraMap B S hS δ₀)
    (pushforwardAlgebraMap B S hS δ₁)
    (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS p₀ hqc₀ hqs₀)
    (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS p₁ hqc₁ hqs₁)
  exact bijective_val_app_of_bijective_of_cartesian B S hS X'.1 X'.2
    (chartEqualizerComparison δ₀ δ₁)
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X'.1 X'.2 _
      (isQuasicoherent_unitAlgebra B S hS X'))
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X'.1 X'.2 _ hE) hW hW' f h

end Chart

end AlgebraicGeometry.Space

end
