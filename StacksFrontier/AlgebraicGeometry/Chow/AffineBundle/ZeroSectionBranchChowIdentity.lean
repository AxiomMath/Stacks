module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionBranchFinalCycle
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchSupPresentation
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowPrimeCycleNotContained

/-!
# Tag 0F98

In the situation of [Stacks, Tag 0F97] the diagram

  `D₁ --i₁--> L`,  `p : L ⟶ Y`,  `p₁ : D₁ ⟶ D`,  `i : D ⟶ Y`

gives two maps `A_{k+1}(Y) ⟶ A_{k+1}(D₁)`, and [Stacks, Tag 0F98] asserts that they agree:

  `i₁^* ∘ p^* = p₁^* ∘ i^*`.

This file proves it, for an **arbitrary** diagram `R` as in [Stacks, Tag 0F97], read at
`R.normalize`; the base-change clause of [Stacks, Tag 0F99] needs it for the base change of a
diagram, which is a diagram but not the constructed one. The reduction to a prime cycle `[W]` for
`W ⊆ Y` integral of δ-dimension `k+1` is `gysinChowBranch₁_flatPullbackChowProj_of_primeCycle`;
the case `W ⊄ D` is `leftRule_cycle_eq_rightRule_cycle_of_not_le`, an equality of cycles; and the
case `W ⊆ D` is `leftRule_cycle_sub_rightRule_cycle_isRationallyEquivalentToZeroWithin_of_le`,
whose branch and restriction hypotheses are discharged here. All names are in the namespace
`Stacks.Chow.TensorZeroScheme`.

## Main results

* `leftRule_cycle_sub_rightRule_cycle_isRationallyEquivalentToZeroWithin`: the case `W ⊆ D` at
  the source's own hypotheses.
* `gysinChowBranch₁_flatPullbackChowProj`: [Stacks, Tag 0F98].

## Implementation notes

### `k+2` against `k+1+1`

The Gysin rule of `i₁` is an `Stacks.Chow.IntegralComponentRule` at `k+1`, so the δ-dimension it
demands of a component is the term `k+1+1`, while
`Stacks.Chow.TensorZeroScheme.schemeDeltaDimension_sup_comap_proj_of_le` supplies the same integer
written `k+2`. The two are interchangeable only through a rewrite, and
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowPrimeCycleContained` deliberately leaves
that conversion to its consumer. It is done here, once, by `congrArg` at the coercion `ℤ → EInt`
applied to `(k + 2 : ℤ) = k + 1 + 1`: the conversion is an equality of integers inside the
coercion, not a transport of the δ-dimension itself.

### The transparency barrier at the bundle's base

The structure morphism of the base of the branch bundle over `W` is instantiated here at
`δ ≫ (i ≫ sY)`, a morphism whose source is spelled as the zero scheme of the restricted section
while the statements it is fed to type it at `(branchSituation …).X`. The two agree only at
default transparency and instance search matches syntactically, so the two instances that cross —
`LocallyOfFiniteType` of that composite and the integrality of the base — are supplied by hand,
their defeq discharged once by the elaborator's check of an ascribed type. Nothing is rewritten.

### Why the two deductions about the restriction of `W` to `D` go through isomorphisms

`W|_D` is isomorphic to the restricted divisor `D'` (`zeroIdealBaseChangeIsoComap`), and `D'` is
integral of the right δ-dimension by `isIntegral_zeroIdeal_pullbackTensorSection_subscheme_of_le`
and `schemeDeltaDimension_zeroIdeal_comap_of_le`. Integrality transports along the isomorphism by
`AlgebraicGeometry.IsIntegral.of_isIso` and δ-dimension by
`Stacks.Chow.schemeDeltaDimension_comp_iso`; neither eliminates an equation into a type.

## References

* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

namespace Stacks.Chow.TensorZeroScheme

attribute [local instance] Stacks.LineBundle.Situation.flat_totalSpaceToBase
  isClosedImmersion_zeroIdealBaseChangeMap_subschemeι

variable (C : Stacks.Chow.ChowSituation.{u}) (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (k : ℤ)

include h₁ h₂ in
/-- For `W ⊆ Y` an integral closed subscheme of δ-dimension `k+1` contained in the divisor
`D = Z(s)`, the two cycles `i₁^*p^*[W]` and `p₁^*i^*[W]` differ by a cycle rationally equivalent
to zero on `D₁` witnessed inside the preimage of `W`. -/
theorem leftRule_cycle_sub_rightRule_cycle_isRationallyEquivalentToZeroWithin
    (W : Y.IdealSheafData) (hWint : IsIntegral W.subscheme)
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hW : zeroIdeal Y L₁ L₂ s ≤ W) :
    Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
      ((leftRule C Y L₁ L₂ s R sY k).cycle W hWint hDim -
        (rightRule C Y L₁ L₂ s R sY k).cycle W hWint hDim)
      ((R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y)) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.sheaf.obj
      W.subscheme.ringCatSheaf.property ((Scheme.Modules.pullback W.subschemeι).obj L₂) :=
    Stacks.Divisors.pullback_isInvertible _ _
  have hsDft : @LocallyOfFiniteType
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X C.S
      (zeroIdealBaseChangeMap s W.subschemeι ≫ ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)) :=
    inferInstanceAs (LocallyOfFiniteType
      (zeroIdealBaseChangeMap s W.subschemeι ≫ ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)))
  have hW₁int := isIntegral_sup_comap_proj_of_le L₁ L₂ s R W hW
  have hk := congrArg (fun n : ℤ ↦ ((n : EInt))) (show (k + 2 : ℤ) = k + 1 + 1 by lia)
  have hW₁dim := (schemeDeltaDimension_sup_comap_proj_of_le L₁ L₂ s R W C sY k hW hDim).trans hk
  have hW₂int := isIntegral_sup_comap_proj₂_of_le L₁ L₂ s R W hW
  have hW₂dim := (schemeDeltaDimension_sup_comap_proj₂_of_le L₁ L₂ s R W C sY k hW hDim).trans hk
  have := isIntegral_zeroIdeal_pullbackTensorSection_subscheme_of_le L₁ L₂ s W hW
  have hWDdim : Stacks.Chow.schemeDeltaDimension C
      ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι ≫
        (zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt) :=
    (schemeDeltaDimension_comap_comm C sY (zeroIdeal Y L₁ L₂ s) W).trans
      ((congrArg (fun I : W.subscheme.IdealSheafData ↦
          Stacks.Chow.schemeDeltaDimension C (I.subschemeι ≫ W.subschemeι ≫ sY))
        (comap_zeroIdeal s W.subschemeι)).trans
        (schemeDeltaDimension_zeroIdeal_comap_of_le L₁ L₂ s W C sY k hW hDim))
  have hVint : IsIntegral
      ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).comap R.normalize.p₁).subscheme := by
    rw [← comap_comap_proj_branch₁_eq Y L₁ L₂ s R W]
    exact IsIntegral.of_isIso
      (Scheme.IdealSheafData.supComapSubschemeIso R.normalize.D₁
        (W.comap R.normalize.p)).hom
  have hVdim : Stacks.Chow.schemeDeltaDimension C
      (((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).comap R.normalize.p₁).subschemeι ≫
        R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) = ((k + 1 + 1 : ℤ) : EInt) := by
    rw [← comap_comap_proj_branch₁_eq Y L₁ L₂ s R W]
    have hfac : (R.normalize.D₁ ⊔ W.comap R.normalize.p).subschemeι ≫
          R.normalize.p ≫ sY =
        (Scheme.IdealSheafData.supComapSubschemeIso R.normalize.D₁
            (W.comap R.normalize.p)).hom ≫
          (((W.comap R.normalize.p).comap R.normalize.D₁.subschemeι).subschemeι ≫
            R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) := by
      simp only [← Category.assoc, Scheme.IdealSheafData.supComapSubschemeIso_hom_subschemeι,
        Scheme.IdealSheafData.inclusion_subschemeι]
    exact (Stacks.Chow.schemeDeltaDimension_comp_iso C _ _).symm.trans
      ((Stacks.Chow.schemeDeltaDimension_congr C hfac).symm.trans hW₁dim)
  have : IsIso (⊥ : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2 rfl
  have : IsIntegral (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X :=
    isIntegral_branchSituation_X_of_le L₁ L₂ s W
      ((Scheme.Modules.pullback W.subschemeι).obj L₂) hW
  have hbotInt : IsIntegral (⊥ : (branchSituation W.subscheme
      ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subscheme :=
    IsIntegral.of_isIso (asIso (⊥ : (branchSituation W.subscheme
      ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι).inv
  have hsDeq : zeroIdealBaseChangeMap s W.subschemeι ≫
        ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) =
      (zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι ≫ W.subschemeι ≫ sY := by
    rw [← Category.assoc, zeroIdealBaseChangeMap_comp_subschemeι, Category.assoc]
  have hbotDim : Stacks.Chow.schemeDeltaDimension C
      ((⊥ : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫
        (zeroIdealBaseChangeMap s W.subschemeι ≫
          ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY))) = ((k + 1 : ℤ) : EInt) :=
    (Stacks.Chow.schemeDeltaDimension_comp_iso C
      (asIso (⊥ : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι) _).trans
      ((Stacks.Chow.schemeDeltaDimension_congr C hsDeq).trans
        (schemeDeltaDimension_zeroIdeal_comap_of_le L₁ L₂ s W C sY k hW hDim))
  exact leftRule_cycle_sub_rightRule_cycle_isRationallyEquivalentToZeroWithin_of_le
    L₁ L₂ s R W C sY
    (zeroIdealBaseChangeMap s W.subschemeι ≫ ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)) rfl k
    hWint hDim hW hW₁int hW₁dim hW₂int hW₂dim
    (not_branch₁_le_branch₂_sup_comap_proj_of_le L₁ L₂ s R W C sY k hW hDim) hbotInt hbotDim
    (IsIntegral.of_isIso (zeroIdealBaseChangeIsoComap L₁ L₂ s W).inv) hWDdim hVint hVdim

include h₁ h₂ in
/-- In the situation of [Stacks, Tag 0F97],

  `i₁^* p^* α = p₁^* i^* α`  in  `A_{k+1}(D₁)`  for every  `α ∈ A_{k+1}(Y)`. -/
@[stacks 0F98]
theorem gysinChowBranch₁_flatPullbackChowProj (α : Stacks.Chow.chowGroup C sY (k + 1)) :
    gysinChowBranch₁ C Y L₁ L₂ s R sY (k + 1)
        (flatPullbackChowProj C Y L₁ L₂ s R sY (k + 1) α) =
      flatPullbackChowProj₁ C Y L₁ L₂ s R sY k (gysinChowZeroIdeal C Y L₁ L₂ s sY k α) :=
  gysinChowBranch₁_flatPullbackChowProj_of_primeCycle C Y L₁ L₂ s R sY k
    (fun W hWint hDim ↦ by
      by_cases hle : zeroIdeal Y L₁ L₂ s ≤ W
      · exact leftRule_cycle_sub_rightRule_cycle_isRationallyEquivalentToZeroWithin
          C Y L₁ L₂ s R sY k W hWint hDim hle
      · rw [leftRule_cycle_eq_rightRule_cycle_of_not_le C Y L₁ L₂ s R sY k W hWint hDim hle,
          sub_self]
        exact Stacks.Chow.isRationallyEquivalentToZeroWithin_zero C
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1) _) α

end Stacks.Chow.TensorZeroScheme

end
