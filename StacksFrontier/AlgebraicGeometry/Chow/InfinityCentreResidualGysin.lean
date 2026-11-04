module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreResidualDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestrictionVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardPulledBackModule
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDifferencePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.CompletedClassFundamental

/-!
# The Gysin map at infinity on the residual divisor

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` with `dim_δ(X) ≤ k + 1`, and let `Z ⊆ Y ⊆ X` be closed subschemes with ideals
`ℐ_Y ⊆ ℐ_Z`, where `Y` is an effective Cartier divisor. Let `W_Z` be the blowup at infinity of
Stacks 0FBG in the centre `∞(Z)`, with fibre at infinity `W_{Z,∞}` and strict transform `X'_Z`, and
let `V = W_Z ∖ X'_Z`. On `V` live two invertible modules with global sections:

* `𝒪(D_∞)` pulled back from `𝐏¹_X`, whose zero scheme is `W_{Z,∞} ∩ V`;
* `𝒪(𝒟_Y)` pulled back along the change of centre `ρ : V ⟶ W_Y`, where `𝒟_Y` is the residual
  divisor of `ℐ_Y · 𝒪_{W_Y}`; its zero scheme is the residual zero scheme
  `Z₂ = V(𝒟_Z) ∩ V`, an effective Cartier divisor on `V`.

The proof of Stacks 0FEB applies Stacks 0B73 to these two sections on `[V]_{k+2}`. This file
computes the composite in which the residual section comes first:

* the Gysin map of the residual section carries `[V]_{k+2}` to `[Z₂]_{k+1}` (Stacks 02TB);
* the strict transform `T = W_{Z ∩ Y} ∖ X''` of `𝐏¹_Y` lies in `Z₂`, and off `W_{Z,∞}` the two
  are the same closed subscheme of `V` (both are cut out by `ℐ_Y · 𝒪` there). So
  `[Z₂]_{k+1}` and `u_*[T]_{k+1}` agree off `D = W_{Z,∞} ∩ Z₂`, where `𝒪(D_∞)` is trivial, and
  the Gysin map of `𝒪(D_∞)` does not distinguish them (Remark 0B6Z);
* the Gysin map of `𝒪(D_∞)` commutes with `u_*` (Stacks 02TA), and carries `[T]_{k+1}` to the
  fundamental class of the fibre at infinity `D'' = W_{Z ∩ Y, ∞} ∩ T` (Stacks 02TB);
* `D''` is the normal cone `C_ZY` (Stacks 0FBH).

Hence `(1_{D_∞})^*(1_{𝒟_Y})^*[V]_{k+2} = κ_*[C_ZY]_k` for the inclusion `κ : C_ZY ⟶ D`.

## Main definitions

* `Stacks.Chow.residualZeroSchemeAtInfinity` — the residual zero scheme `Z₂ ⊆ W_Z ∖ X'_Z`.
* `Stacks.Chow.strictTransformToResidualZeroScheme` — the closed immersion
  `u : W_{Z ∩ Y} ∖ X'' ⟶ Z₂`.
* `Stacks.Chow.residualFibreAtInfinity` and `Stacks.Chow.strictTransformFibreAtInfinity` — the
  zero schemes `D ⊆ Z₂` and `D'' ⊆ W_{Z ∩ Y} ∖ X''` of the section at infinity.
* `Stacks.Chow.normalConeIsoFibreAtInfinityCompl` — `C_ZX ≅ W_∞ ∩ (W ∖ X')`, and
  `Stacks.Chow.normalConeIsoStrictTransformFibreAtInfinity` — `C_ZY ≅ D''`.
* `Stacks.Chow.normalConeToResidualFibreAtInfinity` — the closed immersion `κ : C_ZY ⟶ D`.

## Main results

* `Stacks.Chow.schemeDeltaDimension_strictTransformComplAtInfinity_le` and
  `Stacks.Chow.schemeDeltaDimension_strictTransformComplAtInfinity_le_of_isEffectiveCartierDivisor`
  — `dim_δ(W_Z ∖ X'_Z) ≤ n + 1` and `dim_δ(W_{Z ∩ Y} ∖ X'') ≤ n` when `dim_δ(X) ≤ n`.
* `Stacks.Chow.gysinSystemOfInvertible_residualModuleAtInfinity_fundamentalChowClass` —
  `(1_{𝒟_Y})^*[V]_{n+1} = [Z₂]_n`.
* `Stacks.Chow.gysinHomomorphismOfInvertible_eq_of_eq_off_zeroScheme` — Remark 0B6Z: when `L` is
  trivial on `Z(s)`, the Gysin map of `s` only sees a cycle off `Z(s)`.
* `Stacks.Chow.gysinSystemOfInvertible_lineInfinityModule_residualZeroSchemeAtInfinity` —
  `(1_{D_∞})^*[Z₂]_{k+1} = j_*[D'']_k`.
* `Stacks.Chow.gysinSystemOfInvertible_lineInfinityModule_comp_residualModuleAtInfinity`
  — the same composite on `[V]_{k+2}`, in the form of
  `Stacks.Chow.gysinSystemOfInvertible_comm_properPushforward`.
* `Stacks.Chow.gysinSystemOfInvertible_lineInfinityModule_residualZeroScheme_eq_normalCone`
  — `(1_{D_∞})^*[Z₂]_{k+1} = κ_*[C_ZY]_k`.

## Implementation notes

No integrality of `X` is needed: the Cartier property of `𝒟_Z` and of the fibres at infinity, and
the dimension bounds, hold for any `X` locally of finite type over `S`. The proper morphism of zero
schemes along which the result is pushed forward is taken as a hypothesis, compatible with the
inclusions, as in Stacks 02TA
(`Stacks.Chow.gysinSystemOfInvertible_properPushforward_pullbackModule`); the canonical choices are
`Stacks.Chow.strictTransformFibreToResidualFibre` and
`Stacks.Chow.normalConeToResidualFibreAtInfinity`.

## References

* [Stacks Project, Tag 0FEB](https://stacks.math.columbia.edu/tag/0FEB)
* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02TB](https://stacks.math.columbia.edu/tag/02TB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor

/-! ### Dimension bounds -/

section Dimension

/-- The blowup at infinity of a scheme locally of finite type over a locally Noetherian base is
locally of finite type over that base. -/
instance locallyOfFiniteType_blowupAtInfinityToBase_comp {S X : Scheme.{u}}
    [IsLocallyNoetherian S] (sX : X ⟶ S) [LocallyOfFiniteType sX] (ℐ : X.IdealSheafData) :
    LocallyOfFiniteType (blowupAtInfinityToBase ℐ ≫ sX) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  infer_instance

variable (C : ChowSituation.{u})

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **`dim_δ(W) ≤ n + 1` for the blowup at infinity `W` of Stacks 0FBG** when `dim_δ(X) ≤ n`. -/
theorem schemeDeltaDimension_blowupAtInfinity_le (ℐ : X.IdealSheafData) {n : ℤ}
    (hX : schemeDeltaDimension C sX ≤ (n : EInt)) :
    schemeDeltaDimension C (blowupAtInfinityToBase ℐ ≫ sX) ≤ ((n + 1 : ℤ) : EInt) := by
  set b := blowupAtInfinityToProjectiveLineProduct ℐ sX
  have h := schemeDeltaDimension_modificationBaseChange_le C sX b
    (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct ℐ sX) (𝟙 X) n (by simpa using hX)
    (isEffectiveCartierDivisor_ker_modificationInfinityBaseChange_blowupAtInfinity ℐ sX (𝟙 X))
  have e : blowupAtInfinityToBase ℐ ≫ sX = modificationProjection sX b ≫ sX := by
    rw [modificationProjection_blowupAtInfinityToProjectiveLineProduct]
  rwa [schemeDeltaDimension_congr C e, ← schemeDeltaDimension_comp_iso C
    (asIso (pullback.fst (modificationProjection sX b) (𝟙 X)))]

/-- **`dim_δ(W ∖ X') ≤ n + 1`** for the open complement of the strict transform in the blowup at
infinity, when `dim_δ(X) ≤ n`. -/
theorem schemeDeltaDimension_strictTransformComplAtInfinity_le (ℐ : X.IdealSheafData) {n : ℤ}
    (hX : schemeDeltaDimension C sX ≤ (n : EInt)) :
    schemeDeltaDimension C
        ((strictTransformComplAtInfinity ℐ).ι ≫ blowupAtInfinityToBase ℐ ≫ sX) ≤
      ((n + 1 : ℤ) : EInt) :=
  schemeDeltaDimension_comp_isOpenImmersion_le C _ _
    (schemeDeltaDimension_blowupAtInfinity_le C sX ℐ hX)

/-- **`dim_δ(W' ∖ X'') ≤ n` for the blowup at infinity `W'` of an effective Cartier divisor
`Y ⊆ X`** when `dim_δ(X) ≤ n`. -/
theorem schemeDeltaDimension_strictTransformComplAtInfinity_le_of_isEffectiveCartierDivisor
    {Y : Scheme.{u}} (iY : Y ⟶ X) [IsClosedImmersion iY]
    (hY : Stacks.Divisors.IsEffectiveCartierDivisor iY.ker) (ℐ' : Y.IdealSheafData) {n : ℤ}
    (hX : schemeDeltaDimension C sX ≤ (n : EInt)) :
    schemeDeltaDimension C
        ((strictTransformComplAtInfinity ℐ').ι ≫ blowupAtInfinityToBase ℐ' ≫ iY ≫ sX) ≤
      (n : EInt) := by
  have hY' : schemeDeltaDimension C (iY ≫ sX) ≤ ((n - 1 : ℤ) : EInt) :=
    schemeDeltaDimension_le_of_genericPoints_notMem_range C sX iY
      (fun x hx => notMem_range_of_mem_genericPoints_of_isEffectiveCartierDivisor iY hY hx)
      (by rwa [sub_add_cancel])
  have h := schemeDeltaDimension_strictTransformComplAtInfinity_le C (iY ≫ sX) ℐ' hY'
  rwa [sub_add_cancel] at h

end Dimension

/-! ### The comparison `W' ∖ X̃' ⟶ W ∖ X̃` -/

section StrictTransform

variable {X X' : Scheme.{u}} (f : X' ⟶ X) (ℐ : X.IdealSheafData) (ℐ' : X'.IdealSheafData)
  (hℐ' : ℐ' = ℐ.comap f)

/-- **The comparison `W' ∖ X̃' ⟶ W ∖ X̃`** of the open complements of the strict transforms, the
restriction of the comparison `W' ⟶ W` of the blowups at infinity, which carries `W' ∖ X̃'` onto
the inverse image of `W ∖ X̃`. -/
def strictTransformComplAtInfinityComap :
    (strictTransformComplAtInfinity ℐ').toScheme ⟶ (strictTransformComplAtInfinity ℐ).toScheme :=
  ((blowupAtInfinity ℐ').isoOfEq
      (preimage_strictTransformComplAtInfinity_blowupAtInfinityComap f ℐ ℐ' hℐ')).inv ≫
    (blowupAtInfinityComap f ℐ ℐ' hℐ' ∣_ strictTransformComplAtInfinity ℐ)

/-- The comparison `W' ∖ X̃' ⟶ W ∖ X̃` followed by the inclusion of `W ∖ X̃` is the inclusion of
`W' ∖ X̃'` followed by the comparison `W' ⟶ W`. -/
@[reassoc (attr := simp)]
theorem strictTransformComplAtInfinityComap_ι :
    strictTransformComplAtInfinityComap f ℐ ℐ' hℐ' ≫ (strictTransformComplAtInfinity ℐ).ι =
      (strictTransformComplAtInfinity ℐ').ι ≫ blowupAtInfinityComap f ℐ ℐ' hℐ' := by
  rw [strictTransformComplAtInfinityComap, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, Scheme.isoOfEq_inv_ι]

/-- The comparison `W' ∖ X̃' ⟶ W ∖ X̃` lies over `X' ⟶ X`. -/
@[reassoc]
theorem strictTransformComplAtInfinityComap_toBase :
    strictTransformComplAtInfinityComap f ℐ ℐ' hℐ' ≫ (strictTransformComplAtInfinity ℐ).ι ≫
        blowupAtInfinityToBase ℐ =
      (strictTransformComplAtInfinity ℐ').ι ≫ blowupAtInfinityToBase ℐ' ≫ f := by
  rw [strictTransformComplAtInfinityComap_ι_assoc, blowupAtInfinityComap_toBase]

/-- The comparison `W' ∖ X̃' ⟶ W ∖ X̃` lies over `𝐏¹_{X'} ⟶ 𝐏¹_X`. -/
@[reassoc]
theorem strictTransformComplAtInfinityComap_toLine :
    strictTransformComplAtInfinityComap f ℐ ℐ' hℐ' ≫ (strictTransformComplAtInfinity ℐ).ι ≫
        blowupAtInfinityToLine ℐ =
      (strictTransformComplAtInfinity ℐ').ι ≫ blowupAtInfinityToLine ℐ' ≫
        projectiveLineBaseChange f := by
  rw [strictTransformComplAtInfinityComap_ι_assoc, blowupAtInfinityComap_comp]

/-- If `f` is a closed immersion, so is the comparison `W' ∖ X̃' ⟶ W ∖ X̃`. -/
instance [IsClosedImmersion f] :
    IsClosedImmersion (strictTransformComplAtInfinityComap f ℐ ℐ' hℐ') := by
  rw [strictTransformComplAtInfinityComap]
  infer_instance

/-- The ideal of `W' ∖ X̃' ⟶ W ∖ X̃` is the ideal of `W' ⟶ W` restricted to `W ∖ X̃`. -/
theorem ker_strictTransformComplAtInfinityComap [IsClosedImmersion f] :
    (strictTransformComplAtInfinityComap f ℐ ℐ' hℐ').ker =
      (blowupAtInfinityComap f ℐ ℐ' hℐ').ker.comap (strictTransformComplAtInfinity ℐ).ι := by
  rw [strictTransformComplAtInfinityComap, Scheme.Hom.ker_comp_of_isIso,
    ker_morphismRestrict_eq_comap]

end StrictTransform

/-! ### The residual zero scheme on `W_Z ∖ X'_Z` -/

section ResidualZeroScheme

variable {X : Scheme.{u}} {ℐY ℐZ : X.IdealSheafData} (h : ℐY ≤ ℐZ)

/-- For an effective Cartier divisor `ℐ_Y`, the residual ideal `𝒟_Y` of `ℐ_Y · 𝒪_{W_Y}` is an
effective Cartier divisor. -/
instance isEffectiveCartierDivisor_residualIdealAtInfinity_self
    [hY : Stacks.Divisors.IsEffectiveCartierDivisor ℐY] :
    Stacks.Divisors.IsEffectiveCartierDivisor (residualIdealAtInfinity ℐY ℐY) :=
  isEffectiveCartierDivisor_residualIdealAtInfinity le_rfl hY

variable [Stacks.Divisors.IsEffectiveCartierDivisor ℐY]

/-- **The invertible module `ρ^*𝒪(𝒟_Y)` on `W_Z ∖ X'_Z`**: the module of the residual divisor `𝒟_Y`
of the blowup at infinity in the centre `∞(Y)`, pulled back along the change of centre
`ρ : W_Z ∖ X'_Z ⟶ W_Y`. -/
abbrev residualModuleAtInfinity : (strictTransformComplAtInfinity ℐZ).toScheme.Modules :=
  (Scheme.Modules.pullback (blowupAtInfinityChangeOfCentre h)).obj
    (Stacks.Divisors.divisorSheaf (residualIdealAtInfinity ℐY ℐY))

/-- The canonical section of `𝒪(𝒟_Y)`, pulled back along the change of centre. -/
abbrev residualModuleSectionAtInfinity : Γ(residualModuleAtInfinity h, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections (blowupAtInfinityChangeOfCentre h) _
    (Stacks.Divisors.divisorSheafGlobalSection (residualIdealAtInfinity ℐY ℐY))

/-- **The residual zero scheme `Z₂ = Z(ρ^* 1_{𝒟_Y}) ⊆ W_Z ∖ X'_Z`**, which is `𝒟_Z` restricted to
`W_Z ∖ X'_Z` (`Stacks.Chow.residualZeroSchemeAtInfinity_eq`). -/
abbrev residualZeroSchemeAtInfinity :
    (strictTransformComplAtInfinity ℐZ).toScheme.IdealSheafData :=
  Stacks.Divisors.zeroScheme _ (residualModuleAtInfinity h) (residualModuleSectionAtInfinity h)

/-- **The zero scheme of `ρ^* 1_{𝒟_Y}` is `𝒟_Z` restricted to `W_Z ∖ X'_Z`**
(`Stacks.Chow.comap_residualIdealAtInfinity_changeOfCentre`). -/
theorem residualZeroSchemeAtInfinity_eq :
    residualZeroSchemeAtInfinity h =
      (residualIdealAtInfinity ℐY ℐZ).comap (strictTransformComplAtInfinity ℐZ).ι := by
  have h1 : Stacks.Divisors.zeroScheme _
      (Stacks.Divisors.divisorSheaf (residualIdealAtInfinity ℐY ℐY))
      (Stacks.Divisors.divisorSheafGlobalSection (residualIdealAtInfinity ℐY ℐY)) =
        residualIdealAtInfinity ℐY ℐY :=
    Stacks.Divisors.zeroScheme_canonicalSection _
  rw [residualZeroSchemeAtInfinity, Stacks.Divisors.zeroScheme_pullback, h1,
    comap_residualIdealAtInfinity_changeOfCentre h]

/-- The residual zero scheme is an effective Cartier divisor on `W_Z ∖ X'_Z`. -/
theorem isEffectiveCartierDivisor_residualZeroSchemeAtInfinity :
    Stacks.Divisors.IsEffectiveCartierDivisor (residualZeroSchemeAtInfinity h) := by
  rw [residualZeroSchemeAtInfinity_eq]
  exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
    (isEffectiveCartierDivisor_residualIdealAtInfinity h ‹_›) _

/-- The morphism `Z₂ ⟶ W_Z ∖ X'_Z ⟶ W_Z ⟶ 𝐏¹_X` from the residual zero scheme. -/
abbrev residualZeroSchemeToLine :
    (residualZeroSchemeAtInfinity h).subscheme ⟶ relativeProjectiveLine X :=
  (residualZeroSchemeAtInfinity h).subschemeι ≫ (strictTransformComplAtInfinity ℐZ).ι ≫
    blowupAtInfinityToLine ℐZ

/-- **The fibre at infinity `D = W_{Z,∞} ∩ Z₂` of the residual zero scheme**: the zero scheme of
the pullback of `1_{D_∞}` to `Z₂`. -/
abbrev residualFibreAtInfinity : (residualZeroSchemeAtInfinity h).subscheme.IdealSheafData :=
  Stacks.Divisors.zeroScheme _ (lineInfinityModule (residualZeroSchemeToLine h))
    (lineInfinityModuleSection (residualZeroSchemeToLine h))

/-- A point of the residual zero scheme off its fibre at infinity lies, in `W_Z`, off the fibre at
infinity `W_{Z,∞}`. -/
theorem mem_fibreComplAtInfinity_of_notMem_residualFibreAtInfinity
    (a : (residualZeroSchemeAtInfinity h).subscheme)
    (ha : a ∉ Set.range (residualFibreAtInfinity h).subschemeι.base) :
    (strictTransformComplAtInfinity ℐZ).ι.base
        ((residualZeroSchemeAtInfinity h).subschemeι.base a) ∈ fibreComplAtInfinity ℐZ := by
  rw [Scheme.IdealSheafData.range_subschemeι, residualFibreAtInfinity,
    zeroScheme_lineInfinityModuleSection, coe_support_comap] at ha
  rwa [fibreComplAtInfinity_eq_preimage]

end ResidualZeroScheme

/-! ### The strict transform of `𝐏¹_Y` inside the residual zero scheme -/

section ResidualStrictTransform

variable {X Y : Scheme.{u}} (iY : Y ⟶ X) [IsClosedImmersion iY]
  [Stacks.Divisors.IsEffectiveCartierDivisor iY.ker] {ℐZ : X.IdealSheafData} (h : iY.ker ≤ ℐZ)
  (ℐ' : Y.IdealSheafData) (hℐ' : ℐ' = ℐZ.comap iY)

/-- **The strict transform `W_{Z ∩ Y} ∖ X''` of `𝐏¹_Y` lies in the residual zero scheme**: the
comparison `W_{Z ∩ Y} ∖ X'' ⟶ W_Z ∖ X'_Z` factors through `Z₂ = V(𝒟_Z) ∩ (W_Z ∖ X'_Z)`. -/
def strictTransformToResidualZeroScheme :
    (strictTransformComplAtInfinity ℐ').toScheme ⟶ (residualZeroSchemeAtInfinity h).subscheme :=
  IsClosedImmersion.lift (residualZeroSchemeAtInfinity h).subschemeι
    (strictTransformComplAtInfinityComap iY ℐZ ℐ' hℐ') (by
      rw [Scheme.IdealSheafData.ker_subschemeι, ker_strictTransformComplAtInfinityComap,
        residualZeroSchemeAtInfinity_eq]
      exact Scheme.IdealSheafData.comap_mono _
        (residualIdealAtInfinity_le_ker_blowupAtInfinityComap h iY ℐ' hℐ'
          ((le_ker_iff_comap_eq_bot _ _).1 le_rfl)))

/-- The map `W_{Z ∩ Y} ∖ X'' ⟶ Z₂` followed by the inclusion of `Z₂` is the comparison
`W_{Z ∩ Y} ∖ X'' ⟶ W_Z ∖ X'_Z`. -/
@[reassoc (attr := simp)]
theorem strictTransformToResidualZeroScheme_subschemeι :
    strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫ (residualZeroSchemeAtInfinity h).subschemeι =
      strictTransformComplAtInfinityComap iY ℐZ ℐ' hℐ' :=
  IsClosedImmersion.lift_fac _ _ _

/-- The map `W_{Z ∩ Y} ∖ X'' ⟶ Z₂` is a closed immersion. -/
instance : IsClosedImmersion (strictTransformToResidualZeroScheme iY h ℐ' hℐ') := by
  have : IsClosedImmersion (strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫
      (residualZeroSchemeAtInfinity h).subschemeι) := by
    rw [strictTransformToResidualZeroScheme_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (residualZeroSchemeAtInfinity h).subschemeι

/-- The inclusion of the strict transform of `𝐏¹_Y` into the residual zero scheme lies over
`Y ⟶ X`. -/
@[reassoc]
theorem strictTransformToResidualZeroScheme_comp_toBase :
    strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫ (residualZeroSchemeAtInfinity h).subschemeι ≫
        (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ =
      (strictTransformComplAtInfinity ℐ').ι ≫ blowupAtInfinityToBase ℐ' ≫ iY := by
  rw [strictTransformToResidualZeroScheme_subschemeι_assoc,
    strictTransformComplAtInfinityComap_toBase]

/-- The inclusion of the strict transform of `𝐏¹_Y` into the residual zero scheme lies over
`𝐏¹_Y ⟶ 𝐏¹_X`. -/
theorem strictTransformToResidualZeroScheme_comp_toLine :
    strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫ residualZeroSchemeToLine h =
      (strictTransformComplAtInfinity ℐ').ι ≫ blowupAtInfinityToLine ℐ' ≫
        projectiveLineBaseChange iY := by
  rw [residualZeroSchemeToLine, strictTransformToResidualZeroScheme_subschemeι_assoc,
    strictTransformComplAtInfinityComap_toLine]

/-- **The fibre at infinity `D''` of the strict transform `W_{Z ∩ Y} ∖ X''` of `𝐏¹_Y`**: the zero
scheme of the pullback of `1_{D_∞}` along `W_{Z ∩ Y} ∖ X'' ⟶ Z₂ ⟶ 𝐏¹_X`. -/
abbrev strictTransformFibreAtInfinity :
    (strictTransformComplAtInfinity ℐ').toScheme.IdealSheafData :=
  Stacks.Divisors.zeroScheme _
    (lineInfinityModule (strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫
      residualZeroSchemeToLine h))
    (lineInfinityModuleSection (strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫
      residualZeroSchemeToLine h))

/-- **`D''` is the fibre at infinity `W_{Z ∩ Y, ∞} ∩ (W_{Z ∩ Y} ∖ X'')`** of the blowup at infinity
of `Y` in the centre `∞(Z ∩ Y)`. -/
theorem strictTransformFibreAtInfinity_eq :
    strictTransformFibreAtInfinity iY h ℐ' hℐ' =
      (fibreIdealAtInfinity ℐ').comap (strictTransformComplAtInfinity ℐ').ι := by
  rw [strictTransformFibreAtInfinity, zeroScheme_lineInfinityModuleSection,
    strictTransformToResidualZeroScheme_comp_toLine, Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.comap_comp, comap_lineInfinityDivisor_projectiveLineBaseChange,
    fibreIdealAtInfinity]

/-- `D''` is an effective Cartier divisor on `W_{Z ∩ Y} ∖ X''`. -/
theorem isEffectiveCartierDivisor_strictTransformFibreAtInfinity :
    Stacks.Divisors.IsEffectiveCartierDivisor (strictTransformFibreAtInfinity iY h ℐ' hℐ') := by
  rw [strictTransformFibreAtInfinity_eq]
  exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
    (isEffectiveCartierDivisor_fibreIdealAtInfinity ℐ') _

/-- **The inclusion `D'' ⟶ D` of the fibres at infinity** induced by `u : W_{Z ∩ Y} ∖ X'' ⟶ Z₂`. -/
def strictTransformFibreToResidualFibre :
    (strictTransformFibreAtInfinity iY h ℐ' hℐ').subscheme ⟶
      (residualFibreAtInfinity h).subscheme :=
  IsClosedImmersion.lift (residualFibreAtInfinity h).subschemeι
    ((strictTransformFibreAtInfinity iY h ℐ' hℐ').subschemeι ≫
      strictTransformToResidualZeroScheme iY h ℐ' hℐ') (by
      rw [Scheme.IdealSheafData.ker_subschemeι, le_ker_iff_comap_eq_bot,
        Scheme.IdealSheafData.comap_comp, residualFibreAtInfinity,
        ← Stacks.Divisors.zeroScheme_pullback, Stacks.Divisors.zeroScheme_pullback_comp,
        ← le_ker_iff_comap_eq_bot, Scheme.IdealSheafData.ker_subschemeι])

/-- The inclusion `D'' ⟶ D` followed by the inclusion of `D` into `Z₂` is the inclusion of `D''`
into `W_{Z ∩ Y} ∖ X''` followed by the map `W_{Z ∩ Y} ∖ X'' ⟶ Z₂`. -/
@[reassoc (attr := simp)]
theorem strictTransformFibreToResidualFibre_subschemeι :
    strictTransformFibreToResidualFibre iY h ℐ' hℐ' ≫ (residualFibreAtInfinity h).subschemeι =
      (strictTransformFibreAtInfinity iY h ℐ' hℐ').subschemeι ≫
        strictTransformToResidualZeroScheme iY h ℐ' hℐ' :=
  IsClosedImmersion.lift_fac _ _ _

/-- The inclusion `D'' ⟶ D` is a closed immersion. -/
instance : IsClosedImmersion (strictTransformFibreToResidualFibre iY h ℐ' hℐ') := by
  have : IsClosedImmersion (strictTransformFibreToResidualFibre iY h ℐ' hℐ' ≫
      (residualFibreAtInfinity h).subschemeι) := by
    rw [strictTransformFibreToResidualFibre_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (residualFibreAtInfinity h).subschemeι

end ResidualStrictTransform

/-! ### The Gysin map of the residual section on `[W_Z ∖ X'_Z]` -/

section ResidualGysin

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {ℐY ℐZ : X.IdealSheafData} (h : ℐY ≤ ℐZ) [Stacks.Divisors.IsEffectiveCartierDivisor ℐY]

/-- **Stacks 02TB for the residual section**: the Gysin map of `ρ^* 1_{𝒟_Y}` carries
`[W_Z ∖ X'_Z]_{n+1}` to the fundamental class `[Z₂]_n` of the residual zero scheme, when
`dim_δ(X) ≤ n`. -/
theorem gysinSystemOfInvertible_residualModuleAtInfinity_fundamentalChowClass {n : ℤ}
    (hX : schemeDeltaDimension C sX ≤ (n : EInt)) :
    (gysinSystemOfInvertible C).onChow
        ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX)
        (residualModuleAtInfinity h) (residualModuleSectionAtInfinity h) n
        (fundamentalChowClass C
          ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX) (n + 1)) =
      fundamentalChowClass C ((residualZeroSchemeAtInfinity h).subschemeι ≫
        (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX) n := by
  rw [gysinSystemOfInvertible_onChow_eq_gysinChowOfInvertible]
  exact gysinChowOfInvertible_fundamentalChowClass C _ n _ _
    (schemeDeltaDimension_strictTransformComplAtInfinity_le C sX ℐZ hX)
    (isEffectiveCartierDivisor_residualZeroSchemeAtInfinity h)

end ResidualGysin

/-! ### The Gysin map only sees a cycle off the zero scheme -/

section OffZeroScheme

variable (C : ChowSituation.{u}) {T : Scheme.{u}} (p : T ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : T.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **Remark 0B6Z, read off the zero scheme.** If the restriction of `L` to the zero scheme
`D = Z(s)` is trivial, the Gysin map of `s` on a cycle depends only on the coefficients of the
cycle off `D`. -/
theorem gysinHomomorphismOfInvertible_eq_of_eq_off_zeroScheme
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme T L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme T L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme T L s).subschemeι).obj L))
    (α β : CycleGroup C p (k + 1))
    (hαβ : ∀ t ∉ Set.range (Stacks.Divisors.zeroScheme T L s).subschemeι.base,
      α.1 t = β.1 t) :
    gysinHomomorphismOfInvertible C p k L s α = gysinHomomorphismOfInvertible C p k L s β := by
  set D := Stacks.Divisors.zeroScheme T L s
  have hδ : α - β = properPushforward C (D.subschemeι ≫ p) p D.subschemeι rfl (k + 1)
      ⟨cycleComap D.subschemeι D.subschemeι.isClosedEmbedding.injective (α - β).1,
        cycleComap_mem_cyclesOfDimension_of_isClosedImmersion C p _ D.subschemeι rfl (k + 1)
          (α - β).2⟩ := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun t => ?_)
    by_cases ht : t ∈ Set.range D.subschemeι.base
    · obtain ⟨y, rfl⟩ := ht
      exact (properPushforward_cycleComap_apply_of_isClosedImmersion C p _ D.subschemeι rfl
        (α - β) y).symm
    · have h0 : (properPushforward C (D.subschemeι ≫ p) p D.subschemeι rfl (k + 1)
          ⟨cycleComap D.subschemeι D.subschemeι.isClosedEmbedding.injective (α - β).1,
            cycleComap_mem_cyclesOfDimension_of_isClosedImmersion C p _ D.subschemeι rfl (k + 1)
              (α - β).2⟩).1 t = 0 := by
        by_contra hne
        exact ht (support_properPushforward_subset C _ p D.subschemeι rfl (k + 1) _ hne)
      rw [h0]
      show α.1 t - β.1 t = 0
      rw [hαβ t ht, sub_self]
  rw [← sub_eq_zero, ← map_sub, hδ]
  exact gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι_eq_zero C p k L s htriv _

end OffZeroScheme

/-! ### The residual zero scheme and the strict transform agree off the fibre at infinity -/

section Coefficients

/-- **The coefficient of the cycle of a closed subscheme only depends on the subscheme near the
point**: if two ideal sheaves agree on an open subscheme, the cycles of the closed subschemes they
cut out have the same coefficients at the points of that open. -/
theorem closedSubschemeCycleCoeff_eq_of_comap_eq (C : ChowSituation.{u}) {A A' : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (m : A' ⟶ A) [IsOpenImmersion m]
    {I J : A.IdealSheafData} (hIJ : I.comap m = J.comap m) (k : ℤ) (a' : A') :
    closedSubschemeCycleCoeff C sA I.subschemeι k (m.base a') =
      closedSubschemeCycleCoeff C sA J.subschemeι k (m.base a') := by
  rw [← closedSubschemeCycleCoeff_comap_of_isOpenImmersion C sA (m ≫ sA) m rfl I k a', hIJ,
    closedSubschemeCycleCoeff_comap_of_isOpenImmersion C sA (m ≫ sA) m rfl J k a']

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (iY : Y ⟶ X) [IsClosedImmersion iY] [Stacks.Divisors.IsEffectiveCartierDivisor iY.ker]
  {ℐZ : X.IdealSheafData} (h : iY.ker ≤ ℐZ) (ℐ' : Y.IdealSheafData) (hℐ' : ℐ' = ℐZ.comap iY)

/-- **Off the fibre at infinity, the residual zero scheme and the strict transform of `𝐏¹_Y` have
the same cycle**: at a point of `W_Z ∖ X'_Z` off `W_{Z,∞}`, the coefficients of the cycles of
`Z₂ = V(𝒟_Z) ∩ (W_Z ∖ X'_Z)` and of `W_{Z ∩ Y} ∖ X''` agree. -/
theorem closedSubschemeCycleCoeff_residualZeroSchemeAtInfinity (k : ℤ)
    (x : (strictTransformComplAtInfinity ℐZ).toScheme)
    (hx : (strictTransformComplAtInfinity ℐZ).ι.base x ∈ fibreComplAtInfinity ℐZ) :
    closedSubschemeCycleCoeff C
        ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX)
        (residualZeroSchemeAtInfinity h).subschemeι k x =
      closedSubschemeCycleCoeff C
        ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX)
        (strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫
          (residualZeroSchemeAtInfinity h).subschemeι) k x := by
  have e1 : closedSubschemeCycleCoeff C
      ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX)
      (residualZeroSchemeAtInfinity h).subschemeι k x =
        closedSubschemeCycleCoeff C (blowupAtInfinityToBase ℐZ ≫ sX)
          (residualIdealAtInfinity iY.ker ℐZ).subschemeι k
          ((strictTransformComplAtInfinity ℐZ).ι.base x) := by
    rw [closedSubschemeCycleCoeff_congr C _ (residualZeroSchemeAtInfinity_eq h) k x,
      closedSubschemeCycleCoeff_comap_of_isOpenImmersion C (blowupAtInfinityToBase ℐZ ≫ sX) _
        (strictTransformComplAtInfinity ℐZ).ι rfl _ k x]
  have e2 : closedSubschemeCycleCoeff C
      ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX)
      (strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫
        (residualZeroSchemeAtInfinity h).subschemeι) k x =
        closedSubschemeCycleCoeff C (blowupAtInfinityToBase ℐZ ≫ sX)
          (blowupAtInfinityComap iY ℐZ ℐ' hℐ').ker.subschemeι k
          ((strictTransformComplAtInfinity ℐZ).ι.base x) := by
    show (cycleAssociatedToClosedSubscheme C
      ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX)
      (strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫
        (residualZeroSchemeAtInfinity h).subschemeι) k).1 x = _
    rw [cycleAssociatedToClosedSubscheme_congr C _ _
        (strictTransformComplAtInfinityComap iY ℐZ ℐ' hℐ')
        (strictTransformToResidualZeroScheme_subschemeι iY h ℐ' hℐ') k,
      cycleAssociatedToClosedSubscheme_ker]
    show closedSubschemeCycleCoeff C
      ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX)
      (strictTransformComplAtInfinityComap iY ℐZ ℐ' hℐ').ker.subschemeι k x = _
    rw [closedSubschemeCycleCoeff_congr C _
        (ker_strictTransformComplAtInfinityComap iY ℐZ ℐ' hℐ') k x,
      closedSubschemeCycleCoeff_comap_of_isOpenImmersion C (blowupAtInfinityToBase ℐZ ≫ sX) _
        (strictTransformComplAtInfinity ℐZ).ι rfl _ k x]
  rw [e1, e2]
  obtain ⟨o, ho⟩ : (strictTransformComplAtInfinity ℐZ).ι.base x ∈
      Set.range (fibreComplAtInfinity ℐZ).ι.base := by
    rwa [Scheme.Opens.range_ι]
  rw [← ho]
  exact closedSubschemeCycleCoeff_eq_of_comap_eq C (blowupAtInfinityToBase ℐZ ≫ sX)
    (fibreComplAtInfinity ℐZ).ι (comap_residualIdealAtInfinity_compl_fibre_eq_ker iY h ℐ' hℐ') k o

end Coefficients

/-! ### The Gysin map at infinity on the residual zero scheme -/

section InfinityGysin

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (iY : Y ⟶ X) [IsClosedImmersion iY] [Stacks.Divisors.IsEffectiveCartierDivisor iY.ker]
  {ℐZ : X.IdealSheafData} (h : iY.ker ≤ ℐZ) (ℐ' : Y.IdealSheafData) (hℐ' : ℐ' = ℐZ.comap iY)

/-- **The Gysin map at infinity on the residual zero scheme.** Let `Z₂ = V(𝒟_Z) ∩ (W_Z ∖ X'_Z)` be
the residual zero scheme, carrying the pullback of `𝒪(D_∞)` and of its canonical section, with zero
scheme `D = W_{Z,∞} ∩ Z₂`, let `u : W_{Z ∩ Y} ∖ X'' ⟶ Z₂` be the inclusion of the strict transform
of `𝐏¹_Y`, and let `D''` be its fibre at infinity, the zero scheme of the pulled-back section
(`Stacks.Chow.strictTransformFibreAtInfinity_eq`). If `Y ⊆ X` is an effective Cartier divisor and
`dim_δ(X) ≤ k + 1`, then for any proper `j : D'' ⟶ D` over `u`

  `(1_{D_∞}|_{Z₂})^*[Z₂]_{k+1} = j_*[D'']_k`. -/
theorem gysinSystemOfInvertible_lineInfinityModule_residualZeroSchemeAtInfinity {k : ℤ}
    (hX : schemeDeltaDimension C sX ≤ ((k + 1 : ℤ) : EInt))
    (j : (strictTransformFibreAtInfinity iY h ℐ' hℐ').subscheme ⟶
      (residualFibreAtInfinity h).subscheme) [IsProper j]
    (hjsq : j ≫ (residualFibreAtInfinity h).subschemeι =
      (strictTransformFibreAtInfinity iY h ℐ' hℐ').subschemeι ≫
        strictTransformToResidualZeroScheme iY h ℐ' hℐ')
    (hj : j ≫ (residualFibreAtInfinity h).subschemeι ≫
        (residualZeroSchemeAtInfinity h).subschemeι ≫
          (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX =
      (strictTransformFibreAtInfinity iY h ℐ' hℐ').subschemeι ≫
        strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫
          (residualZeroSchemeAtInfinity h).subschemeι ≫
            (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX) :
    (gysinSystemOfInvertible C).onChow
        ((residualZeroSchemeAtInfinity h).subschemeι ≫
          (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX)
        (lineInfinityModule (residualZeroSchemeToLine h))
        (lineInfinityModuleSection (residualZeroSchemeToLine h)) k
        (fundamentalChowClass C ((residualZeroSchemeAtInfinity h).subschemeι ≫
          (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX) (k + 1)) =
      properChowPushforward C _ _ j hj k (properPushforwardDescends C _ _ j hj k)
        (fundamentalChowClass C ((strictTransformFibreAtInfinity iY h ℐ' hℐ').subschemeι ≫
          strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫
            (residualZeroSchemeAtInfinity h).subschemeι ≫
              (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX) k) := by
  have hoff : ∀ a ∉ Set.range (residualFibreAtInfinity h).subschemeι.base,
      (fundamentalCycle C ((residualZeroSchemeAtInfinity h).subschemeι ≫
        (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX) (k + 1)).1 a =
        (properPushforward C _ _ (strictTransformToResidualZeroScheme iY h ℐ' hℐ') rfl (k + 1)
          (fundamentalCycle C (strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫
            (residualZeroSchemeAtInfinity h).subschemeι ≫
              (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX)
            (k + 1))).1 a := by
    intro a ha
    rw [fundamentalCycle, fundamentalCycle, properPushforward_cycleAssociatedToClosedSubscheme_id]
    show closedSubschemeCycleCoeff C _ (𝟙 _) (k + 1) a =
      closedSubschemeCycleCoeff C _ (strictTransformToResidualZeroScheme iY h ℐ' hℐ') (k + 1) a
    rw [← closedSubschemeCycleCoeff_comp_isClosedImmersion C _ _
        (residualZeroSchemeAtInfinity h).subschemeι rfl,
      ← closedSubschemeCycleCoeff_comp_isClosedImmersion C _ _
        (residualZeroSchemeAtInfinity h).subschemeι rfl]
    have hid := congrArg (fun c : CycleGroup C
        ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX) (k + 1) =>
          c.1 ((residualZeroSchemeAtInfinity h).subschemeι.base a))
      (cycleAssociatedToClosedSubscheme_congr C _ _ (residualZeroSchemeAtInfinity h).subschemeι
        (Category.id_comp _) (k + 1))
    exact hid.trans (closedSubschemeCycleCoeff_residualZeroSchemeAtInfinity C sX iY h ℐ' hℐ'
      (k + 1) _ (mem_fibreComplAtInfinity_of_notMem_residualFibreAtInfinity h a ha))
  have hdim : schemeDeltaDimension C (strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫
      (residualZeroSchemeAtInfinity h).subschemeι ≫
        (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX) ≤
      ((k + 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_congr C (strictTransformToResidualZeroScheme_comp_toBase_assoc
      iY h ℐ' hℐ' sX)]
    exact schemeDeltaDimension_strictTransformComplAtInfinity_le_of_isEffectiveCartierDivisor C sX
      iY ‹_› ℐ' hX
  have h02TB := gysinChowOfInvertible_fundamentalChowClass C _ k _ _ hdim
    (isEffectiveCartierDivisor_strictTransformFibreAtInfinity iY h ℐ' hℐ')
  have h02TA := gysinSystemOfInvertible_properPushforward_pullbackModule C _ _
    (strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫ residualZeroSchemeToLine h)
    (residualZeroSchemeToLine h) (strictTransformToResidualZeroScheme iY h ℐ' hℐ') rfl rfl _ _ k
    j hjsq hj (fundamentalChowClass C (strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫
      (residualZeroSchemeAtInfinity h).subschemeι ≫
        (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX) (k + 1))
  simp only [gysinSystemOfInvertible_onChow_eq_gysinChowOfInvertible] at h02TA ⊢
  show gysinHomomorphismOfInvertible C _ k _ _ (fundamentalCycle C _ (k + 1)) = _
  rw [gysinHomomorphismOfInvertible_eq_of_eq_off_zeroScheme C _ k _ _
    (isTrivial_lineInfinityModule _) _ _ hoff]
  exact h02TA.trans (congrArg _ h02TB)

/-- **The second composite of Stacks 0B73 on `[W_Z ∖ X'_Z]`, in the form of
`Stacks.Chow.gysinSystemOfInvertible_comm_properPushforward`.** Applying first the Gysin map of the
residual section `ρ^* 1_{𝒟_Y}` and then that of `1_{D_∞}` to `[W_Z ∖ X'_Z]_{k+2}` gives
`j_*[D'']_k`, when `Y ⊆ X` is an effective Cartier divisor and `dim_δ(X) ≤ k + 1`. The modules and
sections are written out as `Stacks.Chow.gysinSystemOfInvertible_comm_properPushforward` takes
them, with `Y₂ = Z₂` and `u₂ = 𝟙`. -/
theorem gysinSystemOfInvertible_lineInfinityModule_comp_residualModuleAtInfinity
    {k : ℤ} (hX : schemeDeltaDimension C sX ≤ ((k + 1 : ℤ) : EInt))
    (j : (strictTransformFibreAtInfinity iY h ℐ' hℐ').subscheme ⟶
      (residualFibreAtInfinity h).subscheme) [IsProper j]
    (hjsq : j ≫ (residualFibreAtInfinity h).subschemeι =
      (strictTransformFibreAtInfinity iY h ℐ' hℐ').subschemeι ≫
        strictTransformToResidualZeroScheme iY h ℐ' hℐ')
    (hj : j ≫ (residualFibreAtInfinity h).subschemeι ≫
        (residualZeroSchemeAtInfinity h).subschemeι ≫
          (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX =
      (strictTransformFibreAtInfinity iY h ℐ' hℐ').subschemeι ≫
        strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫
          (residualZeroSchemeAtInfinity h).subschemeι ≫
            (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX) :
    (gysinSystemOfInvertible C).onChow
        ((residualZeroSchemeAtInfinity h).subschemeι ≫
          (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX)
        ((Scheme.Modules.pullback ((residualZeroSchemeAtInfinity h).subschemeι ≫
          (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToLine ℐZ)).obj
            (Stacks.Divisors.divisorSheaf (lineInfinityDivisor X)))
        (AlgebraicGeometry.pullbackGlobalSections ((residualZeroSchemeAtInfinity h).subschemeι ≫
          (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToLine ℐZ) _
            (Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor X))) k
        (properChowPushforward C _ ((residualZeroSchemeAtInfinity h).subschemeι ≫
            (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX) (𝟙 _)
          (Category.id_comp _) (k + 1) (properPushforwardDescends C _ _ _ _ _)
          ((gysinSystemOfInvertible C).onChow
            ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX)
            ((Scheme.Modules.pullback (blowupAtInfinityChangeOfCentre h)).obj
              (Stacks.Divisors.divisorSheaf (residualIdealAtInfinity iY.ker iY.ker)))
            (AlgebraicGeometry.pullbackGlobalSections (blowupAtInfinityChangeOfCentre h) _
              (Stacks.Divisors.divisorSheafGlobalSection
                (residualIdealAtInfinity iY.ker iY.ker))) (k + 1)
            (fundamentalChowClass C
              ((strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX)
              (k + 1 + 1)))) =
      properChowPushforward C _ _ j hj k (properPushforwardDescends C _ _ j hj k)
        (fundamentalChowClass C ((strictTransformFibreAtInfinity iY h ℐ' hℐ').subschemeι ≫
          strictTransformToResidualZeroScheme iY h ℐ' hℐ' ≫
            (residualZeroSchemeAtInfinity h).subschemeι ≫
              (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX) k) := by
  have h2 := gysinSystemOfInvertible_residualModuleAtInfinity_fundamentalChowClass C sX h hX
  rw [properChowPushforward_id]
  exact (congrArg _ h2).trans
    (gysinSystemOfInvertible_lineInfinityModule_residualZeroSchemeAtInfinity C sX iY h ℐ' hℐ' hX
      j hjsq hj)

end InfinityGysin

/-! ### The normal cone as the fibre at infinity of `W ∖ X'` -/

section NormalCone

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The ideal of `C_ZX ⊆ W ∖ X'` is the fibre at infinity**: the closed immersion `C_ZX ⟶ W ∖ X'`
of `Stacks.Chow.normalConeToStrictTransformComplAtInfinity` cuts out
`W_∞ ∩ (W ∖ X') = E ∩ (W ∖ X')` (Stacks 0FBH). -/
theorem ker_normalConeToStrictTransformComplAtInfinity :
    (normalConeToStrictTransformComplAtInfinity i).ker =
      (fibreIdealAtInfinity i.ker).comap (strictTransformComplAtInfinity i.ker).ι := by
  rw [normalConeToStrictTransformComplAtInfinity, Scheme.Hom.ker_comp_of_isIso,
    ker_morphismRestrict_eq_comap, Scheme.IdealSheafData.ker_subschemeι,
    comap_fibreIdealAtInfinity_ι_compl]

/-- **`C_ZX ≅ W_∞ ∩ (W ∖ X')`** (Stacks 0FBH): the normal cone is the fibre at infinity of the open
complement `W ∖ X'` of the strict transform, as closed subschemes of `W ∖ X'`. -/
def normalConeIsoFibreAtInfinityCompl :
    Stacks.Conormal.normalCone i ≅
      ((fibreIdealAtInfinity i.ker).comap (strictTransformComplAtInfinity i.ker).ι).subscheme :=
  asIso (normalConeToStrictTransformComplAtInfinity i).toImage ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (ker_normalConeToStrictTransformComplAtInfinity i))

/-- The identification `C_ZX ≅ W_∞ ∩ (W ∖ X')` followed by the inclusion into `W ∖ X'` is the
morphism `C_ZX ⟶ W ∖ X'`. -/
@[reassoc (attr := simp)]
theorem normalConeIsoFibreAtInfinityCompl_hom_subschemeι :
    (normalConeIsoFibreAtInfinityCompl i).hom ≫
        ((fibreIdealAtInfinity i.ker).comap (strictTransformComplAtInfinity i.ker).ι).subschemeι =
      normalConeToStrictTransformComplAtInfinity i := by
  rw [normalConeIsoFibreAtInfinityCompl, Iso.trans_hom, eqToIso.hom, Category.assoc,
    subschemeι_eqToHom (ker_normalConeToStrictTransformComplAtInfinity i), asIso_hom,
    Scheme.Hom.toImage_imageι]

/-- The identification `C_ZX ≅ W_∞ ∩ (W ∖ X')` is compatible with the open immersion
`j : C_ZX ⟶ W_∞` of Stacks 0FBH and the inclusions into `W`. -/
@[reassoc]
theorem normalConeIsoFibreAtInfinityCompl_hom_comp_inclusion {S : Scheme.{u}} (sX : X ⟶ S) :
    (normalConeIsoFibreAtInfinityCompl i).hom ≫
        ((fibreIdealAtInfinity i.ker).comap (strictTransformComplAtInfinity i.ker).ι).subschemeι ≫
          (strictTransformComplAtInfinity i.ker).ι =
      normalConeToFibreAtInfinity i sX ≫
        modificationInclusionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct i.ker sX) := by
  rw [normalConeIsoFibreAtInfinityCompl_hom_subschemeι_assoc,
    normalConeToStrictTransformComplAtInfinity_ι_eq]

/-- The normal cone of a closed subscheme of a scheme locally of finite type over a locally
Noetherian base is locally of finite type over the base. -/
instance locallyOfFiniteType_normalConeToX_comp {S : Scheme.{u}} [IsLocallyNoetherian S]
    (sX : X ⟶ S) [LocallyOfFiniteType sX] : LocallyOfFiniteType (normalConeToX i ≫ sX) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have : LocallyOfFiniteType (normalConeToX i) := by
    change LocallyOfFiniteType (Stacks.Conormal.normalConeToBase i ≫ i)
    rw [← normalConeToExceptionalDivisor_comp_toBase]
    infer_instance
  infer_instance

end NormalCone

/-! ### The normal cone `C_ZY` as the Gysin image -/

section NormalConeGysin

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (iY : Y ⟶ X) [IsClosedImmersion iY] [Stacks.Divisors.IsEffectiveCartierDivisor iY.ker]
  {ℐZ : X.IdealSheafData} (h : iY.ker ≤ ℐZ) (iZY : Z ⟶ Y) [IsClosedImmersion iZY]
  (hZY : iZY.ker = ℐZ.comap iY)

/-- **`C_ZY ≅ D''`**: the normal cone of `Z ⊆ Y` is the fibre at infinity of the strict transform
`W_{Z ∩ Y} ∖ X''` of `𝐏¹_Y` (Stacks 0FBH). -/
def normalConeIsoStrictTransformFibreAtInfinity :
    Stacks.Conormal.normalCone iZY ≅
      (strictTransformFibreAtInfinity iY h iZY.ker hZY).subscheme :=
  normalConeIsoFibreAtInfinityCompl iZY ≪≫ eqToIso (congrArg Scheme.IdealSheafData.subscheme
    (strictTransformFibreAtInfinity_eq iY h iZY.ker hZY).symm)

/-- The identification `C_ZY ≅ D''` followed by the inclusion of `D''` into `W_{Z ∩ Y} ∖ X''` is
the morphism `C_ZY ⟶ W_{Z ∩ Y} ∖ X''`. -/
@[reassoc (attr := simp)]
theorem normalConeIsoStrictTransformFibreAtInfinity_hom_subschemeι :
    (normalConeIsoStrictTransformFibreAtInfinity iY h iZY hZY).hom ≫
        (strictTransformFibreAtInfinity iY h iZY.ker hZY).subschemeι =
      normalConeToStrictTransformComplAtInfinity iZY := by
  rw [normalConeIsoStrictTransformFibreAtInfinity, Iso.trans_hom, eqToIso.hom, Category.assoc,
    subschemeι_eqToHom (strictTransformFibreAtInfinity_eq iY h iZY.ker hZY).symm,
    normalConeIsoFibreAtInfinityCompl_hom_subschemeι]

/-- **The closed immersion `κ : C_ZY ⟶ D = W_{Z,∞} ∩ Z₂`**: the normal cone of `Z ⊆ Y`, as the
fibre at infinity of the strict transform of `𝐏¹_Y`, inside the fibre at infinity of the residual
zero scheme. -/
def normalConeToResidualFibreAtInfinity :
    Stacks.Conormal.normalCone iZY ⟶ (residualFibreAtInfinity h).subscheme :=
  (normalConeIsoStrictTransformFibreAtInfinity iY h iZY hZY).hom ≫
    strictTransformFibreToResidualFibre iY h iZY.ker hZY

/-- The morphism `κ : C_ZY ⟶ D` is a closed immersion. -/
instance : IsClosedImmersion (normalConeToResidualFibreAtInfinity iY h iZY hZY) := by
  rw [normalConeToResidualFibreAtInfinity]
  infer_instance

/-- The morphism `κ : C_ZY ⟶ D` followed by the inclusion of `D` into `Z₂` is the morphism
`C_ZY ⟶ W_{Z ∩ Y} ∖ X''` followed by the map `W_{Z ∩ Y} ∖ X'' ⟶ Z₂`. -/
@[reassoc (attr := simp)]
theorem normalConeToResidualFibreAtInfinity_subschemeι :
    normalConeToResidualFibreAtInfinity iY h iZY hZY ≫ (residualFibreAtInfinity h).subschemeι =
      normalConeToStrictTransformComplAtInfinity iZY ≫
        strictTransformToResidualZeroScheme iY h iZY.ker hZY := by
  rw [normalConeToResidualFibreAtInfinity, Category.assoc,
    strictTransformFibreToResidualFibre_subschemeι,
    normalConeIsoStrictTransformFibreAtInfinity_hom_subschemeι_assoc]

omit [LocallyOfFiniteType sX] in
/-- A morphism `C_ZY ⟶ D` over `C_ZY ⟶ W_{Z ∩ Y} ∖ X'' ⟶ Z₂` lies over `X`. -/
theorem comp_toBase_of_comp_residualFibreAtInfinity_subschemeι
    (κ : Stacks.Conormal.normalCone iZY ⟶ (residualFibreAtInfinity h).subscheme)
    (hκ : κ ≫ (residualFibreAtInfinity h).subschemeι =
      normalConeToStrictTransformComplAtInfinity iZY ≫
        strictTransformToResidualZeroScheme iY h iZY.ker hZY) :
    κ ≫ (residualFibreAtInfinity h).subschemeι ≫ (residualZeroSchemeAtInfinity h).subschemeι ≫
        (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX =
      normalConeToX iZY ≫ iY ≫ sX := by
  rw [reassoc_of% hκ, strictTransformToResidualZeroScheme_comp_toBase_assoc,
    normalConeToStrictTransformComplAtInfinity_ι_assoc,
    reassoc_of% normalConeToExceptionalDivisor_comp_toBase]
  rfl

/-- **The Gysin map at infinity on the residual zero scheme is the normal cone `C_ZY`.** Let
`Z ⊆ Y ⊆ X` be closed subschemes with `ℐ_Y ⊆ ℐ_Z`, `Y` an effective Cartier divisor in `X`, and
`dim_δ(X) ≤ k + 1`. Then for any proper `κ : C_ZY ⟶ D` into the zero scheme `D = W_{Z,∞} ∩ Z₂`
lying over `C_ZY ⟶ W_{Z ∩ Y} ∖ X'' ⟶ Z₂` (for instance
`Stacks.Chow.normalConeToResidualFibreAtInfinity`),

  `(1_{D_∞}|_{Z₂})^*[Z₂]_{k+1} = κ_*[C_ZY]_k`. -/
theorem gysinSystemOfInvertible_lineInfinityModule_residualZeroScheme_eq_normalCone
    {k : ℤ} (hX : schemeDeltaDimension C sX ≤ ((k + 1 : ℤ) : EInt))
    (κ : Stacks.Conormal.normalCone iZY ⟶ (residualFibreAtInfinity h).subscheme) [IsProper κ]
    (hκ : κ ≫ (residualFibreAtInfinity h).subschemeι =
      normalConeToStrictTransformComplAtInfinity iZY ≫
        strictTransformToResidualZeroScheme iY h iZY.ker hZY) :
    (gysinSystemOfInvertible C).onChow
        ((residualZeroSchemeAtInfinity h).subschemeι ≫
          (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX)
        (lineInfinityModule (residualZeroSchemeToLine h))
        (lineInfinityModuleSection (residualZeroSchemeToLine h)) k
        (fundamentalChowClass C ((residualZeroSchemeAtInfinity h).subschemeι ≫
          (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX) (k + 1)) =
      properChowPushforward C (normalConeToX iZY ≫ iY ≫ sX) _ κ
        (comp_toBase_of_comp_residualFibreAtInfinity_subschemeι C sX iY h iZY hZY κ hκ) k
        (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (normalConeToX iZY ≫ iY ≫ sX) k) := by
  set e := normalConeIsoStrictTransformFibreAtInfinity iY h iZY hZY
  have hjsq : (e.inv ≫ κ) ≫ (residualFibreAtInfinity h).subschemeι =
      (strictTransformFibreAtInfinity iY h iZY.ker hZY).subschemeι ≫
        strictTransformToResidualZeroScheme iY h iZY.ker hZY := by
    rw [Category.assoc, hκ,
      ← normalConeIsoStrictTransformFibreAtInfinity_hom_subschemeι iY h iZY hZY, Category.assoc,
      Iso.inv_hom_id_assoc]
  have hj : (e.inv ≫ κ) ≫ (residualFibreAtInfinity h).subschemeι ≫
      (residualZeroSchemeAtInfinity h).subschemeι ≫
        (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX =
      (strictTransformFibreAtInfinity iY h iZY.ker hZY).subschemeι ≫
        strictTransformToResidualZeroScheme iY h iZY.ker hZY ≫
          (residualZeroSchemeAtInfinity h).subschemeι ≫
            (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX := by
    rw [← Category.assoc _ (residualFibreAtInfinity h).subschemeι, hjsq, Category.assoc]
  have he : e.hom ≫ (strictTransformFibreAtInfinity iY h iZY.ker hZY).subschemeι ≫
      strictTransformToResidualZeroScheme iY h iZY.ker hZY ≫
        (residualZeroSchemeAtInfinity h).subschemeι ≫
          (strictTransformComplAtInfinity ℐZ).ι ≫ blowupAtInfinityToBase ℐZ ≫ sX =
      normalConeToX iZY ≫ iY ≫ sX := by
    rw [normalConeIsoStrictTransformFibreAtInfinity_hom_subschemeι_assoc,
      strictTransformToResidualZeroScheme_comp_toBase_assoc,
      normalConeToStrictTransformComplAtInfinity_ι_assoc,
      reassoc_of% normalConeToExceptionalDivisor_comp_toBase]
    rfl
  rw [gysinSystemOfInvertible_lineInfinityModule_residualZeroSchemeAtInfinity C sX iY h iZY.ker
      hZY hX (e.inv ≫ κ) hjsq hj,
    ← chowPushforwardOfIso_fundamentalChowClass C _ _ e.hom he k,
    ← properChowPushforward_eq_chowPushforwardOfIso C _ _ e.hom he k
      (properPushforwardDescends C _ _ _ _ _)]
  exact (properChowPushforward_comp_apply C _ _ _ e.hom (e.inv ≫ κ) κ
    (Iso.hom_inv_id_assoc _ _) he hj _ k _ _ _ _).symm

end NormalConeGysin

end Stacks.Chow

end
