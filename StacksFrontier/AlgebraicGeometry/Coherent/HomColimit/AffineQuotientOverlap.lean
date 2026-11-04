module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.AffineQuotientSurjectivity
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.QuotientRaise

/-!
# The affine comparison of two local morphisms `Iⁿ|_W ⟶ (F/F_n)|_W`

Let `X` be a scheme, let `I` be a quasi-coherent sheaf of ideals of finite type, let `F` be a
quasi-coherent `𝒪_X`-module, let `F_n` be the subsheaf of sections annihilated by `Iⁿ` and write
`U = X ∖ V(I)`.  Over an **affine** open `W`, two morphisms `θ, θ' : Iⁿ|_W ⟶ (F/F_n)|_W` whose
values on the unit section of `Iⁿ` agree over every open of `W` missing the support of `I` need
not be equal; but after raising the exponent they are.

This is the injectivity half of the affine statement [Stacks, Tag 01PM] in the language of
`𝒪_X`-modules, and it is the comparison on the overlaps that the surjectivity half of
[Stacks, Tag 01PQ] (c) needs: the local morphisms produced by
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_affine_restrictSections_oneSection_eq` on two
members of an affine covering agree on the unit section over the intersection, and that is all
they do agree on until the exponent is raised.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.affineQuotientLinearMap`: the `Γ(X, W)`-linear map
  `I(W)ⁿ → Γ(F, W)/Γ(F, W)_n` read off from a morphism `Iⁿ|_W ⟶ (F/F_n)|_W` over an affine open
  `W`.  This is the inverse of
  `Stacks.AlgebraicGeometry.IdealPowerColimit.affineQuotientHomOnSections`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_raiseExponent_eq_of_oneSection_eq`:
  **the overlap comparison.**  Two morphisms `Iⁿ|_W ⟶ (F/F_n)|_W` over an affine open agreeing on
  the unit section away from `V(I)` become equal after raising the exponent to some `n + N`.

## Implementation notes

The proof is the affine argument of [Stacks, Tag 01PM], applied to the *difference* of the two
linear maps read off from `θ` and `θ'`:

* `affineQuotientLinearMap` turns each morphism into a `Γ(X, W)`-linear map
  `δ : I(W)ⁿ → Γ(F, W)/Γ(F, W)_n`, using
  `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowAffineSectionsEquiv` and
  `Stacks.AlgebraicGeometry.IdealPowerColimit.quotientSectionsAffineEquiv`;
* for `f ∈ I(W)` the section `δ(fⁿ)` of `F/F_n` over `W` vanishes on `D(f)`, because there `fⁿ`
  is `fⁿ` times the unit section (`eq_smul_map_oneSection`) and the two morphisms agree on the
  unit section over `D(f)`, which misses the support of `I`
  (`basicOpen_le_compl_support`);
* `F/F_n` is quasi-coherent, `W` is quasi-compact, so a power of `f` annihilates `δ(fⁿ)`, by
  `Stacks.AlgebraicGeometry.QcqsLocalization.exists_pow_smul_eq_zero_of_res_eq_zero_of_isCompact`;
* `I(W)` is finitely generated, so
  `Stacks.AlgebraicGeometry.IdealPowerSections.exists_comp_inclusion_eq_zero` produces an `N`
  with `δ` vanishing on `I(W)^(n+N)`;
* `Stacks.AlgebraicGeometry.IdealPowerColimit.restrictSections_ext_of_affineQuotientHom` turns
  that back into an equality of morphisms, the postcomposition with `F/F_n ⟶ F/F_(n+N)` being
  harmless since the two sides are already equal before it.

Note that the conclusion is stated with
`Stacks.AlgebraicGeometry.IdealPowerColimit.raiseExponent` on both sides even though the proof
gives the stronger statement that the two *precomposites* `I^(n+N)|_W ⟶ (F/F_n)|_W` agree: the
raised form is the one with matching source and target exponents, hence the one that can be fed
to the glueing.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM) (the affine case)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### The linear map read off from a morphism over an affine open -/

/-- The underlying ring element of the section of `Iⁿ` over an affine open `W` corresponding to
`y ∈ I(W)ⁿ` is `y` itself. -/
theorem idealPowAffineSectionsEquiv_symm_coe (I : X.IdealSheafData) (n : ℕ)
    (W : X.affineOpens) (y : ↥(I.ideal W ^ n : Ideal Γ(X, W.1))) :
    (((idealPowAffineSectionsEquiv I n W).symm y).1 : Γ(X, W.1)) = (y.1 : Γ(X, W.1)) := rfl

section

variable (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
  (hFG : ∀ V : X.affineOpens, (I.ideal V).FG) (n : ℕ) (W : X.affineOpens)

/-- The `Γ(X, W)`-linear map `I(W)ⁿ → Γ(F, W)/Γ(F, W)_n` read off from a morphism
`θ : Iⁿ|_W ⟶ (F/F_n)|_W` over an affine open `W`: the value of the sectionwise family of `θ` at
`W`, conjugated by the two identifications of sections over an affine open.  This inverts
`Stacks.AlgebraicGeometry.IdealPowerColimit.affineQuotientHomOnSections`. -/
noncomputable def affineQuotientLinearMap
    (θ : Scheme.Modules.restrict (idealPow I n) W.1.ι ⟶
      Scheme.Modules.restrict (quotientModule I F n) W.1.ι) :
    ↥(I.ideal W ^ n : Ideal Γ(X, W.1)) →ₗ[Γ(X, W.1)] affineQuotient I F n W where
  toFun x := (quotientSectionsAffineEquiv I F n hFG W).symm
    (restrictSections θ W.1 le_rfl ((idealPowAffineSectionsEquiv I n W).symm x))
  map_add' x y := by
    simp only [map_add, restrictSections_add]
  map_smul' r x := by
    simp only [RingHom.id_apply, map_smul, restrictSections_smul]

/-- The value of `affineQuotientLinearMap` at `x ∈ I(W)ⁿ` is the value of the sectionwise family
of `θ` at `W` on the section of `Iⁿ` corresponding to `x`, transported to `Γ(F, W)/Γ(F, W)_n`. -/
theorem affineQuotientLinearMap_apply
    (θ : Scheme.Modules.restrict (idealPow I n) W.1.ι ⟶
      Scheme.Modules.restrict (quotientModule I F n) W.1.ι)
    (x : ↥(I.ideal W ^ n : Ideal Γ(X, W.1))) :
    affineQuotientLinearMap I F hFG n W θ x
      = (quotientSectionsAffineEquiv I F n hFG W).symm
          (restrictSections θ W.1 le_rfl ((idealPowAffineSectionsEquiv I n W).symm x)) :=
  rfl

/-! ### The overlap comparison -/

include hFG in
/-- **The overlap comparison of [Stacks, Tag 01PQ] (c), in the affine case.** Let `I` be a
quasi-coherent sheaf of ideals of finite type and `F` a quasi-coherent `𝒪_X`-module.  If two
morphisms `θ, θ' : Iⁿ|_W ⟶ (F/F_n)|_W` over an affine open `W` send the unit section of `Iⁿ` to
the same section of `F/F_n` over every open of `W` missing the support of `I`, then there is an
`N` for which the two morphisms raised to the exponent `n + N` are equal.

This is the injectivity half of [Stacks, Tag 01PM] read on `𝒪_X`-modules; the exponent really has
to be raised, as the two morphisms differ by one killed by a power of `I` which is not bounded by
`n`. -/
theorem exists_raiseExponent_eq_of_oneSection_eq
    (θ θ' : Scheme.Modules.restrict (idealPow I n) W.1.ι ⟶
      Scheme.Modules.restrict (quotientModule I F n) W.1.ι)
    (hagree : ∀ (V : X.Opens) (hVW : V ≤ W.1) (hVU : V ≤ (I.support.compl : X.Opens)),
      restrictSections θ V hVW ((idealPow I n).presheaf.map (homOfLE hVU).op (oneSection I n))
        = restrictSections θ' V hVW
            ((idealPow I n).presheaf.map (homOfLE hVU).op (oneSection I n))) :
    ∃ N : ℕ, raiseExponent I F (Nat.le_add_right n N) W.1 θ
      = raiseExponent I F (Nat.le_add_right n N) W.1 θ' := by
  classical
  let := isQuasicoherent_quotientModule I F n hFG
  set δ : ↥(I.ideal W ^ n : Ideal Γ(X, W.1)) →ₗ[Γ(X, W.1)] affineQuotient I F n W :=
    affineQuotientLinearMap I F hFG n W θ - affineQuotientLinearMap I F hFG n W θ' with hδdef
  have hkey : ∀ (f : Γ(X, W.1)) (hf : f ∈ I.ideal W),
      ∃ k : ℕ, f ^ k • δ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩ = 0 := by
    intro f hf
    have hDW : X.basicOpen f ≤ W.1 := X.basicOpen_le f
    have hDU : X.basicOpen f ≤ (I.support.compl : X.Opens) := basicOpen_le_compl_support I W hf
    set x : Γ(idealPow I n, W.1) :=
      (idealPowAffineSectionsEquiv I n W).symm ⟨f ^ n, Ideal.pow_mem_pow hf n⟩ with hxdef
    set z : Γ(quotientModule I F n, W.1) :=
      restrictSections θ W.1 le_rfl x - restrictSections θ' W.1 le_rfl x with hzdef
    have hxres : (idealPow I n).presheaf.map (homOfLE hDW).op x
        = (X.presheaf.map (homOfLE hDW).op f) ^ n •
            (idealPow I n).presheaf.map (homOfLE hDU).op (oneSection I n) :=
      eq_smul_map_oneSection I n hDU _ (by
        rw [val_map_idealPow, hxdef, idealPowAffineSectionsEquiv_symm_coe, map_pow])
    have hzres : (quotientModule I F n).presheaf.map (homOfLE hDW).op z = 0 := by
      rw [hzdef, map_sub, sub_eq_zero,
        ← restrictSections_res θ (X.basicOpen f) W.1 hDW le_rfl x,
        ← restrictSections_res θ' (X.basicOpen f) W.1 hDW le_rfl x, hxres,
        restrictSections_smul, restrictSections_smul, hagree (X.basicOpen f) hDW hDU]
    obtain ⟨k, hk⟩ :=
      Stacks.AlgebraicGeometry.QcqsLocalization.exists_pow_smul_eq_zero_of_res_eq_zero_of_isCompact
        (quotientModule I F n) W.2.isCompact f rfl hDW z hzres
    refine ⟨k, ?_⟩
    have hval : δ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩
        = (quotientSectionsAffineEquiv I F n hFG W).symm z := by
      rw [hδdef, LinearMap.sub_apply, affineQuotientLinearMap_apply,
        affineQuotientLinearMap_apply, ← map_sub]
    rw [hval, ← map_smul, hk, map_zero]
  obtain ⟨N, hN⟩ := IdealPowerSections.exists_comp_inclusion_eq_zero
    Γ(X, W.1) (I.ideal W) (affineQuotient I F n W) (hFG W) n δ hkey
  let : (idealPow I (n + N)).IsQuasicoherent :=
    Stacks.Algebraization.idealPowerMultiple_isQuasicoherent I (n + N) (structureModule X)
  let := isQuasicoherent_quotientModule I F (n + N) hFG
  refine ⟨N, restrictSections_ext_of_isAffineOpen
    (show IsAffineOpen (W.1 : X.Opens) from W.2) fun y => ?_⟩
  have hinc : idealPowAffineSectionsEquiv I n W
        ((idealPowMap I (Nat.le_add_right n N)).app W.1 y)
      = Submodule.inclusion
          (Ideal.pow_le_pow_right (I := I.ideal W) (Nat.le_add_right n N))
          (idealPowAffineSectionsEquiv I (n + N) W y) :=
    Subtype.ext (val_idealPowMap_app I (Nat.le_add_right n N) W.1 y)
  have hzero : δ (idealPowAffineSectionsEquiv I n W
      ((idealPowMap I (Nat.le_add_right n N)).app W.1 y)) = 0 := by
    rw [hinc]
    simpa using LinearMap.congr_fun hN (idealPowAffineSectionsEquiv I (n + N) W y)
  rw [hδdef, LinearMap.sub_apply, sub_eq_zero, affineQuotientLinearMap_apply,
    affineQuotientLinearMap_apply, LinearEquiv.symm_apply_apply] at hzero
  rw [restrictSections_raiseExponent, restrictSections_raiseExponent,
    (quotientSectionsAffineEquiv I F n hFG W).symm.injective hzero]

end

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
