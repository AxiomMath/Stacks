module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.QuotientColimit
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineRestrictSections

/-!
# A module map over an affine open as a morphism `Iⁿ|_W ⟶ (F/F_n)|_W`

Let `X` be a scheme, let `I` be a quasi-coherent sheaf of ideals of finite type, let `F` be a
quasi-coherent `𝒪_X`-module and let `F_n` be the subsheaf of sections annihilated by `Iⁿ`. Over
an affine open `W`, a `Γ(X, W)`-linear map

`I(W)ⁿ ⟶ Γ(F, W) / {x | I(W)ⁿ x = 0}`

is the action on sections of a morphism `Iⁿ|_W ⟶ (F/F_n)|_W` of `𝒪_X`-modules, and that morphism
is unique. This is the affine step of the surjectivity half of [Stacks, Tag 01PQ], compare
[Stacks, Tag 01PM].

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowAffineSectionsEquiv`: the sections of `Iⁿ`
  over an affine open `W` are the ideal `I(W)ⁿ`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_restrictSections_eq_of_affineQuotientHom`:
  a `Γ(X, W)`-linear map `I(W)ⁿ → Γ(F, W)/Γ(F, W)_n` is the value at `W` of the sectionwise
  family of a morphism `Iⁿ|_W ⟶ (F/F_n)|_W`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.restrictSections_ext_of_affineQuotientHom`: two
  such morphisms whose sectionwise families agree at `W` are equal.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_sectionFamily_eq_of_affineQuotientHom`: such
  a linear map is the value at `W` of a family of maps `Γ(Iⁿ, U) → Γ(F/F_n, U)`, one for each open
  `U ≤ W`, additive, `Γ(X, U)`-homogeneous and compatible with restriction.

## Implementation notes

Both halves are `Stacks.AlgebraicGeometry.ModuleLimits.exists_restrictSections_eq_of_isAffineOpen`
and `Stacks.AlgebraicGeometry.ModuleLimits.restrictSections_ext_of_isAffineOpen`, the fullness
and faithfulness of `Γ(-, W)` on morphisms of quasi-coherent modules over an affine open `W`,
conjugated by two identifications of sections:

* the sections of `Iⁿ` over an affine open are `I(W)ⁿ`
  (`Stacks.AlgebraicGeometry.IdealPowerColimit.obj_idealPow_affineOpen`), for `Iⁿ` encoded as
  `idealPowerMultiple` rather than `AlgebraicGeometry.idealPower`;
* the sections of `F/F_n` over an affine open are `Γ(F, W)/Γ(F, W)_n`
  (`Stacks.AlgebraicGeometry.IdealPowerColimit.quotientSectionsAffineEquiv`).

The finite-type hypothesis on `I` enters only through the second one: it is what makes `F_n`,
hence `F/F_n`, quasi-coherent.

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

/-! ### The sections of `Iⁿ` over an affine open -/

/-- The sections of `Iⁿ` over an affine open `W`, identified with the ideal `I(W)ⁿ`. -/
noncomputable def idealPowAffineSectionsEquiv (I : X.IdealSheafData) (n : ℕ)
    (W : X.affineOpens) :
    Γ(idealPow I n, W.1) ≃ₗ[Γ(X, W.1)] ↥(I.ideal W ^ n : Ideal Γ(X, W.1)) :=
  LinearEquiv.ofEq _ _ (obj_idealPow_affineOpen I n W)

/-- The element of `I(W)ⁿ` attached to a section of `Iⁿ` over `W` is that section, viewed as a
section of `𝒪_X`. -/
@[simp]
theorem idealPowAffineSectionsEquiv_coe (I : X.IdealSheafData) (n : ℕ) (W : X.affineOpens)
    (x : Γ(idealPow I n, W.1)) :
    ((idealPowAffineSectionsEquiv I n W x : Γ(X, W.1))) = (x.1 : Γ(X, W.1)) := rfl

/-! ### The quotient `F / F_n` over an affine open -/

section

variable (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
  (hFG : ∀ V : X.affineOpens, (I.ideal V).FG) (n : ℕ) (W : X.affineOpens)

/-- The identification of the sections of `F/F_n` over an affine open with `Γ(F, W)/Γ(F, W)_n`
carries the class of a section of `F` to its image under the projection `F ⟶ F/F_n`. -/
@[simp]
theorem quotientSectionsAffineEquiv_mkQ (y : Γ(F, W.1)) :
    quotientSectionsAffineEquiv I F n hFG W
        (Submodule.mkQ (Submodule.torsionBySet Γ(X, W.1) Γ(F, W.1)
          ((I.ideal W ^ n : Ideal Γ(X, W.1)) : Set Γ(X, W.1))) y)
      = (quotientπ I F n).app W.1 y := by
  unfold quotientSectionsAffineEquiv
  simp only [LinearEquiv.trans_apply, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk]
  rfl

/-- Abbreviation for the module `Γ(F, W)/Γ(F, W)_n` of the affine statement of
[Stacks, Tag 01PM]: the sections of `F` over `W` modulo those annihilated by `I(W)ⁿ`. -/
noncomputable abbrev affineQuotient : Type u :=
  Γ(F, W.1) ⧸ Submodule.torsionBySet Γ(X, W.1) Γ(F, W.1)
    ((I.ideal W ^ n : Ideal Γ(X, W.1)) : Set Γ(X, W.1))

/-- The `Γ(X, W)`-linear map on sections over an affine open `W` attached to a module map
`I(W)ⁿ → Γ(F, W)/Γ(F, W)_n`. -/
noncomputable def affineQuotientHomOnSections
    (φ : ↥(I.ideal W ^ n : Ideal Γ(X, W.1)) →ₗ[Γ(X, W.1)] affineQuotient I F n W) :
    Γ(idealPow I n, W.1) →ₗ[Γ(X, W.1)] Γ(quotientModule I F n, W.1) :=
  ((quotientSectionsAffineEquiv I F n hFG W).toLinearMap.comp φ).comp
    (idealPowAffineSectionsEquiv I n W).toLinearMap

/-- The map `affineQuotientHomOnSections` sends a section `x` of `Iⁿ` over `W` to the image of
`φ x` in the sections of `F/F_n` over `W`. -/
@[simp]
theorem affineQuotientHomOnSections_apply
    (φ : ↥(I.ideal W ^ n : Ideal Γ(X, W.1)) →ₗ[Γ(X, W.1)] affineQuotient I F n W)
    (x : Γ(idealPow I n, W.1)) :
    affineQuotientHomOnSections I F hFG n W φ x
      = quotientSectionsAffineEquiv I F n hFG W (φ (idealPowAffineSectionsEquiv I n W x)) :=
  rfl

/-! ### Fullness and faithfulness over an affine open -/

/-- Over an affine open `W`, a `Γ(X, W)`-linear map `I(W)ⁿ → Γ(F, W)/Γ(F, W)_n` is the value at
`W` of the sectionwise family of a morphism `Iⁿ|_W ⟶ (F/F_n)|_W`. -/
theorem exists_restrictSections_eq_of_affineQuotientHom
    (φ : ↥(I.ideal W ^ n : Ideal Γ(X, W.1)) →ₗ[Γ(X, W.1)] affineQuotient I F n W) :
    ∃ θ : Scheme.Modules.restrict (idealPow I n) W.1.ι ⟶
        Scheme.Modules.restrict (quotientModule I F n) W.1.ι,
      ∀ x : Γ(idealPow I n, W.1),
        restrictSections θ W.1 le_rfl x
          = quotientSectionsAffineEquiv I F n hFG W
              (φ (idealPowAffineSectionsEquiv I n W x)) := by
  let := isQuasicoherent_quotientModule I F n hFG
  let : (idealPow I n).IsQuasicoherent :=
    Stacks.Algebraization.idealPowerMultiple_isQuasicoherent I n (structureModule X)
  exact exists_restrictSections_eq_of_isAffineOpen
    (show IsAffineOpen (W.1 : X.Opens) from W.2) (affineQuotientHomOnSections I F hFG n W φ)

/-- Two morphisms `Iⁿ|_W ⟶ (F/F_n)|_W` over an affine open whose sectionwise families agree at
`W` are equal. -/
theorem restrictSections_ext_of_affineQuotientHom
    {θ θ' : Scheme.Modules.restrict (idealPow I n) W.1.ι ⟶
      Scheme.Modules.restrict (quotientModule I F n) W.1.ι}
    (hFG' : ∀ V : X.affineOpens, (I.ideal V).FG)
    (h : ∀ x : Γ(idealPow I n, W.1),
      restrictSections θ W.1 le_rfl x = restrictSections θ' W.1 le_rfl x) :
    θ = θ' := by
  let := isQuasicoherent_quotientModule I F n hFG'
  let : (idealPow I n).IsQuasicoherent :=
    Stacks.Algebraization.idealPowerMultiple_isQuasicoherent I n (structureModule X)
  exact restrictSections_ext_of_isAffineOpen
    (show IsAffineOpen (W.1 : X.Opens) from W.2) h

/-- Over an affine open `W`, a `Γ(X, W)`-linear map `φ : I(W)ⁿ → Γ(F, W)/Γ(F, W)_n` is the value
at `W` of a family of maps `Γ(Iⁿ, U) → Γ(F/F_n, U)`, one for each open `U ≤ W`, which are
additive, `Γ(X, U)`-homogeneous and compatible with restriction. -/
theorem exists_sectionFamily_eq_of_affineQuotientHom
    (φ : ↥(I.ideal W ^ n : Ideal Γ(X, W.1)) →ₗ[Γ(X, W.1)] affineQuotient I F n W) :
    ∃ t : ∀ U : X.Opens, U ≤ W.1 → Γ(idealPow I n, U) → Γ(quotientModule I F n, U),
      (∀ (U : X.Opens) (h : U ≤ W.1) (x y : Γ(idealPow I n, U)),
        t U h (x + y) = t U h x + t U h y) ∧
      (∀ (U : X.Opens) (h : U ≤ W.1) (r : Γ(X, U)) (x : Γ(idealPow I n, U)),
        t U h (r • x) = r • t U h x) ∧
      (∀ (U V : X.Opens) (hUV : U ≤ V) (hV : V ≤ W.1) (x : Γ(idealPow I n, V)),
        t U (hUV.trans hV) ((idealPow I n).presheaf.map (homOfLE hUV).op x)
          = (quotientModule I F n).presheaf.map (homOfLE hUV).op (t V hV x)) ∧
      ∀ x : Γ(idealPow I n, W.1),
        t W.1 le_rfl x
          = quotientSectionsAffineEquiv I F n hFG W
              (φ (idealPowAffineSectionsEquiv I n W x)) := by
  obtain ⟨θ, hθ⟩ := exists_restrictSections_eq_of_affineQuotientHom I F hFG n W φ
  exact ⟨restrictSections θ, restrictSections_add θ, restrictSections_smul θ,
    restrictSections_res θ, hθ⟩

end

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
