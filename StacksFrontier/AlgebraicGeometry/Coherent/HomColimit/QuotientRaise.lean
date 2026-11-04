module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.QuotientColimit
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescent

/-!
# Raising the exponent of a local morphism `Iⁿ|_O ⟶ (F/F_n)|_O`

Let `X` be a scheme, let `I` be a quasi-coherent sheaf of ideals, let `F` be an `𝒪_X`-module and
let `F_n` be the subsheaf of sections annihilated by `Iⁿ`.  The surjectivity half of
[Stacks, Tag 01PQ] produces a morphism `θ : Iⁿ|_O ⟶ (F/F_n)|_O` over each member `O` of an
affine covering, with an exponent `n` depending on the member, and then has to compare them on
the overlaps.  Both steps need the same elementary operation: carrying `θ` to an exponent
`m ≥ n`, by precomposing with the inclusion `I^m ⟶ Iⁿ` and postcomposing with the projection
`F/F_n ⟶ F/F_m`.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.raiseExponent`: the morphism
  `I^m|_O ⟶ (F/F_m)|_O` attached to `θ : Iⁿ|_O ⟶ (F/F_n)|_O` and an inequality `n ≤ m`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.restrictSections_raiseExponent`: its action on
  sections, which is the form every consumer uses.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.raiseExponent_raiseExponent`: raising twice is
  raising once, so an equality obtained at one exponent persists at every larger one.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.restrictTo_raiseExponent`: raising commutes with
  restricting to a smaller open.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.restrictSections_raiseExponent_oneSection_eq`:
  **raising preserves the value on the unit section.**  If `θ` sends the unit section of `Iⁿ` to
  the class of a section `s` of `F` over every open of `O` missing the support of `I`, then the
  raised morphism sends the unit section of `I^m` to the class of `s` there.

## Implementation notes

Everything is proved on sections, through
`Stacks.AlgebraicGeometry.ModuleLimits.restrictSections_comp` and
`Stacks.AlgebraicGeometry.ModuleLimits.restrictSections_restrictFunctor_map`, and the two
compatibilities are then deduced from
`Stacks.AlgebraicGeometry.ModuleLimits.restrictSections_ext` rather than from the functoriality
of `AlgebraicGeometry.Scheme.Modules.restrictFunctor`; this keeps the argument free of the
transports between `Γ(M.restrict O.ι, U')` and `Γ(M, O.ι ''ᵁ U')`.

The value on the unit section is preserved because the inclusion `I^m ⟶ Iⁿ` carries the unit
section of `I^m` to that of `Iⁿ` (`idealPowMap_app_oneSection`, both powers being the whole
structure sheaf away from the support of `I`) and because `F ⟶ F/F_n ⟶ F/F_m` is `F ⟶ F/F_m`
(`quotientπ_comp_quotientMap`).

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### The raised morphism -/

/-- **Raising the exponent of a local morphism.** For `n ≤ m` the morphism
`I^m|_O ⟶ (F/F_m)|_O` obtained from `θ : Iⁿ|_O ⟶ (F/F_n)|_O` by precomposing with the inclusion
`I^m ⟶ Iⁿ` and postcomposing with the projection `F/F_n ⟶ F/F_m`. -/
noncomputable def raiseExponent (I : X.IdealSheafData) (F : X.Modules) {n m : ℕ} (h : n ≤ m)
    (O : X.Opens)
    (θ : Scheme.Modules.restrict (idealPow I n) O.ι ⟶
      Scheme.Modules.restrict (quotientModule I F n) O.ι) :
    Scheme.Modules.restrict (idealPow I m) O.ι ⟶
      Scheme.Modules.restrict (quotientModule I F m) O.ι :=
  (Scheme.Modules.restrictFunctor O.ι).map (idealPowMap I h) ≫ θ ≫
    (Scheme.Modules.restrictFunctor O.ι).map (quotientMap I F h)

/-- The action of the raised morphism on sections. -/
theorem restrictSections_raiseExponent (I : X.IdealSheafData) (F : X.Modules) {n m : ℕ}
    (h : n ≤ m) (O : X.Opens)
    (θ : Scheme.Modules.restrict (idealPow I n) O.ι ⟶
      Scheme.Modules.restrict (quotientModule I F n) O.ι)
    (U : X.Opens) (hU : U ≤ O) (x : Γ(idealPow I m, U)) :
    restrictSections (raiseExponent I F h O θ) U hU x
      = (quotientMap I F h).app U
          (restrictSections θ U hU ((idealPowMap I h).app U x)) := by
  unfold raiseExponent
  rw [restrictSections_comp, restrictSections_comp, restrictSections_restrictFunctor_map,
    restrictSections_restrictFunctor_map]

/-- Raising from `n` to `m` and then from `m` to `p` is raising from `n` to `p`. -/
theorem raiseExponent_raiseExponent (I : X.IdealSheafData) (F : X.Modules) {n m p : ℕ}
    (h₁ : n ≤ m) (h₂ : m ≤ p) (O : X.Opens)
    (θ : Scheme.Modules.restrict (idealPow I n) O.ι ⟶
      Scheme.Modules.restrict (quotientModule I F n) O.ι) :
    raiseExponent I F h₂ O (raiseExponent I F h₁ O θ)
      = raiseExponent I F (h₁.trans h₂) O θ := by
  refine restrictSections_ext fun U hU x => ?_
  rw [restrictSections_raiseExponent, restrictSections_raiseExponent,
    restrictSections_raiseExponent]
  have hI : (idealPowMap I h₁).app U ((idealPowMap I h₂).app U x)
      = (idealPowMap I (h₁.trans h₂)).app U x := by
    rw [← idealPowMap_comp I h₁ h₂]
    rfl
  rw [hI, ← quotientMap_comp I F h₁ h₂]
  rfl

/-- Raising the exponent commutes with restricting to a smaller open. -/
theorem restrictTo_raiseExponent (I : X.IdealSheafData) (F : X.Modules) {n m : ℕ} (h : n ≤ m)
    {O O' : X.Opens} (hO : O' ≤ O)
    (θ : Scheme.Modules.restrict (idealPow I n) O.ι ⟶
      Scheme.Modules.restrict (quotientModule I F n) O.ι) :
    restrictTo hO (raiseExponent I F h O θ)
      = raiseExponent I F h O' (restrictTo hO θ) := by
  refine restrictSections_ext fun U hU x => ?_
  rw [restrictSections_restrictTo, restrictSections_raiseExponent,
    restrictSections_raiseExponent, restrictSections_restrictTo]

/-! ### Raising preserves the value on the unit section -/

/-- **Raising the exponent preserves the value on the unit section.** If `θ : Iⁿ|_O ⟶ (F/F_n)|_O`
sends the unit section of `Iⁿ` to the class of `s ∈ Γ(X ∖ V(I), F)` over every open of `O`
missing the support of `I`, then for `n ≤ m` the raised morphism `I^m|_O ⟶ (F/F_m)|_O` sends the
unit section of `I^m` to the class of `s` over every such open.

This is the bookkeeping that lets a family of local morphisms with member-dependent exponents be
brought to one common exponent before being glued. -/
theorem restrictSections_raiseExponent_oneSection_eq (I : X.IdealSheafData) (F : X.Modules)
    {n m : ℕ} (h : n ≤ m) (O : X.Opens)
    (θ : Scheme.Modules.restrict (idealPow I n) O.ι ⟶
      Scheme.Modules.restrict (quotientModule I F n) O.ι)
    (s : Γ(F, (I.support.compl : X.Opens)))
    (hθ : ∀ (V : X.Opens) (hVO : V ≤ O) (hVU : V ≤ (I.support.compl : X.Opens)),
      restrictSections θ V hVO ((idealPow I n).presheaf.map (homOfLE hVU).op (oneSection I n))
        = (quotientπ I F n).app V (F.presheaf.map (homOfLE hVU).op s))
    (V : X.Opens) (hVO : V ≤ O) (hVU : V ≤ (I.support.compl : X.Opens)) :
    restrictSections (raiseExponent I F h O θ) V hVO
        ((idealPow I m).presheaf.map (homOfLE hVU).op (oneSection I m))
      = (quotientπ I F m).app V (F.presheaf.map (homOfLE hVU).op s) := by
  rw [restrictSections_raiseExponent]
  have hone : (idealPowMap I h).app V
        ((idealPow I m).presheaf.map (homOfLE hVU).op (oneSection I m))
      = (idealPow I n).presheaf.map (homOfLE hVU).op (oneSection I n) := by
    rw [← app_naturality (idealPowMap I h) hVU (oneSection I m), idealPowMap_app_oneSection]
  rw [hone, hθ V hVO hVU]
  conv_rhs => rw [← quotientπ_comp_quotientMap I F h]
  rfl

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
