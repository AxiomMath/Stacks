module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.LowerShriekExtendScalarsIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.Vanishing
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CoefficientUniverseTransfer
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Remark 0GL6: `Rf_!` commutes with derived extension of coefficients

Let `φ : Λ₁ → Λ₂` be a homomorphism of commutative rings with `Λ₁` torsion, `f : X ⟶ Y` a
morphism of schemes with `Y` quasi-compact and `j` a compactification of `X` over `Y`, so that
`Rf_! = R(f̄)_* ∘ j_!` as in [Stacks, Tag 0F7H].  The second diagram of [Stacks, Remark 0GL6] says
that the comparison `Rf_!(E) ⊗^L_{Λ₁} Λ₂ ⟶ Rf_!(E ⊗^L_{Λ₁} Λ₂)` is an isomorphism.

## Main results

* `Stacks.EtaleCohomology.isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_properBaseChange`:
  the second diagram from any proof of the statement of [Stacks, Tag 095T] in the form
  `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isProper`.
* `Stacks.EtaleCohomology.isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_torsion`: **the
  second diagram of [Stacks, Remark 0GL6]**, the previous theorem applied to
  `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isProper` (Tag 095T).
* `Stacks.EtaleCohomology.derivedLowerShriekUnbounded_commutes_restrictScalars_and_extendScalars`:
  **[Stacks, Remark 0GL6]**, both diagrams, the first being
  `Stacks.EtaleCohomology.derivedLowerShriekUnboundedRestrictScalarsIso`.

## Implementation notes

Tag 095T is stated with coefficients in `AddCommGrpCat.{u + 1}`; it extends to the coefficient
universe of `Λ₁` by `CohomologyCommutesWithBaseChange.of_univ_zero`.  The cohomology of proper
curves over algebraically closed fields vanishes above degree two by [Stacks, Tag 0A53]
(`TorsionSheafSituation.isVanishingAboveDegreeTwo`).  Together they bound the cohomological
dimension of `R(f̄)_*` on torsion sheaves ([Stacks, Tag 095U]), which makes the projection
formula comparison for `R(f̄)_*` invertible ([Stacks, Tag 0GL5]).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-- **The second diagram of [Stacks, Remark 0GL6] from the statement of Tag 095T.**  Let
`φ : Λ₁ → Λ₂` be a homomorphism of commutative rings with `Λ₁` torsion, `f : X ⟶ Y` a morphism of
schemes with `Y` quasi-compact and `j` a compactification of `X` over `Y`.  Then, for any proof
`h095T` of the statement of [Stacks, Tag 095T] in the form of
`Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isProper`, the comparison
`Rf_!(E) ⊗^L_{Λ₁} Λ₂ ⟶ Rf_!(E ⊗^L_{Λ₁} Λ₂)` is an isomorphism.

The statement of Tag 095T extends to the coefficient universe of `Λ₁` by
`CohomologyCommutesWithBaseChange.of_univ_zero`; the vanishing on proper curves over
algebraically closed fields is [Stacks, Tag 0A53]
(`TorsionSheafSituation.isVanishingAboveDegreeTwo`); [Stacks, Tag 095U] then bounds the
cohomological dimension of `R(f̄)_*` and the comparison is invertible.
`isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_torsion` applies it to Tag 095T itself. -/
theorem isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_properBaseChange
    (h095T : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] {X' Y' : Scheme.{u}} (g : Y' ⟶ Y)
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback g' f' f g)
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (_hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F),
      IsIso (etaleAbelianSheafDerivedBaseChange.{u, 0} f g g' f' sq.w F))
    (hΛ₁ : ∀ x : Λ₁, ∃ n : ℕ, 0 < n ∧ (n : Λ₁) * x = 0)
    {X Y : Scheme.{u}} [CompactSpace Y] (f : X ⟶ Y) (j : CompactificationOf (Over.mk f)) :
    IsIso (derivedLowerShriekUnboundedExtendScalarsMap.{u, r} φ f j) := by
  have hpbc : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p := fun _ _ p _ ↦
    have : QuasiSeparated p := IsSeparated.instQuasiSeparated p
    CohomologyCommutesWithBaseChange.of_univ_zero fun _ _ g g' f' sq F hF ↦
      h095T p g g' f' sq F hF
  have hcurve : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      (π : X ⟶ Spec (.of k)) [IsProper π], topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞) →
      ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
        Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
        ∀ q : ℕ, 2 * 1 < q →
          let := isGrothendieckAbelian_sheaf_smallEtale.{u, r} X
          let := IsGrothendieckAbelian.hasExt.{max (u + 1) r}
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})
          Subsingleton (Sheaf.H.{max (u + 1) r} G q) := by
    intro k _ _ X π _ hX G hG q hq _ _
    let S : TorsionSheafSituation.{u, r} :=
      { k := k, X := X, structureMorphism := π, dimension_le_one := hX, F := G, isTorsion := hG }
    exact S.isVanishingAboveDegreeTwo q (by omega)
  -- given by its term: in this module's import closure instance search for
  -- `QuasiSeparated j.toBase` runs out of heartbeats
  have : QuasiSeparated j.toBase := IsSeparated.instQuasiSeparated j.toBase
  obtain ⟨N, hN⟩ := @AlgebraicGeometry.exists_topologicalKrullDim_fiber_le _ _ j.toBase
    (IsProper.toLocallyOfFiniteType (f := j.toBase))
    (@AlgebraicGeometry.instQuasiCompactOfUniversallyClosed _ _ _
      (IsProper.toUniversallyClosed (f := j.toBase))) ‹_›
  have := isIso_derivedDirectImageUnboundedExtendScalarsMap φ j.toBase
    ⟨2 * N + 1, fun q hq F ↦ isZero_rightDerived_etaleModuleDirectImage_of_abelian Λ₁ hΛ₁
      j.toBase q (fun G hG ↦
        isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim_of_curve.{u, r} hpbc
          hcurve j.toBase N hN G hG q (by omega)) F⟩
  have : ∀ E, IsIso ((derivedLowerShriekUnboundedExtendScalarsMap.{u, r} φ f j).app E) :=
    fun E => isIso_derivedLowerShriekUnboundedExtendScalarsMap_app_of_isIso φ f j E
      inferInstance inferInstance
  exact NatIso.isIso_of_isIso_app _

/-- **The second diagram of [Stacks, Remark 0GL6].**  Let `φ : Λ₁ → Λ₂` be a homomorphism of
commutative rings with `Λ₁` torsion, `f : X ⟶ Y` a morphism of schemes with `Y` quasi-compact and
`j` a compactification of `X` over `Y`, so that `Rf_! = R(f̄)_* ∘ j_!` as in [Stacks, Tag 0F7H].
Then the comparison `Rf_!(E) ⊗^L_{Λ₁} Λ₂ ⟶ Rf_!(E ⊗^L_{Λ₁} Λ₂)`, natural in
`E ∈ D(X_étale, Λ₁)`, is an isomorphism: the square of `Rf_!` and `- ⊗^L_{Λ₁} Λ₂` commutes.

This is `isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_properBaseChange` applied to the
proper base change theorem, [Stacks, Tag 095T]
(`Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isProper`). -/
@[stacks 0GL6 "diagram (2): Rf_! commutes with - ⊗^L_{Λ₁} Λ₂", sga "4 XVII 5.2.2" "special case"]
theorem isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_torsion
    (hΛ₁ : ∀ x : Λ₁, ∃ n : ℕ, 0 < n ∧ (n : Λ₁) * x = 0)
    {X Y : Scheme.{u}} [CompactSpace Y] (f : X ⟶ Y) (j : CompactificationOf (Over.mk f)) :
    IsIso (derivedLowerShriekUnboundedExtendScalarsMap.{u, r} φ f j) :=
  isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_properBaseChange φ
    (fun {_ _} f _ {_ _} g g' f' sq F hF ↦
      isIso_etaleAbelianSheafDerivedBaseChange_of_isProper f g g' f' sq F hF)
    hΛ₁ f j

/-- **[Stacks, Remark 0GL6], both diagrams.**  Let `φ : Λ₁ → Λ₂` be a homomorphism of commutative
rings with `Λ₁` torsion, `f : X ⟶ Y` a morphism of schemes with `Y` quasi-compact and `j` a
compactification of `X` over `Y`, so that `Rf_! = R(f̄)_* ∘ j_!` as in [Stacks, Tag 0F7H].  Then
1. `Rf_!` commutes with restriction of coefficients: `res_φ ∘ Rf_! ≅ Rf_! ∘ res_φ` as functors
   `D(X_étale, Λ₂) ⥤ D(Y_étale, Λ₁)` (`derivedLowerShriekUnboundedRestrictScalarsIso`);
2. `Rf_!` commutes with derived extension of coefficients:
   `Rf_!(-) ⊗^L_{Λ₁} Λ₂ ≅ Rf_!(- ⊗^L_{Λ₁} Λ₂)` as functors `D(X_étale, Λ₁) ⥤ D(Y_étale, Λ₂)`
   (`isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_torsion`). -/
@[stacks 0GL6]
theorem derivedLowerShriekUnbounded_commutes_restrictScalars_and_extendScalars
    (hΛ₁ : ∀ x : Λ₁, ∃ n : ℕ, 0 < n ∧ (n : Λ₁) * x = 0)
    {X Y : Scheme.{u}} [CompactSpace Y] (f : X ⟶ Y) (j : CompactificationOf (Over.mk f)) :
    Nonempty (derivedLowerShriekUnbounded.{u, r} f j Λ₂ ⋙
        etaleModuleDerivedRestrictScalars.{u, r} φ Y ≅
      etaleModuleDerivedRestrictScalars.{u, r} φ X ⋙ derivedLowerShriekUnbounded.{u, r} f j Λ₁) ∧
    Nonempty (derivedLowerShriekUnbounded.{u, r} f j Λ₁ ⋙
        etaleModuleDerivedExtendScalars.{u, r} φ Y ≅
      etaleModuleDerivedExtendScalars.{u, r} φ X ⋙ derivedLowerShriekUnbounded.{u, r} f j Λ₂) :=
  have := isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_torsion φ hΛ₁ f j
  ⟨⟨derivedLowerShriekUnboundedRestrictScalarsIso.{u, r} φ f j⟩,
    ⟨asIso (derivedLowerShriekUnboundedExtendScalarsMap.{u, r} φ f j)⟩⟩

end Stacks.EtaleCohomology

end
