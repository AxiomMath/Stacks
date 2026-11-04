module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CitedStatements
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocalHigherBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleHigherBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.FirstFailureDiagramNormalization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeUnconditional

/-!
# The cited inputs of the smooth base change theorem that are proved elsewhere

The second proof of the smooth base change theorem ([Stacks, Tag 0EYU]) cites results whose
statements are recorded in `CitedStatements.lean`. Those among them that are proved in the
library are supplied here.

* `flatReducedFibresBaseChangeAt`, `flatReducedFibresBaseChange` — [Stacks, Tag 0EYS], from
  `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_flat_geometricallyReduced`.
* `etaleLocalHigherBaseChange` — [Stacks, Tag 0EZR] (3), from
  `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isIso_local`.
* `higherBaseChangePaste` — [Stacks, Tag 0EZS] for abelian sheaves, from
  `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_paste`.
* `affineCurveCohomologyVanishing` — [Stacks, Tag 03SC] (2), which is [Stacks, Tag 0A54]
  (`Stacks.EtaleCohomology.TorsionSheafSituation.isAffineVanishingAboveDegreeOne`).
* `curveCohomologyAlgClosedInvariance` — [Stacks, Tag 03SC] (6), which is [Stacks, Tag 0A58]
  (`Stacks.EtaleCohomology.TorsionSheafSituation.baseChangePrimeToCharacteristic`).
* `firstFailureNormalization` — [Stacks, Tag 0F08], from
  `Stacks.EtaleCohomology.FirstFailureDiagram.normalFailureDiagram_of_firstFailure`.

## References

* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
* [Stacks Project, Tag 0EYS](https://stacks.math.columbia.edu/tag/0EYS)
* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 0EZS](https://stacks.math.columbia.edu/tag/0EZS)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology.SmoothBaseChange

/-- [Stacks, Tag 0EYS] as an isomorphism of functors: base change for pushforward of sheaves of
sets along a flat morphism locally of finite presentation with geometrically reduced fibres. -/
theorem isIso_smallEtaleSetBaseChange_natTrans_of_flat_geometricallyReduced
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    IsIso (smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm) := by
  have := fun F => isIso_smallEtaleSetBaseChange_of_flat_geometricallyReduced.{u, v} f h e g sq F
  exact NatIso.isIso_of_isIso_app _

/-- [Stacks, Tag 0EYS], in the form of `FlatReducedFibresBaseChangeAt`. -/
theorem flatReducedFibresBaseChangeAt : FlatReducedFibresBaseChangeAt.{u, v} :=
  fun _ _ _ _ f h e g sq _ _ _ =>
    isIso_smallEtaleSetBaseChange_natTrans_of_flat_geometricallyReduced.{u, v} f h e g sq

/-- [Stacks, Tag 0EYS] for sheaves of sets in `Type (u + 1)`. -/
theorem flatReducedFibresBaseChange : FlatReducedFibresBaseChange.{u} :=
  flatReducedFibresBaseChangeAt.{u, 0}

/-- [Stacks, Tag 0EZR], part (3): higher base change is étale local on the source. -/
theorem etaleLocalHigherBaseChange : EtaleLocalHigherBaseChange.{u} :=
  fun D q h => isIso_higherBaseChangeMapAb_app_of_isIso_local D q h

/-- [Stacks, Tag 0EZS] for abelian sheaves: higher base change for a pasting of two squares. -/
theorem higherBaseChangePaste : HigherBaseChangePaste.{u} :=
  fun _ _ _ _ _ _ g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ q F h₁ h₂ =>
    isIso_higherBaseChangeMapAb_app_of_paste g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ q F h₁ h₂

/-- [Stacks, Tag 03SC] (2): the étale cohomology of a torsion sheaf on an affine curve over an
algebraically closed field vanishes above degree one. -/
theorem affineCurveCohomologyVanishing : AffineCurveCohomologyVanishing.{u} := by
  intro k _ _ X π _ _ _ hdim hX _ F hF q hq
  let S : TorsionSheafSituation.{u, 0} :=
    { k := k, X := X, structureMorphism := π, dimension_le_one := hdim, F := F, isTorsion := hF }
  exact S.isAffineVanishingAboveDegreeOne hX q hq

/-- [Stacks, Tag 03SC] (6): for a sheaf of torsion prime to the characteristic on a curve over an
algebraically closed field `k`, étale cohomology does not change under extension to an
algebraically closed field `k' ⊇ k`. -/
theorem curveCohomologyAlgClosedInvariance : CurveCohomologyAlgClosedInvariance.{u} := by
  intro k k' _ _ _ _ _ X π _ _ _ hdim _ _ F hF q
  have hcop : ∀ n : ℕ, (ringChar k = 0 ∨ n.Coprime (ringChar k)) →
      n.Coprime (ringExpChar k) := by
    intro n hn
    rcases Nat.eq_zero_or_pos (ringChar k) with h0 | h0
    · rw [ringExpChar, h0]
      exact Nat.coprime_one_right n
    · rw [ringExpChar, max_eq_left h0]
      exact hn.resolve_left h0.ne'
  have hprime : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology
      (ringExpChar k) F := by
    intro U a
    obtain ⟨n, hn, hc, ha⟩ := hF U a
    refine ⟨⊤, X.smallEtaleTopology.top_mem U, fun V f _ => ⟨n, hn, hcop n hc, ?_⟩⟩
    rw [← map_nsmul, ha, map_zero]
  let S : TorsionSheafSituation.{u, 0} :=
    { k := k, X := X, structureMorphism := π, dimension_le_one := hdim, F := F,
      isTorsion := Stacks.Torsion.torsionSheafProperty_of_isPrimeToCharacteristicTorsion _ hprime }
  exact S.baseChangePrimeToCharacteristic hprime k' q

/-- [Stacks, Tag 0F08]: a first failure of base change is realized by a normal failure diagram. -/
theorem firstFailureNormalization : FirstFailureNormalization.{u} :=
  fun _ _ f n q hprev hfail =>
    FirstFailureDiagram.normalFailureDiagram_of_firstFailure f n q hprev hfail

end Stacks.EtaleCohomology.SmoothBaseChange

end
