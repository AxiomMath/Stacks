module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AnnihilatedSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.HigherDirectImageFilteredColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.TorsionExhaustion

/-!
# The smooth base change theorem

Stacks, Theorem 0EYU: in a cartesian square of schemes
```
X  ←-h-  Y
|f       |e
S  ←-g-  T
```
with `f` smooth and `g` quasi-compact and quasi-separated,
`f⁻¹ R^q g_* F = R^q h_* e⁻¹ F` for every `q` and every abelian sheaf `F` on `T_étale` all of whose
stalks at geometric points are torsion of orders invertible on `S`.

The second proof of the source is followed. A sheaf `F` with such stalks is the filtered colimit
of its subsheaves `F[n]`, `n` invertible on `S`
(`Stacks.EtaleCohomology.SmoothBaseChange.isColimitTorsionCocone`); inverse images commute with
colimits and higher direct images along quasi-compact quasi-separated morphisms commute with
filtered colimits (Stacks 0H7B, 03Q5), so it suffices to treat `F[n]`, which is
`Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_of_smooth_of_zsmul_eq_zero`.
The source cites Lemma 09Z1 for the commutation with colimits; its special case for a constant
system of schemes is what is used, and it is proved here from Stacks 0H7B and 03Q5.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_of_smooth` — the smooth
  base change theorem, from the cited inputs of `CitedStatements.lean` and the Noetherian case of
  Stacks 0EYJ (`h0EYD`); the degree-one vanishing `AffineLineFirstVanishing` is
  supplied by `affineLineFirstVanishing`, with 0EZJ from
  `AlgebraicGeometry.exists_finiteEtaleGaloisCover_extending_genericFiber`.

## References

* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

/-- The `n`-torsion subsheaf of an abelian sheaf is annihilated by `n`. -/
theorem zsmul_kernel_eq_zero {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J Ab.{u + 1}] (F : Sheaf J Ab.{u + 1}) (n : ℤ) (U : Cᵒᵖ)
    (x : (kernel (n • 𝟙 F)).obj.obj U) : n • x = 0 := by
  refine (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff _ n).1 ?_ U x
  rw [← cancel_mono (kernel.ι (n • 𝟙 F)), Preadditive.zsmul_comp, Category.id_comp,
    zero_comp, ← Category.comp_id (kernel.ι (n • 𝟙 F)), ← Preadditive.comp_zsmul,
    kernel.condition]

/-- **The smooth base change theorem** (Stacks, Theorem 0EYU), from the inputs cited by its
second proof (Stacks 0EYS, 0EZR, 0EZS, 0F08, 03SC (2) and (6), and 0EZJ from its Noetherian
case 0EYJ). In a cartesian square
```
X  ←-h-  Y
|f       |e
S  ←-g-  T
```
with `f` smooth and `g` quasi-compact and quasi-separated, the base change map
`f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism for every `q` and every abelian sheaf `F` on
`T_étale` all of whose stalks at geometric points are torsion of orders invertible on `S`. -/
theorem isIso_higherBaseChangeMapAb_of_smooth
    (h0EYS : FlatReducedFibresBaseChange.{u}) (h0EZR : EtaleLocalHigherBaseChange.{u})
    (h0EZS : HigherBaseChangePaste.{u}) (h0F08 : FirstFailureNormalization.{u})
    (h03SC2 : AffineCurveCohomologyVanishing.{u}) (h03SC6 : CurveCohomologyAlgClosedInvariance.{u})
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : ∀ (t : GeometricPoint T) (a : (smallEtaleStalkAb t.hom).obj F),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(S, ⊤)) ∧ n • a = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMapAb f g h e sq.w q).app F) := by
  have : QuasiCompact h := MorphismProperty.of_isPullback sq.flip ‹_›
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq.flip ‹_›
  let D := torsionDiagram F S
  have : PreservesColimit D ((smallEtalePushforwardAb g).rightDerived q) :=
    preservesColimit_rightDerived_smallEtalePushforwardAb g q D
  have : PreservesColimit (D ⋙ smallEtalePullbackAb e)
      ((smallEtalePushforwardAb h).rightDerived q) :=
    preservesColimit_rightDerived_smallEtalePushforwardAb h q _
  have : PreservesColimitsOfSize.{u + 1, u + 1} (smallEtalePullbackAb f) :=
    (smallEtaleAdjunctionAb f).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u + 1, u + 1} (smallEtalePullbackAb e) :=
    (smallEtaleAdjunctionAb e).leftAdjoint_preservesColimits
  refine isIso_app_of_isColimit (isColimitTorsionCocone S F hF)
    (higherBaseChangeMapAb f g h e sq.w q) fun k => ?_
  exact isIso_higherBaseChangeMapAb_of_smooth_of_zsmul_eq_zero h0EYS h0EZR h0EZS h0F08 h03SC2
    h03SC6 h0EYD f h e g sq (isUnit_invertibleIndex S k.down) (D.obj k)
    (fun U x => zsmul_kernel_eq_zero F _ (op U) x) q

end Stacks.EtaleCohomology.SmoothBaseChange

end
