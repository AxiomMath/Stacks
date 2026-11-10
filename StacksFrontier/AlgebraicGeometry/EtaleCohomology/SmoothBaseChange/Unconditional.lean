module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Theorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CitedInputs
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularPurity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullbackRamification
public import StacksCore.Tactic.StacksAttribute

/-!
# The smooth base change theorem

[Stacks, Theorem 0EYU]: in a cartesian square of schemes with `f` smooth and `g` quasi-compact
and quasi-separated, the base change map `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism for
every `q` and every abelian sheaf `F` on `T_étale` all of whose stalks at geometric points are
torsion of orders invertible on `S`.

This is `Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_of_smooth` (the
second proof of the source) with each of its cited inputs supplied by a proved theorem:
[Stacks, Tags 0EYS, 0EZR, 0EZS, 0F08 and 03SC (2), (6)] from `CitedInputs.lean` and the tame
half of [Stacks, Tag 0EYD]
(`Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne`) for the Noetherian
case of [Stacks, Tag 0EYJ].

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth`

## References

* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

/-- **The smooth base change theorem** ([Stacks, Theorem 0EYU]). In a cartesian square
```
X  ←-h-  Y
|f       |e
S  ←-g-  T
```
with `f` smooth and `g` quasi-compact and quasi-separated, the base change map
`f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism for every `q` and every abelian sheaf `F` on
`T_étale` all of whose stalks at geometric points are torsion of orders invertible on `S`: every
element of every such stalk is killed by a positive integer `n` which is a unit on `S`. -/
@[stacks 0EYU]
theorem isIso_higherBaseChangeMapAb_app_of_smooth
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : ∀ (t : GeometricPoint T) (a : (smallEtaleStalkAb t.hom).obj F),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(S, ⊤)) ∧ n • a = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMapAb f g h e sq.w q).app F) :=
  isIso_higherBaseChangeMapAb_of_smooth flatReducedFibresBaseChange etaleLocalHigherBaseChange
    higherBaseChangePaste firstFailureNormalization affineCurveCohomologyVanishing
    curveCohomologyAlgClosedInvariance
    (fun D hD => Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne D hD)
    f h e g sq F hF q

end Stacks.EtaleCohomology.SmoothBaseChange

end
