module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CoefficientUniverseReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantCharacteristicCurveStatements
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsAllUniverses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimaryVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionConstantSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology of torsion sheaves on curves: statements (1) -- (8) of Situation 0A52

Let `k` be an algebraically closed field, `X` a separated scheme of finite type over `k` of
dimension at most one, and `F` a torsion abelian sheaf on `X_étale` (Situation 0A52,
`Stacks.EtaleCohomology.TorsionSheafSituation`). This file proves that the eight statements of
the source hold in every such situation — Tags 0A53 to 0A5A, which together are Theorem 03SC —
and Lemma 0GJA.

The proof is the source's. The base case, Lemma 0A5B for the constant sheaf `𝐙/ℓ𝐙` on a smooth
curve, is `Stacks.EtaleCohomology.curveStatementsConstantOnSmoothCurves_zmod`: for `ℓ` invertible
in `k` it is `curveStatementsConstantOnSmoothCurves_of_isUnit` (Kummer theory, Tag 03RM and the
Jacobian), and for `ℓ = char(k)` it is `curveStatementsConstantOnSmoothCurves_of_charP`
(Artin–Schreier theory). The dévissage from the base case to an arbitrary torsion sheaf at every
coefficient universe is `TorsionSheafSituation.curveStatements_of_base` and its eight projections.

## Main results

* `Stacks.EtaleCohomology.TorsionSheafSituation.isVanishingAboveDegreeTwo` (0A53),
  `isAffineVanishingAboveDegreeOne` (0A54), `isPrimePowerTorsionVanishing` (0A55),
  `finiteCohomologyOfPrimeToCharacteristic` (0A56), `finiteCohomologyOfIsProper` (0A57),
  `baseChangePrimeToCharacteristic` (0A58), `properBaseChangeStatement` (0A59),
  `isDegreeTwoOpenRestrictionSurjective` (0A5A). Their conjunction is the bundle
  `Stacks.EtaleCohomology.CurveStatements`, by `TorsionSheafSituation.curveStatements_iff`.
* `Stacks.EtaleCohomology.curveStatements_iff_curveStatements_extensionByZero_of_dense` (0GJA).

## References

* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v u

namespace Stacks.EtaleCohomology

/-- **Lemma 0A5B for `𝐙/ℓ𝐙`**: statements (1) -- (8) of Situation 0A52 hold for the constant sheaf
`𝐙/ℓ𝐙` on every smooth curve over an algebraically closed field `k`, for every prime `ℓ`. If `ℓ`
is invertible in `k` this is the Kummer computation; otherwise `ℓ` is the characteristic of `k`
and it is the Artin–Schreier computation. -/
theorem curveStatementsConstantOnSmoothCurves_zmod (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ : ℕ) (hℓ : ℓ.Prime) :
    CurveStatementsConstantOnSmoothCurves k (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) := by
  have hE : Nonempty (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)) ≃+ ZMod ℓ) := ⟨AddEquiv.ulift⟩
  by_cases h : IsUnit (ℓ : k)
  · exact curveStatementsConstantOnSmoothCurves_of_isUnit k h _ hE
  · have h0 : (ℓ : k) = 0 := by simpa [isUnit_iff_ne_zero] using h
    have : CharP k ℓ := (CharP.charP_iff_prime_eq_zero hℓ).2 h0
    exact curveStatementsConstantOnSmoothCurves_of_charP hℓ _ hE

namespace TorsionSheafSituation

variable (S : TorsionSheafSituation.{u, v})

/-- Statements (1) -- (8) hold in every Situation 0A52, by dévissage from the base case. -/
private theorem curveStatements_zmod
    [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    CurveStatements.{u, v, w} S.structureMorphism S.F :=
  S.curveStatements_of_base (curveStatementsConstantOnSmoothCurves_zmod S.k)

/-- **Stacks Project, Tag 0A53**, statement (1) of Situation 0A52: `H^q(X, F) = 0` for `q > 2`. -/
@[stacks 0A53]
theorem isVanishingAboveDegreeTwo
    [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    IsVanishingAboveDegreeTwo.{u, v, w} S.F :=
  S.curveStatements_zmod.vanishing

/-- **Stacks Project, Tag 0A54**, statement (2) of Situation 0A52: if `X` is affine then
`H^q(X, F) = 0` for `q > 1`. -/
@[stacks 0A54]
theorem isAffineVanishingAboveDegreeOne
    [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    IsAffineVanishingAboveDegreeOne.{u, v, w} S.F :=
  S.curveStatements_zmod.affineVanishing

/-- **Stacks Project, Tag 0A55**, statement (3) of Situation 0A52: if `p = char(k) > 0` and `F`
is `p`-power torsion then `H^q(X, F) = 0` for `q > 1`. -/
@[stacks 0A55]
theorem isPrimePowerTorsionVanishing
    [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (p : ℕ) [CharP S.k p] :
    IsPrimePowerTorsionVanishing.{u, v, w} S.structureMorphism p S.F :=
  S.curveStatements_zmod.primePowerVanishing p

/-- **Stacks Project, Tag 0A56**, statement (4) of Situation 0A52: if `F` is constructible and
torsion prime to `char(k)` then `H^q(X, F)` is finite. -/
@[stacks 0A56, sga "5 VI 3.1" "Finite length of H^i(X"]
theorem finiteCohomologyOfPrimeToCharacteristic (B : BigEtaleSite.{u}) (hX : B.Contains S.X)
    [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    S.FiniteCohomologyOfPrimeToCharacteristic.{u, v, w} B hX :=
  have := SmallEtale.isRightAdjoint_smallEtalePushforward_addCommGrpCat.{u, v} B
  have := SmallEtale.hasWeakSheafify_over_addCommGrpCat.{u, v} B
  S.curveStatements_zmod.finite_of_isPrimeToCharacteristicTorsion B hX

/-- **Stacks Project, Tag 0A57**, statement (5) of Situation 0A52: if `X` is proper and `F` is
constructible then `H^q(X, F)` is finite. -/
@[stacks 0A57]
theorem finiteCohomologyOfIsProper (B : BigEtaleSite.{u}) (hX : B.Contains S.X)
    [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    S.FiniteCohomologyOfIsProper.{u, v, w} B hX :=
  have := SmallEtale.isRightAdjoint_smallEtalePushforward_addCommGrpCat.{u, v} B
  have := SmallEtale.hasWeakSheafify_over_addCommGrpCat.{u, v} B
  S.curveStatements_zmod.finite_of_isProper B hX

/-- **Stacks Project, Tag 0A58**, statement (6) of Situation 0A52: if `F` is torsion prime to
`char(k)` then `H^q(X, F) → H^q(X_{k'}, F|_{X_{k'}})` is bijective for every extension `k'/k` of
algebraically closed fields. -/
@[stacks 0A58]
theorem baseChangePrimeToCharacteristic : S.BaseChangePrimeToCharacteristic.{u, v, w} := by
  intro htors k' _ _ _ _ _ q
  exact S.curveStatements_zmod.bijective_of_isPrimeToCharacteristicTorsion htors k' q

/-- **Stacks Project, Tag 0A59**, statement (7) of Situation 0A52: if `X` is proper then
`H^q(X, F) → H^q(X_{k'}, F|_{X_{k'}})` is bijective for every extension `k'/k` of algebraically
closed fields. -/
@[stacks 0A59]
theorem properBaseChangeStatement : S.ProperBaseChangeStatement.{u, v, w} := by
  intro hπ k' _ _ _ _ _ q
  exact S.curveStatements_zmod.bijective_of_isProper hπ k' q

/-- **Stacks Project, Tag 0A5A**, statement (8) of Situation 0A52: `H²(X, F) → H²(U, F)` is
surjective for every open `U ⊆ X`. -/
@[stacks 0A5A]
theorem isDegreeTwoOpenRestrictionSurjective
    [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    IsDegreeTwoOpenRestrictionSurjective.{u, v, w} S.F :=
  S.curveStatements_zmod.surjective

end TorsionSheafSituation

section DenseOpen

variable {k : Type u} [Field k] [IsAlgClosed k] {X X' : Scheme.{u}} (π : X ⟶ Spec (.of k))
  [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] (hdim : topologicalKrullDim X ≤ 1)
  (j : X' ⟶ X) [IsOpenImmersion j] (hj : Dense (Set.range j.base))
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

include hdim hj in
/-- In Situation 0A52 let `j : X' → X` be the inclusion of a dense open subscheme. Then statements
(1) -- (8) hold for `F` if and only if they hold for `j_! j^{-1} F`.

The source assumes `F` constructible; that is not needed here, both sides being true for every
torsion `F` by Theorem 03SC (`j_! j^{-1} F` is a subsheaf of `F`, hence torsion). The direction
from `j_! j^{-1} F` to `F` is the dense-open reduction of
`Stacks.EtaleCohomology.curveStatements_of_curveStatements_extensionByZero_of_dense`. -/
@[stacks 0GJA "for every torsion sheaf F, not only constructible ones"]
theorem curveStatements_iff_curveStatements_extensionByZero_of_dense
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    CurveStatements.{u, v, w} π F ↔ CurveStatements.{u, v, w} π
      ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) := by
  refine ⟨fun _ ↦ ?_,
    curveStatements_of_curveStatements_extensionByZero_of_dense.{u, v, w} π hdim j hj F⟩
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, v}
    (closedComplementι j) j (range_eq_compl_range_closedComplementι j) F
  exact curveStatements_of_torsionSheafProperty_max π hdim
    (curveStatementsConstantOnSmoothCurves_zmod k) _
    (torsionSheafProperty_of_shortExact hS hF).1

end DenseOpen

end Stacks.EtaleCohomology

end
