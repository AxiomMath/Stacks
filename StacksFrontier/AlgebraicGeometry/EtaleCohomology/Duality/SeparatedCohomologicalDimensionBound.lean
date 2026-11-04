module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CohomologicalDimensionInputReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `cd(X) ≤ 2 dim X` for torsion abelian sheaves, and the input `CohomologicalDimensionInput`

`Stacks.EtaleCohomology.SeparatedCohomologicalDimensionBound k` is the bound `H^q(X, F) = 0` for
`q > 2 dim X`, for every torsion abelian sheaf `F` (in the sense of
[Tag 0F0Q](https://stacks.math.columbia.edu/tag/0F0Q),
`AlgebraicGeometry.Scheme.IsEtaleCohomologyBound`) on every `X` separated, quasi-compact and
locally of finite type over `k`. Read on sheaves of `ℤ/ℓ`-modules through
`Ext^q(ℤ/ℓ, G) = H^q(X, G)` it gives `Stacks.EtaleCohomology.UnitCohomologicalDimensionInput`,
hence `Stacks.EtaleCohomology.CohomologicalDimensionInput`.

In dimension at most one over an algebraically closed field the bound is Tag 0A53
(`Stacks.EtaleCohomology.TorsionSheafSituation.isVanishingAboveDegreeTwo`):
`Stacks.EtaleCohomology.isEtaleCohomologyBound_two_of_topologicalKrullDim_le_one`.

## Main definitions

* `Stacks.EtaleCohomology.SeparatedCohomologicalDimensionBound`.

## Main results

* `Stacks.EtaleCohomology.unitCohomologicalDimensionInput_of_separatedCohomologicalDimensionBound`.
* `Stacks.EtaleCohomology.cohomologicalDimensionInput_of_separatedCohomologicalDimensionBound`.
* `Stacks.EtaleCohomology.isEtaleCohomologyBound_two_of_topologicalKrullDim_le_one`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]

/-- **`cd(X) ≤ 2 dim X`**: for `X` separated, quasi-compact and locally of finite type over `k`
with `dim X ≤ n`, `H^q(X, F) = 0` for `q > 2n` and every torsion abelian sheaf `F` on `X_ét`. Over
a separably closed field this is SGA 4 X 4.3; for affine `X` the sharper bound `cd(X) ≤ dim X` is
[Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V). -/
def SeparatedCohomologicalDimensionBound : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
    [CompactSpace X] (n : ℕ), topologicalKrullDim X ≤ n →
      Scheme.IsEtaleCohomologyBound X ((2 * n : ℕ) : ℕ∞)

variable {k} in
/-- **`H^q(X, G) = 0` for `q > 2 dim X` on sheaves of `ℤ/ℓ`-modules**, from the bound on torsion
abelian sheaves: `Ext^q(ℤ/ℓ, G) = H^q(X, G)` for the underlying abelian sheaf, which is torsion. -/
theorem unitCohomologicalDimensionInput_of_separatedCohomologicalDimensionBound
    (h : SeparatedCohomologicalDimensionBound k) : UnitCohomologicalDimensionInput ℓ k := by
  intro X p _ _ _ n hn G q hq
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hH : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian X (ZMod ℓ)).obj G) q) :=
    h X p n hn _ (torsionSheafProperty_etaleModuleUnderlyingAbelian_zmod ℓ G) q
      (by exact_mod_cast hq)
  exact (extForgetSheafHAddEquiv (ZMod ℓ) X G q).toEquiv.subsingleton

variable {k} in
/-- **`CohomologicalDimensionInput` from `cd(X) ≤ 2 dim X`.** -/
theorem cohomologicalDimensionInput_of_separatedCohomologicalDimensionBound [IsAlgClosed k]
    (h : SeparatedCohomologicalDimensionBound k) : CohomologicalDimensionInput ℓ k :=
  cohomologicalDimensionInput_of_unitCohomologicalDimensionInput ℓ k
    (unitCohomologicalDimensionInput_of_separatedCohomologicalDimensionBound ℓ h)

variable {k} in
/-- **`cd(X) ≤ 2` in dimension at most one** (Tag 0A53): for `X` separated, quasi-compact and
locally of finite type over an algebraically closed field with `dim X ≤ 1`, `H^q(X, F) = 0` for
`q > 2` and every torsion abelian sheaf `F`. -/
@[sga "4 X 5.2" "special case"]
theorem isEtaleCohomologyBound_two_of_topologicalKrullDim_le_one [IsAlgClosed k]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
    [CompactSpace X] (hX : topologicalKrullDim X ≤ 1) :
    Scheme.IsEtaleCohomologyBound X ((2 * 1 : ℕ) : ℕ∞) := by
  intro F hF q hq
  let S : TorsionSheafSituation.{u, 0} :=
    { k := k, X := X, structureMorphism := p, quasiCompact := quasiCompact_of_compactSpace p,
      dimension_le_one := hX, F := F, isTorsion := hF }
  exact S.isVanishingAboveDegreeTwo q (by exact_mod_cast hq)

end Stacks.EtaleCohomology

end
