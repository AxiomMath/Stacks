module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LisseExtVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityFibrationInputs
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField

/-!
# The input `CohomologicalDimensionInput` from the cohomological dimension of varieties

`Stacks.EtaleCohomology.CohomologicalDimensionInput ℓ k`, an input of the fibration step of
Poincaré duality, asks for `Ext^q_X(F, G) = 0` for `q > 2n`, `F` locally constant of finite type
and `G` any sheaf of `ℤ/ℓ`-modules, on every `X` separated, quasi-compact and locally of finite
type over `k` with `dim X ≤ n`. We reduce it to the case `F = ℤ/ℓ`, i.e. to the cohomological
dimension bound `H^q(X, G) = Ext^q(ℤ/ℓ, G) = 0` for `q > 2 dim X`
(`Stacks.EtaleCohomology.UnitCohomologicalDimensionInput ℓ k`).

The reduction needs no internal `𝓗om`: `X` is Noetherian, so it has finitely many connected
components, all open; on each, `F` is a direct summand of `π_* π⁻¹F` for a connected finite étale
`π : T → W` of degree prime to `ℓ` over which `π⁻¹F` is a successive extension of copies of
`ℤ/ℓ_T` (Tags 0A3R and 03SH), and `T` is again separated, quasi-compact and locally of finite type
over `k` of dimension `≤ n`
(`Stacks.EtaleCohomology.subsingleton_ext_of_isFiniteTypeLocallyConstant`).

## Main definitions

* `Stacks.EtaleCohomology.UnitCohomologicalDimensionInput`: `H^q(X, G) = 0` for `q > 2 dim X`.

## Main results

* `Stacks.EtaleCohomology.cohomologicalDimensionInput_of_unitCohomologicalDimensionInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]

/-- **The cohomological dimension of a variety, at the constant sheaf**: for `X` separated,
quasi-compact and locally of finite type over `k` with `dim X ≤ n` and any sheaf `G` of
`ℤ/ℓ`-modules on `X_ét`, `H^q(X, G) = Ext^q_X(ℤ/ℓ, G) = 0` for `q > 2n`. Over a separably closed
field this is the bound `cd(X) ≤ 2 dim X` of SGA 4 X 4.3 (for affine `X` the sharper Artin
vanishing `cd(X) ≤ dim X` is [Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)). -/
def UnitCohomologicalDimensionInput : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
    [CompactSpace X] (n : ℕ), topologicalKrullDim X ≤ n →
    ∀ (G : EtaleModules.{u, 0} (ZMod ℓ) X) (q : ℕ), 2 * n < q →
      Subsingleton (Ext (unitSheaf (X := X) ℓ) G q)

/-- **`CohomologicalDimensionInput` from its case `F = ℤ/ℓ`.** If `H^q(X, G) = 0` for `q > 2 dim X`
on every `X` separated, quasi-compact and locally of finite type over `k`, then
`Ext^q_X(F, G) = 0` for `q > 2 dim X` and every finite type locally constant `F`. -/
theorem cohomologicalDimensionInput_of_unitCohomologicalDimensionInput [IsAlgClosed k]
    (h : UnitCohomologicalDimensionInput ℓ k) : CohomologicalDimensionInput ℓ k := by
  intro X p _ _ _ n hn F G hF q hq
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian X := {}
  have := Stacks.AlgebraicGeometry.ProperGeomConnected.finite_connectedComponents_of_noetherianSpace
    (α := X)
  refine subsingleton_ext_of_isFiniteTypeLocallyConstant q (fun W _ T π _ _ K ↦ ?_) F hF G
  have : CompactSpace W :=
    isCompact_iff_compactSpace.1 (TopologicalSpace.NoetherianSpace.isCompact (W : Set X))
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace π
  exact h T (π ≫ W.ι ≫ p) n ((topologicalKrullDim_le_of_etale (π ≫ W.ι)).trans hn) K q hq

end Stacks.EtaleCohomology

end
