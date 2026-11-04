module

public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminant
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochDeterminant
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochInvertibleDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# Equation 0BRZ with `c₁(ℰ)` read at the determinant of `ℰ`

Let `k` be a field, `X` a proper scheme of dimension at most one over `k` and `ℰ` a finite
locally free `𝒪_X`-module of constant rank `r`. Equation [Stacks, Tag 0BRZ] reads

`χ(X, ℰ) = deg(c₁(ℰ) ∩ [X]_1) + rank(ℰ) · χ(X, 𝒪_X)`.

This file gives `deg(c₁(ℰ) ∩ [X]_1)` a reading that is a function of `ℰ` alone at **every** rank,
by taking the first Chern class at the determinant of `ℰ`. The determinant of a module of
constant rank `r` is its top exterior power `⋀ʳ ℰ`, which is invertible
(`AlgebraicGeometry.Scheme.Modules.isInvertible_exteriorPower_self`), and for an invertible module
the first Chern class component rule of Stacks 02SO is a function of the module,
`Stacks.Chow.firstChernComponentCycleRule`. So

`AlgebraicGeometry.curveChernDegreeOfDeterminant k p hdim ℰ r`
  `= deg(c₁(⋀ʳ ℰ) ∩ [X]_1)`

needs no Chern class datum, where `AlgebraicGeometry.curveChernDegreeOfModule` of
`StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRoch` reads `c₁` at the rank-`r` classes of
Stacks 02U0 and is therefore a function of `ℰ` together with that datum.

## What the equation reduces to at this reading

Exactly one identity about degrees, and it is the first equality of [Stacks, Tag 0DJ5]:

`deg(ℰ) = deg(⋀ʳ ℰ)`.

Everything else is proved and needs no input. Equation 0BRX is the definition
`AlgebraicGeometry.curveDegree`, available as
`AlgebraicGeometry.curveDegree_eq_eulerCharacteristic_sub`; and equation 0BRY for an invertible
module, at the pinned rule of Stacks 02SO, is
`AlgebraicGeometry.curveDegree_eq_curveChernDegree_of_isInvertible` of
`StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochInvertibleDegree`, which holds for every
proper `X` of dimension at most one over `k` with nothing further to supply. Applied to `⋀ʳ ℰ` it
turns `deg(⋀ʳ ℰ)` into `deg(c₁(⋀ʳ ℰ) ∩ [X]_1)`, so the degree identity above is the whole
distance between the two sides of equation 0BRZ at this reading.

`AlgebraicGeometry.curveDegree_exteriorPower_one_eq` of
`StacksFrontier/AlgebraicGeometry/CurveDegreeDeterminant.lean` gives that identity outright at rank
one, since `⋀¹ ℰ ≅ ℰ`, and
`AlgebraicGeometry.curveDegree_eq_curveDegree_exteriorPower_of_devissage` gives it at every rank
at least one from the one-step dévissage of Stacks 0AYP together with the determinant comparison
of Stacks 0B38.

## Main definitions

* `AlgebraicGeometry.determinantFirstChernRule` — the first Chern class component rule of Stacks
  02SO at the determinant `⋀ʳ ℰ`, a function of `ℰ` and `r`; an alias of
  `AlgebraicGeometry.curveDeterminantChernRule`.
* `AlgebraicGeometry.curveChernDegreeOfDeterminant` — the integer `deg(c₁(⋀ʳ ℰ) ∩ [X]_1)`; an alias
  of `AlgebraicGeometry.curveChernDegreeDet`.

## Main results

* `AlgebraicGeometry.curveDegree_eq_curveChernDegreeOfDeterminant` — equation 0BRY at this
  reading, from the degree identity of Stacks 0DJ5.
* `AlgebraicGeometry.eulerCharacteristic_eq_curveChernDegreeOfDeterminant_add` — equation 0BRZ at
  this reading, from the same single identity.
* `AlgebraicGeometry.eulerCharacteristic_eq_curveChernDegreeOfDeterminant_add_rank_one` —
  equation 0BRZ at this reading for a module of constant rank one, with nothing further to
  supply. The tag itself is registered at every rank in
  `StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochFull`.

## References

* [Stacks Project, Tag 0BRZ](https://stacks.math.columbia.edu/tag/0BRZ)
* [Stacks Project, Tag 0BRX](https://stacks.math.columbia.edu/tag/0BRX)
* [Stacks Project, Tag 0BRY](https://stacks.math.columbia.edu/tag/0BRY)
* [Stacks Project, Tag 0DJ5](https://stacks.math.columbia.edu/tag/0DJ5)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Chow

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]

/-- **The first Chern class component rule of `ℰ`, read at its determinant.** This is
`AlgebraicGeometry.curveDeterminantChernRule`: the rule of Stacks 02SO at the top exterior power
`⋀ʳ ℰ`, which is invertible, so a function of `ℰ` and `r` at every rank. -/
alias determinantFirstChernRule := curveDeterminantChernRule

/-- The rule of `determinantFirstChernRule` is the rule of Stacks 02SO at `⋀ʳ ℰ`, wherever the
invertibility of `⋀ʳ ℰ` is already available. -/
public theorem determinantFirstChernRule_eq (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.exteriorPower E (r : ℤ))] :
    determinantFirstChernRule k p E r =
      firstChernComponentCycleRule (fieldChowSituation k) p 0
        (Scheme.Modules.exteriorPower E (r : ℤ)) :=
  rfl

/-- **The integer `deg(c₁(ℰ) ∩ [X]_1)` of equations 0BRY and 0BRZ, read at the determinant of
`ℰ`**: the degree of the zero cycle `c₁(⋀ʳ ℰ) ∩ [X]_1` at the rule of Stacks 02SO. This is
`AlgebraicGeometry.curveChernDegreeDet`. -/
alias curveChernDegreeOfDeterminant := curveChernDegreeDet

/-- **Equation 0BRY with `c₁(ℰ)` read at the determinant of `ℰ`.** The degree of a finite locally
free module of constant rank `r` is the degree of the zero cycle `c₁(⋀ʳ ℰ) ∩ [X]_1`.

The one input is `hdet`, the first equality of [Stacks, Tag 0DJ5] for `ℰ`. Given it, equation
0BRY for the invertible module `⋀ʳ ℰ`
(`AlgebraicGeometry.curveDegree_eq_curveChernDegree_of_isInvertible`) finishes, and that statement
holds for every proper `X` of dimension at most one over `k` with nothing further to supply. -/
public theorem curveDegree_eq_curveChernDegreeOfDeterminant (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hdet : curveDegree k p hdim E r =
      @curveDegree k _ X p _ hdim (Scheme.Modules.exteriorPower E (r : ℤ)) 1
        (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E r)) :
    curveDegree k p hdim E r = curveChernDegreeOfDeterminant k p hdim E r := by
  rw [hdet]
  exact (curveChernDegreeDet_eq_curveDegree_exteriorPower k p hdim E r).symm

/-- **Riemann-Roch, equation 0BRZ, with `c₁(ℰ)` read at the determinant of `ℰ`.** On a proper
scheme of dimension at most one over a field the Euler characteristic of a finite locally free
module `ℰ` of constant rank `r` is the degree of the zero cycle `c₁(⋀ʳ ℰ) ∩ [X]_1`, plus `r` times
the Euler characteristic of the structure sheaf:

`χ(X, ℰ) = deg(c₁(⋀ʳ ℰ) ∩ [X]_1) + rank(ℰ) · χ(X, 𝒪_X)`.

The proof is the source's: equation 0BRX, which is the definition
`AlgebraicGeometry.curveDegree`, combined with equation 0BRY at this reading,
`curveDegree_eq_curveChernDegreeOfDeterminant`. The one input is the same `hdet`, the first
equality of [Stacks, Tag 0DJ5]. -/
@[sga "7 X 1.4" "more general"]
public theorem eulerCharacteristic_eq_curveChernDegreeOfDeterminant_add
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [E.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    (hdet : curveDegree k p hdim E r =
      @curveDegree k _ X p _ hdim (Scheme.Modules.exteriorPower E (r : ℤ)) 1
        (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E r)) :
    eulerCharacteristic k p E =
      curveChernDegreeOfDeterminant k p hdim E r +
        (r : ℤ) * eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) := by
  have h := curveDegree_eq_curveChernDegreeOfDeterminant k p hdim E r hdet
  rw [curveDegree_eq_eulerCharacteristic_sub k p hdim E r] at h
  linarith

/-- **Riemann-Roch, equation 0BRZ at the determinant, for a module of constant rank one**, with
nothing further to supply:

`χ(X, ℰ) = deg(c₁(ℰ) ∩ [X]_1) + χ(X, 𝒪_X)`.

`X` is a proper scheme of dimension at most one over `k`, not assumed integral nor of dimension
exactly one, and `ℰ` is finite locally free of constant rank one, which is the tag's own
hypothesis on `ℰ` at that rank. The determinant of `ℰ` is `⋀¹ ℰ ≅ ℰ`, so the input `hdet` of
`eulerCharacteristic_eq_curveChernDegreeOfDeterminant_add` is
`AlgebraicGeometry.curveDegree_exteriorPower_one_eq`.

Equation 0BRZ at every rank, with the first Chern class of [Stacks, Tag 02U0], is
`AlgebraicGeometry.eulerCharacteristic_eq_chowDegree_firstChernCapOnCycles_add` of
`StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochChern`, where the tag is registered. -/
@[sga "7 X 1.4" "more general"]
public theorem eulerCharacteristic_eq_curveChernDegreeOfDeterminant_add_rank_one
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 1]
    [E.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent] :
    eulerCharacteristic k p E =
      curveChernDegreeOfDeterminant k p hdim E 1 +
        ((1 : ℕ) : ℤ) * eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) :=
  eulerCharacteristic_eq_curveChernDegreeOfDeterminant_add k p hdim E 1
    (curveDegree_exteriorPower_one_eq k p hdim E)

end AlgebraicGeometry

end
