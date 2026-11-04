module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnectionGeneral
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningScheme

/-!
# The second-order universal thickening as a datum for the canonical connection

`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionGeneral.lean` carries the second-order
universal thickening `(U, T'', δ'')` of [Stacks, Tag 07J3] as the hypothesis structure
`Crystalline.GlobalCrystallineSituation.SecondOrderThickeningSiteData`, on the ground that the
library had `(U, T'', δ'')` only on structure sheaves and not as an *object* of `CRIS(X/S)`.  That
is no longer the case: `StacksFrontier/AlgebraicGeometry/Crystalline/SecondOrderThickeningScheme.lean`
builds the object `Crystalline.GlobalCrystallineSituation.secondOrderThickeningObject`, the three
morphisms `q₀, q₁, q₂` to `(U, T, δ)`, the three morphisms `q₀₁, q₀₂, q₁₂` to the first-order
thickening `(U, T', δ')`, and all six composition relations of the tag, in `CRIS(X/S)`.

This module assembles those into the datum, so that the step of the integrability argument of
[Stacks, Tag 07J6] which consumes it is unconditional.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.secondOrderThickeningSiteData` — **the datum of the
  second-order universal thickening of [Stacks, Tag 07J3] as an object of `CRIS(X/S)`**,
  constructed.

## Main results

* `Crystalline.GlobalCrystallineSituation.crystalConnection_restrict_q₁₂'` — **the connection
  carried along `q₁₂` to the second-order thickening is the difference `q₂^* s - q₁^* s`**, with
  no datum assumed.

## What is and is not proved

[Stacks, Tag 07J6] itself — a crystal on the small site `Cris(X/S)` has a canonical integrable
connection — is formalized, with no quasi-coherence hypothesis, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalIntegrableConnectionCris.lean`,
in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`: the connection
`crystalConnectionCris : F ⟶ F ⊗ Ω_{X/S}`, a morphism of abelian sheaves on `Cris(X/S)`, and the
theorems `crystalConnectionCris_isConnection` and `crystalConnectionCris_isIntegrable`.  This
module is about the big site `CRIS(X/S)` and carries no attribute for that tag.

The datum is constructed, so the conditionality recorded in the previous module for
`Crystalline.GlobalCrystallineSituation.crystalConnection_restrict_q₁₂` is removed.  This is *not*
integrability: as that module explains, the remaining steps of the source's proof read the outcome
inside `F_T ⊗ Ω²_{T/S,δ}`, which needs the identification of the ideal of the diagonal with
`F_T ⊗ Ω` in degree two.  Nothing here supplies that and no attribute here claims integrability.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- **The second-order universal thickening of [Stacks, Tag 07J3] as an object of `CRIS(X/S)`,
with the morphism `q₁₂` and the two relations the integrability argument consumes.**  Every field
is a declaration of
`StacksFrontier/AlgebraicGeometry/Crystalline/SecondOrderThickeningScheme.lean`: the object is
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningObject`, the morphisms are
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningSiteQ₁₂`,
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningSiteQ₁` and
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningSiteQ₂`, and the two relations are
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningSiteQ₁₂_comp_P₀` and
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningSiteQ₁₂_comp_P₁`. -/
@[stacks 07J3 "the second-order thickening as an object of CRIS(X/S) together with q₁₂ and the \
two relations q₁ = q₁₂ ∘ p₀, q₂ = q₁₂ ∘ p₁, in the shape in which the integrability argument of \
07J6 consumes them"]
def secondOrderThickeningSiteData (A : Thickening S) : SecondOrderThickeningSiteData A where
  obj := secondOrderThickeningObject S A
  q₁₂ := secondOrderThickeningSiteQ₁₂ S A
  q₁ := secondOrderThickeningSiteQ₁ S A
  q₂ := secondOrderThickeningSiteQ₂ S A
  q₁_eq := secondOrderThickeningSiteQ₁₂_comp_P₀ S A
  q₂_eq := secondOrderThickeningSiteQ₁₂_comp_P₁ S A

/-- **The connection carried to the second-order thickening is the second-order difference**,
unconditionally.  Restricting `∇(s)` along `q₁₂ : T'' ⟶ T'` gives `q₂^* s - q₁^* s`, by the two
relations `q₁ = q₁₂ ∘ p₀` and `q₂ = q₁₂ ∘ p₁` of [Stacks, Tag 07J3].  This is
`Crystalline.GlobalCrystallineSituation.crystalConnection_restrict_q₁₂` with the datum supplied by
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningSiteData`; it is the step by which the
proof of [Stacks, Tag 07J6] moves `∇(s)` onto `T''`.

It is *not* integrability: the remaining steps read the outcome inside `F_T ⊗ Ω²_{T/S,δ}`, which
needs the identification of the ideal of the diagonal with `F_T ⊗ Ω` in degree two. -/
theorem crystalConnection_restrict_q₁₂' (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (A : Thickening S) (s : M.val.obj (op A)) :
    moduleSiteRestrict M (secondOrderThickeningSiteQ₁₂ S A) (crystalConnection M A s) =
      moduleSiteRestrict M (secondOrderThickeningSiteQ₂ S A) s -
        moduleSiteRestrict M (secondOrderThickeningSiteQ₁ S A) s :=
  crystalConnection_restrict_q₁₂ M A (secondOrderThickeningSiteData A) s

end Crystalline.GlobalCrystallineSituation

end

end
