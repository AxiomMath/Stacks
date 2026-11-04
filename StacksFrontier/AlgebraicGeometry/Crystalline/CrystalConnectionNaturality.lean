module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnectionGeneral
public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningFunctorial

/-!
# Naturality of the canonical connection, with the functoriality datum supplied

[Stacks, Tag 07J6] says that the family of maps

`∇ : Γ(T, F_T) ⟶ Γ(T, F_T ⊗_{𝒪_T} Ω_{T/S,δ})`

over the objects of `Cris(X/S)` "is functorial in `T` because the construction of `T'` is
functorial in `T`", and that is what makes the family a connection rather than a family of
unrelated maps.  `StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionGeneral.lean` proves
the naturality against the hypothesis structure
`Crystalline.GlobalCrystallineSituation.FirstOrderThickeningHom`, the functoriality of
`(U, T, δ) ↦ (U, T', δ')`, which that module records as not constructed.

`StacksFrontier/AlgebraicGeometry/Crystalline/UniversalThickeningFunctorial.lean` constructs it.
This module assembles the datum and restates the naturality with nothing assumed.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningHom` — **the functoriality datum of
  the first-order universal thickening of [Stacks, Tag 07J2], for every morphism of
  `CRIS(X/S)`**, constructed.

## Main results

* `Crystalline.GlobalCrystallineSituation.crystalConnection_naturality'` — **the canonical
  connection of [Stacks, Tag 07J6] is natural in the object of the site**, with no datum assumed.

## What is and is not proved

[Stacks, Tag 07J6] itself — a crystal on the small site `Cris(X/S)` has a canonical integrable
connection — is formalized, with no quasi-coherence hypothesis, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalIntegrableConnectionCris.lean`,
in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`: the connection
`crystalConnectionCris : F ⟶ F ⊗ Ω_{X/S}`, a morphism of abelian sheaves on `Cris(X/S)`, and the
theorems `crystalConnectionCris_isConnection` and `crystalConnectionCris_isIntegrable`.  This
module is about the big site `CRIS(X/S)` and carries no attribute for that tag.

The naturality clause of [Stacks, Tag 07J6] is unconditional here, for every sheaf of
`𝒪_{X/S}`-modules and every morphism of `CRIS(X/S)`.  What is still read in the weaker target is
the connection itself: its values are sections of the ideal of the diagonal, and the tag's
`F_T ⊗_{𝒪_T} Ω_{T/S,δ}` is reached only through the identification discussed in
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionTensor.lean`.  Integrability is not
proved.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- **The functoriality datum of the first-order universal thickening of [Stacks, Tag 07J2].**
For a morphism `g : (U, T, δ) ⟶ (U₁, T₁, δ₁)` of `CRIS(X/S)`, the induced morphism
`(U, T', δ') ⟶ (U₁, T₁', δ₁')` of the site together with its two commutation relations, which
`StacksFrontier/AlgebraicGeometry/Crystalline/UniversalThickeningFunctorial.lean` constructs as
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteMap`,
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteMap_comp_P₀` and
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteMap_comp_P₁`.

This is the input [Stacks, Tag 07J6] uses to turn its family of connections into a morphism of
abelian sheaves on the site. -/
@[stacks 07J2 "the functoriality datum of the first-order thickening, in the shape in which the \
naturality clause of 07J6 consumes it"]
def firstOrderThickeningHom {A B : Thickening S} (g : A ⟶ B) : FirstOrderThickeningHom g where
  hom := firstOrderThickeningSiteMap g
  comp_p₀ := firstOrderThickeningSiteMap_comp_P₀ g
  comp_p₁ := firstOrderThickeningSiteMap_comp_P₁ g

/-- **Naturality of the canonical connection of [Stacks, Tag 07J6] in the object of the site**,
with nothing assumed: the connection commutes with the restriction maps of `F` along the
functoriality of the first-order universal thickening.  This is the clause of the tag that the
family of connections is a morphism of abelian sheaves on `Cris(X/S)` — "functorial in `T`
because the construction of `T'` is functorial in `T`" — and the functoriality of `T'` is now
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteMap`.

It needs nothing of `F`: both terms of `∇` are restrictions of `F` along a morphism of the site,
and the two commutation relations identify the two composites. -/
theorem crystalConnection_naturality' (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    {A B : Thickening S} (g : A ⟶ B) (s : M.val.obj (op B)) :
    moduleSiteRestrict M (firstOrderThickeningSiteMap g) (crystalConnection M B s) =
      crystalConnection M A (moduleSiteRestrict M g s) :=
  crystalConnection_naturality M g (firstOrderThickeningHom g) s

end Crystalline.GlobalCrystallineSituation

end

end
