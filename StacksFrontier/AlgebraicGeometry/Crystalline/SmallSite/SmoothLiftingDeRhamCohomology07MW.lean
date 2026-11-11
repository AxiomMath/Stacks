module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingCrisDeRhamIso07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingCrisDeRhamLinear07MW

/-!
# Crystalline cohomology is the de Rham cohomology of a smooth lifting

Let `p` be a prime, `(A, I, γ)` a divided power ring with `p` nilpotent in `A`, `S = Spec(A)`,
`S₀ = Spec(A/I)`, `Y` a smooth scheme over `S` and `X = Y ×_S S₀`
(`Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW`).  For a crystal `F` in
quasi-coherent `𝒪_{X/S}`-modules (`F.IsQuasicoherentOnSite`), with the canonical integrable
connection on its restriction `F_Y` (`Situation07MW.moduleWithConnection`), this file proves part
(3) of [Stacks, Tag 07MW]:

`RΓ(Cris(X/S), F) = RΓ(Y, F_Y ⊗_{𝒪_Y} Ω^•_{Y/S})` in `D(A)`.

The left hand side is `...SmallSite.moduleULiftDerivedGlobalSections S F` and the right hand side
is `AlgebraicGeometry.Scheme.Hom.derivedBaseGlobalSections` of the twisted de Rham complex of
`F_Y`, both objects of `D⁺(Mod_A)`.

The proof is the source's.  The map of [Stacks, Equation 07LP] at the object `(X, Y, γ)` is an
isomorphism in `D⁺(Ab)` (`Situation07MW.isIso_crystallineToAmbientDeRham`): it is checked on the
sections of `Ru_{X/S, *}` over the opens of `X_{Zar} = Y_{Zar}` with affine preimage in `Y`, where
it is the affine computation of [Stacks, Tag 07LG] and [Stacks, Tag 07LH].  The `A`-linear
comparison of `Situation07MW.nonempty_iso_derivedBaseGlobalSections_of_isIso` then upgrades this
to `D⁺(Mod_A)`.

## Main results

* `Situation07MW.deRhamComparison` — part (3) of [Stacks, Tag 07MW] for one crystal.
* `Situation07MW.deRhamComparison07MW` — the proposition `Situation07MW.DeRhamComparison07MW`
  holds.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07LP](https://stacks.math.columbia.edu/tag/07LP)
* [Stacks Project, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Hom

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

variable {S : GlobalCrystallineSituation.{u}} (T : Situation07MW S)
  [HasDerivedCategory.{u + 1} (ModuleSheaf S)]
  [HasDerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory (TwistedModules T.toBase)]
  [HasDerivedCategory (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasDerivedCategory (Sheaf (Opens.grothendieckTopology
    T.crystallineThickening.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})]

/-- **Stacks Project, Tag 07MW, part (3).**  Let `p` be a prime, `(A, I, γ)` a divided power
ring with `p` nilpotent in `A`, `S = Spec(A)`, `Y` a smooth `S`-scheme and `X = Y ×_S S₀`, and let
`F` be a crystal in quasi-coherent `𝒪_{X/S}`-modules.  Then

`RΓ(Cris(X/S), F) = RΓ(Y, F_Y ⊗_{𝒪_Y} Ω^•_{Y/S})` in `D(A)`,

where `F_Y` carries the canonical integrable connection of part (2),
`Situation07MW.moduleWithConnection`, and the right hand side is the cohomology of its twisted de
Rham complex. -/
@[stacks 07MW "(3): RΓ(Cris(X/S), F) = RΓ(Y, F_Y ⊗ Ω^•_{Y/S}) in D(A), for every crystal F in \
quasi-coherent O_{X/S}-modules, F_Y with the canonical integrable connection of (2)"]
theorem deRhamComparison {F : SheafOfModules.{u} (structureSheaf S)}
    (hF : F.IsQuasicoherentOnSite) :
    Nonempty (moduleULiftDerivedGlobalSections S F ≅
      derivedBaseGlobalSections T.toBase (T.moduleWithConnection hF).complex) :=
  T.nonempty_iso_derivedBaseGlobalSections_of_isIso hF (T.isIso_crystallineToAmbientDeRham hF)

/-- **`Situation07MW.DeRhamComparison07MW` holds**: for every crystal in quasi-coherent
`𝒪_{X/S}`-modules `F` there is an `𝒪_Y`-module with integrable connection — the restriction
`F_Y` with its canonical connection — whose twisted de Rham complex computes
`RΓ(Cris(X/S), F)` in `D(A)`. -/
theorem deRhamComparison07MW : T.DeRhamComparison07MW :=
  fun _ hF => ⟨T.moduleWithConnection hF, T.deRhamComparison hF⟩

end Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

end

end
