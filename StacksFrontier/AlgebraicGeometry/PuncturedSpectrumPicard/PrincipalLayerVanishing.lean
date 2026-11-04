module

public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.InfinitesimalThickeningTower
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PicardRestrictionPullback
public import StacksFrontier.AlgebraicGeometry.Thickenings.PrincipalIdealSheafTrivialization
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.GlobalSheafCohomology

/-!
# Discharging the cohomological hypothesis of the tower of infinitesimal neighbourhoods

Let `i : Z ⟶ X` be an immersion whose defining ideal sheaf is generated, on every affine chart
of the ambient open subscheme, by the restriction of one global section `f` which is a
nonzerodivisor there. Then the defining ideal sheaf of each stage `Zₙ ⟶ Zₙ₊₁` of the tower of
infinitesimal neighbourhoods is the structure sheaf of the bottom stage `Z₀`, pushed forward
(`Stacks.Thickenings.idealSheafIsoStructureSheafNthOrderBottom`), so its second cohomology is
that of `𝒪_{Z₀}`.

This turns the standing cohomological hypothesis of
`Stacks.PuncturedSpectrumPicard.exists_isCompatible` into **one** vanishing statement about
`Z₀`, uniformly in `n`: that is the step the proof of [Stacks, Tag 0F2D] records as
`H²(U₀, 𝒪_{U₀}) = H³_𝔪(A/fA) = 0`.

The tower itself is `Stacks.PuncturedSpectrumPicard.infinitesimalTower`; the statements below add
the pullback spelling of its conclusion, in terms of `Stacks.Picard.ofScheme` and
`Stacks.Picard.schemePullbackClass`, which is the spelling
`Stacks.PuncturedSpectrumPicard.PicardColimitSurjective` is written at.

## Main results

* `Stacks.PuncturedSpectrumPicard.forall_eq_zero_sheafH_idealAddSheafOnSub_of_principal`: for an
  immersion cut out by a nonzerodivisor, the vanishing of `H²(Z₀, 𝒪_{Z₀})` gives the vanishing of
  `H²` of the defining ideal sheaf of every stage of the tower.
* `Stacks.PuncturedSpectrumPicard.exists_isCompatiblePullback_infinitesimalTower`: the tower
  statement in the pullback spelling.
* `Stacks.PuncturedSpectrumPicard.exists_isCompatiblePullback_infinitesimalTower_of_principal`:
  **both together** — for an immersion cut out by a nonzerodivisor and with `H²(Z₀, 𝒪_{Z₀}) = 0`,
  every Picard class on `Z₀` extends to a family along the tower, each the pullback of the next.

## References

* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open scoped AlgebraicGeometry

universe u

namespace Stacks.PuncturedSpectrumPicard

attribute [local implicit_reducible]
  TopCat.Sheaf
  structureSheafRing
  SheafOfModules.toSheaf

/-- `Ext`-groups of abelian sheaves on a topological space are computed in the universe of the
sections, because the category of abelian sheaves has enough injectives. This repeats the local
instance of `StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.FormalTower`. -/
local instance hasExtAbelianSheafIdealPowerTower (Y : TopCat.{u}) :
    HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} Y) :=
  hasExt_of_enoughInjectives _

open Stacks.Thickenings (nthOrderInfinitesimalNeighbourhood nthOrderSucc nthOrderBottom
  nthOrderSucc_isFirstOrderThickening idealAddSheafOnSub globalRestrict
  idealSheafIsoStructureSheafNthOrderBottom
  forall_eq_zero_cohomology_idealAddSheafOnSub_of_iso)

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The structure sheaf of the bottom stage of the tower of infinitesimal neighbourhoods, as a
sheaf of modules on that stage. -/
abbrev bottomStructureSheaf : (nthOrderInfinitesimalNeighbourhood i 0).Modules :=
  SheafOfModules.unit (structureSheafRing (nthOrderInfinitesimalNeighbourhood i 0).toSheafedSpace)

/-- **The cohomological hypothesis of the tower, reduced to the bottom stage.** Let `i : Z ⟶ X`
be an immersion whose defining ideal sheaf is generated on every affine chart of the ambient open
subscheme by the restriction of a global section `f`, with `f` a nonzerodivisor on every such
chart. If the second cohomology of `𝒪_{Z₀}` vanishes, then so does the second cohomology of the
defining ideal sheaf of every stage `Zₙ ⟶ Zₙ₊₁`.

Multiplication by `f ^ (n + 1)` identifies the ideal sheaf of the stage with the pushforward of
`𝒪_{Z₀}` (`Stacks.Thickenings.idealSheafIsoStructureSheafNthOrderBottom`), and cohomology is
unchanged along the closed immersion `Z₀ ⟶ Zₙ₊₁`. -/
theorem forall_eq_zero_sheafH_idealAddSheafOnSub_of_principal
    (f : Γ(i.coborderRange.toScheme, ⊤))
    (hK : ∀ V : i.coborderRange.toScheme.affineOpens,
      i.liftCoborder.ker.ideal V =
        Ideal.span {globalRestrict i.coborderRange.toScheme f V.1})
    (hf : ∀ V : i.coborderRange.toScheme.affineOpens,
      globalRestrict i.coborderRange.toScheme f V.1 ∈
        nonZeroDivisors Γ(i.coborderRange.toScheme, V.1))
    (h0 : ∀ y : CategoryTheory.Sheaf.H.{u}
      ((SheafOfModules.toSheaf
        (nthOrderInfinitesimalNeighbourhood i 0).ringCatSheaf).obj
          (bottomStructureSheaf i)) 2, y = 0)
    (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{u} (idealAddSheafOnSub (nthOrderSucc i n)) 2) :
    x = 0 :=
  forall_eq_zero_cohomology_idealAddSheafOnSub_of_iso (nthOrderSucc i n)
    (nthOrderSucc_isFirstOrderThickening i n)
    (idealSheafIsoStructureSheafNthOrderBottom i n f hK hf)
    (Stacks.Cohomology.ClosedImmersion.eq_zero_sheafH_pushforward
      (nthOrderBottom i n) (bottomStructureSheaf i) 2 h0) x

/-! ### The tower statement in the pullback spelling -/

/-- **Picard classes extend along the tower of infinitesimal neighbourhoods, in the pullback
spelling.** This is `Stacks.PuncturedSpectrumPicard.exists_isCompatiblePullback` at
`Stacks.PuncturedSpectrumPicard.infinitesimalTower`; it differs from
`Stacks.PuncturedSpectrumPicard.exists_isCompatible_infinitesimalTower` only in using
`Stacks.Picard.schemePullbackClass` rather than `Stacks.Thickenings.picardRestriction`, which is
the spelling `Stacks.PuncturedSpectrumPicard.PicardColimitSurjective` is written at. -/
theorem exists_isCompatiblePullback_infinitesimalTower
    (h2 : ∀ n, ∀ x : CategoryTheory.Sheaf.H.{u}
      (idealAddSheafOnSub (nthOrderSucc i n)) 2, x = 0)
    (c₀ : Stacks.Picard.ofScheme (nthOrderInfinitesimalNeighbourhood i 0)) :
    ∃ c : (n : ℕ) → Stacks.Picard.ofScheme ((infinitesimalTower i).obj n),
      c 0 = c₀ ∧ IsCompatiblePullback (infinitesimalTower i) c :=
  exists_isCompatiblePullback (infinitesimalTower i) h2 c₀

/-- **Picard classes extend along the tower of infinitesimal neighbourhoods of an immersion cut
out by a nonzerodivisor**, given the vanishing of `H²(Z₀, 𝒪_{Z₀})`.

This is the first half of the proof of [Stacks, Tag 0F2D] in the generality the argument has:
the tower is `Stacks.PuncturedSpectrumPicard.infinitesimalTower`, the identification of the ideal
sheaf of a stage with `𝒪_{Z₀}` is
`Stacks.Thickenings.idealSheafIsoStructureSheafNthOrderBottom`, and the single-stage lift is
[Stacks, Tag 0C6R]. -/
theorem exists_isCompatiblePullback_infinitesimalTower_of_principal
    (f : Γ(i.coborderRange.toScheme, ⊤))
    (hK : ∀ V : i.coborderRange.toScheme.affineOpens,
      i.liftCoborder.ker.ideal V =
        Ideal.span {globalRestrict i.coborderRange.toScheme f V.1})
    (hf : ∀ V : i.coborderRange.toScheme.affineOpens,
      globalRestrict i.coborderRange.toScheme f V.1 ∈
        nonZeroDivisors Γ(i.coborderRange.toScheme, V.1))
    (h0 : ∀ y : CategoryTheory.Sheaf.H.{u}
      ((SheafOfModules.toSheaf
        (nthOrderInfinitesimalNeighbourhood i 0).ringCatSheaf).obj
          (bottomStructureSheaf i)) 2, y = 0)
    (c₀ : Stacks.Picard.ofScheme (nthOrderInfinitesimalNeighbourhood i 0)) :
    ∃ c : (n : ℕ) → Stacks.Picard.ofScheme ((infinitesimalTower i).obj n),
      c 0 = c₀ ∧ IsCompatiblePullback (infinitesimalTower i) c :=
  exists_isCompatiblePullback_infinitesimalTower i
    (forall_eq_zero_sheafH_idealAddSheafOnSub_of_principal i f hK hf h0) c₀

end Stacks.PuncturedSpectrumPicard

end
