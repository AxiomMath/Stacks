module

public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.FormalTower
public import StacksFrontier.AlgebraicGeometry.Thickenings.IdealSheafCohomologyTransfer
public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalTower

/-!
# The infinitesimal neighbourhoods of an immersion as a tower of first-order thickenings

Let `i : Z ⟶ X` be an immersion of schemes. Its infinitesimal neighbourhoods
`Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood` and the successive inclusions
`Stacks.Thickenings.nthOrderSucc` between them form a tower

`Z₀ ⟶ Z₁ ⟶ Z₂ ⟶ ⋯`

of first-order thickenings, by `Stacks.Thickenings.nthOrderSucc_isFirstOrderThickening`. This
file packages that tower as a `Stacks.PuncturedSpectrumPicard.ThickeningTower` and feeds it to
`Stacks.PuncturedSpectrumPicard.exists_isCompatible`.

In the proof of [Stacks Project, Tag 0F2D] the immersion is the inclusion of the punctured
closed fibre `U₀` of `Spec(A/fA)` into the punctured spectrum `U` of `A`, and the tower is the
system `U₀ ⊆ U₁ ⊆ U₂ ⊆ ⋯` the source writes down. This file supplies the tower itself in the
generality of an arbitrary immersion; it does **not** supply the vanishing hypothesis `h2`,
which the source obtains from the identification of the ideal sheaf of `Uₙ` in `Uₙ₊₁` with
`𝒪_{U₀}` together with `H²(U₀, 𝒪_{U₀}) = H³_𝔪(A/fA) = 0`. See the section "What this does not
do" below.

## Main definitions

* `Stacks.PuncturedSpectrumPicard.infinitesimalTower` is the tower of infinitesimal
  neighbourhoods of an immersion, as a `Stacks.PuncturedSpectrumPicard.ThickeningTower`.

## Main results

* `Stacks.PuncturedSpectrumPicard.exists_isCompatible_infinitesimalTower`: if the second
  cohomology of the ideal sheaf of every stage of the tower of infinitesimal neighbourhoods
  vanishes, then every Picard class on `Z₀` extends to a compatible family of Picard classes
  along the whole tower. This is
  `Stacks.PuncturedSpectrumPicard.exists_isCompatible` instantiated at
  `Stacks.PuncturedSpectrumPicard.infinitesimalTower`.
* `Stacks.PuncturedSpectrumPicard.exists_isCompatible_infinitesimalTower_of_iso` is the same
  statement with the cohomological hypothesis replaced by a **module-level** one: it suffices to
  trivialize the defining ideal sheaf of each stage as a sheaf of modules, by an isomorphism onto
  a sheaf whose second cohomology vanishes. This is the shape in which the remaining input of
  [Stacks Project, Tag 0F2D] is owed.

## What this does not do

The vanishing hypothesis `h2` is **carried, not discharged**. It is a hypothesis of
`Stacks.PuncturedSpectrumPicard.exists_isCompatible` and it stays a hypothesis here. Discharging
it for the tower of [Stacks Project, Tag 0F2D] needs two things this library does not have:

1. the identification of the defining ideal sheaf of a stage with the structure sheaf of `Z₀`,
   which for the inclusion of `U₀` into `U` cut out by a nonzerodivisor `f` is the source's
   observation that the ideal sheaf of `Uₙ` in `Uₙ₊₁` is `𝒪_{U₀}`. The chart-level half of that
   identification is `Stacks.Thickenings.ker_ideal_nthOrderSucc`, which computes the ideal sheaf
   as `K ^ (n + 1) / K ^ (n + 2)`; what is missing is the comparison of that with the structure
   sheaf, i.e. the multiplication-by-`fⁿ⁺¹` isomorphism. Only the *module-level* form of it is
   needed: `Stacks.Thickenings.forall_eq_zero_cohomology_idealAddSheafOnSub_of_iso` carries an
   isomorphism of sheaves of modules across to the cohomological hypothesis, so there is no
   further comparison to make between `TopCat.Sheaf AddCommGrpCat`, where the cohomology lives,
   and `CategoryTheory.SheafOfModules`, where the conormal and ideal-sheaf machinery of this
   library lives;
2. the reflection of `Stacks.LocalCohomology`'s punctured-spectrum comparison, which is stated
   in the `Hgroup` spelling, into the `CategoryTheory.Sheaf.H` spelling that `h2` is written at.

Neither is proved here, so nothing in this file carries a `@[stacks 0F2D]` attribute: the
conclusion of that tag remains the unproved
`Stacks.PuncturedSpectrumPicard.PicardColimitSurjective`.

Note also that the bottom stage of the tower is `Z₀`, the closed subscheme cut out by `K` itself
rather than `Z`. The two are isomorphic when `i` is a closed immersion — `Z₀` is the
scheme-theoretic image of `i.liftCoborder` — but this library has no such identification, and
`Stacks.Thickenings.nthOrderInclusion` at `n = 0` is the only arrow between them that is
available.

## References

* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.PuncturedSpectrumPicard

attribute [local implicit_reducible]
  TopCat.Sheaf
  structureSheafRing
  SheafOfModules.toSheaf

attribute [local instance] hasExtAbelianSheaf
  Stacks.Cohomology.Generators.picardGroupAddCommGroup

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **The tower of infinitesimal neighbourhoods of an immersion** `i : Z ⟶ X`, as a tower of
first-order thickenings: the `n`th stage is
`Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i n`, the inclusion of one stage in the
next is `Stacks.Thickenings.nthOrderSucc`, and it is a first-order thickening by
`Stacks.Thickenings.nthOrderSucc_isFirstOrderThickening`.

This is the tower `U₀ ⊆ U₁ ⊆ U₂ ⊆ ⋯` that the proof of [Stacks Project, Tag 0F2D] runs along,
for `i` the inclusion of the punctured closed fibre into the punctured spectrum. -/
def infinitesimalTower : ThickeningTower.{u} where
  obj n := Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i n
  hom n := Stacks.Thickenings.nthOrderSucc i n
  isFirstOrderThickening n := Stacks.Thickenings.nthOrderSucc_isFirstOrderThickening i n

/-- The `n`th stage of `infinitesimalTower i` is the `n`th order infinitesimal neighbourhood
of `i`. -/
@[simp]
theorem infinitesimalTower_obj (n : ℕ) :
    (infinitesimalTower i).obj n =
      Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i n :=
  rfl

/-- The `n`th transition map of `infinitesimalTower i` is the inclusion
`Stacks.Thickenings.nthOrderSucc i n` of the `n`th infinitesimal neighbourhood in the
`(n + 1)`st. -/
@[simp]
theorem infinitesimalTower_hom (n : ℕ) :
    (infinitesimalTower i).hom n = Stacks.Thickenings.nthOrderSucc i n :=
  rfl

/-- **Picard classes extend along the tower of infinitesimal neighbourhoods.** If the second
cohomology of the ideal sheaf of every stage `Zₙ ⟶ Zₙ₊₁` vanishes, then every Picard class on
the bottom stage `Z₀` extends to a family of Picard classes along the tower, each restricting to
the previous one.

This is `Stacks.PuncturedSpectrumPicard.exists_isCompatible` instantiated at
`Stacks.PuncturedSpectrumPicard.infinitesimalTower`, which is the step the proof of
[Stacks Project, Tag 0F2D] takes along the system of infinitesimal neighbourhoods of the
punctured closed fibre. The vanishing hypothesis is carried: for the tower of the tag the source
derives it from `H²(U₀, 𝒪_{U₀}) = H³_𝔪(A/fA) = 0` together with the identification of the ideal
sheaf of `Uₙ` in `Uₙ₊₁` with `𝒪_{U₀}`, and neither that identification nor that vanishing is
available in this library. -/
theorem exists_isCompatible_infinitesimalTower
    (h2 : ∀ n, ∀ x : CategoryTheory.Sheaf.H.{u}
      (Stacks.Thickenings.idealAddSheafOnSub (Stacks.Thickenings.nthOrderSucc i n)) 2, x = 0)
    (c₀ : Pic (Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i 0)) :
    ∃ c : (n : ℕ) → Pic ((infinitesimalTower i).obj n),
      c 0 = c₀ ∧ IsCompatible (infinitesimalTower i) c :=
  exists_isCompatible (infinitesimalTower i) h2 c₀

/-- **What remains of the first half of [Stacks Project, Tag 0F2D] for the tower of
infinitesimal neighbourhoods, stated at the level of sheaves of modules.** Suppose that for each
`n` the defining ideal sheaf of the stage `Zₙ ⟶ Zₙ₊₁`, as a sheaf of modules on `Zₙ₊₁`, is
isomorphic to a sheaf `M n` whose second cohomology vanishes. Then every Picard class on the
bottom stage extends to a compatible family along the whole tower.

This is `Stacks.PuncturedSpectrumPicard.exists_isCompatible_infinitesimalTower` with its
cohomological hypothesis supplied by
`Stacks.Thickenings.forall_eq_zero_cohomology_idealAddSheafOnSub_of_iso`. It is the shape in
which the remaining geometric input is owed: for the tower of the source, `M n` is the structure
sheaf of `U₀` pushed forward and the isomorphism is multiplication by `fⁿ⁺¹` for the
nonzerodivisor `f` cutting out `U₀`, whose vanishing second cohomology is
`H²(U₀, 𝒪_{U₀}) = H³_𝔪(A/fA) = 0`. **Neither the isomorphism nor the vanishing is proved
here**; both are hypotheses. -/
theorem exists_isCompatible_infinitesimalTower_of_iso
    (M : ∀ n : ℕ, SheafOfModules.{u}
      (structureSheafRing
        (Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i (n + 1)).toSheafedSpace))
    (e : ∀ n : ℕ,
      Stacks.Thickenings.idealModuleSheaf (Stacks.Thickenings.nthOrderSucc i n) ≅ M n)
    (hM : ∀ n : ℕ, ∀ y : CategoryTheory.Sheaf.H.{u}
      ((SheafOfModules.toSheaf
        (structureSheafRing
          (Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i (n + 1)).toSheafedSpace)).obj
        (M n)) 2, y = 0)
    (c₀ : Pic (Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i 0)) :
    ∃ c : (n : ℕ) → Pic ((infinitesimalTower i).obj n),
      c 0 = c₀ ∧ IsCompatible (infinitesimalTower i) c :=
  exists_isCompatible_infinitesimalTower i
    (fun n ↦ Stacks.Thickenings.forall_eq_zero_cohomology_idealAddSheafOnSub_of_iso
      (Stacks.Thickenings.nthOrderSucc i n)
      (Stacks.Thickenings.nthOrderSucc_isFirstOrderThickening i n) (e n) (hM n)) c₀

end Stacks.PuncturedSpectrumPicard

end
