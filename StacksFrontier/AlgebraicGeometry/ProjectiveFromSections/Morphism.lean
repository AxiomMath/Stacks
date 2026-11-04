module

public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
import StacksCore.Tactic.StacksAttribute

/-!
# The morphism `φ_{(L, (s₀, …, sₙ))}` to projective space

Let `X` be a scheme over a base `S`, let `L` be an invertible `𝒪_X`-module and let
`s₀, …, sₙ` be global sections of `L` generating it. Section 27.13 of the Stacks project
attaches to this datum a morphism

`φ_{(L, (s₀, …, sₙ))} : X ⟶ ℙⁿ_S`

over `S`, and uses that notation thereafter. This file produces that morphism as data.

The construction is the glueing of the chart morphisms `X_{sᵢ} ⟶ ℙⁿ_ℤ` attached to the ratios
`sₖ / sᵢ`: those ratios are global sections of `𝒪` on `X_{sᵢ}` spanning the unit ideal, and
`Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse` turns such a family into a
morphism. The nonvanishing opens cover `X` because the sections generate, and the chart
morphisms agree on the overlaps, so `AlgebraicGeometry.Scheme.Cover.glueMorphisms` applies.

## Main definitions

* `Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse`: the glued morphism
  `X ⟶ ℙⁿ_ℤ`.
* `Stacks.ProjectiveFromSections.toProjectiveSpaceOver`: **`φ_{(L, (s₀, …, sₙ))} : X ⟶ ℙⁿ_S`**,
  the notation of the section, over a base scheme.

## Main results

* `Stacks.ProjectiveFromSections.chart_agree`: the chart morphisms agree on the overlaps of the
  nonvanishing cover. This is read off the existence statement
  `Stacks.ProjectiveFromSections.exists_hom_projectiveSpaceAtUniverse_of_generatesStalks`, whose
  witness restricts to both of them.
* `Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse` and
  `Stacks.ProjectiveFromSections.ι_toProjectiveSpaceOver`: the glued morphism restricted to the
  `i`-th chart is the chart morphism. This is what pins the morphism down.
* `Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst`: the morphism lies over `S`.

## Implementation notes

The chart agreement is derived from the existence statement rather than reproved: a morphism
`g` with `(X_{sᵢ}).ι ≫ g = chartᵢ` for every `i` makes both sides of the agreement equal to
`pullback.fst _ _ ≫ (X_{sᵢ}).ι ≫ g`, which `CategoryTheory.Limits.pullback.condition`
identifies, so no part of the proof of
`exists_hom_projectiveSpaceAtUniverse_of_generatesStalks` is repeated.

The two statements about Mathlib's `AlgebraicGeometry.Proj.fromOfGlobalSections` that the
glueing step is stated conditionally on are supplied here by
`Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality` and
`Stacks.ProjGlobalSectionsAppTop.hasUnitInvariance`, so the morphism below is unconditional.

## References

* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveFromSections

variable {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {n : ℕ}
  (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s)

/-- The morphism of the `i`-th chart: the one attached by
`Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse` to the ratios `sₖ / sᵢ`. -/
abbrev chartHom (i : Fin (n + 1)) : (nvCover s i).toScheme ⟶ projectiveSpaceAtUniverse.{u} n :=
  Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (chartRatio s i)
    (span_range_chartRatio s i)

include hs in
/-- **The chart morphisms of a generating family agree on the overlaps.** The witness of
`Stacks.ProjectiveFromSections.exists_hom_projectiveSpaceAtUniverse_of_generatesStalks`
restricts to both of them, so they agree wherever both are defined. -/
theorem chart_agree (i j : Fin (n + 1)) :
    pullback.fst (nvCover s i).ι (nvCover s j).ι ≫ chartHom s i =
      pullback.snd (nvCover s i).ι (nvCover s j).ι ≫ chartHom s j := by
  obtain ⟨g, hg⟩ := exists_hom_projectiveSpaceAtUniverse_of_generatesStalks
    Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality
    Stacks.ProjGlobalSectionsAppTop.hasUnitInvariance s hs
  have hi : chartHom s i = (nvCover s i).ι ≫ g := (hg i).symm
  have hj : chartHom s j = (nvCover s j).ι ≫ g := (hg j).symm
  rw [hi, hj, ← Category.assoc, ← Category.assoc, pullback.condition]

/-- **The morphism `X ⟶ ℙⁿ_ℤ` attached to an invertible `𝒪_X`-module with a generating family of
`n + 1` global sections**, glued from the chart morphisms of the ratios `sₖ / sᵢ`. -/
def toProjectiveSpaceAtUniverse : X ⟶ projectiveSpaceAtUniverse.{u} n :=
  (X.openCoverOfIsOpenCover (nvCover s)
      (isOpenCover_nvCover_of_generatesStalks s hs)).glueMorphisms (chartHom s)
    fun i j => chart_agree s hs i j

/-- **The glued morphism restricted to the `i`-th chart is the chart morphism.** Together with
the cover this determines `Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse`. -/
theorem ι_toProjectiveSpaceAtUniverse (i : Fin (n + 1)) :
    (nvCover s i).ι ≫ toProjectiveSpaceAtUniverse s hs = chartHom s i :=
  (X.openCoverOfIsOpenCover (nvCover s)
    (isOpenCover_nvCover_of_generatesStalks s hs)).ι_glueMorphisms _ _ i

/-- **The morphism `φ_{(L, (s₀, …, sₙ))} : X ⟶ ℙⁿ_S` of Section 27.13**, attached to a structure
morphism `f : X ⟶ S`, an invertible `𝒪_X`-module `L` and a generating family of `n + 1` global
sections of `L`. It is the morphism to the integral model paired with `f`; no compatibility has
to be checked, `ℙⁿ_S` being a fibre product over the terminal scheme. -/
@[stacks 01ND "the notation phi_(L, (s_0, ..., s_n)) of the section, as data: the morphism to \
P^n_S attached to an invertible module with n + 1 generating global sections, pinned on each \
standard chart. The scheme P^n_S itself is Tag 01NF \
(AlgebraicGeometry.projectiveSpaceOver). The section's characterisation of the morphism by \
L = phi^* O(1) and s_i = phi^* T_i is NOT proved: the comparison of L with the pullback of the \
hyperplane sheaf is the twist identification recorded as missing in \
StacksFrontier/AlgebraicGeometry/AmpleProjectiveImmersion/Basic.lean. The representability \
statement Tag 01NE is likewise not proved, only this direction of it"]
def toProjectiveSpaceOver {S : Scheme.{u}} (f : X ⟶ S) : X ⟶ projectiveSpaceOver n S :=
  Stacks.AmpleProjectiveImmersion.liftOver f (toProjectiveSpaceAtUniverse s hs)

/-- `φ_{(L, (s₀, …, sₙ))}` lies over `S`. -/
@[simp] theorem toProjectiveSpaceOver_fst {S : Scheme.{u}} (f : X ⟶ S) :
    toProjectiveSpaceOver s hs f ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f :=
  Stacks.AmpleProjectiveImmersion.liftOver_fst _ _

/-- `φ_{(L, (s₀, …, sₙ))}` induces the glued morphism on the integral model. -/
@[simp] theorem toProjectiveSpaceOver_snd {S : Scheme.{u}} (f : X ⟶ S) :
    toProjectiveSpaceOver s hs f ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse s hs :=
  Stacks.AmpleProjectiveImmersion.liftOver_snd _ _

/-- **`φ_{(L, (s₀, …, sₙ))}` restricted to the `i`-th chart is the chart morphism**, read on the
integral model. -/
theorem ι_toProjectiveSpaceOver {S : Scheme.{u}} (f : X ⟶ S) (i : Fin (n + 1)) :
    (nvCover s i).ι ≫ toProjectiveSpaceOver s hs f ≫
        projectiveSpaceOver.toIntegralAtUniverse n S = chartHom s i := by
  rw [toProjectiveSpaceOver_snd, ι_toProjectiveSpaceAtUniverse]

end Stacks.ProjectiveFromSections

end
