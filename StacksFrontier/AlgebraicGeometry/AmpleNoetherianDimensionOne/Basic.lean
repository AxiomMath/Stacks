module

public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.Extension
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.ClosedUnionGlue
public import StacksFrontier.AlgebraicGeometry.AmpleSurjectiveThickening.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedThickeningLift.SectionsLift
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic

/-!
# Ample invertible sheaves on Noetherian separated schemes of dimension one

[Stacks, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ) asserts

> Let `X` be a Noetherian separated scheme of dimension `1`. Then `X` has an ample invertible
> sheaf.

The source's proof is three sentences. Let `Z = X_red` be the reduction, the reduced closed
subscheme cut out by the vanishing ideal sheaf of the whole space; it has the same underlying
topological space as `X`. Then

* `Z` is Noetherian, separated, reduced and of dimension at most one, so
  [Stacks, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX) gives an ample invertible
  `𝒪_Z`-module `M`;
* the closed immersion `i : Z ⟶ X` has Noetherian target of dimension at most one, so
  [Stacks, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY) writes `M` as `i^* L` for an
  invertible `𝒪_X`-module `L`;
* `i` is a surjective closed immersion of Noetherian schemes, so
  [Stacks, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS) descends ampleness from `i^* L`
  to `L`.

All three cited lemmas are proved in this library; the direction of [Stacks, Tag 09MS] needed
here is `Stacks.TwistedThickeningLift.isAmple_of_isAmple_modulePullback`.

## Main results

* `Stacks.AmpleNoetherianDimensionOne.surjective_reductionι`: the closed immersion of the
  reduction into `X` is surjective, which is what makes it the thickening
  [Stacks, Tag 09MS] is about.
* A Noetherian separated scheme of dimension at most one has an ample invertible sheaf:
  `Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one`
* `Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_topologicalKrullDim_le_one`: the same
  statement, under a shorter name.

The dimension hypothesis is `≤ 1` rather than `= 1`, so the statement also covers the
zero-dimensional case and is stronger than the source's; this is the form in which
[Stacks, Tag 09NX] and [Stacks, Tag 09NY] are formalized.

## How the reduction inherits the hypotheses

The reduction is `(AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⊤).subscheme`, and the
four properties [Stacks, Tag 09NX] asks of it are each one application: reducedness is
`AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal`, Noetherianness is
`StacksTag09NX.isNoetherian_subscheme`, separatedness is
`StacksTag09NX.isSeparated_of_isClosedImmersion` and the dimension bound is
`StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion`. Surjectivity of the immersion,
which is what the last step needs and the first two do not, is
`Stacks.AmpleNoetherianDimensionOne.surjective_reductionι`: the image is the support of the
vanishing ideal sheaf of `⊤`, which is `⊤`.

Two spellings of ampleness are crossed once each.
`AlgebraicGeometry.Scheme.Modules.IsAmple` is the one [Stacks, Tag 09NX] and [Stacks, Tag 09NY]
are stated over, `Stacks.Ample.IsAmple` the one the 09MS cluster is stated over, and
`Stacks.AmpleBridge.isAmple_iff_isAmple` proves with no hypothesis that they agree. Likewise
`AlgebraicGeometry.Scheme.Modules.pullback i` and
`RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom` are definitionally equal, so the
module `i^* L` needs no comparison isomorphism, only that instance search be given the
invertibility at the spelling it is asked for.

## The step through [Stacks, Tag 09MS]

The converse half of [Stacks, Tag 09MS] is
`Stacks.TwistedThickeningLift.isAmple_of_isAmple_modulePullback`: for a surjective closed immersion
`i : Z ⟶ X` onto a locally Noetherian scheme, ampleness of `i^* L` gives ampleness of `L`. It is
applied to the reduction, with no further input.

## References

* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal isReduced_subscheme_vanishingIdeal)

universe u

namespace Stacks.AmpleNoetherianDimensionOne

/-- **The reduction is a thickening.** The closed immersion of the reduced closed subscheme on
the whole space into `X` is surjective: its image is the support of the vanishing ideal sheaf of
`⊤`, which is `⊤`. -/
theorem surjective_reductionι (X : Scheme.{u}) :
    AlgebraicGeometry.Surjective (vanishingIdeal (⊤ : Closeds X)).subschemeι := by
  refine ⟨fun x => ?_⟩
  have hx : x ∈ Set.range (vanishingIdeal (⊤ : Closeds X)).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Stacks.AffineClosedUnion.support_vanishingIdeal]
    simp
  exact hx

/-- **[Stacks, Tag 09NZ].** A Noetherian separated scheme of topological Krull dimension at most
one carries an ample invertible module.

The reduction `Z` of `X` is Noetherian, reduced, separated and of dimension at most one, so it has
an ample invertible module by [Stacks, Tag 09NX]; that module is `i^* L` for an invertible module
`L` on `X` by [Stacks, Tag 09NY]; and `L` is ample because `i^* L` is, by the converse half of
[Stacks, Tag 09MS] applied to the surjective closed immersion `i : Z ⟶ X`. -/
@[stacks 09NZ "with dimension at most one in place of the source's dimension one"]
theorem exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one
    (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (L : X.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      AlgebraicGeometry.Scheme.Modules.IsAmple X L := by
  have _ : AlgebraicGeometry.IsNoetherian (vanishingIdeal (⊤ : Closeds X)).subscheme :=
    StacksTag09NX.isNoetherian_subscheme _
  have _ : AlgebraicGeometry.IsReduced (vanishingIdeal (⊤ : Closeds X)).subscheme :=
    isReduced_subscheme_vanishingIdeal _
  have _ : (vanishingIdeal (⊤ : Closeds X)).subscheme.IsSeparated :=
    StacksTag09NX.isSeparated_of_isClosedImmersion (vanishingIdeal (⊤ : Closeds X)).subschemeι
  have hdimZ : topologicalKrullDim ((vanishingIdeal (⊤ : Closeds X)).subscheme : Type u) ≤ 1 :=
    (StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion
      (vanishingIdeal (⊤ : Closeds X)).subschemeι).trans hdim
  obtain ⟨M, hM, hampleM⟩ :=
    Stacks.AmpleReducedDimensionOne.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one
      (vanishingIdeal (⊤ : Closeds X)).subscheme hdimZ
  have _ := hM
  have _ : NoetherianSpace (X : Type u) := AlgebraicGeometry.IsNoetherian.noetherianSpace
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    Stacks.LiftInvertible.exists_modulePullback_iso_of_isClosedImmersion_of_dimension_le_one
      X (vanishingIdeal (⊤ : Closeds X)).subscheme
      (vanishingIdeal (⊤ : Closeds X)).subschemeι hdim M
  have _ := hL
  have hLinv : Stacks.Ample.IsInvertibleModule X L := hL
  have : AlgebraicGeometry.Surjective (vanishingIdeal (⊤ : Closeds X)).subschemeι :=
    surjective_reductionι X
  have hpull : Stacks.Ample.IsInvertibleModule (vanishingIdeal (⊤ : Closeds X)).subscheme
      ((modulePullback (vanishingIdeal (⊤ : Closeds X)).subschemeι.toLRSHom.toShHom).obj L) :=
    AlgebraicGeometry.SheafOfModules.isInvertible_pullback
      (vanishingIdeal (⊤ : Closeds X)).subschemeι L
  have hZ : Stacks.Ample.IsAmple (vanishingIdeal (⊤ : Closeds X)).subscheme
      ((modulePullback (vanishingIdeal (⊤ : Closeds X)).subschemeι.toLRSHom.toShHom).obj L) :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
      (AlgebraicGeometry.Scheme.Modules.isAmple_of_iso e.symm hampleM)
  have hX : Stacks.Ample.IsAmple X L :=
    Stacks.TwistedThickeningLift.isAmple_of_isAmple_modulePullback
      (vanishingIdeal (⊤ : Closeds X)).subschemeι L hZ
  exact ⟨L, hL, (Stacks.AmpleBridge.isAmple_iff_isAmple X L).mp hX⟩

/-- **An ample invertible module on a Noetherian separated scheme of dimension at most one**:
this is
`Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one`,
under a shorter name. -/
theorem exists_isAmple_of_topologicalKrullDim_le_one
    (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (L : X.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      AlgebraicGeometry.Scheme.Modules.IsAmple X L :=
  exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one X hdim

end Stacks.AmpleNoetherianDimensionOne

end
