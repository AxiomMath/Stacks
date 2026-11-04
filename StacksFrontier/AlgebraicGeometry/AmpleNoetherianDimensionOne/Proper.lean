module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteSurjective.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleNoetherianDimensionOne.Basic
import StacksFrontier.AlgebraicGeometry.Limits.EventuallySeparatedOverBase

/-!
# Ample invertible modules on proper schemes of dimension at most one

A scheme proper over a Noetherian ring whose underlying space has topological Krull dimension at
most one carries an ample invertible module.

This is the case of [Stacks, Tag 09NZ] that the source's applications to curves actually use —
the proof of [Stacks, Tag 0A26] and the first step of [Stacks, Tag 0E7R] both apply 09NZ to a
scheme proper over a field — and in that case the source's three-sentence proof goes through
with nothing assumed. Let `Z = X_red` be the reduction of `X` and `i : Z ⟶ X` its closed
immersion.

* `Z` is Noetherian, reduced, separated and of dimension at most one, so [Stacks, Tag 09NX]
  gives an ample invertible `𝒪_Z`-module `M`;
* the target of `i` is Noetherian of dimension at most one, so [Stacks, Tag 09NY] writes `M` as
  `i^* L` for an invertible `𝒪_X`-module `L`;
* `i` is a finite surjective morphism of schemes proper over the Noetherian base, so
  [Stacks, Tag 0B5V] — `Stacks.AmpleFiniteSurjective.isAmple_of_isAmple_modulePullback` —
  descends ampleness from `i^* L` to `L`.

The source's last step cites [Stacks, Tag 09MS] instead of 0B5V; for a non-proper `X` that tag's
converse rests on a cohomological lift that this library does not have in general (see
`StacksFrontier/AlgebraicGeometry/AmpleNoetherianDimensionOne/Basic.lean`), but over a proper base
0B5V gives the same conclusion with no hypothesis.

## Main results

* `Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isProper_of_topologicalKrullDim_le_one`

## References

* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 0B5V](https://stacks.math.columbia.edu/tag/0B5V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal isReduced_subscheme_vanishingIdeal)

universe u

namespace Stacks.AmpleNoetherianDimensionOne

/-- **An ample invertible module on a scheme proper over a Noetherian ring of dimension at most
one.** If `f : X ⟶ Spec R` is proper, `R` is Noetherian and the underlying space of `X` has
topological Krull dimension at most one, then `X` carries an ample invertible `𝒪_X`-module.

This is [Stacks, Tag 09NZ] for a scheme proper over a Noetherian ring: the reduction carries an
ample module by [Stacks, Tag 09NX], it lifts to `X` by [Stacks, Tag 09NY], and the lift is ample
by [Stacks, Tag 0B5V] applied to the finite surjective closed immersion of the reduction. -/
theorem exists_isAmple_of_isProper_of_topologicalKrullDim_le_one {R : Type u} [CommRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (L : X.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      AlgebraicGeometry.Scheme.Modules.IsAmple X L := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have : X.IsSeparated := AlgebraicGeometry.Scheme.IsSeparated.of_isSeparated f
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
    Stacks.AmpleFiniteSurjective.isAmple_of_isAmple_modulePullback
      (vanishingIdeal (⊤ : Closeds X)).subschemeι L R f hZ
  exact ⟨L, hL, (Stacks.AmpleBridge.isAmple_iff_isAmple X L).mp hX⟩

end Stacks.AmpleNoetherianDimensionOne

end
