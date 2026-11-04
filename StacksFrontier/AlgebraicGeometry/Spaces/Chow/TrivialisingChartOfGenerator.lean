module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseRankCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemePreimageModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleChartSections

/-!
# A free generator over an affine chart trivialises the module on the slice

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `ℒ` be an
`𝒪_X`-module which is cartesian on affine charts — an invertible module is
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isInvertible`) — and let `V` be an étale
chart of `X` with **affine** scheme.  A single section `t ∈ ℒ(V)` which generates `ℒ(V)` freely
over `𝒪_X(V)` already trivialises `ℒ` over *every* chart above `V`:
`AlgebraicGeometry.Space.IsTrivialisingChart` holds at `V`.

This is the step from a free generator at one chart to the compatible family of free generators
over the charts above it.  It is what the consumers of a trivialising chart —
`AlgebraicGeometry.Space.sectionEvaluationIdealAt_modulePullback_eq_map` and through it
`AlgebraicGeometry.Space.ker_componentVanishingLocusChartImmersion` — ask for, and until now the
only producers of the family were
`AlgebraicGeometry.Space.exists_generator_cover_smul_of_isInvertible` (over the members of a
covering family, chosen by Stacks 0B8Q) and
`AlgebraicGeometry.Space.exists_generator_smul_of_iso_unit` (from a *global* isomorphism
`ℒ ≅ 𝒪_X`).  Neither takes a generator over a prescribed chart as its input, so a chart known to
carry a free generator could not be known to trivialise `ℒ`.

## Main results

* `AlgebraicGeometry.Space.isTrivialisingChart_of_bijective_smul`: **a free generator of the
  sections over an affine chart trivialises the module over that chart.**

## Implementation notes

The proof is a composition of two existing results, and the only new content is the passage from a
free generator to a basis indexed by `Fin 1`:
`AlgebraicGeometry.Space.exists_isColimitCofanUnit_of_basis` turns that basis into the
one-element cofan presenting the restriction of `ℒ` to the slice at `V` as one copy of the
structure sheaf, and `AlgebraicGeometry.Space.exists_generator_smul_of_isColimit` reads the cofan
as the compatible family of free generators.

Affineness of the chart is where the first of those two results lives: it is the hypothesis under
which the restricted basis of `AlgebraicGeometry.Space.chartRestrictBasis` is again a basis, the
affine charts above `V` covering every chart above `V`.  It is not a restriction on the use made
of this statement here, the charts cut out by affine opens of a chart scheme being affine
(`AlgebraicGeometry.Space.isAffine_chartScheme_openChart`).

## References

* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A section generating the sections of a module over a chart freely gives a basis of them
indexed by `Fin 1`: the map `r ↦ r • t` is then a linear isomorphism from the regular functions,
and the one-element basis of a ring over itself travels along it. -/
noncomputable def basisOfBijectiveSmul {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} (G : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (t : G.val.obj (op V))
    (ht : Function.Bijective fun r : chartRing B S hS F hF V ↦ r • t) :
    Module.Basis (Fin 1) (chartRing B S hS F hF V) (G.val.obj (op V)) :=
  (Module.Basis.singleton (Fin 1) (chartRing B S hS F hF V)).map
    (LinearEquiv.ofBijective
      (LinearMap.toSpanSingleton (chartRing B S hS F hF V) (G.val.obj (op V)) t) ht)

/-- **A free generator of the sections over an affine chart trivialises the module over that
chart.**  Let `ℒ` be an `𝒪_X`-module cartesian on affine charts, let `V` be an étale chart of `X`
whose scheme is affine, and let `t ∈ ℒ(V)` be such that `r ↦ r • t` is a bijection
`𝒪_X(V) → ℒ(V)`.  Then `V` is a trivialising chart for `ℒ`: there is a family of free generators
of `ℒ` over the charts above `V`, compatible with restriction.

The generator gives a basis of `ℒ(V)` indexed by `Fin 1`, which by
`AlgebraicGeometry.Space.exists_isColimitCofanUnit_of_basis` presents the restriction of `ℒ` to
the slice at `V` as a single copy of the structure sheaf, and
`AlgebraicGeometry.Space.exists_generator_smul_of_isColimit` reads that presentation as the
family. -/
theorem isTrivialisingChart_of_bijective_smul {Y : AlgebraicSpaces B S hS}
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : IsCartesianOnAffineCharts G)
    (V : SmallEtale B S hS Y.1) (hV : IsAffine (chartScheme V))
    (t : G.val.obj (op V))
    (ht : Function.Bijective fun r : chartRing B S hS Y.1 Y.2 V ↦ r • t) :
    IsTrivialisingChart B S hS G V := by
  obtain ⟨ι, ⟨hc⟩⟩ := exists_isColimitCofanUnit_of_basis B S hS Y.1 Y.2 G hG hV
    (basisOfBijectiveSmul B S hS G V t ht)
  exact exists_generator_smul_of_isColimit B S hS Y.1 Y.2 G V ι hc

/-- **An invertible module is trivialised by every affine chart over which it has a free
generator.**  This is `AlgebraicGeometry.Space.isTrivialisingChart_of_bijective_smul` with its
cartesianness hypothesis discharged by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isInvertible`. -/
theorem isTrivialisingChart_of_bijective_smul_of_isInvertible {Y : AlgebraicSpaces B S hS}
    (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hG : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS Y)
      (structureRingSheaf B S hS Y).property G)
    (V : SmallEtale B S hS Y.1) (hV : IsAffine (chartScheme V))
    (t : G.val.obj (op V))
    (ht : Function.Bijective fun r : chartRing B S hS Y.1 Y.2 V ↦ r • t) :
    IsTrivialisingChart B S hS G V :=
  isTrivialisingChart_of_bijective_smul B S hS G
    (isCartesianOnAffineCharts_of_isInvertible B S hS Y G hG) V hV t ht

end AlgebraicGeometry.Space

end
