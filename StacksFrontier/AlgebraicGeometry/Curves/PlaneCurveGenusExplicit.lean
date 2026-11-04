module

public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveGenus

/-!
# Tag 0BYD from its explicit hypotheses

[Stacks, Tag 0BYD] is about a closed subscheme `Z ⊆ 𝐏²_k = Proj k[T₀, T₁, T₂]` satisfying the
explicit hypotheses of [Stacks, Tag 0BYB]: `Z` has no embedded points, `dim Z = 1`, every
irreducible component of `Z` has dimension one, and a chosen homogeneous polynomial `F`
generates `I(Z)`. The library's own proof of the tag, `planeCurveGlobalSectionsEquiv` and
`genus_planeCurve`, is stated over the bundled
`AlgebraicGeometry.ProjectiveSpectrum.Proj.PlaneCurveData` rather than over this hypothesis list,
so a caller holding the source's hypotheses directly cannot apply it. This file is the bridge:
it builds a `PlaneCurveData` from exactly that hypothesis list and reads the two conclusions of
Tag 0BYD off it.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.planeCurveDataOfExplicit`: the `PlaneCurveData`
  built from the explicit hypothesis list of [Stacks, Tag 0BYB].

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.nonempty_of_topologicalKrullDim_eq_one`: a scheme
  of Krull dimension `1` is nonempty.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.isHomogeneous_totalDegree_of_idealOfClosedSubscheme_eq_span_singleton`: a chosen generator
  of the (homogeneous) ideal of a closed subscheme is itself homogeneous, of degree its own
  total degree.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheafCohomologyEquiv_of_explicit` and
  `.genus_eq_of_explicit`: the two conclusions of [Stacks, Tag 0BYD], read off
  `planeCurveDataOfExplicit` through `planeCurveGlobalSectionsEquiv` and `genus_planeCurve`.

## Implementation notes

Nonemptiness of `Z` is recovered from `dim Z = 1` via `topologicalKrullDim_eq_bot_iff_isEmpty`:
the empty scheme has dimension `⊥`, so a scheme of dimension `1` cannot be empty. This is the
same role nonemptiness plays as a separate field of `PlaneCurveData`, see that structure's
docstring.

Homogeneity of the given generator `F` is recovered from `hF`, that `I(Z) = (F)`, together with
the gradedness of `I(Z)` (`idealOfClosedSubscheme_isHomogeneous`): a generator of a homogeneous
principal ideal of a graded domain is homogeneous
(`Stacks.GradedRing.isHomogeneousElem_of_span_singleton_isHomogeneous`), and the degree this
produces is forced to be `F.totalDegree` by `MvPolynomial.IsHomogeneous.totalDegree` once
`F ≠ 0`; the case `F = 0` is immediate since `0` lies in every homogeneous piece.

`Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 2` and
`MvPolynomial.homogeneousSubmodule (Fin 3) k` are the same term — the former is an `abbrev` for
the latter — so stating the closed immersion against `MvPolynomial.homogeneousSubmodule (Fin 3)
k`, as [Stacks, Tag 0BYD]'s own statement does, already states it against the model
`PlaneCurveData` uses.

## References

* [Stacks Project, Tag 0BYD](https://stacks.math.columbia.edu/tag/0BYD)
* [Stacks Project, Tag 0BYB](https://stacks.math.columbia.edu/tag/0BYB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- **A scheme of Krull dimension `1` is nonempty.** The empty scheme has Krull dimension `⊥`
(`topologicalKrullDim_eq_bot_iff_isEmpty`), and `⊥ ≠ 1` in `WithBot ℕ∞`. -/
theorem nonempty_of_topologicalKrullDim_eq_one {Z : Scheme.{u}}
    (hdim : topologicalKrullDim Z = 1) : Nonempty Z := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hbot := (topologicalKrullDim_eq_bot_iff_isEmpty Z).2 h
  rw [hdim] at hbot
  exact absurd hbot (by decide)

/-- **A chosen generator of the homogeneous ideal of a closed subscheme is itself homogeneous,
of degree its own total degree.** The ideal `idealOfClosedSubscheme` is always homogeneous
(`idealOfClosedSubscheme_isHomogeneous`); once `F ≠ 0` this is
`Stacks.GradedRing.isHomogeneousElem_of_span_singleton_isHomogeneous`, whose witnessing degree is
identified with `F.totalDegree` by `MvPolynomial.IsHomogeneous.totalDegree`. The case `F = 0` is
immediate. -/
theorem isHomogeneous_totalDegree_of_idealOfClosedSubscheme_eq_span_singleton
    {Z : Scheme.{u}} (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    [IsClosedImmersion i] {F : MvPolynomial (Fin 3) k}
    (hF : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {F}) :
    F ∈ MvPolynomial.homogeneousSubmodule (Fin 3) k F.totalDegree := by
  rcases eq_or_ne F 0 with rfl | hF0
  · exact Submodule.zero_mem _
  · have hhomog : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k)
        (Ideal.span {F}) := by
      rw [← hF]; exact idealOfClosedSubscheme_isHomogeneous _ i
    obtain ⟨n, hn⟩ :=
      Stacks.GradedRing.isHomogeneousElem_of_span_singleton_isHomogeneous hF0 hhomog
    have hhom : F.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hn
    rwa [hhom.totalDegree hF0]

/-- **The `PlaneCurveData` of [Stacks, Tag 0BYB], built from the source's own hypothesis list**
rather than from the bundled structure. This is the bridge that lets a caller holding the
source's hypotheses — a closed immersion `Z ↪ 𝐏²_k`, the absence of embedded points,
`dim Z = 1`, equidimensionality of the irreducible components, and a chosen `F` generating
`I(Z)` — apply [Stacks, Tag 0BYD] as `planeCurveGlobalSectionsEquiv` and `genus_planeCurve`
state it. -/
def planeCurveDataOfExplicit {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion i]
    (hno : HasNoEmbeddedPoints Z) (hdim : topologicalKrullDim Z = 1)
    (hequidim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (F : MvPolynomial (Fin 3) k)
    (hF : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {F}) :
    PlaneCurveData k :=
  haveI := nonempty_of_topologicalKrullDim_eq_one hdim
  { Z := Z, i := i, hasNoEmbeddedPoints := hno, equidimensional := hequidim
    deg := F.totalDegree, F := F
    isHomogeneous :=
      isHomogeneous_totalDegree_of_idealOfClosedSubscheme_eq_span_singleton i hF
    span_eq := hF }

/-- **[Stacks, Tag 0BYD], global functions, from the explicit hypothesis list.** `H⁰(Z, 𝒪_Z) =
k` for a closed subscheme `Z ⊆ 𝐏²_k` as in [Stacks, Tag 0BYB], stated with the source's own
hypotheses rather than through `PlaneCurveData`. -/
def structureSheafCohomologyEquiv_of_explicit {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion i]
    (hno : HasNoEmbeddedPoints Z) (hdim : topologicalKrullDim Z = 1)
    (hequidim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (F : MvPolynomial (Fin 3) k)
    (hF : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {F}) :
    structureSheafCohomology (i ≫ projToSpecCoeff k 2) 0 ≃ₗ[k] k :=
  planeCurveGlobalSectionsEquiv (planeCurveDataOfExplicit i hno hdim hequidim F hF)

/-- **[Stacks, Tag 0BYD], the genus formula, from the explicit hypothesis list.** The genus of a
closed subscheme `Z ⊆ 𝐏²_k` as in [Stacks, Tag 0BYB] is `(d - 1)(d - 2)/2` for
`d = F.totalDegree`, stated with the source's own hypotheses rather than through
`PlaneCurveData`. -/
theorem genus_eq_of_explicit {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion i]
    (hno : HasNoEmbeddedPoints Z) (hdim : topologicalKrullDim Z = 1)
    (hequidim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (F : MvPolynomial (Fin 3) k)
    (hF : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {F}) :
    genus (i ≫ projToSpecCoeff k 2) = (F.totalDegree - 1) * (F.totalDegree - 2) / 2 :=
  genus_planeCurve (planeCurveDataOfExplicit i hno hdim hequidim F hF)

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
