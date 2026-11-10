module

public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralLimitVertex.VanishingFromCechAcyclicity

/-!
# The colimit-comparison clauses of Tag 0A37 for a system of injective sheaves

The quasi-compact-open clause of Stacks 0A37 asserts that a presentation of the cohomology cocone
over a quasi-compact open `U` of a stage is a colimit cocone, and the Stacks proof of it is a
degree induction that compares the long exact sequences of a short exact sequence of systems
`0 → 𝒜 → 𝒢 → 𝒬 → 0` with `𝒢` a system of injective sheaves.  **This file proves the clause for
such a `𝒢`**, in every positive degree, modulo exactly one input: the vanishing of the cohomology
on the vertex.

In positive degree both sides of the comparison vanish for an injective system, and that is the
whole content.  Each object of the cohomology diagram is, by the `objIso` field of
`CohomologyCocone`, the cohomology of an injective abelian sheaf over an open of a stage, so it is
a zero object by `Stacks.Cohomology.AbelianBasis.isZero_H'_succ_of_injective`.  A cocone whose
diagram is pointwise zero and whose vertex is zero is a colimit cocone for trivial reasons: every
arrow out of a zero object is zero, so the required factorization is the zero map, and it is
unique because the vertex is zero.

What that leaves is the vanishing on the vertex, `Hⁿ⁺¹(pᵢ⁻¹U, c.pt.sheaf) = 0`.  It is **not**
a consequence of injectivity of the stage sheaves in any formal way: `c.pt.sheaf` is the filtered
colimit `colimⱼ pⱼ⁻¹𝒢ⱼ` and `pⱼ⁻¹` does not preserve injectives, so the library's vanishing for a
filtered colimit of injectives does not apply.  It is reduced to Čech acyclicity of `c.pt.sheaf`
by `isZero_H'_succ_conePoint_of_cechAcyclic`.

## Main results

* `CohomologyCocone.isColimit_cocone_of_isZero`: a presentation of the cohomology cocone whose
  diagram is pointwise zero and whose vertex is zero is a colimit cocone.
* `CohomologyCocone.isZero_diagram_obj_of_injective`: in positive degree, the cohomology diagram
  of a presentation is pointwise zero as soon as every stage sheaf is injective.
* `SpectralAbelianSheafSystem.isColimit_cohomologyCocone_of_injective_system`, in the namespace
  `Stacks.Cohomology.SpectralLimit`: **the quasi-compact-open clause of Stacks 0A37 in positive
  degree for a system of injective sheaves**, with the vanishing on the vertex as its single
  hypothesis.
* `SpectralAbelianSheafSystem.isIso_comparison_of_injective_system`: the same conclusion in the
  form the clause states, as invertibility of `CohomologyCocone.comparison`.

## Implementation notes

`isColimit_cocone_of_isZero` is stated at independent index universes, because nothing in it needs
a colimit of the cohomology diagram to exist; the universes collapse to `u` only in
`isIso_comparison_of_injective_system`, which goes through
`CohomologyCocone.isIso_comparison_of_isColimit` and therefore needs
`HasColimitsOfShape Kᵒᵖ AddCommGrpCat.{u}`.  As everywhere in this development the collapse is
forced by the only available form of abelian Stacks 01FF, whose single universe parameter serves
as space, coefficient, index-object and index-hom universe at once while the space and coefficient
universes are pinned to `u` by `SpectralAbelianSheafSystem` and `CohomologyCocone`.

`Injective` of a stage sheaf is taken as an explicit argument at the `TopCat.Sheaf` spelling and
handed to `isZero_H'_succ_of_injective`, which takes it explicitly for the same reason:
`TopCat.Sheaf` is a semireducible `def` over `Sheaf (Opens.grothendieckTopology X)`, and an
`Injective` hypothesis stated at one of the two spellings is not found by instance search at the
other.

The hypothesis of `isZero_diagram_obj_of_injective` is injectivity of **every** stage sheaf rather
than of the one at `k`, because that is the form the degree induction supplies — the system of
injectives is built all at once — and asking for less would not shorten any proof.

## References

* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u v v'

namespace Stacks.Cohomology.SpectralLimit

namespace CohomologyCocone

variable {K : Type v} [Category.{v'} K]
  {E : K ⥤ SheafedSpace.{_, _, u} AddCommGrpCat.{u}} {c : Cone E} {O : OpenCone E c} {p : ℕ}

/-- **A presentation of the cohomology cocone with zero diagram and zero vertex is a colimit
cocone.**  Every arrow out of a zero object is zero, so the only candidate factorization through
the vertex is the zero map and it does factor; and it is the only arrow out of the vertex at all,
because the vertex is a zero object too.

This is the degenerate case that carries the positive-degree clauses of Stacks 0A37 for a system
of injective sheaves. -/
def isColimit_cocone_of_isZero (D : CohomologyCocone E c O p)
    (hd : ∀ k : K, IsZero (D.diagram.obj (op k)))
    (hv : IsZero (Sheaf.H'.{u, u, u} c.pt.sheaf p O.pt)) :
    IsColimit D.cocone where
  desc _ := 0
  fac s k := by
    rw [Limits.comp_zero]
    exact ((hd k.unop).eq_of_src (s.ι.app k) 0).symm
  uniq _ m _ := hv.eq_of_src m 0

/-- **In positive degree the cohomology diagram of a presentation is pointwise zero as soon as
every stage sheaf is injective.**  The object at `k` is identified by the `objIso` field with
`Hⁿ⁺¹` of the stage sheaf over the stage open, and the positive-degree cohomology of an injective
abelian sheaf vanishes over every open
(`Stacks.Cohomology.AbelianBasis.isZero_H'_succ_of_injective`). -/
theorem isZero_diagram_obj_of_injective {n : ℕ} (D : CohomologyCocone E c O (n + 1))
    (hinj : ∀ k, Injective (E.obj k).sheaf) (k : K) : IsZero (D.diagram.obj (op k)) :=
  (AbelianBasis.isZero_H'_succ_of_injective (E.obj k).sheaf (hinj k) (O.obj k) n).of_iso
    (D.objIso k)

end CohomologyCocone

namespace SpectralAbelianSheafSystem

variable {K : Type u} [SmallCategory K] [IsCofiltered K]
  (S : SpectralAbelianSheafSystem.{u, u, u} K)

/-- **The quasi-compact-open clause of Stacks 0A37 in positive degree, for a system of injective
sheaves.**  If every stage sheaf is injective and the cohomology of the sheaf on the vertex
vanishes in degree `n + 1` over `pᵢ⁻¹U`, then every presentation of the cohomology cocone over a
quasi-compact open `U` of the stage `i` is a colimit cocone in degree `n + 1`.

Both sides of the comparison are zero: the diagram by
`CohomologyCocone.isZero_diagram_obj_of_injective`, since the sheaves of the restricted diagram
`(Over.forget i) ⋙ S.E` are the stage sheaves, and the vertex by hypothesis.  The vanishing on
the vertex is the one piece that is not formal; `isZero_H'_succ_conePoint_of_cechAcyclic` reduces
it to Čech acyclicity of the sheaf on the vertex.

This is the base of the degree induction of Stacks 0A37: the general clause is obtained from it by
embedding the system of sheaves in a system of injectives and comparing the two long exact
sequences. -/
def isColimit_cohomologyCocone_of_injective_system (c : Cone S.E) (i : K)
    (U : Opens (S.E.obj i)) (n : ℕ)
    (hinj : ∀ j, Injective (S.E.obj j).sheaf)
    (hvan : IsZero (Sheaf.H'.{u, u, u} c.pt.sheaf (n + 1) (S.stageOpenCone c i U).pt))
    (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) (n + 1)) :
    IsColimit D.cocone :=
  D.isColimit_cocone_of_isZero
    (D.isZero_diagram_obj_of_injective (fun A => hinj A.left)) hvan

/-- **The quasi-compact-open clause of Stacks 0A37 for a system of injective sheaves, in the form
the clause states it**: the comparison out of the colimit of the stage cohomology groups is an
isomorphism.  This is
`isColimit_cohomologyCocone_of_injective_system` through
`CohomologyCocone.isIso_comparison_of_isColimit`. -/
theorem isIso_comparison_of_injective_system (c : Cone S.E) (i : K)
    (U : Opens (S.E.obj i)) (n : ℕ)
    (hinj : ∀ j, Injective (S.E.obj j).sheaf)
    (hvan : IsZero (Sheaf.H'.{u, u, u} c.pt.sheaf (n + 1) (S.stageOpenCone c i U).pt))
    (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) (n + 1)) :
    IsIso D.comparison :=
  CohomologyCocone.isIso_comparison_of_isColimit D
    (S.isColimit_cohomologyCocone_of_injective_system c i U n hinj hvan D)

end SpectralAbelianSheafSystem

end Stacks.Cohomology.SpectralLimit

end
