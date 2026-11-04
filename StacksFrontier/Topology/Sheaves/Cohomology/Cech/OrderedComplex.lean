module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.HomologicalComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingCochainGroups
public import StacksFrontier.Topology.Sheaves.Presheaf.Abelian
import StacksCore.Tactic.StacksAttribute

/-!
# The ordered Čech complex

Let `X` be a topological space, let `U : I → Opens X` be a family of open subsets indexed by
a linearly ordered set `I`, and let `ℱ` be an abelian presheaf on `X`. The *ordered* Čech
complex of Stacks 01FH–01FI uses, in degree `p`, only the strictly increasing tuples of
indices: its degree-`p` term is `∏_{i_0 < … < i_p} ℱ(U_{i_0} ∩ … ∩ U_{i_p})` and its
differential is the usual alternating sum of restrictions, reindexed so that the result is
again supported on strictly increasing tuples.

The ordered cochains, their differential, and the fact that the differential squares to zero
are `CechCochains.OrdCochain`, `CechCochains.ordD` and `CechCochains.ordD_ordD`, developed for the
comparison of the ordered and alternating Čech complexes in Tag 01FJ. This file assembles
them into a cochain complex.

## Main definitions

* `Stacks.Cech.orderedCechComplex`: the ordered Čech cochain complex.

## Main results

* `Stacks.Cech.orderedCechComplex_X` and `Stacks.Cech.orderedCechComplex_d` identify its
  terms and its differentials.

## Implementation notes

The complex is built for an arbitrary indexed family of opens: no covering hypothesis is
needed to form it. The index universe `v` and the coefficient universe `w` are
independent, which is why the terms live in `AddCommGrpCat.{max v w}`.

## References

* [Stacks Project, Tag 01FI](https://stacks.math.columbia.edu/tag/01FI)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v w

namespace Stacks.Cech

variable {X : TopCat.{u}} {I : Type v} [LinearOrder I]

/-- The ordered Čech cochain complex of an abelian presheaf with respect to a linearly
ordered family of open subsets. -/
@[stacks 01FI]
noncomputable def orderedCechComplex (U : I → Opens X)
    (ℱ : TopCat.Presheaf AddCommGrpCat.{w} X) :
    CochainComplex AddCommGrpCat.{max v w} ℕ :=
  CochainComplex.of
    (fun p => AddCommGrpCat.of (CechCochains.OrdCochain U ℱ p))
    (fun p => AddCommGrpCat.ofHom (CechCochains.ordD U ℱ p))
    (fun p => by
      ext s
      exact CechCochains.ordD_ordD U ℱ p s)

/-- The degree `p` term of the ordered Čech complex is the ordered Čech cochain group. -/
@[simp]
theorem orderedCechComplex_X (U : I → Opens X)
    (ℱ : TopCat.Presheaf AddCommGrpCat.{w} X) (p : ℕ) :
    (orderedCechComplex U ℱ).X p =
      AddCommGrpCat.of (CechCochains.OrdCochain U ℱ p) := rfl

/-- The differential from degree `p` to degree `p + 1` is the ordered Čech differential. -/
@[simp]
theorem orderedCechComplex_d (U : I → Opens X)
    (ℱ : TopCat.Presheaf AddCommGrpCat.{w} X) (p : ℕ) :
    (orderedCechComplex U ℱ).d p (p + 1) =
      AddCommGrpCat.ofHom (CechCochains.ordD U ℱ p) := by apply CochainComplex.of_d

end Stacks.Cech
