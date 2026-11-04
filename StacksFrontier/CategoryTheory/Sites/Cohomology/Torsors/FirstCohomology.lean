module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology.AbelianTorsor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology.FiberTorsor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology.PushoutExtension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology.EquivH1

/-!
# First cohomology and torsors

For an abelian sheaf on a site, the isomorphism classes of torsors under the
sheaf are canonically in bijection with its first cohomology group.  This file
re-exports four parts:

* `AbelianTorsor`: torsors under an abelian sheaf, their isomorphism classes, differences
  of sections, and the free abelian presheaf on a torsor;
* `FiberTorsor`: the fiber of a short exact sequence over a global section as a torsor;
* `PushoutExtension`: the pushout extension of a torsor, its extension class, and the class
  of a torsor in first cohomology;
* `EquivH1`: the canonical bijection between isomorphism classes of torsors and first
  cohomology, its characterization, normalization and naturality, and the triviality of
  torsors when first cohomology vanishes.
-/
