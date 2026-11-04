module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FlatSliceExtension
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.SequentialColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionExists
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ResolutionByExtensionsByZero
import StacksCore.Tactic.StacksAttribute

/-!
# Every complex of sheaves of modules receives a quasi-isomorphism from a K-flat complex

Let `(C, O)` be a ringed site. Every cochain complex `G` of `O`-modules admits a
quasi-isomorphism `P ⟶ G` with `P` K-flat. This is the existence half of Stacks 06YS, and it
is what makes the derived tensor product of Stacks 06YU well defined.

The proof is the one in the source, assembled from parts that are already in the library. Stacks 077J
produces a ladder `K_1 ⟶ K_2 ⟶ ⋯` of bounded above complexes, each resolving an upper
truncation of `G`, whose terms are direct sums of extensions by zero `j_{U!} O_U` of the
structure sheaves of the slice sites, and whose colimit maps to `G` by a quasi-isomorphism.
Each `j_{U!} O_U` is a flat `O`-module (Stacks 03EV) and a direct sum of flat modules is flat
(Stacks 05NG), so each `K_n` is a bounded above complex of flat modules, hence K-flat by
Stacks 06YQ; and a sequential colimit of K-flat complexes is K-flat by Stacks 06YE. So the
colimit of the ladder is the required K-flat complex and the colimit comparison is the
required quasi-isomorphism.

## Main results

* `Stacks.SheafOfModules.exists_kFlat_quasiIso`: every cochain complex of sheaves of modules on
  a ringed site receives a quasi-isomorphism from a K-flat complex.

Flatness of a direct sum of extensions by zero of structure sheaves of slices,
`Stacks.SheafOfModules.isFlat_of_isSumOfExtensionByZeroStructureSheaves`, is imported from
`StacksFrontier/CategoryTheory/Sites/Cohomology/KFlat/ResolutionExists.lean`, where it is stated
without the sheafification hypotheses on the site that this file carries.

## Implementation notes

Only the existence assertion of 06YS is proved here, not the source's further assertions that
the K-flat complex can be taken to have flat terms and that the quasi-isomorphism can be taken
termwise surjective; the tag is carried with that qualification. Those two assertions are not
needed for Stacks 06YU, which is what this file exists to serve, and the first of them would
require in addition that a filtered colimit of flat modules is flat.

The object universe of the site is independent of its morphism and section universes.  The
resolution is not the one of Stacks 077J by direct sums of extensions by zero `j_{U!}O_U`,
whose flatness rests on a sheafification comparison pinning the ring universe to the *morphism*
universe of the site; it is the one of
`Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize`, whose ladder is resolved
by flat modules supplied by a flat cover and which carries no relation between the three
universes.  That is what makes this statement available for the small étale site of an
algebraic space, whose objects form a type one universe above its morphisms.

The two spellings `AlgebraicGeometry.RingedSite.ringSheaf X` and
`Stacks.SheafOfModules.Tensor.ringSheaf X.O` of the underlying sheaf of rings are definitionally
  equal, both
being `(sheafCompose X.J (forget₂ CommRingCat RingCat)).obj X.O`, so the 077J ladder and the
K-flatness predicate may be used side by side.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 077J](https://stacks.math.columbia.edu/tag/077J)
* [Stacks Project, Tag 03EV](https://stacks.math.columbia.edu/tag/03EV)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YE](https://stacks.math.columbia.edu/tag/06YE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- Every cochain complex of sheaves of modules on a ringed site receives a quasi-isomorphism
from a K-flat complex. This is the existence assertion of Stacks 06YS. -/
@[stacks 06YS "existence of a K-flat resolution"]
theorem exists_kFlat_quasiIso
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (p :
      P ⟶ G),
      IsKFlat X.O P ∧ QuasiIso p :=
  Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize X.O G

end Stacks.SheafOfModules

end
