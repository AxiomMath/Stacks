module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankLocus

/-!
# The open and closed subspace where a finite locally free module has rank `r`

Let `ℰ` be a finite locally free `𝒪_Y`-module on an algebraic space `Y` over a scheme `S`. Its
rank loci `|Y|_r ⊆ |Y|` (`AlgebraicGeometry.Space.rankLocus`) are open, pairwise disjoint and
cover `|Y|`, so each of them is also closed, its complement being the union of the others. The
open subspace `Y_r ⊆ Y` cut out by `|Y|_r` (Stacks 03BZ) is therefore an open and closed subspace,
and `ℰ|_{Y_r}` is finite locally free of rank `r`. This is the decomposition

`Y = Y_0 ⨿ Y_1 ⨿ Y_2 ⨿ …`

of `Y` into the open and closed subspaces where the rank of `ℰ` is `r`, as in Stacks 0ES2.

## Main definitions

* `AlgebraicGeometry.Space.rankSubspace`: the open subspace `Y_r` cut out by the rank locus.

## Main results

* `AlgebraicGeometry.Space.isClosed_rankLocus`: the rank loci of a finite locally free module are
  closed.
* `AlgebraicGeometry.Space.isOpenSubspace_rankSubspace` and
  `AlgebraicGeometry.Space.isClosedSubspace_rankSubspace`: `Y_r` is an open and a closed subspace.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_modulePullback_rankSubspace`: `ℰ|_{Y_r}` is
  finite locally free of rank `r`.

## References

* [Stacks Project, Tag 0ES2](https://stacks.math.columbia.edu/tag/0ES2)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Y : AlgebraicSpaces B S hS}
  (M : Modules.{u, u} B S hS Y.1 Y.2)

/-- The complement of a rank locus of a finite locally free module is the union of the other
rank loci. -/
theorem compl_rankLocus (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M) (n : ℕ) :
    (rankLocus M n)ᶜ = ⋃ (m : ℕ) (_ : m ≠ n), rankLocus M m := by
  ext y
  simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
  refine ⟨fun hy => ?_, fun ⟨m, hmn, hm⟩ hn => hmn (eq_of_mem_rankLocus_of_mem_rankLocus hm hn)⟩
  obtain ⟨m, hm⟩ := exists_mem_rankLocus hM y
  exact ⟨m, fun h => hy (h ▸ hm), hm⟩

/-- **The rank loci of a finite locally free module are closed**: the complement of one is the
union of the others, which are open. -/
theorem isClosed_rankLocus (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M) (n : ℕ) :
    IsClosed (rankLocus M n) := by
  rw [← isOpen_compl_iff, compl_rankLocus M hM n]
  exact isOpen_iUnion fun m => isOpen_iUnion fun _ => isOpen_rankLocus M m

/-- **The subspace `Y_r ⊆ Y` where `ℰ` has rank `r`**: the open subspace cut out by the rank
locus of `r` (Stacks 03BZ). -/
def rankSubspace (n : ℕ) : Subfunctor Y.1 :=
  openSubspaceOfPoints B S hS Y.1 (rankLocus M n)

/-- The set of points of `Y_r` is the rank locus of `r`. -/
theorem range_pointsMap_ι_rankSubspace (n : ℕ) :
    Set.range (pointsMap B S hS (rankSubspace M n).toFunctor (rankSubspace M n).ι) =
      rankLocus M n :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- `Y_r` is an open subspace. -/
theorem isOpenSubspace_rankSubspace (n : ℕ) : IsOpenSubspace B S hS (rankSubspace M n) :=
  isOpenSubspace_openSubspaceOfPoints B S hS Y.2 _ (isOpen_rankLocus M n)

/-- `Y_r` is a closed subspace when `ℰ` is finite locally free. -/
theorem isClosedSubspace_rankSubspace (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M)
    (n : ℕ) : IsClosedSubspace B S hS (rankSubspace M n) :=
  isClosedSubspace_openSubspaceOfPoints B S hS Y.2 _ (isOpen_rankLocus M n)
    (isClosed_rankLocus M hM n)

/-- **`ℰ|_{Y_r}` is finite locally free of rank `r`**: the image of `Y_r` on points is the rank
locus of `r` (`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_modulePullback_iff`). The
algebraic space structure on `Y_r` is an arbitrary proof, so that the statement applies to
whichever one a consumer carries. -/
theorem isFiniteLocallyFreeOfRank_modulePullback_rankSubspace
    (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M) (n : ℕ)
    (h : IsAlgebraicSpace B S hS (rankSubspace M n).toFunctor) :
    RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite B S hS (rankSubspace M n).toFunctor h)
      ((modulePullback B S hS (ObjectProperty.homMk (rankSubspace M n).ι :
        (⟨(rankSubspace M n).toFunctor, h⟩ : AlgebraicSpaces B S hS) ⟶ Y)).obj M) n :=
  (isFiniteLocallyFreeOfRank_modulePullback_iff
    (X := (⟨(rankSubspace M n).toFunctor, h⟩ : AlgebraicSpaces B S hS))
    (ObjectProperty.homMk (rankSubspace M n).ι) hM n).2
    (range_pointsMap_ι_rankSubspace M n).le

end AlgebraicGeometry.Space
