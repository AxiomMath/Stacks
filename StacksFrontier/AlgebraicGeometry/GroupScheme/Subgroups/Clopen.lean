module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs

/-!
# Open subgroup schemes that are also closed

An open subgroup scheme of a group scheme `G` is also a *closed* subgroup scheme as soon as its
image in `G` is closed, because an immersion with closed image is a closed immersion. The image is
closed whenever `G` is the disjoint union of a family of open subschemes one of which is the
subgroup: the complement of one member of such a family is the union of the others, which is open.

Applied to the decomposition of the Picard scheme `Pic_{X/k}` of a smooth projective curve `X` over
a separably closed field `k` into its degree components `Pic^d_{X/k}` (clause (1) of [Stacks,
Tag 0BA0]), this shows that the degree-zero component `Pic^0_{X/k}` is closed as well as open: the
closedness half of clause (3).

## Main results

* `AlgebraicGeometry.isClosed_range_of_pairwiseDisjoint_of_iUnion_range_eq_univ`: one member of a
  family of open immersions with pairwise disjoint ranges covering the target has closed range.
* `AlgebraicGeometry.OpenSubgroupScheme.isClosedImmersion_of_isClosed_range`: an open subgroup
  scheme with closed image is a closed immersion.
* `AlgebraicGeometry.OpenSubgroupScheme.toClosedSubgroupScheme`: the resulting closed subgroup
  scheme, on the same carrier and the same inclusion.
* `AlgebraicGeometry.OpenSubgroupScheme.isClosedImmersion_of_degreeDecomposition` and
  `AlgebraicGeometry.OpenSubgroupScheme.toClosedSubgroupSchemeOfDegreeDecomposition`:
  **Tag 0BA0, the closedness half of clause (3)**, read off from the degree decomposition of clause
  (1).

## Implementation notes

The representability of the Picard functor (Tag 0B9Z) and the openness of its degree subfunctors
(Tag 0B9T) enter the last two results as hypotheses, in the form of a `ℤ`-indexed family of open
immersions into the group scheme with pairwise disjoint ranges covering it.

The decomposition is phrased by the ranges of the inclusions rather than as a colimit cofan so that
the index type may live in any universe, which a `ℤ`-indexed decomposition of `Scheme.{u}` needs.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 047D](https://stacks.math.columbia.edu/tag/047D)
-/

@[expose] public section

open CategoryTheory

universe v u

namespace AlgebraicGeometry

/-- **One member of a disjoint open cover by immersions has closed range.** The complement of the
range of `j d₀` is the union of the ranges of the `j d` for `d ≠ d₀`, each of which is open. -/
theorem isClosed_range_of_pairwiseDisjoint_of_iUnion_range_eq_univ {σ : Type v} {Y : Scheme.{u}}
    {g : σ → Scheme.{u}} (j : ∀ d, g d ⟶ Y) [∀ d, IsOpenImmersion (j d)]
    (hdisj : Pairwise fun d e => Disjoint (Set.range (j d).base) (Set.range (j e).base))
    (hcover : ⋃ d, Set.range (j d).base = Set.univ) (d₀ : σ) :
    IsClosed (Set.range (j d₀).base) := by
  rw [← isOpen_compl_iff]
  have hcompl : (Set.range (j d₀).base)ᶜ = ⋃ d ∈ {d : σ | d ≠ d₀}, Set.range (j d).base := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hx
      obtain ⟨d, hd⟩ := Set.mem_iUnion.mp (hcover ▸ Set.mem_univ x)
      exact ⟨d, fun h => hx (h ▸ hd), hd⟩
    · rintro ⟨d, hd, hx⟩ hmem
      exact Set.disjoint_iff_forall_ne.mp (hdisj hd) hx hmem rfl
  rw [hcompl]
  exact isOpen_biUnion fun d _ => (j d).isOpenEmbedding.isOpen_range

namespace OpenSubgroupScheme

variable {S : Scheme.{u}} {G : Grp (Over S)}

/-- **An open subgroup scheme whose image is closed is a closed immersion.** An open immersion is
an immersion, and an immersion with closed image is a closed immersion. -/
theorem isClosedImmersion_of_isClosed_range (H : OpenSubgroupScheme G)
    (h : IsClosed (Set.range H.ι.hom.hom.left.base)) :
    IsClosedImmersion H.ι.hom.hom.left :=
  have := H.isOpenImmersion
  IsClosedImmersion.of_isPreimmersion _ h

/-- **An open subgroup scheme whose image is closed is a closed subgroup scheme**, on the same
carrier and with the same inclusion: only the property of the inclusion changes. -/
def toClosedSubgroupScheme (H : OpenSubgroupScheme G)
    (h : IsClosed (Set.range H.ι.hom.hom.left.base)) :
    ClosedSubgroupScheme G where
  carrier := H.carrier
  ι := H.ι
  isClosedImmersion := H.isClosedImmersion_of_isClosed_range h

/-- **Stacks Project, Tag 0BA0, the closedness half of clause (3).** Let `G` be a group scheme over
a field `k`, presented as the disjoint union of a `ℤ`-indexed family of open subschemes `P d` (for
the Picard scheme of a smooth projective curve, its degree components). An open subgroup scheme `H`
of `G` whose image is the degree-zero member of that family has closed image, so the inclusion
`H ⟶ G` is a closed immersion as well as an open one. -/
theorem isClosedImmersion_of_degreeDecomposition {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G) {P : ℤ → Scheme.{u}}
    (j : ∀ d : ℤ, P d ⟶ G.X.left) [∀ d, IsOpenImmersion (j d)]
    (hdisj : Pairwise fun d e => Disjoint (Set.range (j d).base) (Set.range (j e).base))
    (hcover : ⋃ d, Set.range (j d).base = Set.univ)
    (hH : Set.range H.ι.hom.hom.left.base = Set.range (j 0).base) :
    IsClosedImmersion H.ι.hom.hom.left :=
  H.isClosedImmersion_of_isClosed_range
    (hH ▸ isClosed_range_of_pairwiseDisjoint_of_iUnion_range_eq_univ j hdisj hcover 0)

/-- **Stacks Project, Tag 0BA0, the closedness half of clause (3)**, as a closed subgroup scheme.
Together with the given `OpenSubgroupScheme` this exhibits the degree-zero component of the Picard
scheme of a curve as an open *and closed* subgroup scheme, on one carrier and one inclusion. -/
noncomputable def toClosedSubgroupSchemeOfDegreeDecomposition {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G) {P : ℤ → Scheme.{u}}
    (j : ∀ d : ℤ, P d ⟶ G.X.left) [∀ d, IsOpenImmersion (j d)]
    (hdisj : Pairwise fun d e => Disjoint (Set.range (j d).base) (Set.range (j e).base))
    (hcover : ⋃ d, Set.range (j d).base = Set.univ)
    (hH : Set.range H.ι.hom.hom.left.base = Set.range (j 0).base) :
    ClosedSubgroupScheme G :=
  H.toClosedSubgroupScheme
    (hH ▸ isClosed_range_of_pairwiseDisjoint_of_iUnion_range_eq_univ j hdisj hcover 0)

end OpenSubgroupScheme

end AlgebraicGeometry

end
