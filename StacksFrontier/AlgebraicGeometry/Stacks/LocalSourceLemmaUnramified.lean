module

public import StacksFrontier.AlgebraicGeometry.Stacks.LocalSourceLemmaFurtherInstances
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyLocusOnSpaces
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyLocus

/-!
# Unramifiedness as an instance of the local-source lemma

**Stacks 06M3** takes three properties `𝒫`, `𝒬`, `ℛ` of morphisms of algebraic spaces and
produces, for a 1-morphism of algebraic stacks representable by algebraic spaces and having
`𝒬`, a maximal open substack of the source on which it has `𝒫`, compatible with base change
along a morphism with `ℛ`. Two of its four hypotheses are about morphisms of algebraic spaces
alone: (3) every morphism `f : X ⟶ Y` of algebraic spaces with `𝒬` has a largest open subspace
`W(𝒫, f) ⊆ X` on which `f` has `𝒫`, and (4) for such an `f` and any `g : Y' ⟶ Y` with `ℛ`, the
identity `Y' ×_Y W(𝒫, f) = W(𝒫, f')` holds for the base change `f'`.

**Stacks 06M5** lists the triples for which the four hypotheses hold, giving references for (3)
and (4). This file carries the third entry of that list, at `𝒬 = ` locally of finite type,
`ℛ = ∅` and `𝒫 = ` unramified, whose reference is **Stacks 05W2**;
`StacksFrontier/AlgebraicGeometry/Stacks/LocalSourceLemmaInstances.lean` carries entries (1) and
(2), at `𝒫 = ` relative dimension `≤ d` and at `𝒫 = ` locally quasi-finite.

This is the entry **Stacks 06N2** needs. Entry (5), at `𝒫 = ` étale, is the one its statement
names, but the source obtains entry (5) by combining this entry with entry (4), at `𝒫 = ` flat,
and it is this entry whose `ℛ` is empty — so it is the one whose clause (4) applies to a base
change along a field-valued point, which is not flat. See the module documentation of
`StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale`.

## Main results

* `AlgebraicGeometry.Space.exists_isGreatest_isUnramified`: hypothesis (3) of Stacks 06M3 at
  `𝒫 = ` unramified, in the shape the lemma consumes.
* `AlgebraicGeometry.Space.eq_preimage_of_isGreatest_isUnramified`: hypothesis (4) of
  Stacks 06M3 at `𝒫 = ` unramified, for an arbitrary base change since the entry's `ℛ` is `∅`.
* `AlgebraicGeometry.Space.isUnramified_unramifiedLocus` and
  `AlgebraicGeometry.Space.le_unramifiedLocus`: the two clauses which make
  `AlgebraicGeometry.Space.unramifiedLocus` the largest open subspace of the source on which
  the morphism is unramified.
* `AlgebraicGeometry.Space.unramifiedLocus_preimage_of_isPullback`: that open subspace commutes
  with an arbitrary base change.
* `AlgebraicGeometry.Space.isUnramifiedAt_iff_of_isOpenSubspace`: unramifiedness at a point is
  unchanged by restricting the source to an open subspace containing the point.

## Implementation notes

The open subspace is `AlgebraicGeometry.Space.unramifiedLocus`, part (1) of **Stacks 05W2**,
which the library already has together with the identification of its point set as the set of
points at which the morphism is unramified. What this file adds is that it is *largest*, which
the source leaves implicit: being unramified is being unramified at every point
(`AlgebraicGeometry.Space.isUnramified_tfae`, the equivalence of its clauses (1) and (2), which
is **Stacks 03ZK**), and unramifiedness at a point does not see the restriction of the source to
an open subspace, so the point set of any open subspace on which the morphism is unramified
lands in the point set of the locus, and part (1) of **Stacks 03BZ** turns that containment of
point sets into a containment of open subspaces.

Neither of those two clauses carries the tag 05W2: part (1) of that lemma asserts only the
existence of an open subspace whose point set is the set of points of unramifiedness, and says
nothing about the restriction of the morphism to it being unramified nor about maximality. The
tag that covers them is 06M5, on the two statements of hypotheses (3) and (4) below, which is
where the source makes those two assertions.

Neither clause needs a finiteness hypothesis, because unramifiedness at a point is itself
defined by an open neighbourhood on which the morphism is unramified. The statements are
therefore stronger than hypothesis (3) of Stacks 06M3 at `𝒬 = ` locally of finite type, which
is what the entry asks for. Hypothesis (4) does use local finite type: it is read off part (2)
of Stacks 05W2, `AlgebraicGeometry.Space.setOf_isUnramifiedAt_eq_preimage_of_isPullback`,
whose proof needs it.

Stacks 06M3 takes hypotheses (3) and (4) quantified over largest open subspaces rather than
over a chosen one, so the statements below are given in that shape, as
`AlgebraicGeometry.Stacks.LocalSourceLemmaInstances` does for the other two entries; a greatest
element of an ordered type is unique, so both quantified forms reduce to the canonical locus.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 03ZK](https://stacks.math.columbia.edu/tag/03ZK)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 05W2](https://stacks.math.columbia.edu/tag/05W2)
* [Stacks Project, Tag 06M3](https://stacks.math.columbia.edu/tag/06M3)
* [Stacks Project, Tag 06M5](https://stacks.math.columbia.edu/tag/06M5)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Locus

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 05W2, part (1).** The restriction of a morphism of algebraic spaces over `S` to
`AlgebraicGeometry.Space.unramifiedLocus` is unramified.

Every point of that open subspace is carried to a point at which the morphism is unramified,
by `AlgebraicGeometry.Space.range_pointsMap_unramifiedLocus`, and unramifiedness at a point is
unchanged by the restriction; being unramified at every point is being unramified, which is the
equivalence of clauses (1) and (2) of `AlgebraicGeometry.Space.isUnramified_tfae`.

This is left untagged: part (1) of Stacks 05W2 asserts only that the set of points of
unramifiedness is the point set of an open subspace, not that the morphism is unramified on
that open subspace. Both are needed for hypothesis (3) of Stacks 06M3, so the tag sits on
`AlgebraicGeometry.Space.exists_isGreatest_isUnramified` below. -/
theorem isUnramified_unramifiedLocus (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsUnramified B S hS ((unramifiedLocus B S hS hX f).1.ι ≫ f) := by
  refine ((isUnramified_tfae B S hS (unramifiedLocus B S hS hX f).2.1 hY
    ((unramifiedLocus B S hS hX f).1.ι ≫ f)).out 1 2).2 fun x' => ?_
  have hmem : pointsMap B S hS (unramifiedLocus B S hS hX f).1.toFunctor
      (unramifiedLocus B S hS hX f).1.ι x' ∈
      {x : points B S hS X | IsUnramifiedAt B S hS f x} := by
    rw [← range_pointsMap_unramifiedLocus B S hS hX f]
    exact Set.mem_range_self x'
  exact (isUnramifiedAt_iff_of_isOpenSubspace B S hS hX hY (unramifiedLocus B S hS hX f).1
    (unramifiedLocus B S hS hX f).2 f x').1 hmem

/-- **Stacks 05W2, part (1).** Every open subspace of the source on which a morphism of
algebraic spaces over `S` is unramified is contained in
`AlgebraicGeometry.Space.unramifiedLocus`.

The morphism is unramified at every point of such an open subspace, hence — unramifiedness at a
point not seeing the restriction — at every point of its image, so its point set is contained in
that of the locus; part (1) of **Stacks 03BZ** turns that into the containment of open
subspaces.

Left untagged for the same reason as
`AlgebraicGeometry.Space.isUnramified_unramifiedLocus`: maximality is not part of the assertion
of part (1) of Stacks 05W2. -/
theorem le_unramifiedLocus (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (U : {U : Subfunctor X // IsOpenSubspace B S hS U})
    (hU : IsUnramified B S hS (U.1.ι ≫ f)) :
    U ≤ unramifiedLocus B S hS hX f := by
  have hat := ((isUnramified_tfae B S hS U.2.1 hY (U.1.ι ≫ f)).out 1 2).1 hU
  refine le_of_range_pointsMap_ι_subset B S hS (unramifiedLocus B S hS hX f).2 ?_
  rw [range_pointsMap_unramifiedLocus]
  rintro x ⟨x', rfl⟩
  exact (isUnramifiedAt_iff_of_isOpenSubspace B S hS hX hY U.1 U.2 f x').2 (hat x')

/-! ### Hypotheses (3) and (4) of Stacks 06M3 for unramifiedness -/

end Locus

section BaseChange

/-- **Stacks 06M5, third entry, hypothesis (4) of Stacks 06M3, for the canonical open
subspace.** In a cartesian square of algebraic spaces over `S` whose right vertical arrow `f`
is locally of finite type, the open unramified locus of the base change `f'` is the inverse
image of the open unramified locus of `f`.

No condition is imposed on the base change: the source writes `ℛ = ∅` for this entry, and
part (2) of **Stacks 05W2**,
`AlgebraicGeometry.Space.setOf_isUnramifiedAt_eq_preimage_of_isPullback`, gives the invariance
of the set of points of unramifiedness under an arbitrary base change. On points both sides are
that set, by `AlgebraicGeometry.Space.range_pointsMap_unramifiedLocus` and the identification
`AlgebraicGeometry.Space.pointsRange_preimage` of the point set of an inverse image; the two
open subspaces then agree because part (1) of **Stacks 03BZ** is injective. -/
@[stacks 06M5 "entry (3), hypothesis (4) of Stacks 06M3 at 𝒬 = locally of finite type and \
𝒫 = unramified, for the canonical open subspace: the formation of the largest open subspace \
commutes with base change, for an arbitrary base change since the entry's ℛ is ∅, from \
Stacks 05W2", ega "IV 17.7.2" "more general"]
theorem unramifiedLocus_preimage_of_isPullback
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    (unramifiedLocus B S hS hX' f').1 = (unramifiedLocus B S hS hX f).1.preimage g' := by
  have hcat : IsPullback
      (ObjectProperty.homMk g' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk f' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y', hY'⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk g : (⟨Y', hY'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) sq
  refine eq_of_range_pointsMap_ι_eq B S hS (unramifiedLocus B S hS hX' f').2
    (isOpenSubspace_preimage B S hS g' (unramifiedLocus B S hS hX f).1 hX hX'
      (unramifiedLocus B S hS hX f).2) ?_
  rw [range_pointsMap_unramifiedLocus, pointsRange_preimage,
    range_pointsMap_unramifiedLocus]
  exact setOf_isUnramifiedAt_eq_preimage_of_isPullback B S hS hcat hf

end BaseChange

end Space

/-! ### The entry read as the hypotheses of Stacks 06M3 -/

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Hypothesis (3) of Stacks 06M3 at the second entry of Stacks 06M5**, in the shape
`AlgebraicGeometry.Stack.exists_isRelativePropertyLocus_of_hasRelativePropertyLocusOnSpaces`
takes it: at `𝒬 = ` locally of finite type and `𝒫 = ` locally quasi-finite. -/
theorem hasRelativePropertyLocusOnSpaces_isLocallyQuasiFinite :
    HasRelativePropertyLocusOnSpaces B S hS (Space.locallyQuasiFiniteProperty B S hS)
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k.hom) :=
  fun _ _ hX hY f hf => Space.exists_isGreatest_isLocallyQuasiFinite B S hS hX hY f hf

/-- **Hypothesis (4) of Stacks 06M3 at the second entry of Stacks 06M5**, in the shape
`AlgebraicGeometry.Stack.exists_isRelativePropertyLocus_of_hasRelativePropertyLocusOnSpaces`
takes it. The entry has `ℛ = ∅`, so the compatibility holds for an arbitrary base change and the
condition on the base change may be taken to be `⊤`. -/
theorem relativePropertyLocusBaseChange_isLocallyQuasiFinite :
    RelativePropertyLocusBaseChange B S hS (Space.locallyQuasiFiniteProperty B S hS)
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k.hom) ⊤ :=
  fun _ _ _ _ hX' hX hY' hY _ _ _ _ sq hf _ W hW W' hW' =>
    Space.eq_preimage_of_isGreatest_isLocallyQuasiFinite B S hS sq hX' hX hY' hY hf W hW W' hW'

/-- **Hypothesis (3) of Stacks 06M3 at the third entry of Stacks 06M5**, in the shape
`AlgebraicGeometry.Stack.exists_isRelativePropertyLocus_of_hasRelativePropertyLocusOnSpaces`
takes it: at `𝒬 = ` locally of finite type and `𝒫 = ` unramified. The locus exists for an
arbitrary morphism, so `𝒬` is not used. -/
theorem hasRelativePropertyLocusOnSpaces_isUnramified :
    HasRelativePropertyLocusOnSpaces B S hS (Space.unramifiedMorphismProperty B S hS)
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k.hom) :=
  fun _ _ hX hY f _ => (Space.exists_isGreatest_isUnramified B S hS hX hY f).imp fun _ h => h.1

/-- **Hypothesis (4) of Stacks 06M3 at the third entry of Stacks 06M5**, in the shape
`AlgebraicGeometry.Stack.exists_isRelativePropertyLocus_of_hasRelativePropertyLocusOnSpaces`
takes it. The entry has `ℛ = ∅`, so the compatibility holds for an arbitrary base change and
the condition on the base change may be
taken to be `⊤`. -/
@[ega "IV 17.7.2" "more general"]
theorem relativePropertyLocusBaseChange_isUnramified :
    RelativePropertyLocusBaseChange B S hS (Space.unramifiedMorphismProperty B S hS)
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k.hom) ⊤ :=
  fun _ _ _ _ hX' hX hY' hY _ _ _ _ sq hf _ W hW W' hW' =>
    Space.eq_preimage_of_isGreatest_isUnramified B S hS sq hX' hX hY' hY hf W hW W' hW'

end Stack

end AlgebraicGeometry

end
