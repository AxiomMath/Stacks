module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedInducedStructureClosedImmersion

/-!
# An algebraic stack is a thickening of its reduction, at the reduction (Stacks 0BPT)

**Stacks 0BPT** records three things about the reduction `𝒳'_red` of an algebraic stack `𝒳'`
over `S`, in the sense of **Stacks 050C**.

1. `𝒳'` is a thickening of its reduction `𝒳'_red`.
2. If `𝒳 ⊆ 𝒳'` is a thickening of algebraic stacks, then `𝒳'_red = 𝒳_red ⊆ 𝒳`.
3. In other words, `𝒳 = 𝒳'_red` exactly when `𝒳` is a reduced algebraic stack.

This file states all three at *the* reduction, `AlgebraicGeometry.Stack.stackReduction`, with no
hypothesis beyond the data of the source: an algebraic stack for (1), a thickening for (2) and (3).

## Main results

* `AlgebraicGeometry.Stack.isThickening_stackReduction_inclusion`: **assertion (1)**.
* `AlgebraicGeometry.Stack.essImage_stackReduction_eq_of_isThickening`: **assertion (2)**.
* `AlgebraicGeometry.Stack.essImage_stackReduction_eq_essImage_iff_isReducedStack`:
  **assertion (3)**.

## Implementation notes

The reduction `𝒳'_red` is `AlgebraicGeometry.Stack.stackReduction 𝒳'`: the full subcategory of
`𝒳'` cut out by an object property which is a reduction in the tagged sense
`AlgebraicGeometry.Stack.IsReduction` of Definition 050C, with its inclusion. Such a property
exists by the existence half of **Stacks 0509**
(`AlgebraicGeometry.Stack.exists_isReducedInducedStackStructure`) and is unique by its
uniqueness half (`AlgebraicGeometry.Stack.IsReduction.unique`), so `stackReduction` names the
reduction of the source and no choice is visible in the statements below.

Substacks of `𝒳'` are object properties of `𝒳'`, and equality of substacks is equality of those
properties, as in `AlgebraicGeometry.Stack.IsClosedSubstack` (**Stacks 04YM**). A 1-morphism
`j` into `𝒳'` is read as a substack of `𝒳'` through the essential image of its underlying functor,
which is the substack `j` factors through as an equivalence by **Stacks 0506** when `j` is an
immersion. So "`𝒳'_red = 𝒳_red`" says that the reduction of `𝒳'` and the composite of the
reduction of `𝒳` with the thickening `𝒳 ⟶ 𝒳'` cut out the same substack of `𝒳'`, and
"`𝒳 = 𝒳'_red`" that the reduction of `𝒳'` and the thickening cut out the same substack.

The earlier statements of `StacksFrontier.AlgebraicGeometry.Stacks.ThickeningReduction` hold for an
arbitrary `AlgebraicGeometry.Stack.StackReduction`, and the one of assertion (2) there carries
target locality of closed immersions of algebraic spaces as an instance argument. Here that
locality is `AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fppf` (**Stacks 0420** at
the fppf precoverage), a global instance proved from the fpqc form, so it is resolved and not
assumed.

## References

* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 050C](https://stacks.math.columbia.edu/tag/050C)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 0BPS](https://stacks.math.columbia.edu/tag/0BPS)
* [Stacks Project, Tag 0BPT](https://stacks.math.columbia.edu/tag/0BPT)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0BPT, assertion (1).** An algebraic stack `𝒳'` over `S` is a thickening of its
reduction `𝒳'_red` (**Stacks 050C**): the inclusion of the reduction is a closed immersion which
is surjective on points, the two clauses of `AlgebraicGeometry.Stack.IsThickening`
(**Stacks 0BPP**). -/
@[stacks 0BPT "assertion (1): an algebraic stack is a thickening of its reduction"]
theorem isThickening_stackReduction_inclusion (𝒳' : AlgebraicStacks.{u, w} B S hS) :
    IsThickening (stackReduction 𝒳').inclusion :=
  isThickening_stackReductionInclusion (stackReduction 𝒳')

/-- The essential image of a composite with a fully faithful functor is the essential image of
that functor exactly when the first factor is essentially surjective. -/
private theorem essImage_comp_eq_essImage_iff {𝒵 𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒵 ⟶ 𝒳) (i : 𝒳 ⟶ 𝒳') [(CatFiberedInGroupoids.homFunctor i.hom).Full]
    [(CatFiberedInGroupoids.homFunctor i.hom).Faithful] :
    (CatFiberedInGroupoids.homFunctor (f ≫ i).hom).essImage =
        (CatFiberedInGroupoids.homFunctor i.hom).essImage ↔
      (CatFiberedInGroupoids.homFunctor f.hom).essImage = ⊤ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · funext z
    refine propext ⟨fun _ => trivial, fun _ => ?_⟩
    have hz : (CatFiberedInGroupoids.homFunctor i.hom).essImage
        ((CatFiberedInGroupoids.homFunctor i.hom).obj z) := ⟨z, ⟨Iso.refl _⟩⟩
    rw [← h] at hz
    obtain ⟨x, ⟨e⟩⟩ := hz
    exact ⟨x, ⟨(CatFiberedInGroupoids.homFunctor i.hom).preimageIso e⟩⟩
  · funext y
    refine propext ⟨fun ⟨x, ⟨e⟩⟩ => ⟨_, ⟨e⟩⟩, fun ⟨z, ⟨e⟩⟩ => ?_⟩
    have hz : (CatFiberedInGroupoids.homFunctor f.hom).essImage z := by
      rw [h]
      trivial
    obtain ⟨x, ⟨e'⟩⟩ := hz
    exact ⟨x, ⟨(CatFiberedInGroupoids.homFunctor i.hom).mapIso e' ≪≫ e⟩⟩

/-- **Stacks 0BPT, assertion (2).** Let `i : 𝒳 ⟶ 𝒳'` be a thickening of algebraic stacks over
`S`. Then `𝒳'_red = 𝒳_red ⊆ 𝒳`: the reduction of `𝒳'` is the substack of `𝒳'` cut out by the
reduction of `𝒳` included through `i`, and it lies in the substack cut out by `𝒳`.

The composite of the inclusion of `𝒳_red` with `i` is again a thickening by **Stacks 0BPS** and
has reduced source, so its essential image is a reduction of `𝒳'` in the sense of
`AlgebraicGeometry.Stack.IsReduction`; so is that of the inclusion of `𝒳'_red`, and the two agree
by uniqueness of the reduction (**Stacks 0509**). -/
@[stacks 0BPT "assertion (2): a thickening has the same reduction as its ambient stack"]
theorem essImage_stackReduction_eq_of_isThickening {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    (CatFiberedInGroupoids.homFunctor (stackReduction 𝒳').inclusion.hom).essImage =
        (CatFiberedInGroupoids.homFunctor ((stackReduction 𝒳).inclusion ≫ i).hom).essImage ∧
      (CatFiberedInGroupoids.homFunctor (stackReduction 𝒳').inclusion.hom).essImage ≤
        (CatFiberedInGroupoids.homFunctor i.hom).essImage := by
  have heq : (CatFiberedInGroupoids.homFunctor (stackReduction 𝒳').inclusion.hom).essImage =
      (CatFiberedInGroupoids.homFunctor ((stackReduction 𝒳).inclusion ≫ i).hom).essImage :=
    IsReduction.unique B S hS (stackReduction 𝒳').isReduction
      (stackReductionOfThickening (stackReduction 𝒳) i hi).isReduction
  refine ⟨heq, ?_⟩
  rw [heq]
  exact fun _ ⟨_, ⟨e⟩⟩ => ⟨_, ⟨e⟩⟩

/-- **Stacks 0BPT, assertion (3).** Let `i : 𝒳 ⟶ 𝒳'` be a thickening of algebraic stacks over
`S`. Then `𝒳 = 𝒳'_red` — the reduction of `𝒳'` and `𝒳` cut out the same substack of `𝒳'` —
exactly when `𝒳` is a reduced algebraic stack.

By assertion (2) the reduction of `𝒳'` is the substack cut out by the reduction of `𝒳` through
`i`; since `i` is fully faithful (**Stacks 0506**), that is the substack cut out by `i` exactly
when the reduction of `𝒳` is all of `𝒳`, which is reducedness of `𝒳` by
`AlgebraicGeometry.Stack.isReducedStack_iff_essImage_stackReduction_eq_top`. -/
@[stacks 0BPT "assertion (3): a thickening is the reduction of its ambient stack exactly when it
is reduced"]
theorem essImage_stackReduction_eq_essImage_iff_isReducedStack
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    (CatFiberedInGroupoids.homFunctor (stackReduction 𝒳').inclusion.hom).essImage =
        (CatFiberedInGroupoids.homFunctor i.hom).essImage ↔
      IsReducedStack B S hS 𝒳 := by
  obtain ⟨_, _⟩ := AlgebraicStacks.full_and_faithful_homFunctor_of_isImmersion i
    (AlgebraicStacks.isImmersion_of_isClosedImmersion B S hS i hi.1)
  rw [(essImage_stackReduction_eq_of_isThickening i hi).1, essImage_comp_eq_essImage_iff,
    isReducedStack_iff_essImage_stackReduction_eq_top]

end AlgebraicGeometry.Stack

end
