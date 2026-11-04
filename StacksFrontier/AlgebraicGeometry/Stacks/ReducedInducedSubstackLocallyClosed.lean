module

public import Mathlib.Topology.LocallyClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.Reduction

/-!
# The reduced induced substack structure on a locally closed set of points (Stacks 06FK)

Let `𝒳` be an algebraic stack over `S` and let `T ⊆ |𝒳|` be a locally closed subset of its
space of points (**Stacks 04XL**). Write `∂T = T̄ \ T` for the boundary of `T`, so that
`|𝒳| \ ∂T` is Mathlib's `coborder T`. **Stacks 06FK** takes the open substack `𝒰 ⊆ 𝒳` with
`|𝒰| = |𝒳| \ ∂T` (**Stacks 06FJ**) and the reduced closed substack `𝒵 ⊆ 𝒰` with `|𝒵| = T`
(**Stacks 050C**), and asserts that

* `𝒵 ⟶ 𝒳`, the composite of a closed immersion with an open immersion, is an *immersion* of
  algebraic stacks, by **Stacks 0502**;
* `𝒵` is reduced;
* `|𝒵| = T` as subsets of `|𝒳|`.

Such a `𝒵` is called the *reduced induced substack structure* on `T`.

## Main results

* `AlgebraicGeometry.Stack.isClosed_preimage_pointsMap_openSubstack`: for an open substack `𝒰`
  of `𝒳` with `|𝒰| = |𝒳| \ ∂T`, the part of `T` seen inside `|𝒰|` is closed, for every subset
  `T`.
* `AlgebraicGeometry.Stack.exists_reducedInducedSubstack`: there are an open substack `𝒰` with
  `|𝒰| = |𝒳| \ ∂T` and a reduced induced algebraic stack structure `𝒵` of **Stacks 050C** on the
  part of `T` inside `|𝒰|` (a reduced closed substack of `𝒰`) such that `𝒵 ⟶ 𝒳` is an immersion,
  `𝒵` is reduced, and `|𝒵| = T` in `|𝒳|`.

## Implementation notes

The point topology `AlgebraicGeometry.Stack.pointTopology` of **Stacks 04Y8** is not a global
instance; it is written out with `@` in every statement mentioning `IsOpen`, `IsClosed`,
`IsLocallyClosed` or `coborder`.

## References

* [Stacks Project, Tag 042U](https://stacks.math.columbia.edu/tag/042U)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0502](https://stacks.math.columbia.edu/tag/0502)
* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 050C](https://stacks.math.columbia.edu/tag/050C)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 06FK](https://stacks.math.columbia.edu/tag/06FK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

variable {𝒵 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- An open immersion of algebraic stacks over `S` is an immersion. -/
theorem isImmersion_of_isOpenImmersion (i : 𝒵 ⟶ 𝒳)
    (hi : IsOpenImmersion B S hS i) :
    IsImmersion B S hS i :=
  ⟨hi.1, fun U y hy F hF he =>
    Space.isImmersion_of_isOpenImmersion B S hS (hi.2 U y hy F hF he)⟩

end AlgebraicStacks

variable {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **The part of `T` inside `|𝒳| \ ∂T` is closed there.** Let `T` be a subset of the points of
an algebraic stack `𝒳` over `S` and let `𝒰` be an open substack of `𝒳` whose point set is
`|𝒳| \ ∂T`, that is `coborder T`. Then the preimage of `T` along the point map of the inclusion
of `𝒰` is closed in `|𝒰|`. -/
theorem isClosed_preimage_pointsMap_openSubstack
    (T : Set (AlgebraicStacks.points B S hS 𝒳)) (𝒰 : OpenSubstack 𝒳)
    (h𝒰 : 𝒰.pointSet B S hS = @coborder _ (pointTopology B S hS 𝒳.val) T) :
    @IsClosed _
        (pointTopology B S hS
          (fullSubcategoryAlgebraicStack 𝒳 𝒰.property 𝒰.isAlgebraic).val)
        (AlgebraicStacks.pointsMap B S hS 𝒰.inclusion ⁻¹' T) := by
  let _ := pointTopology B S hS 𝒳.val
  let _ := pointTopology B S hS
    (fullSubcategoryAlgebraicStack 𝒳 𝒰.property 𝒰.isAlgebraic).val
  have hrange : Set.range (AlgebraicStacks.pointsMap B S hS 𝒰.inclusion) = coborder T := h𝒰
  have hpre : AlgebraicStacks.pointsMap B S hS 𝒰.inclusion ⁻¹' T =
      AlgebraicStacks.pointsMap B S hS 𝒰.inclusion ⁻¹' closure T := by
    refine Set.Subset.antisymm (Set.preimage_mono subset_closure) fun z hz => ?_
    have hboth : AlgebraicStacks.pointsMap B S hS 𝒰.inclusion z ∈ closure T ∩ coborder T :=
      ⟨hz, hrange ▸ Set.mem_range_self z⟩
    rwa [closure_inter_coborder] at hboth
  rw [hpre]
  exact isClosed_closure.preimage (continuous_pointsMap B S hS
    (fullSubcategoryAlgebraicStack 𝒳 𝒰.property 𝒰.isAlgebraic).val 𝒳.val
    𝒰.inclusion.hom.hom)

/-- **The reduced induced substack structure on a locally closed set of points.**
Let `𝒳` be an algebraic stack over `S` and let `T` be a locally closed subset of its space of
points, with boundary `∂T = T̄ \ T`. Then there are

* an open substack `𝒰` of `𝒳` with `|𝒰| = |𝒳| \ ∂T` (Mathlib's `coborder T`), and
* a reduced induced algebraic stack structure `𝒵` (**Stacks 050C**) on the part of `T` inside
  `|𝒰|`, that is, a reduced closed substack of `𝒰` with that set of points,

such that the composite `𝒵 ⟶ 𝒰 ⟶ 𝒳` of the two inclusions is an immersion, `𝒵` is reduced, and
the image of `|𝒵|` in `|𝒳|` is exactly `T`. -/
@[stacks 06FK "a locally closed T in |X|: the open substack U with |U| = |X| minus the boundary \
of T, the reduced induced closed substack Z of U on the points of T (Stacks 050C), the immersion \
Z -> U -> X, Z reduced, and |Z| = T in |X|"]
theorem exists_reducedInducedSubstack
    (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsLocallyClosed _ (pointTopology B S hS 𝒳.val) T) :
    ∃ (𝒰 : OpenSubstack 𝒳)
      (P : ObjectProperty
        (fullSubcategoryAlgebraicStack 𝒳 𝒰.property 𝒰.isAlgebraic).val.val.obj)
      (hP : IsAlgebraicStack.{u, w} B S hS
        (fullSubcategoryBased (fullSubcategoryAlgebraicStack 𝒳 𝒰.property 𝒰.isAlgebraic) P)),
      𝒰.pointSet B S hS = @coborder _ (pointTopology B S hS 𝒳.val) T ∧
      IsReducedInducedStackStructure B S hS
        (AlgebraicStacks.pointsMap B S hS 𝒰.inclusion ⁻¹' T) P ∧
      AlgebraicStacks.IsImmersion B S hS
        (fullSubcategoryInclusion (fullSubcategoryAlgebraicStack 𝒳 𝒰.property 𝒰.isAlgebraic)
          P hP ≫ 𝒰.inclusion) ∧
      IsReducedStack B S hS
        (fullSubcategoryAlgebraicStack (fullSubcategoryAlgebraicStack 𝒳 𝒰.property 𝒰.isAlgebraic)
          P hP) ∧
      Set.range (AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion (fullSubcategoryAlgebraicStack 𝒳 𝒰.property 𝒰.isAlgebraic)
          P hP ≫ 𝒰.inclusion)) = T := by
  let _ := pointTopology B S hS 𝒳.val
  let 𝒰 := OpenSubstack.ofIsOpen B S hS (coborder T) hT.isOpen_coborder
  have h𝒰 : 𝒰.pointSet B S hS = coborder T := OpenSubstack.pointSet_ofIsOpen _ _
  have hrange : Set.range (AlgebraicStacks.pointsMap B S hS 𝒰.inclusion) = coborder T := h𝒰
  obtain ⟨P, hP⟩ := exists_isReducedInducedStackStructure
    (fullSubcategoryAlgebraicStack 𝒳 𝒰.property 𝒰.isAlgebraic) _
    (isClosed_preimage_pointsMap_openSubstack B S hS T 𝒰 h𝒰)
  obtain ⟨hAP, hCI⟩ := hP.1.1.2
  refine ⟨𝒰, P, hAP, h𝒰, hP, ?_, hP.2 hAP, ?_⟩
  · exact AlgebraicStacks.isImmersion_comp B S hS _ _
      (AlgebraicStacks.isImmersion_of_isClosedImmersion B S hS _ hCI)
      (AlgebraicStacks.isImmersion_of_isOpenImmersion B S hS _ 𝒰.isOpenImmersion)
  · rw [AlgebraicStacks.pointsMap_comp, Set.range_comp, hP.1.2 hAP,
      Set.image_preimage_eq_inter_range, hrange]
    exact Set.inter_eq_left.2 subset_coborder

end AlgebraicGeometry.Stack

end
