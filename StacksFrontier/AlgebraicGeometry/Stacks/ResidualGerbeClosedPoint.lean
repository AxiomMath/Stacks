module

public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeEquivalentConditions
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeLocallyNoetherian

/-!
# Closed points and residual gerbes on locally Noetherian algebraic stacks (Stacks 0H27)

Let `𝒳` be a locally Noetherian algebraic stack over `S` and `x ∈ |𝒳|` a point with residual
gerbe `𝒵_x ⊂ 𝒳` (**Stacks 06MU**, whose existence is **Stacks 0H22**). Then `x` is a closed point
of `|𝒳|` if and only if the inclusion `𝒵_x ⟶ 𝒳` is a closed immersion.

The source's proof. If `𝒵_x ⟶ 𝒳` is a closed immersion, it is a closed map on points
(**Stacks 0H20**, used by the source through **Stacks 0CL8**), and its image is `{x}`. Conversely,
if `x` is closed, let `𝒵 ⊂ 𝒳` be the reduced closed substack with `|𝒵| = {x}` (**Stacks 0509**).
It is locally Noetherian, its inclusion being an immersion, hence locally of finite type
(**Stacks 06FV**), over a locally Noetherian stack (**Stacks 06R6**). Being reduced, locally
Noetherian and one-point over `x`, it meets the specification of the residual gerbe, so it is
`𝒵_x` by the uniqueness assertion of **Stacks 06MT**.

## Main results

* `AlgebraicGeometry.Stack.isClosed_singleton_iff_isClosedImmersion_residualGerbeInclusion`:
  the equivalence, for every object property meeting the specification
  `AlgebraicGeometry.Stack.IsResidualGerbeAt` of the residual gerbe at `x`.
* `AlgebraicGeometry.Stack.exists_isResidualGerbeAt_and_isClosed_singleton_iff_isClosedImmersion`:
  **Stacks 0H27**, the residual gerbe at `x` taken from **Stacks 0H22**
  (`AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_isLocallyNoetherianStack`).

## References

* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 06FV](https://stacks.math.columbia.edu/tag/06FV)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MU](https://stacks.math.columbia.edu/tag/06MU)
* [Stacks Project, Tag 06R6](https://stacks.math.columbia.edu/tag/06R6)
* [Stacks Project, Tag 0CL8](https://stacks.math.columbia.edu/tag/0CL8)
* [Stacks Project, Tag 0H20](https://stacks.math.columbia.edu/tag/0H20)
* [Stacks Project, Tag 0H22](https://stacks.math.columbia.edu/tag/0H22)
* [Stacks Project, Tag 0H27](https://stacks.math.columbia.edu/tag/0H27)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The reduced closed substack on a closed point is the residual gerbe.** Let `𝒳` be a locally
Noetherian algebraic stack over `S`, `x` a closed point of `|𝒳|`, and `Q` an object property of
`𝒳` cutting out a reduced closed substack with `|𝒵_Q| = {x}` (Stacks 0509). Then `Q` meets the
specification of the residual gerbe at `x`: the closed substack is locally Noetherian by
**Stacks 06FV** and **Stacks 06R6**, and its one point lies over `x` because its inclusion is
injective on points (**Stacks 0H20**). -/
theorem isResidualGerbeAt_of_isClosedSubstack_of_range_eq_singleton
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack B S hS 𝒳)
    (x : AlgebraicStacks.points B S hS 𝒳) (Q : ObjectProperty 𝒳.val.val.obj)
    (hQc : IsClosedSubstack 𝒳 Q)
    (hpts : ∀ hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q),
      Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ)) = {x})
    (hred : ∀ hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q),
      IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ)) :
    IsResidualGerbeAt B S hS 𝒳 x Q := by
  obtain ⟨hiso, hQ, himm⟩ := hQc
  let i := fullSubcategoryInclusion 𝒳 Q hQ
  have hi : AlgebraicStacks.IsImmersion B S hS i :=
    AlgebraicStacks.isImmersion_of_isClosedImmersion B S hS i himm
  refine ⟨hiso, hQ, hred hQ, AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS i
    (AlgebraicStacks.isLocallyOfFiniteType_of_isImmersion B S hS i hi) h𝒳, ?_⟩
  let := pointTopology B S hS 𝒳.val
  let := pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val
  have hinj := (AlgebraicStacks.isEmbedding_pointsMap_of_isImmersion B S hS i hi).injective
  obtain ⟨z, hz⟩ : x ∈ Set.range (AlgebraicStacks.pointsMap B S hS i) :=
    (hpts hQ).symm ▸ Set.mem_singleton x
  refine ⟨z, fun z' => hinj ?_, hz⟩
  have hz' : AlgebraicStacks.pointsMap B S hS i z' ∈ ({x} : Set _) :=
    hpts hQ ▸ Set.mem_range_self z'
  exact (Set.mem_singleton_iff.1 hz').trans hz.symm

/-- **Stacks 0H27, for a given residual gerbe.** Let `𝒳` be a locally Noetherian algebraic stack
over `S` and `x ∈ |𝒳|`, and let `P` be an object property of `𝒳` meeting the specification
`AlgebraicGeometry.Stack.IsResidualGerbeAt` of the residual gerbe `𝒵_x` at `x`
(**Stacks 06MU**; such a `P` is unique by Stacks 06MT and exists by Stacks 0H22). Then `x` is a
closed point of `|𝒳|` if and only if the inclusion `𝒵_x ⟶ 𝒳` is a closed immersion. -/
theorem isClosed_singleton_iff_isClosedImmersion_residualGerbeInclusion
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack B S hS 𝒳)
    (x : AlgebraicStacks.points B S hS 𝒳)
    (P : ObjectProperty 𝒳.val.val.obj) (hP : IsResidualGerbeAt B S hS 𝒳 x P) :
    @IsClosed _ (pointTopology B S hS 𝒳.val) {x} ↔
      AlgebraicStacks.IsClosedImmersion B S hS (residualGerbeInclusion B S hS 𝒳 x P hP) := by
  let := pointTopology B S hS 𝒳.val
  refine ⟨fun hx => ?_, fun hcl => ?_⟩
  · obtain ⟨Q, ⟨hQc, hpts, hred⟩, -⟩ := existsUnique_reducedClosedSubstack B S hS 𝒳 {x} hx
    obtain rfl := eq_of_isResidualGerbeAt_of_bootstrap B S hS
      (isResidualGerbeAt_of_isClosedSubstack_of_range_eq_singleton B S hS 𝒳 h𝒳 x Q hQc hpts hred)
      hP
    exact hQc.2.choose_spec
  · let := pointTopology B S hS (residualGerbe B S hS 𝒳 x P hP).val
    have hrange : Set.range (AlgebraicStacks.pointsMap B S hS
        (residualGerbeInclusion B S hS 𝒳 x P hP)) = {x} := by
      obtain ⟨z, -, hzx⟩ := hP.2.choose_spec.2.2
      refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨z, hzx⟩, ?_⟩
      rintro _ ⟨z', rfl⟩
      exact pointsMap_eq_of_isResidualGerbeAt B S hS hP hP.2.choose z'
    rw [← hrange, ← Set.image_univ]
    exact AlgebraicStacks.isClosedMap_pointsMap_of_isClosedImmersion B S hS _ hcl _
      isClosed_univ

/-- **Stacks 0H27.** Let `𝒳` be a locally Noetherian algebraic stack over `S` and `x ∈ |𝒳|`.
The residual gerbe `𝒵_x ⊂ 𝒳` of `𝒳` at `x` exists (**Stacks 0H22**), and for it, `x` is a closed
point of `|𝒳|` if and only if the inclusion `𝒵_x ⟶ 𝒳` is a closed immersion.

The residual gerbe is the strictly full subcategory cut out by an object property meeting the
specification `AlgebraicGeometry.Stack.IsResidualGerbeAt` (**Stacks 06MU**), which is unique by
`AlgebraicGeometry.Stack.eq_of_isResidualGerbeAt_of_bootstrap`; the equivalence is
`AlgebraicGeometry.Stack.isClosed_singleton_iff_isClosedImmersion_residualGerbeInclusion`. -/
@[stacks 0H27]
theorem exists_isResidualGerbeAt_and_isClosed_singleton_iff_isClosedImmersion
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack B S hS 𝒳)
    (x : AlgebraicStacks.points B S hS 𝒳) :
    ∃ (P : ObjectProperty 𝒳.val.val.obj) (hP : IsResidualGerbeAt B S hS 𝒳 x P),
      (@IsClosed _ (pointTopology B S hS 𝒳.val) {x} ↔
        AlgebraicStacks.IsClosedImmersion B S hS (residualGerbeInclusion B S hS 𝒳 x P hP)) := by
  obtain ⟨P, hP⟩ := exists_isResidualGerbeAt_of_isLocallyNoetherianStack B S hS 𝒳 h𝒳 x
  exact ⟨P, hP, isClosed_singleton_iff_isClosedImmersion_residualGerbeInclusion B S hS 𝒳 h𝒳 x P hP⟩

end AlgebraicGeometry.Stack

end
