module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ComponentMultiplicity
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionClosedImmersion

/-!
# The dimension at a point as the supremum over the irreducible components through it

**Stacks 0DRZ** says that for a locally Noetherian algebraic stack `𝒳` over `S` and a point
`x ∈ |𝒳|` the dimension of Stacks 0AFN satisfies

`dim_x(𝒳) = sup_𝒯 dim_x(𝒯)`,

the supremum running over the irreducible components `𝒯` of `|𝒳|` through `x`, each endowed with
its induced reduced structure.

## Main definitions

* `AlgebraicGeometry.Stack.componentDimensionsAt`: the set of values `dim_x(𝒯)` appearing on the
  right-hand side — the dimensions of Stacks 0AFN at `x` of the reduced closed substacks supported
  on the irreducible components of `|𝒳|` through `x`.

## Main results

* `AlgebraicGeometry.Stack.sSup_componentDimensionsAt_le`: the inequality `sup_𝒯 dim_x(𝒯) ≤
  dim_x(𝒳)`, which is the half of **Stacks 0DRZ** the source gets from Stacks 0DRY.
* `AlgebraicGeometry.Stack.mem_componentDimensionsAt_of_isSmooth_chart`: a reduced closed substack
  supported on the closure of the image of an irreducible component of a smooth scheme chart
  contributes to that set, by Stacks 0DR5.
* `AlgebraicGeometry.Stack.dimensionSubNat_antitone`: the subtraction of Stacks 0AFN is antitone
  in the relative dimension.

## Implementation notes

The supremum is `sSup` in `EInt`, the codomain of Stacks 0AFN as the library takes it: `EInt` is
`WithBot (WithTop ℤ)` and a `CompleteLinearOrder`, so the supremum of the possibly infinite family
of components through `x` is total and needs no nonemptiness hypothesis. The one-sided bounds are
then `sSup_le` and `le_sSup`, and the statement is an equality of extended integers.

"The irreducible component `𝒯` endowed with its induced reduced structure" is not formed: the
existence half of **Stacks 0509** is not in the library, only the uniqueness half
(`AlgebraicGeometry.Stack.eq_of_isReducedStack_of_range_pointsMap_eq`), existence resting on the
half of Stacks 0507 that matches closed substacks with invariant closed subspaces of a
presentation. So the reduced structure enters as existentially bound data inside
`AlgebraicGeometry.Stack.componentDimensionsAt`: a value belongs to that set when *some* reduced
algebraic stack with a closed immersion into `𝒳` whose points are exactly the given component
realises it at a point over `x`. By the uniqueness half of Stacks 0509 such a substack is unique
once it exists, so the set is the source's family of values and no choice is hidden in it; and
since a component carrying no such substack simply contributes nothing, this form is at least as
strong as one that assumed existence.

The inequality `sup_𝒯 dim_x(𝒯) ≤ dim_x(𝒳)` is proved outright: each contributing substack has a
closed immersion into `𝒳` carrying its point to `x`, so **Stacks 0DRY**
(`AlgebraicGeometry.Stack.dimensionAtPoint_le_of_isClosedImmersion`) bounds its dimension by
`dim_x(𝒳)`, and `sSup_le` concludes.

### Stacks 0DRZ itself

The reverse inequality is the source's equation **Stacks 0DS0**, and Stacks 0DRZ itself is
`AlgebraicGeometry.Stack.dimensionAtPoint_eq_sSup_irreducibleComponents` in
`StacksFrontier/AlgebraicGeometry/Stacks/DimensionIrreducibleComponentsSupremum.lean`, which
combines
the inequality above with `AlgebraicGeometry.Stack.mem_componentDimensionsAt_of_isSmooth_chart`.

## References

* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DR5](https://stacks.math.columbia.edu/tag/0DR5)
* [Stacks Project, Tag 0DRY](https://stacks.math.columbia.edu/tag/0DRY)
* [Stacks Project, Tag 0DRZ](https://stacks.math.columbia.edu/tag/0DRZ)
* [Stacks Project, Tag 0DS0](https://stacks.math.columbia.edu/tag/0DS0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The subtraction of Stacks 0AFN is antitone in the relative dimension: a smaller relative
dimension leaves a larger difference. -/
theorem dimensionSubNat_antitone {d d' : ℕ} (h : d' ≤ d) (δ : WithBot ℕ∞) :
    dimensionSubNat δ d ≤ dimensionSubNat δ d' := by
  induction δ using WithBot.recBotCoe with
  | bot => rw [dimensionSubNat_bot, dimensionSubNat_bot]
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      rw [show ((⊤ : ℕ∞) : WithBot ℕ∞) = (⊤ : WithBot ℕ∞) from rfl, dimensionSubNat_top,
        dimensionSubNat_top]
    | coe n =>
      have hd : ∀ e : ℕ, dimensionSubNat (((n : ℕ∞) : WithBot ℕ∞)) e =
          (((n : ℤ) - (e : ℤ) : ℤ) : EInt) := fun _ => rfl
      rw [hd d, hd d', WithBotTop.coe_le_coe]
      omega

/-- The set of values `dim_x(𝒯)` of **Stacks 0DRZ**: an extended integer belongs to it when some
irreducible component `T` of `|𝒳|` through `x` carries a reduced closed substack of `𝒳` — a
reduced algebraic stack `𝒯` with a closed immersion `i : 𝒯 ⟶ 𝒳` whose points are exactly `T` —
which is locally Noetherian and whose dimension of Stacks 0AFN at its point over `x` is that
value.

The reduced induced structure on `T` is bound existentially rather than constructed because only
the uniqueness half of Stacks 0509 is available; by that uniqueness there is at most one such
substack for each `T`, so this is the source's family of values. -/
def componentDimensionsAt (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) : Set EInt :=
  {d | ∃ T : Set (points B S hS 𝒳.val.val 𝒳.val.property),
    T ∈ irreducibleComponents (points B S hS 𝒳.val.val 𝒳.val.property) ∧ x ∈ T ∧
      ∃ (𝒯 : AlgebraicStacks.{u, w} B S hS) (i : 𝒯 ⟶ 𝒳)
        (_ : AlgebraicStacks.IsClosedImmersion B S hS i) (_ : IsReducedStack B S hS 𝒯)
        (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
        (t : points B S hS 𝒯.val.val 𝒯.val.property),
        Set.range (pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property i.hom.hom) = T ∧
          pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property i.hom.hom t = x ∧
            d = dimensionAtPoint B S hS 𝒯 h𝒯 t}

/-- **The easy half of Stacks 0DRZ.** The supremum of the dimensions at `x` of the reduced
irreducible components of `|𝒳|` through `x` is at most `dim_x(𝒳)`.

Each contributing substack carries a closed immersion into `𝒳` taking its distinguished point to
`x`, so **Stacks 0DRY** bounds its dimension at that point by `dim_x(𝒳)`; the supremum of a set
of such bounds obeys the same bound. -/
theorem sSup_componentDimensionsAt_le (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) :
    sSup (componentDimensionsAt B S hS 𝒳 x) ≤ dimensionAtPoint B S hS 𝒳 h𝒳 x := by
  refine sSup_le ?_
  rintro d ⟨T, -, -, 𝒯, i, hi, -, h𝒯, t, -, hit, rfl⟩
  have hle := dimensionAtPoint_le_of_isClosedImmersion B S hS i hi h𝒯 h𝒳 t
  rwa [hit] at hle

/-- **Stacks 0DR5 feeding Stacks 0DRZ.** Let `f : U ⟶ 𝒳` be a smooth 1-morphism from the algebraic
stack of a scheme `U` of the site to a locally Noetherian algebraic stack, let `u ∈ U` lie over
`x ∈ |𝒳|`, and let `T'` be an irreducible component of `U` containing `u`. A reduced closed
substack `𝒯` of `𝒳` supported on the closure of the image of `T'`, with a point `t` over `x`,
contributes `dim_t(𝒯)` to the set of **Stacks 0DRZ**.

The closure of the image of `T'` is an irreducible component of `|𝒳|` by Stacks 0DR5, and it
contains `x`, which is the image of `u ∈ T'`. -/
theorem mem_componentDimensionsAt_of_isSmooth_chart (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hf : AlgebraicStacks.IsSmooth B S hS f)
    (u : (BigFppfOver.toScheme B S hS).obj U)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hu : AlgebraicStacks.chartPointMap B S hS U 𝒳 f u = x)
    (T' : Set ((BigFppfOver.toScheme B S hS).obj U))
    (hT' : T' ∈ irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U)) (huT' : u ∈ T')
    (𝒯 : AlgebraicStacks.{u, w} B S hS) (i : 𝒯 ⟶ 𝒳)
    (hi : AlgebraicStacks.IsClosedImmersion B S hS i) (hred : IsReducedStack B S hS 𝒯)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (t : points B S hS 𝒯.val.val 𝒯.val.property)
    (hrange :
      Set.range (pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property i.hom.hom) =
        closure (AlgebraicStacks.chartPointMap B S hS U 𝒳 f '' T'))
    (hit : pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property i.hom.hom t = x) :
    dimensionAtPoint B S hS 𝒯 h𝒯 t ∈ componentDimensionsAt B S hS 𝒳 x :=
  ⟨closure (AlgebraicStacks.chartPointMap B S hS U 𝒳 f '' T'),
    AlgebraicStacks.closure_image_chartPointMap_mem_irreducibleComponents B S hS U 𝒳 h𝒳 f hf T'
      hT',
    hu ▸ subset_closure ⟨u, huT', rfl⟩, 𝒯, i, hi, hred, h𝒯, t, hrange, hit, rfl⟩

end AlgebraicGeometry.Stack

end
