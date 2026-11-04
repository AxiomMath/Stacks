module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionBranchIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchComapCartier

/-!
# The branch bundle over `W` as a closed subscheme of the branch `D₁`

In the situation of [Stacks, Tag 0F97], let `W ⊆ Y` be a closed subscheme. The diagram base
changes along `W ↪ Y` (`Stacks.Chow.TensorZeroScheme.decompositionComap`), and condition (4) of
the tag presents the first closed subscheme of the base-changed diagram — the scheme `W₁` of the
case `W ⊆ D` of [Stacks, Tag 0F98] — as the total space of a line bundle over the restricted
divisor.

This file supplies the **closed immersion of that total space into the branch `D₁` of the
unrestricted diagram**, which is the ambient scheme the dévissage of [Stacks, Tag 0F98] computes
on, together with the two factorizations a consumer needs: through the structure morphism of the
base situation, and over `W ↪ Y`.

It is the datum `j` of
`isRationallyEquivalentToZeroWithin_properPushforward_zeroSection_branchSituation_subschemeι`
at `A = D₁`, and with it that statement computes clause (5) of [Stacks, Tag 0F96] on `D₁` with
carrier the preimage of `W` — the carrier
`Stacks.Chow.TensorZeroScheme.gysinChowBranch₁_flatPullbackChowProj_of_primeCycle` prescribes.

## Main results

* `Stacks.Chow.TensorZeroScheme.branchComapToBranch₁` — **the closed immersion
  `D₁ ∩ p^{-1}(W) ⟶ D₁`**, the base change of `D₁` along `p^{-1}(W) ↪ L`.
* `Stacks.Chow.TensorZeroScheme.isPullback_branchComapToBranch₁` — it sits in a cartesian square,
  whence it is a closed immersion.
* `Stacks.Chow.TensorZeroScheme.branchTotalSpaceToBranch₁` — **the closed immersion of the total
  space of the branch bundle over `W` into `D₁`**, obtained by composing with condition (4).
* `Stacks.Chow.TensorZeroScheme.branchTotalSpaceToBranch₁_comp_subschemeι_comp_proj` — it lies
  over `W ↪ Y`, which is what makes the carrier the preimage of `W`.

## Implementation notes

### No `sup` appears, so the `sup_comm` transport never arises

The obvious routes to a morphism out of `D₁ ∩ p^{-1}(W)` present that intersection as a join of
ideal sheaves, and then the two usable presentations are
`p^{-1}(W) ⊔ D₁` — the order
`AlgebraicGeometry.Scheme.IdealSheafData.supComapSubschemeIso` is stated in, which reads the
intersection inside `p^{-1}(W)` — and `D₁ ⊔ p^{-1}(W)`, the order whose `le_sup_left` inclusion
lands in `D₁`. They differ by `sup_comm`, an equality of *concrete ideal sheaves*; eliminating it
into a type would put a scheme under a `cast`, which this repository cannot reduce. (Where the
goal is a proposition depending only on the underlying closed subset the reordering is harmless
and is done inside `congrArg`, as in
`Stacks.Chow.TensorZeroScheme.schemeDeltaDimension_sup_comap_proj_of_le`; a morphism is data and
has no such escape.)

Nothing here needs either presentation. The base-changed subscheme is the *inverse image*
`D₁.comap (p^{-1}(W) ↪ L)`, not a join, and
`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeMap_of_comap` takes that inverse-image
identity as a **hypothesis** rather than writing it into its statement — exactly so that it applies
to any ideal sheaf equal to it with no transport. So
`Stacks.Chow.TensorZeroScheme.comap_branch₁_decompositionComap` is consumed as a hypothesis of that
lemma, in `Prop`, and no join, no `sup_comm` and no `Eq.rec` on a scheme occurs anywhere below.

A bespoke `AlgebraicGeometry.IsClosedImmersion.isIso_lift` isomorphism between the two join
presentations is therefore not needed either.

### Why the base of the bundle is not rewritten to `W`

The base of `branchSituation` over `W` stays spelled as the zero scheme of the restricted section,
never rewritten to `W` along
`Stacks.Chow.TensorZeroScheme.zeroIdeal_pullbackTensorSection_subschemeι_eq_bot`, for the reason
recorded in
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionBranchCarrier`: that equation is
between concrete ideal sheaves and an `Eq.rec` at it would put a line-bundle situation under a
`cast`.

### No `@[stacks]` attribute here

This is the base-change clause of [Stacks, Tag 0F97] combined with its condition (4), read as a
closed immersion into `D₁`; it asserts neither tag. Nor does it assert [Stacks, Tag 0F98], which
is a single identity of maps — see the convention note in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowMaps`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

namespace Stacks.Chow.TensorZeroScheme

variable {Y : Scheme.{u}} (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (W : Y.IdealSheafData)

/-! ### The restriction of `D₁` to `p^{-1}(W)`, as a closed subscheme of `D₁` -/

include h₁ h₂ in
/-- **The restriction of the branch `D₁` to `p^{-1}(W)`, as a closed subscheme of `D₁`.** This is
the morphism induced on closed subschemes by `p^{-1}(W) ↪ L`, from the first closed subscheme of
the base-changed diagram to `D₁`.

No join of ideal sheaves is formed: the source is the inverse image of `D₁`, by
`Stacks.Chow.TensorZeroScheme.comap_branch₁_decompositionComap`, which enters only as the
hypothesis `h` of `AlgebraicGeometry.Scheme.IdealSheafData.le_map_iff_comap_le`. -/
def branchComapToBranch₁ :
    (decompositionComap L₁ L₂ s R W).D₁.subscheme ⟶ R.normalize.D₁.subscheme :=
  Scheme.IdealSheafData.subschemeMap (decompositionComap L₁ L₂ s R W).D₁ R.normalize.D₁
    (W.comap R.normalize.p).subschemeι
    (Scheme.IdealSheafData.le_map_iff_comap_le.2
      (comap_branch₁_decompositionComap L₁ L₂ s R W).symm.le)

include h₁ h₂ in
/-- **The restriction of `D₁` to `p^{-1}(W)` is the base change of `D₁` along `p^{-1}(W) ↪ L`.**
This is `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeMap_of_comap` fed the
inverse-image identity
`Stacks.Chow.TensorZeroScheme.comap_branch₁_decompositionComap` as its hypothesis — the route
that avoids presenting the intersection as a join. -/
theorem isPullback_branchComapToBranch₁ :
    IsPullback (decompositionComap L₁ L₂ s R W).D₁.subschemeι
      (branchComapToBranch₁ L₁ L₂ s R W) (W.comap R.normalize.p).subschemeι
      R.normalize.D₁.subschemeι :=
  Scheme.IdealSheafData.isPullback_subschemeMap_of_comap (W.comap R.normalize.p).subschemeι
    (comap_branch₁_decompositionComap L₁ L₂ s R W).symm

include h₁ h₂ in
/-- The morphism `Stacks.Chow.TensorZeroScheme.branchComapToBranch₁` lies over `p^{-1}(W) ↪ L`:
composing it with `D₁ ↪ L` is the inclusion of `D₁ ∩ p^{-1}(W)` into `L` through `p^{-1}(W)`. -/
@[reassoc]
theorem branchComapToBranch₁_subschemeι :
    branchComapToBranch₁ L₁ L₂ s R W ≫ R.normalize.D₁.subschemeι =
      (decompositionComap L₁ L₂ s R W).D₁.subschemeι ≫
        (W.comap R.normalize.p).subschemeι :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

include h₁ h₂ in
/-- The morphism `Stacks.Chow.TensorZeroScheme.branchComapToBranch₁` is a closed immersion, being
the base change of the closed immersion `p^{-1}(W) ↪ L` along `D₁ ↪ L` in the cartesian square
`Stacks.Chow.TensorZeroScheme.isPullback_branchComapToBranch₁`.

The base change is taken rather than the factorization through `D₁ ↪ L`, because in that composite
the intermediate scheme is spelled as the total space of the base-changed diagram on one side and
as `p^{-1}(W)` on the other; those agree only at default transparency, and instance search matches
syntactically, so it cannot find `IsClosedImmersion` for the second factor there. Here the
instance is requested at the plain spelling, where it is a Mathlib instance. -/
theorem isClosedImmersion_branchComapToBranch₁ :
    IsClosedImmersion (branchComapToBranch₁ L₁ L₂ s R W) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_branchComapToBranch₁ L₁ L₂ s R W)
    (inferInstanceAs (IsClosedImmersion (W.comap R.normalize.p).subschemeι))

/-! ### The total space of the branch bundle over `W`, as a closed subscheme of `D₁` -/

include h₁ h₂ in
/-- **The total space of the branch bundle over `W`, as a closed subscheme of `D₁`.** Condition
(4) of [Stacks, Tag 0F97] for the base-changed diagram identifies `D₁ ∩ p^{-1}(W)` with the total
space of a line bundle over the restricted divisor; composing its inverse with
`Stacks.Chow.TensorZeroScheme.branchComapToBranch₁` presents that total space as a closed
subscheme of `D₁`.

This is the datum `j` of
`isRationallyEquivalentToZeroWithin_properPushforward_zeroSection_branchSituation_subschemeι`
at `A = D₁`. -/
def branchTotalSpaceToBranch₁ :
    (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpace ⟶
      R.normalize.D₁.subscheme :=
  (decompositionComap L₁ L₂ s R W).branch₁.inv ≫ branchComapToBranch₁ L₁ L₂ s R W

include h₁ h₂ in
/-- The morphism `Stacks.Chow.TensorZeroScheme.branchTotalSpaceToBranch₁` is a closed immersion:
it is an isomorphism followed by
`Stacks.Chow.TensorZeroScheme.branchComapToBranch₁`. -/
theorem isClosedImmersion_branchTotalSpaceToBranch₁ :
    IsClosedImmersion (branchTotalSpaceToBranch₁ L₁ L₂ s R W) :=
  have := isClosedImmersion_branchComapToBranch₁ L₁ L₂ s R W
  IsClosedImmersion.comp _ _

/-! ### The factorization over `W ↪ Y` -/

include h₁ h₂ in
/-- **`D₁ ∩ p^{-1}(W) ⟶ D₁ ⟶ Y` factors through `W ↪ Y`**, through the restriction of `p`.

This is `Stacks.Chow.TensorZeroScheme.branchComapToBranch₁_subschemeι` followed by the
commutativity of the cartesian square
`Stacks.Chow.TensorZeroScheme.isPullback_comap_proj`. It is stated in term mode on purpose: the
total space of the base-changed diagram and `p^{-1}(W)` are the same scheme only at default
transparency, so a `rw` whose motive composes a morphism out of the one with a morphism out of the
other is rejected with an ill-typed motive, while an `exact` crosses the barrier for free — the
discipline recorded in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionTransport`. -/
theorem branchComapToBranch₁_subschemeι_comp_proj :
    branchComapToBranch₁ L₁ L₂ s R W ≫ R.normalize.D₁.subschemeι ≫ R.normalize.p =
      (decompositionComap L₁ L₂ s R W).D₁.subschemeι ≫
        (decompositionComap L₁ L₂ s R W).p ≫ W.subschemeι :=
  (branchComapToBranch₁_subschemeι_assoc L₁ L₂ s R W R.normalize.p).trans
    (congrArg (fun t => (decompositionComap L₁ L₂ s R W).D₁.subschemeι ≫ t)
      (isPullback_comap_proj L₁ L₂ s R W).w)

include h₁ h₂ in
/-- **The total space of the branch bundle over `W` lies over `W`.** Composing
`Stacks.Chow.TensorZeroScheme.branchTotalSpaceToBranch₁` with `D₁ ↪ L ⟶ Y` factors through
`W ↪ Y`, the intermediate morphism being the projection of the bundle to its base followed by the
inclusion of the restricted divisor into `W`.

This is the pair `(q, hq)` of
`isRationallyEquivalentToZeroWithin_properPushforward_zeroSection_branchSituation_subschemeι`,
and it is what makes the carrier of that statement the preimage of `W` — the carrier the dévissage
of [Stacks, Tag 0F98] prescribes.

It is condition (2) of [Stacks, Tag 0F97] for the base-changed diagram, recorded as the field
`comm₁` of `Stacks.Chow.TensorZeroScheme.Decomposition`, composed with
`Stacks.Chow.TensorZeroScheme.branchComapToBranch₁_subschemeι_comp_proj`.

The intermediate morphism is written in the vocabulary of the base-changed diagram rather than as
the bundle's own projection `totalSpaceToBase`, which it equals by condition (4) — the field
`branch₁_toBase`. That is not a stylistic choice: the base of the bundle is `(branchSituation …).X`
on one spelling and the restricted divisor on the other, and those agree only at default
transparency, so a goal mentioning both is ill-typed at the transparency `rw` builds its motive
at. -/
theorem branchTotalSpaceToBranch₁_comp_subschemeι_comp_proj :
    branchTotalSpaceToBranch₁ L₁ L₂ s R W ≫
        R.normalize.D₁.subschemeι ≫ R.normalize.p =
      ((decompositionComap L₁ L₂ s R W).branch₁.inv ≫
          (decompositionComap L₁ L₂ s R W).p₁ ≫
            (zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι) ≫
        W.subschemeι := by
  rw [branchTotalSpaceToBranch₁, Category.assoc, branchComapToBranch₁_subschemeι_comp_proj,
    reassoc_of% (decompositionComap L₁ L₂ s R W).comm₁]
  simp only [Category.assoc]

end Stacks.Chow.TensorZeroScheme

end
