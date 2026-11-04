module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionBranchAmbient
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowMaps

/-!
# The branch bundle's flat pullback read on the branch `D₁`

In the situation of [Stacks, Tag 0F97] let `W ⊆ Y` be a closed subscheme. Condition (4) of the
tag presents the first closed subscheme of the diagram base changed along `W ↪ Y` as the total
space of a line bundle over the restricted divisor `D'`, and
`Stacks.Chow.TensorZeroScheme.branchTotalSpaceToBranch₁` presents that total space as a closed
subscheme of the branch `D₁` of the unrestricted diagram.

The dévissage of the case `W ⊆ D` of [Stacks, Tag 0F98] computes on `D₁`, and it needs the two
ways of getting a cycle from `D'` to `D₁` to agree:

* pull back along the bundle's own projection `π : W₁ ⟶ D'` and push the result forward along the
  immersion `j : W₁ ⟶ D₁`;
* push forward along `δ : D' ⟶ D` and pull back along `p₁ : D₁ ⟶ D`.

This file proves they agree, **as an identity of cycles**.

## Main results

All in the namespace `Stacks.Chow.TensorZeroScheme`.

* `branchTotalSpaceToBranch₁_comp_base` — the immersion `j` lies over the structure morphism of
  the bundle's base, which is what makes the two pushforwards below well-typed.
* `properPushforward_branchTotalSpaceToBranch₁_flatPullback_totalSpaceToBase`
  — **the comparison**: `j_*π^*β = p₁^*δ_*β` for every cycle `β` on `D'`.

## Implementation notes

### Why this is a base change and not a new computation

The square

  `W₁ --j--> D₁`
  `|π         |p₁`
  `D' --δ--> D`

is cartesian: it is `Stacks.Chow.TensorZeroScheme.isPullback_bcProj`, the statement that the
inverse image of `D₁` in `p^{-1}(W)` is `D₁ ×_D D'`, with its apex moved along the isomorphism of
condition (4). So the comparison is [Stacks, Tag 02RG] — flat pullback commutes with proper
pushforward across a fibre product square — at that square, in the fully discharged form
`Stacks.Chow.flatPullback_properPushforward_of_isProper`, together with the isomorphism case
`Stacks.Chow.flatPullback_properPushforward_of_isIso` to move the apex.

`δ` is proper because it is a closed immersion, being the base change of `W ↪ Y` along `D ↪ Y`
(`Stacks.Chow.TensorZeroScheme.isPullback_zeroIdealBaseChangeMap`), and `p₁` is flat of relative
dimension one by condition (2) of Tag 0F97.

### The transparency barrier at the bundle's base

`(branchSituation …).X` and the restricted divisor are the same scheme, but only at default
transparency: `Stacks.Chow.TensorZeroScheme.branchSituation_X` is `rfl`, while `rw` builds its
motive at `instances` transparency and an abstraction over a morphism typed at one spelling, used
at the other, is rejected as an ill-typed motive. So every step that mentions both spellings is
either a `congrArg` at an explicitly typed function — where the body is elaborated at default
transparency and the barrier costs nothing — or an `Eq.trans`, whose middle term is unified at
default transparency as well. No step of either proof below is a `rw` across the barrier. This is
the discipline recorded in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionTransport` and already followed
by `Stacks.Chow.TensorZeroScheme.branchComapToBranch₁_subschemeι_comp_proj`.

For the same reason the structure morphism of the bundle's base is a *parameter* `sD` with the
factorization through `δ` as a hypothesis, exactly as in
`isRationallyEquivalentToZeroWithin_properPushforward_zeroSection_branchSituation_subschemeι`,
whose `sD` this is: the two statements are made to compose.

### No `@[stacks]` attribute here

This is [Stacks, Tag 02RG] at a particular square, not a new assertion of it; the tag is carried
by `Stacks.Chow.flatPullback_properPushforward_of_isProper`. Nor does anything here assert
[Stacks, Tag 0F98], which is a single identity of maps — see the convention note in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowMaps`.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

namespace Stacks.Chow.TensorZeroScheme

attribute [local instance] Stacks.LineBundle.Situation.flat_totalSpaceToBase

variable {Y : Scheme.{u}} (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (W : Y.IdealSheafData)

/-! ### The bundle's projection and the restriction of `p₁` -/

include h₁ h₂ in
/-- **The projection of the branch bundle over `W` is the restriction of `p₁`**, read through the
isomorphism of [Stacks, Tag 0F97](4): precomposing `p₁'` with the inverse of that isomorphism is
the bundle's own projection `totalSpaceToBase`.

This is the structure field `branch₁_toBase` of
`Stacks.Chow.TensorZeroScheme.Decomposition` cancelled against the isomorphism. The conclusion is
ascribed at `(branchSituation …).X` rather than at the restricted divisor: those agree only at
default transparency, and an equation stated at the second spelling cannot be used to rewrite an
occurrence typed at the first. -/
theorem branch₁_inv_comp_p₁_decompositionComap :
    ((decompositionComap L₁ L₂ s R W).branch₁.inv ≫ (decompositionComap L₁ L₂ s R W).p₁ :
        (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpace ⟶
          (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X) =
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase :=
  (congrArg
      (fun t ↦ (decompositionComap L₁ L₂ s R W).branch₁.inv ≫ t)
      (decompositionComap L₁ L₂ s R W).branch₁_toBase.symm).trans
    ((decompositionComap L₁ L₂ s R W).branch₁.inv_hom_id_assoc _)

/-- Precomposing `p₁'` followed by any morphism `t` with the inverse of the isomorphism of
[Stacks, Tag 0F97](4) is the bundle's projection followed by `t`. -/
private theorem inv_comp_p₁_comp_decompositionComap {T : Scheme.{u}}
    (t : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X ⟶ T) :
    (decompositionComap L₁ L₂ s R W).branch₁.inv ≫ (decompositionComap L₁ L₂ s R W).p₁ ≫ t =
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ t :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ t) (branch₁_inv_comp_p₁_decompositionComap L₁ L₂ s R W))

/-! ### The two closed immersions are proper -/

include h₁ h₂ in
/-- **`δ : D' ⟶ D` is a closed immersion**, being the base change of `W ↪ Y` along `D ↪ Y` in the
cartesian square `Stacks.Chow.TensorZeroScheme.isPullback_zeroIdealBaseChangeMap`. Registered as a
local instance below, so that the pushforward of cycles along `δ` is available. -/
theorem isClosedImmersion_zeroIdealBaseChangeMap_subschemeι :
    IsClosedImmersion (zeroIdealBaseChangeMap s W.subschemeι) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_zeroIdealBaseChangeMap s W.subschemeι)
    (inferInstanceAs (IsClosedImmersion W.subschemeι))

include h₁ h₂ in
/-- **`δ : D' ⟶ D` is proper**, being a closed immersion — with its source spelled as the base
`(branchSituation …).X` of the branch bundle.

The implicit arguments are pinned because the two spellings of that scheme agree only at default
transparency and instance search matches syntactically. A statement whose pushforward along `δ`
takes the structure morphism of the bundle's base as its source datum fixes the source at this
spelling, and the instance stated at the other one is then invisible; here the defeq is discharged
once, by the elaborator's check of this declaration's ascribed type against the type of
`inferInstanceAs`'s result. -/
theorem isProper_zeroIdealBaseChangeMap_subschemeι :
    @IsProper
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X
      (zeroIdeal Y L₁ L₂ s).subscheme (zeroIdealBaseChangeMap s W.subschemeι) :=
  have := isClosedImmersion_zeroIdealBaseChangeMap_subschemeι L₁ L₂ s W
  inferInstanceAs (IsProper (zeroIdealBaseChangeMap s W.subschemeι))

attribute [local instance] isClosedImmersion_zeroIdealBaseChangeMap_subschemeι
  isProper_zeroIdealBaseChangeMap_subschemeι
  isClosedImmersion_branchComapToBranch₁ isClosedImmersion_branchTotalSpaceToBranch₁

/-! ### The restricted divisor, read inside `D` -/

include h₁ h₂ in
/-- **`δ : D' ⟶ D` cuts out the restriction of `W` to `D`.** The kernel ideal of the canonical
morphism of zero schemes is the inverse image of `W` along `D ↪ Y`.

`δ` is the base change of `W ↪ Y` along `D ↪ Y`
(`Stacks.Chow.TensorZeroScheme.isPullback_zeroIdealBaseChangeMap`), and the kernel of a base change
of a closed immersion is the inverse image of its kernel. -/
theorem ker_zeroIdealBaseChangeMap_subschemeι :
    (zeroIdealBaseChangeMap s W.subschemeι).ker =
      W.comap (zeroIdeal Y L₁ L₂ s).subschemeι := by
  rw [AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
    (isPullback_zeroIdealBaseChangeMap s W.subschemeι).flip,
    Scheme.IdealSheafData.ker_subschemeι]

include h₁ h₂ in
/-- **The restricted divisor is the restriction of `W` to `D`, as an isomorphism of closed
subschemes of `D`.** The zero scheme `D'` of the restricted section inside `W` and the inverse
image `W|_D` of `W` inside `D` are two closed subschemes of `D` with the same kernel ideal, by
`Stacks.Chow.TensorZeroScheme.ker_zeroIdealBaseChangeMap_subschemeι`, so the comparison morphism
between them is an isomorphism.

This is what lets a Chern component cycle computed on `D` at the component `W|_D` be compared with
one computed on the base of the branch bundle: the two ambient schemes are identified here, and the
change of ambient is then
`Stacks.Chow.firstChernComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin` at
`δ`, whose scheme-theoretic image hypothesis is the kernel identity above read through
`AlgebraicGeometry.Scheme.IdealSheafData.map_bot`.

No equation between concrete ideal sheaves is eliminated into a type: the identity is consumed in
`Prop`, as the hypothesis of `AlgebraicGeometry.IsClosedImmersion.isIso_lift`, exactly as in
`AlgebraicGeometry.Scheme.IdealSheafData.supComapSubschemeIso`. -/
def zeroIdealBaseChangeIsoComap :
    (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subscheme ≅
      (zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)).subscheme :=
  haveI := isClosedImmersion_zeroIdealBaseChangeMap_subschemeι L₁ L₂ s W
  haveI := IsClosedImmersion.isIso_lift (zeroIdealBaseChangeMap s W.subschemeι)
    (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι
    ((ker_zeroIdealBaseChangeMap_subschemeι L₁ L₂ s W).trans
      (Scheme.IdealSheafData.ker_subschemeι _).symm)
  asIso (IsClosedImmersion.lift (zeroIdealBaseChangeMap s W.subschemeι)
    (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι
    ((ker_zeroIdealBaseChangeMap_subschemeι L₁ L₂ s W).trans
      (Scheme.IdealSheafData.ker_subschemeι _).symm).le)

include h₁ h₂ in
/-- The isomorphism of
`Stacks.Chow.TensorZeroScheme.zeroIdealBaseChangeIsoComap` is one of closed subschemes of `D`. -/
@[reassoc]
theorem zeroIdealBaseChangeIsoComap_hom_comp :
    (zeroIdealBaseChangeIsoComap L₁ L₂ s W).hom ≫ zeroIdealBaseChangeMap s W.subschemeι =
      (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι :=
  have := isClosedImmersion_zeroIdealBaseChangeMap_subschemeι L₁ L₂ s W
  IsClosedImmersion.lift_fac _ _ _

/-! ### The immersion into `D₁` lies over the structure morphism of the bundle's base -/

variable (C : Stacks.Chow.ChowSituation.{u}) (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sD : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
    ((Scheme.Modules.pullback W.subschemeι).obj L₂)
    (pullbackTensorSection W.subschemeι L₁ L₂ s)
    ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X ⟶ C.S) [LocallyOfFiniteType sD]
  (hsD : zeroIdealBaseChangeMap s W.subschemeι ≫
    ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) = sD)

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType sD] in
include h₁ h₂ hsD in
/-- **The immersion of the branch bundle over `W` into `D₁` lies over the structure morphism of
the bundle's base.** Composing
`Stacks.Chow.TensorZeroScheme.branchTotalSpaceToBranch₁` with `D₁ ↪ L ⟶ Y ⟶ S` is the bundle's
projection followed by `sD`.

This is `Stacks.Chow.TensorZeroScheme.branchTotalSpaceToBranch₁_comp_subschemeι_comp_proj`
composed with `sY`, the resulting intermediate morphism being rewritten by
`Stacks.Chow.TensorZeroScheme.branch₁_inv_comp_p₁_decompositionComap` and the hypothesis `hsD`.
It is the datum `hj` of
`isRationallyEquivalentToZeroWithin_properPushforward_zeroSection_branchSituation_subschemeι`
at `A = D₁`. -/
theorem branchTotalSpaceToBranch₁_comp_base :
    branchTotalSpaceToBranch₁ L₁ L₂ s R W ≫
        (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) =
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD := by
  have h := congrArg (· ≫ sY) (branchTotalSpaceToBranch₁_comp_subschemeι_comp_proj L₁ L₂ s R W)
  simp only [Category.assoc] at h ⊢
  refine h.trans ((inv_comp_p₁_comp_decompositionComap L₁ L₂ s R W _).trans ?_)
  rw [← hsD, zeroIdealBaseChangeMap_comp_subschemeι_assoc]

/-! ### The comparison -/

include h₁ h₂ hsD in
/-- **`j_*π^*β = p₁^*δ_*β`.** For every cycle `β` on the base `D'` of the branch bundle over `W`,
the flat pullback of `β` along the bundle's projection, pushed forward along the closed immersion
of the total space into the branch `D₁`, is the flat pullback along `p₁ : D₁ ⟶ D` of the
pushforward of `β` along `δ : D' ⟶ D`.

This is [Stacks, Tag 02RG] at the cartesian square

  `W₁ --j--> D₁`
  `|π         |p₁`
  `D' --δ--> D`

whose lower-left presentation is `Stacks.Chow.TensorZeroScheme.isPullback_bcProj`: the inverse
image of `D₁` in `p^{-1}(W)` is `D₁ ×_D D'`. Two applications: the fully discharged
`Stacks.Chow.flatPullback_properPushforward_of_isProper` at that square, which produces the
pushforward along `Stacks.Chow.TensorZeroScheme.branchComapToBranch₁` of the flat pullback along
`p₁'`, and `Stacks.Chow.flatPullback_properPushforward_of_isIso` at the isomorphism of condition
(4), which turns that flat pullback into the bundle's own. The two pushforwards then compose by
`Stacks.Chow.properPushforward_comp` into the pushforward along `j`, which is by definition their
composite. -/
theorem properPushforward_branchTotalSpaceToBranch₁_flatPullback_totalSpaceToBase (k : ℤ)
    (β : Stacks.Chow.CycleGroup C sD k) :
    Stacks.Chow.properPushforward C
        ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD)
        (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
        (branchTotalSpaceToBranch₁ L₁ L₂ s R W)
        (branchTotalSpaceToBranch₁_comp_base L₁ L₂ s R W C sY sD hsD) (k + ((1 : ℕ) : ℤ))
        (Stacks.Chow.flatPullback C
          ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD) sD
          (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase rfl 1
          (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)).relativeDimension_totalSpaceToBase
          k β) =
      Stacks.Chow.flatPullback C
        (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
        ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
        (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
        ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
        (Stacks.Chow.properPushforward C sD ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
          (zeroIdealBaseChangeMap s W.subschemeι) hsD k β) := by
  have hsq : IsPullback (decompositionComap L₁ L₂ s R W).p₁ (branchComapToBranch₁ L₁ L₂ s R W)
      (zeroIdealBaseChangeMap s W.subschemeι) R.normalize.p₁ :=
    (isPullback_bcProj W.subschemeι (isPullback_comap_proj L₁ L₂ s R W) R.normalize.p₁
      R.normalize.comm₁
      (comap_branch₁_decompositionComap L₁ L₂ s R W).symm).flip
  have hp₁ft : LocallyOfFiniteType (decompositionComap L₁ L₂ s R W).p₁ :=
    MorphismProperty.of_isPullback hsq.flip inferInstance
  have hp₁flat : AlgebraicGeometry.Flat (decompositionComap L₁ L₂ s R W).p₁ :=
    MorphismProperty.of_isPullback hsq.flip inferInstance
  -- Every instance below is stated twice, once at each of the two spellings of the bundle's base:
  -- `(branchSituation …).X` and the zero scheme of the restricted section are the same scheme only
  -- at default transparency, instance search matches syntactically, and the statements here mix
  -- the two — `sD` and `totalSpaceToBase` are typed at the first, `δ` and `p₁'` at the second.
  have hsDft : @LocallyOfFiniteType
      (zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)).subscheme C.S sD :=
    inferInstanceAs (LocallyOfFiniteType sD)
  have : LocallyOfFiniteType ((decompositionComap L₁ L₂ s R W).p₁ ≫ sD) :=
    @AlgebraicGeometry.locallyOfFiniteType_comp _ _ _
      (decompositionComap L₁ L₂ s R W).p₁ sD hp₁ft hsDft
  have : @LocallyOfFiniteType (decompositionComap L₁ L₂ s R W).D₁.subscheme
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X
      (decompositionComap L₁ L₂ s R W).p₁ := hp₁ft
  have : @AlgebraicGeometry.Flat (decompositionComap L₁ L₂ s R W).D₁.subscheme
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X
      (decompositionComap L₁ L₂ s R W).p₁ := hp₁flat
  have h02RG := Stacks.Chow.flatPullback_properPushforward_of_isProper C sD
    ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) ((decompositionComap L₁ L₂ s R W).p₁ ≫ sD)
    (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
    (zeroIdealBaseChangeMap s W.subschemeι) R.normalize.p₁
    (decompositionComap L₁ L₂ s R W).p₁ (branchComapToBranch₁ L₁ L₂ s R W) hsq hsD
    (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) rfl 1
    ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k β
  have hu₁ : (decompositionComap L₁ L₂ s R W).branch₁.inv ≫
        ((decompositionComap L₁ L₂ s R W).p₁ ≫ sD) =
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD :=
    inv_comp_p₁_comp_decompositionComap L₁ L₂ s R W sD
  have hiso := Stacks.Chow.flatPullback_properPushforward_of_isIso C sD
    ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD) sD
    ((decompositionComap L₁ L₂ s R W).p₁ ≫ sD)
    (CategoryTheory.CategoryStruct.id _) (Category.id_comp sD)
    (decompositionComap L₁ L₂ s R W).branch₁.inv hu₁
    (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase rfl
    (decompositionComap L₁ L₂ s R W).p₁ rfl
    ((Category.comp_id _).trans (branch₁_inv_comp_p₁_decompositionComap L₁ L₂ s R W).symm) 1
    (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).relativeDimension_totalSpaceToBase
    (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip
      ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)))
    k β
  rw [Stacks.Chow.properPushforward_id] at hiso
  have hfac : branchComapToBranch₁ L₁ L₂ s R W ≫
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) =
      (decompositionComap L₁ L₂ s R W).p₁ ≫ sD := by
    rw [← (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY), ← Category.assoc,
      ← hsq.w, Category.assoc, hsD]
  refine Eq.trans ?_ h02RG.symm
  refine Eq.trans (congrFun (Stacks.Chow.properPushforward_comp C
    ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD)
    ((decompositionComap L₁ L₂ s R W).p₁ ≫ sD)
    (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
    (decompositionComap L₁ L₂ s R W).branch₁.inv (branchComapToBranch₁ L₁ L₂ s R W) hu₁ hfac
    (k + ((1 : ℕ) : ℤ))) _).symm ?_
  exact congrArg
    (Stacks.Chow.properPushforward C ((decompositionComap L₁ L₂ s R W).p₁ ≫ sD)
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      (branchComapToBranch₁ L₁ L₂ s R W) hfac (k + ((1 : ℕ) : ℤ))) hiso.symm

end Stacks.Chow.TensorZeroScheme

end
