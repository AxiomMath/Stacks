module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceContainmentGeneralBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityAffineLocalBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The assassin containment locus as a neighbourhood

Stacks 0CVV — in this development the theorem
`isLocallyConstructible_relativeAssassinContainmentLocus_of_isQuasiCompact` of the
`AlgebraicGeometry.Space` namespace — makes the locus
`{v ∈ V | Ass_{X/V}(ℱ) ∩ f^{-1}(\{v\}) ⊆ |U|}`
locally constructible, and Morphisms 05LW,
`AlgebraicGeometry.mem_nhds_of_isLocallyConstructible_of_specializes_subset`, turns a locally
constructible set containing every generalization of a point into a neighbourhood of that
point. Composing the two gives the "after shrinking the base" step of a dévissage: on some open
neighbourhood of `v` the assassin is captured by `U`.

This file performs that composition
(`AlgebraicGeometry.Space.mem_nhds_relativeAssassinContainmentLocus_of_specializes_subset`),
and records what the composition is worth.

## The composition does not weaken anything

`AlgebraicGeometry.specializes_subset_of_mem_nhds` is the observation that for *any* set `E` and
any point `x` of a topological space,

`E ∈ 𝓝 x → {x' | x' ⤳ x} ⊆ E`,

because a specialization of `x` lies in every open set containing `x`. Together with 05LW this
makes the two conditions **equivalent** for a locally constructible `E`:
`AlgebraicGeometry.mem_nhds_iff_specializes_subset_of_isLocallyConstructible`.

So the generalization hypothesis of the composition above is not a weaker hypothesis than its
conclusion — it is the same statement. A dévissage cannot buy its "after shrinking `B`" step by
carrying that hypothesis: carrying it is carrying the conclusion. The composition is 05LW
applied to a particular set and is useful only when the generalization hypothesis is
*discharged* from something else, which for the dévissage of Stacks 0CWC means from part (2) of
Stacks 0CW3 over the base change to `Spec 𝒪_{V, v}`. The statement
`AlgebraicGeometry.Space.mem_nhds_relativeAssassinContainmentLocus_of_specializes_subset` is
therefore stated with the hypothesis under its own name and no claim that it is primitive; the
module docstring of
`StacksFrontier/AlgebraicGeometry/Spaces/Flat/PurityAffineLocalBase.lean` describes the
construction that makes 0CW3 part (2) applicable over such a base, and the implementation notes
below say exactly which step is still missing between the two.

## Moving the hypothesis to the local base does not help either

The natural repair is to ask for the containment not on `V` but on the base change to
`Spec 𝒪_{V, v}` — the image in `|X|` of `Ass_{X_𝒪 / Spec 𝒪_{V, v}}(ℱ_𝒪)` inside `|U|` — since
that is a statement about a different algebraic space and is what part (2) of Stacks 0CW3
produces over a base which is affine local at its closed point, a base which
`AlgebraicGeometry.Space.PrePureSituation.isAffineLocalAt_specStalkPointedOver` now builds.

That does not help: the two are **equivalent**, which is
`mem_nhds_relativeAssassinContainmentLocus_iff_specStalkBaseChange_image_subset` in the
`AlgebraicGeometry.Space` namespace below. The reason is that the base change along
`Spec 𝒪_{V, v} ⟶ V` sees exactly the points specializing to `v`
(`AlgebraicGeometry.Scheme.range_fromSpecStalk`, read on points as
`AlgebraicGeometry.BigFppfOver.exists_pointsMap_specStalkTo_eq` and
`AlgebraicGeometry.BigFppfOver.specializes_pointsToScheme_pointsMap_specStalkTo`), while the
relative weak assassin crosses that base change in both directions — part (2) of Stacks 0CV2,
`AlgebraicGeometry.Space.exists_isRelativeWeaklyAssociatedPoint_baseChange_of_pointsMap_eq`,
lifts a point of `Ass_{X/V}(ℱ)` above such a point, and part (1),
`AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_of_baseChange`, pushes one back down.
So the two containments determine each other.

## What the shrinking step must actually come from

The conclusion of these composites is therefore not reachable from any containment of
`Ass_{X/V}(ℱ)`, at either level: every such containment hypothesis is a restatement of it. It
has to come instead from the *hypotheses* of part (2) of Stacks 0CW3 —

* purity of `ℱ_𝒪` above the closed point of `Spec 𝒪_{V, v}`,
* affine locality of that base at that point, which is now constructed, and
* containment of the fibre over that closed point in `|U|` —

none of which is a containment of `Ass_{X/V}(ℱ)` and none of which this conclusion implies.
Of the three, the first is the ascent of purity along `Spec 𝒪_{V, v} ⟶ V` that the source uses
silently and that this development carries; see
`StacksFrontier/AlgebraicGeometry/Spaces/Flat/PurityHenselianReductionAffineLocal.lean`.

## References

* [Stacks Project, Tag 0CVV](https://stacks.math.columbia.edu/tag/0CVV)
* [Stacks Project, Tag 05LW](https://stacks.math.columbia.edu/tag/05LW)
* [Stacks Project, Tag 0CW3](https://stacks.math.columbia.edu/tag/0CW3)
* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
* [Stacks Project, Tag 0CW2](https://stacks.math.columbia.edu/tag/0CW2)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry

/-- **A neighbourhood of a point contains every generalization of that point.** A set which is a
neighbourhood of `x` contains an open set containing `x`, and a point specializing to `x` lies
in every open set containing `x`.

No constructibility is needed, and this is the direction of
`AlgebraicGeometry.mem_nhds_iff_specializes_subset_of_isLocallyConstructible` which is free. It
is recorded because it is what makes the generalization hypothesis of Morphisms 05LW no weaker
than 05LW's conclusion. -/
@[sga "1 IV 6.3" "necessity"]
theorem specializes_subset_of_mem_nhds {X : Scheme.{u}} {E : Set X} {x : X} (hE : E ∈ 𝓝 x) :
    {x' : X | x' ⤳ x} ⊆ E := by
  obtain ⟨W, hWE, hWopen, hxW⟩ := mem_nhds_iff.1 hE
  exact fun _ hx' ↦ hWE (hx'.mem_open hWopen hxW)

/-- **Morphisms 05LW as an equivalence.** For a locally constructible subset `E` of a scheme,
being a neighbourhood of `x` and containing every generalization of `x` are the same condition.

The substantive direction is 05LW itself,
`AlgebraicGeometry.mem_nhds_of_isLocallyConstructible_of_specializes_subset`; the other is
`AlgebraicGeometry.specializes_subset_of_mem_nhds` and holds for every set.

The point of stating the equivalence is that it settles what a carried generalization
hypothesis is worth: for a locally constructible `E` it is worth exactly the conclusion, so a
proof that assumes it has assumed what it set out to prove. -/
@[sga "1 IV 6.3" "special case", sga "3 XV 3.3" "partial"]
theorem mem_nhds_iff_specializes_subset_of_isLocallyConstructible
    {X : Scheme.{u}} {E : Set X} {x : X} (hE : IsLocallyConstructible E) :
    E ∈ 𝓝 x ↔ {x' : X | x' ⤳ x} ⊆ E :=
  ⟨specializes_subset_of_mem_nhds,
    mem_nhds_of_isLocallyConstructible_of_specializes_subset hE⟩

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CVV composed with Morphisms 05LW: the assassin containment locus is a
neighbourhood of any point all of whose generalizations it contains.** In the situation of
Stacks 0CVV — `X` of finite presentation over a scheme `V` of the site, `ℱ` quasi-coherent of
finite presentation, `U ⊆ X` an open subspace quasi-compact over `V` — the locus of points of
`V` over which `Ass_{X/V}(ℱ)` is captured by `U` contains an open neighbourhood of `v` as soon
as it contains every generalization of `v`.

The locus is locally constructible by Stacks 0CVV, and a locally constructible set containing
every generalization of a point is a neighbourhood of it by Morphisms 05LW.

The hypothesis `hspec` is **not weaker than the conclusion**: by
`AlgebraicGeometry.mem_nhds_iff_specializes_subset_of_isLocallyConstructible` the two are
equivalent here, 0CVV supplying the local constructibility. This declaration is therefore 05LW
specialized to the containment locus, not a reduction of it; see the module docstring. -/
theorem mem_nhds_relativeAssassinContainmentLocus_of_specializes_subset
    {X : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS)
    (f : X ⟶ schemeSpace V) (hf : IsFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite F)
    (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompact B S hS (U.ι ≫ f.hom))
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hspec : {v' : (BigFppfOver.toScheme B S hS).obj V | v' ⤳ v} ⊆
      relativeAssassinContainmentLocus B S hS V f F
        (Set.range (pointsMap B S hS U.toFunctor U.ι))) :
    relativeAssassinContainmentLocus B S hS V f F
        (Set.range (pointsMap B S hS U.toFunctor U.ι)) ∈ 𝓝 v :=
  mem_nhds_of_isLocallyConstructible_of_specializes_subset
    (isLocallyConstructible_relativeAssassinContainmentLocus_of_isQuasiCompact
      B S hS V f hf F hF hFfp U hU hUqc) hspec

/-- **The containment locus of Stacks 0CVV is a neighbourhood of `v` exactly when it contains
every generalization of `v`.** This is
`AlgebraicGeometry.mem_nhds_iff_specializes_subset_of_isLocallyConstructible` with the local
constructibility supplied by Stacks 0CVV, and it is the precise sense in which the two halves
of the dévissage's shrinking step are the same statement. -/
theorem mem_nhds_relativeAssassinContainmentLocus_iff_specializes_subset
    {X : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS)
    (f : X ⟶ schemeSpace V) (hf : IsFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite F)
    (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompact B S hS (U.ι ≫ f.hom))
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    relativeAssassinContainmentLocus B S hS V f F
        (Set.range (pointsMap B S hS U.toFunctor U.ι)) ∈ 𝓝 v ↔
      {v' : (BigFppfOver.toScheme B S hS).obj V | v' ⤳ v} ⊆
        relativeAssassinContainmentLocus B S hS V f F
          (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
  mem_nhds_iff_specializes_subset_of_isLocallyConstructible
    (isLocallyConstructible_relativeAssassinContainmentLocus_of_isQuasiCompact
      B S hS V f hf F hF hFfp U hU hUqc)

/-- **The shrinking step of a dévissage, in the form a consumer wants it**: an open subset of
the base containing `v` over every point of which `Ass_{X/V}(ℱ)` is captured by `U`.

This is `mem_nhds_relativeAssassinContainmentLocus_of_specializes_subset` in this namespace with
the neighbourhood unfolded to an open set and the containment locus unfolded to its defining
condition. The same remark applies: `hspec` is equivalent to the conclusion. -/
theorem exists_isOpen_forall_relativeWeaklyAssociatedPoints_mem_of_specializes_subset
    {X : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS)
    (f : X ⟶ schemeSpace V) (hf : IsFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite F)
    (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompact B S hS (U.ι ≫ f.hom))
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hspec : {v' : (BigFppfOver.toScheme B S hS).obj V | v' ⤳ v} ⊆
      relativeAssassinContainmentLocus B S hS V f F
        (Set.range (pointsMap B S hS U.toFunctor U.ι))) :
    ∃ W : Set ((BigFppfOver.toScheme B S hS).obj V), IsOpen W ∧ v ∈ W ∧
      ∀ w ∈ W, ∀ x ∈ relativeWeaklyAssociatedPoints B S hS f F,
        schemeSpacePointToScheme B S hS V (pointsMap B S hS X.1 f.hom x) = w →
          x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  obtain ⟨W, hWsub, hWopen, hvW⟩ := mem_nhds_iff.1
    (mem_nhds_relativeAssassinContainmentLocus_of_specializes_subset B S hS V f hf F hF hFfp
      U hU hUqc v hspec)
  exact ⟨W, hWopen, hvW, fun w hw x hx hxw ↦ hWsub hw x hx hxw⟩

/-! ### The shrinking step with a hypothesis on the base change -/

/-- **A chart containment on a base change pushes forward to a containment of images.** If
`X'_Z = X_Z ×_X U` is presented as a cartesian square over the projection `X_Z ⟶ X` and the
chart `U ⟶ X`, then a subset of `|X_Z|` lying in the image of `|X'_Z| → |X_Z|` has its image in
`|X|` inside the image of `|U| → |X|`.

This is the step which turns the conclusion of part (2) of Stacks 0CW3 over a base change —
a containment in the image of the base-changed chart — into the hypothesis of
`mem_nhds_relativeAssassinContainmentLocus_of_specStalkBaseChange_image_subset` in this
namespace, which is a containment of images in `|X|`. -/
theorem image_pointsMap_subset_range_of_subset_range_of_isPullback
    {X XZ X'Z U' : AlgebraicSpaces B S hS} {pZ : XZ ⟶ X} {u : U' ⟶ X}
    {gZ : X'Z ⟶ XZ} {rZ : X'Z ⟶ U'}
    (sq' : IsPullback gZ.hom rZ.hom pZ.hom u.hom) (E : Set (points B S hS XZ.1))
    (hE : E ⊆ Set.range (pointsMap B S hS X'Z.1 gZ.hom)) :
    pointsMap B S hS XZ.1 pZ.hom '' E ⊆ Set.range (pointsMap B S hS U'.1 u.hom) := by
  rintro _ ⟨ξ, hξ, rfl⟩
  obtain ⟨w, rfl⟩ := hE hξ
  exact ⟨pointsMap B S hS X'Z.1 rZ.hom w, (pointsMap_apply_comm B S hS sq'.w w).symm⟩

/-- **The shrinking step of the dévissage, with the containment assumed over
`Spec 𝒪_{V, v}`.** In the situation of Stacks 0CVV, suppose that on the base change of `X` along
`Spec 𝒪_{V, v} ⟶ V` the relative weak assassin has its image in `|X|` inside `|U|`. Then the
locus of points of `V` over which `Ass_{X/V}(ℱ)` is captured by `|U|` contains an open
neighbourhood of `v`.

This is the composition of Stacks 0CVV with Morphisms 05LW whose hypothesis is stated on the
base change rather than on `V`. The generalization hypothesis of
`mem_nhds_relativeAssassinContainmentLocus_of_specializes_subset` in this namespace is derived,
not assumed:

* a point of `V` specializing to `v` is exactly a point in the image of
  `Spec 𝒪_{V, v} ⟶ V`, by `AlgebraicGeometry.Scheme.range_fromSpecStalk`;
* a point of `Ass_{X/V}(ℱ)` above such a point lifts to a point of
  `Ass_{X_𝒪 / Spec 𝒪_{V, v}}(ℱ_𝒪)` by part (2) of Stacks 0CV2,
  `AlgebraicGeometry.Space.exists_isRelativeWeaklyAssociatedPoint_baseChange_of_pointsMap_eq`;
* and `hcapture` returns its image to `|U|`.

`hcapture` is the conclusion of part (2) of Stacks 0CW3 over the base change, pushed into `|X|`
by `image_pointsMap_subset_range_of_subset_range_of_isPullback` above; part (2) of Stacks 0CW3
is applicable there because
`AlgebraicGeometry.Space.PrePureSituation.isAffineLocalAt_specStalkPointedOver` makes that base
change affine local at its closed point.

`hcapture` is nevertheless **equivalent** to the conclusion, by
`mem_nhds_relativeAssassinContainmentLocus_iff_specStalkBaseChange_image_subset` in this
namespace: moving the containment to the local base does not make it more primitive. So this
declaration is a reformulation, useful because its hypothesis is the shape part (2) of
Stacks 0CW3 delivers, and not a reduction. The module docstring says what the shrinking step
must come from instead. -/
theorem mem_nhds_relativeAssassinContainmentLocus_of_specStalkBaseChange_image_subset
    {X : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS)
    (f : X ⟶ schemeSpace V) (hf : IsFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite F)
    (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompact B S hS (U.ι ≫ f.hom))
    (v : (BigFppfOver.toScheme B S hS).obj V)
    {XZ : AlgebraicSpaces B S hS} {pZ : XZ ⟶ X}
    {qZ : XZ ⟶ schemeSpace (BigFppfOver.specStalk B S hS V v)}
    (sq : IsPullback pZ.hom qZ.hom f.hom
      (schemeSpaceMap (BigFppfOver.specStalkTo B S hS V v)).hom)
    (hcapture : pointsMap B S hS XZ.1 pZ.hom ''
        relativeWeaklyAssociatedPoints B S hS qZ ((modulePullback B S hS pZ).obj F) ⊆
      Set.range (pointsMap B S hS U.toFunctor U.ι)) :
    relativeAssassinContainmentLocus B S hS V f F
        (Set.range (pointsMap B S hS U.toFunctor U.ι)) ∈ 𝓝 v := by
  refine mem_nhds_relativeAssassinContainmentLocus_of_specializes_subset B S hS V f hf F hF
    hFfp U hU hUqc v fun v' hv' ↦ ?_
  intro x hx hxv'
  -- A point specializing to `v` lies in the image of `Spec 𝒪_{V, v} ⟶ V`.
  obtain ⟨t, ht⟩ := BigFppfOver.exists_pointsMap_specStalkTo_eq B S hS V v hv'
  -- The chosen point of `Spec 𝒪_{V, v}` lies over the image of `x`.
  have hty : pointsMap B S hS (schemeSpace (BigFppfOver.specStalk B S hS V v)).1
        (schemeSpaceMap (BigFppfOver.specStalkTo B S hS V v)).hom t =
      pointsMap B S hS X.1 f.hom x :=
    injective_pointsToScheme B S hS V (ht.trans hxv'.symm)
  -- Part (2) of Stacks 0CV2 lifts `x` to the relative weak assassin of the base change.
  obtain ⟨ξ, hξ, hξp, -⟩ :=
    exists_isRelativeWeaklyAssociatedPoint_baseChange_of_pointsMap_eq B S hS sq F hF hx hty
  exact hξp ▸ hcapture ⟨ξ, hξ, rfl⟩

/-- **The containment on the base change is implied by the conclusion too.** If the containment
locus is a neighbourhood of `v`, then the image in `|X|` of
`Ass_{X_𝒪 / Spec 𝒪_{V, v}}(ℱ_𝒪)` lies in `|U|`.

Part (1) of Stacks 0CV2,
`AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_of_baseChange`, puts the image of a
point of the relative weak assassin of the base change into `Ass_{X/V}(ℱ)`; its image in `V`
specializes to `v` by
`AlgebraicGeometry.BigFppfOver.specializes_pointsToScheme_pointsMap_specStalkTo`; and a
neighbourhood of `v` contains every point specializing to `v`.

Together with `mem_nhds_relativeAssassinContainmentLocus_of_specStalkBaseChange_image_subset`
this makes the base-change containment **equivalent** to the conclusion — see
`mem_nhds_relativeAssassinContainmentLocus_iff_specStalkBaseChange_image_subset` below. -/
theorem specStalkBaseChange_image_subset_of_mem_nhds
    {X : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS)
    (f : X ⟶ schemeSpace V) (F : Modules.{u, u} B S hS X.1 X.2)
    (U : Subfunctor X.1) (v : (BigFppfOver.toScheme B S hS).obj V)
    {XZ : AlgebraicSpaces B S hS} {pZ : XZ ⟶ X}
    {qZ : XZ ⟶ schemeSpace (BigFppfOver.specStalk B S hS V v)}
    (sq : IsPullback pZ.hom qZ.hom f.hom
      (schemeSpaceMap (BigFppfOver.specStalkTo B S hS V v)).hom)
    (hnhds : relativeAssassinContainmentLocus B S hS V f F
      (Set.range (pointsMap B S hS U.toFunctor U.ι)) ∈ 𝓝 v) :
    pointsMap B S hS XZ.1 pZ.hom ''
        relativeWeaklyAssociatedPoints B S hS qZ ((modulePullback B S hS pZ).obj F) ⊆
      Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  rintro _ ⟨ξ, hξ, rfl⟩
  -- The image in `V` of the point of the base change factors through `Spec 𝒪_{V, v}`.
  have himg := pointsMap_apply_comm B S hS sq.w ξ
  -- Hence it specializes to `v`, so the neighbourhood contains it.
  refine specializes_subset_of_mem_nhds hnhds
    (show schemeSpacePointToScheme B S hS V
        (pointsMap B S hS X.1 f.hom (pointsMap B S hS XZ.1 pZ.hom ξ)) ⤳ v from ?_)
    _ (isRelativeWeaklyAssociatedPoint_of_baseChange B S hS sq F hξ) rfl
  rw [himg]
  exact BigFppfOver.specializes_pointsToScheme_pointsMap_specStalkTo B S hS V v _

/-- **The shrinking step is equivalent to the containment on the base change.** For a situation
of Stacks 0CVV, the containment locus is a neighbourhood of `v` **if and only if** the image in
`|X|` of `Ass_{X_𝒪 / Spec 𝒪_{V, v}}(ℱ_𝒪)` lies in `|U|`.

This is the precise obstruction to buying the dévissage's shrinking step by carrying a
containment hypothesis. Phrasing the hypothesis at the local base `Spec 𝒪_{V, v}` instead of at
`V` does **not** make it more primitive: the base change along `Spec 𝒪_{V, v} ⟶ V` sees exactly
the points specializing to `v` (`AlgebraicGeometry.Scheme.range_fromSpecStalk`), and part (1)
of Stacks 0CV2 carries the relative weak assassin across that base change in the direction the
first half needs while part (2) carries it in the other, so the two containments determine each
other.

What this leaves is that the shrinking step cannot come from the containment at all. It has to
come from the *hypotheses* of part (2) of Stacks 0CW3 — purity above the closed point of
`Spec 𝒪_{V, v}`, affine locality of that base (now
`AlgebraicGeometry.Space.PrePureSituation.isAffineLocalAt_specStalkPointedOver`), and the
containment of the fibre over the closed point — none of which is a containment of
`Ass_{X/V}(ℱ)` and none of which is implied by this conclusion. -/
theorem mem_nhds_relativeAssassinContainmentLocus_iff_specStalkBaseChange_image_subset
    {X : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS)
    (f : X ⟶ schemeSpace V) (hf : IsFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite F)
    (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompact B S hS (U.ι ≫ f.hom))
    (v : (BigFppfOver.toScheme B S hS).obj V)
    {XZ : AlgebraicSpaces B S hS} {pZ : XZ ⟶ X}
    {qZ : XZ ⟶ schemeSpace (BigFppfOver.specStalk B S hS V v)}
    (sq : IsPullback pZ.hom qZ.hom f.hom
      (schemeSpaceMap (BigFppfOver.specStalkTo B S hS V v)).hom) :
    relativeAssassinContainmentLocus B S hS V f F
        (Set.range (pointsMap B S hS U.toFunctor U.ι)) ∈ 𝓝 v ↔
      pointsMap B S hS XZ.1 pZ.hom ''
          relativeWeaklyAssociatedPoints B S hS qZ ((modulePullback B S hS pZ).obj F) ⊆
        Set.range (pointsMap B S hS U.toFunctor U.ι) :=
  ⟨specStalkBaseChange_image_subset_of_mem_nhds B S hS V f F U v sq,
    mem_nhds_relativeAssassinContainmentLocus_of_specStalkBaseChange_image_subset
      B S hS V f hf F hF hFfp U hU hUqc v sq⟩

end Space

end AlgebraicGeometry

end
