module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting

/-!
# The closure condition of Stacks 07AK (1) for the smooth objects (Stacks 0788, part (1))

Stacks 0788, part (1), asserts that the inclusion of the lisse-étale site of an algebraic stack
`𝒳` into its étale site is fully faithful, continuous and cocontinuous. Full faithfulness is
`CategoryTheory.ObjectProperty.fullyFaithfulι`; continuity and cocontinuity are the étale case of
**Stacks 07AK**, available as `AlgebraicGeometry.Stack.LisseEtale.isContinuous_inclusion` and its
siblings, each carrying the closure condition of 07AK (1) for the smooth objects as the hypothesis
`AlgebraicGeometry.Stack.LisseEtale.ClosedUnderSmoothMorphisms`.

**This file discharges that hypothesis**, so the four assertions become unconditional, and with
them the clauses part (1) derives from them: the morphism of topoi `g` of (1)(a), the lower shriek
and its unit and counit on sheaves of sets of (1)(b) and (1)(c), the lower shriek and its unit on
abelian sheaves of (1)(d) and (1)(e), and the identification `g⁻¹𝒪_𝒳 = 𝒪_{𝒳_{lisse,étale}}` with
the flat morphism of ringed topoi it gives of (1)(f). The last assertion of (1)(f), that `g^*` on
sheaves of modules is `g^{-1}`, is in
`StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleRingedModules.lean`.

The argument is the smooth analogue of `AlgebraicGeometry.Stack.flatObject_of_flat`, mirrored
lemma for lemma. An object `x` of `𝒳` is smooth (**Stacks 0787**) when the 1-morphism it names
under the 2-Yoneda lemma is a smooth 1-morphism of algebraic stacks in the sense of
**Stacks 075U**, which is the existential smooth-diagram criterion of **Stacks 06FM**,
condition (2). For a 1-morphism representable by algebraic spaces that criterion is the relative
property of **Stacks 03YK** at `AlgebraicGeometry.Space.IsSmooth`, by
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_relative`; the relative property is
stable under composition by **Stacks 045B**; and
`AlgebraicGeometry.Stack.objectMorphismFactorIso` identifies `x : U → 𝒳` with the composite
`U → V → 𝒳` up to a 2-isomorphism, along which the relative property transports by
`AlgebraicGeometry.Stack.hasRelativeProperty_congr_twoIso`.

## Main definitions

* `AlgebraicGeometry.Space.isSmooth_yoneda_map`: a morphism of the big fppf site of `S` whose
  underlying morphism of schemes is smooth is a smooth morphism of algebraic spaces over `S`.
* `AlgebraicGeometry.Stack.LisseEtale.setsShriek`: the functor `g_!^{Sh}` of
  **Stacks 0788** (1)(b) on sheaves of sets.
* `AlgebraicGeometry.Stack.LisseEtale.ringedTopos'` and
  `AlgebraicGeometry.Stack.LisseEtale.toposMorphismOnRings`: the lisse-étale ringed topos and the
  morphism of topoi of (1)(a) at the universe of the sections of the structure sheaf, with no
  hypothesis.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.smoothObject_of_smooth`: smoothness of an object of an
  algebraic stack is inherited along a morphism lying over a smooth morphism of schemes.
* `AlgebraicGeometry.Stack.LisseEtale.isContinuous_inclusion'`,
  `AlgebraicGeometry.Stack.LisseEtale.isCocontinuous_inclusion'`,
  `AlgebraicGeometry.Stack.LisseEtale.isContinuous_inclusion_topology'` and
  `AlgebraicGeometry.Stack.LisseEtale.isCocontinuous_inclusion_topology'`: **Stacks 0788**,
  part (1), continuity and cocontinuity of the inclusion of the lisse-étale site, at each of the
  two descriptions of its topology, with no hypothesis.
* `AlgebraicGeometry.Stack.LisseEtale.toposMorphism'` and
  `AlgebraicGeometry.Stack.LisseEtale.toposMorphismTopology'`: **Stacks 0788**, part (1)(a), the
  morphism of topoi `g : Sh(𝒳_{lisse,étale}) → Sh(𝒳_étale)`, with no hypothesis.
* `AlgebraicGeometry.Stack.LisseEtale.setsShriekAdjunction`: **Stacks 0788**, part (1)(b), the
  adjunction `g_!^{Sh} ⊣ g⁻¹` on sheaves of sets.
* `AlgebraicGeometry.Stack.LisseEtale.isIso_setsShriekAdjunction_unit`, with the general instance
  `CategoryTheory.Functor.isIso_sheafAdjunctionCocontinuous_counit`:
  **Stacks 0788**, part (1)(c), the two canonical maps `id ⟶ g⁻¹g_!^{Sh}` and `g⁻¹g_* ⟶ id` on
  sheaves of sets are isomorphisms.
* `AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriekAdjunction'`: **Stacks 0788**, part
  (1)(d), the adjunction `g_! ⊣ g⁻¹` on abelian sheaves, with no hypothesis.
* `AlgebraicGeometry.Stack.LisseEtale.isIso_abelianLowerShriek_unit'`: **Stacks 0788**, part
  (1)(e), the unit of that adjunction is an isomorphism, with no hypothesis.
* `AlgebraicGeometry.Stack.LisseEtale.structureSheafIso`,
  `AlgebraicGeometry.Stack.LisseEtale.structureSheafIso_apply`,
  `AlgebraicGeometry.Stack.LisseEtale.ringedToposMorphism'` and
  `AlgebraicGeometry.Stack.LisseEtale.isFlat_ringedToposMorphism'`: **Stacks 0788**, part (1)(f),
  the identification `g⁻¹𝒪_𝒳 = 𝒪_{𝒳_{lisse,étale}}` — pinned to be the identity on sections — the
  morphism of ringed topoi it gives, and its flatness, all with no hypothesis. The remaining
  assertion of (1)(f), that `g^*` on sheaves of modules is `g^{-1}`, is
  `AlgebraicGeometry.Stack.LisseEtale.modulePullbackIso` of
  `StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleRingedModules.lean`.

## Implementation notes

The one ingredient the library did not already have is
`AlgebraicGeometry.Space.isSmooth_yoneda_map`, and it is a one-line instantiation of the
generic `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map` at
`AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget`. It is deliberately untagged, matching
its sibling `AlgebraicGeometry.Space.isFlat_yoneda_map`.

The three instances the relative-property route asks of `AlgebraicGeometry.Space.IsSmooth` are
all available: base-change stability is `AlgebraicGeometry.Space.isSmooth_isStableUnderBaseChange`
(**Stacks 03ZE**) and fppf target-locality comes from the fpqc one
(`AlgebraicGeometry.Space.smooth_isLocalAtTarget_fpqc`) along
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`. The hypothesis of
`AlgebraicGeometry.Stack.hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram` is **Stacks 06FC**
at smoothness, which is formalized as
`AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_smooth`.

Three of the imports each supply a name used here and nothing else:
`StacksFrontier.CategoryTheory.Sites.CoverLifting` for
`CategoryTheory.Functor.sheafAdjunctionLowerShriek`,
`StacksFrontier.CategoryTheory.Sites.Continuous` for
`CategoryTheory.Functor.isIso_unit_of_sheafPushforwardContinuous`, and
`StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness` for the instance
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`, which is what makes the ringed
clause (1)(f) unconditional rather than conditional on essential smallness.

The primed names restate declarations of
`StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleInclusion` with their hypothesis discharged rather
than editing them in place, because the hypothesis is part of those statements and a consumer may
still want the conditional form over an arbitrary category fibred in groupoids.

## References

* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u w

/-- **Stacks 03ZF for a morphism of the site**: a morphism of the big fppf site of `S` whose
underlying morphism of schemes is smooth is a smooth morphism of algebraic spaces over `S`.

This is the smooth sibling of `AlgebraicGeometry.Space.isFlat_yoneda_map`, and like it an
instantiation of the generic `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map` at a
property which is étale local on the source and target. -/
theorem Space.isSmooth_yoneda_map (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : Smooth ((BigFppfOver.toScheme B S hS).map k)) :
    Space.IsSmooth B S hS (yoneda.map k) :=
  Space.holdsOnEveryEtaleChart_yoneda_map B S hS
    Smooth.isEtaleLocalOnSourceAndTarget k hk

namespace Stack.LisseEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Smoothness of an object of an algebraic stack is inherited along a morphism lying over a
smooth morphism of schemes.** If `f : x ⟶ y` lies over a smooth morphism of schemes and `y` is a
smooth object in the sense of **Stacks 0787**, then so is `x`.

This is the closure condition of **Stacks 07AK** (1) for the smooth objects, and the only input of
Stacks 0788 (1) beyond full faithfulness of the inclusion. The source's argument is that
`x : U → 𝒳` is the composition `U → V → 𝒳`, so the statement reduces to smoothness of
1-morphisms being stable under composition; see the module documentation for how that is spelled
out here. -/
theorem smoothObject_of_smooth {x y : 𝒳.val.val.obj} (f : x ⟶ y)
    (hsmooth : Smooth (B.inclusion.map (𝒳.val.val.p.map f).left))
    (hy : smoothObject.{u, w} B S hS 𝒳 y) :
    smoothObject.{u, w} B S hS 𝒳 x := by
  let smoothP : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ h => Space.IsSmooth B S hS h
  have hsm : Space.IsSmoothLocalOnSourceAndTarget B S hS smoothP :=
    Space.isSmoothLocalOnSourceAndTarget_smooth B S hS
  let : (spaceProperty B S hS smoothP).IsStableUnderBaseChange :=
    Space.isSmooth_isStableUnderBaseChange B S hS
  let : (spaceProperty B S hS smoothP).IsLocalAtTarget
      (Space.Topology.fpqc.precoverage.{u, u + 1} B S hS) :=
    Space.smooth_isLocalAtTarget_fpqc B S hS
  let : (spaceProperty B S hS smoothP).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.fpqc.precoverage.{u, u + 1} B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  -- the two 2-Yoneda 1-morphisms are representable by algebraic spaces, the target being a stack
  have hrep (z : 𝒳.val.val.obj) : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := z) rfl)).hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _) _
  have hrx := hrep x
  have hry := hrep y
  -- smoothness of `y` as the relative property of Stacks 03YK (Stacks 06FM, forward direction)
  have hrely : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS smoothP)
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl)) hry :=
    hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, u + 1} B S hS smoothP hsm
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl)) hry hy
  -- relative smoothness of the 1-morphism `g : U → V` induced by the smooth morphism of schemes
  have hrelg : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS smoothP)
      (schemeFibredCategoryMap B S hS (𝒳.val.val.p.map f))
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS
        (𝒳.val.val.p.map f)) :=
    hasRelativeProperty_schemeFibredCategoryMap.{u, u + 1} B S hS
      (spaceProperty B S hS smoothP) _
      (Space.isSmooth_yoneda_map B S hS (𝒳.val.val.p.map f) hsmooth)
  -- the composite `U → V → 𝒳`, by Stacks 045B
  have hrcomp : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (schemeFibredCategoryMap B S hS (𝒳.val.val.p.map f) ≫
        objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl)).hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS _ _
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS _) hry
  have hrelcomp : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS smoothP)
      (schemeFibredCategoryMap B S hS (𝒳.val.val.p.map f) ≫
        objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl)) hrcomp :=
    hasRelativeProperty_comp B S hS (spaceProperty B S hS smoothP) _ _ _ _ hrelg hrely
  -- and `x : U → 𝒳` is that composite up to a 2-isomorphism
  have hrelx : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS smoothP)
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) hrx :=
    hasRelativeProperty_congr_twoIso.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS smoothP) (objectMorphismFactorIso B S hS 𝒳.val f).symm
      hrcomp hrx hrelcomp
  exact hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u + 1} B S hS smoothP
    𝒳.property (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) hrx hrelx

/-- **Stacks 0788, part (1): continuity of the inclusion of the lisse-étale site.** The étale case
of Stacks 07AK at the chosen étale precoverage of **Stacks 03FF**, with the closure condition of
07AK (1) discharged. -/
@[stacks 0788 "the inclusion of the lisse-etale site is continuous"]
theorem isContinuous_inclusion' :
    (smoothObject.{u, w} B S hS 𝒳).ι.IsContinuous (inclusionTopology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) :=
  isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms B S hS 𝒳)

/-- **Stacks 0788, part (1): cocontinuity of the inclusion of the lisse-étale site.** -/
@[stacks 0788 "the inclusion of the lisse-etale site is cocontinuous"]
theorem isCocontinuous_inclusion' :
    (smoothObject.{u, w} B S hS 𝒳).ι.IsCocontinuous (inclusionTopology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) :=
  isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms B S hS 𝒳)

/-- **Stacks 0788, part (1): continuity of the inclusion of the lisse-étale site, for the
chosen-family topology.** The same assertion at
`AlgebraicGeometry.Stack.LisseEtale.topology`, which is the description Stacks 0787 is recorded
at. -/
@[stacks 0788 "continuity of that inclusion, read at the topologies"]
theorem isContinuous_inclusion_topology' :
    (smoothObject.{u, w} B S hS 𝒳).ι.IsContinuous (topology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) :=
  isContinuous_inclusion_topology.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms B S hS 𝒳)

/-- **Stacks 0788, part (1): cocontinuity of the inclusion of the lisse-étale site, for the
chosen-family topology.** -/
@[stacks 0788 "cocontinuity of that inclusion, read at the topologies"]
theorem isCocontinuous_inclusion_topology' :
    (smoothObject.{u, w} B S hS 𝒳).ι.IsCocontinuous (topology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) :=
  isCocontinuous_inclusion_topology.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms B S hS 𝒳)

/-- **The morphism of topoi of Stacks 0788 (1)(a)**:
`g : Sh(𝒳_{lisse,étale}) ⟶ Sh(𝒳_étale)`, with inverse image restriction along the inclusion of
the smooth objects. This is `AlgebraicGeometry.Stack.LisseEtale.toposMorphism` with its hypothesis
discharged. -/
@[stacks 0788 "the morphism of topoi induced by the lisse-etale inclusion"]
noncomputable def toposMorphism' :
    MorphismOfTopoi
      (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) (Type (u + 1)))
      (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (Type (u + 1))) :=
  toposMorphism.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms B S hS 𝒳)

/-- **The morphism of topoi of Stacks 0788 (1)(a), for the chosen-family topology**: the same
morphism of topoi read at `AlgebraicGeometry.Stack.LisseEtale.topology`. -/
@[stacks 0788 "the lisse-etale morphism of topoi, read at the topologies"]
noncomputable def toposMorphismTopology' :
    MorphismOfTopoi
      (Sheaf (topology.{u, w} B S hS 𝒳) (Type (u + 1)))
      (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (Type (u + 1))) :=
  toposMorphismTopology.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms B S hS 𝒳)

/-! ### Lower shriek on sheaves of sets (Stacks 0788 (1)(b) and (1)(c)) -/

section Sets

attribute [local instance] isContinuous_inclusion_topology' isCocontinuous_inclusion_topology'

/-- **The lower-shriek functor `g_!^{Sh}` of Stacks 0788 (1)(b)**, on sheaves of sets: the left
Kan extension along the inclusion of the smooth objects, sheafified
(`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`).

No smallness assumption enters at this coefficient universe. The objects of the étale site of `𝒳`
form a `Type (u + 1)` whose morphisms live in `Type u`, so the comma categories indexing the Kan
extension and the sheafification are `Type (u + 1)`-sized, and `Type (u + 1)` has the limits and
colimits of that size. -/
@[sga "4 IV 4.10.6" "3°, special case"]
noncomputable abbrev setsShriek :
    Sheaf (topology.{u, w} B S hS 𝒳) (Type (u + 1)) ⥤
      Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback (smoothObject.{u, w} B S hS 𝒳).ι
    (Type (u + 1)) (topology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))

/-- **Stacks 0788, part (1)(b).** The inverse image of the morphism of topoi `g` of
Stacks 0788 (1)(a) has a left adjoint on sheaves of sets, namely
`AlgebraicGeometry.Stack.LisseEtale.setsShriek`.

This is `CategoryTheory.Functor.sheafAdjunctionLowerShriek` (**Stacks 00XR** (2)) at the inclusion
of the smooth objects, whose continuity is
`AlgebraicGeometry.Stack.LisseEtale.isContinuous_inclusion_topology'`. The right-hand side is the
inverse image of `AlgebraicGeometry.Stack.LisseEtale.toposMorphismTopology'`, restriction along
the inclusion. -/
@[stacks 0788 "part (1)(b): the lower-shriek adjunction on sheaves of sets"]
noncomputable abbrev setsShriekAdjunction :
    setsShriek.{u, w} B S hS 𝒳 ⊣
      (smoothObject.{u, w} B S hS 𝒳).ι.sheafPushforwardContinuous (Type (u + 1))
        (topology.{u, w} B S hS 𝒳)
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) :=
  (smoothObject.{u, w} B S hS 𝒳).ι.sheafAdjunctionLowerShriek (Type (u + 1))
    (topology.{u, w} B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))

/-- **Stacks 0788, part (1)(c), the half about `g_!^{Sh}`.** The canonical map `F ⟶ g⁻¹g_!F` on
sheaves of sets — the unit of `AlgebraicGeometry.Stack.LisseEtale.setsShriekAdjunction` — is an
isomorphism.

This is **Stacks 00XT** for a fully faithful, continuous and cocontinuous functor of sites, all
three of which hold for the inclusion of the smooth objects at this topology. -/
@[stacks 0788 "part (1)(c): the unit of the sets lower-shriek adjunction is invertible"]
instance isIso_setsShriekAdjunction_unit : IsIso (setsShriekAdjunction.{u, w} B S hS 𝒳).unit :=
  Functor.isIso_unit_of_sheafPushforwardContinuous (smoothObject.{u, w} B S hS 𝒳).ι
    (Type (u + 1)) (topology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (setsShriekAdjunction.{u, w} B S hS 𝒳)

end Sets

/-! ### Lower shriek on abelian sheaves (Stacks 0788 (1)(d) and (1)(e)) -/

section Abelian

/-- **The adjunction `g_! ⊣ g⁻¹` of Stacks 0788 (1)(d) on abelian sheaves**, with no hypothesis:
`AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriekAdjunction` with its closure property
discharged. -/
@[stacks 0788 "part (1)(d): the lower-shriek adjunction on abelian sheaves"]
noncomputable abbrev abelianLowerShriekAdjunction' :
    abelianLowerShriek.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms B S hS 𝒳) ⊣
      abelianInverseImage.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms B S hS 𝒳) :=
  abelianLowerShriekAdjunction.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms B S hS 𝒳)

/-- **Stacks 0788, part (1)(e)**, with no hypothesis: the canonical map `F ⟶ g⁻¹(g_!F)` on abelian
sheaves — the unit of `AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriekAdjunction'` — is an
isomorphism. This is **Stacks 077I**, whose three hypotheses on the inclusion of the smooth
objects are full faithfulness, `isContinuous_inclusion'` and `isCocontinuous_inclusion'`. -/
@[stacks 0788 "part (1)(e): the unit of the abelian lower-shriek adjunction is invertible"]
theorem isIso_abelianLowerShriek_unit'
    (F : Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1}) :
    IsIso ((abelianLowerShriekAdjunction'.{u, w} B S hS 𝒳).unit.app F) :=
  isIso_abelianLowerShriek_unit.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms B S hS 𝒳) F

end Abelian

/-! ### The ringed topoi of Stacks 0788 (1)(f) -/

section Ringed

open Stacks.Sheaves.ToposPushforward

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **The lisse-étale site as a ringed topos**, with no hypothesis: the smooth objects with the
restriction of the étale structure sheaf of **Stacks 06TV**. This is
`AlgebraicGeometry.Stack.LisseEtale.ringedTopos` with its closure property discharged. -/
noncomputable abbrev ringedTopos' : RingedTopos.{u, u + 1, u} :=
  ringedTopos.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms B S hS 𝒳)

/-- **The morphism of topoi `g` of Stacks 0788 (1)(a) at the universe of the sections of the
structure sheaf.** This is the same geometric morphism as
`AlgebraicGeometry.Stack.LisseEtale.toposMorphism'` — inverse image restriction along the
inclusion of the smooth objects, pushforward its cocontinuous right adjoint — read at `Type u`
rather than at `Type (u + 1)`, which is where the structure sheaves of **Stacks 06TV** live. -/
noncomputable abbrev toposMorphismOnRings :
    MorphismOfTopoi (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) (Type u))
      (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (Type u)) :=
  subsiteToposMorphism B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳)

/-- **Stacks 0788, part (1)(f), first assertion**:
`g⁻¹𝒪_𝒳 = 𝒪_{𝒳_{lisse,étale}}`. The inverse image of the étale structure sheaf of **Stacks 06TV**
along the morphism of topoi of Stacks 0788 (1)(a) is the structure sheaf of the lisse-étale site.

The inverse image of `g` on sheaves of sets *is* restriction along the inclusion of the smooth
objects, so this is the comparison of the transported commutative ring operations with those of
the restricted sheaf, and that comparison is the identity on sections
(`AlgebraicGeometry.Stack.LisseEtale.structureSheafIso_apply`). -/
@[stacks 0788 "part (1)(f): the inverse image of the structure sheaf is the lisse-etale \
structure sheaf"]
noncomputable def structureSheafIso :
    (inverseImageCommRingFunctor (toposMorphismOnRings.{u, w} B S hS 𝒳)).obj
        (etaleRingedTopos.{u, w} B S hS 𝒳).O ≅ (ringedTopos'.{u, w} B S hS 𝒳).O :=
  subsiteStructureSheafIso B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
    (etaleTopology_le_topology B) (smoothObject.{u, w} B S hS 𝒳)

/-- **Stacks 0788, part (1)(f).** The identification `g⁻¹𝒪_𝒳 ≅ 𝒪_{𝒳_{lisse,étale}}` is the
identity on sections over a smooth object. This pins it: it is not an arbitrary automorphism of
the restricted structure sheaf. -/
@[stacks 0788 "part (1)(f): that identification, on sections"]
theorem structureSheafIso_apply (U : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ)
    (a : ((inverseImageCommRingFunctor (toposMorphismOnRings.{u, w} B S hS 𝒳)).obj
      (etaleRingedTopos.{u, w} B S hS 𝒳).O).obj.obj U) :
    (structureSheafIso.{u, w} B S hS 𝒳).hom.hom.app U a = a :=
  subsiteStructureSheafIso_hom_app B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, w} B S hS 𝒳) U a

/-- **The morphism of ringed topoi of Stacks 0788 (1)(f)**, with no hypothesis:
`(g, g♯) : (Sh(𝒳_{lisse,étale}), 𝒪_{𝒳_{lisse,étale}}) ⟶ (Sh(𝒳_étale), 𝒪_𝒳)`, whose structure map
is the adjoint of `AlgebraicGeometry.Stack.LisseEtale.structureSheafIso`. This is
`AlgebraicGeometry.Stack.LisseEtale.ringedToposMorphism` with its closure property
discharged. -/
@[stacks 0788 "part (1)(f): the induced morphism of ringed topoi"]
noncomputable def ringedToposMorphism' :
    RingedToposHom (ringedTopos'.{u, w} B S hS 𝒳) (etaleRingedTopos.{u, w} B S hS 𝒳) :=
  ringedToposMorphism.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms B S hS 𝒳)

/-- **Stacks 0788, part (1)(f), second assertion**, with no hypothesis: the lisse-étale morphism
of ringed topoi is flat in the sense of **Stacks 04JB**, its inverse-image structure map being the
isomorphism `AlgebraicGeometry.Stack.LisseEtale.structureSheafIso`. -/
@[stacks 0788 "part (1)(f): that morphism of ringed topoi is flat"]
theorem isFlat_ringedToposMorphism' :
    RingedToposHom.IsFlat
      (X := ringedTopos'.{u, w} B S hS 𝒳) (Y := etaleRingedTopos.{u, w} B S hS 𝒳)
      (ringedToposMorphism'.{u, w} B S hS 𝒳) :=
  isFlat_ringedToposMorphism.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms B S hS 𝒳)

end Ringed

end Stack.LisseEtale

end AlgebraicGeometry

add_to_stacks 0788 "lisse_inclusion" CategoryTheory.ObjectProperty.fullyFaithfulι

end
