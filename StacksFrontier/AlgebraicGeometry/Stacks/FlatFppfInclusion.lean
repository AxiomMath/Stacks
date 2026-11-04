module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSite
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryRingedTopos
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategorySite
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# The inclusion of the flat-fppf site (Stacks 0788, flat case)

Stacks 0788 (2) asserts that the inclusion of the flat-fppf site of an algebraic stack `𝒳` into
its fppf site is fully faithful, continuous and cocontinuous, and derives from that the morphism
of topoi `g : Sh(𝒳_{flat,fppf}) → Sh(𝒳_{fppf})` whose inverse image is restriction, together with
the lower-shriek functors left adjoint to it.

Full faithfulness is `CategoryTheory.ObjectProperty.fullyFaithfulι`. Continuity and cocontinuity
are the fppf case of **Stacks 07AK**, proved as
`AlgebraicGeometry.Stack.isContinuous_ι_fppfTopology` and
`AlgebraicGeometry.Stack.isCocontinuous_ι_fppfTopology`, whose one hypothesis is the closure
condition of 07AK (1): *an object of `𝒳` admitting a morphism to a flat object, lying over a flat
and locally finitely presented morphism of schemes, is itself flat.*

That closure condition is proved here, so the three assertions are unconditional and carry the
tag. The proof is the one the source leaves implicit at "the composition `U → V → 𝒳`": flatness of
an object is flatness of its 2-Yoneda 1-morphism, which by **Stacks 06FM** is the relative
property of **Stacks 03YK** at flatness of morphisms of algebraic spaces; that relative property is
stable under composition by **Stacks 045B**; and `AlgebraicGeometry.Stack.objectMorphismFactorIso`
exhibits `x : U → 𝒳` as the composite of `g : U → V` with `y : V → 𝒳` up to a 2-isomorphism, along
which the relative property transports.

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.ClosedUnderFlatMorphisms`: the closure condition of
  **Stacks 07AK** (1) for the flat objects, in the form 07AK states it.
* `AlgebraicGeometry.Stack.FlatFppf.toposMorphism` and
  `AlgebraicGeometry.Stack.FlatFppf.toposMorphismTopology`: **Stacks 0788** (2)(a), the morphism
  of topoi `g`, at each of the two descriptions of the topology.
* `AlgebraicGeometry.Stack.FlatFppf.setsShriek` and
  `AlgebraicGeometry.Stack.FlatFppf.abelianShriek`: **Stacks 0788** (2)(b) and (2)(d), the left
  adjoint `g_!` of `g⁻¹` on sheaves of sets and on abelian sheaves.
* `AlgebraicGeometry.Stack.FlatFppf.abelianInverseImage`,
  `AlgebraicGeometry.Stack.FlatFppf.abelianPushforward` and
  `AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriek`: the three functors `g⁻¹`, `g_*` and
  `g_!` on abelian sheaves read at `AlgebraicGeometry.Stack.FlatFppf.inclusionTopology` through
  the general theory of **Stacks 077I**, with their adjunctions
  `AlgebraicGeometry.Stack.FlatFppf.abelianPushforwardAdjunction` and
  `AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriekAdjunction`.

## Main results

* `AlgebraicGeometry.Stack.flatObject_of_flat`: the closure condition — an object admitting a
  morphism to a flat object over a *flat* morphism of schemes is flat.
* `AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`: the same, in the form
  **Stacks 07AK** (1) states it.
* `AlgebraicGeometry.Stack.FlatFppf.isContinuous_inclusion'`,
  `AlgebraicGeometry.Stack.FlatFppf.isCocontinuous_inclusion'`,
  `AlgebraicGeometry.Stack.FlatFppf.isContinuous_inclusion_topology` and
  `AlgebraicGeometry.Stack.FlatFppf.isCocontinuous_inclusion_topology`: **Stacks 0788** (2),
  continuity and cocontinuity of the inclusion, at each of the two descriptions of the topology.
* `AlgebraicGeometry.Stack.FlatFppf.topology_le_inclusionTopology`,
  `AlgebraicGeometry.Stack.FlatFppf.inclusionTopology_le_topology` and
  `AlgebraicGeometry.Stack.FlatFppf.inclusionTopology_eq_topology`: the two descriptions of the
  topology of the flat-fppf site agree.
* `AlgebraicGeometry.BigFppfOver.exists_isCovering_le_of_mem_topology` and
  `AlgebraicGeometry.Stack.exists_isCovering_le_of_mem_associatedTopology`: every covering sieve
  of the big fppf category over `S`, respectively of the fppf site of a category fibred in
  groupoids over it, contains a family whose image is a *chosen* covering family.
* `AlgebraicGeometry.Stack.FlatFppf.setsShriekAdjunction` and
  `AlgebraicGeometry.Stack.FlatFppf.isIso_setsShriekAdjunction_unit`, with the general instance
  `CategoryTheory.Functor.isIso_sheafAdjunctionCocontinuous_counit`: **Stacks 0788**
  (2)(b) and (2)(c), the adjunction `g_! ⊣ g⁻¹` on sheaves of sets and the fact that the two
  canonical maps `F ⟶ g⁻¹g_!F` and `g⁻¹g_*F ⟶ F` are isomorphisms.
* `AlgebraicGeometry.Stack.FlatFppf.abelianShriekAdjunction` and
  `AlgebraicGeometry.Stack.FlatFppf.isIso_abelianShriekAdjunction_unit`: **Stacks 0788** (2)(d)
  and (2)(e), the same two assertions on abelian sheaves; see the implementation notes for the
  essential smallness they rest on and where it comes from.
* `AlgebraicGeometry.Stack.FlatFppf.isIso_abelianLowerShriek_unit` and
  `AlgebraicGeometry.Stack.FlatFppf.isIso_abelianPushforward_counit`: **Stacks 077I** for this
  inclusion, at `AlgebraicGeometry.Stack.FlatFppf.inclusionTopology`.

## Implementation notes

`AlgebraicGeometry.Stack.flatObject_of_flat` does **not** use the locally-finite-presentation
hypothesis of Stacks 07AK (1): flatness of the morphism of schemes alone suffices, because the
relative property being composed is flatness and nothing in the argument tests finite
presentation. It is therefore stated without it, and
`AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms` discards the unused hypothesis.

### The topology of the flat-fppf site

Two descriptions of that topology are available, and they are proved equal here
(`AlgebraicGeometry.Stack.FlatFppf.inclusionTopology_eq_topology`); the statements below are
nevertheless phrased at one of them, so one has to be chosen. The one used first is
`AlgebraicGeometry.Stack.FlatFppf.inclusionTopology`, namely
`P.ι.inheritedTopology (associatedTopology … B.topology)` for
`P = AlgebraicGeometry.Stack.flatObject`: a family of morphisms of flat objects covers exactly
when the sieve its image generates covers in `𝒳_{fppf}`. Three reasons:

* it is the reading of Stacks 0787's covering notion that the library's Stacks 07AK material is
  built on — `CategoryTheory.ObjectProperty.subcategoryCoverage_toGrothendieck` proves that the
  coverage of 07AK, the families of flat objects whose image covers in `𝒳_{fppf}`, generates
  exactly this topology;
* it is the same construction `CategoryTheory.Functor.inheritedTopology` that
  `AlgebraicGeometry.Stack.associatedTopology` (**Stacks 06TP**) applies one level down, so the
  two sites of 0788 (2) are described in the same way;
* it is the one at which continuity and cocontinuity come out of Stacks 07AK directly, the other
  description then inheriting them along the equality of the two: see below.

The sibling `AlgebraicGeometry.Stack.FlatFppf.topology` of
`StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSite` is generated instead by the families whose
image is one of the *chosen* covering families of the ambient big site. The two are equal; no
third topology is introduced. Each inequality is proved separately, because the two have quite
different content.

`AlgebraicGeometry.Stack.FlatFppf.topology_le_inclusionTopology` is formal: a chosen covering
family of flat objects consists of strongly cartesian morphisms and its image covers, so it
generates a covering sieve of the inherited topology.

`AlgebraicGeometry.Stack.FlatFppf.inclusionTopology_le_topology` is the content: every fppf
covering sieve of a flat object has to be *refined by a chosen covering family with flat
sources*. Three nested inherited structures have to be unwound for it — the localization of the
big fppf site at `S`, the site `𝒳` inherits from it, and the site the flat objects inherit from
`𝒳` — and that is what the two refinement lemmas above do: a covering sieve of the chosen-family
topology of the big site contains a chosen covering family
(`AlgebraicGeometry.exists_covering_le_of_mem_topology`), hence so does a covering sieve of its
localization at `S`, and the cartesian lifts of such a family refine a covering sieve of `𝒳`
(`AlgebraicGeometry.Stack.exists_isCovering_le_of_mem_associatedTopology`, the fppf instance of
the generic `AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`). The
members of a chosen fppf family are flat, so those lifts are flat objects by
`AlgebraicGeometry.Stack.flatObject_of_flat`, and the family is already a covering family of the
flat-fppf site.

Continuity transfers from a topology to a smaller one and cocontinuity transfers the other way,
so both assertions of 0788 (2) are recorded at both descriptions of the topology.

### Conditional and unconditional forms

`AlgebraicGeometry.Stack.FlatFppf.isContinuous_inclusion` and
`AlgebraicGeometry.Stack.FlatFppf.isCocontinuous_inclusion` take the closure condition as an
explicit hypothesis, and the primed
`AlgebraicGeometry.Stack.FlatFppf.isContinuous_inclusion'` and
`AlgebraicGeometry.Stack.FlatFppf.isCocontinuous_inclusion'` are the same statements with that
hypothesis discharged by
`AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`; only the primed ones carry the tag,
the hypothesised ones not being 0788's statement. The conditional forms are kept because the
abelian layer below reads them at an arbitrary instance of the hypothesis, exactly as
`AlgebraicGeometry.Stack.LisseEtale.isContinuous_inclusion` and
`AlgebraicGeometry.Stack.LisseEtale.isContinuous_inclusion'` are kept apart on the lisse-étale
side.

### The morphism of topoi

The morphism of topoi is the cocontinuous one: `g_*` is
`CategoryTheory.Functor.sheafPushforwardCocontinuous` and `g⁻¹` is
`CategoryTheory.Functor.sheafPushforwardContinuous`, i.e. restriction along the inclusion of the
flat objects on the nose, which is the form 0788 (2)(a) requires; left exactness of the inverse
image is then automatic. The adjunction `g⁻¹ ⊣ g_*` is a *field* of `toposMorphism` rather than a
separate declaration, because its statement names the two sheaf functors and so cannot be formed
before the two locality instances are available. On abelian sheaves it is named separately, as
`AlgebraicGeometry.Stack.FlatFppf.abelianPushforwardAdjunction`, because the unit and counit
statements of Stacks 077I have to refer to it.

### Lower shriek, and the essential smallness the abelian case rests on

Parts (2)(b) and (2)(c) are the lower-shriek adjunction of **Stacks 00XR** (2) and the two
isomorphisms of **Stacks 00XT** for a fully faithful, continuous and cocontinuous functor of
sites, instantiated at this inclusion. On sheaves of sets they are unconditional: the fppf site of
`𝒳` is a `Type (u + 1)` with morphisms in `Type u`, so the comma categories indexing the left Kan
extension and the sheafification are of that size and `Type (u + 1)` has the limits and colimits
they need.

Parts (2)(d) and (2)(e), the same two assertions on *abelian* sheaves, need more: sheafification
and Kan extensions with abelian coefficients need the site to be essentially small. That is not
automatic from the sizes, and it is supplied rather than assumed.
`StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite` reduces it to two inputs — essential
smallness of the size-bounded category of schemes, which is an instance
(`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmallSchemes`, Stacks 000J), and essential
smallness of each fibre `𝒳(U)`, which is a descent statement about the smooth presentation. The
latter is
`AlgebraicGeometry.Stack.essentiallySmall_fiber_algebraicStack` of
`StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness`, and the composite
`EssentiallySmall.{u} 𝒳.val.val.obj` is the instance
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack` there. So the abelian declarations
below are unconditional, exactly as 0788 (2)(d) and (2)(e) state them, and instance search
discharges the smallness at each of them.

Each of the two assertions therefore carries the tag, at one declaration apiece: (2)(d) at
`AlgebraicGeometry.Stack.FlatFppf.abelianShriekAdjunction`, whose type names
`AlgebraicGeometry.Stack.FlatFppf.abelianShriek` and so states the clause whole — the functor on
its own asserts nothing and is left untagged, exactly as
`AlgebraicGeometry.Stack.FlatFppf.setsShriek` is for (2)(b) — and (2)(e) at
`AlgebraicGeometry.Stack.FlatFppf.isIso_abelianShriekAdjunction_unit`.

The second abelian layer, at `AlgebraicGeometry.Stack.FlatFppf.inclusionTopology` and at the
single coefficient universe `AbCat.{u, u + 1} = Ab.{u + 1}`, is the general theory of
**Stacks 077I** (`StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekFullyFaithful`)
specialised to this inclusion: no construction is repeated, because the inclusion satisfies that
file's three hypotheses — continuous, cocontinuous and fully faithful. It is what the derived
lower shriek of **Stacks 07AS** is built on, and it is stated conditionally for the reason
recorded above.

### What 0788 asserts and is not proved here

Part (2)(f), the identification `g⁻¹𝒪_𝒳 = 𝒪_{𝒳_{flat,fppf}}` making `g` a flat morphism of ringed
topoi, is `StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRinged`, which builds the two ringed
topoi and the morphism between them from the unconditional continuity and cocontinuity proved
here. Part (1), the lisse-étale case, is
`StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleInclusion` and
`StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure`.

## References

* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06NU](https://stacks.math.columbia.edu/tag/06NU)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 077I](https://stacks.math.columbia.edu/tag/077I)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Flatness of an object of an algebraic stack is inherited along a morphism lying over a flat
morphism of schemes.** If `f : x ⟶ y` lies over a flat morphism of schemes and `y` is flat in the
sense of **Stacks 0H14**, then `x` is flat.

This is the closure condition of **Stacks 07AK** (1) for the flat objects, and the only input of
Stacks 0788 (2) beyond full faithfulness of the inclusion. The source's argument is that
`x : U → 𝒳` is the composition `U → V → 𝒳`, so the statement reduces to flatness of 1-morphisms
being stable under composition. In the library that is: flatness of an object is the existential
smooth-diagram criterion (condition (2) of **Stacks 06FM**), which for a 1-morphism representable
by algebraic spaces is the relative property of **Stacks 03YK** at
`AlgebraicGeometry.Space.IsFlat`; the relative property is stable under composition by
**Stacks 045B**; and `AlgebraicGeometry.Stack.objectMorphismFactorIso` identifies `x : U → 𝒳` with
the composite up to a 2-isomorphism, along which the relative property transports by
`AlgebraicGeometry.Stack.hasRelativeProperty_congr_twoIso`.

The locally-finite-presentation hypothesis of Stacks 07AK (1) is not needed; see the
implementation notes. -/
theorem flatObject_of_flat {x y : 𝒳.val.val.obj} (f : x ⟶ y)
    (hflat : Flat (B.inclusion.map (𝒳.val.val.p.map f).left))
    (hy : flatObject B S hS 𝒳.val y) :
    flatObject B S hS 𝒳.val x := by
  let flatP : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ h => Space.IsFlat B S hS h
  have hsm : Space.IsSmoothLocalOnSourceAndTarget B S hS flatP :=
    Space.isSmoothLocalOnSourceAndTarget_flat B S hS
  let : (spaceProperty B S hS flatP).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  let : (spaceProperty B S hS flatP).IsLocalAtTarget
      (Space.Topology.fpqc.precoverage.{u, u + 1} B S hS) :=
    Space.isFlat_isLocalAtTarget_fpqc B S hS
  let : (spaceProperty B S hS flatP).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.fpqc.precoverage.{u, u + 1} B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  let : (spaceProperty B S hS flatP).IsStableUnderComposition :=
    Space.isFlat_isStableUnderComposition B S hS
  -- the 2-Yoneda 1-morphisms of objects are representable by algebraic spaces, the target being a
  -- stack
  have hr (z : 𝒳.val.val.obj) : IsRepresentableByAlgebraicSpaces B S hS
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := z) rfl)).hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _) _
  -- flatness of `y` as the relative property of Stacks 03YK (Stacks 06FM, forward direction)
  have hrely : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS flatP)
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl)) (hr y) :=
    hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, u + 1} B S hS flatP hsm
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl)) (hr y) hy
  -- relative flatness of the 1-morphism `g : U → V` induced by the flat morphism of schemes
  have hrelg : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS flatP)
      (schemeFibredCategoryMap B S hS (𝒳.val.val.p.map f))
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS
        (𝒳.val.val.p.map f)) :=
    hasRelativeProperty_schemeFibredCategoryMap.{u, u + 1} B S hS
      (spaceProperty B S hS flatP) _
      (Space.isFlat_yoneda_map B S hS (𝒳.val.val.p.map f) hflat)
  -- the composite `U → V → 𝒳`, by Stacks 045B
  have hrcomp : IsRepresentableByAlgebraicSpaces B S hS
      (schemeFibredCategoryMap B S hS (𝒳.val.val.p.map f) ≫
        objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl)).hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS _ _
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS _) (hr y)
  have hrelcomp : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS flatP)
      (schemeFibredCategoryMap B S hS (𝒳.val.val.p.map f) ≫
        objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl)) hrcomp :=
    hasRelativeProperty_comp B S hS (spaceProperty B S hS flatP) _ _ _ _ hrelg hrely
  -- and `x : U → 𝒳` is that composite up to a 2-isomorphism
  have hrelx : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS flatP)
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) (hr x) :=
    hasRelativeProperty_congr_twoIso.{u, u, u + 1, u + 1} B S hS
      (spaceProperty B S hS flatP) (objectMorphismFactorIso B S hS 𝒳.val f).symm
      hrcomp (hr x) hrelcomp
  exact hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u + 1} B S hS flatP
    𝒳.property (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) (hr x) hrelx

/-! ### Refining a covering sieve by a chosen covering family -/

/-- **A covering sieve of the big fppf category over `S` contains a chosen covering family.**
This is `AlgebraicGeometry.exists_covering_le_of_mem_topology` after localization at `S`: a
covering sieve of `AlgebraicGeometry.BigFppfOver.topology` is by definition one whose image under
`CategoryTheory.Sieve.overEquiv` covers in the big fppf site, and a chosen covering family
refining that image is read back upstairs by equipping each of its members with the composite
structure morphism to `S`. -/
theorem _root_.AlgebraicGeometry.BigFppfOver.exists_isCovering_le_of_mem_topology
    {U : BigFppfOver B S hS} {R : Sieve U} (hR : R ∈ BigFppfOver.topology B S hS U) :
    ∃ E : PreZeroHypercover.{u + 1} U,
      BigFppfOver.IsCovering B S hS ⟨U, E⟩ ∧ E.presieve₀ ≤ R.arrows := by
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨E, hE, hle⟩ := exists_covering_le_of_mem_topology B hR
  refine ⟨⟨E.I₀, fun i => Over.mk (E.f i ≫ U.hom), fun i => Over.homMk (E.f i) rfl⟩, ?_, ?_⟩
  · change B.IsCovering ⟨U.left, _⟩
    simpa [PreZeroHypercover.map] using hE
  · rw [Presieve.ofArrows_le_iff]
    intro i
    exact (Sieve.overEquiv_iff R (E.f i)).mp (hle _ _ ⟨i⟩)

section Refinement

universe v v'

variable {X : Type v} [Category.{v'} X] (p : X ⥤ BigFppfOver B S hS)

/-- **A covering sieve of the fppf site of a category fibred in groupoids contains a family whose
image is a chosen covering family.** The generating covering families of
`AlgebraicGeometry.Stack.associatedTopology` (**Stacks 06TP**) only ask that the image *generate*
a covering sieve, and the topology is their saturation; this sharpens both.

This is the fppf instance of
`AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`, its base-level input
being `AlgebraicGeometry.BigFppfOver.exists_isCovering_le_of_mem_topology`. -/
theorem exists_isCovering_le_of_mem_associatedTopology (hp : p.IsFiberedInGroupoids)
    ⦃y : X⦄ (T : Sieve y) (hT : T ∈ associatedTopology B S hS p B.topology y) :
    ∃ E : PreZeroHypercover.{u + 1} y,
      BigFppfOver.IsCovering B S hS ⟨p.obj y, E.map p⟩ ∧ E.presieve₀ ≤ T.arrows :=
  exists_chosenCovering_le_of_mem_associatedTopology B S hS p B.topology
    (fun E => BigFppfOver.IsCovering B S hS E)
    (fun _ _ hR => BigFppfOver.exists_isCovering_le_of_mem_topology B S hS hR) hp T hT

end Refinement

namespace FlatFppf

/-- The flat objects of an algebraic stack, read as a property of the objects of its total
category. -/
abbrev objectProperty : ObjectProperty 𝒳.val.val.obj := flatObject B S hS 𝒳.val

/-- **The closure condition of Stacks 07AK (1) for the flat objects.** An object of `𝒳` with a
morphism to a flat object, lying over a flat and locally finitely presented morphism of schemes,
is flat.

This is the only input of Stacks 0788 (2) beyond full faithfulness of the inclusion. It is the
form in which Stacks 07AK states the condition, and it is
`AlgebraicGeometry.Stack.flatObject_of_flat` with the locally-finite-presentation hypothesis
added back; that hypothesis is not used. -/
def ClosedUnderFlatMorphisms : Prop :=
  ∀ ⦃x y : 𝒳.val.val.obj⦄ (f : x ⟶ y),
    Flat (B.inclusion.map (𝒳.val.val.p.map f).left) →
    LocallyOfFinitePresentation (B.inclusion.map (𝒳.val.val.p.map f).left) →
    flatObject B S hS 𝒳.val y → flatObject B S hS 𝒳.val x

/-- **The closure condition of Stacks 07AK (1) holds for the flat objects of an algebraic
stack.** -/
theorem closedUnderFlatMorphisms : ClosedUnderFlatMorphisms B S hS 𝒳 :=
  fun {_ _} f hflat _ hy => flatObject_of_flat B S hS 𝒳 f hflat hy

/-- The topology of the flat-fppf site in the sense of the source: a family of morphisms of flat
objects covers exactly when its image covers in the fppf site of `𝒳` (**Stacks 06TP**). -/
abbrev inclusionTopology : GrothendieckTopology (ObjectProperty.FullSubcategory
    (objectProperty B S hS 𝒳)) :=
  (objectProperty B S hS 𝒳).ι.inheritedTopology
    (associatedTopology B S hS 𝒳.val.val.p B.topology)

/-- **The topology generated by the chosen covering families of the flat-fppf site is coarser
than the one it inherits from `𝒳_{fppf}`.**

No hypothesis is needed. A chosen covering family of `AlgebraicGeometry.Stack.FlatFppf.topology`
is a family of morphisms of flat objects whose image in the big fppf category of `S` is a chosen
fppf covering family. Each of its members is strongly cartesian for the inclusion of the full
subcategory, by `CategoryTheory.ObjectProperty.instIsStronglyCartesianIotaMap`, and its image in
`𝒳` is a family of strongly cartesian morphisms, because every morphism of a category fibred in
groupoids is strongly cartesian over its own image; pushing it down to `B.Schemes` gives back the
chosen fppf family. So it is a covering family of the inherited precoverage at each of the two
steps `AlgebraicGeometry.Stack.FlatFppf.inclusionTopology` is built from. -/
theorem topology_le_inclusionTopology :
    topology B S hS 𝒳 ≤ inclusionTopology B S hS 𝒳 := by
  refine Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr ?_
  intro X R hR
  obtain ⟨E, rfl, hE⟩ := hR
  rw [GrothendieckTopology.mem_toPrecoverage_iff]
  apply Precoverage.generate_mem_toGrothendieck
  refine ⟨fun _ _ _ => inferInstance, ?_⟩
  rw [GrothendieckTopology.mem_toPrecoverage_iff]
  apply Precoverage.generate_mem_toGrothendieck
  refine ⟨fun _ f _ => 𝒳.val.isFiberedInGroupoids.isStronglyCartesian f, ?_⟩
  rw [GrothendieckTopology.mem_toPrecoverage_iff, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_generate, ← Sieve.arrows_generate_map_eq_functorPushforward,
    Sieve.generate_sieve]
  apply Precoverage.generate_mem_toGrothendieck
  exact ⟨((E.map (objectProperty B S hS 𝒳).ι).map 𝒳.val.val.p).map
      (BigFppfOver.forget B S hS),
    by simp only [PreZeroHypercover.presieve₀_map], hE⟩

/-- **Every fppf covering sieve of a flat object is refined by a chosen covering family with flat
sources.** This is the converse inequality to
`AlgebraicGeometry.Stack.FlatFppf.topology_le_inclusionTopology`, and the assertion with content:
the inherited topology of the source's own definition is no finer than the topology generated by
the chosen covering families.

Both sides are generated by a collection of families, so it suffices to refine a generating family
of the first by a covering family of the second. A generating family of the inherited topology is
one whose image in `𝒳` generates an fppf covering sieve there, and
`AlgebraicGeometry.Stack.exists_isCovering_le_of_mem_associatedTopology` refines that sieve by a
family whose image is a *chosen* covering family of the big fppf category over `S`. The members of
a chosen family are flat (**Stacks 021R**, through
`AlgebraicGeometry.Stack.flat_and_locallyOfFinitePresentation_of_mem_precoverage`), so their
sources are flat objects by `AlgebraicGeometry.Stack.flatObject_of_flat`; the family therefore
lives in the flat-fppf site, where it is a covering family by construction, and each of its
members factors through a member of the family one started with. -/
theorem inclusionTopology_le_topology :
    inclusionTopology B S hS 𝒳 ≤ topology B S hS 𝒳 := by
  rw [inclusionTopology, Functor.inheritedTopology_eq,
    Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
  intro x R hR
  rw [GrothendieckTopology.mem_toPrecoverage_iff]
  obtain ⟨E, hEcov, hEle⟩ := exists_isCovering_le_of_mem_associatedTopology B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _ hR.2
  have hmem : ((E.map 𝒳.val.val.p).map (BigFppfOver.forget B S hS)).presieve₀ ∈
      B.precoverage ((BigFppfOver.forget B S hS).obj (𝒳.val.val.p.obj x.obj)) :=
    ⟨_, rfl, hEcov⟩
  have hflat : ∀ i, flatObject B S hS 𝒳.val (E.X i) := fun i =>
    flatObject_of_flat B S hS 𝒳 (E.f i)
      (flat_and_locallyOfFinitePresentation_of_mem_precoverage B _ hmem _
        (Presieve.ofArrows.mk i)).1 x.property
  refine (topology B S hS 𝒳).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck (J := precoverage B S hS 𝒳)
      (R := (⟨E.I₀, fun i => ⟨E.X i, hflat i⟩, fun i => ObjectProperty.homMk (E.f i)⟩ :
        PreZeroHypercover.{u + 1} x).presieve₀) ⟨_, rfl, hEcov⟩)
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  obtain ⟨W, h, g, hg, hcomp⟩ := hEle _ _ (Presieve.ofArrows.mk i)
  obtain ⟨hg₀⟩ := hg
  rename_i y₀ g₀
  exact ⟨y₀, ObjectProperty.homMk h, g₀, hg₀,
    (objectProperty B S hS 𝒳).ι.map_injective (by simpa using hcomp)⟩

/-- **The two descriptions of the topology of the flat-fppf site agree.** The inherited topology
of the source's own definition and the topology generated by the inherited chosen covering
families are the same Grothendieck topology. -/
theorem inclusionTopology_eq_topology :
    inclusionTopology B S hS 𝒳 = topology B S hS 𝒳 :=
  le_antisymm (inclusionTopology_le_topology B S hS 𝒳)
    (topology_le_inclusionTopology B S hS 𝒳)

/-- **Continuity of the inclusion of the flat-fppf site (Stacks 0788 (2)), conditional on the
closure property.** This is the fppf case of Stacks 07AK with its closure hypothesis exposed; the
hypothesis is discharged in
`AlgebraicGeometry.Stack.FlatFppf.isContinuous_inclusion'`. -/
theorem isContinuous_inclusion (h : ClosedUnderFlatMorphisms B S hS 𝒳) :
    (objectProperty B S hS 𝒳).ι.IsContinuous (inclusionTopology B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p B.topology) :=
  isContinuous_ι_fppfTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _ h

/-- **Cocontinuity of the inclusion of the flat-fppf site (Stacks 0788 (2)), conditional on the
closure property.** The hypothesis is discharged in
`AlgebraicGeometry.Stack.FlatFppf.isCocontinuous_inclusion'`. -/
theorem isCocontinuous_inclusion (h : ClosedUnderFlatMorphisms B S hS 𝒳) :
    (objectProperty B S hS 𝒳).ι.IsCocontinuous (inclusionTopology B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p B.topology) :=
  isCocontinuous_ι_fppfTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _ h

/-- **Continuity of the inclusion of the flat-fppf site (Stacks 0788 (2)).** This is the fppf case
of Stacks 07AK, whose closure hypothesis is
`AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`. -/
@[stacks 0788 "the inclusion of the flat-fppf site is continuous"]
theorem isContinuous_inclusion' :
    (objectProperty B S hS 𝒳).ι.IsContinuous (inclusionTopology B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p B.topology) :=
  isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)

/-- **Cocontinuity of the inclusion of the flat-fppf site (Stacks 0788 (2)).** -/
@[stacks 0788 "the inclusion of the flat-fppf site is cocontinuous"]
theorem isCocontinuous_inclusion' :
    (objectProperty B S hS 𝒳).ι.IsCocontinuous (inclusionTopology B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p B.topology) :=
  isCocontinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)

/-- **Continuity of the inclusion of the flat-fppf site, for the chosen-family topology
(Stacks 0788 (2)).** The same assertion at
`AlgebraicGeometry.Stack.FlatFppf.topology` rather than at
`AlgebraicGeometry.Stack.FlatFppf.inclusionTopology`.

Continuity passes from a topology to any smaller one, because a sheaf for the larger topology is a
sheaf for the smaller, so this follows from
`AlgebraicGeometry.Stack.FlatFppf.isContinuous_inclusion'` and
`AlgebraicGeometry.Stack.FlatFppf.topology_le_inclusionTopology`. Cocontinuity does *not* pass in
that direction, which is why the two are recorded differently here. -/
@[stacks 0788 "continuity of the inclusion, read at the topologies"]
theorem isContinuous_inclusion_topology :
    (objectProperty B S hS 𝒳).ι.IsContinuous (topology B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p B.topology) where
  op_comp_isSheaf_of_types G :=
    Presieve.isSheaf_of_le _ (topology_le_inclusionTopology B S hS 𝒳)
      ((isContinuous_inclusion' B S hS 𝒳).op_comp_isSheaf_of_types G)

/-- **Cocontinuity of the inclusion of the flat-fppf site, for the chosen-family topology
(Stacks 0788 (2)).** The same assertion at `AlgebraicGeometry.Stack.FlatFppf.topology` rather than
at `AlgebraicGeometry.Stack.FlatFppf.inclusionTopology`.

Unlike continuity, cocontinuity does not transfer from a topology to a smaller one, so this needs
the equality `AlgebraicGeometry.Stack.FlatFppf.inclusionTopology_eq_topology` and not merely
`AlgebraicGeometry.Stack.FlatFppf.topology_le_inclusionTopology`. -/
@[stacks 0788 "cocontinuity of the inclusion, read at the topologies"]
theorem isCocontinuous_inclusion_topology :
    (objectProperty B S hS 𝒳).ι.IsCocontinuous (topology B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p B.topology) := by
  rw [← inclusionTopology_eq_topology B S hS 𝒳]
  exact isCocontinuous_inclusion' B S hS 𝒳

/-- **The morphism of topoi `g` of Stacks 0788 (2)(a)**:
`g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})`, with inverse image restriction along the inclusion of
the flat objects, pushforward its cocontinuous right adjoint, and left exactness of the inverse
image automatic. -/
@[stacks 0788 "the morphism of topoi induced by the inclusion"]
noncomputable def toposMorphism :
    MorphismOfTopoi
      (Sheaf (inclusionTopology B S hS 𝒳) (Type (u + 1)))
      (Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) (Type (u + 1))) := by
  haveI := isContinuous_inclusion' B S hS 𝒳
  haveI := isCocontinuous_inclusion' B S hS 𝒳
  exact
    { pushforward := (objectProperty B S hS 𝒳).ι.sheafPushforwardCocontinuous (Type (u + 1)) _ _
      inverseImage :=
        (objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous (Type (u + 1)) _ _
      adj := (objectProperty B S hS 𝒳).ι.sheafAdjunctionCocontinuous (Type (u + 1)) _ _
      preservesFiniteLimits := by infer_instance }

/-- **The morphism of topoi `g` of Stacks 0788 (2)(a), for the chosen-family topology**: the same
morphism of topoi as `AlgebraicGeometry.Stack.FlatFppf.toposMorphism`, transported along
`AlgebraicGeometry.Stack.FlatFppf.inclusionTopology_eq_topology`, so that its source is the topos
of sheaves for `AlgebraicGeometry.Stack.FlatFppf.topology`. No second construction is involved:
the two topologies are equal, and this is the one morphism of topoi read at the other
description. -/
@[stacks 0788 "that morphism of topoi, read at the topologies"]
noncomputable def toposMorphismTopology :
    MorphismOfTopoi
      (Sheaf (topology B S hS 𝒳) (Type (u + 1)))
      (Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) (Type (u + 1))) :=
  inclusionTopology_eq_topology B S hS 𝒳 ▸ toposMorphism B S hS 𝒳

/-! ### Lower shriek on sheaves of sets -/

section Sets

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology

/-- **The lower-shriek functor `g_!` of Stacks 0788 (2)(b)**, on sheaves of sets: the left Kan
extension along the inclusion of the flat objects, sheafified
(`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`).

No smallness assumption enters at this coefficient universe. The objects of the fppf site of `𝒳`
form a `Type (u + 1)` whose morphisms live in `Type u`, so the comma categories indexing the Kan
extension and the sheafification are `Type (u + 1)`-sized, and `Type (u + 1)` has the limits and
colimits of that size. -/
noncomputable abbrev setsShriek :
    Sheaf (topology B S hS 𝒳) (Type (u + 1)) ⥤
      Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback (objectProperty B S hS 𝒳).ι (Type (u + 1))
    (topology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)

/-- **Stacks 0788 (2)(b).** The inverse image of the morphism of topoi `g` of Stacks 0788 (2)(a)
has a left adjoint on sheaves of sets, namely `AlgebraicGeometry.Stack.FlatFppf.setsShriek`.

This is `CategoryTheory.Functor.sheafAdjunctionLowerShriek` (**Stacks 00XR** (2)) at the inclusion
of the flat objects, whose continuity is
`AlgebraicGeometry.Stack.FlatFppf.isContinuous_inclusion_topology`. The right-hand side is the
inverse image of `AlgebraicGeometry.Stack.FlatFppf.toposMorphismTopology`, restriction along the
inclusion. -/
@[stacks 0788 "the lower-shriek adjunction on sheaves of sets"]
noncomputable abbrev setsShriekAdjunction :
    setsShriek B S hS 𝒳 ⊣
      (objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous (Type (u + 1))
        (topology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology) :=
  (objectProperty B S hS 𝒳).ι.sheafAdjunctionLowerShriek (Type (u + 1)) (topology B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p B.topology)

/-- **Stacks 0788 (2)(c), the half about `g_!`.** The canonical map `F ⟶ g⁻¹g_!F` on sheaves of
sets — the unit of `AlgebraicGeometry.Stack.FlatFppf.setsShriekAdjunction` — is an isomorphism.

This is **Stacks 00XT** for a fully faithful, continuous and cocontinuous functor of sites, all
three of which hold for the inclusion of the flat objects at this topology. -/
@[stacks 0788 "the unit of the sets lower-shriek adjunction is invertible"]
instance isIso_setsShriekAdjunction_unit : IsIso (setsShriekAdjunction B S hS 𝒳).unit :=
  Functor.isIso_unit_of_sheafPushforwardContinuous (objectProperty B S hS 𝒳).ι (Type (u + 1))
    (topology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)
    (setsShriekAdjunction B S hS 𝒳)

end Sets

/-! ### Lower shriek on abelian sheaves

Stacks 0788 (2)(d) and (2)(e) are stated here **unconditionally**: essential smallness of the fppf
site of `𝒳` in the universe of its schemes is the instance
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack` of
`StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness`, and instance search supplies it.
They therefore carry the tag, one site each:
`AlgebraicGeometry.Stack.FlatFppf.abelianShriekAdjunction` for (2)(d) and
`AlgebraicGeometry.Stack.FlatFppf.isIso_abelianShriekAdjunction_unit` for (2)(e).
See the implementation notes above.
-/

section Abelian

universe v

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology

/-- An essentially small fppf site of an algebraic stack stays essentially small in any larger
coefficient universe: it is equivalent to its small model, which is small in every larger
universe. -/
theorem essentiallySmall_obj_coefficient : EssentiallySmall.{max u v} 𝒳.val.val.obj :=
  (essentiallySmall_congr (equivSmallModel.{u} 𝒳.val.val.obj)).mpr inferInstance

attribute [local instance] essentiallySmall_obj_coefficient

/-- The flat-fppf site of an algebraic stack is essentially small as soon as its fppf site is: it
is a full subcategory of it. -/
theorem essentiallySmall_flatFppf : EssentiallySmall.{max u v}
    (ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)) :=
  essentiallySmall_of_fully_faithful.{max u v} (objectProperty B S hS 𝒳).ι

attribute [local instance] essentiallySmall_flatFppf

/-- Abelian sheaves on the fppf site of an algebraic stack have a sheafification, in any
coefficient universe containing that of its schemes. -/
theorem hasSheafify_associatedTopology_ab :
    HasSheafify (associatedTopology B S hS 𝒳.val.val.p B.topology) Ab.{max u v} :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max u v} _ _

attribute [local instance] hasSheafify_associatedTopology_ab

/-- Restriction of abelian presheaves along the inclusion of the flat objects admits a left Kan
extension: the comma categories indexing it are essentially small, so the required colimits exist
in abelian groups. -/
theorem hasLeftKanExtension_inclusion_ab :
    ∀ F : (ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳))ᵒᵖ ⥤ Ab.{max u v},
      (objectProperty B S hS 𝒳).ι.op.HasLeftKanExtension F := fun F => by
  have : (objectProperty B S hS 𝒳).ι.op.HasPointwiseLeftKanExtension F := fun Y => by
    have := hasColimitsOfShape_of_essentiallySmall.{max u v}
      (CostructuredArrow (objectProperty B S hS 𝒳).ι.op Y) Ab.{max u v}
    infer_instance
  infer_instance

attribute [local instance] hasLeftKanExtension_inclusion_ab

/-- **The lower-shriek functor `g_!` of Stacks 0788 (2)(d)**, on abelian sheaves. -/
noncomputable abbrev abelianShriek :
    Sheaf (topology B S hS 𝒳) Ab.{max u v} ⥤
      Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) Ab.{max u v} :=
  Functor.sheafPullbackConstruction.sheafPullback (objectProperty B S hS 𝒳).ι Ab.{max u v}
    (topology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)

/-- **Stacks 0788 (2)(d).** Restriction of abelian sheaves along the inclusion of the flat
objects has a left adjoint, namely `AlgebraicGeometry.Stack.FlatFppf.abelianShriek`. -/
@[stacks 0788 "the lower-shriek adjunction on abelian sheaves"]
noncomputable abbrev abelianShriekAdjunction :
    abelianShriek.{u, w, v} B S hS 𝒳 ⊣
      (objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous Ab.{max u v}
        (topology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology) :=
  (objectProperty B S hS 𝒳).ι.sheafAdjunctionLowerShriek Ab.{max u v} (topology B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p B.topology)

/-- Restriction of abelian presheaves along the inclusion of the flat objects admits a pointwise
right Kan extension, by the same essential smallness that gives the left one. -/
theorem hasPointwiseRightKanExtension_inclusion_ab :
    ∀ F : (ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳))ᵒᵖ ⥤ Ab.{max u v},
      (objectProperty B S hS 𝒳).ι.op.HasPointwiseRightKanExtension F := fun _ Y => by
  have := hasLimitsOfShape_of_essentiallySmall.{max u v}
    (StructuredArrow Y (objectProperty B S hS 𝒳).ι.op) Ab.{max u v}
  infer_instance

attribute [local instance] hasPointwiseRightKanExtension_inclusion_ab

/-- **Stacks 0788 (2)(e)**: the canonical map `F ⟶ g⁻¹g_!F` on abelian sheaves — the unit of
`AlgebraicGeometry.Stack.FlatFppf.abelianShriekAdjunction` — is an isomorphism. This is
**Stacks 00XT** again, now at abelian coefficients. -/
@[stacks 0788 "the unit of the abelian lower-shriek adjunction is invertible"]
instance isIso_abelianShriekAdjunction_unit :
    IsIso (abelianShriekAdjunction.{u, w, v} B S hS 𝒳).unit :=
  Functor.isIso_unit_of_sheafPushforwardContinuous (objectProperty B S hS 𝒳).ι Ab.{max u v}
    (topology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)
    (abelianShriekAdjunction.{u, w, v} B S hS 𝒳)

end Abelian

/-! ### Abelian sheaves at the inherited topology, through Stacks 077I

The three functors `g⁻¹`, `g_*`, `g_!` and the two canonical maps of **Stacks 077I**, read at
`AlgebraicGeometry.Stack.FlatFppf.inclusionTopology` and at the single coefficient universe
`AbCat.{u, u + 1}`, through the general theory of
`StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekFullyFaithful`. The closure property is
carried as an explicit hypothesis here, which is the form the derived lower shriek of
**Stacks 07AS** consumes.
-/

section AbelianInclusionTopology

open Stacks.Sites.LowerShriek.FullyFaithful

variable (h : ClosedUnderFlatMorphisms B S hS 𝒳)

include h

/-- **The inverse image `g⁻¹` of Stacks 0788 (2)(a) on abelian sheaves, conditional on the
closure property**: restriction of an abelian sheaf on the fppf site of `𝒳` to the flat
objects. -/
noncomputable abbrev abelianInverseImage :
    Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) AbCat.{u, u + 1} ⥤
      Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1} :=
  haveI := isContinuous_inclusion B S hS 𝒳 h
  haveI := isCocontinuous_inclusion B S hS 𝒳 h
  gInv (objectProperty B S hS 𝒳).ι _ _

/-- **The direct image `g_*` of Stacks 0788 (2)(a) on abelian sheaves, conditional on the
closure property.** -/
noncomputable abbrev abelianPushforward :
    Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1} ⥤
      Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) AbCat.{u, u + 1} :=
  haveI := isContinuous_inclusion B S hS 𝒳 h
  haveI := isCocontinuous_inclusion B S hS 𝒳 h
  gStar (objectProperty B S hS 𝒳).ι _ _

/-- **The lower shriek `g_!` of Stacks 0788 (2)(b) on abelian sheaves, conditional on the
closure property**: the left adjoint of restriction, obtained from the continuous inclusion as a
left Kan extension followed by sheafification. -/
noncomputable abbrev abelianLowerShriek :
    Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1} ⥤
      Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) AbCat.{u, u + 1} :=
  haveI := isContinuous_inclusion B S hS 𝒳 h
  haveI := isCocontinuous_inclusion B S hS 𝒳 h
  gShriek (objectProperty B S hS 𝒳).ι _ _

/-- **The adjunction `g_! ⊣ g⁻¹` of Stacks 0788 (2)(b) on abelian sheaves.** -/
noncomputable abbrev abelianLowerShriekAdjunction :
    abelianLowerShriek B S hS 𝒳 h ⊣ abelianInverseImage B S hS 𝒳 h :=
  haveI := isContinuous_inclusion B S hS 𝒳 h
  haveI := isCocontinuous_inclusion B S hS 𝒳 h
  adjShriek (objectProperty B S hS 𝒳).ι _ _

/-- **The adjunction `g⁻¹ ⊣ g_*` of Stacks 0788 (2)(a) on abelian sheaves.** -/
noncomputable abbrev abelianPushforwardAdjunction :
    abelianInverseImage B S hS 𝒳 h ⊣ abelianPushforward B S hS 𝒳 h :=
  haveI := isContinuous_inclusion B S hS 𝒳 h
  haveI := isCocontinuous_inclusion B S hS 𝒳 h
  adjStar (objectProperty B S hS 𝒳).ι _ _

/-- **Stacks 077I for the flat-fppf inclusion.** The unit `F ⟶ g⁻¹ (g_! F)` of the adjunction
defining the lower shriek on abelian sheaves is an isomorphism: the inclusion is continuous,
cocontinuous and fully faithful, which is exactly the hypothesis of Stacks 077I. -/
theorem isIso_abelianLowerShriek_unit
    (F : Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1}) :
    IsIso ((abelianLowerShriekAdjunction B S hS 𝒳 h).unit.app F) := by
  have := isContinuous_inclusion B S hS 𝒳 h
  have := isCocontinuous_inclusion B S hS 𝒳 h
  exact stacks077I_unit_isIso (objectProperty B S hS 𝒳).ι _ _ F

/-- **Stacks 077I for the flat-fppf inclusion**, counit half: the counit `g⁻¹ (g_* F) ⟶ F` of
the adjunction of the morphism of topoi is an isomorphism. -/
theorem isIso_abelianPushforward_counit
    (F : Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1}) :
    IsIso ((abelianPushforwardAdjunction B S hS 𝒳 h).counit.app F) := by
  have := isContinuous_inclusion B S hS 𝒳 h
  have := isCocontinuous_inclusion B S hS 𝒳 h
  exact stacks077I_counit_isIso (objectProperty B S hS 𝒳).ι _ _ F

end AbelianInclusionTopology

end FlatFppf

add_to_stacks 0788 "flat_inclusion" CategoryTheory.ObjectProperty.fullyFaithfulι
add_to_sga "3 I 1.1.1" "Hom_C(X,Y) = Hom_D(X,Y)" CategoryTheory.ObjectProperty.fullyFaithfulι
add_to_sga "6 II 3.0" "more general" CategoryTheory.ObjectProperty.fullyFaithfulι

end AlgebraicGeometry.Stack

end
