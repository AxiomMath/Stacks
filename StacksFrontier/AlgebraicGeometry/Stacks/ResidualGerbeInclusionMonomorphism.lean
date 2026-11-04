module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangedFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordSingletonEtaleCoverUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothDiagramRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointResidualGerbeExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentationBootstrap
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStackFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeIsomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedAlgebraicStack

/-!
# The inclusion of a residual gerbe is a monomorphism

Let `𝒳` be an algebraic stack over `S`, let `x ∈ |𝒳|` and let `P` be an object property of `𝒳`
meeting the specification `AlgebraicGeometry.Stack.IsResidualGerbeAt` of **Stacks 06MT** — the
residual gerbe of `𝒳` at `x`. This file proves that the inclusion `𝒵_x ⟶ 𝒳` is **representable by
algebraic spaces** through a flat presentation of the gerbe, with nothing assumed. That the
inclusion is a **monomorphism** needs nothing about the gerbe: the inclusion of any algebraic full
subcategory is one, by
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion`, the
implication (2) ⟹ (1) of **Stacks 04ZZ** for a fully faithful 1-morphism.

A residual gerbe is *reduced, locally Noetherian and has exactly one point*, by the specification
of Stacks 06MT, so the implication (1) ⟹ (2) of **Stacks 06MP**
(`hasLocallyOfFinitePresentationFlatFieldCover_of_isReducedLocallyNoetherian`) gives it a
surjective, flat, locally finitely presented 1-morphism from the algebraic stack of the spectrum of
a field. That is a flat presentation of the subcategory by an object representable by an algebraic
space, and a flat presentation makes the inclusion representable: each 2-fibre product of the
inclusion with a scheme-valued point of `𝒳` is a stack in setoids, because the inclusion of a full
subcategory is faithful (**Stacks 05UI**), and it receives the base change of the presentation, so
the implication (1) ⟹ (3) of **Stacks 04SZ**
(`isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_baseChange`) represents it by an
algebraic space.

At a **finite type point** the residual gerbe exists, by **Stacks 06G3**
(`AlgebraicGeometry.Stack.isFiniteTypePoint_tfae_unconditional`), and if `𝒳` is DM then so is
`𝒵_x`, by **Stacks 06MZ** at the monomorphism of its inclusion. Reducedness, local Noetherianity
and the one-point space come with the residual gerbe, so `𝒵_x` satisfies the hypothesis
`AlgebraicGeometry.Stack.IsReducedLocallyNoetherianSingletonDM` of **Stacks 06N0**. Stacks 06N0
itself is `AlgebraicGeometry.Stack.hasSurjectiveEtaleFieldSpectrumCover_unconditional`, so there
are a field `k` and a 1-morphism `Spec k ⟶ 𝒳` which is **unramified** in the relative sense of
Properties of Stacks, Section **04XB**, with image `{x}`: the étale cover of the gerbe is
unramified by **Stacks 0CIW**, the inclusion is unramified because it is a locally-of-finite-type
monomorphism (**Stacks 05W6**), and **Stacks 045B** composes the two. This is the 1-morphism `x`
of the cartesian diagram `F = U ×_{𝒳, x} Spec(k)` in the proof of **Stacks 06N3**, and its
unramifiedness makes `F ⟶ U` unramified for every chart `U` of `𝒳`.

## Main results

* `isStackInSetoids_twoFibreProduct_fullSubcategoryBased`: the base change of the inclusion of an
  algebraic full subcategory along a scheme-valued point is a stack in setoids.
* `isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_flatPresentation` and
  `isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_fieldSpectrumCover`: the
  inclusion of an algebraic full subcategory with a flat presentation by an algebraic space — in
  particular one covered by the spectrum of a field, surjectively, flatly and of finite
  presentation — is representable by algebraic spaces.
* `hasLocallyOfFinitePresentationFlatFieldSpectrumCover_of_isResidualGerbeAt`: a residual gerbe
  has such a cover, by **Stacks 06MP**.
* `isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_isResidualGerbeAt`:
  representability at a residual gerbe, with nothing assumed.
* `isReducedLocallyNoetherianSingletonDM_of_isResidualGerbeAt`: the residual gerbe of a DM
  algebraic stack meets the hypothesis of **Stacks 06N0**.
* At a finite type point of a DM algebraic stack, the residual gerbe exists, its inclusion is a
  monomorphism locally of finite type, and the gerbe meets the hypothesis of **Stacks 06N0**.
* `exists_relativelyUnramified_fieldSpectrum_point_of_isFiniteTypePoint`: the unramified
  field-valued point at a finite type point, with nothing assumed.

## Implementation notes

`isStackInSetoids_twoFibreProduct_fullSubcategoryBased` and
`isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_fieldSpectrumCover` are
**not** the lemmas `isStackInSetoids_twoFibreProduct_localImage` and
`isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_localImage`, and neither pair
implies the other. Those apply *before* the subcategory is known to be an algebraic stack —
algebraicity is their consequence, through Stacks 05UM — so they supply the stack property of the
subcategory by hand, from `AlgebraicGeometry.Stack.isStack_localImageStack`, and they take the
flat presentation as three separate relative properties of a given factorization. The lemmas here
take algebraicity of the subcategory as a hypothesis, and take the presentation in the packaged
form of condition (2) of Stacks 06MP.

The conversions between the two renderings of a property of a 1-morphism — the smooth-diagram
tests of **Stacks 06PW**, **06Q2** and **04ZS** used for the 2-category of algebraic stacks, and
the relative property of **Stacks 03YK** used for representability — are **Stacks 06FM**
(`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some` followed by
`AlgebraicGeometry.Stack.hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram`) and **Stacks
04XI** (`AlgebraicGeometry.Stack.pointsMap_surjective_iff_isRelativelySurjective`) for
surjectivity. They need both source and target to be algebraic stacks, which is why the
algebraicity hypothesis is needed here.

The proof `hP` that the full subcategory is an algebraic stack appears in the statement of
`AlgebraicGeometry.Stack.IsResidualGerbeAt` under an existential quantifier as well as in
`AlgebraicGeometry.Stack.fullSubcategoryAlgebraicStack`; the two are interchangeable by
definitional proof irrelevance, so the clauses of `IsResidualGerbeAt` are used at the outer `hP`
without transport.

## References

* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 05UI](https://stacks.math.columbia.edu/tag/05UI)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 05W6](https://stacks.math.columbia.edu/tag/05W6)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06G3](https://stacks.math.columbia.edu/tag/06G3)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MW](https://stacks.math.columbia.edu/tag/06MW)
* [Stacks Project, Tag 06MZ](https://stacks.math.columbia.edu/tag/06MZ)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 0CIW](https://stacks.math.columbia.edu/tag/0CIW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.isFlat_isStableUnderBaseChange
  Space.isLocallyOfFinitePresentation_isStableUnderBaseChange
  Space.isLocallyOfFiniteType_isStableUnderBaseChange

section Representability

/-- A 1-morphism from a scheme-valued point to an algebraic stack is representable by algebraic
spaces. -/
private theorem isRepresentableByAlgebraicSpaces_of_schemeFibredCategory_source
    {𝒴 : AlgebraicStacks.{u, w} B S hS} (V : BigFppfOver B S hS)
    (g : schemeFibredCategory B S hS V ⟶ 𝒴.val) : IsRepresentableByAlgebraicSpaces B S hS g.hom :=
  isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒴.property
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V) g

/-- A property on every smooth diagram of a representable 1-morphism of algebraic stacks gives the
corresponding relative property. -/
private theorem hasRelativeProperty_of_hasPropertyOnEverySmoothDiagram
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    [(spaceProperty B S hS P).IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳.val ⟶ 𝒴.val)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (h : HasPropertyOnEverySmoothDiagram B S hS P f) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (spaceProperty B S hS P) f hf :=
  hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, u} B S hS P hP f hf
    ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP 𝒳.property 𝒴.property f).1 h)


/-- **The base change of the inclusion of an algebraic full subcategory along a scheme-valued
point is a stack in setoids.**

This is **Stacks 05UI**: the inclusion is faithful, the subcategory is a stack fibred in groupoids
because it is an algebraic stack, the category represented by an object of the site is a stack in
setoids, and `𝒳` is a stack. -/
theorem isStackInSetoids_twoFibreProduct_fullSubcategoryBased
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) (V : BigFppfOver B S hS)
    (y : (schemeFibredCategory B S hS V).val ⥤ᵇ 𝒳.val.val) :
    (twoFibreProduct B S hS 𝒳.val (fullSubcategoryAlgebraicStack 𝒳 P hP).val
        (schemeFibredCategory B S hS V)
        (fullSubcategoryBasedInclusion 𝒳 P) y).val.p.IsStackInSetoids
      (BigFppfOver.topology B S hS) := by
  obtain ⟨-, ⟨h𝒳stk, -⟩, -, -⟩ := 𝒳.property
  obtain ⟨-, ⟨hPstk, -⟩, -, -⟩ := id hP
  have hfaithP : P.ι.Faithful := ObjectProperty.faithful_ι P
  have : (fullSubcategoryBasedInclusion 𝒳 P).toFunctor.Faithful := hfaithP
  exact Functor.isStackInSetoids_twoFibreProduct (BigFppfOver.topology B S hS)
    hPstk (fullSubcategoryAlgebraicStack 𝒳 P hP).val.isFiberedInGroupoids
    (isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS
      (schemeFibredCategory B S hS V)
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V))
    h𝒳stk
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS
      (Bicategory.InducedBicategory.mkHom (fullSubcategoryBasedInclusion 𝒳 P) :
        (fullSubcategoryAlgebraicStack 𝒳 P hP).val ⟶ 𝒳.val))
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS
      (Bicategory.InducedBicategory.mkHom y : schemeFibredCategory B S hS V ⟶ 𝒳.val))

/-- **The inclusion of an algebraic full subcategory with a flat presentation by an algebraic
space is representable by algebraic spaces.**

By the pointwise criterion
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct` it is enough
that each 2-fibre product of the inclusion with a scheme-valued point of `𝒳` be representable by
an algebraic space. That 2-fibre product is a stack in setoids
(`AlgebraicGeometry.Stack.isStackInSetoids_twoFibreProduct_fullSubcategoryBased`) receiving the
base change of the given presentation, so the engine of the implication (1) ⟹ (3) of
**Stacks 04SZ**,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_baseChange`,
applies. -/
theorem isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_flatPresentation
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    {𝒬 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (v : 𝒬 ⟶ (fullSubcategoryAlgebraicStack 𝒳 P hP).val)
    (h𝒬 : IsRepresentableByAlgebraicSpace B S hS 𝒬)
    (hv : IsRepresentableByAlgebraicSpaces B S hS v.hom)
    (hsurj : RelativeProperty B S hS (Space.surjectiveMorphismProperty B S hS) v)
    (hflat : RelativeProperty B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom) v)
    (hlfp : RelativeProperty B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) v) :
    IsRepresentableByAlgebraicSpaces B S hS (fullSubcategoryBasedInclusion 𝒳 P) := by
  refine isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct B S hS 𝒳.val
    (fullSubcategoryAlgebraicStack 𝒳 P hP).val (fullSubcategoryBasedInclusion 𝒳 P) ?_
  intro V y
  have hy : IsRepresentableByAlgebraicSpaces B S hS y :=
    isRepresentableByAlgebraicSpaces_of_schemeFibredCategory_source B S hS V
      (Bicategory.InducedBicategory.mkHom y : schemeFibredCategory B S hS V ⟶ 𝒳.val)
  refine (isRepresentableByAlgebraicSpace_twoFibreProduct_swap_iff B S hS 𝒳.val
    (fullSubcategoryAlgebraicStack 𝒳 P hP).val (schemeFibredCategory B S hS V)
    (fullSubcategoryBasedInclusion 𝒳 P) y).1 ?_
  exact isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_baseChange B S hS v
    (Bicategory.InducedBicategory.mkHom
      (twoFibreProductFst B S hS 𝒳.val (fullSubcategoryAlgebraicStack 𝒳 P hP).val
        (schemeFibredCategory B S hS V) (fullSubcategoryBasedInclusion 𝒳 P) y))
    (isStackInSetoids_twoFibreProduct_fullSubcategoryBased B S hS 𝒳 P hP V y)
    h𝒬 hv hsurj hflat hlfp
    (isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳.val
      (fullSubcategoryAlgebraicStack 𝒳 P hP).val (schemeFibredCategory B S hS V)
      (fullSubcategoryBasedInclusion 𝒳 P) y hy)

/-- **The inclusion of an algebraic full subcategory covered by the spectrum of a field is
representable by algebraic spaces.** Condition (2) of **Stacks 06MP** on the subcategory — a
surjective, flat, locally finitely presented 1-morphism from the algebraic stack of a field
spectrum — is a flat presentation of it by an object representable by an algebraic space, so
`isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_flatPresentation` applies.

The cover's three properties are the smooth-diagram ones of **Stacks 06PW**, **06Q2** part (1) and
**04ZS**; **Stacks 06FM** and **Stacks 04XI** turn them into the relative properties of
**Stacks 03YK**. -/
theorem isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_fieldSpectrumCover
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hcov : HasLocallyOfFinitePresentationFlatFieldSpectrumCover.{u, w} B S hS
      (fullSubcategoryAlgebraicStack 𝒳 P hP)) :
    IsRepresentableByAlgebraicSpaces B S hS (fullSubcategoryBasedInclusion 𝒳 P) := by
  obtain ⟨F, f, hlfp, hsurj, hflat⟩ := hcov
  have hfrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_schemeFibredCategory_source B S hS F.base f.hom
  refine isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_flatPresentation
    B S hS 𝒳 P hP f.hom
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS F.base) hfrep ?_ ?_ ?_
  · exact (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS f hfrep).mp hsurj
  · exact hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) f.hom hfrep
      ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).1 hflat)
  · exact hasRelativeProperty_of_hasPropertyOnEverySmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) f.hom hfrep hlfp

end Representability

section ResidualGerbe


/-- **A residual gerbe is covered by the spectrum of a field, surjectively, flatly and of finite
presentation.** It is reduced, locally Noetherian and has exactly one point, by the specification
`AlgebraicGeometry.Stack.IsResidualGerbeAt` of **Stacks 06MT** — that is condition (1) of
**Stacks 06MP**, as
`AlgebraicGeometry.Stack.isReducedLocallyNoetherianWithUniquePoint_of_isResidualGerbeAt` records —
so this is the implication (1) ⟹ (2) of Stacks 06MP. -/
theorem hasLocallyOfFinitePresentationFlatFieldSpectrumCover_of_isResidualGerbeAt
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hgerbe : IsResidualGerbeAt B S hS 𝒳 x P) :
    HasLocallyOfFinitePresentationFlatFieldSpectrumCover.{u, w} B S hS
      (fullSubcategoryAlgebraicStack 𝒳 P hP) :=
  hasLocallyOfFinitePresentationFlatFieldCover_of_isReducedLocallyNoetherian.{u, w} B S hS
    (fullSubcategoryAlgebraicStack 𝒳 P hP)
    (isReducedLocallyNoetherianWithUniquePoint_of_isResidualGerbeAt B S hS 𝒳 x P hgerbe)

/-- **The inclusion of a residual gerbe is representable by algebraic spaces.** The gerbe is
covered by the spectrum of a field flatly, surjectively and of finite presentation, by
**Stacks 06MP**, and
`isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_fieldSpectrumCover` turns that
presentation into representability. Nothing is assumed; in particular the implication (2) ⟹ (3) of
**Stacks 04Y5** is not used. -/
theorem isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_isResidualGerbeAt
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hgerbe : IsResidualGerbeAt B S hS 𝒳 x P) :
    IsRepresentableByAlgebraicSpaces B S hS (fullSubcategoryBasedInclusion 𝒳 P) :=
  isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_fieldSpectrumCover
    B S hS 𝒳 P hP
    (hasLocallyOfFinitePresentationFlatFieldSpectrumCover_of_isResidualGerbeAt
      B S hS 𝒳 x P hP hgerbe)

/-- **The residual gerbe of a DM algebraic stack meets the hypothesis of Stacks 06N0.** It is
reduced, locally Noetherian and has exactly one point by the specification of **Stacks 06MT**
(`AlgebraicGeometry.Stack.isReducedLocallyNoetherianWithUniquePoint_of_isResidualGerbeAt`), and
it is DM by **Stacks 06MZ** at the monomorphism
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion`. -/
theorem isReducedLocallyNoetherianSingletonDM_of_isResidualGerbeAt
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (h𝒳 : AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳)
    (hgerbe : IsResidualGerbeAt B S hS 𝒳 x P) :
    IsReducedLocallyNoetherianSingletonDM.{u, w} B S hS hZ
      (fullSubcategoryAlgebraicStack 𝒳 P hP) := by
  obtain ⟨⟨hred, hne, hsub⟩, hnoeth⟩ :=
    isReducedLocallyNoetherianWithUniquePoint_of_isResidualGerbeAt B S hS 𝒳 x P hgerbe
  exact ⟨AlgebraicStacks.isAbsolutelyDM_of_isMonomorphism.{u, w} B S hS hZ
      (fullSubcategoryInclusion 𝒳 P hP)
      (AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion B S hS 𝒳 P hP) h𝒳,
    hnoeth, hred, hne, hsub⟩

end ResidualGerbe

section FiniteTypePoint

/-- **The first two steps of the proof of Stacks 06N3.** At a finite type point `x` of a DM
algebraic stack `𝒳` the residual gerbe `𝒵_x` exists, its inclusion into `𝒳` is locally of finite
type and a monomorphism, and `𝒵_x` is a reduced, locally Noetherian, one-point DM algebraic stack —
which is exactly the hypothesis of **Stacks 06N0**.

Existence and local finite type are the implication (1) ⟹ (3) of **Stacks 06G3**,
`AlgebraicGeometry.Stack.existsLocallyOfFiniteTypeResidualGerbe`; monomorphy is
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion`; and the DM
condition on `𝒵_x` is **Stacks 06MZ** at that monomorphism. -/
theorem
  exists_isResidualGerbeAt_isMonomorphism_isReducedLocallyNoetherianSingletonDM_of_isFiniteTypePoint
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) :
    ∃ (P : ObjectProperty 𝒳.val.val.obj)
      (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)),
      IsResidualGerbeAt B S hS 𝒳 x P ∧
        AlgebraicStacks.IsLocallyOfFiniteType B S hS (fullSubcategoryInclusion 𝒳 P hP) ∧
          AlgebraicStacks.IsMonomorphism B S hS (fullSubcategoryInclusion 𝒳 P hP) ∧
            IsReducedLocallyNoetherianSingletonDM.{u, w} B S hS hZ
              (fullSubcategoryAlgebraicStack 𝒳 P hP) := by
  obtain ⟨P, hP, hgerbe, hlft⟩ := existsLocallyOfFiniteTypeResidualGerbe.{u, w} B S hS 𝒳 x hx
  exact ⟨P, hP, hgerbe, hlft,
    AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion B S hS 𝒳 P hP,
    isReducedLocallyNoetherianSingletonDM_of_isResidualGerbeAt B S hS hZ 𝒳 x P hP h𝒳 hgerbe⟩

/-- **The unramified field-valued point of Stacks 06N3.** At a finite type
point `x` of a DM algebraic stack there are a field spectrum `Spec k` and a 1-morphism
`u : Spec k ⟶ 𝒳` whose image on points is `{x}` and which is unramified in the relative sense of
Properties of Stacks, Section **04XB** — so that `U ×_{𝒳, u} Spec k ⟶ U` is unramified for every
chart `U` of `𝒳`.

The source's `u` is the composite `Spec k ⟶ 𝒵_x ⟶ 𝒳` of the surjective étale cover of the
residual gerbe that **Stacks 06N0** produces, which is
`AlgebraicGeometry.Stack.hasSurjectiveEtaleFieldSpectrumCover_unconditional`, with the
inclusion of the gerbe. The cover is unramified by **Stacks 0CIW** and the inclusion because it is
a locally-of-finite-type monomorphism (**Stacks 05W6**,
`AlgebraicGeometry.Space.isUnramified_of_isLocallyOfFiniteType_of_mono`); **Stacks 045B** composes
them. Local finite type of the composite is part of unramifiedness and is not stated separately. -/
theorem exists_relativelyUnramified_fieldSpectrum_point_of_isFiniteTypePoint
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) :
    ∃ (F : FieldSpectrum B S hS) (u : schemeStack.{u, w} B S hS F.base ⟶ 𝒳),
      RelativeProperty B S hS (Space.unramifiedMorphismProperty B S hS) u.hom ∧
        Set.range (AlgebraicStacks.pointsMap B S hS u) = {x} := by
  have : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u + 1} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  let : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  obtain ⟨P, hP, hgerbe, hlft, hmono, hdm⟩ :=
  exists_isResidualGerbeAt_isMonomorphism_isReducedLocallyNoetherianSingletonDM_of_isFiniteTypePoint
      B S hS hZ 𝒳 h𝒳 x hx
  obtain ⟨-, hP', -, -, z₀, huniq, hz₀x⟩ := id hgerbe
  obtain ⟨F, z, hzsurj, hzetale⟩ :=
    hasSurjectiveEtaleFieldSpectrumCover_unconditional.{u, w} B S hS hZ
      (fullSubcategoryAlgebraicStack 𝒳 P hP) hdm
  have hzrep : IsRepresentableByAlgebraicSpaces B S hS z.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_schemeFibredCategory_source B S hS F.base z.hom
  have hzunr : RelativeProperty B S hS (Space.unramifiedMorphismProperty B S hS) z.hom :=
    hasRelativeProperty_unramified_of_isUnramified B S hS z hzrep
      (isUnramified_of_isEtale B S hS hzetale)
  have hιlft : RelativeProperty B S hS (Space.locallyOfFiniteTypeProperty B S hS)
      (fullSubcategoryInclusion 𝒳 P hP).hom :=
    hasRelativeProperty_of_hasPropertyOnEverySmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (fullSubcategoryInclusion 𝒳 P hP).hom hmono.1 hlft
  have hιunr : RelativeProperty B S hS (Space.unramifiedMorphismProperty B S hS)
      (fullSubcategoryInclusion 𝒳 P hP).hom := by
    intro U y hy G hG he
    exact Space.isUnramified_of_isLocallyOfFiniteType_of_mono B S hS _
      (hιlft U y hy G hG he)
      ((Space.mono_hom_iff_mono B S hS _).2 (hmono.2 U y hy G hG he))
  have hrangeι : Set.range (AlgebraicStacks.pointsMap B S hS
      (fullSubcategoryInclusion 𝒳 P hP)) = {x} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨z₀, hz₀x⟩, ?_⟩
    rintro - ⟨a, rfl⟩
    rw [huniq a]
    exact hz₀x
  refine ⟨F, z ≫ fullSubcategoryInclusion 𝒳 P hP,
    hasRelativeProperty_comp.{u, u, u + 1, u + 1} B S hS
      (Space.unramifiedMorphismProperty B S hS) z.hom
      (fullSubcategoryInclusion 𝒳 P hP).hom hzrep hmono.1 hzunr hιunr, ?_⟩
  calc Set.range (AlgebraicStacks.pointsMap B S hS (z ≫ fullSubcategoryInclusion 𝒳 P hP))
      = Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hP) ∘
          AlgebraicStacks.pointsMap B S hS z) := by rw [AlgebraicStacks.pointsMap_comp]
    _ = Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hP)) :=
        hzsurj.range_comp _
    _ = {x} := hrangeι

end FiniteTypePoint

end AlgebraicGeometry.Stack

end
