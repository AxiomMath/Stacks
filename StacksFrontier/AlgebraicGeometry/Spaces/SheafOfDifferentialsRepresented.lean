module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentialsIso
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.CategoryTheory.Sites.YonedaRepresentableMorphism

/-!
# The sheaf of differentials of a morphism of represented algebraic spaces

Let `α : U ⟶ V` be a morphism of the big fppf site over a scheme `S`, and let
`ψ = schemeSpaceMap α : yoneda.obj U ⟶ yoneda.obj V` be the morphism of algebraic spaces it
represents.  This module compares the spaces-level sheaf of differentials `Ω_{ψ}` of Stacks 04CT
with the small-étale module `(Ω_{U/V})^a` associated to the Zariski sheaf of relative
differentials of the morphism of schemes underlying `α`.

Both objects corepresent a class of derivations of the structure sheaf of the small étale site:
`Ω_{ψ}` the `ψ♯`-derivations (`AlgebraicGeometry.Space.universalDerivation_isUniversal`), and
`(Ω_{U/V})^a` the derivations annihilating the functions pulled back from an open of `V`
(Stacks 04CS, `AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedDerivation`).  The
comparison
is therefore a matter of matching the two classes, and the matching is the content of this file:
a derivation of `𝒪` on the small étale site of a represented algebraic space annihilates the
image of `ψ♯` exactly when it annihilates every *chartwise pullback of a regular function* from
the target.

## Main definitions

* `AlgebraicGeometry.Space.representedModuleSiteEquivalence` is the equivalence of the module
  categories of the two small étale sites, and
  `AlgebraicGeometry.Space.representedChartBase` is the structure morphism of an étale chart of
  a represented algebraic space, read as a morphism of the big fppf site over `S`.
* `AlgebraicGeometry.Space.representedOpenChart` reads an open of the scheme underlying `U` as
  an étale chart of `yoneda.obj U`, and
  `AlgebraicGeometry.Space.representedOpenChartDiagram` is the diagram of charts an open of the
  target and its preimage make up.
* `AlgebraicGeometry.Space.representedUniversalDerivation` is the canonical derivation `d^a` of
  Stacks 04CS read on the small étale site of the represented algebraic space, as a
  `ψ`-derivation, and `AlgebraicGeometry.Space.representedDifferentialsComparison` is the
  comparison map `(Ω_{U/V})^a ⟶ Ω_{ψ}` it produces.
* `AlgebraicGeometry.Space.sheafOfDifferentialsRepresentedIso` is **Stacks 04CS for a morphism
  of represented algebraic spaces**: the isomorphism `Ω_{ψ} ≅ (Ω_{U/V})^a`.

## Main results

* `AlgebraicGeometry.Space.isIso_representedDifferentialsComparison`: **the comparison map is an
  isomorphism.**  This is the deliverable: the canonical derivation `d^a` is a `ψ`-derivation
  and the universal `ψ`-derivation annihilates the functions pulled back from an open of the
  target, so the two corepresented classes of derivations coincide.
* `AlgebraicGeometry.Space.representedUniversalDerivation_d` and
  `AlgebraicGeometry.Space.restrictedUniversalDerivation_pullbackSection`: the two halves of
  that coincidence.
* `AlgebraicGeometry.Space.isZero_representedAssociatedModule_iff`: the comparison functor
  detects the zero object at a quasi-coherent module.
* `AlgebraicGeometry.Space.structureSharpInverseImageSet_comp_eq_of_chartPullback` and
  `AlgebraicGeometry.Space.chartPullback_eq_of_structureSharpInverseImageSet_comp_eq`: **two
  morphisms out of `𝒪_X` agree after `f♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` if and only if they agree on every
  chartwise pullback of a regular function.**  This is the translation between the two
  descriptions of a relative derivation, in both directions.
* `AlgebraicGeometry.Space.chartBaseChangeMap_comp_representedChartBase`: the square of a chart
  index over a morphism of represented algebraic spaces commutes already in the big fppf site.
* `AlgebraicGeometry.Space.associatedDerivation_chartPullback`: **the canonical derivation `d^a`
  of Stacks 04CS annihilates every chartwise pullback of a regular function from the target.**

## Implementation notes

**Why `representedModuleSiteEquivalence` is built here rather than reused.**
`AlgebraicGeometry.Space.representedModuleEquivalence`
(`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartSchemeModuleComparison.lean:189`) is the same
construction, universe-polymorphic in the module universe, and reusing it would be the right
thing.  It cannot be imported here: `AffineChartSchemeModuleComparison` drags
`ChartSpaceGlobalPresentation` into this file's import closure, and that makes
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningFormallyEtale.lean:283` fail with
`stuck at solving universe constraint u + 1 =?= max (u + 1) ?u` while unifying
`Abelian (Modules …)` with `Abelian.{max (u + 1) ?u, …} (SheafOfModules.{max (u + 1) u ?u, …} …)`.
So the two constructions are deliberately kept apart until that constraint is fixed at its
source; neither is to be deleted in favour of the other meanwhile.

The sections of an inverse image `f^{-1}𝒪_Y` are not described by a formula anywhere in this
development, so the vanishing of a derivation on them is never checked sectionwise.  It is
checked in the direct-image form of the structure map, where
`AlgebraicGeometry.Space.moduleChartProjection_ext` presents the sections over an étale chart
`V` of `Y` as a limit over the étale charts of `X` above `X ×_Y V`, and
`AlgebraicGeometry.Space.moduleChartProjection_app_structureSharp` computes the chart projection
of `f♯` as `AlgebraicGeometry.Space.chartPullback`; the two forms of the structure map are
matched by `AlgebraicGeometry.Space.structureSharpInverseImage_of_structureSharpSetComp` and
`AlgebraicGeometry.Space.structureSharpSetComp_of_structureSharpInverseImage`.

This pin elaborates with strict transparency, and the terms of the small étale ringed site are
large.  Two consequences shape the statements below.  First, the naturality of a chart
projection is quoted through `Stacks.Sites.natTrans_app_apply`, an abstract restatement of
`CategoryTheory.NatTrans.naturality_apply`: applying the Mathlib lemma directly at the small
étale site is a deterministic `whnf` timeout, while applying the abstract one is immediate.
Second, `AlgebraicGeometry.Space.representedChartBase` exists so that the structure morphism of
a chart carries the type `AlgebraicGeometry.Space.chartBaseChangeMap` composes with; the Yoneda
element `yonedaEquiv V.1.hom` has a definitionally equal but syntactically different type, which
`rw` rejects.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map of a
  morphism of algebraic spaces in its two forms.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the chartwise
  description of the direct image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite

universe u v₁ v₂ u₁ u₂

namespace Stacks.Sites

/-- Naturality of a natural transformation of functors with values in types, on an element.

This is `CategoryTheory.NatTrans.naturality_apply` restated without the concrete-category
coercions; it is quoted rather than used directly because the Mathlib statement does not
elaborate at the small étale ringed site within the heartbeat budget. -/
theorem natTrans_app_apply {C : Type u₁} [Category.{v₁} C] {F G : C ⥤ Type u}
    (φ : F ⟶ G) {A E : C} (δ : A ⟶ E) (x : F.obj A) :
    φ.app E (F.map δ x) = G.map δ (φ.app A x) :=
  NatTrans.naturality_apply φ δ x

/-- Two equal morphisms of sheaves of types agree on sections. -/
theorem sheafHom_congr_app {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {A E : CategoryTheory.Sheaf J (Type u)} {m m' : A ⟶ E} (hm : m = m') (Z : Cᵒᵖ)
    (b : A.obj.obj Z) : m.hom.app Z b = m'.hom.app Z b := by rw [hm]

end Stacks.Sites

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  {R : Dᵒᵖ ⥤ CommRingCat.{u}} {M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
  {Base₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {φ₀ : Base₀ ⟶ R}

/-- **A derivation of a presheaf of modules, read on the restriction along a functor, over an
arbitrary base.**  The underlying additive map, the Leibniz rule and the compatibility with
restriction are those of the given derivation; the vanishing on the new base is the hypothesis.

The restriction is `PresheafOfModules.pushforward` along the identity comparison of the
coefficient rings, which is the shape in which a transport along an equivalence of sites that
matches the two structure sheaves appears. -/
noncomputable def Derivation.pushforwardOfId (d : PresheafOfModulesOfCommRing.Derivation' M φ₀)
    {Base : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : Base ⟶ F.op ⋙ R)
    (hφ : ∀ (X : Cᵒᵖ) (a : Base.obj X),
      d.d (X := F.op.obj X) ((φ.app X).hom a) = 0) :
    PresheafOfModulesOfCommRing.Derivation' ((PresheafOfModules.pushforward
        (𝟙 ((F.op ⋙ R) ⋙ forget₂ CommRingCat.{u} RingCat.{u}))).obj M) φ where
  d {X} := d.d (X := F.op.obj X)
  d_mul {_X} a b := d.d_mul a b
  d_map {_X _Y} g x := d.d_map (F.op.map g) x
  d_app {X} a := hφ X a

end PresheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The equivalence of module categories of a represented algebraic space -/

/-- The first coherence identity of the two structure-sheaf comparisons of the equivalence of
small étale sites: both comparisons are identities and the counit of the equivalence does not
move the underlying scheme of an object. -/
theorem representedStructureMap_counit_coherence (C : BigFppfOver B S hS) :
    Functor.whiskerRight (NatTrans.op (representedSmallEtaleEquivalence B S hS C).counit)
        (AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj =
      (representedStructureMapInverse B S hS C).hom ≫
        (representedSmallEtaleEquivalence B S hS C).inverse.op.whiskerLeft
          (representedStructureMap B S hS C).hom := by
  ext : 2
  exact rfl

/-- The second coherence identity of the two structure-sheaf comparisons of the equivalence of
small étale sites. -/
theorem representedStructureMap_unit_coherence (C : BigFppfOver B S hS) :
    (representedStructureMap B S hS C).hom ≫
        (representedSmallEtaleEquivalence B S hS C).functor.op.whiskerLeft
          (representedStructureMapInverse B S hS C).hom ≫
        Functor.whiskerRight (NatTrans.op (representedSmallEtaleEquivalence B S hS C).unit)
          (ringStructureSheaf B S hS (yoneda.obj C)).obj =
      𝟙 (ringStructureSheaf B S hS (yoneda.obj C)).obj := by
  ext : 2
  exact rfl

/-- **The modules on the small étale site of a represented algebraic space are the modules on
the small étale site of the representing scheme.**  The equivalence of sites matches the two
structure sheaves on the nose, so the two transports of modules along it,
`AlgebraicGeometry.Space.representedModulePushforward` and
`AlgebraicGeometry.Space.representedModuleRestriction`, are mutually inverse. -/
noncomputable def representedModuleSiteEquivalence (C : BigFppfOver B S hS) :
    SheafOfModules.{u} (AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj C) C.left.property) ≌
      SheafOfModules.{u} (ringStructureSheaf B S hS (yoneda.obj C)) :=
  SheafOfModules.pushforwardPushforwardEquivalence
    (representedSmallEtaleEquivalence B S hS C)
    (representedStructureMap B S hS C) (representedStructureMapInverse B S hS C)
    (representedStructureMap_counit_coherence B S hS C)
    (representedStructureMap_unit_coherence B S hS C)

/-- The functor of `AlgebraicGeometry.Space.representedModuleSiteEquivalence` is
`AlgebraicGeometry.Space.representedModulePushforward`. -/
theorem representedModuleSiteEquivalence_functor (C : BigFppfOver B S hS) :
    (representedModuleSiteEquivalence B S hS C).functor =
      representedModulePushforward B S hS C :=
  rfl

/-- The inverse of `AlgebraicGeometry.Space.representedModuleSiteEquivalence` is
`AlgebraicGeometry.Space.representedModuleRestriction`. -/
theorem representedModuleSiteEquivalence_inverse (C : BigFppfOver B S hS) :
    (representedModuleSiteEquivalence B S hS C).inverse =
      representedModuleRestriction B S hS C :=
  rfl

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The two descriptions of a relative derivation -/

/-- A chart projection of the structure map followed by a direct image is the morphism applied
to the chartwise pullback of regular functions. -/
theorem moduleChartProjection_app_structureSharpSet (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    {E : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (δ : structureSetSheaf B S hS X ⟶ E)
    (b : (structureSetSheaf B S hS Y).obj.obj (op V))
    (x : (smallEtaleDirectImage B S hS f ⋙
      sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj
        (structureSetSheaf B S hS X))
    (hx : (moduleChartProjection B S hS f V j).app (structureSetSheaf B S hS X) x =
      chartPullback B S hS f V j b) :
    (moduleChartProjection B S hS f V j).app E
        ((smallEtaleDirectImage B S hS f ⋙
            sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).map δ x) =
      δ.hom.app j.right (chartPullback B S hS f V j b) :=
  Eq.trans (Stacks.Sites.natTrans_app_apply (moduleChartProjection B S hS f V j) δ x)
    (congrArg (δ.hom.app j.right) hx)

/-- **Two morphisms out of `𝒪_X` agree after `f♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` as soon as they agree on
every chartwise pullback of a regular function.**

The sections of the direct image over an étale chart `V` of `Y` are a limit over the étale
charts of `X` above `X ×_Y V`, and the chart projection of `f♯` is pullback of regular
functions along the induced morphism of charts; so the hypothesis gives the identity in the
direct-image form of the structure map, which
`AlgebraicGeometry.Space.structureSharpInverseImage_of_structureSharpSetComp` carries back to
the inverse-image form. -/
theorem structureSharpInverseImageSet_comp_eq_of_chartPullback (f : X ⟶ Y)
    {E : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (δ ε : structureSetSheaf B S hS X ⟶ E)
    (h : ∀ (V : SmallEtale B S hS Y.1)
      (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
      (b : (structureSetSheaf B S hS Y).obj.obj (op V)),
      δ.hom.app j.right (chartPullback B S hS f V j b) =
        ε.hom.app j.right (chartPullback B S hS f V j b)) :
    structureSharpInverseImageSet B S hS f ≫ δ =
      structureSharpInverseImageSet B S hS f ≫ ε := by
  refine structureSharpInverseImage_of_structureSharpSetComp B S hS f δ ε ?_
  refine hom_ext_sections (fun W b ↦ ?_)
  obtain ⟨V⟩ := W
  refine moduleChartProjection_ext B S hS f V E (fun j ↦ ?_)
  refine Eq.trans (moduleChartProjection_app_structureSharpSet B S hS f V j δ b _
    (moduleChartProjection_app_structureSharp B S hS f V j b)) ?_
  exact Eq.trans (h V j b) (moduleChartProjection_app_structureSharpSet B S hS f V j ε b _
    (moduleChartProjection_app_structureSharp B S hS f V j b)).symm

/-- **Two morphisms out of `𝒪_X` which agree after `f♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` agree on every
chartwise pullback of a regular function.**  This is the converse of
`AlgebraicGeometry.Space.structureSharpInverseImageSet_comp_eq_of_chartPullback`, obtained from
the same two computations read in the other direction. -/
theorem chartPullback_eq_of_structureSharpInverseImageSet_comp_eq (f : X ⟶ Y)
    {E : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (δ ε : structureSetSheaf B S hS X ⟶ E)
    (h : structureSharpInverseImageSet B S hS f ≫ δ =
      structureSharpInverseImageSet B S hS f ≫ ε)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (b : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    δ.hom.app j.right (chartPullback B S hS f V j b) =
      ε.hom.app j.right (chartPullback B S hS f V j b) := by
  have hdi := structureSharpSetComp_of_structureSharpInverseImage B S hS f δ ε h
  have hb : (smallEtaleDirectImage B S hS f ⋙
        sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).map δ
        ((structureSharpSet B S hS f).hom.app (op V) b) =
      (smallEtaleDirectImage B S hS f ⋙
        sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).map ε
        ((structureSharpSet B S hS f).hom.app (op V) b) :=
    Stacks.Sites.sheafHom_congr_app hdi (op V) b
  refine Eq.trans (moduleChartProjection_app_structureSharpSet B S hS f V j δ b _
    (moduleChartProjection_app_structureSharp B S hS f V j b)).symm ?_
  exact Eq.trans (congrArg ((moduleChartProjection B S hS f V j).app E) hb)
    (moduleChartProjection_app_structureSharpSet B S hS f V j ε b _
      (moduleChartProjection_app_structureSharp B S hS f V j b))

/-! ### Charts of a represented algebraic space -/

/-- The structure morphism of an étale chart of a represented algebraic space, read as a
morphism of the big fppf site over `S`. -/
noncomputable def representedChartBase (C : BigFppfOver B S hS)
    (V : SmallEtale B S hS (schemeSpace C).1) :
    (SmallEtale.toOver B S hS (schemeSpace C).1).obj V ⟶ C :=
  yonedaEquiv V.1.hom

/-- The Yoneda morphism of the structure morphism of a chart is the chart itself. -/
theorem yoneda_map_representedChartBase (C : BigFppfOver B S hS)
    (V : SmallEtale B S hS (schemeSpace C).1) :
    yoneda.map (representedChartBase B S hS C V) = V.1.hom :=
  CategoryTheory.yoneda_map_yonedaEquiv V.1.hom

/-- The structure morphism of a chart of a represented algebraic space is étale on underlying
schemes: the chart is an object of the small étale site of the representing scheme, under
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`. -/
instance etale_toScheme_representedChartBase (C : BigFppfOver B S hS)
    (V : SmallEtale B S hS (schemeSpace C).1) :
    Etale ((BigFppfOver.toScheme B S hS).map (representedChartBase B S hS C V)) :=
  AlgebraicGeometry.SmallEtale.etale_objHom (associatedBigEtaleSite B)
    C.left.property ((representedSmallEtaleEquivalence B S hS C).functor.obj V)

variable {U' V' : BigFppfOver B S hS} (α : U' ⟶ V')

/-- **The square of a chart index over a morphism of represented algebraic spaces commutes in
the big fppf site.**  Over a represented algebraic space a chart and its structure morphism are
a morphism of the big fppf site, and the commuting triangle of
`AlgebraicGeometry.Space.chartDiagramOfIndex` is the Yoneda image of this square. -/
theorem chartBaseChangeMap_comp_representedChartBase
    (V : SmallEtale B S hS (schemeSpace V').1)
    (j : StructuredArrow (op (chartBaseChange B S hS (schemeSpaceMap α) V))
      (comparisonFunctor B S hS (schemeSpace U')).op) :
    chartBaseChangeMap B S hS (schemeSpaceMap α) V j ≫ representedChartBase B S hS V' V =
      representedChartBase B S hS U' j.right.unop ≫ α := by
  refine yoneda.map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, yoneda_map_representedChartBase,
    yoneda_map_representedChartBase]
  exact ((chartDiagramOfIndex B S hS (schemeSpaceMap α) V j).comm).symm

/-- **The canonical derivation `d^a` of Stacks 04CS annihilates every chartwise pullback of a
regular function from the target.**

The chartwise pullback is pullback of a function on the scheme underlying a chart `V` of the
target along the morphism of schemes which the chart index induces, and that morphism commutes
with the two structure morphisms to the scheme underlying `V'`
(`AlgebraicGeometry.Space.chartBaseChangeMap_comp_representedChartBase`).  The chart `V` is
étale over that scheme, so this is
`AlgebraicGeometry.SmallEtale.associatedDerivation_etaleBase_eq_zero`. -/
theorem associatedDerivation_chartPullback
    (V : SmallEtale B S hS (schemeSpace V').1)
    (j : StructuredArrow (op (chartBaseChange B S hS (schemeSpaceMap α) V))
      (comparisonFunctor B S hS (schemeSpace U')).op)
    (b : (structureSetSheaf B S hS (schemeSpace V')).obj.obj (op V)) :
    (AlgebraicGeometry.SmallEtale.associatedDerivation (associatedBigEtaleSite B)
        U'.left.property ((BigFppfOver.toScheme B S hS).map α)).d
        (X := op ((representedSmallEtaleEquivalence B S hS U').functor.obj j.right.unop))
      (chartPullback B S hS (schemeSpaceMap α) V j b) = 0 :=
  AlgebraicGeometry.SmallEtale.associatedDerivation_etaleBase_eq_zero (associatedBigEtaleSite B)
    U'.left.property ((BigFppfOver.toScheme B S hS).map α)
    ((BigFppfOver.toScheme B S hS).map (representedChartBase B S hS V' V))
    (op ((representedSmallEtaleEquivalence B S hS U').functor.obj j.right.unop))
    ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS (schemeSpaceMap α) V j))
    (Eq.trans
      (Eq.trans ((BigFppfOver.toScheme B S hS).map_comp _ _).symm
        (congrArg (BigFppfOver.toScheme B S hS).map
          (chartBaseChangeMap_comp_representedChartBase B S hS α V j)))
      ((BigFppfOver.toScheme B S hS).map_comp _ _))
    b


/-! ### The canonical derivation `d^a` as a `ψ♯`-derivation -/

/-- The small-étale module associated to the Zariski sheaf of relative differentials of the
morphism of schemes underlying `α`, read on the small étale site of the represented algebraic
space `yoneda.obj U`. -/
noncomputable abbrev representedRelativeDifferentials :
    SheafOfModules.{u} (structureRingSheaf B S hS (schemeSpace U')) :=
  (representedAssociatedModule B S hS U' (schemeSpace U').property).obj
    (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α))

/-- The canonical derivation `d^a` of Stacks 04CS on the small étale site of the scheme
underlying `U`. -/
noncomputable abbrev representedAssociatedDerivation :=
  AlgebraicGeometry.SmallEtale.associatedDerivation (associatedBigEtaleSite B)
    U'.left.property ((BigFppfOver.toScheme B S hS).map α)

/-- **The canonical derivation `d^a`, read on the small étale site of the represented algebraic
space, as a morphism of the underlying sheaves of sets.** -/
noncomputable def representedAssociatedDerivationHom :
    structureSetSheaf B S hS (schemeSpace U') ⟶
      moduleSetSheaf B S hS (schemeSpace U')
        (representedRelativeDifferentials B S hS α) :=
  unaryOpHom
    (fun Z a ↦ (representedAssociatedDerivation B S hS α).d
      (X := op ((representedSmallEtaleEquivalence B S hS U').functor.obj Z.unop)) a)
    (fun {_Z _W} g a ↦ ((representedAssociatedDerivation B S hS α).d_map
      ((representedSmallEtaleEquivalence B S hS U').functor.map g.unop).op a).symm)

/-- The value of `AlgebraicGeometry.Space.representedAssociatedDerivationHom` on a section. -/
theorem representedAssociatedDerivationHom_app
    (Z : (SmallEtale B S hS (schemeSpace U').1)ᵒᵖ)
    (a : (structureSetSheaf B S hS (schemeSpace U')).obj.obj Z) :
    (representedAssociatedDerivationHom B S hS α).hom.app Z a =
      (representedAssociatedDerivation B S hS α).d
        (X := op ((representedSmallEtaleEquivalence B S hS U').functor.obj Z.unop)) a :=
  rfl

/-- **The canonical derivation `d^a` annihilates the image of `ψ♯ : ψ^{-1}𝒪 ⟶ 𝒪`, in the form
of an identity of morphisms of sheaves of sets.**  By
`AlgebraicGeometry.Space.structureSharpInverseImageSet_comp_eq_of_chartPullback` it is enough
that it annihilate every chartwise pullback of a regular function, which is
`AlgebraicGeometry.Space.associatedDerivation_chartPullback`. -/
theorem structureSharpInverseImageSet_comp_representedAssociatedDerivationHom :
    structureSharpInverseImageSet B S hS (schemeSpaceMap α) ≫
        representedAssociatedDerivationHom B S hS α =
      structureSharpInverseImageSet B S hS (schemeSpaceMap α) ≫
        zeroDerivationHom (structureRingSheaf B S hS (schemeSpace U'))
          (representedRelativeDifferentials B S hS α) :=
  structureSharpInverseImageSet_comp_eq_of_chartPullback B S hS (schemeSpaceMap α) _ _
    (fun V j b ↦ associatedDerivation_chartPullback B S hS α V j b)

/-- **The canonical derivation `d^a` annihilates the image of `ψ♯ : ψ^{-1}𝒪 ⟶ 𝒪`.** -/
theorem representedAssociatedDerivation_structureSharpInverseImage
    (Z : (SmallEtale B S hS (schemeSpace U').1)ᵒᵖ)
    (a : (inverseImageStructureSheaf B S hS (schemeSpaceMap α)).obj.obj Z) :
    (representedAssociatedDerivation B S hS α).d
        (X := op ((representedSmallEtaleEquivalence B S hS U').functor.obj Z.unop))
      (((structureSharpInverseImage B S hS (schemeSpaceMap α)).hom.app Z).hom a) = 0 :=
  Stacks.Sites.sheafHom_congr_app
    (structureSharpInverseImageSet_comp_representedAssociatedDerivationHom B S hS α) Z a

/-- **The canonical derivation `d^a` of Stacks 04CS is a `ψ`-derivation of the structure sheaf
of the small étale site of the represented algebraic space.** -/
noncomputable def representedUniversalDerivation :
    PresheafOfModulesOfCommRing.Derivation' (representedRelativeDifferentials B S hS α).val
      (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom :=
  PresheafOfModules.Derivation.pushforwardOfId
    (representedSmallEtaleEquivalence B S hS U').functor
    (representedAssociatedDerivation B S hS α)
    (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom
    (representedAssociatedDerivation_structureSharpInverseImage B S hS α)

/-- The value of the `ψ`-derivation of
`AlgebraicGeometry.Space.representedUniversalDerivation` is the value of `d^a`. -/
theorem representedUniversalDerivation_d
    (Z : (SmallEtale B S hS (schemeSpace U').1)ᵒᵖ)
    (a : (structureSetSheaf B S hS (schemeSpace U')).obj.obj Z) :
    (representedUniversalDerivation B S hS α).d a =
      (representedAssociatedDerivation B S hS α).d
        (X := op ((representedSmallEtaleEquivalence B S hS U').functor.obj Z.unop)) a :=
  rfl

/-! ### Chart diagrams over a morphism of represented algebraic spaces -/

/-- **A square in the big fppf site over `S` is a diagram of étale scheme charts over the
morphism of represented algebraic spaces it induces.**  This is the converse of
`AlgebraicGeometry.Space.chartBaseChangeMap_comp_representedChartBase`. -/
noncomputable def representedChartDiagram
    (Z : SmallEtale B S hS (schemeSpace U').1) (V : SmallEtale B S hS (schemeSpace V').1)
    (g : (SmallEtale.toOver B S hS (schemeSpace U').1).obj Z ⟶
      (SmallEtale.toOver B S hS (schemeSpace V').1).obj V)
    (hg : representedChartBase B S hS U' Z ≫ α = g ≫ representedChartBase B S hS V' V) :
    ChartDiagram B S hS (schemeSpace U').1 (schemeSpace V').1 (schemeSpaceMap α).hom where
  U := Z
  V := V
  g := g
  comm := by
    rw [← yoneda_map_representedChartBase B S hS U' Z,
      ← yoneda_map_representedChartBase B S hS V' V,
      show (schemeSpaceMap α).hom = yoneda.map α from rfl]
    exact Eq.trans (yoneda.map_comp _ _).symm
      (Eq.trans (congrArg yoneda.map hg) (yoneda.map_comp _ _))

/-! ### Opens of the chart as charts of the represented algebraic space -/

/-- An open of the scheme underlying an object `C` of the big fppf site, read as an étale chart
of the represented algebraic space `yoneda.obj C`. -/
noncomputable def representedOpenChart (C : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj C).Opens) :
    SmallEtale B S hS (schemeSpace C).1 :=
  (representedSmallEtaleEquivalence B S hS C).inverse.obj
    ((AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj W)

/-- The structure morphism to `S` of the chart attached to an open is the open immersion
followed by the structure morphism of `C`. -/
theorem inclusion_map_representedOpenChart_hom (C : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj C).Opens) :
    B.inclusion.map ((SmallEtale.toOver B S hS (schemeSpace C).1).obj
        (representedOpenChart B S hS C W)).hom =
      W.ι ≫ B.inclusion.map C.hom :=
  rfl

/-- The structure morphism of the chart attached to an open is the open immersion. -/
theorem toScheme_representedChartBase_representedOpenChart (C : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj C).Opens) :
    (BigFppfOver.toScheme B S hS).map
        (representedChartBase B S hS C (representedOpenChart B S hS C W)) =
      W.ι := by
  have h : representedChartBase B S hS C (representedOpenChart B S hS C W) =
      Over.homMk (ObjectProperty.homMk W.ι) rfl := yonedaEquiv_yoneda_map _
  rw [h]
  rfl

/-- A morphism of the big fppf site over `S` is compatible with the structure morphisms to
`S`. -/
theorem toScheme_map_comp_inclusion_map_hom :
    (BigFppfOver.toScheme B S hS).map α ≫ B.inclusion.map V'.hom =
      B.inclusion.map U'.hom :=
  congrArg B.inclusion.map (Over.w α)

/-- **The restriction of `α` to the preimage of an open is compatible with the structure
morphisms to `S`.** -/
theorem resLE_comp_open_ι_comp (W : ((BigFppfOver.toScheme B S hS).obj V').Opens) :
    ((BigFppfOver.toScheme B S hS).map α).resLE W
          ((BigFppfOver.toScheme B S hS).map α ⁻¹ᵁ W) le_rfl ≫
        (W.ι ≫ B.inclusion.map V'.hom) =
      ((BigFppfOver.toScheme B S hS).map α ⁻¹ᵁ W).ι ≫ B.inclusion.map U'.hom := by
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
    toScheme_map_comp_inclusion_map_hom]

/-- The restriction of `α` to the preimage of an open, as a morphism of the big fppf site over
`S` between the charts the two opens define. -/
noncomputable def representedOpenChartMap
    (W : ((BigFppfOver.toScheme B S hS).obj V').Opens) :
    (SmallEtale.toOver B S hS (schemeSpace U').1).obj
        (representedOpenChart B S hS U'
          ((BigFppfOver.toScheme B S hS).map α ⁻¹ᵁ W)) ⟶
      (SmallEtale.toOver B S hS (schemeSpace V').1).obj (representedOpenChart B S hS V' W) :=
  Over.homMk (ObjectProperty.homMk
      (((BigFppfOver.toScheme B S hS).map α).resLE W
        ((BigFppfOver.toScheme B S hS).map α ⁻¹ᵁ W) le_rfl))
    (B.inclusion.map_injective
      (Eq.trans (Functor.map_comp _ _ _) (resLE_comp_open_ι_comp B S hS α W)))

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.representedOpenChartMap` is the
restriction of `α` to the preimage of the open. -/
theorem toScheme_representedOpenChartMap
    (W : ((BigFppfOver.toScheme B S hS).obj V').Opens) :
    (BigFppfOver.toScheme B S hS).map (representedOpenChartMap B S hS α W) =
      ((BigFppfOver.toScheme B S hS).map α).resLE W
        ((BigFppfOver.toScheme B S hS).map α ⁻¹ᵁ W) le_rfl :=
  rfl
/-! ### The Zariski restriction of the universal `ψ`-derivation -/

/-- **A function pulled back along the restriction of a morphism of schemes to the preimage of
an open is the pullback of the function along the morphism, read on the open subscheme.** -/
theorem resLE_appTop_topIso_inv {X₀ Y₀ : Scheme.{u}} (f : X₀ ⟶ Y₀) (W : Y₀.Opens)
    (b : Γ(Y₀, W)) :
    ((f.resLE W (f ⁻¹ᵁ W) le_rfl).appTop).hom ((W.topIso.inv).hom b) =
      (((f ⁻¹ᵁ W).topIso.inv).hom ((f.app W).hom b)) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
  show ((f ⁻¹ᵁ W).topIso.inv).hom ((f.app W).hom ((W.topIso.hom).hom
    ((W.topIso.inv).hom b))) = _
  rw [show (W.topIso.hom).hom ((W.topIso.inv).hom b) = b from
    ConcreteCategory.congr_hom W.topIso.inv_hom_id b]

/-- The diagram of étale scheme charts attached to an open `W` of the scheme underlying `V'`
and its preimage under `α`.

Both charts are the ones a *represented* algebraic space carries on an open of its own
representing scheme, `AlgebraicGeometry.Space.representedOpenChart`, so the diagram is
determined by `W` alone.  It is not an instance of
`AlgebraicGeometry.Space.openChartDiagram` of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeVanishing.lean`, which cuts a
diagram out of an open of the scheme of an *arbitrary* chart `W` of the source together with a
morphism `w` presenting that chart; that construction lives in a module importing this one, so
it is not available here. -/
noncomputable def representedOpenChartDiagram (W : ((BigFppfOver.toScheme B S hS).obj V').Opens) :
    ChartDiagram B S hS (schemeSpace U').1 (schemeSpace V').1 (schemeSpaceMap α).hom :=
  representedChartDiagram B S hS α
    (representedOpenChart B S hS U' ((BigFppfOver.toScheme B S hS).map α ⁻¹ᵁ W))
    (representedOpenChart B S hS V' W) (representedOpenChartMap B S hS α W)
    ((BigFppfOver.toScheme B S hS).map_injective
      (Eq.trans (Functor.map_comp _ _ _)
        (Eq.trans
          (congrArg (fun m ↦ m ≫ (BigFppfOver.toScheme B S hS).map α)
            (toScheme_representedChartBase_representedOpenChart B S hS U'
              ((BigFppfOver.toScheme B S hS).map α ⁻¹ᵁ W)))
          (Eq.trans (Scheme.Hom.resLE_comp_ι _ _).symm
            (Eq.trans
              (congrArg (fun m ↦ (BigFppfOver.toScheme B S hS).map
                  (representedOpenChartMap B S hS α W) ≫ m)
                (toScheme_representedChartBase_representedOpenChart B S hS V' W).symm)
              (Functor.map_comp _ _ _).symm)))))

/-- The chartwise pullback of a regular function along the diagram of
`AlgebraicGeometry.Space.representedOpenChartDiagram` is pullback along the restriction of `α`. -/
theorem chartDiagramPullback_representedOpenChartDiagram
    (W : ((BigFppfOver.toScheme B S hS).obj V').Opens)
    (b : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (schemeSpace V').1
      (schemeSpace V').2).O)).obj.obj (op (representedOpenChart B S hS V' W))) :
    chartDiagramPullback B S hS (schemeSpaceMap α) (representedOpenChartDiagram B S hS α W) b =
      ((((BigFppfOver.toScheme B S hS).map α).resLE W
        ((BigFppfOver.toScheme B S hS).map α ⁻¹ᵁ W) le_rfl).appTop).hom b :=
  rfl
section ZeroHom

variable {C₀ : Type u₁} [Category.{v₁} C₀] {J₀ : GrothendieckTopology C₀}
    [J₀.HasSheafCompose (forget RingCat.{u})] [J₀.HasSheafCompose (forget AddCommGrpCat.{u})]
    {R₀ : Sheaf J₀ RingCat.{u}} {G₀ : SheafOfModules.{u} R₀}

/-- The zero morphism from the sheaf of sets underlying a sheaf of rings to the one underlying a
module vanishes on sections. -/
theorem zeroDerivationHom_hom_app (Z : C₀ᵒᵖ) (x : (ringSheaf R₀).obj.obj Z) :
    (zeroDerivationHom R₀ G₀).hom.app Z x = (0 : G₀.val.obj Z) :=
  Eq.trans (map_zeroDerivationHom R₀ G₀ (sectionsFunctor J₀ Z) x)
    (sectionsFunctor_map_moduleZeroHom R₀ G₀ Z default)

end ZeroHom

variable {U'' V'' : BigFppfOver B S hS} (β : U'' ⟶ V'')

/-- The universal `Y`-derivation, as a morphism of the underlying sheaves of sets, on a
section. -/
theorem universalDerivationHom_hom_app {X₁ Y₁ : AlgebraicSpaces B S hS} (p : X₁ ⟶ Y₁)
    (Z : (SmallEtale B S hS X₁.1)ᵒᵖ)
    (x : (structureSetSheaf B S hS X₁).obj.obj Z) :
    (universalDerivationHom B S hS p).hom.app Z x = (universalDerivation B S hS p).d x :=
  rfl

/-- **The universal `ψ`-derivation annihilates every chartwise pullback of a regular function
from the target.**  This is the vanishing clause of `d_{ψ}` read through
`AlgebraicGeometry.Space.chartPullback_eq_of_structureSharpInverseImageSet_comp_eq`. -/
theorem universalDerivation_chartPullback
    (V : SmallEtale B S hS (schemeSpace V'').1)
    (j : StructuredArrow (op (chartBaseChange B S hS (schemeSpaceMap β) V))
      (comparisonFunctor B S hS (schemeSpace U'')).op)
    (b : (structureSetSheaf B S hS (schemeSpace V'')).obj.obj (op V)) :
    (universalDerivation B S hS (schemeSpaceMap β)).d (X := j.right)
        (chartPullback B S hS (schemeSpaceMap β) V j b) = 0 := by
  refine Eq.trans (universalDerivationHom_hom_app B S hS (schemeSpaceMap β) j.right
    (chartPullback B S hS (schemeSpaceMap β) V j b)).symm ?_
  refine Eq.trans (chartPullback_eq_of_structureSharpInverseImageSet_comp_eq B S hS
    (schemeSpaceMap β) (universalDerivationHom B S hS (schemeSpaceMap β))
    (zeroDerivationHom (structureRingSheaf B S hS (schemeSpace U''))
      (sheafOfDifferentials B S hS (schemeSpaceMap β)))
    (structureSharpInverseImageSet_comp_universalDerivationHom B S hS (schemeSpaceMap β))
    V j b) ?_
  exact zeroDerivationHom_hom_app (R₀ := structureRingSheaf B S hS (schemeSpace U''))
    (G₀ := sheafOfDifferentials B S hS (schemeSpaceMap β)) j.right
    (chartPullback B S hS (schemeSpaceMap β) V j b)

/-- **The universal `ψ`-derivation of `Ω_{ψ}`, read on the small étale site of the scheme
underlying `U'`.**  Its value over an object of that site is the value of `d_{ψ}` over the chart
of the represented algebraic space that the object defines. -/
noncomputable def restrictedUniversalDerivation :=
  PresheafOfModules.Derivation.pushforwardOfId
    (representedSmallEtaleEquivalence B S hS U'').inverse
    (universalDerivation B S hS (schemeSpaceMap β))
    (Functor.whiskerLeft (representedSmallEtaleEquivalence B S hS U'').inverse.op
      (structureSharpInverseImage B S hS (schemeSpaceMap β)).hom)
    (fun _T a ↦ (universalDerivation B S hS (schemeSpaceMap β)).d_app a)

/-- **The Zariski restriction of the universal `ψ`-derivation annihilates every function pulled
back from an open of the scheme underlying `V'`.**  The open and its preimage make up a diagram
of étale scheme charts over `ψ`, and the chartwise pullback of regular functions along that
diagram is exactly the function pulled back along the restriction of `α`. -/
theorem restrictedUniversalDerivation_d
    (T : AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U'') U''.left.property)
    (x : (AlgebraicGeometry.SmallEtale.commRingStructurePresheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U'') U''.left.property).obj (op T)) :
    (restrictedUniversalDerivation B S hS β).d (X := op T) x =
      (universalDerivation B S hS (schemeSpaceMap β)).d
        (X := op ((representedSmallEtaleEquivalence B S hS U'').inverse.obj T)) x :=
  rfl

/-- **The Zariski restriction of the universal `ψ`-derivation annihilates every function pulled
back from an open of the scheme underlying `V'`.**  The open and its preimage make up a diagram
of étale scheme charts over `ψ`, and the chartwise pullback of regular functions along that
diagram is exactly the function pulled back along the restriction of `α`. -/
theorem restrictedUniversalDerivation_pullbackSection
    (W : ((BigFppfOver.toScheme B S hS).obj V'').Opens)
    (b : Γ((BigFppfOver.toScheme B S hS).obj V'', W)) :
    (restrictedUniversalDerivation B S hS β).d
      (AlgebraicGeometry.SmallEtale.pullbackSection (associatedBigEtaleSite B)
        U''.left.property ((BigFppfOver.toScheme B S hS).map β) W b) = 0 := by
  have hb : chartPullback B S hS (schemeSpaceMap β) (representedOpenChart B S hS V'' W)
        (indexOfChartDiagram B S hS (schemeSpaceMap β) (representedOpenChartDiagram B S hS β W))
        ((W.topIso.inv).hom b) =
      AlgebraicGeometry.SmallEtale.pullbackSection (associatedBigEtaleSite B)
        U''.left.property ((BigFppfOver.toScheme B S hS).map β) W b :=
    Eq.trans (chartPullback_indexOfChartDiagram B S hS (schemeSpaceMap β)
        (representedOpenChartDiagram B S hS β W) _)
      (Eq.trans (chartDiagramPullback_representedOpenChartDiagram B S hS β W _)
        (resLE_appTop_topIso_inv ((BigFppfOver.toScheme B S hS).map β) W b))
  refine Eq.trans (restrictedUniversalDerivation_d B S hS β _ _) ?_
  refine Eq.trans (congrArg
    (f := fun z : (structureSetSheaf B S hS (schemeSpace U'')).obj.obj
        (op (representedOpenChart B S hS U''
          ((BigFppfOver.toScheme B S hS).map β ⁻¹ᵁ W))) ↦
      (universalDerivation B S hS (schemeSpaceMap β)).d
        (X := op (representedOpenChart B S hS U''
          ((BigFppfOver.toScheme B S hS).map β ⁻¹ᵁ W))) z) hb).symm ?_
  exact universalDerivation_chartPullback B S hS β (representedOpenChart B S hS V'' W)
    (indexOfChartDiagram B S hS (schemeSpaceMap β) (representedOpenChartDiagram B S hS β W))
    ((W.topIso.inv).hom b)
/-! ### The comparison isomorphism -/

/-- **The universal `ψ`-derivation of `Ω_{ψ}`, read on the small étale site of the scheme
underlying `U'` over the constant presheaf of rings `ℤ`:** the same values as
`AlgebraicGeometry.Space.restrictedUniversalDerivation`, with only the Leibniz rule recorded.

This is the form in which the scheme-level development of Stacks 04CS consumes a derivation:
`AlgebraicGeometry.SmallEtale.associatedDerivation_postcomp_differentialsComparison` and
`AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedDerivation` are stated over
`AlgebraicGeometry.SmallEtale.siteConstIntMap`, the weakest base available, while
`AlgebraicGeometry.Space.restrictedUniversalDerivation` is taken over the structure map
`ψ♯` of the morphism of small étale ringed topoi.  Only the base differs; the values, and hence
`AlgebraicGeometry.SmallEtale.differentialsComparison`, are unchanged, so the two readings are
interchangeable wherever the vanishing condition over `ψ♯` is not itself used. -/
noncomputable def restrictedUniversalIntDerivation :
    PresheafOfModulesOfCommRing.Derivation'
      (R := (AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U'') U''.left.property).obj)
      ((representedModuleRestriction B S hS U'').obj
        (sheafOfDifferentials B S hS (schemeSpaceMap β))).val
      (AlgebraicGeometry.SmallEtale.siteConstIntMap (associatedBigEtaleSite B)
        U''.left.property _) where
  d := (restrictedUniversalDerivation B S hS β).d
  d_mul := (restrictedUniversalDerivation B S hS β).d_mul
  d_map := (restrictedUniversalDerivation B S hS β).d_map
  d_app {V} a :=
    AlgebraicGeometry.SmallEtale.siteConstIntMap_app_eq_zero
      (P := (AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U'') U''.left.property).obj)
      (associatedBigEtaleSite B) U''.left.property
      (restrictedUniversalDerivation B S hS β).d
      ((restrictedUniversalDerivation B S hS β).d_one V) a

/-- **The comparison map of Stacks 04CS at `Ω_{ψ}`, on the small étale site of the scheme
underlying `U'`.** -/
noncomputable def schemeDifferentialsComparison :
    AlgebraicGeometry.SmallEtale.associatedRelativeDifferentials (associatedBigEtaleSite B)
        U''.left.property ((BigFppfOver.toScheme B S hS).map β) ⟶
      (representedModuleRestriction B S hS U'').obj
        (sheafOfDifferentials B S hS (schemeSpaceMap β)) :=
  AlgebraicGeometry.SmallEtale.differentialsComparison (associatedBigEtaleSite B)
    U''.left.property ((BigFppfOver.toScheme B S hS).map β)
    (F := (representedModuleRestriction B S hS U'').obj
      (sheafOfDifferentials B S hS (schemeSpaceMap β)))
    (restrictedUniversalIntDerivation B S hS β)
    (restrictedUniversalDerivation_pullbackSection B S hS β)

/-- **The comparison map `(Ω_{U/V})^a ⟶ Ω_{ψ}` on the small étale site of the represented
algebraic space.** -/
noncomputable def representedDifferentialsComparison :
    representedRelativeDifferentials B S hS β ⟶
      sheafOfDifferentials B S hS (schemeSpaceMap β) :=
  (representedModulePushforward B S hS U'').map (schemeDifferentialsComparison B S hS β) ≫
    (representedModuleSiteEquivalence B S hS U'').counit.app
      (sheafOfDifferentials B S hS (schemeSpaceMap β))
/-- The comparison map on sections: the scheme-level comparison at the corresponding object of
the small étale site of the scheme, followed by the counit of the equivalence of module
categories. -/
theorem representedDifferentialsComparison_val_app
    (Z : (SmallEtale B S hS (schemeSpace U'').1)ᵒᵖ)
    (y : (representedRelativeDifferentials B S hS β).val.obj Z) :
    (representedDifferentialsComparison B S hS β).val.app Z y =
      (sheafOfDifferentials B S hS (schemeSpaceMap β)).val.map
          ((representedSmallEtaleEquivalence B S hS U'').unit.app Z.unop).op
        ((schemeDifferentialsComparison B S hS β).val.app
          (op ((representedSmallEtaleEquivalence B S hS U'').functor.obj Z.unop)) y) :=
  rfl

/-- **The comparison map carries the canonical derivation `d^a` to the universal
`ψ`-derivation.**  Over the chart attached to an object of the small étale site of the scheme it
is the scheme-level statement
`AlgebraicGeometry.SmallEtale.associatedDerivation_postcomp_differentialsComparison` of
Stacks 04CS, read on a section, and the counit of the equivalence of module categories is
restriction along the unit of the equivalence of sites, which does not move a regular
function. -/
theorem representedDifferentialsComparison_representedUniversalDerivation
    (Z : (SmallEtale B S hS (schemeSpace U'').1)ᵒᵖ)
    (x : (structureSetSheaf B S hS (schemeSpace U'')).obj.obj Z) :
    (representedDifferentialsComparison B S hS β).val.app Z
        ((representedUniversalDerivation B S hS β).d x) =
      (universalDerivation B S hS (schemeSpaceMap β)).d x := by
  refine Eq.trans (representedDifferentialsComparison_val_app B S hS β Z _) ?_
  refine Eq.trans (congrArg (fun z ↦
      (sheafOfDifferentials B S hS (schemeSpaceMap β)).val.map
        ((representedSmallEtaleEquivalence B S hS U'').unit.app Z.unop).op z)
    (Eq.trans
      (PresheafOfModulesOfCommRing.Derivation.congr_d
        (X := op ((representedSmallEtaleEquivalence B S hS U'').functor.obj Z.unop))
        (AlgebraicGeometry.SmallEtale.associatedDerivation_postcomp_differentialsComparison
          (associatedBigEtaleSite B) U''.left.property
          ((BigFppfOver.toScheme B S hS).map β)
          (F := (representedModuleRestriction B S hS U'').obj
            (sheafOfDifferentials B S hS (schemeSpaceMap β)))
          (restrictedUniversalIntDerivation B S hS β)
          (restrictedUniversalDerivation_pullbackSection B S hS β)) x)
      (restrictedUniversalDerivation_d B S hS β
        ((representedSmallEtaleEquivalence B S hS U'').functor.obj Z.unop) x))) ?_
  exact ((universalDerivation B S hS (schemeSpaceMap β)).d_map
    ((representedSmallEtaleEquivalence B S hS U'').unit.app Z.unop).op x).symm
/-! ### The comparison map is an isomorphism -/

section Injective

/-- Restriction along an isomorphism of a presheaf of modules is injective on sections. -/
theorem _root_.PresheafOfModules.map_injective_of_isIso {C : Type u₁} [Category.{v₁} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} (P : PresheafOfModules.{u} R) {Z₁ Z₂ : Cᵒᵖ} (g : Z₁ ⟶ Z₂)
    [IsIso g] {a b : P.obj Z₁} (h : P.map g a = P.map g b) : a = b :=
  (ConcreteCategory.bijective_of_isIso
    (((PresheafOfModules.toPresheaf R).obj P).map g)).1 h

end Injective

/-- Transport of modules along the equivalence of small étale sites is full. -/
instance full_representedModulePushforward (C : BigFppfOver B S hS) :
    (representedModulePushforward B S hS C).Full :=
  inferInstanceAs ((representedModuleSiteEquivalence B S hS C).functor).Full

/-- Transport of modules along the equivalence of small étale sites is faithful. -/
instance faithful_representedModulePushforward (C : BigFppfOver B S hS) :
    (representedModulePushforward B S hS C).Faithful :=
  inferInstanceAs ((representedModuleSiteEquivalence B S hS C).functor).Faithful

/-- Two derivations of a presheaf of modules are equal when their values agree on sections. -/
private theorem derivation_ext_of_d_eq {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}}
    {M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} {φ : S₀ ⟶ F.op ⋙ R}
    {d d' : PresheafOfModulesOfCommRing.Derivation M φ} (h : ∀ (Z : Dᵒᵖ) (x : R.obj Z), d.d x = d'.d x) : d = d' :=
  PresheafOfModulesOfCommRing.Derivation.ext (funext fun Z ↦ AddMonoidHom.ext (h Z))

/-- **A morphism out of `(Ω_{U/V})^a` is determined by its values on the canonical differentials
over the objects of the small étale site coming from charts of the represented algebraic
space.**  Every object of that site is isomorphic to one of them, by the counit of the
equivalence of sites, and restriction along an isomorphism is injective on sections. -/
theorem eq_of_representedAssociatedDerivation
    {P : SheafOfModules.{u} (AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U'') U''.left.property)}
    (u₁ u₂ : AlgebraicGeometry.SmallEtale.associatedRelativeDifferentials
      (associatedBigEtaleSite B) U''.left.property
      ((BigFppfOver.toScheme B S hS).map β) ⟶ P)
    (h : ∀ (Z : SmallEtale B S hS (schemeSpace U'').1)
      (x : (AlgebraicGeometry.SmallEtale.commRingStructurePresheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U'') U''.left.property).obj
          (op ((representedSmallEtaleEquivalence B S hS U'').functor.obj Z))),
      u₁.val.app (op ((representedSmallEtaleEquivalence B S hS U'').functor.obj Z))
          ((representedAssociatedDerivation B S hS β).d x) =
        u₂.val.app (op ((representedSmallEtaleEquivalence B S hS U'').functor.obj Z))
          ((representedAssociatedDerivation B S hS β).d x)) :
    u₁ = u₂ := by
  have hall : ∀ (T : AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U'') U''.left.property)
      (x : (AlgebraicGeometry.SmallEtale.commRingStructurePresheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U'') U''.left.property).obj (op T)),
      u₁.val.app (op T) ((representedAssociatedDerivation B S hS β).d x) =
        u₂.val.app (op T) ((representedAssociatedDerivation B S hS β).d x) := by
    intro T x
    have key : ∀ (u : AlgebraicGeometry.SmallEtale.associatedRelativeDifferentials
          (associatedBigEtaleSite B) U''.left.property
          ((BigFppfOver.toScheme B S hS).map β) ⟶ P),
        P.val.map ((representedSmallEtaleEquivalence B S hS U'').counit.app T).op
            (u.val.app (op T) ((representedAssociatedDerivation B S hS β).d x)) =
          u.val.app (op ((representedSmallEtaleEquivalence B S hS U'').functor.obj
              ((representedSmallEtaleEquivalence B S hS U'').inverse.obj T)))
            ((representedAssociatedDerivation B S hS β).d
              ((AlgebraicGeometry.SmallEtale.commRingStructurePresheaf
                (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U'')
                U''.left.property).map
                ((representedSmallEtaleEquivalence B S hS U'').counit.app T).op x)) := by
      intro u
      refine Eq.trans (PresheafOfModules.naturality_apply u.val
        ((representedSmallEtaleEquivalence B S hS U'').counit.app T).op
        ((representedAssociatedDerivation B S hS β).d x)).symm ?_
      exact congrArg (u.val.app _)
        ((representedAssociatedDerivation B S hS β).d_map
          ((representedSmallEtaleEquivalence B S hS U'').counit.app T).op x).symm
    let : IsIso ((representedSmallEtaleEquivalence B S hS U'').counit.app T) :=
      ((representedSmallEtaleEquivalence B S hS U'').counitIso.app T).isIso_hom
    refine P.val.map_injective_of_isIso
      ((representedSmallEtaleEquivalence B S hS U'').counit.app T).op ?_
    exact Eq.trans (key u₁)
      (Eq.trans (h ((representedSmallEtaleEquivalence B S hS U'').inverse.obj T) _)
        (key u₂).symm)
  have hDa := AlgebraicGeometry.SmallEtale.associatedDerivation_pullbackSection_eq_zero
    (associatedBigEtaleSite B) U''.left.property ((BigFppfOver.toScheme B S hS).map β)
  obtain ⟨_g, -, huniq⟩ :=
    AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedDerivation
      (associatedBigEtaleSite B) U''.left.property ((BigFppfOver.toScheme B S hS).map β) (F := P)
      ((AlgebraicGeometry.SmallEtale.associatedDerivation (associatedBigEtaleSite B)
        U''.left.property ((BigFppfOver.toScheme B S hS).map β)).postcomp u₁.val)
      (AlgebraicGeometry.SmallEtale.postcomp_pullbackSection_eq_zero (associatedBigEtaleSite B)
        U''.left.property ((BigFppfOver.toScheme B S hS).map β) _ hDa u₁)
  exact Eq.trans (huniq u₁ rfl) (huniq u₂ (derivation_ext_of_d_eq
    fun Z x ↦ (hall Z.unop x).symm)).symm
/-- An isomorphism may be cancelled on the right. -/
private theorem eq_of_comp_inv_eq {C₁ : Type u₁} [Category.{v₁} C₁] {A T₁ T₂ : C₁}
    {u v : A ⟶ T₂} (e : T₁ ≅ T₂) (h : u ≫ e.inv = v ≫ e.inv) : u = v := by
  rw [← Category.comp_id u, ← e.inv_hom_id, ← Category.assoc, h, Category.assoc,
    e.inv_hom_id, Category.comp_id]

/-- **A morphism out of the transported module `(Ω_{U/V})^a` is determined by its values on the
canonical derivation.**  The target is the image under the equivalence of module categories of
its own reading on the small étale site of the scheme, and there this is
`AlgebraicGeometry.Space.eq_of_representedAssociatedDerivation`. -/
theorem eq_of_representedUniversalDerivation
    {G : SheafOfModules.{u} (structureRingSheaf B S hS (schemeSpace U''))}
    (u₁ u₂ : representedRelativeDifferentials B S hS β ⟶ G)
    (h : ∀ (Z : SmallEtale B S hS (schemeSpace U'').1)
      (x : (structureSetSheaf B S hS (schemeSpace U'')).obj.obj (op Z)),
      u₁.val.app (op Z) ((representedUniversalDerivation B S hS β).d x) =
        u₂.val.app (op Z) ((representedUniversalDerivation B S hS β).d x)) :
    u₁ = u₂ := by
  set i := (representedModuleSiteEquivalence B S hS U'').counitIso.app G
  have hm : ∀ u : representedRelativeDifferentials B S hS β ⟶ G,
      (representedModulePushforward B S hS U'').map
        ((representedModulePushforward B S hS U'').preimage (u ≫ i.inv)) = u ≫ i.inv :=
    fun _ ↦ (representedModulePushforward B S hS U'').map_preimage _
  have hkey : (representedModulePushforward B S hS U'').preimage (u₁ ≫ i.inv) =
      (representedModulePushforward B S hS U'').preimage (u₂ ≫ i.inv) := by
    refine eq_of_representedAssociatedDerivation B S hS β _ _ (fun Z x ↦ ?_)
    refine Eq.trans (congrArg (fun m ↦ m.val.app (op Z)
      ((representedUniversalDerivation B S hS β).d x)) (hm u₁)) ?_
    refine Eq.trans ?_ (congrArg (fun m ↦ m.val.app (op Z)
      ((representedUniversalDerivation B S hS β).d x)) (hm u₂)).symm
    exact congrArg (i.inv.val.app (op Z)) (h Z x)
  exact eq_of_comp_inv_eq i
    (Eq.trans (hm u₁).symm (Eq.trans (congrArg (representedModulePushforward B S hS U'').map hkey)
      (hm u₂)))

/-! ### Stacks 04CS for a morphism of represented algebraic spaces -/

/-- **The comparison map `(Ω_{U/V})^a ⟶ Ω_{ψ}` is an isomorphism.**

The sheaf of differentials `Ω_{ψ}` corepresents the `ψ`-derivations of `𝒪` on the small étale
site of `yoneda.obj U`, and `(Ω_{U/V})^a` corepresents the derivations annihilating the
functions pulled back from an open of the scheme underlying `V` (Stacks 04CS).  The canonical
derivation `d^a` is a `ψ`-derivation
(`AlgebraicGeometry.Space.representedUniversalDerivation`) and the universal `ψ`-derivation
annihilates the pulled-back functions
(`AlgebraicGeometry.Space.restrictedUniversalDerivation_pullbackSection`), so the two
corepresented classes agree and the two comparison maps are mutually inverse. -/
theorem isIso_representedDifferentialsComparison :
    IsIso (representedDifferentialsComparison B S hS β) := by
  obtain ⟨c, hc, -⟩ := universalDerivation_isUniversal B S hS (schemeSpaceMap β)
    (representedRelativeDifferentials B S hS β) (representedUniversalDerivation B S hS β)
  have hcd : ∀ (Z : (SmallEtale B S hS (schemeSpace U'').1)ᵒᵖ)
      (x : (structureSetSheaf B S hS (schemeSpace U'')).obj.obj Z),
      c.val.app Z ((universalDerivation B S hS (schemeSpaceMap β)).d x) =
        (representedUniversalDerivation B S hS β).d x :=
    fun _Z x ↦ PresheafOfModulesOfCommRing.Derivation.congr_d hc x
  refine ⟨c, ?_, ?_⟩
  · refine eq_of_representedUniversalDerivation B S hS β _ _ (fun Z x ↦ ?_)
    refine Eq.trans (congrArg (c.val.app (op Z))
      (representedDifferentialsComparison_representedUniversalDerivation B S hS β
        (op Z) x)) ?_
    exact hcd (op Z) x
  · obtain ⟨_g, -, hu⟩ := universalDerivation_isUniversal B S hS (schemeSpaceMap β)
      (sheafOfDifferentials B S hS (schemeSpaceMap β))
      (universalDerivation B S hS (schemeSpaceMap β))
    refine Eq.trans (hu _ ?_) (hu _ (derivation_ext_of_d_eq fun _ _ ↦ rfl)).symm
    refine derivation_ext_of_d_eq fun Z x ↦ ?_
    refine Eq.trans (congrArg
      ((representedDifferentialsComparison B S hS β).val.app Z) (hcd Z x)) ?_
    exact representedDifferentialsComparison_representedUniversalDerivation B S hS β Z x

/-- **Stacks 04CS for a morphism of represented algebraic spaces.**  The sheaf of differentials
of the morphism of algebraic spaces represented by a morphism `α : U ⟶ V` of the big fppf site
over `S` is the small-étale module associated to the Zariski sheaf of relative differentials of
the morphism of schemes underlying `α`. -/
noncomputable def sheafOfDifferentialsRepresentedIso :
    sheafOfDifferentials B S hS (schemeSpaceMap β) ≅
      (representedAssociatedModule B S hS U'' (schemeSpace U'').property).obj
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map β)) :=
  (@asIso _ _ _ _ _ (isIso_representedDifferentialsComparison B S hS β)).symm
/-! ### Zero objects and the comparison functor -/

/-- **The comparison functor to the small étale site of a represented algebraic space detects
the zero object** at a quasi-coherent module.  It preserves the zero object because it is
additive, and it reflects it because the associated-module functor of the small étale site of a
scheme does at a quasi-coherent module (Stacks 08H8) and because transport along the
equivalence of sites is an equivalence of module categories. -/
theorem isZero_representedAssociatedModule_iff (C : BigFppfOver B S hS)
    (N : ((BigFppfOver.toScheme B S hS).obj C).Modules) [N.IsQuasicoherent] :
    CategoryTheory.Limits.IsZero
        ((representedAssociatedModule B S hS C (schemeSpace C).property).obj N) ↔
      CategoryTheory.Limits.IsZero N := by
  have := additive_representedAssociatedModule B S hS C (schemeSpace C).property
  refine ⟨fun h ↦ ?_, fun h ↦ Functor.map_isZero _ h⟩
  refine AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj C) C.left.property N ?_
  exact CategoryTheory.Limits.IsZero.of_iso
    (Functor.map_isZero (representedModuleRestriction B S hS C) h)
    ((representedModuleSiteEquivalence B S hS C).unitIso.app _)

end AlgebraicGeometry.Space

end
