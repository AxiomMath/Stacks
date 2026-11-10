module

public import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Descent
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Stalk
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.MorphismSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionPullbackIso
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenChartSectionsRingTransport
public import StacksFrontier.RingTheory.Descent.EqualizerDescent

/-!
# The chart-restriction comparison of a quasi-coherent module is an isomorphism

Let `g : V ⟶ U` be a morphism of étale charts of an algebraic space `F` and let `M` be an
`𝒪_F`-module.  `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` is the
comparison

  `(chartSchemeMap g)^* (M|_U) ⟶ M|_V`

between the inverse image along the chart morphism of the restriction of `M` to the larger chart
scheme and the restriction of `M` to the smaller one.  This file proves it is an **isomorphism**
when `M` is quasi-coherent on the small étale site.

The proof is the affine-local criterion
`AlgebraicGeometry.Space.isIso_restrictToChartSchemePullbackComparison_of_forall_isAffineOpen`
fed with the affine case, and the affine case is the recognition of the comparison as a base
change:

* over a pair of affine Zariski opens `O`, `O'` with `O' ≤ chartSchemeMap g ⁻¹ᵁ O`, the sections
  of the inverse image are the base change of the sections of `M|_U` over `O`, by
  `AlgebraicGeometry.isBaseChange_pullbackSection_of_isAffineOpen`;
* the restriction map of `M` between the two étale charts the opens cut out is *also* a base
  change, because `M` is cartesian on affine charts and the base rings transport, which is
  `AlgebraicGeometry.Space.bijective_liftBaseChange_of_isQuasicoherentOnSite_openChart`;
* the comparison carries the first to the second, by the computation
  `sectionsLinearEquivOfIso_restrictToChartSchemePullbackComparison_app_pullbackSection` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionSectionsUnit.lean`;
* and a map between two base changes of one module that is compatible with both structure maps is
  bijective.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.openSectionsModule` names the module structure over the ring
  of regular functions carried by the sections of a module on a scheme; see the implementation
  notes for why naming it is necessary.

## Main results

* `Stacks.BaseChange.bijective_of_isBaseChange_comp`: **a map of base changes of one module is
  bijective.**  If `ρ : M →ₗ[R] N` exhibits `N` as the base change of `M` to `S` and
  `c : N →ₗ[S] P` composes with it to a map that exhibits `P` as the base change of `M` to `S`,
  then `c` is bijective.
* `AlgebraicGeometry.Space.isIso_restrictToChartSchemePullbackComparison_app_of_isAffineOpen`:
  **the affine case.**  Over a pair of affine Zariski opens the component of the comparison is
  an isomorphism.
* `AlgebraicGeometry.Space.isIso_restrictToChartSchemePullbackComparison_of_isQuasicoherentOnSite`:
  **the comparison is an isomorphism.**

## Implementation notes

**Why the module structures are supplied by hand.**  The sections `Γ(N, O)` of a module on a
scheme carry a `Module Γ(X, O)` structure as an instance, and instance search finds it at once
for a general scheme and module.  At the concrete sheaves here — the Zariski sheafification
`AlgebraicGeometry.Space.restrictToChartScheme` and the direct image of the chart sections along
`AlgebraicGeometry.Space.chartSchemeRestrictionSheafHom` — the search does **not** terminate
within the project's `maxSynthPendingDepth`, which is what the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionSectionsUnit.lean` record when they
say the type of the linear equivalence "cannot be written out".  No recursion depth is raised and
no bridging instance across the `CommRingCat`/`RingCat` boundary is introduced: the one instance
that search finds generically is named once, as
`AlgebraicGeometry.Scheme.Modules.openSectionsModule`, and supplied with `letI` at each concrete
type, exactly as `AlgebraicGeometry.Scheme.Modules.pullbackSectionsModule` is supplied for the
sections of a pullback.  Everything else is `Module.compHom` along a map already in the tree.

**The two readings of the scalars agree definitionally.**  The action of `Γ(chartScheme U, O)` on
the sections of `M` over the étale chart `openChart U O`, read through the direct image along
`chartSchemeRestrictionSheafHom`, **is** the action of the chart ring
`𝒪_F(openChart U O)` transported along `AlgebraicGeometry.Space.openChartRingEquiv`; the
hypotheses `hMod` and `hN` of
`AlgebraicGeometry.Space.bijective_liftBaseChange_iff_sectionsBaseChange_openChart` are therefore
discharged by `rfl` here.  That is what makes the transport of
`StacksFrontier/AlgebraicGeometry/Spaces/OpenChartSectionsRingTransport.lean` applicable at all:
`chartSchemeRestrictionRingHom` is `AlgebraicGeometry.Scheme.restrictFunctorΓ.inv` whiskered, so
its component over `O` is the inverse of `AlgebraicGeometry.Scheme.Opens.topIso`, which is what
`openChartRingEquiv` bundles.

**Why the conclusion is about a bare function and not about linearity.**  `IsIso` of a component
of a morphism of sheaves of modules on a scheme is bijectivity of the underlying function, by
`CategoryTheory.ConcreteCategory.isIso_iff_bijective`; the component is linear over the
`RingCat`-valued sections while the base-change argument runs over the `CommRingCat`-valued
`Γ(chartScheme V, O')`.  Bijectivity of a function does not mention either, so the boundary is
never crossed by a term: the argument is run entirely on the `CommRingCat` side, using
`AlgebraicGeometry.Scheme.Modules.sectionsLinearMap` to read the component there, and its
conclusion is transported by nothing.

**What this closes, and what it does not.**  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/AlgebraSheafChartCartesian.lean` list three inputs missing
before a descent datum for Stacks 081V can be assembled; the third of them, "the module-level
comparison", is what this file supplies: the canonical comparison
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` is now invertible, and not only
is there *some* isomorphism between its source and target, which is what
`AlgebraicGeometry.Space.nonempty_pullback_restrictToChartScheme` gives.  Nothing here says
anything about sheaves of **algebras**, and the datum a descent construction consumes is an
isomorphism of sheaves of algebras, which is strictly more than this.  Three steps separate the
two, in this order.

* **The algebra-level comparison does not exist as a term.**
  `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransition` is a morphism into a
  direct image; its transpose along
  `Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction` — a morphism
  `(algebraPullback (chartSchemeMap g)).obj (𝒜|_V) ⟶ 𝒜|_W` — is formed nowhere in the tree.
* **Reflecting invertibility needs the module underlying an algebra inverse image.**
  `Stacks.FundamentalGroup.isIso_of_isIso_underlyingModuleMap` reflects isomorphisms of sheaves
  of algebras on a scheme from their underlying modules, and
  `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule_restrictToChartScheme` identifies the
  module underlying a chart restriction by `rfl`; what is **not** available is the identification
  of the module underlying `g⁻¹𝒜` with the inverse image of the module underlying `𝒜`.  That is
  the step recorded in the docstring of
  `Stacks.SheafOfModules.AlgebraPushout.algebraPullbackComparison`.  Its pushout half *is* done,
  as `Stacks.SheafOfModules.AlgebraPushout.isIso_extendScalarsComparison` and
  `Stacks.SheafOfModules.AlgebraPushout.underlyingModulePushoutIso`; the inverse-image half is
  what remains.
* **Beyond the datum**, the identification of the glued morphism's direct image with `𝒜` is
  proved nowhere; see the docstring of
  `AlgebraicGeometry.Space.boundedPushforwardAlgebraFunctor`.

So this file does not assert essential surjectivity of
`AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor`, whose content is the right-hand side
of `AlgebraicGeometry.Space.essSurj_boundedPushforwardAlgebraFunctor_iff`, and nothing here
should be read as asserting it.

**No `stacks` attribute is claimed.**  What is proved is the cartesianness of the chart
restriction of a quasi-coherent module — the content of Descent, Proposition 03DX(2) read for
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` through the identification of
the chart restriction with an inverse image, Stacks 03LY.  Both tags are registered elsewhere
and no declaration here asserts either; in particular none of this is Stacks 03M0.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **The module structure over the regular functions on an open carried by the sections of a
module on a scheme**, named.

It is already an instance, and instance search finds it at once for a general scheme and module;
at the concrete sheaves of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionPullbackIsoAffine.lean` it does not
terminate within the project's `maxSynthPendingDepth`, so it is named here and supplied with
`letI` there.  See the implementation notes of that file. -/
@[instance_reducible]
noncomputable def Scheme.Modules.openSectionsModule {X : Scheme.{u}} (N : X.Modules)
    (V : X.Opens) : Module Γ(X, V) Γ(N, V) :=
  inferInstance

end AlgebraicGeometry

namespace Stacks.BaseChange

/-- **A map between two base changes of one module, compatible with both structure maps, is
bijective.**  If `ρ : M →ₗ[R] N` exhibits `N` as the base change of `M` along `R → S`, and the
`S`-linear map `c : N →ₗ[S] P` composed with `ρ` is a map `g₁` which exhibits `P` as the base
change of `M`, then `c` is bijective.

Both `ρ` and `g₁` have bijective base-change comparisons out of `S ⊗[R] M`, by
`IsBaseChange.bijective_liftBaseChange`, and `c` composed with the first is the second — on a
pure tensor because `c` is `S`-linear, in general because all three maps are additive.  So `c` is
the second comparison followed by the inverse of the first. -/
theorem bijective_of_isBaseChange_comp {R S M N P : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    {ρ : M →ₗ[R] N} (hρ : IsBaseChange S ρ) (c : N →ₗ[S] P) {g₁ : M →ₗ[R] P}
    (hg : ∀ m, c (ρ m) = g₁ m) (hg₁ : IsBaseChange S g₁) :
    Function.Bijective c := by
  have hcomp : ∀ z : S ⊗[R] M, c (ρ.liftBaseChange S z) = g₁.liftBaseChange S z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s m =>
        rw [LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul, hg]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have h1 := hρ.bijective_liftBaseChange
  have h2 := hg₁.bijective_liftBaseChange
  refine ⟨fun x y hxy => ?_, fun p => ?_⟩
  · obtain ⟨a, ha⟩ := h1.2 x
    obtain ⟨b, hb⟩ := h1.2 y
    rw [← ha, ← hb] at hxy ⊢
    exact congrArg _ (h2.1 ((hcomp a).symm.trans (hxy.trans (hcomp b))))
  · obtain ⟨z, hz⟩ := h2.2 p
    exact ⟨ρ.liftBaseChange S z, (hcomp z).trans hz⟩

end Stacks.BaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)

/-! ### The comparison over a pair of affine opens -/

/-- **The component of the chart-restriction comparison over a pair of affine Zariski opens is an
isomorphism**, for a module quasi-coherent on the small étale site.

Over `O` affine in the larger chart scheme and `O'` affine in the smaller one inside the preimage
of `O`, the sections of the inverse image are the base change of the sections of `M|_U` over `O`
(`AlgebraicGeometry.isBaseChange_pullbackSection_of_isAffineOpen`, whose quasi-coherence
hypothesis is `AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme`); the restriction
map of `M` along the morphism of étale charts
`openChartHomOfLE V hle ≫ openChartRestrict g O` is also a base change
(`AlgebraicGeometry.Space.bijective_liftBaseChange_of_isQuasicoherentOnSite_openChart`, which is
cartesianness on affine charts read over the rings of regular functions); and the comparison
carries the first to the second through the two identifications of the chart restrictions'
sections with the chart sections of `M`, which is the computation
`sectionsLinearEquivOfIso_restrictToChartSchemePullbackComparison_app_pullbackSection` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionSectionsUnit.lean`.
`Stacks.BaseChange.bijective_of_isBaseChange_comp` concludes.

Affineness of the étale chart an affine open cuts out is affineness of the open, with no
transport, by `AlgebraicGeometry.Space.openChartFunctor_comp_toScheme`. -/
theorem isIso_restrictToChartSchemePullbackComparison_app_of_isAffineOpen
    (M : Modules.{u, u} B S hS F hF) (hM : M.IsQuasicoherentOnSite)
    {U V : SmallEtale B S hS F} (g : V ⟶ U)
    [HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology (chartScheme V)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme V)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(openChartFunctor B S hS F U).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme U)) (SmallEtale.topology B S hS F)]
    [(openChartFunctor B S hS F V).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme V)) (SmallEtale.topology B S hS F)]
    {O : (chartScheme U).Opens} {O' : (chartScheme V).Opens}
    (hO : IsAffineOpen O) (hO' : IsAffineOpen O')
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O) :
    IsIso ((restrictToChartSchemePullbackComparison B S hS F hF M g).val.app (op O')) := by
  have : (restrictToChartScheme B S hS F hF M U).IsQuasicoherent :=
    isQuasicoherent_restrictToChartScheme B S hS ⟨F, hF⟩ M hM U
  let : Algebra Γ(chartScheme U, O) Γ(chartScheme V, O') :=
    ((chartSchemeMap g).appLE O O' hle).hom.toAlgebra
  let := Scheme.Modules.pullbackSectionsModule (chartSchemeMap g)
    (restrictToChartScheme B S hS F hF M U) O O' hle
  have : IsScalarTower Γ(chartScheme U, O) Γ(chartScheme V, O')
      Γ((Scheme.Modules.pullback (chartSchemeMap g)).obj
        (restrictToChartScheme B S hS F hF M U), O') :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hbc := isBaseChange_pullbackSection_of_isAffineOpen (chartSchemeMap g)
    (restrictToChartScheme B S hS F hF M U) hO hO' hle (fun _ => rfl)
    (Scheme.Modules.pullbackSectionₗ (chartSchemeMap g)
      (restrictToChartScheme B S hS F hF M U) O O' hle) (fun _ => rfl)
  let := Scheme.Modules.openSectionsModule (restrictToChartScheme B S hS F hF M U) O
  let := Scheme.Modules.openSectionsModule (restrictToChartScheme B S hS F hF M V) O'
  let : Module Γ(chartScheme U, O) Γ(restrictToChartScheme B S hS F hF M V, O') :=
    Module.compHom _ ((chartSchemeMap g).appLE O O' hle).hom
  have : IsScalarTower Γ(chartScheme U, O) Γ(chartScheme V, O')
      Γ(restrictToChartScheme B S hS F hF M V, O') :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : Module Γ(chartScheme U, O)
      (M.val.obj (op (openChart B S hS F U O)) : Type u) :=
    Scheme.Modules.openSectionsModule
      ((SheafOfModules.pushforward.{u} (chartSchemeRestrictionSheafHom B S hS hF U)).obj M) O
  let : Module Γ(chartScheme V, O')
      (M.val.obj (op (openChart B S hS F V O')) : Type u) :=
    Scheme.Modules.openSectionsModule
      ((SheafOfModules.pushforward.{u} (chartSchemeRestrictionSheafHom B S hS hF V)).obj M) O'
  let : Module Γ(chartScheme U, O)
      (M.val.obj (op (openChart B S hS F V O')) : Type u) :=
    Module.compHom _ ((chartSchemeMap g).appLE O O' hle).hom
  have : IsScalarTower Γ(chartScheme U, O) Γ(chartScheme V, O')
      (M.val.obj (op (openChart B S hS F V O')) : Type u) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let := chartSectionsModule M
    (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O)
  let f₁ : (M.val.obj (op (openChart B S hS F U O)) : Type u) →ₗ[Γ(chartScheme U, O)]
      (M.val.obj (op (openChart B S hS F V O')) : Type u) :=
    { toFun := fun x => chartRestrictLinear M
        (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O) x
      map_add' := map_add _
      map_smul' := fun r x => by
        change chartRestrictLinear M
              (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O)
            (openChartRingEquiv B S hS F hF U O r • x) =
          openChartRingEquiv B S hS F hF V O' ((chartSchemeMap g).appLE O O' hle r) •
            chartRestrictLinear M
              (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O) x
        rw [openChartRingEquiv_appLE B S hS F hF g hle r]
        exact (chartRestrictLinear M
          (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O)).map_smul
            (openChartRingEquiv B S hS F hF U O r) x }
  let cL := Scheme.Modules.sectionsLinearMap
    (restrictToChartSchemePullbackComparison B S hS F hF M g) O'
  have hbcg : IsBaseChange Γ(chartScheme V, O')
      ((cL.restrictScalars Γ(chartScheme U, O)).comp
        (Scheme.Modules.pullbackSectionₗ (chartSchemeMap g)
          (restrictToChartScheme B S hS F hF M U) O O' hle)) :=
    IsBaseChange.of_linearEquiv
      (Stacks.FlatSectionsDescent.isBaseChange_of_bijective_liftBaseChange f₁
        (bijective_liftBaseChange_of_isQuasicoherentOnSite_openChart B S hS F hF M hM g hle hO hO'
          (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) f₁ (fun _ => rfl)))
      (sectionsLinearEquivOfIso (restrictToChartSchemeIsoPushforward B S hS hF U M) O)
      (sectionsLinearEquivOfIso (restrictToChartSchemeIsoPushforward B S hS hF V M) O') _
      (fun a =>
        sectionsLinearEquivOfIso_restrictToChartSchemePullbackComparison_app_pullbackSection
          B S hS hF M g O O' hle a)
  rw [ConcreteCategory.isIso_iff_bijective]
  exact Stacks.BaseChange.bijective_of_isBaseChange_comp hbc cL (fun _ => rfl) hbcg

/-! ### The comparison is an isomorphism -/

/-- **The chart-restriction comparison of a quasi-coherent `𝒪_F`-module is an isomorphism.**
For a morphism `g : V ⟶ U` of étale charts of an algebraic space `F` and a module `M`
quasi-coherent on the small étale site, the comparison
`(chartSchemeMap g)^* (M|_U) ⟶ M|_V` is invertible.

This is the affine-local criterion
`AlgebraicGeometry.Space.isIso_restrictToChartSchemePullbackComparison_of_forall_isAffineOpen`
applied to
`AlgebraicGeometry.Space.isIso_restrictToChartSchemePullbackComparison_app_of_isAffineOpen`: the
affine Zariski opens of the smaller chart scheme lying inside the preimage of an affine Zariski
open of the larger form a basis, and the components over those are isomorphisms. -/
theorem isIso_restrictToChartSchemePullbackComparison_of_isQuasicoherentOnSite
    (M : Modules.{u, u} B S hS F hF) (hM : M.IsQuasicoherentOnSite)
    {U V : SmallEtale B S hS F} (g : V ⟶ U)
    [HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology (chartScheme V)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme V)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(openChartFunctor B S hS F U).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme U)) (SmallEtale.topology B S hS F)]
    [(openChartFunctor B S hS F V).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme V)) (SmallEtale.topology B S hS F)] :
    IsIso (restrictToChartSchemePullbackComparison B S hS F hF M g) :=
  isIso_restrictToChartSchemePullbackComparison_of_forall_isAffineOpen B S hS F hF M g
    (fun _O _O' hO hO' hle =>
      isIso_restrictToChartSchemePullbackComparison_app_of_isAffineOpen B S hS hF M hM g
        hO hO' hle)

end AlgebraicGeometry.Space

end
