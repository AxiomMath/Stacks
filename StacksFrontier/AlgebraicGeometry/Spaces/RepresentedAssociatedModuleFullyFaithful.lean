module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparison

/-!
# `M ↦ Mᵃ` on the small étale site of a represented algebraic space is fully faithful

Let `U` be an object of the big fppf site over a scheme `S`.  An `𝒪`-module on the scheme
underlying `U` becomes an `𝒪`-module on the small étale site of the represented algebraic space
`yoneda.obj U` by `AlgebraicGeometry.Space.representedAssociatedModule`, which is the
associated-module functor of [Stacks Project, Tag 03DU] (4) on the small étale site of the
scheme followed by the transport along the identification of that site with the small étale site
of `yoneda.obj U`.  This file records that the resulting map on morphisms is **bijective** as
soon as the target module is quasi-coherent, with no further hypothesis.

Both halves are proved and neither carries a hypothesis:

* the small étale half of [Stacks Project, Tag 0GN7] is unconditional, because
  [Stacks Project, Tag 070S] (2) for the small étale site is proved —
  `AlgebraicGeometry.SmallEtale.sectionsComparisonSheafifiesToIso` — and therefore so is
  `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`: the unit of the associated-module
  adjunction is an isomorphism at every quasi-coherent module;
* the transport is the functor of an equivalence of module categories,
  `Stacks.SheafOfModules.reindexEquivalence` along
  `AlgebraicGeometry.Space.representedSmallEtaleEquivalence`, hence fully faithful.

Only the *target* has to be quasi-coherent.  That is because the bijection is
`CategoryTheory.Adjunction.bijective_map_of_isIso_unit_app`, which asks for invertibility of the
unit at the target alone — the same shape in which
`AlgebraicGeometry.SmallEtale.bijective_associatedModule_map_free` is stated.

## Main results

* `AlgebraicGeometry.SmallEtale.bijective_associatedModule_map_of_isQuasicoherent`: **the small
  étale half of [Stacks Project, Tag 0GN7] in hom-set form**, `β ↦ βᵃ` bijective for an
  arbitrary source and a quasi-coherent target.
* `AlgebraicGeometry.Space.bijective_representedAssociatedModule_map`: the same for
  `AlgebraicGeometry.Space.representedAssociatedModule`, on the small étale site of the
  represented algebraic space.
* `Stacks.AlgebraicGeometry.ModuleLimits.bijective_appTopₗ`: the Zariski companion, that
  morphisms of quasi-coherent sheaves of modules on an affine scheme are exactly the
  `Γ(X, ⊤)`-linear maps of their global sections.  Both halves of it are proved
  (`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top` and `…exists_hom_app_top_eq`); what
  is added here is the linear form `…appTopₗ` of the action on global sections and the packaging
  as one bijection.
* `AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap`: **the two composed** —
  the morphisms `Mᵃ ⟶ Nᵃ` on the small étale site of a represented algebraic space with affine
  underlying scheme are the `Γ(U, ⊤)`-linear maps of global sections, which is exactly the shape
  of `AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`.

## Why this is wanted

It is the passage from an isomorphism of sheaves to a bijection of *morphisms* that the source
comparison of step (II) of [Stacks Project, Tag 04AM] needs.  The acting sheaf of
[Stacks Project, Tag 061D] has the small-étale `a^*Ω_{Y/B}` as the source of its sections, while
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` has the Zariski
`Γ(a^*Ω_{W/V}, ⊤)`; `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso` exhibits
the former, restricted to a chart which factors through the chart square, as the associated
module of the latter, and what then identifies the two groups of morphisms is the statement
proved here.

**The step does not go through the slice at an *affine* chart**, by
`AlgebraicGeometry.Space.SmallEtale.bijective_associatedModuleMap_slice`, which would carry the
fpqc sheaf condition of [Stacks Project, Tag 03DT].  That sheaf condition is in any case
proved (Tag 03DT itself is
`AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'`, and its slice instance is
`AlgebraicGeometry.Space.SmallEtale.isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent`), and the
detour through a slice is unnecessary — Tag 0GN7's small étale half holds over an arbitrary
scheme, with no affineness, and that is what is used here.

## Implementation notes

The fullness of the transport is supplied by a `haveI` with the equivalence written out, exactly
as `AlgebraicGeometry.Space.faithful_representedModulePushforward` writes it out for
faithfulness: instance search does not produce it, the two structure sheaves being written in
two spellings which it does not identify.

The composite's bijectivity is `Function.Bijective.comp`, with the outer factor's domain and
codomain written out.  No equation between
`AlgebraicGeometry.Space.representedAssociatedModule` and its two factors is needed, that
functor being their composite definitionally.

`Stacks.AlgebraicGeometry.ModuleLimits.appTopₗ` has to be introduced because
`AlgebraicGeometry.Scheme.Modules.Hom.app` lands in `AddCommGrpCat`: its `hom` is an
`AddMonoidHom`, not the `Γ(X, ⊤)`-linear map that
`Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq` quantifies over.  The component of
the underlying morphism of presheaves of modules at `⊤` is that linear map on the nose, so
`…appTopₗ_apply` is `rfl` and the two library statements apply to it with no transport.

The two bijections of
`AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap` share the domain `M ⟶ N`,
so the composite is one `CategoryTheory.Equiv.trans` of an `Equiv.ofBijective` with the inverse
of another; no map between the two codomains is constructed, and in particular no choice of a
preimage is made outside `Equiv.ofBijective` itself.

## References

* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The small étale half of [Stacks Project, Tag 0GN7] in hom-set form.**  For an arbitrary
`𝒪_S`-module `M` and a *quasi-coherent* `𝒪_S`-module `N`, the map `β ↦ βᵃ` from `M ⟶ N` to
`Mᵃ ⟶ Nᵃ` on the small étale site of `S` is bijective.

This is `CategoryTheory.Adjunction.bijective_map_of_isIso_unit_app` at the associated-module
adjunction, whose hypothesis is invertibility of the unit at the target only; that is
`AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`, which carries nothing. -/
theorem bijective_associatedModule_map_of_isQuasicoherent
    (M N : S.Modules) [N.IsQuasicoherent] :
    Function.Bijective (fun β : M ⟶ N => (associatedModule B S hS).map β) :=
  (associatedModuleAdjunction B S hS).bijective_map_of_isIso_unit_app M
    (unitIsoOnQuasicoherent B S hS ⟨N, inferInstance⟩)

end AlgebraicGeometry.SmallEtale

namespace Stacks.AlgebraicGeometry.ModuleLimits

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} [IsAffine X]

/-- **A morphism of sheaves of modules on a scheme, read on global sections as a linear map.**
`AlgebraicGeometry.Scheme.Modules.Hom.app` lands in `AddCommGrpCat`, so it supplies only the
additive map; the component of the underlying morphism of presheaves of modules at `⊤` is already
`Γ(X, ⊤)`-linear, and this is that component. -/
def appTopₗ {F G : X.Modules} (χ : F ⟶ G) :
    ↑Γ(F, (⊤ : X.Opens)) →ₗ[Γ(X, (⊤ : X.Opens))] ↑Γ(G, (⊤ : X.Opens)) :=
  (χ.val.app (op ⊤)).hom

omit [IsAffine X] in
/-- The linear map of
`Stacks.AlgebraicGeometry.ModuleLimits.appTopₗ` is the action on global sections, so the
statements of this file apply to
`AlgebraicGeometry.Scheme.Modules.Hom.app` at `⊤` unchanged. -/
theorem appTopₗ_apply {F G : X.Modules} (χ : F ⟶ G) (a : Γ(F, (⊤ : X.Opens))) :
    appTopₗ χ a = χ.app ⊤ a := rfl

/-- **Morphisms of quasi-coherent sheaves of modules on an affine scheme are exactly the
`Γ(X, ⊤)`-linear maps of their global sections**, as one bijection.  Injectivity is
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top` and surjectivity is
`Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq`; this packages the two so that the
resulting `CategoryTheory.Equiv` can be composed with other hom-set bijections. -/
theorem bijective_appTopₗ {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Function.Bijective (fun χ : F ⟶ G => appTopₗ χ) :=
  ⟨fun _ _ h => hom_ext_of_app_top fun a => DFunLike.congr_fun h a,
    fun w => ⟨(exists_hom_app_top_eq w).choose,
      LinearMap.ext (exists_hom_app_top_eq w).choose_spec⟩⟩

end Stacks.AlgebraicGeometry.ModuleLimits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`M ↦ Mᵃ` on the small étale site of a represented algebraic space is bijective on
morphisms into a quasi-coherent module.**  For an object `U` of the big fppf site over `S`, an
arbitrary `𝒪`-module `M` on the scheme underlying `U` and a quasi-coherent one `N`, the map
`β ↦ βᵃ` from `M ⟶ N` to the morphisms of the two `𝒪`-modules on the small étale site of
`yoneda.obj U` is bijective.

`AlgebraicGeometry.Space.representedAssociatedModule` is the associated-module functor of
[Stacks Project, Tag 03DU] (4) on the small étale site of the scheme followed by the transport
along `AlgebraicGeometry.Space.representedSmallEtaleEquivalence`.  The first factor is bijective
on these hom-sets by
`AlgebraicGeometry.SmallEtale.bijective_associatedModule_map_of_isQuasicoherent`, the small
étale half of [Stacks Project, Tag 0GN7]; the second is the functor of an equivalence of module
categories, hence fully faithful. -/
theorem bijective_representedAssociatedModule_map (U : BigFppfOver B S hS)
    (hF : IsAlgebraicSpace B S hS (yoneda.obj U))
    (M N : ((BigFppfOver.toScheme B S hS).obj U).Modules) [N.IsQuasicoherent] :
    Function.Bijective (fun β : M ⟶ N =>
      (representedAssociatedModule B S hS U hF).map β) := by
  have : (representedModulePushforward B S hS U).Full :=
    Equivalence.full_functor (Stacks.SheafOfModules.reindexEquivalence
      (J' := SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property))
  have h₂ : Function.Bijective
      (fun γ : (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M ⟶
          (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj N =>
        (representedModulePushforward B S hS U).map γ) :=
    ⟨fun _ _ h => (representedModulePushforward B S hS U).map_injective h,
      fun k => ⟨(representedModulePushforward B S hS U).preimage k, Functor.map_preimage _ _⟩⟩
  exact h₂.comp
    (_root_.AlgebraicGeometry.SmallEtale.bijective_associatedModule_map_of_isQuasicoherent
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property M N)

/-- **The acting group of a chart presentation, as the morphisms of associated modules on the
small étale site of the chart.**  For an object `U` of the big fppf site whose underlying scheme
is affine and quasi-coherent `𝒪`-modules `M`, `N` on it, the morphisms
`Mᵃ ⟶ Nᵃ` of `𝒪`-modules on the small étale site of `yoneda.obj U` are exactly the
`Γ(U, ⊤)`-linear maps `Γ(M, ⊤) ⟶ Γ(N, ⊤)`.

This is the shape `AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` has, and it is
the two bijections above composed: `β ↦ βᵃ` by
`AlgebraicGeometry.Space.bijective_representedAssociatedModule_map` and `χ ↦ χ|_⊤` by
`Stacks.AlgebraicGeometry.ModuleLimits.bijective_appTopₗ`, both with domain `M ⟶ N`. -/
def representedAssociatedModuleHomEquivLinearMap (U : BigFppfOver B S hS)
    (hF : IsAlgebraicSpace B S hS (yoneda.obj U))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (M N : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    ((representedAssociatedModule B S hS U hF).obj M ⟶
        (representedAssociatedModule B S hS U hF).obj N) ≃
      (↑Γ(M, (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens)) →ₗ[
          Γ((BigFppfOver.toScheme B S hS).obj U,
            (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens))]
        ↑Γ(N, (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens))) :=
  (Equiv.ofBijective _ (bijective_representedAssociatedModule_map B S hS U hF M N)).symm.trans
    (Equiv.ofBijective _ Stacks.AlgebraicGeometry.ModuleLimits.bijective_appTopₗ)

end AlgebraicGeometry.Space

end
