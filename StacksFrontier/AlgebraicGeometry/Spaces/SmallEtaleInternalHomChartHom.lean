module

public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.AffineSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHom

/-!
# The sections of the internal Hom over an étale chart

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `G`,
`G'` be `𝒪_F`-modules.  A section of `𝓗om_{𝒪_F}(G, G')` over an étale chart `U` is, by the very
definition of `AlgebraicGeometry.Space.smallEtaleInternalHom`, a morphism of the underlying
presheaves of modules of the restrictions of `G` and `G'` to the slice of the small étale site at
`U`; since `CategoryTheory.SheafOfModules.forget` is fully faithful, that is exactly a morphism
`G|_U ⟶ G'|_U` of `𝒪_F|_U`-modules.  This is
`AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv`, and it holds at an arbitrary module
universe and with no hypothesis on `G`, `G'` or `U`.

For a *quasi-coherent* pair of modules the chart restrictions may be read on the Zariski site of
the chart's scheme, by `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv`, and over an *affine*
chart a morphism of quasi-coherent modules on an affine scheme is its own module of global
sections, by `Stacks.Algebraization.sectionsTop_bijective`.  Composing the three identifies the
sections of the internal Hom over an affine étale chart with the module of `Γ(V, 𝒪_V)`-linear
maps between the global sections of the chart restrictions:

`𝓗om_{𝒪_F}(G, G')(V) ≃ Hom_{Γ(V, 𝒪_V)}(Γ(V, G|_V), Γ(V, G'|_V))`.

That is `AlgebraicGeometry.Space.smallEtaleInternalHomAffineChartHomEquiv`.  It is the
algebraic-space analogue of `Stacks.Algebraization.internalHomEvaluationEquiv`, which is the same
identification over an affine open of a scheme, and it is what lets a statement of commutative
algebra about `Hom_A(M, N)` be read as a statement about the sections of the internal Hom over an
affine étale chart.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv` — **the sections of
  `𝓗om_{𝒪_F}(G, G')` over an étale chart `U` are the morphisms `G|_U ⟶ G'|_U`.**
* `AlgebraicGeometry.Space.smallEtaleInternalHomChartSchemeHomEquiv` — for quasi-coherent
  modules, the morphisms of the chart restrictions read on the chart's scheme.
* `AlgebraicGeometry.Space.smallEtaleInternalHomAffineChartHomEquiv` — **over an affine étale
  chart, the `Γ(V, 𝒪_V)`-linear maps between the global sections of the chart restrictions.**

## Main results

* `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv_val_app` and
  `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv_symm_val_app` — the identification
  of the chart sections with the morphisms of the restrictions does not move the components: it
  is the identity on them, in both directions.

## Implementation notes

The first identification is the full faithfulness of `CategoryTheory.SheafOfModules.forget` and
nothing else; the implicit arguments of
`CategoryTheory.Functor.FullyFaithful.homEquiv` are given explicitly because the carrier of
`(smallEtaleInternalHom … G G').val.obj (op U)` is the Hom-type of the *forgotten* restrictions
only definitionally, and unification does not post that equation on its own.

No `@[stacks]` attribute is carried.  The internal Hom presheaf is Stacks 04TT and its sheaf
property Stacks 03EM, both of which sit on their own declarations; what is below reads off the
definition at one ringed site and composes identifications which are themselves already available.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
-/

@[expose] public section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The sections of `𝓗om_{𝒪_F}(G, G')` over an étale chart `U` are the morphisms
`G|_U ⟶ G'|_U`.**

A section over `U` is a morphism of the underlying presheaves of modules of the restrictions to
the slice at `U`, by the definition of `AlgebraicGeometry.Space.smallEtaleInternalHom`, and
`CategoryTheory.SheafOfModules.forget` is fully faithful.  No hypothesis is needed on `G`, `G'`
or `U`, and the module universe is arbitrary. -/
noncomputable def smallEtaleInternalHomChartHomEquiv (G G' : Modules.{u, m} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    (smallEtaleInternalHom B S hS F hF G G').val.obj (op U) ≃ (G.over U ⟶ G'.over U) :=
  ((SheafOfModules.fullyFaithfulForget _).homEquiv (X := G.over U) (Y := G'.over U)).symm

/-- The identification of the chart sections of the internal Hom with the morphisms of the
restrictions is the identity on components. -/
theorem smallEtaleInternalHomChartHomEquiv_val_app (G G' : Modules.{u, m} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C)
    (α : (smallEtaleInternalHom B S hS F hF G G').val.obj (op U))
    (W : (Over U)ᵒᵖ) :
    (smallEtaleInternalHomChartHomEquiv B S hS F hF G G' U α).val.app W = α.app W := rfl

/-- The inverse identification is also the identity on components. -/
theorem smallEtaleInternalHomChartHomEquiv_symm_val_app (G G' : Modules.{u, m} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) (φ : G.over U ⟶ G'.over U)
    (W : (Over U)ᵒᵖ) :
    ((smallEtaleInternalHomChartHomEquiv B S hS F hF G G' U).symm φ).app W =
      φ.val.app W := rfl

variable (X : AlgebraicSpaces B S hS)

/-- **The sections of the internal Hom of two quasi-coherent `𝒪_X`-modules over an étale chart,
read on the chart's scheme.**  The chart restrictions of quasi-coherent modules are
quasi-coherent sheaves of modules on the Zariski site of the chart's scheme, by Descent,
Proposition 03DX (2), and the transport of Hom-sets along that reading is
`AlgebraicGeometry.Space.chartSchemeModuleHomEquiv`. -/
noncomputable def smallEtaleInternalHomChartSchemeHomEquiv
    (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) :
    (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V) ≃
      (chartSchemeModule B S hS X M hM V ⟶ chartSchemeModule B S hS X N hN V) :=
  (smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 M N V).trans
    (chartSchemeModuleHomEquiv B S hS X M N hM hN V)

/-- **The affine-chart identification of the sections of the internal Hom.**

Over an étale chart whose scheme is affine, the sections of `𝓗om_{𝒪_X}(M, N)` are the
`Γ(V, 𝒪_V)`-linear maps from the global sections of the chart restriction of `M` to those of the
chart restriction of `N`:

`𝓗om_{𝒪_X}(M, N)(V) ≃ Hom_{Γ(V, 𝒪_V)}(Γ(V, M|_V), Γ(V, N|_V))`.

This is the algebraic-space analogue of `Stacks.Algebraization.internalHomEvaluationEquiv`, and
it is the step by which a statement of commutative algebra about `Hom_A(M, N)` — such as the
Artin--Rees comparison of Stacks 09BB — is read as a statement about the sections of the internal
Hom over an affine étale chart.  The affineness of the chart enters only through
`Stacks.Algebraization.sectionsTop_bijective`, that a morphism of quasi-coherent modules on an
affine scheme is its own map of global sections. -/
noncomputable def smallEtaleInternalHomAffineChartHomEquiv
    (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V)) :
    (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V) ≃
      (Γ(chartSchemeModule B S hS X M hM V, ⊤) →ₗ[Γ(chartScheme V, ⊤)]
        Γ(chartSchemeModule B S hS X N hN V, ⊤)) :=
  haveI := hV
  haveI := isQuasicoherent_chartSchemeModule B S hS X M hM V
  (smallEtaleInternalHomChartSchemeHomEquiv B S hS X M N hM hN V).trans
    (Equiv.ofBijective _ (Stacks.Algebraization.sectionsTop_bijective
      (chartSchemeModule B S hS X M hM V) (chartSchemeModule B S hS X N hN V)))

/-- The affine-chart identification is the global-sections component of the morphism of chart
restrictions which the chart identification produces. -/
theorem smallEtaleInternalHomAffineChartHomEquiv_apply
    (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V)) :
    smallEtaleInternalHomAffineChartHomEquiv B S hS X M N hM hN V hV α =
      ((smallEtaleInternalHomChartSchemeHomEquiv B S hS X M N hM hN V α).val.app
        (op ⊤)).hom := rfl

end AlgebraicGeometry.Space

end
