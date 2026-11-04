module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomAffineChartEvaluation

/-!
# The affine-chart reading of the internal Hom is a bijection

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `M`, `N` be
quasi-coherent `𝒪_X`-modules and let `V` be an étale chart of `X` whose scheme is affine.
`AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluation` reads a section of
`𝓗om_{𝒪_X}(M, N)` over `V` as a `𝒪_X(V)`-linear map `M(V) → N(V)`, and over an affine chart that
reading is a bijection

`𝓗om_{𝒪_X}(M, N)(V) ≃ Hom_{𝒪_X(V)}(M(V), N(V))`.

The change of coordinates which gives it is the pair of conjugations
`AlgebraicGeometry.Space.chartOfTopHomEquiv` and `AlgebraicGeometry.Space.chartTopHomEquiv`, each
semilinear over a surjective ring map and neither comparable with the other; the bijection
follows once both conjugates are shown to be the *same* object, namely the component of the
section at the chart which the whole of the chart's scheme cuts out, which is
`AlgebraicGeometry.Space.chartOverOfTopEvaluation`.

## Main results

* `Stacks.Module.eq_of_homEquivOfSemilinear_eq`: a linear map is recognized from its conjugate,
  for a conjugation given by an *equation* rather than written out.
* `AlgebraicGeometry.Space.chartOfTopHomEquiv_eq` and
  `AlgebraicGeometry.Space.chartTopHomEquiv_eq`: each conjugation is the conjugation it is defined
  to be, stated unapplied.
* `AlgebraicGeometry.Space.chartOfTopRestrict_hom_smallEtaleInternalHomChartEvaluation`: the
  `V`-side intertwining, at the spelling that conjugation is semilinear over.  **This is the whole
  hypothesis the `V`-side needs.**
* `AlgebraicGeometry.Space.chartTopSectionsFun_eq`,
  `AlgebraicGeometry.Space.chartTopModCast_smallEtaleInternalHomAffineChartHomEquiv`,
  `AlgebraicGeometry.Space.chartOverOfTop_app_chartTopSectionsFun` and
  `AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv_top_eq_chartTopSectionsFun`: the
  first and last links of the chart-scheme intertwining, and the two bridges between the spellings
  of the global sections which they cross.
* `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv_val_app_chartOverOfTop`: the
  transported morphism and the section have the same component at the chart which `⊤` cuts out,
  stated at the one spelling of the chart at which it elaborates.
* `AlgebraicGeometry.Space.chartOverOfTopEvaluation`: **the object both conjugates are shown to
  be** — the component of the section at the chart which `⊤` cuts out, declared at the spellings
  the two conjugations use.
* `AlgebraicGeometry.Space.chartOverOfTopEvaluation_chartTopSectionsModCast`: the two bridges
  composed, which is the one step where the two spellings of the sections meet.
* `AlgebraicGeometry.Space.chartOverOfTopEvaluation_chartTopSectionsFun`: the chart-scheme
  intertwining.  **This is the whole hypothesis the chart-scheme side needs.**
* `AlgebraicGeometry.Space.bijective_smallEtaleInternalHomChartEvaluation`: **the affine-chart
  reading is a bijection**, with
  `AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluation_eq` exhibiting it as the composite
  of the affine-chart identification of the sections and the two halves.

## Implementation notes

**`Stacks.Module.homEquivOfSemilinear_eq` is never applied to one of the two conjugations with
its data left to unification, and its conclusion is never *stated*.**  At the default
budget, which is the only budget this library allows:

* building the term `Stacks.Module.homEquivOfSemilinear_eq … ψ φ h` at either conjugation, with no
  expected type — as the body of a `have` with no ascription — is free, and its type is already
  the identity wanted;
* matching that type against a *stated* `chartOfTopHomEquiv … ψ = φ` exhausts the budget in
  `whnf`, with the data supplied explicitly as well as left to unification, with the conjugation's
  delta equation supplied as a hypothesis, and with the four module spellings pinned by name;
* the statements themselves elaborate: both conjugate identities check with their proofs left
  out, so what is over budget is the match and nothing else.

`Stacks.Module.eq_of_homEquivOfSemilinear_eq` is therefore stated with the conjugation as a
variable `E` and an equation `hE` identifying it, so that a use site supplies the `rfl` of a
definition — `AlgebraicGeometry.Space.chartOfTopHomEquiv_eq` or
`AlgebraicGeometry.Space.chartTopHomEquiv_eq`, both free *unapplied* — and nothing is unfolded.

The two `Q₁`, `Q₂` of `AlgebraicGeometry.Space.chartOfTopHomEquiv_eq` are pinned by name.  Without
that, the codomain of `PresheafOfModules.map` fixes them at the
`CategoryTheory.ModuleCat.restrictScalars` spelling before the equation's left-hand side can pin
them at the plain one, and instance search finds no `Module` over
`AlgebraicGeometry.Space.chartRing` there.

**The middle link of the chart-scheme intertwining, and the two bridges which carry it.**  That
link is
`AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply`
at the Zariski open `⊤` — the chart which `⊤` cuts out *is*
`AlgebraicGeometry.Space.openChartOfComparisonOver … V ⊤`, syntactically — once the component of
the transported morphism there is recognized as the component of the section at
`AlgebraicGeometry.Space.chartOverOfTop`.  **That recognition is free and crossing it is not**, so
the comparison it needs is made once, in a declaration which does nothing else, and is never
written inside another application.  At the default budget, which is the only budget this
library allows:

* the component of the section has for its domain the slice-restricted spelling
  `((restrFun 𝒪_V).obj M.val).obj (op (chartOverOfTop … V))` over the scalars
  `(ORestr 𝒪_V).obj (op (chartOverOfTop … V))`, whereas the sections identification at `⊤` lands in
  `CategoryTheory.ModuleCat.restrictScalars (chartSectionsRingHom … V ⊤)` of
  `M.val.obj (op (openChartOfComparison … V ⊤))` over `AlgebraicGeometry.Space.chartRing` there.
  Comparing the two is what costs: crossing the recognition on an element — by
  `congrArg (fun k => k.hom z)`, by `DFunLike.congr_fun (congrArg ModuleCat.Hom.hom …)`, and at `z`
  either of the two sections spellings — exhausts the budget, in `whnf` and in `isDefEq`, and so
  does *stating* the component formula at `⊤`, although the same statement with the Zariski
  open left a variable is free;
* the two comparisons are therefore carried by `AlgebraicGeometry.Space.chartOverOfTopEvaluation`,
  which declares the component at the plain spelling, and by
  `AlgebraicGeometry.Space.chartTopSectionsModCast`, which is the identity on the sections — the
  device of `AlgebraicGeometry.Space.chartTopModCast`.  Each is free on its own, and
  `AlgebraicGeometry.Space.chartOverOfTopEvaluation_chartTopSectionsModCast` composes them in a
  single `rfl`, after which the middle link is three `Eq.trans` and the whole file is seconds;
* `AlgebraicGeometry.Space.chartOverOfTopEvaluation_chartTopSectionsModCast` and
  `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv_chartTopSectionsFunVal` bind the
  chart as `(smallEtaleRingedSite … ).C`.  At `AlgebraicGeometry.Space.SmallEtale` instance search
  reports no `CategoryTheory.Category.{u, u + 1} (Over V)` and the `(Over V)ᵒᵖ` argument of the
  transported morphism's `.val.app` does not elaborate at all.  Only the *statements* need that
  binding: `AlgebraicGeometry.Space.chartOverOfTopEvaluation_chartTopSectionsFunVal` is the same
  theorem at `AlgebraicGeometry.Space.SmallEtale`, and applying an elaborated statement needs no
  instance.

No `@[stacks]` attribute is carried: the internal Hom presheaf is Stacks 04TT, its sheaf property
Stacks 03EM and the affine comparison Stacks 03DX, each of which sits on its own declaration, and
what is below is a change of coordinates between two existing readings.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks.Module

variable {R R' : Type*} [Ring R] [Ring R']
    {P₁ P₂ Q₁ Q₂ : Type*}
    [AddCommGroup P₁] [AddCommGroup P₂] [AddCommGroup Q₁] [AddCommGroup Q₂]
    [Module R P₁] [Module R P₂] [Module R' Q₁] [Module R' Q₂]

/-- **A linear map is recognized from its conjugate, for a conjugation given by an equation.**

This is `Stacks.Module.homEquivOfSemilinear_eq` for an equivalence `E` which is *known to be*
the conjugation rather than written as it: the hypothesis `hE` is supplied at the use site, where
it is the `rfl` of a definition, and nothing then has to be unfolded.  Applying
`Stacks.Module.homEquivOfSemilinear_eq` to such a definition directly does not elaborate; see the
implementation notes of this file. -/
theorem eq_of_homEquivOfSemilinear_eq {σ : R →+* R'} {hσ : Function.Surjective σ}
    {f₁ : P₁ → Q₁} {ha₁ : ∀ x y : P₁, f₁ (x + y) = f₁ x + f₁ y}
    {hb₁ : Function.Bijective f₁} {hs₁ : ∀ (r : R) (x : P₁), f₁ (r • x) = σ r • f₁ x}
    {f₂ : P₂ → Q₂} {ha₂ : ∀ x y : P₂, f₂ (x + y) = f₂ x + f₂ y}
    {hb₂ : Function.Bijective f₂} {hs₂ : ∀ (r : R) (x : P₂), f₂ (r • x) = σ r • f₂ x}
    {E : (P₁ →ₗ[R] P₂) ≃ (Q₁ →ₗ[R'] Q₂)}
    (hE : E = homEquivOfSemilinear σ hσ f₁ ha₁ hb₁ hs₁ f₂ ha₂ hb₂ hs₂)
    (ψ : P₁ →ₗ[R] P₂) (φ : Q₁ →ₗ[R'] Q₂) (h : ∀ x : P₁, φ (f₁ x) = f₂ (ψ x)) :
    E ψ = φ :=
  (congrArg (fun e => e ψ) hE).trans
    (homEquivOfSemilinear_eq σ hσ f₁ ha₁ hb₁ hs₁ f₂ ha₂ hb₂ hs₂ ψ φ h)

end Stacks.Module

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The two conjugations, as conjugations -/

/-- `AlgebraicGeometry.Space.chartOfTopHomEquiv` is the conjugation it is defined to be, by `rfl`.
Stated unapplied, which is where the comparison is free; the two codomains are pinned by name,
for the reason the implementation notes give. -/
theorem chartOfTopHomEquiv_eq (M N : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) :
    chartOfTopHomEquiv B S hS X M N V =
      Stacks.Module.homEquivOfSemilinear
        (Q₁ := M.val.obj (op (openChartOfComparison B S hS X V ⊤)))
        (Q₂ := N.val.obj (op (openChartOfComparison B S hS X V ⊤)))
        (chartRestrict (hF := X.2) (chartOfTopHom B S hS X V))
        (surjective_chartOfTopChartRestrict B S hS X V)
        ((M.val.map (op (chartOfTopHom B S hS X V))).hom)
        (fun y z => map_add (M.val.map (op (chartOfTopHom B S hS X V))).hom y z)
        (bijective_chartOfTopRestrict B S hS X M V)
        (fun r y => M.val.map_smul (op (chartOfTopHom B S hS X V)) r y)
        ((N.val.map (op (chartOfTopHom B S hS X V))).hom)
        (fun y z => map_add (N.val.map (op (chartOfTopHom B S hS X V))).hom y z)
        (bijective_chartOfTopRestrict B S hS X N V)
        (fun r y => N.val.map_smul (op (chartOfTopHom B S hS X V)) r y) :=
  rfl

/-- `AlgebraicGeometry.Space.chartTopHomEquiv` is the conjugation it is defined to be, by `rfl`.
Stated unapplied, which is where the comparison is free. -/
theorem chartTopHomEquiv_eq (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) :
    chartTopHomEquiv B S hS X M N hM hN V =
      Stacks.Module.homEquivOfSemilinear (chartTopSectionsRingHom B S hS X V)
        (surjective_chartTopSectionsRingHom B S hS X V)
        (chartTopSectionsFun B S hS X M hM V) (chartTopSectionsFun_add B S hS X M hM V)
        (bijective_chartTopSectionsFun B S hS X M hM V)
        (chartTopSectionsFun_smul B S hS X M hM V)
        (chartTopSectionsFun B S hS X N hN V) (chartTopSectionsFun_add B S hS X N hN V)
        (bijective_chartTopSectionsFun B S hS X N hN V)
        (chartTopSectionsFun_smul B S hS X N hN V) :=
  rfl

/-! ### The intertwinings, link by link -/

/-- **Naturality of the section along `AlgebraicGeometry.Space.chartOverOfTopIso`, at the spelling
the `V`-side conjugation is semilinear over.**

This is `AlgebraicGeometry.Space.chartOfTopRestrict_smallEtaleInternalHomChartEvaluation` with the
restriction maps applied through `CategoryTheory.ModuleCat.Hom.hom`, which is the form the
hypothesis of `Stacks.Module.homEquivOfSemilinear_eq` takes at
`AlgebraicGeometry.Space.chartOfTopHomEquiv`. -/
theorem chartOfTopRestrict_hom_smallEtaleInternalHomChartEvaluation
    (M N : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V))
    (y : M.val.obj (op V)) :
    (α.app (op (chartOverOfTop B S hS X V))).hom
        ((M.val.map (op (chartOfTopHom B S hS X V))).hom y) =
      (N.val.map (op (chartOfTopHom B S hS X V))).hom
        (smallEtaleInternalHomChartEvaluation B S hS X.1 X.2 M N V α y) :=
  chartOfTopRestrict_smallEtaleInternalHomChartEvaluation B S hS X M N V α y

/-- The global sections of the chart restriction, read through
`AlgebraicGeometry.Space.chartTopSectionsFun`, are
`AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv` at `⊤` of the one bridge between
the two spellings of those sections.  This is the step at which the component formula at the
composite sections identification becomes applicable to the chart-scheme conjugation. -/
theorem chartTopSectionsFun_eq (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (y : Γ(chartSchemeModule B S hS X M hM V, ⊤)) :
    chartTopSectionsFun B S hS X M hM V y =
      chartSchemeModuleSectionsLinearEquiv B S hS X M hM V ⊤
        (chartTopModCast B S hS X M hM V y) :=
  rfl

/-- The affine-chart reading of a section is the `⊤`-component of the morphism of chart
restrictions which the Hom-set transport produces from it, across the bridge between the two
spellings of the global sections. -/
theorem chartTopModCast_smallEtaleInternalHomAffineChartHomEquiv
    (M N : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (hV : IsAffine (chartScheme V))
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V))
    (y : Γ(chartSchemeModule B S hS X M hM V, ⊤)) :
    chartTopModCast B S hS X N hN V
        (smallEtaleInternalHomAffineChartHomEquiv B S hS X M N hM hN V hV α y) =
      ((chartSchemeModuleHomEquiv B S hS X M N hM hN V
          (smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 M N V α)).val.app (op ⊤)).hom
        (chartTopModCast B S hS X M hM V y) :=
  rfl

/-- The component of a section of the internal Hom at the chart which `⊤` cuts out, applied to
the chart-scheme reading of a section, is that component applied to the composite sections
identification of the bridged section.  The first link of the chart-scheme intertwining. -/
theorem chartOverOfTop_app_chartTopSectionsFun (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V))
    (y : Γ(chartSchemeModule B S hS X M hM V, ⊤)) :
    (α.app (op (chartOverOfTop B S hS X V))).hom (chartTopSectionsFun B S hS X M hM V y) =
      (α.app (op (chartOverOfTop B S hS X V))).hom
        (chartSchemeModuleSectionsLinearEquiv B S hS X M hM V ⊤
          (chartTopModCast B S hS X M hM V y)) :=
  congrArg (α.app (op (chartOverOfTop B S hS X V))).hom
    (chartTopSectionsFun_eq B S hS X M hM V y)

/-- The composite sections identification at `⊤` of the `⊤`-component of the transported
morphism is the chart-scheme reading of the affine-chart reading.  The last link of the
chart-scheme intertwining. -/
theorem chartSchemeModuleSectionsLinearEquiv_top_eq_chartTopSectionsFun
    (M N : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (hV : IsAffine (chartScheme V))
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V))
    (y : Γ(chartSchemeModule B S hS X M hM V, ⊤)) :
    chartSchemeModuleSectionsLinearEquiv B S hS X N hN V ⊤
        (((chartSchemeModuleHomEquiv B S hS X M N hM hN V
            (smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 M N V α)).val.app (op ⊤)).hom
          (chartTopModCast B S hS X M hM V y)) =
      chartTopSectionsFun B S hS X N hN V
        (smallEtaleInternalHomAffineChartHomEquiv B S hS X M N hM hN V hV α y) :=
  ((congrArg (chartSchemeModuleSectionsLinearEquiv B S hS X N hN V ⊤)
      (chartTopModCast_smallEtaleInternalHomAffineChartHomEquiv B S hS X M N hM hN V hV α
        y)).symm).trans
    (chartTopSectionsFun_eq B S hS X N hN V _).symm

/-- **The transported morphism and the section have the same component at the chart which `⊤` cuts
out.**  This is `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv_val_app`, which is
`rfl`, at that object — the chart which `⊤` cuts out *is*
`AlgebraicGeometry.Space.chartOverOfTop`, syntactically.

The chart is bound at the spelling `(smallEtaleRingedSite … ).C` and not at
`AlgebraicGeometry.Space.SmallEtale`: at the latter, instance search reports no
`CategoryTheory.Category.{u, u + 1} (Over V)` and neither the `(Over V)ᵒᵖ` argument nor the
`.val.app` of the transported morphism elaborates. -/
theorem smallEtaleInternalHomChartHomEquiv_val_app_chartOverOfTop
    (M N : Modules.{u, u} B S hS X.1 X.2) (V : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V)) :
    (smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 M N V α).val.app
        (op (openChartOfComparisonOver B S hS X V ⊤)) =
      α.app (op (chartOverOfTop B S hS X V)) :=
  smallEtaleInternalHomChartHomEquiv_val_app B S hS X.1 X.2 M N V α
    (op (chartOverOfTop B S hS X V))


/-! ### The two bridges which let the intertwining cross the restriction of scalars -/

/-- **The component of a section of the internal Hom at the chart which `⊤` cuts out, as a linear
map over the functions on that chart.**

This is `AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluation` at
`AlgebraicGeometry.Space.chartOverOfTop` in place of `Over.mk (𝟙 V)`: the component of a morphism
of the restrictions to the slice at the object which the whole of the chart's scheme cuts out,
declared at the spellings the two conjugations use — domain `M(V_⊤)`, codomain `N(V_⊤)` and
scalars `AlgebraicGeometry.Space.chartRing` there — rather than at the slice-restricted presheaf
spelling the component carries.

It is the bridge the implementation notes call for: a once-and-never-reused carrier of the
comparison between the two spellings, so that the comparison is made here, where both types are
written out and nothing else is going on, and never inside another application.  Both conjugates
of the change of coordinates are shown to be *this* linear map. -/
def chartOverOfTopEvaluation (M N : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1)
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V)) :
    M.val.obj (op (openChartOfComparison B S hS X V ⊤)) →ₗ[
        chartRing B S hS X.1 X.2 (openChartOfComparison B S hS X V ⊤)]
      N.val.obj (op (openChartOfComparison B S hS X V ⊤)) :=
  (α.app (op (chartOverOfTop B S hS X V))).hom

/-- The sections of `M` over the chart which `⊤` cuts out, from the spelling with the scalars
restricted along `AlgebraicGeometry.Space.chartSectionsRingHom` — which is the codomain of
`AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv` — to the plain spelling.  The
identity.

This is the second bridge, for the *elements* which the first one's linear map is applied to;
compare `AlgebraicGeometry.Space.chartTopModCast`. -/
def chartTopSectionsModCast (M : Modules.{u, u} B S hS X.1 X.2)
    (_hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) :
    (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X V ⊤)).obj
        (M.val.obj (op (openChartOfComparison B S hS X V ⊤))) →
      M.val.obj (op (openChartOfComparison B S hS X V ⊤)) := id

/-- The global sections of the chart restriction, read through
`AlgebraicGeometry.Space.chartTopSectionsFunVal`, are the composite sections identification at `⊤`
across the bridge for the restriction of scalars.  By `rfl`: that is how
`AlgebraicGeometry.Space.chartTopSectionsFunVal` is defined. -/
theorem chartTopSectionsFunVal_eq_chartTopSectionsModCast (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (x : (chartSchemeModule B S hS X M hM V).val.obj (op ⊤)) :
    chartTopSectionsFunVal B S hS X M hM V x =
      chartTopSectionsModCast B S hS X M hM V
        (chartSchemeModuleSectionsLinearEquiv B S hS X M hM V ⊤ x) :=
  rfl

/-- **The two bridges composed: the component at the chart which `⊤` cuts out, applied across the
restriction of scalars, is the component of the transported morphism applied to the section
itself.**  By `rfl` — both sides are the same component of `α`, and the two bridges are the
identity — and this is the one step at which the `CategoryTheory.ModuleCat.restrictScalars`
spelling of the sections meets the plain one.

The chart is bound at the spelling `(smallEtaleRingedSite … ).C`, as it is for
`AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv_val_app_chartOverOfTop`: at
`AlgebraicGeometry.Space.SmallEtale` instance search reports no
`CategoryTheory.Category.{u, u + 1} (Over V)` and the `(Over V)ᵒᵖ` argument of `.val.app` does not
elaborate. -/
theorem chartOverOfTopEvaluation_chartTopSectionsModCast
    (M N : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V))
    (z : (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X V ⊤)).obj
        (M.val.obj (op (openChartOfComparison B S hS X V ⊤)))) :
    chartOverOfTopEvaluation B S hS X M N V α (chartTopSectionsModCast B S hS X M hM V z) =
      ((smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 M N V α).val.app
        (op (openChartOfComparisonOver B S hS X V ⊤))).hom z :=
  rfl

/-! ### The middle link of the chart-scheme intertwining -/

/-- **The middle link of the chart-scheme intertwining**, at the chart binding at which the
transported morphism's components are available.

The component of a section of `𝓗om_{𝒪_X}(M, N)` at the chart which `⊤` cuts out, applied to the
global sections of the chart restriction of `M` read on the chart, is the global sections of the
chart restriction of `N` read on the chart of the `⊤`-component of the morphism of chart
restrictions which the Hom-set transport produces.

This is
`AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply`
at the Zariski open `⊤` — the chart which `⊤` cuts out *is*
`AlgebraicGeometry.Space.openChartOfComparisonOver … V ⊤`, syntactically — crossed through the two
bridges above.  Neither of the two spellings is compared with the other here: the comparison has
already been made, once, in
`AlgebraicGeometry.Space.chartOverOfTopEvaluation_chartTopSectionsModCast`. -/
theorem smallEtaleInternalHomChartHomEquiv_chartTopSectionsFunVal
    (M N : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (V : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V))
    (x : (chartSchemeModule B S hS X M hM V).val.obj (op ⊤)) :
    chartOverOfTopEvaluation B S hS X M N V α (chartTopSectionsFunVal B S hS X M hM V x) =
      chartTopSectionsFunVal B S hS X N hN V
        (((chartSchemeModuleHomEquiv B S hS X M N hM hN V
            (smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 M N V α)).val.app (op ⊤)).hom x) :=
  ((congrArg (fun y => chartOverOfTopEvaluation B S hS X M N V α y)
          (chartTopSectionsFunVal_eq_chartTopSectionsModCast B S hS X M hM V x)).trans
      ((chartOverOfTopEvaluation_chartTopSectionsModCast B S hS X M N hM V α
            (chartSchemeModuleSectionsLinearEquiv B S hS X M hM V ⊤ x)).trans
        (chartSchemeModuleSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply B S hS X M N hM hN V
          (smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 M N V α) ⊤ x).symm)).trans
    (chartTopSectionsFunVal_eq_chartTopSectionsModCast B S hS X N hN V _).symm

/-- `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv_chartTopSectionsFunVal` with the
chart bound at `AlgebraicGeometry.Space.SmallEtale`, which is where the rest of the change of
coordinates is stated.  Only the *statement* of the previous one needs the other binding; applying
it needs no instance at all. -/
theorem chartOverOfTopEvaluation_chartTopSectionsFunVal
    (M N : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V))
    (x : (chartSchemeModule B S hS X M hM V).val.obj (op ⊤)) :
    chartOverOfTopEvaluation B S hS X M N V α (chartTopSectionsFunVal B S hS X M hM V x) =
      chartTopSectionsFunVal B S hS X N hN V
        (((chartSchemeModuleHomEquiv B S hS X M N hM hN V
            (smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 M N V α)).val.app (op ⊤)).hom x) :=
  smallEtaleInternalHomChartHomEquiv_chartTopSectionsFunVal B S hS X M N hM hN V α x

/-- **The chart-scheme intertwining**, at the spelling that conjugation is semilinear over: the
component at the chart which `⊤` cuts out carries the global sections of the chart restriction of
`M` to those of `N`, as the affine-chart reading of the section prescribes.  **This is the whole
hypothesis the chart-scheme side needs.** -/
theorem chartOverOfTopEvaluation_chartTopSectionsFun (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V))
    (y : Γ(chartSchemeModule B S hS X M hM V, ⊤)) :
    chartOverOfTopEvaluation B S hS X M N V α (chartTopSectionsFun B S hS X M hM V y) =
      chartTopSectionsFun B S hS X N hN V
        (smallEtaleInternalHomAffineChartHomEquiv B S hS X M N hM hN V hV α y) :=
  (chartOverOfTopEvaluation_chartTopSectionsFunVal B S hS X M N hM hN V α
      (chartTopModCast B S hS X M hM V y)).trans
    (congrArg (chartTopSectionsFunVal B S hS X N hN V)
      (chartTopModCast_smallEtaleInternalHomAffineChartHomEquiv B S hS X M N hM hN V hV α y).symm)

/-! ### The two conjugates agree, and the affine-chart reading is bijective -/

/-- **The `V`-side conjugate of the affine-chart reading is the component at the chart which `⊤`
cuts out.** -/
theorem chartOfTopHomEquiv_smallEtaleInternalHomChartEvaluation
    (M N : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V)) :
    chartOfTopHomEquiv B S hS X M N V
        (smallEtaleInternalHomChartEvaluation B S hS X.1 X.2 M N V α) =
      chartOverOfTopEvaluation B S hS X M N V α :=
  Stacks.Module.eq_of_homEquivOfSemilinear_eq (chartOfTopHomEquiv_eq B S hS X M N V)
    (smallEtaleInternalHomChartEvaluation B S hS X.1 X.2 M N V α)
    (chartOverOfTopEvaluation B S hS X M N V α)
    (chartOfTopRestrict_hom_smallEtaleInternalHomChartEvaluation B S hS X M N V α)

/-- **The chart-scheme conjugate of the affine-chart reading is the same component.** -/
theorem chartTopHomEquiv_smallEtaleInternalHomAffineChartHomEquiv
    (M N : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (hV : IsAffine (chartScheme V))
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V)) :
    chartTopHomEquiv B S hS X M N hM hN V
        (smallEtaleInternalHomAffineChartHomEquiv B S hS X M N hM hN V hV α) =
      chartOverOfTopEvaluation B S hS X M N V α :=
  Stacks.Module.eq_of_homEquivOfSemilinear_eq (chartTopHomEquiv_eq B S hS X M N hM hN V)
    (smallEtaleInternalHomAffineChartHomEquiv B S hS X M N hM hN V hV α)
    (chartOverOfTopEvaluation B S hS X M N V α)
    (chartOverOfTopEvaluation_chartTopSectionsFun B S hS X M N hM hN V hV α)

/-- **The change of coordinates, carried out**: over an étale chart whose scheme is affine, the
reading of a section of `𝓗om_{𝒪_X}(M, N)` as a `𝒪_X(V)`-linear map `M(V) → N(V)` is the
affine-chart identification of the sections, conjugated by the two halves. -/
theorem smallEtaleInternalHomChartEvaluation_eq (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V)) :
    smallEtaleInternalHomChartEvaluation B S hS X.1 X.2 M N V α =
      (chartOfTopHomEquiv B S hS X M N V).symm
        (chartTopHomEquiv B S hS X M N hM hN V
          (smallEtaleInternalHomAffineChartHomEquiv B S hS X M N hM hN V hV α)) :=
  (Equiv.eq_symm_apply (chartOfTopHomEquiv B S hS X M N V)).2
    ((chartOfTopHomEquiv_smallEtaleInternalHomChartEvaluation B S hS X M N V α).trans
      (chartTopHomEquiv_smallEtaleInternalHomAffineChartHomEquiv B S hS X M N hM hN V hV α).symm)

/-- **Over an étale chart whose scheme is affine, a section of `𝓗om_{𝒪_X}(M, N)` is exactly a
`𝒪_X(V)`-linear map `M(V) → N(V)`:**

`𝓗om_{𝒪_X}(M, N)(V) ≃ Hom_{𝒪_X(V)}(M(V), N(V))`.

By `AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluation_eq` the reading is the composite
of three bijections — the affine-chart identification of the sections and the two halves of the
change of coordinates — so it is one itself.  The affineness of the chart enters only through the
first, where it is `Stacks.Algebraization.sectionsTop_bijective`. -/
theorem bijective_smallEtaleInternalHomChartEvaluation (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V)) :
    Function.Bijective (smallEtaleInternalHomChartEvaluation B S hS X.1 X.2 M N V) := by
  rw [funext (smallEtaleInternalHomChartEvaluation_eq B S hS X M N hM hN V hV)]
  exact (chartOfTopHomEquiv B S hS X M N V).symm.bijective.comp
    ((chartTopHomEquiv B S hS X M N hM hN V).bijective.comp
      (smallEtaleInternalHomAffineChartHomEquiv B S hS X M N hM hN V hV).bijective)

end AlgebraicGeometry.Space

end
