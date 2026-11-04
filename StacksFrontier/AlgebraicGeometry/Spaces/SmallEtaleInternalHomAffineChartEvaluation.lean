module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSectionsEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomAffineChartSections

/-!
# The chart-scheme half of the change of coordinates for the affine-chart reading

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `M`, `N` be
quasi-coherent `𝒪_X`-modules and let `V` be an étale chart of `X`.
`AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluation` reads a section of
`𝓗om_{𝒪_X}(M, N)` over `V` as a `𝒪_X(V)`-linear map `M(V) → N(V)`, the component of the section
at the terminal object of the slice at `V`, and over an *affine* chart that reading is expected to
be a bijection

`𝓗om_{𝒪_X}(M, N)(V) ≃ Hom_{𝒪_X(V)}(M(V), N(V))`.

The existing reading `AlgebraicGeometry.Space.smallEtaleInternalHomAffineChartHomEquiv` has as its
target the `Γ(V, 𝒪_V)`-linear maps between the global sections of the chart restrictions, so what
is needed is a change of coordinates between the two, and it has two halves, each semilinear over
a surjective ring map rather than linear.  The half over
`AlgebraicGeometry.Space.chartOfTopHom`, which does not involve the chart's scheme, is
`AlgebraicGeometry.Space.chartOfTopHomEquiv`; **the half over the chart's scheme is here**, and
both are consumed through `Stacks.Module.homEquivOfSemilinear`.

What is *not* here is the identity that equates the two conjugates, which is what the bijection
needs; the obstruction to it is an elaboration cost and it is described in the implementation
notes below.

## Main definitions

* `AlgebraicGeometry.Space.chartTopRingCast` and `AlgebraicGeometry.Space.chartTopModCast` — the
  two spellings of the global functions and of the global sections on the chart's scheme, bridged
  once each by the identity.
* `AlgebraicGeometry.Space.chartTopSectionsRingHom` — the composite scalar map of the chart at
  `⊤`, with its domain spelled `Γ(chartScheme V, ⊤)` and its codomain spelled
  `AlgebraicGeometry.Space.chartRing`.
* `AlgebraicGeometry.Space.chartTopSectionsFunVal` and
  `AlgebraicGeometry.Space.chartTopSectionsFun` — the global sections of the chart restriction of
  `M` are the sections of `M` over the étale chart which `⊤` cuts out, as a function, at the two
  spellings of its domain.
* `AlgebraicGeometry.Space.chartTopHomEquiv` — **the Hom-module on the chart's scheme, conjugated
  onto the chart which `⊤` cuts out** — the first half of the change of coordinates.

## Implementation notes

**Every property of the sections identification is proved by applying
`AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv` as a whole, and nothing is ever
matched against its decomposition.**  It is built from a `CategoryTheory.eqToIso` of an equality
of `CategoryTheory.ModuleCat` objects, and — as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSectionsNaturality` record — comparing two
spellings of such a transport *after* applying it to a section exhausts the heartbeat budget.
Taking it as a plain *function* with an explicit codomain erases the restriction of scalars in
that codomain for free, and then `map_add`, `map_smul` and injectivity all compose with it
syntactically.  What does not work is any bundled route: `AddEquiv`- or
`Equiv.bijective`-shaped proofs make the elaborator compare `Function.Bijective` at the two
spellings of the codomain and time out, and so does producing the inverse as `(… ).symm w`.
**Surjectivity is therefore obtained by consuming `LinearEquiv.surjective` on an element**,
exactly as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartAlphaBaseCase` record for the same equivalence.

**The two spellings of the global functions and sections on the chart's scheme are bridged once,
on an element, and never inside another comparison.**  The scalars of
`AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv` are
`(chartScheme V).ringCatSheaf.obj.obj (op ⊤)`, those of
`AlgebraicGeometry.Space.smallEtaleInternalHomAffineChartHomEquiv` are `Γ(chartScheme V, ⊤)`; the
two types are equal by `rfl` and cheaply so, but instance search is syntactic and finds no `SMul`
for the first spelling on `Γ(chartSchemeModule … , ⊤)` nor for the codomain spelling of
`AlgebraicGeometry.Space.chartSectionsRingHom` on `M.val.obj (op _)`.  So
`AlgebraicGeometry.Space.chartTopRingCast` and `AlgebraicGeometry.Space.chartTopModCast` carry
the one `rfl` each, `AlgebraicGeometry.Space.chartTopSectionsRingHom` is declared at the
spellings instance search wants, and `AlgebraicGeometry.Space.chartTopSectionsFun_smul` composes
the two cheap steps.  Writing the bridge into the `map_smul` application instead — as a `show`,
or by casting only the scalar — times out.

**What blocks the identity which would equate the two conjugates.**  Each conjugate is
the component of the section at the chart which `⊤` cuts out: for
`AlgebraicGeometry.Space.chartOfTopHomEquiv` that is
`AlgebraicGeometry.Space.chartOfTopRestrict_smallEtaleInternalHomChartEvaluation`, and for
`AlgebraicGeometry.Space.chartTopHomEquiv` it is the component formula
`AlgebraicGeometry.Space.chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply` at the Zariski
open `⊤`.  The latter is stated with `AlgebraicGeometry.Space.chartSectionsLinearEquiv` *after*
the component of `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule`, while
`AlgebraicGeometry.Space.chartTopSectionsFun` is the composite of the two, and no
comparison of those two spellings elaborates.  At the default budget:

* the composite function with the restriction of scalars erased from its codomain *is* definable,
  whether spelled through `AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv`, through
  the two factors applied in turn, or as a `LinearMap.comp` of them — all three are free;
* `map_add`, `map_smul` and `congrArg` under `AlgebraicGeometry.Space.chartSectionsLinearEquiv`
  applied to *variables* are free, as is the component of
  `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` and its bijectivity;
* but every comparison which has to unfold the composite — `rfl` or `LinearEquiv.trans_apply`
  or `LinearMap.comp_apply` between the composite and its two factors applied in turn, in either
  direction and unapplied as well as applied, and any `Eq.trans` chain of the two factors'
  additivity with the composite named on one side — exhausts the budget in `whnf` or `isDefEq`.

So the composite may be *defined* and *used*, and never *decomposed*: `whnf` of the coercion of
the transport applied to a compound argument does not get stuck, which it does when the argument
is a variable.  Erasing the restriction of scalars is *not* what costs this, and the route of
keeping it — never erasing, and supplying the `AlgebraicGeometry.Space.chartRing`-module
structure on it explicitly as `(M.val.obj (op _)).isModule`, which is itself free — does not
help: the two-factor additivity chain costs the budget at that spelling too, with the composite's
source, target and additive structure all syntactically those of the chain.  What is therefore
owed for the identity is a component formula stated at the *composite*
`AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv` rather than at
`AlgebraicGeometry.Space.chartSectionsLinearEquiv` after the component of
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule`, proved where the existing formula is
proved — where the transport is still a `CategoryTheory.eqToHom` and
`AlgebraicGeometry.Space.chartSectionsLinearEquiv_apply` is available to cross it on a section —
and not derived here from the existing one.

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

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The two spellings of the global functions and sections on the chart's scheme -/

/-- The global functions on the chart's scheme, from the `CommRingCat` spelling to the `RingCat`
spelling in which the presheaves of modules of the chart's scheme are indexed.  The identity. -/
def chartTopRingCast (V : SmallEtale B S hS X.1) :
    Γ(chartScheme V, ⊤) → (chartScheme V).ringCatSheaf.obj.obj (op ⊤) := id

/-- The global sections of the chart restriction, from the `Γ` spelling of the sections of an
`𝒪_V`-module to the `val.obj` spelling in which
`AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv` is stated.  The identity. -/
def chartTopModCast (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) :
    Γ(chartSchemeModule B S hS X M hM V, ⊤) →
      (chartSchemeModule B S hS X M hM V).val.obj (op ⊤) := id

/-- The identification of the two spellings of the global sections of the chart restriction is
bijective. -/
theorem bijective_chartTopModCast (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) :
    Function.Bijective (chartTopModCast B S hS X M hM V) :=
  Function.bijective_id

/-- Scalar multiplication on the global sections of the chart restriction is the same in the two
spellings. -/
theorem chartTopModCast_smul (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (r : Γ(chartScheme V, ⊤)) (y : Γ(chartSchemeModule B S hS X M hM V, ⊤)) :
    chartTopModCast B S hS X M hM V (r • y) =
      chartTopRingCast B S hS X V r • chartTopModCast B S hS X M hM V y := rfl

/-! ### The first half of the change of coordinates -/

/-- **The composite scalar map of the chart at `⊤`**, which is
`AlgebraicGeometry.Space.chartSectionsRingHom` there, declared at the spellings instance search
wants: its domain is the `CommRingCat`-valued global functions on the chart's scheme and its
codomain is `AlgebraicGeometry.Space.chartRing`.  This is the ring map over which the half of the
change of coordinates on the chart's scheme is semilinear. -/
def chartTopSectionsRingHom (V : SmallEtale B S hS X.1) :
    Γ(chartScheme V, ⊤) →+* chartRing B S hS X.1 X.2 (openChartOfComparison B S hS X V ⊤) :=
  chartSectionsRingHom B S hS X V ⊤

/-- **The composite scalar map of the chart at `⊤` is surjective**, being
`AlgebraicGeometry.Space.surjective_chartSectionsRingHom` there. -/
theorem surjective_chartTopSectionsRingHom (V : SmallEtale B S hS X.1) :
    Function.Surjective (chartTopSectionsRingHom B S hS X V) :=
  surjective_chartSectionsRingHom B S hS X V ⊤

/-- **The global sections of the chart restriction of `M` are the sections of `M` over the étale
chart which `⊤` cuts out.**

This is `AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv` at `⊤`, taken as a plain
function with the restriction of scalars in its codomain erased; see the implementation notes of
this file for why the bundled form is unusable. -/
def chartTopSectionsFunVal (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) :
    (chartSchemeModule B S hS X M hM V).val.obj (op ⊤) →
      M.val.obj (op (openChartOfComparison B S hS X V ⊤)) :=
  fun y => chartSchemeModuleSectionsLinearEquiv B S hS X M hM V ⊤ y

/-- `AlgebraicGeometry.Space.chartTopSectionsFunVal` is additive. -/
theorem chartTopSectionsFunVal_add (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (y z : (chartSchemeModule B S hS X M hM V).val.obj (op ⊤)) :
    chartTopSectionsFunVal B S hS X M hM V (y + z) =
      chartTopSectionsFunVal B S hS X M hM V y + chartTopSectionsFunVal B S hS X M hM V z :=
  map_add (chartSchemeModuleSectionsLinearEquiv B S hS X M hM V ⊤) y z

/-- `AlgebraicGeometry.Space.chartTopSectionsFunVal` is semilinear over
`AlgebraicGeometry.Space.chartTopSectionsRingHom`. -/
theorem chartTopSectionsFunVal_smul (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (r : Γ(chartScheme V, ⊤))
    (y : (chartSchemeModule B S hS X M hM V).val.obj (op ⊤)) :
    chartTopSectionsFunVal B S hS X M hM V (chartTopRingCast B S hS X V r • y) =
      chartTopSectionsRingHom B S hS X V r • chartTopSectionsFunVal B S hS X M hM V y :=
  map_smul (chartSchemeModuleSectionsLinearEquiv B S hS X M hM V ⊤)
    (chartTopRingCast B S hS X V r) y

/-- `AlgebraicGeometry.Space.chartTopSectionsFunVal` is injective. -/
theorem injective_chartTopSectionsFunVal (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) :
    Function.Injective (chartTopSectionsFunVal B S hS X M hM V) :=
  fun _ _ h => (chartSchemeModuleSectionsLinearEquiv B S hS X M hM V ⊤).injective h

/-- `AlgebraicGeometry.Space.chartTopSectionsFunVal` is surjective. -/
theorem surjective_chartTopSectionsFunVal (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) :
    Function.Surjective (chartTopSectionsFunVal B S hS X M hM V) := by
  intro w
  obtain ⟨y, hy⟩ := (chartSchemeModuleSectionsLinearEquiv B S hS X M hM V ⊤).surjective w
  exact ⟨y, hy⟩

/-- **The global sections of the chart restriction of `M` are the sections of `M` over the étale
chart which `⊤` cuts out**, with the sections of the chart restriction at the `Γ` spelling in
which `AlgebraicGeometry.Space.smallEtaleInternalHomAffineChartHomEquiv` states them. -/
def chartTopSectionsFun (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) :
    Γ(chartSchemeModule B S hS X M hM V, ⊤) →
      M.val.obj (op (openChartOfComparison B S hS X V ⊤)) :=
  fun y => chartTopSectionsFunVal B S hS X M hM V (chartTopModCast B S hS X M hM V y)

/-- `AlgebraicGeometry.Space.chartTopSectionsFun` is additive. -/
theorem chartTopSectionsFun_add (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (y z : Γ(chartSchemeModule B S hS X M hM V, ⊤)) :
    chartTopSectionsFun B S hS X M hM V (y + z) =
      chartTopSectionsFun B S hS X M hM V y + chartTopSectionsFun B S hS X M hM V z :=
  chartTopSectionsFunVal_add B S hS X M hM V _ _

/-- `AlgebraicGeometry.Space.chartTopSectionsFun` is semilinear over
`AlgebraicGeometry.Space.chartTopSectionsRingHom`. -/
theorem chartTopSectionsFun_smul (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (r : Γ(chartScheme V, ⊤)) (y : Γ(chartSchemeModule B S hS X M hM V, ⊤)) :
    chartTopSectionsFun B S hS X M hM V (r • y) =
      chartTopSectionsRingHom B S hS X V r • chartTopSectionsFun B S hS X M hM V y :=
  (congrArg (chartTopSectionsFunVal B S hS X M hM V)
      (chartTopModCast_smul B S hS X M hM V r y)).trans
    (chartTopSectionsFunVal_smul B S hS X M hM V r (chartTopModCast B S hS X M hM V y))

/-- `AlgebraicGeometry.Space.chartTopSectionsFun` is bijective. -/
theorem bijective_chartTopSectionsFun (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) :
    Function.Bijective (chartTopSectionsFun B S hS X M hM V) :=
  Function.Bijective.comp
    ⟨injective_chartTopSectionsFunVal B S hS X M hM V,
      surjective_chartTopSectionsFunVal B S hS X M hM V⟩
    (bijective_chartTopModCast B S hS X M hM V)

/-- **The Hom-module on the chart's scheme, conjugated onto the chart which `⊤` cuts out.**

Conjugation by the sections identification of the chart restriction at `⊤`, which is an additive
bijection semilinear over the composite scalar map of the chart; the latter is surjective.  This
is the half of the change of coordinates which involves the chart's scheme. -/
def chartTopHomEquiv (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) :
    (Γ(chartSchemeModule B S hS X M hM V, ⊤) →ₗ[Γ(chartScheme V, ⊤)]
        Γ(chartSchemeModule B S hS X N hN V, ⊤)) ≃
      (M.val.obj (op (openChartOfComparison B S hS X V ⊤)) →ₗ[
          chartRing B S hS X.1 X.2 (openChartOfComparison B S hS X V ⊤)]
        N.val.obj (op (openChartOfComparison B S hS X V ⊤))) :=
  Stacks.Module.homEquivOfSemilinear (chartTopSectionsRingHom B S hS X V)
    (surjective_chartTopSectionsRingHom B S hS X V)
    (chartTopSectionsFun B S hS X M hM V) (chartTopSectionsFun_add B S hS X M hM V)
    (bijective_chartTopSectionsFun B S hS X M hM V) (chartTopSectionsFun_smul B S hS X M hM V)
    (chartTopSectionsFun B S hS X N hN V) (chartTopSectionsFun_add B S hS X N hN V)
    (bijective_chartTopSectionsFun B S hS X N hN V) (chartTopSectionsFun_smul B S hS X N hN V)

end AlgebraicGeometry.Space

end
