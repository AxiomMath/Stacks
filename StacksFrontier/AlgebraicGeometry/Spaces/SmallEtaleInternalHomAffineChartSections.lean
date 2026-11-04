module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartHomEquivComponent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartHom

/-!
# Evaluating a section of the internal Hom over a chart, and the change of coordinates

Let `X` be an algebraic space over a scheme `S` and let `M`, `N` be `𝒪_X`-modules.  A section of
`𝓗om_{𝒪_X}(M, N)` over an étale chart `V` is, by the definition of
`AlgebraicGeometry.Space.smallEtaleInternalHom`, a morphism of the presheaves of modules of the
restrictions of `M` and `N` to the slice of the small étale site at `V`; its component at the
terminal object `Over.mk (𝟙 V)` of that slice is a map `M(V) → N(V)`, linear over
`AlgebraicGeometry.Space.chartRing` on the nose.  That is
`AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluation`, and over an *affine* chart it is
expected to be bijective:

`𝓗om_{𝒪_X}(M, N)(V) ≃ Hom_{𝒪_X(V)}(M(V), N(V))`.

That reading is what the consumers of Stacks 08B6 hold — the affine-chart computation of the
sections of an ideal-power quotient
(`AlgebraicGeometry.Space.surjective_val_app_smallEtaleAdicQuotient_π` and
`AlgebraicGeometry.Space.ker_val_app_smallEtaleAdicQuotient_π`) and the module-theoretic
Artin--Rees comparison of Stacks 09BB both speak of `M.val.obj (op V)` over `chartRing` — while
the existing reading `AlgebraicGeometry.Space.smallEtaleInternalHomAffineChartHomEquiv` has as its
target the `Γ(V, 𝒪_V)`-linear maps between the global sections of the *chart restrictions*
`Γ(chartSchemeModule … M … V, ⊤)`.  A change of coordinates between the two is therefore needed,
and it has two independent halves, each semilinear over a *surjective* ring map rather than
linear:

* the sections of the chart restriction over `⊤` are the sections of `M` over the étale chart
  which `⊤` cuts out, semilinearly over `AlgebraicGeometry.Space.chartSectionsRingHom` by
  `AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv`;
* that chart is isomorphic to `V` itself, by
  `AlgebraicGeometry.Space.openChartOfComparisonTopIso`, so restriction of sections along
  `AlgebraicGeometry.Space.chartOfTopHom` identifies the sections there with `M(V)`, semilinearly
  over the restriction of functions.

Both are to be consumed through `Stacks.Module.homEquivOfSemilinear`: conjugating a module of
linear maps by two additive bijections which are semilinear over one surjective ring map is a
bijection onto the module of linear maps over the target ring.  Surjectivity of the ring map is
what makes the conjugate homogeneous, and no comparison of the two ring maps with each other is
needed — the two halves are applied to the two sides separately and meet over the chart which `⊤`
cuts out.  The naturality which makes them meet there is
`AlgebraicGeometry.Space.chartOfTopRestrict_smallEtaleInternalHomChartEvaluation`, that evaluation
at the terminal object and the component at the chart which `⊤` cuts out differ by restriction
along `AlgebraicGeometry.Space.chartOverOfTopIso`.

**What is here is that tool, the evaluation map, and the second half of the change of
coordinates**, which is `AlgebraicGeometry.Space.chartOfTopHomEquiv`.  The first half is not
here, and the obstruction to it is an elaboration cost rather than a missing fact; it is described
in the implementation notes below.

## Main definitions

* `Stacks.Module.homEquivOfSemilinear` — conjugation of a module of linear maps by two additive
  bijections semilinear over one surjective ring map.
* `AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluation` and
  `AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluationLinear` — **evaluation of a
  section of the internal Hom at the terminal object of the slice**, as a map and as a linear map
  in the section; defined with no hypothesis and at an arbitrary module universe.
* `AlgebraicGeometry.Space.chartOverOfTopIso` — the chart which `⊤` cuts out is the terminal
  object of the slice, as an isomorphism *in the slice*.
* `AlgebraicGeometry.Space.chartOfTopHomEquiv` — **the Hom-module over `V`, conjugated onto the
  chart which `⊤` cuts out** — the second half of the change of coordinates.

## Main results

* `AlgebraicGeometry.Space.chartOfTopRestrict_smallEtaleInternalHomChartEvaluation` — evaluation
  at the terminal object of the slice and the component at the chart which `⊤` cuts out differ by
  restriction along the isomorphism between them.

## Implementation notes

`Stacks.Module.homEquivOfSemilinear` takes its two bijections as plain *functions* with additivity,
bijectivity and semilinearity as separate hypotheses, rather than as `AddEquiv`s. This is
deliberate: `AlgebraicGeometry.Space.chartSectionsLinearEquiv` is a `CategoryTheory.eqToIso` of an
equality of `CategoryTheory.ModuleCat` objects, and — as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSectionsNaturality` record — comparing two
spellings of it *after* applying them to a section exhausts the heartbeat budget. Coercing it to an
`AddEquiv` and then unifying the applied coercion against the composite is exactly such a
comparison, and it does not elaborate; handing the composite over as a function does. That is why
the half of the change of coordinates which this file does carry, the one over
`AlgebraicGeometry.Space.chartOfTopHom`, goes through `PresheafOfModules.map` and not through any
`CategoryTheory.eqToIso`: `PresheafOfModules.map_smul` is already the semilinearity
`Stacks.Module.homEquivOfSemilinear` asks for, and
`AlgebraicGeometry.Space.bijective_chartOfTopRestrict` reads the bijectivity off
`AlgebraicGeometry.Space.openChartOfComparisonTopIso` through the *underlying presheaf of abelian
groups*, whose `map` is a genuine functor and so has a `CategoryTheory.Functor.mapIso`.

The first half is where the cost bites, and the measurements are these.  The composite
`fun y => chartSectionsLinearEquiv … ((chartSchemeModuleIsoRestrictModule … ).hom.val.app (op W)
).hom y)` *does* elaborate as a definition with target `M.val.obj (op (openChartOfComparison … W))`
— the restriction of scalars in the target of
`AlgebraicGeometry.Space.chartSectionsLinearEquiv` is erased there cheaply.  Each separate step is
also cheap: additivity and semilinearity of each of the two legs,
`ModuleCat.restrictScalars.smul_def'`
at these very arguments, and the generic fact that addition in a restriction of scalars is
addition (`rfl` on variables).  What is *not* cheap is putting the steps together —
`Function.Bijective.comp` of the two legs, or an `Eq.trans` chain of the three additivity steps,
or a `show` reducing the composite to its body — each of which exhausts the heartbeat budget in
`whnf` or `isDefEq`.  So the remaining work on this half is not a mathematical gap but a question
of finding a formulation whose steps compose at the default heartbeat budget, which is the only
budget this tree allows.

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

universe u m

namespace Stacks.Module

variable {R R' : Type*} [Ring R] [Ring R']
    {P₁ P₂ Q₁ Q₂ : Type*}
    [AddCommGroup P₁] [AddCommGroup P₂] [AddCommGroup Q₁] [AddCommGroup Q₂]
    [Module R P₁] [Module R P₂] [Module R' Q₁] [Module R' Q₂]

/-- **Conjugation by two semilinear bijections over one surjective ring map.**

Let `σ : R →+* R'` be surjective and let `f₁ : P₁ → Q₁`, `f₂ : P₂ → Q₂` be additive bijections
with `fᵢ (r • x) = σ r • fᵢ x`.  Then `ψ ↦ f₂ ∘ ψ ∘ f₁⁻¹` is a bijection from the `R`-linear maps
`P₁ → P₂` onto the `R'`-linear maps `Q₁ → Q₂`.

Surjectivity of `σ` is what makes the conjugate map homogeneous: a scalar of `R'` is `σ` of a
scalar of `R`, and only then can it be pulled through `f₁⁻¹`.  No comparison of `σ` with any
other ring map is involved, which is why this is the right shape for a change of coordinates
whose two halves are semilinear over ring maps that are never compared with each other.

The two bijections are taken as functions with their properties listed separately rather than as
`AddEquiv`s; see the implementation notes of this file. -/
def homEquivOfSemilinear (σ : R →+* R') (hσ : Function.Surjective σ)
    (f₁ : P₁ → Q₁) (ha₁ : ∀ x y : P₁, f₁ (x + y) = f₁ x + f₁ y)
    (hb₁ : Function.Bijective f₁) (hs₁ : ∀ (r : R) (x : P₁), f₁ (r • x) = σ r • f₁ x)
    (f₂ : P₂ → Q₂) (ha₂ : ∀ x y : P₂, f₂ (x + y) = f₂ x + f₂ y)
    (hb₂ : Function.Bijective f₂) (hs₂ : ∀ (r : R) (x : P₂), f₂ (r • x) = σ r • f₂ x) :
    (P₁ →ₗ[R] P₂) ≃ (Q₁ →ₗ[R'] Q₂) :=
  let e₁ : P₁ ≃+ Q₁ := AddEquiv.mk' (Equiv.ofBijective f₁ hb₁) ha₁
  let e₂ : P₂ ≃+ Q₂ := AddEquiv.mk' (Equiv.ofBijective f₂ hb₂) ha₂
  have he₁ : ∀ (r : R) (x : P₁), e₁ (r • x) = σ r • e₁ x := hs₁
  have he₂ : ∀ (r : R) (x : P₂), e₂ (r • x) = σ r • e₂ x := hs₂
  have hsymm₁ : ∀ (r : R) (y : Q₁), e₁.symm (σ r • y) = r • e₁.symm y := fun r y =>
    e₁.injective (by rw [e₁.apply_symm_apply, he₁, e₁.apply_symm_apply])
  have hsymm₂ : ∀ (r : R) (y : Q₂), e₂.symm (σ r • y) = r • e₂.symm y := fun r y =>
    e₂.injective (by rw [e₂.apply_symm_apply, he₂, e₂.apply_symm_apply])
  { toFun := fun ψ =>
      { toFun := fun y => e₂ (ψ (e₁.symm y))
        map_add' := fun y z => by rw [map_add, map_add, map_add]
        map_smul' := fun s y => by
          obtain ⟨r, rfl⟩ := hσ s
          change e₂ (ψ (e₁.symm (σ r • y))) = σ r • e₂ (ψ (e₁.symm y))
          rw [hsymm₁, map_smul, he₂] }
    invFun := fun φ =>
      { toFun := fun x => e₂.symm (φ (e₁ x))
        map_add' := fun x y => by rw [map_add, map_add, map_add]
        map_smul' := fun r x => by
          change e₂.symm (φ (e₁ (r • x))) = r • e₂.symm (φ (e₁ x))
          rw [he₁, map_smul, hsymm₂] }
    left_inv := fun ψ => LinearMap.ext fun x => by
      change e₂.symm (e₂ (ψ (e₁.symm (e₁ x)))) = ψ x
      rw [e₁.symm_apply_apply, e₂.symm_apply_apply]
    right_inv := fun φ => LinearMap.ext fun y => by
      change e₂ (e₂.symm (φ (e₁ (e₁.symm y)))) = φ y
      rw [e₁.apply_symm_apply, e₂.apply_symm_apply] }

/-- The conjugate of a linear map, read on a point of the image of `f₁`. -/
theorem homEquivOfSemilinear_apply (σ : R →+* R') (hσ : Function.Surjective σ)
    (f₁ : P₁ → Q₁) (ha₁ : ∀ x y : P₁, f₁ (x + y) = f₁ x + f₁ y)
    (hb₁ : Function.Bijective f₁) (hs₁ : ∀ (r : R) (x : P₁), f₁ (r • x) = σ r • f₁ x)
    (f₂ : P₂ → Q₂) (ha₂ : ∀ x y : P₂, f₂ (x + y) = f₂ x + f₂ y)
    (hb₂ : Function.Bijective f₂) (hs₂ : ∀ (r : R) (x : P₂), f₂ (r • x) = σ r • f₂ x)
    (ψ : P₁ →ₗ[R] P₂) (x : P₁) :
    homEquivOfSemilinear σ hσ f₁ ha₁ hb₁ hs₁ f₂ ha₂ hb₂ hs₂ ψ (f₁ x) = f₂ (ψ x) := by
  show (AddEquiv.mk' (Equiv.ofBijective f₂ hb₂) ha₂)
      (ψ ((AddEquiv.mk' (Equiv.ofBijective f₁ hb₁) ha₁).symm
        ((AddEquiv.mk' (Equiv.ofBijective f₁ hb₁) ha₁) x))) = f₂ (ψ x)
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- **A linear map is recognized from its conjugate.**  If `φ` and `ψ` are intertwined by the two
semilinear bijections then `φ` is the conjugate of `ψ`.  This is the form in which the change of
coordinates is used: both sides of an identity are shown to have the same conjugate. -/
theorem homEquivOfSemilinear_eq (σ : R →+* R') (hσ : Function.Surjective σ)
    (f₁ : P₁ → Q₁) (ha₁ : ∀ x y : P₁, f₁ (x + y) = f₁ x + f₁ y)
    (hb₁ : Function.Bijective f₁) (hs₁ : ∀ (r : R) (x : P₁), f₁ (r • x) = σ r • f₁ x)
    (f₂ : P₂ → Q₂) (ha₂ : ∀ x y : P₂, f₂ (x + y) = f₂ x + f₂ y)
    (hb₂ : Function.Bijective f₂) (hs₂ : ∀ (r : R) (x : P₂), f₂ (r • x) = σ r • f₂ x)
    (ψ : P₁ →ₗ[R] P₂) (φ : Q₁ →ₗ[R'] Q₂)
    (h : ∀ x : P₁, φ (f₁ x) = f₂ (ψ x)) :
    homEquivOfSemilinear σ hσ f₁ ha₁ hb₁ hs₁ f₂ ha₂ hb₂ hs₂ ψ = φ :=
  LinearMap.ext fun y => by
    obtain ⟨x, rfl⟩ := hb₁.2 y
    rw [homEquivOfSemilinear_apply, h x]

end Stacks.Module

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Evaluation of a section of the internal Hom at the terminal object of the slice -/

/-- **Evaluation of a section of `𝓗om_{𝒪_F}(M, N)` over an étale chart `V` at the terminal object
of the slice at `V`.**

A section over `V` is a morphism of the presheaves of modules of the restrictions of `M` and `N`
to the slice of the small étale site at `V`, by the definition of
`AlgebraicGeometry.Space.smallEtaleInternalHom`, and the component of such a morphism at
`Over.mk (𝟙 V)` is a map `M(V) → N(V)`, linear over `AlgebraicGeometry.Space.chartRing` on the
nose.  No hypothesis is needed on `M`, `N` or `V`, and the module universe is arbitrary. -/
def smallEtaleInternalHomChartEvaluation (M N : Modules.{u, m} B S hS F hF)
    (V : SmallEtale B S hS F)
    (α : (smallEtaleInternalHom B S hS F hF M N).val.obj (op V)) :
    M.val.obj (op V) →ₗ[chartRing B S hS F hF V] N.val.obj (op V) :=
  (α.app (op (Over.mk (𝟙 V)))).hom

/-- **Evaluation is linear in the section**: the module structure on the sections of the internal
Hom over a chart is the pointwise one, so both halves are `rfl` on components. -/
def smallEtaleInternalHomChartEvaluationLinear (M N : Modules.{u, m} B S hS F hF)
    (V : SmallEtale B S hS F) :
    (smallEtaleInternalHom B S hS F hF M N).val.obj (op V) →ₗ[chartRing B S hS F hF V]
      (M.val.obj (op V) →ₗ[chartRing B S hS F hF V] N.val.obj (op V)) where
  toFun := smallEtaleInternalHomChartEvaluation B S hS F hF M N V
  map_add' α β := by ext x; rfl
  map_smul' r α := by ext x; rfl

variable (X : AlgebraicSpaces B S hS)

/-! ### The chart which the whole of the chart's scheme cuts out -/

/-- **The chart cut out by the whole of the chart's scheme is the terminal object of the slice.**

This is the isomorphism underlying `AlgebraicGeometry.Space.openChartOfComparisonTopIso`, taken
*before* the projection of the slice: a section of the internal Hom over `V` has a component at
an object of the slice at `V`, not at an étale chart alone, so the comparison between
`AlgebraicGeometry.Space.chartOverOfTop` and `Over.mk (𝟙 V)` has to be available there. -/
def chartOverOfTopIso (V : SmallEtale B S hS X.1) :
    chartOverOfTop B S hS X V ≅ Over.mk (𝟙 V) :=
  (((_root_.AlgebraicGeometry.SmallEtale.isTerminalOpensObjTop (associatedBigEtaleSite B)
        (chartScheme V) (chartFppfObject B S hS X V).left.property).isTerminalObj
          (representedSmallEtaleEquivalence B S hS
            (chartFppfObject B S hS X V)).inverse _).isTerminalObj
          (SmallEtale.chartLocalizationEquivalence B S hS X.1 V).functor _).uniqueUpToIso
      Over.mkIdTerminal

/-- The structural morphism of the chart which `⊤` cuts out: an isomorphism of charts, by
`AlgebraicGeometry.Space.openChartOfComparisonTopIso`. -/
abbrev chartOfTopHom (V : SmallEtale B S hS X.1) :
    openChartOfComparison B S hS X V ⊤ ⟶ V :=
  (openChartOfComparisonTopIso B S hS X V).hom

/-- `AlgebraicGeometry.Space.chartOverOfTopIso` lies over
`AlgebraicGeometry.Space.chartOfTopHom`: the slice isomorphism and the isomorphism of charts are
the same morphism, by `rfl`. -/
theorem chartOverOfTopIso_hom_left (V : SmallEtale B S hS X.1) :
    (chartOverOfTopIso B S hS X V).hom.left = chartOfTopHom B S hS X V := rfl

/-- **Restriction of sections along `AlgebraicGeometry.Space.chartOfTopHom` is bijective**, being
restriction along an isomorphism of charts. -/
theorem bijective_chartOfTopRestrict (P : Modules.{u, m} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) :
    Function.Bijective
      ((P.val.map (op (chartOfTopHom B S hS X V))).hom :
        P.val.obj (op V) → P.val.obj (op (openChartOfComparison B S hS X V ⊤))) :=
  ConcreteCategory.bijective_of_isIso
    (P.val.presheaf.mapIso (openChartOfComparisonTopIso B S hS X V).op).hom

/-- **Restriction of functions along `AlgebraicGeometry.Space.chartOfTopHom` is surjective**,
being restriction along an isomorphism of charts.  This is the ring map over which the
`V`-side half of the change of coordinates is semilinear. -/
theorem surjective_chartOfTopChartRestrict (V : SmallEtale B S hS X.1) :
    Function.Surjective (chartRestrict (hF := X.2) (chartOfTopHom B S hS X V)) :=
  (ConcreteCategory.bijective_of_isIso
    ((((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.mapIso
      (openChartOfComparisonTopIso B S hS X V).op).hom)).2

/-- **The Hom-module over the chart `V`, conjugated onto the chart which `⊤` cuts out.**

Conjugation by restriction of sections along `AlgebraicGeometry.Space.chartOfTopHom`, which is an
additive bijection semilinear over the restriction of functions along it; the latter is
surjective because it is an isomorphism.  This is the half of the change of coordinates which
does not involve the chart's scheme. -/
def chartOfTopHomEquiv (M N : Modules.{u, m} B S hS X.1 X.2) (V : SmallEtale B S hS X.1) :
    (M.val.obj (op V) →ₗ[chartRing B S hS X.1 X.2 V] N.val.obj (op V)) ≃
      (M.val.obj (op (openChartOfComparison B S hS X V ⊤)) →ₗ[
          chartRing B S hS X.1 X.2 (openChartOfComparison B S hS X V ⊤)]
        N.val.obj (op (openChartOfComparison B S hS X V ⊤))) :=
  Stacks.Module.homEquivOfSemilinear (chartRestrict (hF := X.2) (chartOfTopHom B S hS X V))
    (surjective_chartOfTopChartRestrict B S hS X V)
    ((M.val.map (op (chartOfTopHom B S hS X V))).hom)
    (fun y z => map_add (M.val.map (op (chartOfTopHom B S hS X V))).hom y z)
    (bijective_chartOfTopRestrict B S hS X M V)
    (fun r y => M.val.map_smul (op (chartOfTopHom B S hS X V)) r y)
    ((N.val.map (op (chartOfTopHom B S hS X V))).hom)
    (fun y z => map_add (N.val.map (op (chartOfTopHom B S hS X V))).hom y z)
    (bijective_chartOfTopRestrict B S hS X N V)
    (fun r y => N.val.map_smul (op (chartOfTopHom B S hS X V)) r y)

/-- **Evaluation at the terminal object of the slice and the component at the chart which `⊤` cuts
out differ by restriction along the isomorphism between them.**

This is naturality of the section — a morphism of presheaves of modules on the slice — along
`AlgebraicGeometry.Space.chartOverOfTopIso`.  It is what makes the two halves of the change of
coordinates meet: the chart-restriction half carries
`AlgebraicGeometry.Space.smallEtaleInternalHomAffineChartHomEquiv` to the component at
`AlgebraicGeometry.Space.chartOverOfTop`, and this carries evaluation there as well. -/
theorem chartOfTopRestrict_smallEtaleInternalHomChartEvaluation
    (M N : Modules.{u, m} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V))
    (y : M.val.obj (op V)) :
    (α.app (op (chartOverOfTop B S hS X V))).hom
        ((M.val.map (op (chartOfTopHom B S hS X V))) y) =
      (N.val.map (op (chartOfTopHom B S hS X V)))
        (smallEtaleInternalHomChartEvaluation B S hS X.1 X.2 M N V α y) :=
  PresheafOfModules.naturality_apply α (chartOverOfTopIso B S hS X V).hom.op y

end AlgebraicGeometry.Space

end
