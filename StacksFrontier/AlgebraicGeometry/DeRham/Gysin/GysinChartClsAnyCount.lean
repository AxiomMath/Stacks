module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartLocal
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartClsImmersionComp
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinClassMapToSupportLocality

/-!
# The class map of a chart, for any number of equations

The class map `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q] of an equation chart, built from
`Stacks.Perfect.FractionClass.classMapToSupport` and transported to the restriction to the chart
of the global target of [Stacks, Tag 0G86], for any number `c` of equations, zero included; the
Gysin formula of a chart and the locality of its class map.

## Main definitions

* `Stacks.Gysin.chartClsHomOfClassMap`: the class map of a chart, for any number of equations.
* `Stacks.Gysin.chartClsOfClassMap`: the same on the sections over an open of the chart.
* `Stacks.Gysin.openImmersionClsHomOfClassMap`: the class map along an arbitrary open immersion.
* `Stacks.Gysin.chartClsOnOfClassMap`: `chartClsOfClassMap` with the open of the chart and the
  identification of its image supplied.

## Main results

* `Stacks.Gysin.formRestriction_comp_chartGysin_comp_chartTargetHomOfClassMap`: the Gysin
  formula of [Stacks, Tag 0G83] of a chart, for any number of equations, as an identity of
  morphisms on the chart.
* `Stacks.Gysin.chartLoc_subschemeFormPullbackOfClassMap`: the same on sections — on the
  restriction `ω̃|_Z` of an ambient `p`-form the chart's Gysin map takes the value
  `c_{f₁, …, f_c}(ω̃|_Z) ∧ d f₁ ∧ ⋯ ∧ d f_c`.
* `Stacks.Gysin.openImmersionClsHomOfClassMap_comp`: the class map along an open immersion is
  local.
* `Stacks.Gysin.chartClsHomOfClassMap_homOfLE` and `Stacks.Gysin.chartClsOfClassMap_homOfLE`: the
  class map of a chart is local along the inclusion of a smaller chart, as morphisms and on
  sections.

## References

* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.DifferentialsRestrict
open Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.FractionClass
open Stacks.Perfect.LocalCohomologyExcision (chartOpen ι_image_chartOpen)
open Stacks.Perfect.SupportedFraction

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

/-- **The class map `c_{f₁, …, f_c}` of a chart, transported to the ambient scheme, for any
number of equations.**

The class map `Stacks.Perfect.FractionClass.classMapToSupport` of the chart, followed by the
derived excision of [Stacks, Tag 0G78], read on degree-`c` cohomology sheaves as
`Stacks.Gysin.supportCohomologyRestrictIso`, back to the restriction to the chart of the global
target `Stacks.Gysin.gysinTarget`. -/
def chartClsHomOfClassMap (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ)
    (W : X.Opens) (f : Fin c → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base) :
    (Scheme.Modules.restrictFunctor W.ι).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) ⟶
      (Scheme.Modules.restrictFunctor W.ι).obj (gysinTarget i π c p) :=
  haveI : (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p c
  classMapToSupport f
      ((Scheme.Modules.restrictFunctor W.ι).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))) hT hTf ≫
    (supportCohomologyRestrictIso W (isClosed_range_base i) hT (c : ℤ)
      (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).inv

/-- **The class map of a chart on the sections over an open of the ambient scheme contained in
it**, for any number of equations.

This is `chartClsHomOfClassMap` read over `Stacks.Perfect.LocalCohomologyExcision.chartOpen W hV`,
whose image `W.ι ''ᵁ chartOpen W hV` is `V`, conjugated by the restriction maps along that
equality of opens. -/
def chartClsOfClassMap (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ)
    (W : X.Opens) (f : Fin c → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W) :
    Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V) →+ Γ(gysinTarget i π c p, V) :=
  (((gysinTarget i π c p).presheaf.map
        (homOfLE (ι_image_chartOpen W hV).ge).op).hom).comp
    ((((chartClsHomOfClassMap i π p W f hT hTf).val.app
          (op (chartOpen W hV))).hom.toAddMonoidHom).comp
      (((relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).presheaf.map
        (homOfLE (ι_image_chartOpen W hV).le).op).hom))

/-- **The Gysin formula of [Stacks, Tag 0G83] of a chart, for any number of equations**, as an
identity of morphisms on the chart.  Composing the restriction of forms to the closed subscheme
with the Gysin map of the chart's equations and with the identification of its target is wedging
with the equation wedge followed by the class map of [Stacks, Tag 0G7Q] of the chart. -/
theorem formRestriction_comp_chartGysin_comp_chartTargetHomOfClassMap (i : Z ⟶ X)
    [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ) (W : X.Opens) (f : Fin c → Γ(X, W))
    (hcut : IsCutOutByEquationsOn i W f)
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hgT : equationsClosedSet (restrictEquations W f) = W.ι ⁻¹' Set.range i.base)
    (hfrac : ∀ {F G : W.toScheme.Modules} (φ : F ⟶ G),
      fracTermTop (restrictEquations W f) F ≫ (cplxMap (restrictEquations W f) φ).f c =
        φ ≫ fracTermTop (restrictEquations W f) G) :
    formRestriction (i ∣_ W) (W.ι ≫ π) (p : ℤ) ≫ chartGysin i π W f p hcut ≫
        chartTargetHom i π p W (restrictEquations W f) hgT =
      gysinWedgeHom (W.ι ≫ π) (restrictEquations W f) (p : ℤ) ≫
        (relativeDifferentialFormsRestrictIso π W ((p : ℤ) + (c : ℤ))).inv ≫
          chartClsHomOfClassMap i π p W (restrictEquations W f) hT hgT.le := by
  have : (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p c
  have : (relativeDifferentialForms (W.ι ≫ π) ((p : ℤ) + (c : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add (W.ι ≫ π) p c
  have hFFC : formFractionClass (W.ι ≫ π) (restrictEquations W f) ((p : ℤ) + (c : ℤ)) =
      classMapToSupport (restrictEquations W f)
          (relativeDifferentialForms (W.ι ≫ π) ((p : ℤ) + (c : ℤ)))
          (isClosed_equationsClosedSet _) subset_rfl ≫
        (Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward
          (restrictEquations W f)
          (relativeDifferentialForms (W.ι ≫ π) ((p : ℤ) + (c : ℤ)))).hom :=
    (classMapToSupport_comp_supportCohomologyToPushforward (restrictEquations W f) _).symm
  rw [← Category.assoc, chartGysin_formula, gysinFormulaHom, Category.assoc, chartTargetHom,
    hFFC, Category.assoc, Iso.hom_inv_id_assoc]
  refine congrArg (fun φ ↦ gysinWedgeHom (W.ι ≫ π) (restrictEquations W f) (p : ℤ) ≫ φ) ?_
  refine Eq.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun φ ↦ φ ≫
        (eqToHom (supportCohomologySheaf_congr hgT
            (isClosed_equationsClosedSet (restrictEquations W f)) hT (c : ℤ)
            ((Scheme.Modules.restrictFunctor W.ι).obj
              (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) ≫
          (supportCohomologyRestrictIso W (isClosed_range_base i) hT (c : ℤ)
            (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).inv))
        (classMapToSupport_naturality (restrictEquations W f)
          (relativeDifferentialFormsRestrictIso π W ((p : ℤ) + (c : ℤ))).inv
          (isClosed_equationsClosedSet (restrictEquations W f)) subset_rfl (hfrac _)).symm).trans
      (Category.assoc _ _ _))) ?_
  exact congrArg (fun φ ↦
      (relativeDifferentialFormsRestrictIso π W ((p : ℤ) + (c : ℤ))).inv ≫ φ)
    (classMapToSupport_comp_eqToHom (restrictEquations W f) _ hT hgT
      (supportCohomologyRestrictIso W (isClosed_range_base i) hT (c : ℤ)
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).inv)

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- **The Gysin formula of [Stacks, Tag 0G83] for the local Gysin map of a chart, on sections, for
any number of equations.**  On the restriction `ω̃|_Z` of an ambient `p`-form over an open of the
chart, the chart's Gysin map takes the value `c_{f₁, …, f_c}(ω̃|_Z) ∧ d f₁ ∧ ⋯ ∧ d f_c`. -/
theorem chartLoc_subschemeFormPullbackOfClassMap (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    {c : ℕ} (p : ℕ) (W : X.Opens) (f : Fin c → Γ(X, W)) (hcut : IsCutOutByEquationsOn i W f)
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hgT : equationsClosedSet (restrictEquations W f) = W.ι ⁻¹' Set.range i.base)
    (hfrac : ∀ {F G : W.toScheme.Modules} (φ : F ⟶ G),
      fracTermTop (restrictEquations W f) F ≫ (cplxMap (restrictEquations W f) φ).f c =
        φ ≫ fracTermTop (restrictEquations W f) G)
    (V : X.Opens) (hV : V ≤ W) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    chartLoc i π p W f hcut hgT V hV (subschemeFormPullback i π (p : ℤ) V ω) =
      chartClsOfClassMap i π p W (restrictEquations W f) hT hgT.le V hV
        (gysinWedgeOn π f (p : ℤ) hV ω) := by
  have hA1 := srcIso_hom_app_subschemeFormPullback i π W p V ω
  have hStep3 := congrArg (fun φ ↦ Scheme.Modules.Hom.app φ (W.ι ⁻¹ᵁ V)
      (Scheme.Modules.Hom.app (relativeDifferentialFormsRestrictIso π W (p : ℤ)).hom
        (W.ι ⁻¹ᵁ V) ((relativeDifferentialForms π (p : ℤ)).presheaf.map
          (homOfLE (W.ι.image_preimage_le V)).op ω)))
    (formRestriction_comp_chartGysin_comp_chartTargetHomOfClassMap i π p W f hcut hT hgT hfrac)
  have hA4 := gysinWedgeHom_app_relativeDifferentialFormsRestrictIso π W f (p : ℤ) V hV ω
  have hinv := congrArg (fun φ ↦ Scheme.Modules.Hom.app φ (W.ι ⁻¹ᵁ V)
      ((relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).presheaf.map
        (homOfLE (W.ι.image_preimage_le V)).op (gysinWedgeOn π f (p : ℤ) hV ω)))
    (relativeDifferentialFormsRestrictIso π W ((p : ℤ) + (c : ℤ))).hom_inv_id
  refine congrArg ((gysinTarget i π c p).presheaf.map
    (homOfLE (ι_image_chartOpen W hV).ge).op) ?_
  refine Eq.trans (congrArg (fun z ↦ Scheme.Modules.Hom.app
    (chartGysin i π W f p hcut ≫ chartTargetHom i π p W (restrictEquations W f) hgT)
    (W.ι ⁻¹ᵁ V) z) hA1) ?_
  refine Eq.trans hStep3 ?_
  refine congrArg (Scheme.Modules.Hom.app
    (chartClsHomOfClassMap i π p W (restrictEquations W f) hT hgT.le) (W.ι ⁻¹ᵁ V)) ?_
  refine Eq.trans (congrArg (Scheme.Modules.Hom.app
    (relativeDifferentialFormsRestrictIso π W ((p : ℤ) + (c : ℤ))).inv
    (W.ι ⁻¹ᵁ V)) hA4) ?_
  exact hinv

/-! ### The class map of a chart is local, for any number of equations -/

/-- **The class map `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q] along an arbitrary open immersion, for
any number of equations.** -/
def openImmersionClsHomOfClassMap {Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) {c : ℕ} (p : ℕ) (g : Y ⟶ X) [IsOpenImmersion g] (f : Fin c → Γ(Y, ⊤))
    (hT : IsClosed (g ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ g ⁻¹' Set.range i.base) :
    (Scheme.Modules.restrictFunctor g).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) ⟶
      (Scheme.Modules.restrictFunctor g).obj (gysinTarget i π c p) :=
  haveI : (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p c
  classMapToSupport f
      ((Scheme.Modules.restrictFunctor g).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))) hT hTf ≫
    (supportCohomologyOpenImmersionIso g (isClosed_range_base i) hT (c : ℤ)
      (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).inv

/-- **At the inclusion of an open subscheme the class map along an open immersion is the class map
of the chart.** -/
theorem openImmersionClsHomOfClassMap_ι (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (p : ℕ) (W : X.Opens) (f : Fin c → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base) :
    openImmersionClsHomOfClassMap i π p W.ι f hT hTf =
      chartClsHomOfClassMap i π p W f hT hTf := rfl

/-- **The class map of [Stacks, Tag 0G7Q] along an open immersion is local, for any number of
equations.**  Along a composite `l ≫ g` of open immersions, for the equations of `g` restricted
along `l`, it is the class map along `g` restricted along `l`, with
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` mediating at the source and the target. -/
theorem openImmersionClsHomOfClassMap_comp {Y Y' : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ) (l : Y ⟶ Y') (g : Y' ⟶ X)
    [IsOpenImmersion l] [IsOpenImmersion g] (f : Fin c → Γ(Y', ⊤))
    (hT : IsClosed (g ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ g ⁻¹' Set.range i.base)
    (hTl : IsClosed (l ⁻¹' (g ⁻¹' Set.range i.base)))
    (hTfl : equationsClosedSet (fun j => l.appTop (f j)) ⊆
      l ⁻¹' (g ⁻¹' Set.range i.base))
    (hbase : ∀ (M : Y'.Modules),
      (Scheme.Modules.restrictFunctor l).map (fracTermTop f M) ≫
          (Stacks.Perfect.CechDerivedSupportImmersion.restrictCplxIso l f M).hom.f c =
        fracTermTop (fun j => l.appTop (f j)) ((Scheme.Modules.restrictFunctor l).obj M))
    (hnatl : ∀ {F G : Y.Modules} (φ : F ⟶ G),
      fracTermTop (fun j => l.appTop (f j)) F ≫
          (cplxMap (fun j => l.appTop (f j)) φ).f c =
        φ ≫ fracTermTop (fun j => l.appTop (f j)) G) :
    openImmersionClsHomOfClassMap i π p (l ≫ g) (fun j => l.appTop (f j)) hTl hTfl =
      (Scheme.Modules.restrictFunctorComp l g).hom.app
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) ≫
        (Scheme.Modules.restrictFunctor l).map (openImmersionClsHomOfClassMap i π p g f hT hTf) ≫
          (Scheme.Modules.restrictFunctorComp l g).inv.app (gysinTarget i π c p) := by
  have : (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p c
  have hbc := (Iso.eq_comp_inv (supportCohomologyOpenImmersionIso l hT hTl (c : ℤ)
      ((Scheme.Modules.restrictFunctor g).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))))).mpr
    (map_classMapToSupport_comp_supportCohomologyRestrictIso l f
      ((Scheme.Modules.restrictFunctor g).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))) hT hTf hTl hTfl
      (hbase _))
  have : ((Scheme.Modules.restrictFunctor g ⋙ Scheme.Modules.restrictFunctor l).obj
      (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).IsQuasicoherent :=
    inferInstanceAs (((Scheme.Modules.restrictFunctor l).obj
      ((Scheme.Modules.restrictFunctor g).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))).IsQuasicoherent)
  have hnat := classMapToSupport_naturality (fun j ↦ l.appTop (f j))
    ((Scheme.Modules.restrictFunctorComp l g).hom.app
      (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))) hTl hTfl (hnatl _)
  refine Eq.trans (congrArg (fun ψ ↦ classMapToSupport (fun j ↦ l.appTop (f j))
      ((Scheme.Modules.restrictFunctor (l ≫ g)).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))) hTl hTfl ≫ ψ)
    (supportCohomologyOpenImmersionIso_inv_comp l g (isClosed_range_base i) hT hTl
      (c : ℤ) (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) ?_
  refine Eq.trans (chaseNat _ _ _ _ _ _ _ hnat) (Eq.symm ?_)
  refine Eq.trans (congrArg (fun ψ ↦ (Scheme.Modules.restrictFunctorComp l g).hom.app
      (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) ≫ ψ ≫
    (Scheme.Modules.restrictFunctorComp l g).inv.app (gysinTarget i π c p))
    ((Scheme.Modules.restrictFunctor l).map_comp _ _)) ?_
  exact congrArg (fun ψ ↦ (Scheme.Modules.restrictFunctorComp l g).hom.app
      (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) ≫
    (ψ ≫ (Scheme.Modules.restrictFunctor l).map
        (supportCohomologyOpenImmersionIso g (isClosed_range_base i) hT (c : ℤ)
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).inv) ≫
    (Scheme.Modules.restrictFunctorComp l g).inv.app (gysinTarget i π c p)) hbc

/-! ### Transport along an equality of open immersions, and the chart-to-chart leg -/

/-- **The class map along an open immersion transports along an equality of open immersions**, for
any number of equations: for equal open immersions `g = g' : Y ⟶ X` the class map commutes with
the reindexing `AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` of the restriction
functors. -/
theorem openImmersionClsHomOfClassMap_congr {Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) {c : ℕ} (p : ℕ) {g g' : Y ⟶ X} [inst : IsOpenImmersion g]
    [inst' : IsOpenImmersion g'] (h : g = g') (f : Fin c → Γ(Y, ⊤))
    (hT : IsClosed (g ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ g ⁻¹' Set.range i.base)
    (hT' : IsClosed (g' ⁻¹' Set.range i.base))
    (hTf' : equationsClosedSet f ⊆ g' ⁻¹' Set.range i.base) :
    (Scheme.Modules.restrictFunctorCongr h).hom.app
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) ≫
        openImmersionClsHomOfClassMap i π p g' f hT' hTf' =
      openImmersionClsHomOfClassMap i π p g f hT hTf ≫
        (Scheme.Modules.restrictFunctorCongr h).hom.app (gysinTarget i π c p) := by
  subst h
  obtain rfl : inst = inst' := rfl
  obtain rfl : hT = hT' := rfl
  obtain rfl : hTf = hTf' := rfl
  rw [Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorCongr_rfl]
  simp only [NatTrans.id_app, Category.id_comp, Category.comp_id]

/-- **The class map of a chart depends on the equations only through the family**, for any number
of equations: two equal families give the same class map. -/
theorem chartClsHomOfClassMap_congr_equations (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    {c : ℕ} (p : ℕ) (W : X.Opens) {f f' : Fin c → Γ(W.toScheme, ⊤)} (hff' : f = f')
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (hTf' : equationsClosedSet f' ⊆ W.ι ⁻¹' Set.range i.base) :
    chartClsHomOfClassMap i π p W f hT hTf = chartClsHomOfClassMap i π p W f' hT hTf' := by
  subst hff'
  rfl

/-- **The class map of a chart is local along the chart-to-chart leg
`AlgebraicGeometry.Scheme.homOfLE`, for any number of equations.** For charts `W' ≤ W`, the class
map of `W'` with the restricted equations is the restriction along `X.homOfLE e` of the class map
of `W`, up to the reindexings `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` along `X.homOfLE e ≫ W.ι = W'.ι`. -/
theorem chartClsHomOfClassMap_homOfLE (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (p : ℕ) {W' W : X.Opens} (e : W' ≤ W) (f : Fin c → Γ(X, W))
    (hTW : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTfW : equationsClosedSet (restrictEquations W f) ⊆ W.ι ⁻¹' Set.range i.base)
    (hTW' : IsClosed (W'.ι ⁻¹' Set.range i.base))
    (hTe : IsClosed (X.homOfLE e ⁻¹' (W.ι ⁻¹' Set.range i.base)))
    (hTfW' : equationsClosedSet
        (restrictEquations W' (fun k => X.presheaf.map (homOfLE e).op (f k))) ⊆
      W'.ι ⁻¹' Set.range i.base)
    (hTfe : equationsClosedSet (fun j => (X.homOfLE e).appTop (restrictEquations W f j)) ⊆
      X.homOfLE e ⁻¹' (W.ι ⁻¹' Set.range i.base))
    (hbase : ∀ (M : W.toScheme.Modules),
      (Scheme.Modules.restrictFunctor (X.homOfLE e)).map
            (fracTermTop (restrictEquations W f) M) ≫
          (Stacks.Perfect.CechDerivedSupportImmersion.restrictCplxIso (X.homOfLE e)
            (restrictEquations W f) M).hom.f c =
        fracTermTop (fun j => (X.homOfLE e).appTop (restrictEquations W f j))
          ((Scheme.Modules.restrictFunctor (X.homOfLE e)).obj M))
    (hnatl : ∀ {F G : W'.toScheme.Modules} (φ : F ⟶ G),
      fracTermTop (fun j => (X.homOfLE e).appTop (restrictEquations W f j)) F ≫
          (cplxMap (fun j => (X.homOfLE e).appTop (restrictEquations W f j)) φ).f c =
        φ ≫ fracTermTop (fun j => (X.homOfLE e).appTop (restrictEquations W f j)) G) :
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι e)).hom.app
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) ≫
        chartClsHomOfClassMap i π p W'
          (restrictEquations W' (fun k => X.presheaf.map (homOfLE e).op (f k)))
          hTW' hTfW' =
      ((Scheme.Modules.restrictFunctorComp (X.homOfLE e) W.ι).hom.app
            (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE e)).map
              (chartClsHomOfClassMap i π p W (restrictEquations W f) hTW hTfW) ≫
            (Scheme.Modules.restrictFunctorComp (X.homOfLE e) W.ι).inv.app
              (gysinTarget i π c p)) ≫
        (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι e)).hom.app (gysinTarget i π c p) := by
  have hfam : (fun j ↦ (X.homOfLE e).appTop (restrictEquations W f j)) =
      restrictEquations W' (fun k ↦ X.presheaf.map (homOfLE e).op (f k)) :=
    funext fun j ↦ (restrictEquations_homOfLE e f j).symm
  have hTfe' : equationsClosedSet
      (fun j ↦ (X.homOfLE e).appTop (restrictEquations W f j)) ⊆
        W'.ι ⁻¹' Set.range i.base := by
    rwa [hfam]
  refine Eq.trans (congrArg (fun ψ ↦
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι e)).hom.app
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) ≫ ψ)
    (chartClsHomOfClassMap_congr_equations i π p W' hfam.symm hTW' hTfW' hTfe')) ?_
  refine Eq.trans (openImmersionClsHomOfClassMap_congr i π p (X.homOfLE_ι e)
    (fun j ↦ (X.homOfLE e).appTop (restrictEquations W f j)) hTe hTfe hTW' hTfe') ?_
  exact congrArg (fun ψ ↦ ψ ≫ (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι e)).hom.app
      (gysinTarget i π c p))
    (openImmersionClsHomOfClassMap_comp i π p (X.homOfLE e) W.ι (restrictEquations W f)
      hTW hTfW hTe hTfe hbase hnatl)

/-! ### The class map of a chart on sections, at two charts -/

/-- `chartClsOfClassMap` with the open of the chart and the identification of its image supplied:
the class map of the chart over an open `O` of `W` with `W.ι ''ᵁ O = V`, read on the sections over
`V`. -/
def chartClsOnOfClassMap (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ)
    (W : X.Opens) (f : Fin c → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (O : W.toScheme.Opens) (hO : W.ι ''ᵁ O = V) :
    Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V) →+ Γ(gysinTarget i π c p, V) :=
  (((gysinTarget i π c p).presheaf.map (homOfLE hO.ge).op).hom).comp
    ((((chartClsHomOfClassMap i π p W f hT hTf).val.app (op O)).hom.toAddMonoidHom).comp
      (((relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).presheaf.map (homOfLE hO.le).op).hom))

/-- `chartClsOfClassMap` is `chartClsOnOfClassMap` at the chart's own open. -/
theorem chartClsOfClassMap_eq_chartClsOnOfClassMap (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) {c : ℕ} (p : ℕ) (W : X.Opens) (f : Fin c → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W) :
    chartClsOfClassMap i π p W f hT hTf V hV =
      chartClsOnOfClassMap i π p W f hT hTf V (chartOpen W hV) (ι_image_chartOpen W hV) := rfl

/-- **The class map of a chart on sections does not depend on which open of the chart is used to
read them.** -/
theorem chartClsOnOfClassMap_congr (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (p : ℕ) (W : X.Opens) (f : Fin c → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (O O' : W.toScheme.Opens) (hO : W.ι ''ᵁ O = V) (hO' : W.ι ''ᵁ O' = V) :
    chartClsOnOfClassMap i π p W f hT hTf V O hO =
      chartClsOnOfClassMap i π p W f hT hTf V O' hO' := by
  obtain rfl : O = O' := W.ι.image_injective (hO.trans hO'.symm)
  rfl

/-- **The class map of a chart on sections is local, for any number of equations: over an open
contained in a chart it is the class map of that open's own chart.** -/
theorem chartClsOfClassMap_homOfLE (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (p : ℕ) {V W : X.Opens} (e : V ≤ W) (f : Fin c → Γ(X, W))
    (hTW : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTfW : equationsClosedSet (restrictEquations W f) ⊆ W.ι ⁻¹' Set.range i.base)
    (hTV : IsClosed (V.ι ⁻¹' Set.range i.base))
    (hTfV : equationsClosedSet
        (restrictEquations V (fun k => X.presheaf.map (homOfLE e).op (f k))) ⊆
      V.ι ⁻¹' Set.range i.base)
    (hbase : ∀ (M : W.toScheme.Modules),
      (Scheme.Modules.restrictFunctor (X.homOfLE e)).map
            (fracTermTop (restrictEquations W f) M) ≫
          (Stacks.Perfect.CechDerivedSupportImmersion.restrictCplxIso (X.homOfLE e)
            (restrictEquations W f) M).hom.f c =
        fracTermTop (fun j => (X.homOfLE e).appTop (restrictEquations W f j))
          ((Scheme.Modules.restrictFunctor (X.homOfLE e)).obj M))
    (hnatl : ∀ {F G : V.toScheme.Modules} (φ : F ⟶ G),
      fracTermTop (fun j => (X.homOfLE e).appTop (restrictEquations W f j)) F ≫
          (cplxMap (fun j => (X.homOfLE e).appTop (restrictEquations W f j)) φ).f c =
        φ ≫ fracTermTop (fun j => (X.homOfLE e).appTop (restrictEquations W f j)) G)
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V)) :
    chartClsOfClassMap i π p W (restrictEquations W f) hTW hTfW V e y =
      chartClsOfClassMap i π p V
        (restrictEquations V (fun k => X.presheaf.map (homOfLE e).op (f k)))
        hTV hTfV V le_rfl y := by
  have hTe : IsClosed (X.homOfLE e ⁻¹' (W.ι ⁻¹' Set.range i.base)) :=
    Stacks.Perfect.CechDerivedSupportImmersion.isClosed_restrictClosedSubset
      (X.homOfLE e) hTW
  have hTfe := Stacks.Perfect.CechDerivedSupportImmersion.equationsClosedSet_restrict_subset
    (X.homOfLE e) (restrictEquations W f) hTfW
  have heq := chartClsHomOfClassMap_homOfLE i π p e f hTW hTfW hTV hTe hTfV hTfe hbase hnatl
  have hA : W.ι ''ᵁ (X.homOfLE e ''ᵁ chartOpen V le_rfl) = V :=
    (congrArg (fun U ↦ W.ι ''ᵁ U) (image_chartOpen_self e)).trans (ι_image_chartOpen W e)
  have hC : (X.homOfLE e ≫ W.ι) ''ᵁ chartOpen V le_rfl = V :=
    (Scheme.Hom.comp_image (X.homOfLE e) W.ι (chartOpen V le_rfl)).trans hA
  change chartClsOnOfClassMap i π p W (restrictEquations W f) hTW hTfW V (chartOpen W e)
      (ι_image_chartOpen W e) y = _
  rw [chartClsOnOfClassMap_congr i π p W (restrictEquations W f) hTW hTfW V (chartOpen W e)
    (X.homOfLE e ''ᵁ chartOpen V le_rfl) (ι_image_chartOpen W e) hA]
  have E := congrArg (fun ψ :
      (Scheme.Modules.restrictFunctor (X.homOfLE e ≫ W.ι)).obj
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) ⟶
        (Scheme.Modules.restrictFunctor V.ι).obj (gysinTarget i π c p) ↦
    (Scheme.Modules.Hom.app ψ (chartOpen V le_rfl))
      (((relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).presheaf.map
        (homOfLE hC.le).op) y)) heq
  exact sandwich (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) (gysinTarget i π c p)
    (fun z ↦ (Scheme.Modules.Hom.app
      (chartClsHomOfClassMap i π p W (restrictEquations W f) hTW hTfW)
      (X.homOfLE e ''ᵁ chartOpen V le_rfl)) z)
    (fun z ↦ (Scheme.Modules.Hom.app
      (chartClsHomOfClassMap i π p V
        (restrictEquations V (fun k ↦ X.presheaf.map (homOfLE e).op (f k))) hTV hTfV)
      (chartOpen V le_rfl)) z)
    y _ _ _ _ (homOfLE hC.le).op _ _ _ _ E

end Stacks.Gysin

end
