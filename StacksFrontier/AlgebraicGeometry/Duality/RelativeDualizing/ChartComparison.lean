module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.AdaptedOpens
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ChartFactorization
public import StacksFrontier.AlgebraicGeometry.Modules.AffineChartSheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Comparing two affine charts of a quasi-finite morphism over an adapted open

Let `f : Y ⟶ X` be locally of finite type and locally quasi-finite between locally Noetherian
schemes. An affine chart of `f` is an affine open `V` of `Y` inside the preimage of an affine open
`U` of `X`; the chart carries the algebraic relative dualizing module `ω_{Γ(Y,V)/Γ(X,U)}` of a
finite-open factorization `F` of `Γ(X, U) → Γ(Y, V)` (Tag 0BSZ), and hence the sheaf of
`𝒪_Y`-modules `Stacks.Modules.chartSheaf V ω` whose sections over a principal open of `V` are the
corresponding localization.

This file compares the sections of two such chart sheaves over an *adapted open* of `f`
(`Stacks.Discriminant.AdaptedOpen`): an affine open `W` of `Y` over an affine open `U'` of `X`,
with `W` principal in each chart's source open and `U'` principal in each chart's base open.

The comparison is built by **two** steps of Tag 0BT2 and not three, which is the shape worth
recording: part (2) localizes the target from `Γ(Y, V)` to `Γ(Y, W)`, keeping the base `Γ(X, U)`;
part (1) then replaces the base by its localization `Γ(X, U')`, keeping the target. The route
through part (3) — localizing the base and the induced principal open of the source, and then
localizing the target again — needs the intermediate open `V ⊓ f ⁻¹ᵁ U'` and one more step. Both
steps are available at a chart with no extra hypotheses: all the algebra instances they demand are
the chart's own.

What matters for glueing is that the *target* of the comparison, the dualizing module of the
factorization `adaptedFactorization f k` of `Γ(X, k.base) → Γ(Y, k.source)`, depends on the
adapted open alone and not on the chart. That is exactly why the cocycle identity
`adaptedComparison_trans` is free: three comparisons between three charts all factor through one
module, so composing two of them cancels a comparison with its inverse.

## Main definitions

* `Stacks.Discriminant.chartDualizingEquivBasicOpen`: the two-step comparison, stated at a
  principal-open presentation of the adapted open.
* `Stacks.Discriminant.adaptedFactorization`: the finite-open factorization attached to an adapted
  open, over its base open and with its source open as target.
* `Stacks.Discriminant.chartDualizingEquiv`: the comparison of one chart with
  `adaptedFactorization`, at an adapted open good for that chart.
* `Stacks.Discriminant.adaptedComparison`: the comparison of two charts over an adapted open good
  for both.

## Main results

* `Stacks.Discriminant.adaptedComparison_trans`: the cocycle identity.

## Implementation notes

An adapted open records its source and base as *opens*, and goodness for a chart only asserts the
*existence* of functions presenting them as principal opens of that chart. The comparison is
therefore defined in two stages: `chartDualizingEquivOfPresentation` takes the presenting
functions and the two equalities of opens as arguments, destructures the adapted open so that its
two opens become variables, and substitutes the equalities — which is what makes the result a
statement about `k.source` and `k.base` rather than about `Y.basicOpen g` and `X.basicOpen a`.
`chartDualizingEquiv` then feeds it the chosen presentations.

The irreducibility of `dualizingModuleEquiv` is required here, not cosmetic: unfolding the
construction of the canonical comparison of Tag 0BT1 makes unification unfold `SetLike.coe`
without bound, and declarations mentioning it die on `maxRecDepth`.  It is declared
`[irreducible]` at its definition site, so nothing need be done here to obtain it.

## References

* [Stacks Project, Tag 0BSZ](https://stacks.math.columbia.edu/tag/0BSZ)
* [Stacks Project, Tag 0BT1](https://stacks.math.columbia.edu/tag/0BT1)
* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
* [Stacks Project, Tag 0BVG](https://stacks.math.columbia.edu/tag/0BVG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Discriminant

/- Unfolding the construction of the canonical comparison of two factorizations makes
unification unfold `SetLike.coe` without bound; every declaration here mentions it.
`dualizingModuleEquiv` is therefore declared `[irreducible]` at its definition site, so no
attribute is needed here. -/

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [LocallyOfFiniteType f] [LocallyQuasiFinite f]

/-- **The two-step comparison of Tag 0BT2, at a principal-open presentation.** For a chart
`(U, V)` of `f`, a function `a` on the base chart and a function `g` on the source chart with
`D(g)` lying over `D(a)`, the sections over `D(g)` of the chart sheaf of the dualizing module of a
factorization `F` of `Γ(X, U) → Γ(Y, V)` are identified with the dualizing module of any
factorization `Gk` of `Γ(X, D(a)) → Γ(Y, D(g))`: part (2) of Tag 0BT2 localizes the target from
`Γ(Y, V)` to `Γ(Y, D(g))`, part (1) then replaces the base `Γ(X, U)` by `Γ(X, D(a))`. -/
public def chartDualizingEquivBasicOpen (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (a : Γ(X, U.1)) (g : Γ(Y, V.1))
    (hgU : Y.basicOpen g ≤ f ⁻¹ᵁ X.basicOpen a) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, X.basicOpen a) Γ(Y, Y.basicOpen g) :=
      (f.appLE (X.basicOpen a) (Y.basicOpen g) hgU).hom.toAlgebra
    ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (Gk : FiniteOpenFactorization.{u, u, u} Γ(X, X.basicOpen a) Γ(Y, Y.basicOpen g)),
      Γ(Stacks.Modules.chartSheaf V (ModuleCat.of _ (dualizingModule F)), Y.basicOpen g)
        ≃ₗ[Γ(Y, Y.basicOpen g)] dualizingModule Gk := by
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  letI : Algebra Γ(Y, V.1) Γ(Y, Y.basicOpen g) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  letI : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen g) :=
    (f.appLE U.1 (Y.basicOpen g) ((Y.basicOpen_le g).trans hVU)).hom.toAlgebra
  letI : Algebra Γ(X, X.basicOpen a) Γ(Y, Y.basicOpen g) :=
    (f.appLE (X.basicOpen a) (Y.basicOpen g) hgU).hom.toAlgebra
  letI : Algebra Γ(X, U.1) Γ(X, X.basicOpen a) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
  letI : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, Y.basicOpen g) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (f.appLE U.1 (Y.basicOpen g) ((Y.basicOpen_le g).trans hVU)).hom =
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom).comp (f.appLE U V hVU).hom
      rw [← CommRingCat.hom_comp, ← f.appLE_map hVU (homOfLE (Y.basicOpen_le g)).op])
  letI : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen a) Γ(Y, Y.basicOpen g) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (f.appLE U.1 (Y.basicOpen g) ((Y.basicOpen_le g).trans hVU)).hom =
        ((f.appLE (X.basicOpen a) (Y.basicOpen g) hgU).hom).comp
          (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
      rw [← CommRingCat.hom_comp, f.map_appLE hgU (homOfLE (X.basicOpen_le a)).op])
  letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  letI : IsNoetherianRing Γ(Y, Y.basicOpen g) :=
    IsLocallyNoetherian.component_noetherian ⟨Y.basicOpen g, V.2.basicOpen g⟩
  letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, Y.basicOpen g) :=
    RingHom.quasiFinite_algebraMap.mp
      (LocallyQuasiFinite.quasiFinite_appLE U.2 (V.2.basicOpen g) ((Y.basicOpen_le g).trans hVU))
  letI : IsLocalization.Away g Γ(Y, Y.basicOpen g) := V.2.isLocalization_basicOpen g
  letI : IsLocalization.Away a Γ(X, X.basicOpen a) := U.2.isLocalization_basicOpen a
  intro F Gk
  letI : IsScalarTower Γ(Y, V.1) Γ(Y, Y.basicOpen g)
      Γ(Stacks.Modules.chartSheaf V (ModuleCat.of _ (dualizingModule F)), Y.basicOpen g) :=
    IsScalarTower.of_compHom Γ(Y, V.1) Γ(Y, Y.basicOpen g) _
  let G := (nonempty_relativeDualizingChartFactorization f U ⟨Y.basicOpen g, V.2.basicOpen g⟩
    ((Y.basicOpen_le g).trans hVU)).some
  exact (localizedModule_dualizingModule_equiv g F G
      (Stacks.Modules.chartSectionBasicOpen V (ModuleCat.of _ (dualizingModule F)) g)
      (Stacks.Modules.isLocalizedModule_chartSectionBasicOpen V _ g)).trans
    (dualizingModule_equiv_of_isLocalization_away a G Gk)

/-- **The finite-open factorization attached to an adapted open**: a factorization of
`Γ(X, k.base) → Γ(Y, k.source)`, which exists because an adapted open is itself a chart of `f`.
It depends on the adapted open alone, which is what makes the cocycle identity free. -/
public def adaptedFactorization (k : AdaptedOpen f) :
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    FiniteOpenFactorization.{u, u, u} Γ(X, k.base.1) Γ(Y, k.source.1) :=
  (nonempty_relativeDualizingChartFactorization f k.base k.source k.source_le).some

/-- `chartDualizingEquivBasicOpen` read at an adapted open, given functions presenting its source
and base opens as principal opens of the chart. -/
public def chartDualizingEquivOfPresentation (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (k : AdaptedOpen f) (g : Γ(Y, V.1))
    (hg : Y.basicOpen g = k.source.1) (a : Γ(X, U.1)) (ha : X.basicOpen a = k.base.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      Γ(Stacks.Modules.chartSheaf V (ModuleCat.of _ (dualizingModule F)), k.source.1)
        ≃ₗ[Γ(Y, k.source.1)] dualizingModule (adaptedFactorization f k) := by
  obtain ⟨⟨Ws, hWs⟩, ⟨Bs, hBs⟩, hle⟩ := k
  change Y.basicOpen g = Ws at hg
  change X.basicOpen a = Bs at ha
  subst hg
  subst ha
  exact fun F => chartDualizingEquivBasicOpen f U V hVU a g hle F _

/-- **The comparison of a chart with the dualizing module of an adapted open good for it.** -/
public def chartDualizingEquiv (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (k : AdaptedOpen f) (hk : k.Good V U) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      Γ(Stacks.Modules.chartSheaf V (ModuleCat.of _ (dualizingModule F)), k.source.1)
        ≃ₗ[Γ(Y, k.source.1)] dualizingModule (adaptedFactorization f k) :=
  chartDualizingEquivOfPresentation f U V hVU k
    hk.1.choose hk.1.choose_spec hk.2.choose hk.2.choose_spec

/-- **The comparison of two charts over an adapted open good for both**, obtained by composing
the comparison of the first chart with the adapted open's dualizing module and the inverse of the
comparison of the second. -/
public def adaptedComparison (U₁ : X.affineOpens) (V₁ : Y.affineOpens) (hVU₁ : V₁.1 ≤ f ⁻¹ᵁ U₁.1)
    (U₂ : X.affineOpens) (V₂ : Y.affineOpens) (hVU₂ : V₂.1 ≤ f ⁻¹ᵁ U₂.1)
    (k : AdaptedOpen f) (hk₁ : k.Good V₁ U₁) (hk₂ : k.Good V₂ U₂) :
    letI : Algebra Γ(X, U₁.1) Γ(Y, V₁.1) := (f.appLE U₁ V₁ hVU₁).hom.toAlgebra
    letI : Algebra Γ(X, U₂.1) Γ(Y, V₂.1) := (f.appLE U₂ V₂ hVU₂).hom.toAlgebra
    ∀ (F₁ : FiniteOpenFactorization.{u, u, u} Γ(X, U₁.1) Γ(Y, V₁.1))
      (F₂ : FiniteOpenFactorization.{u, u, u} Γ(X, U₂.1) Γ(Y, V₂.1)),
      Γ(Stacks.Modules.chartSheaf V₁ (ModuleCat.of _ (dualizingModule F₁)), k.source.1)
        ≃ₗ[Γ(Y, k.source.1)]
      Γ(Stacks.Modules.chartSheaf V₂ (ModuleCat.of _ (dualizingModule F₂)), k.source.1) := by
  letI : Algebra Γ(X, U₁.1) Γ(Y, V₁.1) := (f.appLE U₁ V₁ hVU₁).hom.toAlgebra
  letI : Algebra Γ(X, U₂.1) Γ(Y, V₂.1) := (f.appLE U₂ V₂ hVU₂).hom.toAlgebra
  letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
    (f.appLE k.base k.source k.source_le).hom.toAlgebra
  exact fun F₁ F₂ => (chartDualizingEquiv f U₁ V₁ hVU₁ k hk₁ F₁).trans
    (chartDualizingEquiv f U₂ V₂ hVU₂ k hk₂ F₂).symm

/-- **The cocycle identity for the chart comparison is free.** All three comparisons between three
charts factor through the dualizing module of `adaptedFactorization f k`, which depends on the
adapted open alone, so composing two of them cancels one comparison with its inverse. -/
public theorem adaptedComparison_trans (U₁ : X.affineOpens) (V₁ : Y.affineOpens)
    (hVU₁ : V₁.1 ≤ f ⁻¹ᵁ U₁.1) (U₂ : X.affineOpens) (V₂ : Y.affineOpens)
    (hVU₂ : V₂.1 ≤ f ⁻¹ᵁ U₂.1) (U₃ : X.affineOpens) (V₃ : Y.affineOpens)
    (hVU₃ : V₃.1 ≤ f ⁻¹ᵁ U₃.1)
    (k : AdaptedOpen f) (hk₁ : k.Good V₁ U₁) (hk₂ : k.Good V₂ U₂) (hk₃ : k.Good V₃ U₃) :
    letI : Algebra Γ(X, U₁.1) Γ(Y, V₁.1) := (f.appLE U₁ V₁ hVU₁).hom.toAlgebra
    letI : Algebra Γ(X, U₂.1) Γ(Y, V₂.1) := (f.appLE U₂ V₂ hVU₂).hom.toAlgebra
    letI : Algebra Γ(X, U₃.1) Γ(Y, V₃.1) := (f.appLE U₃ V₃ hVU₃).hom.toAlgebra
    ∀ (F₁ : FiniteOpenFactorization.{u, u, u} Γ(X, U₁.1) Γ(Y, V₁.1))
      (F₂ : FiniteOpenFactorization.{u, u, u} Γ(X, U₂.1) Γ(Y, V₂.1))
      (F₃ : FiniteOpenFactorization.{u, u, u} Γ(X, U₃.1) Γ(Y, V₃.1))
      (s : Γ(Stacks.Modules.chartSheaf V₁ (ModuleCat.of _ (dualizingModule F₁)), k.source.1)),
      adaptedComparison f U₂ V₂ hVU₂ U₃ V₃ hVU₃ k hk₂ hk₃ F₂ F₃
          (adaptedComparison f U₁ V₁ hVU₁ U₂ V₂ hVU₂ k hk₁ hk₂ F₁ F₂ s) =
        adaptedComparison f U₁ V₁ hVU₁ U₃ V₃ hVU₃ k hk₁ hk₃ F₁ F₃ s := by
  let : Algebra Γ(X, U₁.1) Γ(Y, V₁.1) := (f.appLE U₁ V₁ hVU₁).hom.toAlgebra
  let : Algebra Γ(X, U₂.1) Γ(Y, V₂.1) := (f.appLE U₂ V₂ hVU₂).hom.toAlgebra
  let : Algebra Γ(X, U₃.1) Γ(Y, V₃.1) := (f.appLE U₃ V₃ hVU₃).hom.toAlgebra
  let : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
    (f.appLE k.base k.source k.source_le).hom.toAlgebra
  intro F₁ F₂ F₃ s
  show (chartDualizingEquiv f U₃ V₃ hVU₃ k hk₃ F₃).symm
      ((chartDualizingEquiv f U₂ V₂ hVU₂ k hk₂ F₂)
        ((chartDualizingEquiv f U₂ V₂ hVU₂ k hk₂ F₂).symm
          ((chartDualizingEquiv f U₁ V₁ hVU₁ k hk₁ F₁) s))) =
    (chartDualizingEquiv f U₃ V₃ hVU₃ k hk₃ F₃).symm
      ((chartDualizingEquiv f U₁ V₁ hVU₁ k hk₁ F₁) s)
  rw [LinearEquiv.apply_symm_apply]

end Stacks.Discriminant

end
