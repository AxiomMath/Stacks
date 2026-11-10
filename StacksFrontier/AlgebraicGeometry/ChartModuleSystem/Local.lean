module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.ChartModuleSystem.Basic

/-!
# Descent within a chart

Let `S` be a chart module system. On a chart `d`, the modules on the refinements of `d` are the
localizations of `M d`, and this file shows that they satisfy the sheaf condition for coverings of
`V d` by refinements: an element of `M d` is determined by its restrictions to such a covering
(`AlgebraicGeometry.ChartModuleSystem.eq_of_ρ_eq`), and a family of elements of the modules on a
covering by refinements which agree on all common refinements comes from an element of `M d`
(`AlgebraicGeometry.ChartModuleSystem.exists_ρ_eq`).

The proof compares the modules on the refinements of `d` with the sections of the tilde `M d^~` on
`Spec Γ(Y, V d)` over the preimages of the refinements: for a refinement `e` with `V e = D(g)`,
both `M e` and `Γ(M d^~, D(g))` are localizations of `M d` away from `g`
(`AlgebraicGeometry.ChartModuleSystem.chartTildeEquiv`), compatibly with the restriction maps
(`AlgebraicGeometry.ChartModuleSystem.map_chartTildeEquiv`), and the sheaf condition for `M d^~`
does the rest.

## Main results

* `AlgebraicGeometry.Scheme.AffineChartIndex.isBaseChangeAlong_iff_isLocalizedModule`: the
  localization axiom of a chart module system can be verified as a localization statement.
* `AlgebraicGeometry.ChartModuleSystem.isLocalizedModule_ρ`: the restriction maps are
  localizations.
* `AlgebraicGeometry.ChartModuleSystem.eq_of_ρ_eq` and
  `AlgebraicGeometry.ChartModuleSystem.exists_ρ_eq`: separation and gluing within a chart.
* `AlgebraicGeometry.ChartModuleSystem.existsUnique_of_sieve`: the same for a sieve of charts.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ChartModuleSystem

open Scheme

variable {Y : Scheme.{u}} {I : Y.AffineChartIndex} (S : ChartModuleSystem I)

/-- **The localization axiom of a chart module system, in localization form.** For a refinement
`c'` of `c` with `V c' = D(g)`, a semilinear map `M c → M c'` along the restriction of functions
is a base change exactly when, read `Γ(Y, V c)`-linearly, it is the localization away from `g`.
This is the way to verify `AlgebraicGeometry.ChartModuleSystem.isBaseChangeAlong_ρ` from a
localization statement. -/
theorem _root_.AlgebraicGeometry.Scheme.AffineChartIndex.isBaseChangeAlong_iff_isLocalizedModule
    {c' c : I.ι} (h : I.Refines c' c) (g : Γ(Y, (I.V c).1)) (hg : (I.V c').1 = Y.basicOpen g)
    {N₁ N₂ : Type*} [AddCommGroup N₁] [Module Γ(Y, (I.V c).1) N₁] [AddCommGroup N₂]
    [Module Γ(Y, (I.V c').1) N₂] (f : N₁ →ₛₗ[I.res h] N₂) :
    f.IsBaseChangeAlong ↔
      letI : Module Γ(Y, (I.V c).1) N₂ := Module.compHom _ (I.res h)
      IsLocalizedModule (Submonoid.powers g) f.restrictScalarsAlong :=
  LinearMap.isBaseChangeAlong_iff_isLocalizedModule g
    ((I.isAffineOpen c).isLocalization_of_eq_basicOpen g (homOfLE (I.le_of_refines h)) hg) f

/-- **The restriction maps are localizations.** If `V c' = D(g)` for `g : Γ(Y, V c)`, the
restriction `M c → M c'`, read `Γ(Y, V c)`-linearly, is the localization away from `g`. -/
theorem isLocalizedModule_ρ {c' c : I.ι} (h : I.Refines c' c) (g : Γ(Y, (I.V c).1))
    (hg : (I.V c').1 = Y.basicOpen g) :
    letI : Module Γ(Y, (I.V c).1) (S.M c') := Module.compHom _ (I.res h)
    IsLocalizedModule (Submonoid.powers g) (S.ρ h).restrictScalarsAlong :=
  (I.isBaseChangeAlong_iff_isLocalizedModule h g hg _).mp (S.isBaseChangeAlong_ρ h)

/-- The module on the chart `d`, as an object of `ModuleCat Γ(Y, V d)`. -/
abbrev chartModule (d : I.ι) : ModuleCat.{u} Γ(Y, (I.V d).1) :=
  ModuleCat.of _ (S.M d)

/-- The sheaf `M^~` on `Spec Γ(Y, V d)` attached to the module on the chart `d`, as a sheaf of
`Γ(Y, V d)`-modules. -/
noncomputable abbrev chartTilde (d : I.ι) :
    TopCat.Sheaf (ModuleCat.{u} Γ(Y, (I.V d).1)) (Spec Γ(Y, (I.V d).1)) :=
  modulesSpecToSheaf.obj (tilde (S.chartModule d))

/-- The preimage in `Spec Γ(Y, V d)` of a chart refining `d`. -/
noncomputable abbrev chartPreimage {e d : I.ι} (_h : I.Refines e d) :
    (Spec Γ(Y, (I.V d).1)).Opens :=
  (I.V d).2.fromSpec ⁻¹ᵁ (I.V e).1

/-- A chosen function `g` on `V d` with `V e = D(g)`. -/
noncomputable def gen {e d : I.ι} (h : I.Refines e d) : Γ(Y, (I.V d).1) :=
  (I.exists_eq_basicOpen h).choose

/-- The chart `e` is the basic open of the chosen function `gen h`. -/
theorem eq_basicOpen_gen {e d : I.ι} (h : I.Refines e d) :
    (I.V e).1 = Y.basicOpen (gen h) :=
  (I.exists_eq_basicOpen h).choose_spec

/-- The preimage of a refinement `V e = D(g)` in `Spec Γ(Y, V d)` is the basic open `D(g)`. -/
theorem chartPreimage_eq {e d : I.ι} (h : I.Refines e d) :
    chartPreimage h = PrimeSpectrum.basicOpen (gen h) := by
  rw [chartPreimage, eq_basicOpen_gen h]
  exact (I.V d).2.fromSpec_preimage_basicOpen _

/-- The sections of `M d^~` over the preimage of a refinement `e` are the localization of
`M d` away from `gen h`. -/
instance isLocalizedModule_toOpen_chartPreimage {e d : I.ι} (h : I.Refines e d) :
    IsLocalizedModule (Submonoid.powers (gen h))
      (tilde.toOpen (S.chartModule d) (chartPreimage h)).hom := by
  have key (M : ModuleCat.{u} Γ(Y, (I.V d).1)) (f : Γ(Y, (I.V d).1)) :
      IsLocalizedModule (Submonoid.powers f) (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom :=
    inferInstance
  rw [chartPreimage_eq h]
  exact key _ _

/-- The comparison between the module on a refinement `e` of `d` and the sections of the tilde
of `M d` over the preimage of `V e`: both are localizations of `M d` away from `g`. -/
noncomputable def chartTildeEquiv {e d : I.ι} (h : I.Refines e d) :
    letI : Module Γ(Y, (I.V d).1) (S.M e) := Module.compHom _ (I.res h)
    S.M e ≃ₗ[Γ(Y, (I.V d).1)] (S.chartTilde d).presheaf.obj (op (chartPreimage h)) :=
  letI : Module Γ(Y, (I.V d).1) (S.M e) := Module.compHom _ (I.res h)
  haveI := S.isLocalizedModule_ρ h (gen h) (eq_basicOpen_gen h)
  IsLocalizedModule.linearEquiv (Submonoid.powers (gen h)) (S.ρ h).restrictScalarsAlong
    (tilde.toOpen (S.chartModule d) (chartPreimage h)).hom

/-- `chartTildeEquiv` sends the restriction of `x : M d` to its image in `M d^~`. -/
theorem chartTildeEquiv_ρ {e d : I.ι} (h : I.Refines e d) (x : S.M d) :
    S.chartTildeEquiv h (S.ρ h x) = (tilde.toOpen (S.chartModule d) (chartPreimage h)).hom x :=
  let : Module Γ(Y, (I.V d).1) (S.M e) := Module.compHom _ (I.res h)
  have := S.isLocalizedModule_ρ h (gen h) (eq_basicOpen_gen h)
  IsLocalizedModule.linearEquiv_apply _ _ _ x

/-- Taking preimages of charts is monotone. -/
theorem chartPreimage_mono {e₁ e₂ d : I.ι} (h₁ : I.Refines e₁ d) (h₂ : I.Refines e₂ d)
    (hle : (I.V e₂).1 ≤ (I.V e₁).1) : chartPreimage h₂ ≤ chartPreimage h₁ :=
  Scheme.Hom.preimage_mono _ hle

/-- Membership in the preimage of a chart. -/
theorem mem_chartPreimage {e d : I.ι} (h : I.Refines e d) {p : Spec Γ(Y, (I.V d).1)} :
    p ∈ chartPreimage h ↔ (I.V d).2.fromSpec p ∈ (I.V e).1 :=
  Iff.rfl

/-- Every point of a chart comes from `Spec Γ(Y, V d)`. -/
theorem exists_fromSpec_eq {d : I.ι} {y : Y} (hy : y ∈ (I.V d).1) :
    ∃ p : Spec Γ(Y, (I.V d).1), (I.V d).2.fromSpec p = y :=
  Set.mem_range.mp (by rwa [(I.V d).2.range_fromSpec])

/-- The points of `Spec Γ(Y, V d)` map into `V d`. -/
theorem fromSpec_mem {d : I.ι} (p : Spec Γ(Y, (I.V d).1)) : (I.V d).2.fromSpec p ∈ (I.V d).1 :=
  (I.V d).2.range_fromSpec.subset (Set.mem_range_self p)

/-- The comparison `chartTildeEquiv` commutes with restriction: restricting in the tilde sheaf
from a refinement `e₁` of `d` to a refinement `e₂` of `e₁` is the restriction `ρ` of the chart
system. -/
theorem map_chartTildeEquiv {e₁ e₂ d : I.ι} (h₁ : I.Refines e₁ d) (h₂₁ : I.Refines e₂ e₁)
    (h₂ : I.Refines e₂ d) (i : chartPreimage h₂ ⟶ chartPreimage h₁) (x : S.M e₁) :
    (S.chartTilde d).presheaf.map i.op (S.chartTildeEquiv h₁ x) =
      S.chartTildeEquiv h₂ (S.ρ h₂₁ x) := by
  let : Module Γ(Y, (I.V d).1) (S.M e₁) := Module.compHom _ (I.res h₁)
  let : Module Γ(Y, (I.V d).1) (S.M e₂) := Module.compHom _ (I.res h₂)
  have := S.isLocalizedModule_ρ h₁ (gen h₁) (eq_basicOpen_gen h₁)
  let ρ₂₁ : S.M e₁ →ₗ[Γ(Y, (I.V d).1)] S.M e₂ :=
    { toFun := S.ρ h₂₁
      map_add' := map_add _
      map_smul' := fun a x => by
        change S.ρ h₂₁ (I.res h₁ a • x) = I.res h₂ a • S.ρ h₂₁ x
        rw [map_smulₛₗ, I.res_res] }
  have key : ((S.chartTilde d).presheaf.map i.op).hom ∘ₗ (S.chartTildeEquiv h₁).toLinearMap =
      (S.chartTildeEquiv h₂).toLinearMap ∘ₗ ρ₂₁ := by
    refine IsLocalizedModule.ext (Submonoid.powers (gen h₁)) (S.ρ h₁).restrictScalarsAlong
      (fun ⟨_, n, hn⟩ => ?_) (LinearMap.ext fun x => ?_)
    · subst hn
      rw [map_pow]
      refine (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := tilde _) _ ?_).pow n
      rw [← chartPreimage_eq h₁]
      exact i.le
    · change (S.chartTilde d).presheaf.map i.op (S.chartTildeEquiv h₁ (S.ρ h₁ x)) =
        S.chartTildeEquiv h₂ (S.ρ h₂₁ (S.ρ h₁ x))
      rw [chartTildeEquiv_ρ, S.ρ_ρ, chartTildeEquiv_ρ]
      rfl
  exact LinearMap.congr_fun key x

/-- A family of refinements of `d` covering `V d` has preimages covering `Spec Γ(Y, V d)`. -/
theorem le_iSup_chartPreimage {d : I.ι} {J : Type u} {κ : J → I.ι}
    (hκ : ∀ j, I.Refines (κ j) d) (hcov : ∀ y ∈ (I.V d).1, ∃ j, y ∈ (I.V (κ j)).1) :
    ⊤ ≤ ⨆ j, chartPreimage (hκ j) := by
  intro p _
  obtain ⟨j, hj⟩ := hcov _ (fromSpec_mem p)
  exact Opens.mem_iSup.mpr ⟨j, hj⟩

/-- **Separation within a chart.** Two elements of `M d` with the same restrictions to a family
of refinements of `d` covering `V d` are equal. -/
theorem eq_of_ρ_eq {d : I.ι} {J : Type u} (κ : J → I.ι) (hκ : ∀ j, I.Refines (κ j) d)
    (hcov : ∀ y ∈ (I.V d).1, ∃ j, y ∈ (I.V (κ j)).1) {x₁ x₂ : S.M d}
    (h : ∀ j, S.ρ (hκ j) x₁ = S.ρ (hκ j) x₂) : x₁ = x₂ := by
  refine (ConcreteCategory.bijective_of_isIso (tilde.toOpen (S.chartModule d) ⊤)).injective
    ((S.chartTilde d).eq_of_locally_eq' (fun j => chartPreimage (hκ j)) ⊤
      (fun j => homOfLE le_top) (le_iSup_chartPreimage hκ hcov) _ _ fun j => ?_)
  have h₁ := S.chartTildeEquiv_ρ (hκ j) x₁
  rw [h j] at h₁
  exact h₁.symm.trans (S.chartTildeEquiv_ρ (hκ j) x₂)

/-- **Gluing within a chart.** A family of elements of the modules on a family of refinements of
`d` covering `V d`, compatible on every common refinement of two members, comes from an element of
`M d`. -/
theorem exists_ρ_eq {d : I.ι} {J : Type u} (κ : J → I.ι) (hκ : ∀ j, I.Refines (κ j) d)
    (hcov : ∀ y ∈ (I.V d).1, ∃ j, y ∈ (I.V (κ j)).1) (t : ∀ j, S.M (κ j))
    (ht : ∀ j₁ j₂ (e : I.ι) (h₁ : I.Refines e (κ j₁)) (h₂ : I.Refines e (κ j₂)),
      S.ρ h₁ (t j₁) = S.ρ h₂ (t j₂)) :
    ∃ x : S.M d, ∀ j, S.ρ (hκ j) x = t j := by
  let sf : ∀ j, (S.chartTilde d).presheaf.obj (op (chartPreimage (hκ j))) :=
    fun j => S.chartTildeEquiv (hκ j) (t j)
  have hcompat : TopCat.Presheaf.IsCompatible (S.chartTilde d).presheaf
      (fun j => chartPreimage (hκ j)) sf := by
    intro j₁ j₂
    let K := {e : I.ι // I.Refines e (κ j₁) ∧ I.Refines e (κ j₂)}
    have hK : ∀ k : K, I.Refines k.1 d := fun k => I.refines_trans k.2.1 (hκ j₁)
    refine (S.chartTilde d).eq_of_locally_eq' (fun k : K => chartPreimage (hK k)) _
      (fun k => homOfLE (le_inf (chartPreimage_mono _ _ (I.le_of_refines k.2.1))
        (chartPreimage_mono _ _ (I.le_of_refines k.2.2)))) ?_ _ _ fun k => ?_
    · rintro p ⟨hp₁, hp₂⟩
      obtain ⟨e, he₁, he₂, hpe⟩ := I.exists_refines_refines hp₁ hp₂
      exact Opens.mem_iSup.mpr ⟨⟨e, he₁, he₂⟩, hpe⟩
    · simp only [sf, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rw [S.map_chartTildeEquiv (hκ j₁) k.2.1 (hK k), S.map_chartTildeEquiv (hκ j₂) k.2.2 (hK k),
        ht j₁ j₂ k.1 k.2.1 k.2.2]
  obtain ⟨s, hs, -⟩ := (S.chartTilde d).existsUnique_gluing' (fun j => chartPreimage (hκ j)) ⊤
    (fun j => homOfLE le_top) (le_iSup_chartPreimage hκ hcov) sf hcompat
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (tilde.toOpen (S.chartModule d) ⊤)).surjective s
  exact ⟨x, fun j => (S.chartTildeEquiv (hκ j)).injective ((S.chartTildeEquiv_ρ _ x).trans (hs j))⟩

/-- **Descent within a chart, for a sieve of refinements.** Let `P` be a property of charts stable
under refinement such that the refinements of `d` with `P` cover `V d`, and let `m` be a family of
elements of the modules on the charts with `P`, compatible with restriction. Then there is a unique
element of `M d` restricting to `m e` on every refinement `e` of `d` with `P`. -/
theorem existsUnique_of_sieve (d : I.ι) (P : I.ι → Prop)
    (hPref : ∀ ⦃e' e : I.ι⦄, P e → I.Refines e' e → P e')
    (hcov : ∀ y ∈ (I.V d).1, ∃ e, P e ∧ I.Refines e d ∧ y ∈ (I.V e).1)
    (m : ∀ e, P e → S.M e)
    (hm : ∀ ⦃e' e : I.ι⦄ (he : P e) (h : I.Refines e' e), m e' (hPref he h) = S.ρ h (m e he)) :
    ∃! x : S.M d, ∀ e (he : P e) (h : I.Refines e d), S.ρ h x = m e he := by
  let J := {e : I.ι // P e ∧ I.Refines e d}
  have hJcov : ∀ y ∈ (I.V d).1, ∃ j : J, y ∈ (I.V j.1).1 := fun y hy => by
    obtain ⟨e, he, hed, hye⟩ := hcov y hy
    exact ⟨⟨e, he, hed⟩, hye⟩
  obtain ⟨x, hx⟩ := S.exists_ρ_eq (fun j : J => j.1) (fun j => j.2.2) hJcov
    (fun j => m j.1 j.2.1) fun j₁ j₂ e h₁ h₂ => by
      rw [← hm j₁.2.1 h₁, ← hm j₂.2.1 h₂]
  exact ⟨x, fun e he h => hx ⟨e, he, h⟩, fun x' hx' =>
    S.eq_of_ρ_eq (fun j : J => j.1) (fun j => j.2.2) hJcov fun j =>
      (hx' j.1 j.2.1 j.2.2).trans (hx j).symm⟩

end AlgebraicGeometry.ChartModuleSystem
