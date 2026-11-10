module

public import StacksFrontier.AlgebraicGeometry.ChartModuleSystem.Sheaf

/-!
# Morphisms of chart module systems

Morphisms of chart module systems induce morphisms of the glued sheaves, in two situations.

On one index of charts of `Y`, compatible linear maps `M c → N c` induce a morphism of glued
sheaves (`AlgebraicGeometry.ChartModuleSystem.sheafHom`), functorially, and compatible linear
equivalences an isomorphism (`AlgebraicGeometry.ChartModuleSystem.sheafIso`).

Along a morphism of schemes `b : Y' ⟶ Y`, with indices `I'` of `Y'` and `I` of `Y`, the data are a
relation `Over c' c` between charts of `Y'` and of `Y` with `V c' ≤ b⁻¹(V c)`
(`AlgebraicGeometry.Scheme.AffineChartIndex.MapData`), and maps `τ : M c → M' c'` semilinear along
`Γ(Y, V c) → Γ(Y', V c')` compatible with the restrictions on both sides
(`AlgebraicGeometry.ChartModuleSystem.MapData`). They induce
`AlgebraicGeometry.ChartModuleSystem.MapData.pushforwardMap : S.sheaf ⟶ b_* S'.sheaf`, whose
sections over a chart `c`, restricted to a chart `c'` over `c`, are `τ`.

## Main definitions

* `AlgebraicGeometry.ChartModuleSystem.sheafHom`, `AlgebraicGeometry.ChartModuleSystem.sheafIso`.
* `AlgebraicGeometry.Scheme.AffineChartIndex.MapData`: charts of `Y'` lying over charts of `Y`.
* `AlgebraicGeometry.ChartModuleSystem.MapData`: a morphism of chart module systems along `b`.
* `AlgebraicGeometry.ChartModuleSystem.MapData.pushforwardMap`: the induced morphism
  `S.sheaf ⟶ b_* S'.sheaf`.

## Main results

* `AlgebraicGeometry.ChartModuleSystem.sectionsEquiv_sheafHom_app`,
  `AlgebraicGeometry.ChartModuleSystem.eq_sheafHom`,
  `AlgebraicGeometry.ChartModuleSystem.sheafHom_id` and
  `AlgebraicGeometry.ChartModuleSystem.sheafHom_comp`.
* `AlgebraicGeometry.ChartModuleSystem.MapData.sectionsEquiv_pushforwardMap_app`: the sections of
  `pushforwardMap` are `τ`, and `AlgebraicGeometry.ChartModuleSystem.MapData.eq_pushforwardMap`:
  this characterizes it; in particular it only depends on the maps `τ`
  (`AlgebraicGeometry.ChartModuleSystem.MapData.pushforwardMap_congr`).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme

namespace ChartModuleSystem

variable {Y : Scheme.{u}} {I : Y.AffineChartIndex}

/-! ### Morphisms of systems on the same index -/

section SameIndex

variable {S N : ChartModuleSystem I} (f : ∀ c, S.M c →ₗ[Γ(Y, (I.V c).1)] N.M c)
  (hf : ∀ ⦃c' c : I.ι⦄ (h : I.Refines c' c) (x : S.M c), N.ρ h (f c x) = f c' (S.ρ h x))

/-- **The morphism of glued sheaves induced by compatible maps on the charts.** -/
noncomputable def sheafHom : S.sheaf ⟶ N.sheaf :=
  S.homOfCompatible (fun c => (N.sectionsEquiv c).symm.toLinearMap ∘ₗ f c) fun c' c h x =>
    (N.sectionsEquiv c').injective (by
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.apply_symm_apply]
      rw [sectionsEquiv_restrict, LinearEquiv.apply_symm_apply, hf])

/-- On sections over a chart, `sheafHom f` is `f`. -/
theorem sectionsEquiv_sheafHom_app (c : I.ι) (s : Γ(S.sheaf, (I.V c).1)) :
    N.sectionsEquiv c ((sheafHom f hf).app (I.V c).1 s) = f c (S.sectionsEquiv c s) := by
  rw [sheafHom, homOfCompatible_app]
  exact LinearEquiv.apply_symm_apply _ _

/-- **A morphism of glued sheaves is determined by its effect on the charts.** -/
theorem sheafHom_ext {g₁ g₂ : S.sheaf ⟶ N.sheaf}
    (h : ∀ c (s : Γ(S.sheaf, (I.V c).1)),
      N.sectionsEquiv c (g₁.app (I.V c).1 s) = N.sectionsEquiv c (g₂.app (I.V c).1 s)) :
    g₁ = g₂ :=
  S.hom_ext fun c _ => (N.sectionsEquiv c).injective (h c _)

/-- `sheafHom f` is the unique morphism of glued sheaves that is `f` on the charts. -/
theorem eq_sheafHom {g : S.sheaf ⟶ N.sheaf}
    (hg : ∀ c (s : Γ(S.sheaf, (I.V c).1)),
      N.sectionsEquiv c (g.app (I.V c).1 s) = f c (S.sectionsEquiv c s)) :
    g = sheafHom f hf :=
  sheafHom_ext fun c s => (hg c s).trans (sectionsEquiv_sheafHom_app f hf c s).symm

end SameIndex

/-- The identity maps on the charts induce the identity of the glued sheaf. -/
theorem sheafHom_id (S : ChartModuleSystem I) :
    sheafHom (S := S) (N := S) (fun _ => LinearMap.id) (fun _ _ _ _ => rfl) = 𝟙 S.sheaf :=
  (eq_sheafHom _ _ fun _ _ => rfl).symm

/-- Composites of compatible maps on the charts induce composites of glued sheaves. -/
theorem sheafHom_comp {S N L : ChartModuleSystem I} (f : ∀ c, S.M c →ₗ[Γ(Y, (I.V c).1)] N.M c)
    (hf : ∀ ⦃c' c : I.ι⦄ (h : I.Refines c' c) (x : S.M c), N.ρ h (f c x) = f c' (S.ρ h x))
    (g : ∀ c, N.M c →ₗ[Γ(Y, (I.V c).1)] L.M c)
    (hg : ∀ ⦃c' c : I.ι⦄ (h : I.Refines c' c) (x : N.M c), L.ρ h (g c x) = g c' (N.ρ h x)) :
    sheafHom (fun c => g c ∘ₗ f c) (fun c' c h x => by
        simp only [LinearMap.coe_comp, Function.comp_apply, hg, hf]) =
      sheafHom f hf ≫ sheafHom g hg :=
  (eq_sheafHom _ _ fun c s => by
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, sectionsEquiv_sheafHom_app,
      sectionsEquiv_sheafHom_app]
    rfl).symm

/-- **Compatible isomorphisms on the charts induce an isomorphism of glued sheaves.** -/
noncomputable def sheafIso {S N : ChartModuleSystem I} (e : ∀ c, S.M c ≃ₗ[Γ(Y, (I.V c).1)] N.M c)
    (he : ∀ ⦃c' c : I.ι⦄ (h : I.Refines c' c) (x : S.M c), N.ρ h (e c x) = e c' (S.ρ h x)) :
    S.sheaf ≅ N.sheaf where
  hom := sheafHom (fun c => (e c).toLinearMap) he
  inv := sheafHom (fun c => (e c).symm.toLinearMap) fun c' c h x => (e c').injective (by
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [← he, LinearEquiv.apply_symm_apply])
  hom_inv_id := by
    rw [← sheafHom_comp, ← sheafHom_id]
    exact sheafHom_ext fun c s => by
      rw [sectionsEquiv_sheafHom_app, sectionsEquiv_sheafHom_app]
      exact (e c).symm_apply_apply _
  inv_hom_id := by
    rw [← sheafHom_comp, ← sheafHom_id]
    exact sheafHom_ext fun c s => by
      rw [sectionsEquiv_sheafHom_app, sectionsEquiv_sheafHom_app]
      exact (e c).apply_symm_apply _

end ChartModuleSystem

/-! ### Charts lying over charts -/

/-- **Charts of `Y'` lying over charts of `Y` along `b : Y' ⟶ Y`.** A relation `Over c' c` between
the charts of `I'` and those of `I`, with `V c' ≤ b⁻¹(V c)` whenever `Over c' c`, stable under
refinement of `c'`, and such that the charts of `Y'` over a chart `c` of `Y` cover `b⁻¹(V c)`
arbitrarily finely. -/
structure Scheme.AffineChartIndex.MapData {Y' Y : Scheme.{u}} (b : Y' ⟶ Y)
    (I' : Y'.AffineChartIndex) (I : Y.AffineChartIndex) where
  /-- `Over c' c`: the chart `c'` of `Y'` lies over the chart `c` of `Y`. -/
  Over : I'.ι → I.ι → Prop
  /-- A chart over `c` lies in the preimage of `V c`. -/
  le_preimage : ∀ {c' : I'.ι} {c : I.ι}, Over c' c → (I'.V c').1 ≤ b ⁻¹ᵁ (I.V c).1
  /-- A refinement of a chart over `c` lies over `c`. -/
  over_of_refines : ∀ {c'' c' : I'.ι} {c : I.ι}, Over c' c → I'.Refines c'' c' → Over c'' c
  /-- The charts over `c` cover the preimage of `V c` arbitrarily finely. -/
  exists_over : ∀ {c : I.ι} {y' : Y'}, y' ∈ b ⁻¹ᵁ (I.V c).1 → ∀ {W : Y'.Opens}, y' ∈ W →
    ∃ c', Over c' c ∧ y' ∈ (I'.V c').1 ∧ (I'.V c').1 ≤ W

namespace Scheme.AffineChartIndex.MapData

variable {Y' Y : Scheme.{u}} {b : Y' ⟶ Y} {I' : Y'.AffineChartIndex} {I : Y.AffineChartIndex}
  (D : MapData b I' I)

/-- The pullback of functions from a chart of `Y` to a chart of `Y'` over it. -/
noncomputable def appLE {c' : I'.ι} {c : I.ι} (h : D.Over c' c) :
    Γ(Y, (I.V c).1) →+* Γ(Y', (I'.V c').1) :=
  (b.appLE (I.V c).1 (I'.V c').1 (D.le_preimage h)).hom

/-- Near every point of `b⁻¹(V c) ∩ V d`, some refinement of `d` lies over `c`. -/
theorem exists_over_refines {c : I.ι} {d : I'.ι} {y' : Y'} (hy : y' ∈ b ⁻¹ᵁ (I.V c).1)
    (hyd : y' ∈ (I'.V d).1) : ∃ e, D.Over e c ∧ I'.Refines e d ∧ y' ∈ (I'.V e).1 := by
  obtain ⟨e₀, he₀, hye₀, -⟩ := D.exists_over hy (W := ⊤) trivial
  obtain ⟨e, hee₀, hed, hye⟩ := I'.exists_refines_refines hye₀ hyd
  exact ⟨e, D.over_of_refines he₀ hee₀, hed, hye⟩

end Scheme.AffineChartIndex.MapData

namespace ChartModuleSystem

variable {Y' Y : Scheme.{u}} {b : Y' ⟶ Y} {I' : Y'.AffineChartIndex} {I : Y.AffineChartIndex}
  (D : I'.MapData b I)

/-- **A morphism of chart module systems along `b : Y' ⟶ Y`.** For every chart `c'` of `Y'` over a
chart `c` of `Y`, a map `τ : M c → M' c'` semilinear along `Γ(Y, V c) → Γ(Y', V c')`, compatible
with the restriction maps on both sides. -/
structure MapData (S : ChartModuleSystem I) (S' : ChartModuleSystem I') where
  /-- The map from the module on `c` to the module on a chart `c'` over `c`. -/
  τ : ∀ {c' : I'.ι} {c : I.ι} (h : D.Over c' c), S.M c →ₛₗ[D.appLE h] S'.M c'
  /-- Compatibility with the restriction maps on both sides. -/
  τ_ρ : ∀ {c₁' c' : I'.ι} {c₁ c : I.ι} (h : D.Over c' c) (h₁ : D.Over c₁' c₁)
    (hc : I.Refines c₁ c) (hc' : I'.Refines c₁' c') (x : S.M c),
    τ h₁ (S.ρ hc x) = S'.ρ hc' (τ h x)

namespace MapData

variable {D} {S : ChartModuleSystem I} {S' : ChartModuleSystem I'} (T : MapData D S S')

/-- `τ x` on a finer chart is the restriction of `τ x` on the coarser one. -/
private theorem ρ_τ {c : I.ι} (x : S.M c) {e e₁ : I'.ι} (he : D.Over e c) (h : I'.Refines e₁ e) :
    T.τ (D.over_of_refines he h) x = S'.ρ h (T.τ he x) := by
  rw [← T.τ_ρ he (D.over_of_refines he h) (I.refines_refl c) h, S.ρ_refl]

/-- The family `τ x` on the charts over `c` extends uniquely to a compatible family over
`b⁻¹(V c)`. -/
theorem existsUnique_pushforwardSection (c : I.ι) (x : S.M c) :
    ∃! s : S'.sectionsSubgroup (b ⁻¹ᵁ (I.V c).1),
      ∀ e (he : D.Over e c), s.1 ⟨e, D.le_preimage he⟩ = T.τ he x :=
  S'.existsUnique_sectionsSubgroup (b ⁻¹ᵁ (I.V c).1) (D.Over · c)
    (fun _ he => D.le_preimage he) (fun _ _ => D.over_of_refines)
    (fun _ hd _ hy => D.exists_over_refines (hd hy) hy) (fun _ he => T.τ he x)
    fun _ _ => T.ρ_τ x

/-- The section of `M'` over `b⁻¹(V c)` attached to an element of `M c`: its value on a chart
`c'` over `c` is `τ`. -/
noncomputable def pushforwardSection (c : I.ι) (x : S.M c) :
    S'.sectionsSubgroup (b ⁻¹ᵁ (I.V c).1) :=
  (T.existsUnique_pushforwardSection c x).exists.choose

/-- The section attached to `x` takes the value `τ x` on a chart over `c`. -/
theorem pushforwardSection_apply (c : I.ι) (x : S.M c) {e : I'.ι} (he : D.Over e c) :
    (T.pushforwardSection c x).1 ⟨e, D.le_preimage he⟩ = T.τ he x :=
  (T.existsUnique_pushforwardSection c x).exists.choose_spec e he

/-- `pushforwardSection` is characterized by its values on the charts over `c`. -/
theorem pushforwardSection_eq {c : I.ι} {x : S.M c} {s : S'.sectionsSubgroup (b ⁻¹ᵁ (I.V c).1)}
    (hs : ∀ e (he : D.Over e c), s.1 ⟨e, D.le_preimage he⟩ = T.τ he x) :
    T.pushforwardSection c x = s :=
  (T.existsUnique_pushforwardSection c x).unique (fun _ he => T.pushforwardSection_apply c x he) hs

/-- `pushforwardSection` as a `Γ(Y, V c)`-linear map into the sections of the pushforward. -/
noncomputable def pushforwardApp (c : I.ι) :
    S.M c →ₗ[Γ(Y, (I.V c).1)] Γ((Scheme.Modules.pushforward b).obj S'.sheaf, (I.V c).1) where
  toFun x := T.pushforwardSection c x
  map_add' x y := T.pushforwardSection_eq fun e he => by
    change (T.pushforwardSection c x).1 _ + (T.pushforwardSection c y).1 _ = _
    rw [pushforwardSection_apply, pushforwardSection_apply, map_add]
  map_smul' r x := by
    refine T.pushforwardSection_eq fun e he => ?_
    change (Y'.presheaf.map (homOfLE (D.le_preimage he)).op).hom ((b.app (I.V c).1).hom r) •
      (T.pushforwardSection c x).1 _ = _
    rw [pushforwardSection_apply, map_smulₛₗ]
    rfl

/-- The value of the section attached to `x : M c` on any chart `e` contained in `b⁻¹(V c)`
restricts, on every refinement of `e` over `c`, to `τ x`. -/
theorem ρ_pushforwardSection (c : I.ι) (x : S.M c) {e e₁ : I'.ι}
    (he : (I'.V e).1 ≤ b ⁻¹ᵁ (I.V c).1) (h₁ : D.Over e₁ c) (h₁e : I'.Refines e₁ e) :
    S'.ρ h₁e ((T.pushforwardSection c x).1 ⟨e, he⟩) = T.τ h₁ x := by
  rw [sectionsSubgroup_compat _ h₁e he (D.le_preimage h₁), pushforwardSection_apply]

/-- The maps `pushforwardApp` commute with the restriction maps. -/
theorem pushforwardApp_compat ⦃c' c : I.ι⦄ (h : I.Refines c' c) (x : S.M c) :
    ((Scheme.Modules.pushforward b).obj S'.sheaf).presheaf.map (homOfLE (I.le_of_refines h)).op
      (T.pushforwardApp c x) = T.pushforwardApp c' (S.ρ h x) := by
  refine (T.pushforwardSection_eq fun e he => ?_).symm
  let J := {e₁ : I'.ι // D.Over e₁ c ∧ I'.Refines e₁ e}
  have hle : (I'.V e).1 ≤ b ⁻¹ᵁ (I.V c).1 :=
    (D.le_preimage he).trans (b.preimage_mono (I.le_of_refines h))
  refine S'.eq_of_ρ_eq (fun j : J => j.1) (fun j => j.2.2) (fun y hy => ?_) fun j => ?_
  · obtain ⟨e₁, h₁, h₁e, hy₁⟩ := D.exists_over_refines (hle hy) hy
    exact ⟨⟨e₁, h₁, h₁e⟩, hy₁⟩
  · change S'.ρ j.2.2 ((T.pushforwardSection c x).1 ⟨e, hle⟩) = _
    rw [T.ρ_pushforwardSection c x hle j.2.1 j.2.2, ← T.ρ_τ (S.ρ h x) he j.2.2,
      T.τ_ρ j.2.1 (D.over_of_refines he j.2.2) h (I'.refines_refl _), S'.ρ_refl]

/-- **The morphism of glued sheaves along `b : Y' ⟶ Y` induced by a morphism of chart module
systems**, as a morphism `S.sheaf ⟶ b_* S'.sheaf`. On sections over a chart `c`, followed by
restriction to a chart `c'` over `c`, it is `τ` (`AlgebraicGeometry.ChartModuleSystem.MapData.
sectionsEquiv_pushforwardMap_app`). -/
noncomputable def pushforwardMap : S.sheaf ⟶ (Scheme.Modules.pushforward b).obj S'.sheaf :=
  S.homOfCompatible T.pushforwardApp T.pushforwardApp_compat

/-- **The sections of `pushforwardMap` are `τ`.** The image of a section over a chart `c`, a
section of `S'.sheaf` over `b⁻¹(V c)`, restricts on a chart `c'` over `c` to `τ` of the section. -/
theorem sectionsEquiv_pushforwardMap_app {c' : I'.ι} {c : I.ι} (h : D.Over c' c)
    (s : Γ(S.sheaf, (I.V c).1)) :
    S'.sectionsEquiv c' (S'.sheaf.presheaf.map (homOfLE (D.le_preimage h)).op
      (T.pushforwardMap.app (I.V c).1 s)) = T.τ h (S.sectionsEquiv c s) := by
  rw [pushforwardMap, homOfCompatible_app]
  exact T.pushforwardSection_apply c _ h

/-- `pushforwardMap` is the unique morphism `S.sheaf ⟶ b_* S'.sheaf` whose sections are `τ`. -/
theorem eq_pushforwardMap {g : S.sheaf ⟶ (Scheme.Modules.pushforward b).obj S'.sheaf}
    (hg : ∀ {c' : I'.ι} {c : I.ι} (h : D.Over c' c) (s : Γ(S.sheaf, (I.V c).1)),
      S'.sectionsEquiv c' (S'.sheaf.presheaf.map (homOfLE (D.le_preimage h)).op
        (g.app (I.V c).1 s)) = T.τ h (S.sectionsEquiv c s)) :
    g = T.pushforwardMap :=
  S.hom_ext fun c x => by
    rw [pushforwardMap, homOfCompatible_app]
    exact (T.pushforwardSection_eq fun e he => hg he _).symm

/-- Two morphisms of chart module systems with the same maps `τ` induce the same morphism of
glued sheaves. -/
theorem pushforwardMap_congr {T₁ T₂ : MapData D S S'}
    (h : ∀ {c' : I'.ι} {c : I.ι} (hc : D.Over c' c) (x : S.M c), T₁.τ hc x = T₂.τ hc x) :
    T₁.pushforwardMap = T₂.pushforwardMap :=
  T₂.eq_pushforwardMap fun hc s => by rw [sectionsEquiv_pushforwardMap_app, h]

end MapData

end ChartModuleSystem

end AlgebraicGeometry
