module

public import StacksFrontier.AlgebraicGeometry.ChartModuleSystem.Hom

/-!
# The pullback of a glued sheaf

Let `T` be a morphism of chart module systems along `b : Y' ⟶ Y`
(`AlgebraicGeometry.ChartModuleSystem.MapData`), with maps `τ : M c → M' c'` for the charts `c'` of
`Y'` lying over the charts `c` of `Y`. This file shows that if every `τ` is a base change,
`Γ(Y', V c') ⊗[Γ(Y, V c)] M c ≃ M' c'`, then the adjoint transpose
`b^* S.sheaf ⟶ S'.sheaf` of `T.pushforwardMap : S.sheaf ⟶ b_* S'.sheaf` is an isomorphism.

## Proof

No description of the sections of a pullback is needed. By Yoneda it suffices that composing with
the transpose is a bijection on morphisms into any `H : Y'.Modules`, that is, through the
adjunction, that every morphism `ψ : S.sheaf ⟶ b_* H` factors uniquely as `pushforwardMap ≫ b_* χ`
(`AlgebraicGeometry.ChartModuleSystem.MapData.bijective_pushforwardMap_comp`). On a chart `c'` over
`c`, the component of `χ` has to be the `Γ(Y', V c')`-linear extension along the base change `τ` of
the map `M c → Γ(H, V c')` induced by `ψ`; these extensions are independent of `c` and compatible
with restriction, so they are the components of a morphism out of `S'.sheaf` on the basis of charts
lying over charts (`AlgebraicGeometry.ChartModuleSystem.homOfFamily`).

## Main definitions

* `AlgebraicGeometry.ChartModuleSystem.MapData.pullbackMap`: the comparison
  `b^* S.sheaf ⟶ S'.sheaf`.

## Main results

* `AlgebraicGeometry.ChartModuleSystem.MapData.isIso_pullbackMap`: it is an isomorphism when every
  `τ` is a base change, and `AlgebraicGeometry.ChartModuleSystem.MapData.pullbackIso` is that
  isomorphism.
* `AlgebraicGeometry.ChartModuleSystem.MapData.pushforwardMap_comp`: `pushforwardMap` is compatible
  with composition of morphisms of schemes.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme

namespace ChartModuleSystem.MapData

variable {Y' Y : Scheme.{u}} {b : Y' ⟶ Y} {I' : Y'.AffineChartIndex} {I : Y.AffineChartIndex}
  {D : I'.MapData b I} {S : ChartModuleSystem I} {S' : ChartModuleSystem I'} (T : MapData D S S')

section Lift

variable {H : Y'.Modules} (ψ : S.sheaf ⟶ (Scheme.Modules.pushforward b).obj H)

/-- The component of `ψ : S.sheaf ⟶ b_* H` on a chart, as a map into the sections of `H` over the
preimage of the chart. -/
noncomputable def pushApp (c : I.ι) (s : Γ(S.sheaf, (I.V c).1)) : Γ(H, b ⁻¹ᵁ (I.V c).1) :=
  ψ.app (I.V c).1 s

/-- `pushApp` is additive. -/
theorem pushApp_add (c : I.ι) (s t : Γ(S.sheaf, (I.V c).1)) :
    pushApp ψ c (s + t) = pushApp ψ c s + pushApp ψ c t :=
  (ψ.app (I.V c).1).hom.map_add s t

/-- `pushApp` is semilinear along `b.app`. -/
theorem pushApp_smul (c : I.ι) (a : Γ(Y, (I.V c).1)) (s : Γ(S.sheaf, (I.V c).1)) :
    pushApp ψ c (a • s) = (b.app (I.V c).1).hom a • pushApp ψ c s :=
  Scheme.Modules.Hom.app_smul ψ a s

/-- `pushApp` commutes with restriction. -/
theorem pushApp_map {c d : I.ι} (h : (I.V d).1 ≤ (I.V c).1) (s : Γ(S.sheaf, (I.V c).1)) :
    pushApp ψ d (S.sheaf.presheaf.map (homOfLE h).op s) =
      H.presheaf.map (homOfLE (b.preimage_mono h)).op (pushApp ψ c s) :=
  ψ.app_presheaf_map (homOfLE h) s

/-- The map `M c → Γ(H, V c')` induced by a morphism `ψ : S.sheaf ⟶ b_* H`, for a chart `c'` over
`c`: a section over `V c`, pushed by `ψ` to a section of `H` over `b⁻¹(V c)`, restricted to
`V c'`. -/
noncomputable def liftAux {c' : I'.ι} {c : I.ι} (h : D.Over c' c) :
    S.M c →ₛₗ[D.appLE h] Γ(H, (I'.V c').1) where
  toFun x := H.presheaf.map (homOfLE (D.le_preimage h)).op
    (pushApp ψ c ((S.sectionsEquiv c).symm x))
  map_add' x y := by rw [map_add, pushApp_add, map_add]
  map_smul' a x := by
    rw [map_smul, pushApp_smul]
    exact Scheme.Modules.map_smul H (homOfLE (D.le_preimage h)) ((b.app (I.V c).1).hom a) _

variable (hT : ∀ ⦃c' : I'.ι⦄ ⦃c : I.ι⦄ (h : D.Over c' c), (T.τ h).IsBaseChangeAlong)

/-- The `Γ(Y', V c')`-linear extension of `liftAux ψ h` along the base change `τ`. -/
noncomputable def liftChart {c' : I'.ι} {c : I.ι} (h : D.Over c' c) :
    S'.M c' →ₗ[Γ(Y', (I'.V c').1)] Γ(H, (I'.V c').1) :=
  (hT h).lift (liftAux ψ h)

/-- `liftChart` extends the map induced by `ψ` along `τ`. -/
theorem liftChart_τ {c' : I'.ι} {c : I.ι} (h : D.Over c' c) (x : S.M c) :
    T.liftChart ψ hT h (T.τ h x) = liftAux ψ h x :=
  (hT h).lift_apply _ x

/-- `liftAux` on a restricted element is the restriction of `liftAux`. -/
private theorem liftAux_ρ {e c' : I'.ι} {c d : I.ι} (h : D.Over c' c) (h₂ : D.Over e d)
    (hd : I.Refines d c) (he : I'.Refines e c') (x : S.M c) :
    liftAux ψ h₂ (S.ρ hd x) =
      H.presheaf.map (homOfLE (I'.le_of_refines he)).op (liftAux ψ h x) := by
  obtain ⟨s, rfl⟩ := (S.sectionsEquiv c).surjective x
  rw [← sectionsEquiv_restrict]
  simp only [liftAux, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply, pushApp_map,
    Scheme.Modules.presheaf_map_comp_apply]
  rfl

/-- `liftChart` commutes with restriction to a refinement of the chart of `Y'`. -/
theorem map_liftChart {e c' : I'.ι} {c : I.ι} (h : D.Over c' c) (h' : I'.Refines e c')
    (y : S'.M c') :
    H.presheaf.map (homOfLE (I'.le_of_refines h')).op (T.liftChart ψ hT h y) =
      T.liftChart ψ hT (D.over_of_refines h h') (S'.ρ h' y) := by
  let φ₁ : S'.M c' →ₛₗ[I'.res h'] Γ(H, (I'.V e).1) :=
    { toFun := fun y => H.presheaf.map (homOfLE (I'.le_of_refines h')).op (T.liftChart ψ hT h y)
      map_add' := fun y z => by rw [map_add, map_add]
      map_smul' := fun r y => by
        rw [map_smul]
        exact Scheme.Modules.map_smul H (homOfLE (I'.le_of_refines h')) r _ }
  let φ₂ : S'.M c' →ₛₗ[I'.res h'] Γ(H, (I'.V e).1) :=
    (T.liftChart ψ hT (D.over_of_refines h h')).comp (S'.ρ h')
  have key : φ₁ = φ₂ := (hT h).ext fun x => by
    simp only [φ₁, φ₂, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [liftChart_τ, ← T.τ_ρ h (D.over_of_refines h h') (I.refines_refl c) h', liftChart_τ,
      liftAux_ρ ψ h _ (I.refines_refl c) h']
  exact LinearMap.congr_fun key y

/-- `liftChart` does not depend on the chart of `Y` below: it is unchanged by refining that
chart. -/
theorem liftChart_eq {e : I'.ι} {c d : I.ι} (h : D.Over e c) (h₂ : D.Over e d)
    (hd : I.Refines d c) : T.liftChart ψ hT h = T.liftChart ψ hT h₂ := by
  refine (hT h).ext fun x => ?_
  rw [liftChart_τ]
  have hτ : T.τ h x = T.τ h₂ (S.ρ hd x) := by
    rw [T.τ_ρ h h₂ hd (I'.refines_refl e), S'.ρ_refl]
  rw [hτ, liftChart_τ, liftAux_ρ ψ h h₂ hd (I'.refines_refl e)]
  simp

variable (D) in
/-- The pairs of a chart of `Y'` and a chart of `Y` it lies over. -/
abbrev OverPair : Type u := {p : I'.ι × I.ι // D.Over p.1 p.2}

variable (D) in
/-- The charts of `Y'` lying over some chart of `Y` form a basis of the topology of `Y'`. -/
theorem isBasis_overPair : Opens.IsBasis (Set.range fun k : OverPair D => (I'.V k.1.1).1) := by
  refine Opens.isBasis_iff_nbhd.mpr fun {W y} hy => ?_
  obtain ⟨c, hc⟩ := I.exists_mem (b y)
  obtain ⟨c', h, hyc', hc'W⟩ := D.exists_over (y' := y) hc hy
  exact ⟨_, ⟨⟨(c', c), h⟩, rfl⟩, hyc', hc'W⟩

/-- **The morphism `S'.sheaf ⟶ H` corresponding to `ψ : S.sheaf ⟶ b_* H`** when every `τ` is a
base change: on a chart `c'` over `c` it is the `Γ(Y', V c')`-linear extension along `τ` of the
map `M c → Γ(H, V c')` induced by `ψ`. -/
noncomputable def liftHom : S'.sheaf ⟶ H :=
  S'.homOfFamily (fun k : OverPair D => k.1.1) (isBasis_overPair D)
    (fun k => T.liftChart ψ hT k.2) fun k₁ k₂ y hy₁ hy₂ => by
      obtain ⟨c₃, hc₁, hc₂, hy₃⟩ := I.exists_refines_refines (D.le_preimage k₁.2 hy₁)
        (D.le_preimage k₂.2 hy₂)
      obtain ⟨e₀, he₀₁, he₀₂, hye₀⟩ := I'.exists_refines_refines hy₁ hy₂
      obtain ⟨e, he, hee₀, hye⟩ := D.exists_over_refines (y' := y) hy₃ hye₀
      refine ⟨⟨(e, c₃), he⟩, hye, I'.refines_trans hee₀ he₀₁, I'.refines_trans hee₀ he₀₂,
        fun x => ?_, fun x => ?_⟩
      · rw [T.map_liftChart ψ hT k₁.2,
          T.liftChart_eq ψ hT (D.over_of_refines k₁.2 (I'.refines_trans hee₀ he₀₁)) he hc₁]
      · rw [T.map_liftChart ψ hT k₂.2,
          T.liftChart_eq ψ hT (D.over_of_refines k₂.2 (I'.refines_trans hee₀ he₀₂)) he hc₂]

/-- The component of `liftHom` on a chart over `c` is `liftChart`. -/
theorem liftHom_app {c' : I'.ι} {c : I.ι} (h : D.Over c' c) (s : Γ(S'.sheaf, (I'.V c').1)) :
    (T.liftHom ψ hT).app (I'.V c').1 s = T.liftChart ψ hT h (S'.sectionsEquiv c' s) :=
  S'.homOfFamily_app (fun k : OverPair D => k.1.1) (isBasis_overPair D) _ _ ⟨(c', c), h⟩ s

end Lift

/-- Restricting the section over `b⁻¹(V c)` attached by `pushforwardMap` to a section over `V c`
to a chart `c'` over `c` gives the section over `V c'` attached to `τ`. -/
theorem map_pushforwardMap_app {c' : I'.ι} {c : I.ι} (h : D.Over c' c) (x : S.M c) :
    S'.sheaf.presheaf.map (homOfLE (D.le_preimage h)).op
      (pushApp T.pushforwardMap c ((S.sectionsEquiv c).symm x)) =
      (S'.sectionsEquiv c').symm (T.τ h x) :=
  (S'.sectionsEquiv c').eq_symm_apply.mpr (by
    rw [pushApp, sectionsEquiv_pushforwardMap_app, LinearEquiv.apply_symm_apply])

/-- `pushApp` of a composite with `b_* χ`. -/
theorem pushApp_comp {H H' : Y'.Modules} (ψ : S.sheaf ⟶ (Scheme.Modules.pushforward b).obj H)
    (χ : H ⟶ H') (c : I.ι) (s : Γ(S.sheaf, (I.V c).1)) :
    pushApp (ψ ≫ (Scheme.Modules.pushforward b).map χ) c s =
      χ.app (b ⁻¹ᵁ (I.V c).1) (pushApp ψ c s) :=
  rfl

/-- The composite of `pushforwardMap` with `b_* χ`, on a section over a chart `c`, restricted to a
chart `c'` over `c`. -/
theorem map_comp_app {H : Y'.Modules} (χ : S'.sheaf ⟶ H) {c' : I'.ι} {c : I.ι} (h : D.Over c' c)
    (x : S.M c) :
    H.presheaf.map (homOfLE (D.le_preimage h)).op
      (pushApp (T.pushforwardMap ≫ (Scheme.Modules.pushforward b).map χ) c
        ((S.sectionsEquiv c).symm x)) =
      χ.app (I'.V c').1 ((S'.sectionsEquiv c').symm (T.τ h x)) := by
  rw [← map_pushforwardMap_app, χ.app_presheaf_map, pushApp_comp]

variable (hT : ∀ ⦃c' : I'.ι⦄ ⦃c : I.ι⦄ (h : D.Over c' c), (T.τ h).IsBaseChangeAlong)

include hT in
/-- **Universal property of `pushforwardMap` under base change.** If every `τ` exhibits `M' c'` as
the base change of `M c`, then every morphism `S.sheaf ⟶ b_* H` factors uniquely as
`pushforwardMap` followed by `b_* χ` for a morphism `χ : S'.sheaf ⟶ H`. -/
theorem bijective_pushforwardMap_comp (H : Y'.Modules) :
    Function.Bijective fun χ : S'.sheaf ⟶ H =>
      T.pushforwardMap ≫ (Scheme.Modules.pushforward b).map χ := by
  refine ⟨fun χ₁ χ₂ hχ => ?_, fun ψ => ⟨T.liftHom ψ hT, ?_⟩⟩
  · refine S'.hom_ext_of_isBasis (fun k : OverPair D => k.1.1) (isBasis_overPair D)
      fun k x' => ?_
    let lin : (S'.sheaf ⟶ H) → (S'.M k.1.1 →ₗ[Γ(Y', (I'.V k.1.1).1)] Γ(H, (I'.V k.1.1).1)) :=
      fun χ =>
        { toFun := fun x => χ.app (I'.V k.1.1).1 ((S'.sectionsEquiv k.1.1).symm x)
          map_add' := fun x y => by
            rw [map_add]
            exact (χ.app (I'.V k.1.1).1).hom.map_add _ _
          map_smul' := fun r x => by
            rw [map_smul]
            exact Scheme.Modules.Hom.app_smul χ r _ }
    have key : lin χ₁ = lin χ₂ := (hT k.2).ext fun m => by
      change χ₁.app _ _ = χ₂.app _ _
      rw [← map_comp_app, ← map_comp_app]
      simp only at hχ
      rw [hχ]
    exact LinearMap.congr_fun key x'
  · refine S.hom_ext fun c x => ?_
    let J := {c' : I'.ι // D.Over c' c}
    refine Stacks.BasisRestriction.moduleSheafSection_ext_of_cover H (fun j : J => (I'.V j.1).1)
      (fun j => D.le_preimage j.2) (fun y hy => ?_) _ _ fun j => ?_
    · obtain ⟨c', h, hy', -⟩ := D.exists_over (y' := y) hy (W := ⊤) trivial
      exact ⟨⟨c', h⟩, hy'⟩
    · change H.presheaf.map _ (pushApp (T.pushforwardMap ≫ (Scheme.Modules.pushforward b).map
          (T.liftHom ψ hT)) c _) = H.presheaf.map _ (pushApp ψ c _)
      rw [map_comp_app T (T.liftHom ψ hT) j.2, liftHom_app T ψ hT j.2, LinearEquiv.apply_symm_apply,
        liftChart_τ T ψ hT j.2]
      rfl

/-- **The comparison map `b^* S.sheaf ⟶ S'.sheaf`**, the adjoint transpose of `pushforwardMap`
under the adjunction `b^* ⊣ b_*`. -/
noncomputable def pullbackMap : (Scheme.Modules.pullback b).obj S.sheaf ⟶ S'.sheaf :=
  ((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _).symm T.pushforwardMap

include hT in
/-- **Base change of the chart modules gives an isomorphism `b^* S.sheaf ≅ S'.sheaf`.** If for
every chart `c'` of `Y'` over a chart `c` of `Y` the map `τ : M c → M' c'` exhibits `M' c'` as the
base change `Γ(Y', V c') ⊗[Γ(Y, V c)] M c`, then the adjoint transpose of `pushforwardMap` is an
isomorphism. -/
theorem isIso_pullbackMap : IsIso T.pullbackMap := by
  refine isIso_of_coyoneda_map_bijective _ fun H => ?_
  have heq : (fun χ : S'.sheaf ⟶ H => T.pullbackMap ≫ χ) =
      ((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _).symm ∘
        fun χ : S'.sheaf ⟶ H => T.pushforwardMap ≫ (Scheme.Modules.pushforward b).map χ := by
    funext χ
    exact ((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv_naturality_right_symm _ _).symm
  rw [heq]
  exact (Equiv.bijective _).comp (T.bijective_pushforwardMap_comp hT H)

/-- **The isomorphism `b^* S.sheaf ≅ S'.sheaf`** when every `τ` is a base change; its forward
map is `pullbackMap`. -/
noncomputable def pullbackIso : (Scheme.Modules.pullback b).obj S.sheaf ≅ S'.sheaf :=
  haveI := T.isIso_pullbackMap hT
  asIso T.pullbackMap

/-- The forward map of `pullbackIso` is `pullbackMap`. -/
theorem pullbackIso_hom : (T.pullbackIso hT).hom = T.pullbackMap :=
  rfl

end ChartModuleSystem.MapData

end AlgebraicGeometry

namespace AlgebraicGeometry.ChartModuleSystem.MapData

open Scheme

variable {Y'' Y' Y : Scheme.{u}} {b₂ : Y'' ⟶ Y'} {b₁ : Y' ⟶ Y} {I'' : Y''.AffineChartIndex}
  {I' : Y'.AffineChartIndex} {I : Y.AffineChartIndex} {D₂ : I''.MapData b₂ I'}
  {D₁ : I'.MapData b₁ I} {D₁₂ : I''.MapData (b₂ ≫ b₁) I} {S'' : ChartModuleSystem I''}
  {S' : ChartModuleSystem I'} {S : ChartModuleSystem I}

/-- **`pushforwardMap` is compatible with composition.** If the maps `τ` of a morphism of chart
module systems along `b₂ ≫ b₁` are the composites of those along `b₁` and along `b₂` whenever
these are defined, then its `pushforwardMap` is the composite of the two `pushforwardMap`s. -/
theorem pushforwardMap_comp (T₁ : MapData D₁ S S') (T₂ : MapData D₂ S' S'')
    (T₁₂ : MapData D₁₂ S S'')
    (hT : ∀ {c'' : I''.ι} {c' : I'.ι} {c : I.ι} (h₂ : D₂.Over c'' c') (h₁ : D₁.Over c' c)
      (h₁₂ : D₁₂.Over c'' c) (x : S.M c), T₁₂.τ h₁₂ x = T₂.τ h₂ (T₁.τ h₁ x)) :
    T₁₂.pushforwardMap = T₁.pushforwardMap ≫
      (Scheme.Modules.pushforward b₁).map T₂.pushforwardMap ≫
        (Scheme.Modules.pushforwardComp b₂ b₁).hom.app S''.sheaf := by
  symm
  refine T₁₂.eq_pushforwardMap fun {c'' c} h₁₂ s => ?_
  let t : Γ(S'.sheaf, b₁ ⁻¹ᵁ (I.V c).1) := pushApp T₁.pushforwardMap c s
  let X : Γ(S''.sheaf, b₂ ⁻¹ᵁ (b₁ ⁻¹ᵁ (I.V c).1)) := T₂.pushforwardMap.app _ t
  change S''.sectionsEquiv c'' (S''.sheaf.presheaf.map (homOfLE (D₁₂.le_preimage h₁₂)).op X) = _
  let J := {p : I''.ι × I'.ι // D₁.Over p.2 c ∧ D₂.Over p.1 p.2 ∧ I''.Refines p.1 c''}
  refine S''.eq_of_ρ_eq (fun j : J => j.1.1) (fun j => j.2.2.2) (fun y hy => ?_) fun j => ?_
  · obtain ⟨c', h₁, hyc', -⟩ := D₁.exists_over (y' := b₂ y) (D₁₂.le_preimage h₁₂ hy) (W := ⊤)
      trivial
    obtain ⟨e, he, hec'', hye⟩ := D₂.exists_over_refines (y' := y) hyc' hy
    exact ⟨⟨(e, c'), h₁, he, hec''⟩, hye⟩
  · obtain ⟨⟨e, c'⟩, h₁, h₂, hec''⟩ := j
    change S''.ρ hec'' _ = S''.ρ hec'' _
    have hle₁ : (I'.V c').1 ≤ b₁ ⁻¹ᵁ (I.V c).1 := D₁.le_preimage h₁
    have hnat : T₂.pushforwardMap.app (I'.V c').1 (S'.sheaf.presheaf.map (homOfLE hle₁).op t) =
        S''.sheaf.presheaf.map (homOfLE (b₂.preimage_mono hle₁)).op X :=
      T₂.pushforwardMap.app_presheaf_map (homOfLE hle₁) t
    have ht : S'.sectionsEquiv c' (S'.sheaf.presheaf.map (homOfLE hle₁).op t) =
        T₁.τ h₁ (S.sectionsEquiv c s) :=
      T₁.sectionsEquiv_pushforwardMap_app h₁ s
    rw [← sectionsEquiv_restrict]
    refine Eq.trans (b := S''.sectionsEquiv e (S''.sheaf.presheaf.map
      (homOfLE (D₂.le_preimage h₂)).op (S''.sheaf.presheaf.map
        (homOfLE (b₂.preimage_mono hle₁)).op X))) rfl ?_
    rw [← hnat, T₂.sectionsEquiv_pushforwardMap_app h₂, ht,
      ← hT h₂ h₁ (D₁₂.over_of_refines h₁₂ hec''),
      ← T₁₂.τ_ρ h₁₂ (D₁₂.over_of_refines h₁₂ hec'') (I.refines_refl c) hec'', S.ρ_refl]

end AlgebraicGeometry.ChartModuleSystem.MapData
