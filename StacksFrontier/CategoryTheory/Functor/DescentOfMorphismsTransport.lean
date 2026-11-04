module

public import Mathlib.CategoryTheory.NatIso

/-!
# Transporting the descent of morphisms along comparison functors

Let `L₀ : D ⥤ D₀`, `Lδᵢ : D₀ ⥤ D₁` and `P₀ : E ⥤ E₀`, `Pδᵢ : E₀ ⥤ E₁` (`i = 0, 1`) be the
pullbacks to the two first terms of two simplicial systems, with transitions
`cᵢ : L₀ ⋙ Lδᵢ ≅ L₁` and `θᵢ : P₀ ⋙ Pδᵢ ≅ P₁`, and let comparison functors `ι` commute with
them through `N₀`, `Nδᵢ`, `N₁`. If morphisms descend along `P₀` (a morphism `ψ` whose two
transports agree comes from `E`), if `ι` is full on `M ⟶ N` and faithful on `L₀ M ⟶ L₀ N`, then
morphisms `L₀ M ⟶ L₀ N` whose two transports agree come from `M ⟶ N`. This is how the gluing of
morphisms of Stacks 0DL9 on the spaces-étale sites is read on the small étale sites.

## Main results

* `CategoryTheory.exists_map_eq_of_descent_of_comparison`
* `CategoryTheory.comp_eq_of_descent_of_comparison`: an isomorphism descended through the
  comparisons is compatible with the descent datum.
-/

@[expose] public section

namespace CategoryTheory

variable {D D₀ D₁ E E₀ E₁ : Type*} [Category* D] [Category* D₀] [Category* D₁] [Category* E]
  [Category* E₀] [Category* E₁]

/-- The inverse comparison `c⁻¹`, read through `ι₁`, in terms of `N₁`, `θ⁻¹`, `N₀⁻¹` and `Nδ⁻¹`. -/
private theorem map_inv_app_eq_of_comparison {Lx : D ⥤ D₀} {L₁ : D ⥤ D₁} {Lδ : D₀ ⥤ D₁}
    {Px : E ⥤ E₀} {P₁ : E ⥤ E₁} {Pδ : E₀ ⥤ E₁} {ι : D ⥤ E} {ι₀ : D₀ ⥤ E₀} {ι₁ : D₁ ⥤ E₁}
    (N₀ : Lx ⋙ ι₀ ≅ ι ⋙ Px) (Nδ : Lδ ⋙ ι₁ ≅ ι₀ ⋙ Pδ) (N₁ : L₁ ⋙ ι₁ ≅ ι ⋙ P₁)
    (c : Lx ⋙ Lδ ≅ L₁) (θ : Px ⋙ Pδ ≅ P₁) {ω : D}
    (hc : ι₁.map (c.hom.app ω) ≫ N₁.hom.app ω =
      Nδ.hom.app (Lx.obj ω) ≫ Pδ.map (N₀.hom.app ω) ≫ θ.hom.app (ι.obj ω)) :
    ι₁.map (c.inv.app ω) = N₁.hom.app ω ≫ θ.inv.app (ι.obj ω) ≫
      Pδ.map (N₀.inv.app ω) ≫ Nδ.inv.app (Lx.obj ω) := by
  rw [← cancel_epi (ι₁.map (c.hom.app ω)), ← ι₁.map_comp, Iso.hom_inv_id_app, ι₁.map_id,
    reassoc_of% hc]
  simp only [Iso.hom_inv_id_app_assoc, ← Pδ.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.comp_obj, Functor.map_id, Category.id_comp]

/-- **Descent of morphisms, transported along comparison functors.** With the notation of the
module docstring, if the comparisons satisfy
`ι₁(cᵢ M) ≫ N₁ M = Nδᵢ(L₀ M) ≫ Pδᵢ(N₀ M) ≫ θᵢ(ι M)` (and the same at `N`), morphisms
`L₀ M ⟶ L₀ N` with equal transports `cᵢ⁻¹ ≫ Lδᵢ φ₀ ≫ cᵢ` come from `M ⟶ N`. -/
theorem exists_map_eq_of_descent_of_comparison {L₀ : D ⥤ D₀} {L₁ : D ⥤ D₁}
    {Lδ₀ Lδ₁ : D₀ ⥤ D₁} {P₀ : E ⥤ E₀} {P₁ : E ⥤ E₁} {Pδ₀ Pδ₁ : E₀ ⥤ E₁} {ι : D ⥤ E}
    {ι₀ : D₀ ⥤ E₀} {ι₁ : D₁ ⥤ E₁} (N₀ : L₀ ⋙ ι₀ ≅ ι ⋙ P₀) (Nδ₀ : Lδ₀ ⋙ ι₁ ≅ ι₀ ⋙ Pδ₀)
    (Nδ₁ : Lδ₁ ⋙ ι₁ ≅ ι₀ ⋙ Pδ₁) (N₁ : L₁ ⋙ ι₁ ≅ ι ⋙ P₁) (c₀ : L₀ ⋙ Lδ₀ ≅ L₁)
    (c₁ : L₀ ⋙ Lδ₁ ≅ L₁) (θ₀ : P₀ ⋙ Pδ₀ ≅ P₁) (θ₁ : P₀ ⋙ Pδ₁ ≅ P₁) {M N : D}
    (hc₀M : ι₁.map (c₀.hom.app M) ≫ N₁.hom.app M =
      Nδ₀.hom.app (L₀.obj M) ≫ Pδ₀.map (N₀.hom.app M) ≫ θ₀.hom.app (ι.obj M))
    (hc₀N : ι₁.map (c₀.hom.app N) ≫ N₁.hom.app N =
      Nδ₀.hom.app (L₀.obj N) ≫ Pδ₀.map (N₀.hom.app N) ≫ θ₀.hom.app (ι.obj N))
    (hc₁M : ι₁.map (c₁.hom.app M) ≫ N₁.hom.app M =
      Nδ₁.hom.app (L₀.obj M) ≫ Pδ₁.map (N₀.hom.app M) ≫ θ₁.hom.app (ι.obj M))
    (hc₁N : ι₁.map (c₁.hom.app N) ≫ N₁.hom.app N =
      Nδ₁.hom.app (L₀.obj N) ≫ Pδ₁.map (N₀.hom.app N) ≫ θ₁.hom.app (ι.obj N))
    (hdesc : ∀ ψ : P₀.obj (ι.obj M) ⟶ P₀.obj (ι.obj N),
      θ₀.inv.app (ι.obj M) ≫ Pδ₀.map ψ ≫ θ₀.hom.app (ι.obj N) =
        θ₁.inv.app (ι.obj M) ≫ Pδ₁.map ψ ≫ θ₁.hom.app (ι.obj N) → ∃ g, P₀.map g = ψ)
    (hfull : Function.Surjective (ι.map : (M ⟶ N) → _))
    (hfaith : Function.Injective (ι₀.map : (L₀.obj M ⟶ L₀.obj N) → _))
    (φ₀ : L₀.obj M ⟶ L₀.obj N)
    (hφ : c₀.inv.app M ≫ Lδ₀.map φ₀ ≫ c₀.hom.app N = c₁.inv.app M ≫ Lδ₁.map φ₀ ≫ c₁.hom.app N) :
    ∃ φ : M ⟶ N, L₀.map φ = φ₀ := by
  let ψ : P₀.obj (ι.obj M) ⟶ P₀.obj (ι.obj N) := N₀.inv.app M ≫ ι₀.map φ₀ ≫ N₀.hom.app N
  -- the transport of `ψ` along `δᵢ` is `ι₁` of the transport of `φ₀`, read through `N₁`
  have key : ∀ {Lδ : D₀ ⥤ D₁} {Pδ : E₀ ⥤ E₁} (Nδ : Lδ ⋙ ι₁ ≅ ι₀ ⋙ Pδ) (c : L₀ ⋙ Lδ ≅ L₁)
      (θ : P₀ ⋙ Pδ ≅ P₁)
      (_ : ι₁.map (c.hom.app M) ≫ N₁.hom.app M =
        Nδ.hom.app (L₀.obj M) ≫ Pδ.map (N₀.hom.app M) ≫ θ.hom.app (ι.obj M))
      (_ : ι₁.map (c.hom.app N) ≫ N₁.hom.app N =
        Nδ.hom.app (L₀.obj N) ≫ Pδ.map (N₀.hom.app N) ≫ θ.hom.app (ι.obj N)),
      θ.inv.app (ι.obj M) ≫ Pδ.map ψ ≫ θ.hom.app (ι.obj N) =
        N₁.inv.app M ≫ ι₁.map (c.inv.app M ≫ Lδ.map φ₀ ≫ c.hom.app N) ≫ N₁.hom.app N := by
    intro Lδ Pδ Nδ c θ hM hN
    have hM' : θ.inv.app (ι.obj M) = N₁.inv.app M ≫ ι₁.map (c.inv.app M) ≫
        Nδ.hom.app (L₀.obj M) ≫ Pδ.map (N₀.hom.app M) := by
      rw [map_inv_app_eq_of_comparison N₀ Nδ N₁ c θ hM]
      simp [← Functor.map_comp]
    have hN' : Pδ.map (N₀.hom.app N) ≫ θ.hom.app (ι.obj N) =
        Nδ.inv.app (L₀.obj N) ≫ ι₁.map (c.hom.app N) ≫ N₁.hom.app N := by
      rw [hN, Iso.inv_hom_id_app_assoc]
    have hnat := Nδ.hom.naturality φ₀
    simp only [Functor.comp_map] at hnat
    rw [hM']
    simp only [ψ, Functor.map_comp, Category.assoc]
    have hcancel : Pδ.map (N₀.hom.app M) ≫ Pδ.map (N₀.inv.app M) = 𝟙 _ := by
      rw [← Pδ.map_comp, Iso.hom_inv_id_app, Pδ.map_id]
    rw [reassoc_of% hcancel, hN', ← Category.assoc (Nδ.hom.app (L₀.obj M)),
      ← hnat]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  obtain ⟨g, hg⟩ := hdesc ψ ((key Nδ₀ c₀ θ₀ hc₀M hc₀N).trans
    ((congrArg (fun t => N₁.inv.app M ≫ ι₁.map t ≫ N₁.hom.app N) hφ).trans
      (key Nδ₁ c₁ θ₁ hc₁M hc₁N).symm))
  obtain ⟨φ, rfl⟩ := hfull g
  refine ⟨φ, hfaith ?_⟩
  have hnat := N₀.hom.naturality φ
  simp only [Functor.comp_map] at hnat
  rw [← cancel_mono (N₀.hom.app N), hnat, hg]
  simp only [ψ, Iso.hom_inv_id_app_assoc]

/-- One face of `CategoryTheory.comp_eq_of_descent_of_comparison`: the transport through `ι₁` of
`c⁻¹ ≫ Lδ ε`, for `ι₀ ε = N₀ ≫ P₀(eω) ≫ e`. -/
theorem map_comp_eq_of_comparison {Lx : D ⥤ D₀} {L₁ : D ⥤ D₁} {Lδ : D₀ ⥤ D₁} {Px : E ⥤ E₀}
    {P₁ : E ⥤ E₁} {Pδ : E₀ ⥤ E₁} {ι : D ⥤ E} {ι₀ : D₀ ⥤ E₀} {ι₁ : D₁ ⥤ E₁}
    (N₀ : Lx ⋙ ι₀ ≅ ι ⋙ Px) (Nδ : Lδ ⋙ ι₁ ≅ ι₀ ⋙ Pδ) (N₁ : L₁ ⋙ ι₁ ≅ ι ⋙ P₁)
    (c : Lx ⋙ Lδ ≅ L₁) (θ : Px ⋙ Pδ ≅ P₁) {ω : D}
    (hc : ι₁.map (c.hom.app ω) ≫ N₁.hom.app ω =
      Nδ.hom.app (Lx.obj ω) ≫ Pδ.map (N₀.hom.app ω) ≫ θ.hom.app (ι.obj ω))
    {K : E} {M : D₀} (eω : ι.obj ω ≅ K) (e : Px.obj K ≅ ι₀.obj M) (ε : Lx.obj ω ≅ M)
    (hε : ι₀.map ε.hom = N₀.hom.app ω ≫ Px.map eω.hom ≫ e.hom) :
    ι₁.map (c.inv.app ω ≫ Lδ.map ε.hom) =
      N₁.hom.app ω ≫ P₁.map eω.hom ≫ θ.inv.app K ≫ Pδ.map e.hom ≫ Nδ.inv.app M := by
  have hnat := Nδ.hom.naturality ε.hom
  simp only [Functor.comp_map] at hnat
  have hθ := θ.inv.naturality eω.hom
  simp only [Functor.comp_map] at hθ
  have hδ : ι₁.map (Lδ.map ε.hom) = Nδ.hom.app (Lx.obj ω) ≫ Pδ.map (ι₀.map ε.hom) ≫
      Nδ.inv.app M := by
    rw [← reassoc_of% hnat, Iso.hom_inv_id_app]
    simp
  rw [ι₁.map_comp, map_inv_app_eq_of_comparison N₀ Nδ N₁ c θ hc, hδ, hε]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Pδ.map_comp]
  rw [← Pδ.map_comp_assoc (N₀.inv.app ω), Iso.inv_hom_id_app, Pδ.map_id, Category.id_comp,
    reassoc_of% hθ]

/-- **A descended isomorphism is compatible with the descent datum, read through comparison
functors.** Let `ε : L_x ω ≅ M` with `ι₀ ε = N₀ ≫ P₀(eω) ≫ e` (for `eω : ιω ≅ K`,
`e : P_x K ≅ ι₀ M`), and let `α : Lδ₁ M ≅ Lδ₀ M` be carried by `ι` to `αs` (through `Nδᵢ`), with
`Pδ₁ e ≫ αs = θ₁ ≫ θ₀⁻¹ ≫ Pδ₀ e`. If `ι₁` is faithful on `L₁ ω ⟶ Lδ₀ M`, then
`(c₁⁻¹ ≫ Lδ₁ ε) ≫ α = c₀⁻¹ ≫ Lδ₀ ε`. -/
theorem comp_eq_of_descent_of_comparison {Lx : D ⥤ D₀} {L₁ : D ⥤ D₁} {Lδ₀ Lδ₁ : D₀ ⥤ D₁}
    {Px : E ⥤ E₀} {P₁ : E ⥤ E₁} {Pδ₀ Pδ₁ : E₀ ⥤ E₁} {ι : D ⥤ E} {ι₀ : D₀ ⥤ E₀}
    {ι₁ : D₁ ⥤ E₁} (N₀ : Lx ⋙ ι₀ ≅ ι ⋙ Px) (Nδ₀ : Lδ₀ ⋙ ι₁ ≅ ι₀ ⋙ Pδ₀)
    (Nδ₁ : Lδ₁ ⋙ ι₁ ≅ ι₀ ⋙ Pδ₁) (N₁ : L₁ ⋙ ι₁ ≅ ι ⋙ P₁) (c₀ : Lx ⋙ Lδ₀ ≅ L₁)
    (c₁ : Lx ⋙ Lδ₁ ≅ L₁) (θ₀ : Px ⋙ Pδ₀ ≅ P₁) (θ₁ : Px ⋙ Pδ₁ ≅ P₁) {ω : D}
    (hc₀ : ι₁.map (c₀.hom.app ω) ≫ N₁.hom.app ω =
      Nδ₀.hom.app (Lx.obj ω) ≫ Pδ₀.map (N₀.hom.app ω) ≫ θ₀.hom.app (ι.obj ω))
    (hc₁ : ι₁.map (c₁.hom.app ω) ≫ N₁.hom.app ω =
      Nδ₁.hom.app (Lx.obj ω) ≫ Pδ₁.map (N₀.hom.app ω) ≫ θ₁.hom.app (ι.obj ω))
    {K : E} {M : D₀} (eω : ι.obj ω ≅ K) (e : Px.obj K ≅ ι₀.obj M) (ε : Lx.obj ω ≅ M)
    (hε : ι₀.map ε.hom = N₀.hom.app ω ≫ Px.map eω.hom ≫ e.hom)
    (α : Lδ₁.obj M ≅ Lδ₀.obj M) (αs : Pδ₁.obj (ι₀.obj M) ≅ Pδ₀.obj (ι₀.obj M))
    (hαs : αs.hom = Nδ₁.inv.app M ≫ ι₁.map α.hom ≫ Nδ₀.hom.app M)
    (he : Pδ₁.map e.hom ≫ αs.hom = (θ₁.hom.app K ≫ θ₀.inv.app K) ≫ Pδ₀.map e.hom)
    (hfaith : Function.Injective (ι₁.map : (L₁.obj ω ⟶ Lδ₀.obj M) → _)) :
    (c₁.inv.app ω ≫ Lδ₁.map ε.hom) ≫ α.hom = c₀.inv.app ω ≫ Lδ₀.map ε.hom := by
  apply hfaith
  have hα : ι₁.map α.hom = Nδ₁.hom.app M ≫ αs.hom ≫ Nδ₀.inv.app M := by
    rw [hαs]; simp only [Iso.hom_inv_id_app_assoc, Category.assoc, Iso.hom_inv_id_app,
      Functor.comp_obj, Category.comp_id]
  rw [ι₁.map_comp, map_comp_eq_of_comparison N₀ Nδ₁ N₁ c₁ θ₁ hc₁ eω e ε hε,
    map_comp_eq_of_comparison N₀ Nδ₀ N₁ c₀ θ₀ hc₀ eω e ε hε, hα]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% he]
  simp only [Iso.inv_hom_id_app_assoc]

end CategoryTheory
