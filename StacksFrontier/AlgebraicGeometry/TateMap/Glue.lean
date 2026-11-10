module

public import StacksFrontier.AlgebraicGeometry.Modules.BasisSectionExtension
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Basic

/-!
# Isomorphisms of sheaves of modules from linear isomorphisms on a basis

A family of linear isomorphisms of the sections of two `𝒪_Y`-modules over the members of a basis
of `Y`, compatible with restriction between nested members, is the family of sections of exactly
one isomorphism of sheaves of modules.

## Main results

* `AlgebraicGeometry.TateMap.exists_iso_of_basis`: the isomorphism exists.
* `AlgebraicGeometry.TateMap.hom_ext_of_basis`: two morphisms agreeing on the sections over the
  members of a basis are equal.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v

namespace AlgebraicGeometry.TateMap

variable {Y : Scheme.{u}} {M N : Y.Modules} {κ : Type v} (W : κ → Y.Opens)

/-- Two morphisms of sheaves of modules agreeing on the sections over the members of a basis are
equal. -/
theorem hom_ext_of_basis (hb : ∀ V : Y.Opens, ∀ x ∈ V, ∃ k, x ∈ W k ∧ W k ≤ V)
    (φ ψ : M ⟶ N) (h : ∀ k (s : Γ(M, W k)), φ.app (W k) s = ψ.app (W k) s) : φ = ψ := by
  refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
  ext s
  exact Stacks.Modules.sectionsMap_eq_of_basis (T := ⊤) (W := W) M N
    (fun V _ x hx ↦ hb V x hx) (fun V _ s ↦ φ.app V s) (fun V _ s ↦ ψ.app V s)
    (fun V V' _ _ h s ↦ congr($(φ.mapPresheaf.naturality (homOfLE h).op) s))
    (fun V V' _ _ h s ↦ congr($(ψ.mapPresheaf.naturality (homOfLE h).op) s))
    (fun k _ s ↦ h k s) le_top s

/-- **Glueing an isomorphism of sheaves of modules on a basis.** -/
theorem exists_iso_of_basis (hb : ∀ V : Y.Opens, ∀ x ∈ V, ∃ k, x ∈ W k ∧ W k ≤ V)
    (e : ∀ k, Γ(M, W k) ≃ₗ[Γ(Y, W k)] Γ(N, W k))
    (he : ∀ (k l : κ) (h : W l ≤ W k) (s : Γ(M, W k)),
      e l (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (e k s)) :
    ∃ c : M ≅ N, ∀ k (s : Γ(M, W k)), c.hom.app (W k) s = e k s := by
  obtain ⟨E, hnat, hchart⟩ := Stacks.Modules.exists_sectionEquiv_of_basis M N ⊤ W
    (fun V _ x hx ↦ hb V x hx) e he
  have hU : (⨆ _ : PUnit.{u + 1}, (⊤ : Y.Opens)) = ⊤ := iSup_const
  obtain ⟨φ, hφ, -⟩ := Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app
    (M := M) (N := N) hU
    (fun _ V hV ↦ AddCommGrpCat.ofHom (E V hV).toLinearMap.toAddMonoidHom)
    (fun _ V hV r s ↦ (E V hV).map_smul r s)
    (fun _ V V' hV hWV s ↦ hnat V V' hV (hWV.trans hV) hWV s)
    (fun _ _ _ _ _ ↦ rfl)
  obtain ⟨ψ, hψ, -⟩ := Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app
    (M := N) (N := M) hU
    (fun _ V hV ↦ AddCommGrpCat.ofHom (E V hV).symm.toLinearMap.toAddMonoidHom)
    (fun _ V hV r s ↦ (E V hV).symm.map_smul r s)
    (fun _ V V' hV hWV s ↦ by
      apply (E V' (hWV.trans hV)).injective
      change E V' _ ((E V' _).symm _) = E V' _ (M.presheaf.map (homOfLE hWV).op ((E V hV).symm s))
      rw [hnat V V' hV (hWV.trans hV) hWV, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply])
    (fun _ _ _ _ _ ↦ rfl)
  refine ⟨{ hom := φ, inv := ψ, hom_inv_id := ?_, inv_hom_id := ?_ },
    fun k s ↦ (congr($(hφ PUnit.unit (W k) le_top) s)).trans (hchart k le_top s)⟩ <;>
  · refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
    ext s
    simp only [Scheme.Modules.Hom.comp_app, hφ PUnit.unit V le_top, hψ PUnit.unit V le_top,
      Scheme.Modules.Hom.id_app]
    first
      | exact (E V le_top).symm_apply_apply s
      | exact (E V le_top).apply_symm_apply s

end AlgebraicGeometry.TateMap

namespace AlgebraicGeometry

/-- The linear isomorphism of sections over an open induced by an isomorphism of sheaves of
modules. -/
noncomputable def sectionsLinearEquiv_of_iso {Y : Scheme.{u}} {M N : Y.Modules}
    (e : M ≅ N) (U : Y.Opens) : Γ(M, U) ≃ₗ[Γ(Y, U)] Γ(N, U) := by
  have h₁ : e.hom.val.app (Opposite.op U) ≫ e.inv.val.app (Opposite.op U) = 𝟙 _ :=
    congrArg (fun g : M ⟶ M => g.val.app (Opposite.op U)) e.hom_inv_id
  have h₂ : e.inv.val.app (Opposite.op U) ≫ e.hom.val.app (Opposite.op U) = 𝟙 _ :=
    congrArg (fun g : N ⟶ N => g.val.app (Opposite.op U)) e.inv_hom_id
  let eU : M.val.obj (Opposite.op U) ≅ N.val.obj (Opposite.op U) :=
    { hom := e.hom.val.app (Opposite.op U), inv := e.inv.val.app (Opposite.op U),
      hom_inv_id := h₁, inv_hom_id := h₂ }
  exact eU.toLinearEquiv

/-- `sectionsLinearEquiv_of_iso e U` acts on sections as the component of `e.hom` over `U`. -/
@[simp]
theorem sectionsLinearEquiv_of_iso_apply {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    (U : Y.Opens) (s : Γ(M, U)) : sectionsLinearEquiv_of_iso e U s = e.hom.app U s :=
  rfl

/-- The inverse of `sectionsLinearEquiv_of_iso e U` acts on sections as the component of `e.inv`
over `U`. -/
@[simp]
theorem sectionsLinearEquiv_of_iso_symm_apply {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    (U : Y.Opens) (s : Γ(N, U)) : (sectionsLinearEquiv_of_iso e U).symm s = e.inv.app U s :=
  rfl

end AlgebraicGeometry
