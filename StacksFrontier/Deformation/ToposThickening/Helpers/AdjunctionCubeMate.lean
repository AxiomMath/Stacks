module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ThickeningIdealMapMate

/-!
# The mate of a map of pulled-back ideals around a cube of adjunctions

Consider a commutative cube of morphisms of ringed topoi: on top `i₂ : V ⟶ W`, `j : W ⟶ X` with
`i₂ ≫ j = i₁`, on the bottom `t₂ : T ⟶ T₂`, `γ : T₂ ⟶ T₁` with `t₂ ≫ γ = t₁`, and vertical
maps `p : V ⟶ T`, `f₂ : W ⟶ T₂`, `f₁ : X ⟶ T₁`. Inverse images are left adjoint to direct images,
and the comparisons of inverse images along the faces of the cube (Stacks 03LU) are the mates of
the comparisons of direct images. This file works with the adjunctions only: given a map
`κ : N₁ ⟶ γ_*N₂` and a map `λ : t₁^*N₁ ⟶ t₂^*N₂` adjoint to `κ` followed by the unit of `t₂`, the
map `i₁^*f₁^*N₁ ≅ p^*t₁^*N₁ ⟶ p^*t₂^*N₂ ≅ i₂^*f₂^*N₂` is adjoint to the map
`f₁^*N₁ ⟶ j_*f₂^*N₂` adjoint to `κ` followed by the unit of `f₂`, followed by the unit of `i₂`
(`Deformation.ToposThickening.homEquiv_sq_comp_map_comp_sq_inv`). The only input is the
associativity of the comparisons of direct images around the cube.

This is the comparison used, for the morphism `Spec A₂' ⟶ Spec A₁'` of thickenings of a chart, in
the functoriality of the obstruction classes of `Coh_{X/B}` (second proof of Stacks 08WA).

This module is a helper and carries no `@[stacks]` attribute.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Deformation.ToposThickening

variable {𝒱 𝒲 𝒳 𝒯 𝒯₂ 𝒯₁ : Type*} [Category* 𝒱] [Category* 𝒲] [Category* 𝒳] [c𝒯 : Category* 𝒯]
  [c𝒯₂ : Category* 𝒯₂] [c𝒯₁ : Category* 𝒯₁]
  {Li₁ : 𝒳 ⥤ 𝒱} {Ri₁ : 𝒱 ⥤ 𝒳} (ai₁ : Li₁ ⊣ Ri₁)
  {Li₂ : 𝒲 ⥤ 𝒱} {Ri₂ : 𝒱 ⥤ 𝒲} (ai₂ : Li₂ ⊣ Ri₂)
  {Lj : 𝒳 ⥤ 𝒲} {Rj : 𝒲 ⥤ 𝒳} (aj : Lj ⊣ Rj)
  {Lp : 𝒯 ⥤ 𝒱} {Rp : 𝒱 ⥤ 𝒯} (ap : Lp ⊣ Rp)
  {Lf₁ : 𝒯₁ ⥤ 𝒳} {Rf₁ : 𝒳 ⥤ 𝒯₁} (af₁ : Lf₁ ⊣ Rf₁)
  {Lf₂ : 𝒯₂ ⥤ 𝒲} {Rf₂ : 𝒲 ⥤ 𝒯₂} (af₂ : Lf₂ ⊣ Rf₂)
  {Lt₁ : 𝒯₁ ⥤ 𝒯} {Rt₁ : 𝒯 ⥤ 𝒯₁} (at₁ : Lt₁ ⊣ Rt₁)
  {Lt₂ : 𝒯₂ ⥤ 𝒯} {Rt₂ : 𝒯 ⥤ 𝒯₂} (at₂ : Lt₂ ⊣ Rt₂)
  {Lγ : 𝒯₁ ⥤ 𝒯₂} {Rγ : 𝒯₂ ⥤ 𝒯₁} (aγ : Lγ ⊣ Rγ)
  {Lk₁ : 𝒯₁ ⥤ 𝒱} {Rk₁ : 𝒱 ⥤ 𝒯₁} (ak₁ : Lk₁ ⊣ Rk₁)
  {Lk₂ : 𝒯₂ ⥤ 𝒱} {Rk₂ : 𝒱 ⥤ 𝒯₂} (ak₂ : Lk₂ ⊣ Rk₂)
  {Lk : 𝒯₁ ⥤ 𝒲} {Rk : 𝒲 ⥤ 𝒯₁} (ak : Lk ⊣ Rk)
  (ci : Ri₂ ⋙ Rj ≅ Ri₁) (ct : Rt₂ ⋙ Rγ ≅ Rt₁)
  (a₁ : Ri₁ ⋙ Rf₁ ≅ Rk₁) (b₁ : Rp ⋙ Rt₁ ≅ Rk₁) (a₂ : Ri₂ ⋙ Rf₂ ≅ Rk₂) (b₂ : Rp ⋙ Rt₂ ≅ Rk₂)
  (d₁ : Rj ⋙ Rf₁ ≅ Rk) (d₂ : Rf₂ ⋙ Rγ ≅ Rk) (e₁ : Ri₂ ⋙ Rk ≅ Rk₁) (e₂ : Rk₂ ⋙ Rγ ≅ Rk₁)

/-- The comparison `f_k^* ⋙ i_k^* ≅ t_k^* ⋙ p^*` of inverse images around a side of the cube,
through the inverse image along the diagonal. -/
abbrev cubeSideIso {𝒴 𝒯' : Type*} [Category* 𝒴] [Category* 𝒯'] {Li : 𝒴 ⥤ 𝒱} {Ri : 𝒱 ⥤ 𝒴}
    (ai : Li ⊣ Ri) {Lf : 𝒯' ⥤ 𝒴} {Rf : 𝒴 ⥤ 𝒯'} (af : Lf ⊣ Rf) {Lt : 𝒯' ⥤ 𝒯} {Rt : 𝒯 ⥤ 𝒯'}
    (at' : Lt ⊣ Rt) {Lkk : 𝒯' ⥤ 𝒱} {Rkk : 𝒱 ⥤ 𝒯'} (akk : Lkk ⊣ Rkk)
    (a : Ri ⋙ Rf ≅ Rkk) (b : Rp ⋙ Rt ≅ Rkk) : Lf ⋙ Li ≅ Lt ⋙ Lp :=
  Adjunction.leftAdjointCompIso af ai akk a ≪≫ (Adjunction.leftAdjointCompIso at' ap akk b).symm

include ap in
/-- **The left adjoint cube coherence.** If the comparisons of right adjoints are associative
around the three faces through `j ≫ f₁ = f₂ ≫ γ`, `i₂ ≫ (j ≫ f₁) = (i₂ ≫ f₂) ≫ γ` and
`p ≫ (t₂ ≫ γ)`, then the comparisons of left adjoints around the cube agree. -/
theorem leftAdjointCompIso_cube_app
    (hA : isoWhiskerLeft Ri₂ d₁ ≪≫ e₁ = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight ci Rf₁ ≪≫ a₁)
    (hB : isoWhiskerLeft Ri₂ d₂ ≪≫ e₁ = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight a₂ Rγ ≪≫ e₂)
    (hC : isoWhiskerLeft Rp ct ≪≫ b₁ = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight b₂ Rγ ≪≫ e₂) (N : 𝒯₁) :
    (Adjunction.leftAdjointCompIso aj ai₂ ai₁ ci).hom.app (Lf₁.obj N) ≫
        (cubeSideIso ap ai₁ af₁ at₁ ak₁ a₁ b₁).hom.app N ≫
        Lp.map ((Adjunction.leftAdjointCompIso aγ at₂ at₁ ct).inv.app N) ≫
        (cubeSideIso ap ai₂ af₂ at₂ ak₂ a₂ b₂).inv.app (Lγ.obj N) =
      Li₂.map ((Adjunction.leftAdjointCompIso af₁ aj ak d₁).hom.app N ≫
        (Adjunction.leftAdjointCompIso aγ af₂ ak d₂).inv.app N) := by
  have hAL := congrArg (fun e => e.hom.app N)
    (Adjunction.leftAdjointCompIso_assoc af₁ aj ai₂ ak ai₁ ak₁ d₁ ci a₁ e₁ hA)
  have hBL := congrArg (fun e => e.hom.app N)
    (Adjunction.leftAdjointCompIso_assoc aγ af₂ ai₂ ak ak₂ ak₁ d₂ a₂ e₂ e₁ hB)
  have hCL := congrArg (fun e => e.hom.app N)
    (Adjunction.leftAdjointCompIso_assoc aγ at₂ ap at₁ ak₂ ak₁ ct b₂ e₂ b₁ hC)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp] at hAL hBL hCL
  simp only [cubeSideIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc, Functor.map_comp]
  rw [reassoc_of% hAL]
  congr 1
  rw [← cancel_mono ((Adjunction.leftAdjointCompIso af₂ ai₂ ak₂ a₂).hom.app (Lγ.obj N))]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← cancel_mono ((Adjunction.leftAdjointCompIso aγ ak₂ ak₁ e₂).hom.app N)]
  simp only [Category.assoc]
  rw [hBL, hCL, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

/-- The map `f₁^*N₁ ⟶ j_*f₂^*N₂` on the top of the cube attached to `κ : N₁ ⟶ γ_*N₂`: the
transpose under `f₁^* ⊣ f₁_*` of `κ` followed by `γ_*` of the unit of `f₂` and the comparison
`γ_*f₂_* ≅ k_* ≅ f₁_*j_*`. -/
def cubeTopTranspose {N₁ : 𝒯₁} {N₂ : 𝒯₂} (κ : N₁ ⟶ Rγ.obj N₂) :
    Lf₁.obj N₁ ⟶ Rj.obj (Lf₂.obj N₂) :=
  (af₁.homEquiv _ _).symm (κ ≫ Rγ.map (af₂.unit.app N₂) ≫ (d₂ ≪≫ d₁.symm).hom.app _)

/-- The map `f₁^*N₁ ⟶ i₁_*i₂^*f₂^*N₂` of the top face of the cube attached to `κ : N₁ ⟶ γ_*N₂`:
the map `f₁^*N₁ ⟶ j_*f₂^*N₂` adjoint to `κ` followed by the unit of `f₂`, then `j_*` of the unit of
`i₂` and `j_*i₂_* ≅ i₁_*`. -/
def cubeTopMap {N₁ : 𝒯₁} {N₂ : 𝒯₂} (κ : N₁ ⟶ Rγ.obj N₂) :
    Lf₁.obj N₁ ⟶ Ri₁.obj (Li₂.obj (Lf₂.obj N₂)) :=
  cubeTopTranspose af₁ af₂ d₁ d₂ κ ≫
    Rj.map (ai₂.unit.app (Lf₂.obj N₂)) ≫ ci.hom.app (Li₂.obj (Lf₂.obj N₂))

/-- The map `i₁^*f₁^*N₁ ≅ p^*t₁^*N₁ ⟶ p^*t₂^*N₂ ≅ i₂^*f₂^*N₂` of the sides of the cube attached to
`λ : t₁^*N₁ ⟶ t₂^*N₂`. -/
def cubeSideMap {N₁ : 𝒯₁} {N₂ : 𝒯₂} (lam : Lt₁.obj N₁ ⟶ Lt₂.obj N₂) :
    Li₁.obj (Lf₁.obj N₁) ⟶ Li₂.obj (Lf₂.obj N₂) :=
  (cubeSideIso ap ai₁ af₁ at₁ ak₁ a₁ b₁).hom.app N₁ ≫ Lp.map lam ≫
    (cubeSideIso ap ai₂ af₂ at₂ ak₂ a₂ b₂).inv.app N₂

include ap aγ aj ak in
/-- **The mate of a map of pulled-back ideals around the cube.** For `κ : N₁ ⟶ γ_*N₂` and
`λ : t₁^*N₁ ⟶ t₂^*N₂` adjoint to `κ` followed by the unit of `t₂`, the map
`i₁^*f₁^*N₁ ≅ p^*t₁^*N₁ ⟶ p^*t₂^*N₂ ≅ i₂^*f₂^*N₂` is adjoint under `i₁^* ⊣ i₁_*` to the map
`f₁^*N₁ ⟶ j_*f₂^*N₂` adjoint to `κ` followed by the unit of `f₂`, followed by `j_*` of the unit
of `i₂` and `j_*i₂_* ≅ i₁_*`. -/
theorem homEquiv_sq_comp_map_comp_sq_inv
    (hA : isoWhiskerLeft Ri₂ d₁ ≪≫ e₁ = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight ci Rf₁ ≪≫ a₁)
    (hB : isoWhiskerLeft Ri₂ d₂ ≪≫ e₁ = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight a₂ Rγ ≪≫ e₂)
    (hC : isoWhiskerLeft Rp ct ≪≫ b₁ = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight b₂ Rγ ≪≫ e₂)
    {N₁ : 𝒯₁} {N₂ : 𝒯₂} (κ : N₁ ⟶ Rγ.obj N₂) (lam : Lt₁.obj N₁ ⟶ Lt₂.obj N₂)
    (hlam : at₁.homEquiv _ _ lam = κ ≫ Rγ.map (at₂.unit.app N₂) ≫ ct.hom.app (Lt₂.obj N₂)) :
    ai₁.homEquiv _ _ (cubeSideMap (ap := ap) (ai₁ := ai₁) (ai₂ := ai₂) (af₁ := af₁) (af₂ := af₂)
      (at₁ := at₁) (at₂ := at₂) (ak₁ := ak₁) (ak₂ := ak₂) (a₁ := a₁) (b₁ := b₁) (a₂ := a₂)
      (b₂ := b₂) lam) =
      cubeTopMap (ai₂ := ai₂) (af₁ := af₁) (af₂ := af₂) (ci := ci)
        (d₁ := d₁) (d₂ := d₂) κ := by
  -- `λ` is `t₁^* ≅ γ^* ⋙ t₂^*` followed by `t₂^*` of the adjoint `κ♭ : γ^*N₁ ⟶ N₂` of `κ`
  have hlam' : lam = (Adjunction.leftAdjointCompIso aγ at₂ at₁ ct).inv.app N₁ ≫
      Lt₂.map ((aγ.homEquiv _ _).symm κ) := by
    apply (at₁.homEquiv _ _).injective
    rw [hlam, homEquiv_eq_homEquiv_comp_map_unit_comp_of_eq aγ at₂ at₁ ct _ _ rfl,
      Equiv.apply_symm_apply]
  -- the map `j^*f₁^*N₁ ⟶ f₂^*N₂` adjoint to `ν'`
  have hX : aj.homEquiv _ _ ((Adjunction.leftAdjointCompIso af₁ aj ak d₁).hom.app N₁ ≫
      (Adjunction.leftAdjointCompIso aγ af₂ ak d₂).inv.app N₁ ≫
        Lf₂.map ((aγ.homEquiv _ _).symm κ)) =
      (af₁.homEquiv _ _).symm (κ ≫ Rγ.map (af₂.unit.app N₂) ≫ (d₂ ≪≫ d₁.symm).hom.app _) := by
    rw [Equiv.eq_symm_apply]
    have h1 := Adjunction.homEquiv_eq_leftAdjointCompIso af₁ aj ak d₁
      ((Adjunction.leftAdjointCompIso aγ af₂ ak d₂).inv.app N₁ ≫
        Lf₂.map ((aγ.homEquiv _ _).symm κ))
    have h2 := homEquiv_eq_homEquiv_comp_map_unit_comp_of_eq aγ af₂ ak d₂
      ((aγ.homEquiv _ _).symm κ) _ rfl
    rw [Equiv.apply_symm_apply, h1] at h2
    rw [← cancel_mono (d₁.hom.app (Lf₂.obj N₂))]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id]
    exact h2
  unfold cubeSideMap cubeTopMap cubeTopTranspose
  rw [← hX]
  refine homEquiv_eq_homEquiv_comp_map_unit_comp_of_eq aj ai₂ ai₁ ci _ _ ?_
  rw [← cancel_epi ((Adjunction.leftAdjointCompIso aj ai₂ ai₁ ci).hom.app (Lf₁.obj N₁)),
    Iso.hom_inv_id_app_assoc, hlam', Functor.map_comp, Category.assoc]
  have hn := (cubeSideIso ap ai₂ af₂ at₂ ak₂ a₂ b₂).inv.naturality ((aγ.homEquiv _ _).symm κ)
  simp only [Functor.comp_map] at hn
  rw [hn, reassoc_of% (leftAdjointCompIso_cube_app ai₁ ai₂ aj ap af₁ af₂ at₁ at₂ aγ ak₁ ak₂ ak ci ct
    a₁ b₁ a₂ b₂ d₁ d₂ e₁ e₂ hA hB hC N₁)]
  simp only [Functor.map_comp, Category.assoc]

include ap aγ aj ak in
/-- **The cube mate followed by a map out of `i₂^*f₂^*N₂`.**
`Deformation.ToposThickening.homEquiv_sq_comp_map_comp_sq_inv` followed by a map
`y : i₂^*f₂^*N₂ ⟶ Q`: the transpose is `cubeTopTranspose` followed by `j_*` of the transpose of
`y` and `j_*i₂_* ≅ i₁_*`. -/
theorem homEquiv_cubeSideMap_comp
    (hA : isoWhiskerLeft Ri₂ d₁ ≪≫ e₁ = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight ci Rf₁ ≪≫ a₁)
    (hB : isoWhiskerLeft Ri₂ d₂ ≪≫ e₁ = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight a₂ Rγ ≪≫ e₂)
    (hC : isoWhiskerLeft Rp ct ≪≫ b₁ = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight b₂ Rγ ≪≫ e₂)
    {N₁ : 𝒯₁} {N₂ : 𝒯₂} (κ : N₁ ⟶ Rγ.obj N₂) (lam : Lt₁.obj N₁ ⟶ Lt₂.obj N₂)
    (hlam : at₁.homEquiv _ _ lam = κ ≫ Rγ.map (at₂.unit.app N₂) ≫ ct.hom.app (Lt₂.obj N₂))
    {Q : 𝒱} (y : Li₂.obj (Lf₂.obj N₂) ⟶ Q) :
    ai₁.homEquiv _ _ (cubeSideMap (ap := ap) (ai₁ := ai₁) (ai₂ := ai₂) (af₁ := af₁) (af₂ := af₂)
      (at₁ := at₁) (at₂ := at₂) (ak₁ := ak₁) (ak₂ := ak₂) (a₁ := a₁) (b₁ := b₁) (a₂ := a₂)
      (b₂ := b₂) lam ≫ y) =
      cubeTopTranspose af₁ af₂ d₁ d₂ κ ≫ Rj.map (ai₂.homEquiv _ _ y) ≫ ci.hom.app Q := by
  rw [Adjunction.homEquiv_naturality_right, homEquiv_sq_comp_map_comp_sq_inv ai₁ ai₂ aj ap af₁ af₂
    at₁ at₂ aγ ak₁ ak₂ ak ci ct a₁ b₁ a₂ b₂ d₁ d₂ e₁ e₂ hA hB hC κ lam hlam]
  unfold cubeTopMap
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  simp only [Category.assoc]
  congr 2
  exact (ci.hom.naturality y).symm

include ap aγ aj ak in
/-- **The reductions of the pulled-back ideals around the cube.** Let `Pₓ` be functors equal to the
left adjoints `Lₓ`, `σₖ : P_{fₖ} ⋙ P_{iₖ} ≅ P_{tₖ} ⋙ P_p` the comparisons of left adjoints around
the sides read through these equalities, `λ : P_{t₁}N₁ ⟶ P_{t₂}N₂` adjoint (read through the
equalities) to `κ : N₁ ⟶ γ_*N₂` followed by the unit of `t₂`, `ρₖ : Fₖ ≅ P_{fₖ}Nₖ` (up to
`Fₖ = F'ₖ`), `Bₖ : Qₖ ≅ P_{iₖ}Fₖ`, and `Rₖ : Qₖ ≅ P_pP_{tₖ}Nₖ` the composite of `Bₖ`, `P_{iₖ}ρₖ`
and `σₖ`. Then the transpose of `Bₖ⁻¹` carries the map `F₁ ⟶ j_*F₂` of `κ` to `i₁_*` of
`R₁ ≫ P_pλ ≫ R₂⁻¹`, through `j_*i₂_* ≅ i₁_*`. -/
theorem homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq
    (hA : isoWhiskerLeft Ri₂ d₁ ≪≫ e₁ = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight ci Rf₁ ≪≫ a₁)
    (hB : isoWhiskerLeft Ri₂ d₂ ≪≫ e₁ = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight a₂ Rγ ≪≫ e₂)
    (hC : isoWhiskerLeft Rp ct ≪≫ b₁ = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight b₂ Rγ ≪≫ e₂)
    {Pi₁ : 𝒳 ⥤ 𝒱} {Pi₂ : 𝒲 ⥤ 𝒱} {Pp : 𝒯 ⥤ 𝒱} {Pf₁ : 𝒯₁ ⥤ 𝒳} {Pf₂ : 𝒯₂ ⥤ 𝒲}
    {Pt₁ : 𝒯₁ ⥤ 𝒯} {Pt₂ : 𝒯₂ ⥤ 𝒯} (hi₁ : Li₁ = Pi₁) (hi₂ : Li₂ = Pi₂) (hp : Lp = Pp)
    (hf₁ : Lf₁ = Pf₁) (hf₂ : Lf₂ = Pf₂) (ht₁ : Lt₁ = Pt₁) (ht₂ : Lt₂ = Pt₂)
    (N₁ : 𝒯₁) (N₂ : 𝒯₂) (κ : N₁ ⟶ Rγ.obj N₂) (lam : Pt₁.obj N₁ ⟶ Pt₂.obj N₂)
    (s₁ : Lt₁.obj N₁ ⟶ Pt₁.obj N₁) (hs₁ : s₁ = eqToHom (congrArg (fun F => F.obj N₁) ht₁))
    (s₂ : Pt₂.obj N₂ ⟶ Lt₂.obj N₂) (hs₂ : s₂ = eqToHom (congrArg (fun F => F.obj N₂) ht₂).symm)
    (q : Lt₁.obj N₁ ⟶ Lt₂.obj N₂) (hq : q = s₁ ≫ lam ≫ s₂)
    (hlam : at₁.homEquiv _ _ q = κ ≫ Rγ.map (at₂.unit.app N₂) ≫ ct.hom.app (Lt₂.obj N₂))
    (σ₁ : Pf₁ ⋙ Pi₁ ≅ Pt₁ ⋙ Pp) (σ₂ : Pf₂ ⋙ Pi₂ ≅ Pt₂ ⋙ Pp)
    (hσ₁ : σ₁.hom.app N₁ =
      eqToHom (congrArg (fun F => F.obj N₁) (congrArg₂ (· ⋙ ·) hf₁ hi₁)).symm ≫
        (cubeSideIso ap ai₁ af₁ at₁ ak₁ a₁ b₁).hom.app N₁ ≫
        eqToHom (congrArg (fun F => F.obj N₁) (congrArg₂ (· ⋙ ·) ht₁ hp)))
    (hσ₂ : σ₂.hom.app N₂ =
      eqToHom (congrArg (fun F => F.obj N₂) (congrArg₂ (· ⋙ ·) hf₂ hi₂)).symm ≫
        (cubeSideIso ap ai₂ af₂ at₂ ak₂ a₂ b₂).hom.app N₂ ≫
        eqToHom (congrArg (fun F => F.obj N₂) (congrArg₂ (· ⋙ ·) ht₂ hp)))
    {F₁ F'₁ : 𝒳} (Z₁ : F₁ = F'₁) (ρ₁ : F'₁ ≅ Pf₁.obj N₁)
    {F₂ F'₂ : 𝒲} (Z₂ : F₂ = F'₂) (ρ₂ : F'₂ ≅ Pf₂.obj N₂)
    {Q₁ Q₂ : 𝒱} (B₁ : Q₁ ≅ Pi₁.obj F₁) (B₂ : Q₂ ≅ Pi₂.obj F₂)
    (R₁ : Q₁ ≅ Pp.obj (Pt₁.obj N₁)) (R₂ : Q₂ ≅ Pp.obj (Pt₂.obj N₂))
    (hR₁ : R₁.hom = B₁.hom ≫ Pi₁.map (eqToHom Z₁) ≫ Pi₁.map ρ₁.hom ≫ σ₁.hom.app N₁)
    (hR₂ : R₂.hom = B₂.hom ≫ Pi₂.map (eqToHom Z₂) ≫ Pi₂.map ρ₂.hom ≫ σ₂.hom.app N₂) :
    ai₁.homEquiv _ _ (eqToHom (congrArg (fun F => F.obj F₁) hi₁) ≫ B₁.inv) ≫
        Ri₁.map (R₁.hom ≫ Pp.map lam ≫ R₂.inv) =
      (eqToHom Z₁ ≫ ρ₁.hom ≫ eqToHom (congrArg (fun F => F.obj N₁) hf₁).symm ≫
          cubeTopTranspose af₁ af₂ d₁ d₂ κ ≫
          Rj.map (eqToHom (congrArg (fun F => F.obj N₂) hf₂) ≫ ρ₂.inv ≫ eqToHom Z₂.symm)) ≫
        Rj.map (ai₂.homEquiv _ _ (eqToHom (congrArg (fun F => F.obj F₂) hi₂) ≫ B₂.inv)) ≫
        ci.hom.app Q₂ := by
  subst hq hs₁ hs₂
  subst hi₁ hi₂ hp hf₁ hf₂ ht₁ ht₂ Z₁ Z₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hlam hσ₁ hσ₂ hR₁ hR₂ ⊢
  have hσ₂' : σ₂.inv.app N₂ = (cubeSideIso ap ai₂ af₂ at₂ ak₂ a₂ b₂).inv.app N₂ :=
    congrArg Iso.inv (Iso.ext (show (σ₂.app N₂).hom =
      ((cubeSideIso ap ai₂ af₂ at₂ ak₂ a₂ b₂).app N₂).hom from hσ₂))
  have hR₂' : R₂.inv = σ₂.inv.app N₂ ≫ Li₂.map ρ₂.inv ≫ B₂.inv := by
    rw [← cancel_epi R₂.hom, Iso.hom_inv_id, hR₂]
    simp [← Functor.map_comp_assoc]
  have key := homEquiv_cubeSideMap_comp ai₁ ai₂ aj ap af₁ af₂ at₁ at₂ aγ ak₁ ak₂ ak ci ct
    a₁ b₁ a₂ b₂ d₁ d₂ e₁ e₂ hA hB hC κ lam hlam (Li₂.map ρ₂.inv ≫ B₂.inv)
  unfold cubeSideMap at key
  rw [← Adjunction.homEquiv_naturality_right, hR₁, hR₂', hσ₁, hσ₂']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [CategoryTheory.Functor.map_id, Category.id_comp,
    Adjunction.homEquiv_naturality_left ai₁ ρ₁.hom]
  simp only [Category.assoc] at key
  rw [key, Adjunction.homEquiv_naturality_left ai₂ ρ₂.inv, Functor.map_comp]
  simp only [Category.assoc]

end Deformation.ToposThickening
