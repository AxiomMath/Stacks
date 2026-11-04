module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Pasting of squares of functors built in three layers

Let `ι₁ : C₁ ⥤ D₁`, `ι₂ : C₂ ⥤ D₂`, `ι₃ : C₃ ⥤ D₃` be functors. A square
`β : e ⋙ ι' ≅ ι ⋙ p` is often built in three layers, from isomorphisms `a : m ≅ e`,
`b : ι ⋙ q ≅ m ⋙ ι'` and `c : p ≅ q`. If each layer is compatible with given composition
isomorphisms (`u` for the `e`, `w_m` for the `m`, `w_q` for the `q`, `v` for the `p`), then the
squares built from them paste along `u` and `v`.

## Main results

* `Stacks.CategoryTheory.squareIso_pasting_of_layers`, and
  `Stacks.CategoryTheory.squareIso_pasting_of_layers'` with the first two layers reversed.
* `Stacks.CategoryTheory.squareIso_pasting_of_layers''`: the same with each middle layer a
  composite of three isomorphisms.
* `Stacks.CategoryTheory.squareIso_pasting_of_layers_of_eq`: the same for squares given together
  with their decomposition into layers.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃]
  {ι₁ : C₁ ⥤ D₁} {ι₂ : C₂ ⥤ D₂} {ι₃ : C₃ ⥤ D₃}
  {e₁ m₁ : C₁ ⥤ C₂} {e₂ m₂ : C₂ ⥤ C₃} {e₃ m₃ : C₁ ⥤ C₃}
  {p₁ q₁ : D₁ ⥤ D₂} {p₂ q₂ : D₂ ⥤ D₃} {p₃ q₃ : D₁ ⥤ D₃}

/-- **Squares built in three layers paste when each layer does.** With
`β_i := ι'(a_i⁻¹) ≫ b_i⁻¹ ≫ ι(c_i⁻¹) : e_i ⋙ ι' ≅ ι ⋙ p_i`, the compatibilities of `a` with
`w_m` and `u`, of `b` with `w_m` and `w_q`, and of `c` with `v` and `w_q` give the pasting
`ι₃(u) ≫ β₃ = β₂ ≫ p₂(β₁) ≫ v`. -/
theorem squareIso_pasting_of_layers
    (a₁ : m₁ ≅ e₁) (a₂ : m₂ ≅ e₂) (a₃ : m₃ ≅ e₃)
    (b₁ : ι₁ ⋙ q₁ ≅ m₁ ⋙ ι₂) (b₂ : ι₂ ⋙ q₂ ≅ m₂ ⋙ ι₃) (b₃ : ι₁ ⋙ q₃ ≅ m₃ ⋙ ι₃)
    (c₁ : p₁ ≅ q₁) (c₂ : p₂ ≅ q₂) (c₃ : p₃ ≅ q₃)
    (u : e₁ ⋙ e₂ ≅ e₃) (wm : m₁ ⋙ m₂ ≅ m₃) (wq : q₁ ⋙ q₂ ≅ q₃) (v : p₁ ⋙ p₂ ≅ p₃)
    (ha : wm.hom ≫ a₃.hom =
      Functor.whiskerLeft m₁ a₂.hom ≫ Functor.whiskerRight a₁.hom e₂ ≫ u.hom)
    (hb : ∀ N, wq.hom.app (ι₁.obj N) ≫ b₃.hom.app N =
      q₂.map (b₁.hom.app N) ≫ b₂.hom.app (m₁.obj N) ≫ ι₃.map (wm.hom.app N))
    (hc : v.hom ≫ c₃.hom = Functor.whiskerRight c₁.hom p₂ ≫ Functor.whiskerLeft q₁ c₂.hom ≫ wq.hom)
    (M : C₁) :
    ι₃.map (u.hom.app M) ≫
        (Functor.isoWhiskerRight a₃.symm ι₃ ≪≫ b₃.symm ≪≫ Functor.isoWhiskerLeft ι₁ c₃.symm).hom.app
          M =
      (Functor.isoWhiskerRight a₂.symm ι₃ ≪≫ b₂.symm ≪≫ Functor.isoWhiskerLeft ι₂ c₂.symm).hom.app
          (e₁.obj M) ≫
        p₂.map ((Functor.isoWhiskerRight a₁.symm ι₂ ≪≫ b₁.symm ≪≫
          Functor.isoWhiskerLeft ι₁ c₁.symm).hom.app M) ≫ v.hom.app (ι₁.obj M) := by
  set β₁ := Functor.isoWhiskerRight a₁.symm ι₂ ≪≫ b₁.symm ≪≫ Functor.isoWhiskerLeft ι₁ c₁.symm
  set β₂ := Functor.isoWhiskerRight a₂.symm ι₃ ≪≫ b₂.symm ≪≫ Functor.isoWhiskerLeft ι₂ c₂.symm
  set β₃ := Functor.isoWhiskerRight a₃.symm ι₃ ≪≫ b₃.symm ≪≫ Functor.isoWhiskerLeft ι₁ c₃.symm
  have ha' : wm.hom.app M ≫ a₃.hom.app M =
      a₂.hom.app (m₁.obj M) ≫ e₂.map (a₁.hom.app M) ≫ u.hom.app M := by
    simpa using NatTrans.congr_app ha M
  have hc' : v.hom.app (ι₁.obj M) ≫ c₃.hom.app (ι₁.obj M) =
      p₂.map (c₁.hom.app (ι₁.obj M)) ≫ c₂.hom.app (q₁.obj (ι₁.obj M)) ≫
        wq.hom.app (ι₁.obj M) := by
    simpa using NatTrans.congr_app hc (ι₁.obj M)
  have n₁ : p₂.map (b₁.hom.app M ≫ ι₂.map (a₁.hom.app M)) ≫ c₂.hom.app (ι₂.obj (e₁.obj M)) =
      c₂.hom.app (q₁.obj (ι₁.obj M)) ≫ q₂.map (b₁.hom.app M ≫ ι₂.map (a₁.hom.app M)) :=
    c₂.hom.naturality _
  have n₂ : q₂.map (ι₂.map (a₁.hom.app M)) ≫ b₂.hom.app (e₁.obj M) =
      b₂.hom.app (m₁.obj M) ≫ ι₃.map (m₂.map (a₁.hom.app M)) :=
    b₂.hom.naturality (a₁.hom.app M)
  have n₃ : m₂.map (a₁.hom.app M) ≫ a₂.hom.app (e₁.obj M) =
      a₂.hom.app (m₁.obj M) ≫ e₂.map (a₁.hom.app M) :=
    a₂.hom.naturality (a₁.hom.app M)
  have K : v.hom.app (ι₁.obj M) ≫ β₃.inv.app M =
      p₂.map (β₁.inv.app M) ≫ β₂.inv.app (e₁.obj M) ≫ ι₃.map (u.hom.app M) := by
    simp only [β₁, β₂, β₃, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.map_comp, Category.assoc, Functor.comp_obj]
    rw [reassoc_of% hc', reassoc_of% (hb M), ← ι₃.map_comp, ha', ← reassoc_of% n₃, ι₃.map_comp,
      ι₃.map_comp, ← reassoc_of% n₂, ← q₂.map_comp_assoc, ← reassoc_of% n₁, p₂.map_comp,
      Category.assoc]
  calc ι₃.map (u.hom.app M) ≫ β₃.hom.app M
      = β₂.hom.app (e₁.obj M) ≫ p₂.map (β₁.hom.app M) ≫ p₂.map (β₁.inv.app M) ≫
          β₂.inv.app (e₁.obj M) ≫ ι₃.map (u.hom.app M) ≫ β₃.hom.app M := by
        have e1 : p₂.map (β₁.hom.app M) ≫ p₂.map (β₁.inv.app M) = 𝟙 _ :=
          (p₂.mapIso (β₁.app M)).hom_inv_id
        rw [reassoc_of% e1]
        exact (Iso.hom_inv_id_app_assoc β₂ _ _).symm
    _ = β₂.hom.app (e₁.obj M) ≫ p₂.map (β₁.hom.app M) ≫ v.hom.app (ι₁.obj M) := by
        rw [← reassoc_of% K, Iso.inv_hom_id_app]
        exact congrArg _ (congrArg _ (Category.comp_id _))

/-- **Squares built in three layers paste when each layer does**, with the first two layers in
the forward direction: `β_i := ι'(a_i) ≫ b_i ≫ ι(c_i⁻¹) : e_i ⋙ ι' ≅ ι ⋙ p_i` for
`a_i : e_i ≅ m_i`, `b_i : m_i ⋙ ι' ≅ ι ⋙ q_i` and `c_i : p_i ≅ q_i`. -/
theorem squareIso_pasting_of_layers'
    (a₁ : e₁ ≅ m₁) (a₂ : e₂ ≅ m₂) (a₃ : e₃ ≅ m₃)
    (b₁ : m₁ ⋙ ι₂ ≅ ι₁ ⋙ q₁) (b₂ : m₂ ⋙ ι₃ ≅ ι₂ ⋙ q₂) (b₃ : m₃ ⋙ ι₃ ≅ ι₁ ⋙ q₃)
    (c₁ : p₁ ≅ q₁) (c₂ : p₂ ≅ q₂) (c₃ : p₃ ≅ q₃)
    (u : e₁ ⋙ e₂ ≅ e₃) (wm : m₁ ⋙ m₂ ≅ m₃) (wq : q₁ ⋙ q₂ ≅ q₃) (v : p₁ ⋙ p₂ ≅ p₃)
    (ha : u.hom ≫ a₃.hom =
      Functor.whiskerRight a₁.hom e₂ ≫ Functor.whiskerLeft m₁ a₂.hom ≫ wm.hom)
    (hb : Functor.whiskerRight wm.hom ι₃ ≫ b₃.hom =
      Functor.whiskerLeft m₁ b₂.hom ≫ Functor.whiskerRight b₁.hom q₂ ≫
        Functor.whiskerLeft ι₁ wq.hom)
    (hc : v.hom ≫ c₃.hom = Functor.whiskerRight c₁.hom p₂ ≫ Functor.whiskerLeft q₁ c₂.hom ≫ wq.hom)
    (M : C₁) :
    ι₃.map (u.hom.app M) ≫
        (Functor.isoWhiskerRight a₃ ι₃ ≪≫ b₃ ≪≫ Functor.isoWhiskerLeft ι₁ c₃.symm).hom.app M =
      (Functor.isoWhiskerRight a₂ ι₃ ≪≫ b₂ ≪≫ Functor.isoWhiskerLeft ι₂ c₂.symm).hom.app
          (e₁.obj M) ≫
        p₂.map ((Functor.isoWhiskerRight a₁ ι₂ ≪≫ b₁ ≪≫
          Functor.isoWhiskerLeft ι₁ c₁.symm).hom.app M) ≫ v.hom.app (ι₁.obj M) := by
  have ha' : u.hom.app M ≫ a₃.hom.app M =
      e₂.map (a₁.hom.app M) ≫ a₂.hom.app (m₁.obj M) ≫ wm.hom.app M := by
    simpa using NatTrans.congr_app ha M
  have hb' : ι₃.map (wm.hom.app M) ≫ b₃.hom.app M =
      b₂.hom.app (m₁.obj M) ≫ q₂.map (b₁.hom.app M) ≫ wq.hom.app (ι₁.obj M) := by
    simpa using NatTrans.congr_app hb M
  have hc' : c₂.inv.app (q₁.obj (ι₁.obj M)) ≫ p₂.map (c₁.inv.app (ι₁.obj M)) ≫
      v.hom.app (ι₁.obj M) = wq.hom.app (ι₁.obj M) ≫ c₃.inv.app (ι₁.obj M) := by
    have h0 : v.hom.app (ι₁.obj M) ≫ c₃.hom.app (ι₁.obj M) =
        p₂.map (c₁.hom.app (ι₁.obj M)) ≫ c₂.hom.app (q₁.obj (ι₁.obj M)) ≫
          wq.hom.app (ι₁.obj M) := by
      simpa using NatTrans.congr_app hc (ι₁.obj M)
    rw [← cancel_mono (c₃.hom.app (ι₁.obj M))]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [h0, ← p₂.map_comp_assoc, Iso.inv_hom_id_app, p₂.map_id, Category.id_comp,
      Iso.inv_hom_id_app_assoc]
  have n₁ : c₂.inv.app (ι₂.obj (e₁.obj M)) ≫ p₂.map (ι₂.map (a₁.hom.app M) ≫ b₁.hom.app M) =
      q₂.map (ι₂.map (a₁.hom.app M) ≫ b₁.hom.app M) ≫ c₂.inv.app (q₁.obj (ι₁.obj M)) :=
    (c₂.inv.naturality _).symm
  have n₂ : ι₃.map (m₂.map (a₁.hom.app M)) ≫ b₂.hom.app (m₁.obj M) =
      b₂.hom.app (e₁.obj M) ≫ q₂.map (ι₂.map (a₁.hom.app M)) :=
    b₂.hom.naturality (a₁.hom.app M)
  have n₃ : e₂.map (a₁.hom.app M) ≫ a₂.hom.app (m₁.obj M) =
      a₂.hom.app (e₁.obj M) ≫ m₂.map (a₁.hom.app M) :=
    a₂.hom.naturality _
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [← p₂.map_comp_assoc (ι₂.map (a₁.hom.app M)) (b₁.hom.app M), reassoc_of% n₁, hc',
    Functor.map_comp, Category.assoc, ← reassoc_of% n₂, ← reassoc_of% hb',
    ← ι₃.map_comp_assoc (u.hom.app M) (a₃.hom.app M), ha', reassoc_of% n₃, ι₃.map_comp,
    ι₃.map_comp, Category.assoc, Category.assoc]

/-- The variant of `Stacks.CategoryTheory.squareIso_pasting_of_layers'` whose middle layers are
each a composite of three isomorphisms `b_i ≪≫ b'_i ≪≫ b''_i`, the squares being written fully
right-associated. -/
theorem squareIso_pasting_of_layers''
    {G₁ H₁ : C₁ ⥤ D₂} {G₂ H₂ : C₂ ⥤ D₃} {G₃ H₃ : C₁ ⥤ D₃}
    (a₁ : e₁ ≅ m₁) (a₂ : e₂ ≅ m₂) (a₃ : e₃ ≅ m₃)
    (b₁ : m₁ ⋙ ι₂ ≅ G₁) (b₂ : m₂ ⋙ ι₃ ≅ G₂) (b₃ : m₃ ⋙ ι₃ ≅ G₃)
    (b'₁ : G₁ ≅ H₁) (b'₂ : G₂ ≅ H₂) (b'₃ : G₃ ≅ H₃)
    (b''₁ : H₁ ≅ ι₁ ⋙ q₁) (b''₂ : H₂ ≅ ι₂ ⋙ q₂) (b''₃ : H₃ ≅ ι₁ ⋙ q₃)
    (c₁ : p₁ ≅ q₁) (c₂ : p₂ ≅ q₂) (c₃ : p₃ ≅ q₃)
    (u : e₁ ⋙ e₂ ≅ e₃) (wm : m₁ ⋙ m₂ ≅ m₃) (wq : q₁ ⋙ q₂ ≅ q₃) (v : p₁ ⋙ p₂ ≅ p₃)
    (ha : u.hom ≫ a₃.hom =
      Functor.whiskerRight a₁.hom e₂ ≫ Functor.whiskerLeft m₁ a₂.hom ≫ wm.hom)
    (hb : Functor.whiskerRight wm.hom ι₃ ≫ (b₃ ≪≫ b'₃ ≪≫ b''₃).hom =
      Functor.whiskerLeft m₁ (b₂ ≪≫ b'₂ ≪≫ b''₂).hom ≫
        Functor.whiskerRight (b₁ ≪≫ b'₁ ≪≫ b''₁).hom q₂ ≫ Functor.whiskerLeft ι₁ wq.hom)
    (hc : v.hom ≫ c₃.hom = Functor.whiskerRight c₁.hom p₂ ≫ Functor.whiskerLeft q₁ c₂.hom ≫ wq.hom)
    (M : C₁) :
    ι₃.map (u.hom.app M) ≫
        (Functor.isoWhiskerRight a₃ ι₃ ≪≫ b₃ ≪≫ b'₃ ≪≫ b''₃ ≪≫
          Functor.isoWhiskerLeft ι₁ c₃.symm).hom.app M =
      (Functor.isoWhiskerRight a₂ ι₃ ≪≫ b₂ ≪≫ b'₂ ≪≫ b''₂ ≪≫
          Functor.isoWhiskerLeft ι₂ c₂.symm).hom.app (e₁.obj M) ≫
        p₂.map ((Functor.isoWhiskerRight a₁ ι₂ ≪≫ b₁ ≪≫ b'₁ ≪≫ b''₁ ≪≫
          Functor.isoWhiskerLeft ι₁ c₁.symm).hom.app M) ≫ v.hom.app (ι₁.obj M) := by
  simpa only [Iso.trans_assoc] using squareIso_pasting_of_layers' a₁ a₂ a₃ (b₁ ≪≫ b'₁ ≪≫ b''₁)
    (b₂ ≪≫ b'₂ ≪≫ b''₂) (b₃ ≪≫ b'₃ ≪≫ b''₃) c₁ c₂ c₃ u wm wq v ha hb hc M

/-- `Stacks.CategoryTheory.squareIso_pasting_of_layers''` for squares `β_i` given together with
their decomposition into layers. -/
theorem squareIso_pasting_of_layers_of_eq
    {G₁ H₁ : C₁ ⥤ D₂} {G₂ H₂ : C₂ ⥤ D₃} {G₃ H₃ : C₁ ⥤ D₃}
    {a₁ : e₁ ≅ m₁} {a₂ : e₂ ≅ m₂} {a₃ : e₃ ≅ m₃}
    {b₁ : m₁ ⋙ ι₂ ≅ G₁} {b₂ : m₂ ⋙ ι₃ ≅ G₂} {b₃ : m₃ ⋙ ι₃ ≅ G₃}
    {b'₁ : G₁ ≅ H₁} {b'₂ : G₂ ≅ H₂} {b'₃ : G₃ ≅ H₃}
    {b''₁ : H₁ ≅ ι₁ ⋙ q₁} {b''₂ : H₂ ≅ ι₂ ⋙ q₂} {b''₃ : H₃ ≅ ι₁ ⋙ q₃}
    {c₁ : p₁ ≅ q₁} {c₂ : p₂ ≅ q₂} {c₃ : p₃ ≅ q₃}
    (β₁ : e₁ ⋙ ι₂ ≅ ι₁ ⋙ p₁) (β₂ : e₂ ⋙ ι₃ ≅ ι₂ ⋙ p₂) (β₃ : e₃ ⋙ ι₃ ≅ ι₁ ⋙ p₃)
    (hβ₁ : β₁ = Functor.isoWhiskerRight a₁ ι₂ ≪≫ b₁ ≪≫ b'₁ ≪≫ b''₁ ≪≫
      Functor.isoWhiskerLeft ι₁ c₁.symm)
    (hβ₂ : β₂ = Functor.isoWhiskerRight a₂ ι₃ ≪≫ b₂ ≪≫ b'₂ ≪≫ b''₂ ≪≫
      Functor.isoWhiskerLeft ι₂ c₂.symm)
    (hβ₃ : β₃ = Functor.isoWhiskerRight a₃ ι₃ ≪≫ b₃ ≪≫ b'₃ ≪≫ b''₃ ≪≫
      Functor.isoWhiskerLeft ι₁ c₃.symm)
    (u : e₁ ⋙ e₂ ≅ e₃) (wm : m₁ ⋙ m₂ ≅ m₃) (wq : q₁ ⋙ q₂ ≅ q₃) (v : p₁ ⋙ p₂ ≅ p₃)
    (ha : u.hom ≫ a₃.hom =
      Functor.whiskerRight a₁.hom e₂ ≫ Functor.whiskerLeft m₁ a₂.hom ≫ wm.hom)
    (hb : Functor.whiskerRight wm.hom ι₃ ≫ (b₃ ≪≫ b'₃ ≪≫ b''₃).hom =
      Functor.whiskerLeft m₁ (b₂ ≪≫ b'₂ ≪≫ b''₂).hom ≫
        Functor.whiskerRight (b₁ ≪≫ b'₁ ≪≫ b''₁).hom q₂ ≫ Functor.whiskerLeft ι₁ wq.hom)
    (hc : v.hom ≫ c₃.hom = Functor.whiskerRight c₁.hom p₂ ≫ Functor.whiskerLeft q₁ c₂.hom ≫ wq.hom)
    (M : C₁) :
    ι₃.map (u.hom.app M) ≫ β₃.hom.app M =
      β₂.hom.app (e₁.obj M) ≫ p₂.map (β₁.hom.app M) ≫ v.hom.app (ι₁.obj M) := by
  subst hβ₁ hβ₂ hβ₃
  exact squareIso_pasting_of_layers'' a₁ a₂ a₃ b₁ b₂ b₃ b'₁ b'₂ b'₃ b''₁ b''₂ b''₃ c₁ c₂ c₃
    u wm wq v ha hb hc M

end Stacks.CategoryTheory

end
