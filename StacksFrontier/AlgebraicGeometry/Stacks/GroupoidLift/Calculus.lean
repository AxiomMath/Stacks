module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Basic

/-!
# Functoriality of the deformation modules of a groupoid

For a morphism of square-zero thickenings `φ : (C' → C) → (D' → D)` and points `w` of `C` and
`w₂ = φ ∘ w` of `D`, postcomposition with `φ` maps the module `Mod w` to `Mod w₂`
(`AlgebraicGeometry.Stack.GroupoidLift.modMap`). The transport along an arrow of the groupoid,
with prescribed endpoints, is `AlgebraicGeometry.Stack.GroupoidLift.transModAt`; it is
characterized by the transports of lifts (`transModAt_mk`), it is the identity along an
identity arrow, and it commutes with `modMap`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}} {P : Type u} [CommRing P] [Algebra A' P]
  {G : Groupoid A' κ P}

section Map

variable {C' C D' D : SmallAlg A' κ} {e : SqZero C' C} {e₂ : SqZero D' D}

/-- A map of thickenings commutes with the reductions, evaluated at an element of `C'`. -/
theorem SqZero.Hom.w_apply (φ : SqZero.Hom e e₂) (x : C'.obj) :
    e₂.q.hom.hom (φ.top.hom.hom x) = φ.bot.hom.hom (e.q.hom.hom x) :=
  congrArg (fun f : C' ⟶ D ↦ f.hom.hom x) φ.w

/-- A map of thickenings commutes with the reductions, after composing with an algebra map
`ℓ : P →ₐ[A'] C'`. -/
theorem SqZero.Hom.w_comp (φ : SqZero.Hom e e₂) (ℓ : P →ₐ[A'] C'.obj) :
    e₂.q.hom.hom.comp (φ.top.hom.hom.comp ℓ) = φ.bot.hom.hom.comp (e.q.hom.hom.comp ℓ) := by
  ext x
  exact φ.w_apply (ℓ x)

variable (φ : SqZero.Hom e e₂)

/-- Postcomposition with a map of thickenings, as a semilinear map. -/
def postcomp : (P →ₗ[A'] C'.obj) →ₛₗ[(φ.top.hom.hom : C'.obj →+* D'.obj)] (P →ₗ[A'] D'.obj) where
  toFun D := φ.top.hom.hom.toLinearMap ∘ₗ D
  map_add' _ _ := LinearMap.comp_add _ _ _
  map_smul' c D := by
    ext x
    simp

/-- `postcomp φ D` evaluates to `φ.top` applied to the value of `D`. -/
@[simp] theorem postcomp_apply (D : P →ₗ[A'] C'.obj) (x : P) :
    postcomp φ D x = φ.top.hom.hom (D x) := rfl

/-- Postcomposition with `φ` maps `Der e w` into `Der e₂ w₂`, where `w₂ = φ.bot ∘ w`. -/
theorem mem_Der_postcomp {w : P →ₐ[A'] C.obj} {w₂ : P →ₐ[A'] D.obj}
    (hw : φ.bot.hom.hom.comp w = w₂) {Dv : P →ₗ[A'] C'.obj} (hD : Dv ∈ Der e w) :
    postcomp φ Dv ∈ Der e₂ w₂ := by
  refine ⟨fun x ↦ by rw [postcomp_apply, φ.w_apply, hD.1 x, map_zero], fun x y a' b' ha hb ↦ ?_⟩
  obtain ⟨a, hax⟩ : ∃ a, e.q.hom.hom a = w x := e.surj _
  obtain ⟨b, hby⟩ : ∃ b, e.q.hom.hom b = w y := e.surj _
  rw [postcomp_apply, hD.2 x y a b hax hby, map_add, map_mul, map_mul]
  have hw' : ∀ z, φ.bot.hom.hom (w z) = w₂ z := fun z ↦
    congrArg (fun f : P →ₐ[A'] D.obj ↦ f z) hw
  have k₁ : e₂.q.hom.hom (φ.top.hom.hom a - a') = 0 := by
    rw [map_sub, φ.w_apply, ha, hax, hw', sub_self]
  have k₂ : e₂.q.hom.hom (φ.top.hom.hom b - b') = 0 := by
    rw [map_sub, φ.w_apply, hb, hby, hw', sub_self]
  have z₁ := e₂.mul_eq_zero k₁ (by rw [φ.w_apply, hD.1 y, map_zero])
  have z₂ := e₂.mul_eq_zero k₂ (by rw [φ.w_apply, hD.1 x, map_zero])
  rw [postcomp_apply, postcomp_apply]
  linear_combination z₁ + z₂

/-- Postcomposition with `φ` maps `S G e w` into `S G e₂ w₂`, where `w₂ = φ.bot ∘ w`. -/
theorem mem_S_postcomp {w : P →ₐ[A'] C.obj} {w₂ : P →ₐ[A'] D.obj}
    (hw : φ.bot.hom.hom.comp w = w₂) {Dv : P →ₗ[A'] C'.obj} (hD : Dv ∈ S G e w) :
    postcomp φ Dv ∈ S G e₂ w₂ := by
  induction hD using Submodule.span_induction with
  | mem Dv h =>
    obtain ⟨ℓ₁, ℓ₂, h₁, hrel, rfl⟩ := h
    have hrel' := Tr.map φ hrel
    have h₁' : e₂.q.hom.hom.comp (φ.top.hom.hom.comp ℓ₁) = w₂ := by
      rw [SqZero.Hom.w_comp, h₁, hw]
    rw [G.idt_map, hw] at hrel'
    have := sub_mem_S h₁' hrel'
    convert this using 1
    ext x
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

/-- **The map of deformation modules induced by a map of thickenings.** -/
def modMap {w : P →ₐ[A'] C.obj} {w₂ : P →ₐ[A'] D.obj} (hw : φ.bot.hom.hom.comp w = w₂) :
    Mod G e w →ₛₗ[(φ.top.hom.hom : C'.obj →+* D'.obj)] Mod G e₂ w₂ :=
  Submodule.liftQ _
    ((Submodule.mkQ _).comp
      { toFun := fun D ↦ ⟨postcomp φ D.1, mem_Der_postcomp φ hw D.2⟩
        map_add' := fun D E ↦ Subtype.ext (map_add _ _ _)
        map_smul' := fun c D ↦ Subtype.ext (map_smulₛₗ _ _ _) })
    fun D hD ↦ by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact mem_S_postcomp φ hw hD

/-- `modMap φ hw` sends the class of `Dv` to the class of `postcomp φ Dv`. -/
@[simp] theorem modMap_mk {w : P →ₐ[A'] C.obj} {w₂ : P →ₐ[A'] D.obj}
    (hw : φ.bot.hom.hom.comp w = w₂) (Dv : P →ₗ[A'] C'.obj) (hD : Dv ∈ Der e w) :
    modMap φ hw (mkMod (G := G) Dv hD) = mkMod (postcomp φ Dv) (mem_Der_postcomp φ hw hD) := rfl

end Map

/-! ### Linear maps out of `Mod` -/

section Ext

variable {C' C : SmallAlg A' κ} {e : SqZero C' C}

/-- The class of `Dv` in `Mod G e w` is the class of the difference of the lifts
`addLift Dv hD ℓ hℓ` and `ℓ`. -/
theorem mkMod_addLift {w : P →ₐ[A'] C.obj} (Dv : P →ₗ[A'] C'.obj) (hD : Dv ∈ Der e w)
    (ℓ : P →ₐ[A'] C'.obj) (hℓ : e.q.hom.hom.comp ℓ = w) :
    (mkMod (G := G) Dv hD : Mod G e w) =
      mkMod ((addLift Dv hD ℓ hℓ).toLinearMap - ℓ.toLinearMap)
        (sub_mem_Der hℓ (addLift_reduce Dv hD ℓ hℓ)) := by
  congr 1
  rw [addLift_toLinearMap, add_sub_cancel_left]

/-- Every element of `Mod G e w` is the class `mkMod Dv hD` of some `Dv ∈ Der e w`. -/
theorem Mod.mk_surjective {w : P →ₐ[A'] C.obj} (x : Mod G e w) :
    ∃ (Dv : P →ₗ[A'] C'.obj) (hD : Dv ∈ Der e w), x = mkMod Dv hD := by
  obtain ⟨⟨Dv, hD⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Dv, hD, rfl⟩

end Ext

/-! ### Transport with prescribed endpoints -/

section TransportAt

variable {C' C : SmallAlg A' κ} {e : SqZero C' C}
  (hκ : Cardinal.aleph0 ≤ κ) (hG : G.SrcFormallySmooth)

/-- **The transport along `r`, from `Mod w` to `Mod w'`.** -/
noncomputable def transModAt (r : G.arr.obj C) {w w' : P →ₐ[A'] C.obj} (hs : G.src r = w)
    (ht : G.tgt r = w') (ℓ₀ : P →ₐ[A'] C'.obj) (h₀ : e.q.hom.hom.comp ℓ₀ = w) :
    Mod G e w →ₗ[C'.obj] Mod G e w' := by
  subst hs ht
  exact transMod hκ hG r ℓ₀ h₀

/-- **The transport is computed by transporting lifts.** -/
theorem transModAt_mk (r : G.arr.obj C) {w w' : P →ₐ[A'] C.obj} (hs : G.src r = w)
    (ht : G.tgt r = w') (ℓ₀ : P →ₐ[A'] C'.obj) (h₀ : e.q.hom.hom.comp ℓ₀ = w)
    {ℓ ℓ' m m' : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w)
    (hℓ' : e.q.hom.hom.comp ℓ' = w) (t : Tr G e r ℓ m) (t' : Tr G e r ℓ' m') :
    transModAt hκ hG r hs ht ℓ₀ h₀ (mkMod (ℓ'.toLinearMap - ℓ.toLinearMap) (sub_mem_Der hℓ hℓ')) =
      mkMod (m'.toLinearMap - m.toLinearMap)
        (sub_mem_Der (t.reduce_tgt.trans ht) (t'.reduce_tgt.trans ht)) := by
  subst hs ht
  exact transDer_eq hκ hG r ℓ₀ h₀ hℓ hℓ' t t'

/-- Every class in `Mod G e w` is the difference of two lifts, with transports along `r` of the
lifts `ℓ₀` and the second one. -/
private theorem exists_mkMod_sub_tr (hG : G.SrcFormallySmooth) (r : G.arr.obj C)
    {w : P →ₐ[A'] C.obj} (hs : G.src r = w) (ℓ₀ : P →ₐ[A'] C'.obj)
    (h₀ : e.q.hom.hom.comp ℓ₀ = w) (x : Mod G e w) :
    ∃ (ℓ m₀ m₁ : P →ₐ[A'] C'.obj) (hℓ : e.q.hom.hom.comp ℓ = w), Tr G e r ℓ₀ m₀ ∧ Tr G e r ℓ m₁ ∧
      x = mkMod (ℓ.toLinearMap - ℓ₀.toLinearMap) (sub_mem_Der h₀ hℓ) := by
  obtain ⟨Dv, hD, rfl⟩ := Mod.mk_surjective x
  have hℓ := addLift_reduce Dv hD ℓ₀ h₀
  obtain ⟨m₀, t₀⟩ := exists_tr hG r ℓ₀ (h₀.trans hs.symm)
  obtain ⟨m₁, t₁⟩ := exists_tr hG r (addLift Dv hD ℓ₀ h₀) (hℓ.trans hs.symm)
  exact ⟨_, m₀, m₁, hℓ, t₀, t₁, mkMod_addLift Dv hD ℓ₀ h₀⟩

/-- The transport along an identity is the identity. -/
theorem transModAt_idt {w : P →ₐ[A'] C.obj} (hs : G.src (G.idt w) = w)
    (ht : G.tgt (G.idt w) = w) (ℓ₀ : P →ₐ[A'] C'.obj) (h₀ : e.q.hom.hom.comp ℓ₀ = w)
    (x : Mod G e w) : transModAt hκ hG (G.idt w) hs ht ℓ₀ h₀ x = x := by
  obtain ⟨Dv, hD, rfl⟩ := Mod.mk_surjective x
  rw [mkMod_addLift Dv hD ℓ₀ h₀]
  have hℓ := addLift_reduce Dv hD ℓ₀ h₀
  have t₀ : Tr G e (G.idt w) ℓ₀ ℓ₀ := by
    have := rel_refl (G := G) (e := e) ℓ₀
    rwa [h₀] at this
  have t₁ : Tr G e (G.idt w) (addLift Dv hD ℓ₀ h₀) (addLift Dv hD ℓ₀ h₀) := by
    have := rel_refl (G := G) (e := e) (addLift Dv hD ℓ₀ h₀)
    rwa [hℓ] at this
  rw [transModAt_mk hκ hG _ hs ht ℓ₀ h₀ h₀ hℓ t₀ t₁]

variable {D' D : SmallAlg A' κ} {e₂ : SqZero D' D} (φ : SqZero.Hom e e₂)

/-- **The transport commutes with the maps of thickenings.** -/
theorem modMap_transModAt (r : G.arr.obj C) {w w' : P →ₐ[A'] C.obj} (hs : G.src r = w)
    (ht : G.tgt r = w') (ℓ₀ : P →ₐ[A'] C'.obj) (h₀ : e.q.hom.hom.comp ℓ₀ = w)
    {w₂ w₂' : P →ₐ[A'] D.obj} (hw : φ.bot.hom.hom.comp w = w₂)
    (hw' : φ.bot.hom.hom.comp w' = w₂') (hs₂ : G.src (G.arr.map φ.bot r) = w₂)
    (ht₂ : G.tgt (G.arr.map φ.bot r) = w₂') (ℓ₂ : P →ₐ[A'] D'.obj)
    (h₂ : e₂.q.hom.hom.comp ℓ₂ = w₂) (x : Mod G e w) :
    modMap φ hw' (transModAt hκ hG r hs ht ℓ₀ h₀ x) =
      transModAt hκ hG (G.arr.map φ.bot r) hs₂ ht₂ ℓ₂ h₂ (modMap φ hw x) := by
  obtain ⟨_, _, _, hℓ, t₀, t₁, rfl⟩ := exists_mkMod_sub_tr hG r hs ℓ₀ h₀ x
  rw [transModAt_mk hκ hG r hs ht ℓ₀ h₀ h₀ hℓ t₀ t₁, modMap_mk, modMap_mk]
  have hred : ∀ {ℓ : P →ₐ[A'] C'.obj}, e.q.hom.hom.comp ℓ = w →
      e₂.q.hom.hom.comp (φ.top.hom.hom.comp ℓ) = w₂ := fun h ↦ by
    rw [SqZero.Hom.w_comp, h, hw]
  have hpost : ∀ (ℓ ℓ' : P →ₐ[A'] C'.obj), postcomp φ (ℓ'.toLinearMap - ℓ.toLinearMap) =
      (φ.top.hom.hom.comp ℓ').toLinearMap - (φ.top.hom.hom.comp ℓ).toLinearMap := by
    intro ℓ ℓ'
    ext x
    simp
  simp only [hpost]
  rw [transModAt_mk hκ hG _ hs₂ ht₂ ℓ₂ h₂ (hred h₀) (hred hℓ) (Tr.map φ t₀) (Tr.map φ t₁)]

/-- The transport only depends on the arrow. -/
theorem transModAt_congr {r r' : G.arr.obj C} (hr : r = r') {w w' : P →ₐ[A'] C.obj}
    (hs : G.src r = w) (ht : G.tgt r = w') (hs' : G.src r' = w) (ht' : G.tgt r' = w')
    (ℓ₀ ℓ₀' : P →ₐ[A'] C'.obj) (h₀ : e.q.hom.hom.comp ℓ₀ = w) (h₀' : e.q.hom.hom.comp ℓ₀' = w)
    (x : Mod G e w) :
    transModAt hκ hG r hs ht ℓ₀ h₀ x = transModAt hκ hG r' hs' ht' ℓ₀' h₀' x := by
  subst hr
  obtain ⟨_, _, _, hℓ, t₀, t₁, rfl⟩ := exists_mkMod_sub_tr hG r hs ℓ₀ h₀ x
  rw [transModAt_mk hκ hG r hs ht ℓ₀ h₀ h₀ hℓ t₀ t₁,
    transModAt_mk hκ hG r hs' ht' ℓ₀' h₀' h₀ hℓ t₀ t₁]

/-- Naturality of the transport, with the pulled-back arrow named. -/
theorem modMap_transModAt' {D' D : SmallAlg A' κ} {e₂ : SqZero D' D} (φ : SqZero.Hom e e₂)
    (r : G.arr.obj C) {w w' : P →ₐ[A'] C.obj} (hs : G.src r = w)
    (ht : G.tgt r = w') (ℓ₀ : P →ₐ[A'] C'.obj) (h₀ : e.q.hom.hom.comp ℓ₀ = w)
    {w₂ w₂' : P →ₐ[A'] D.obj} (hw : φ.bot.hom.hom.comp w = w₂)
    (hw' : φ.bot.hom.hom.comp w' = w₂') (r₂ : G.arr.obj D) (hr : G.arr.map φ.bot r = r₂)
    (hs₂ : G.src r₂ = w₂) (ht₂ : G.tgt r₂ = w₂') (ℓ₂ : P →ₐ[A'] D'.obj)
    (h₂ : e₂.q.hom.hom.comp ℓ₂ = w₂) (x : Mod G e w) :
    modMap φ hw' (transModAt hκ hG r hs ht ℓ₀ h₀ x) =
      transModAt hκ hG r₂ hs₂ ht₂ ℓ₂ h₂ (modMap φ hw x) := by
  subst hr
  exact modMap_transModAt hκ hG φ r hs ht ℓ₀ h₀ hw hw' hs₂ ht₂ ℓ₂ h₂ x

/-- **Transports compose.** -/
theorem transModAt_comp (r₁ r₂ : G.arr.obj C) (h : G.src r₂ = G.tgt r₁)
    {w₁ w₂ w₃ : P →ₐ[A'] C.obj} (hs₁ : G.src r₁ = w₁) (ht₁ : G.tgt r₁ = w₂)
    (hs₂ : G.src r₂ = w₂) (ht₂ : G.tgt r₂ = w₃) (hs : G.src (G.comp r₂ r₁ h) = w₁)
    (ht : G.tgt (G.comp r₂ r₁ h) = w₃) (ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj)
    (h₁ : e.q.hom.hom.comp ℓ₁ = w₁) (h₂ : e.q.hom.hom.comp ℓ₂ = w₂) (x : Mod G e w₁) :
    transModAt hκ hG (G.comp r₂ r₁ h) hs ht ℓ₁ h₁ x =
      transModAt hκ hG r₂ hs₂ ht₂ ℓ₂ h₂ (transModAt hκ hG r₁ hs₁ ht₁ ℓ₁ h₁ x) := by
  obtain ⟨_, m₀, m₁, hℓ, t₀, t₁, rfl⟩ := exists_mkMod_sub_tr hG r₁ hs₁ ℓ₁ h₁ x
  obtain ⟨k₀, u₀⟩ := exists_tr hG r₂ m₀ (t₀.reduce_tgt.trans h.symm)
  obtain ⟨k₁, u₁⟩ := exists_tr hG r₂ m₁ (t₁.reduce_tgt.trans h.symm)
  rw [transModAt_mk hκ hG _ hs ht ℓ₁ h₁ h₁ hℓ (Tr.comp h t₀ u₀) (Tr.comp h t₁ u₁),
    transModAt_mk hκ hG r₁ hs₁ ht₁ ℓ₁ h₁ h₁ hℓ t₀ t₁,
    transModAt_mk hκ hG r₂ hs₂ ht₂ ℓ₂ h₂ (t₀.reduce_tgt.trans ht₁) (t₁.reduce_tgt.trans ht₁) u₀ u₁]

end TransportAt

section MapComp

variable {C' C D' D E' E : SmallAlg A' κ} {e : SqZero C' C} {e₂ : SqZero D' D} {e₃ : SqZero E' E}

/-- **`modMap` is functorial.** -/
theorem modMap_modMap (φ : SqZero.Hom e e₂) (ψ : SqZero.Hom e₂ e₃) (χ : SqZero.Hom e e₃)
    (hχ : ∀ x, χ.top.hom.hom x = ψ.top.hom.hom (φ.top.hom.hom x))
    {w : P →ₐ[A'] C.obj} {w₂ : P →ₐ[A'] D.obj} {w₃ : P →ₐ[A'] E.obj}
    (hw : φ.bot.hom.hom.comp w = w₂) (hw₂ : ψ.bot.hom.hom.comp w₂ = w₃)
    (hw₃ : χ.bot.hom.hom.comp w = w₃) (x : Mod G e w) :
    modMap ψ hw₂ (modMap φ hw x) = modMap χ hw₃ x := by
  obtain ⟨Dv, hD, rfl⟩ := Mod.mk_surjective x
  rw [modMap_mk, modMap_mk, modMap_mk]
  congr 1
  ext y
  exact (hχ (Dv y)).symm

end MapComp

end AlgebraicGeometry.Stack.GroupoidLift

end
