module

public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Transporting a natural identification of Hom-groups to shifted Hom-groups

Let `F₁ : C ⥤ D₁` and `F₂ : C ⥤ D₂` be functors commuting with the shift by `ℤ`, let `a₁` and
`a₂` be objects of `D₁` and `D₂`, and let `P` be a class of objects of `C` stable under the
shifts. Suppose given, for every `N` in `P`, an identification

`θ_N : Hom(a₁, F₁ N) ≃+ Hom(a₂, F₂ N)`

natural in `N`. Then for every `n` there is an identification of shifted Hom-groups

`Hom(a₁, (F₁ N)[n]) ≃+ Hom(a₂, (F₂ N)[n])`,

namely `θ_{N[n]}` conjugated by the commutation isomorphisms `F_k(N[n]) ≅ (F_k N)[n]`, and it
is natural in `N` and **compatible with connecting maps**: for `δ : N₃ ⟶ N₁[1]` in `C`, it
carries the composite with the image of `δ` under `F₁` to the composite with the image of `δ`
under `F₂`.

## Main definitions

* `CategoryTheory.ShiftedHom.transport`: the identification of shifted Hom-groups.

## Main results

* `CategoryTheory.ShiftedHom.transport_naturality`: it is natural in `N`.
* `CategoryTheory.ShiftedHom.transport_comp_map`: it is compatible with connecting maps.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace CategoryTheory.ShiftedHom

universe v₀ v₁ v₂ u₀ u₁ u₂

variable {C : Type u₀} {D₁ : Type u₁} {D₂ : Type u₂} [Category.{v₀} C] [Category.{v₁} D₁]
  [Category.{v₂} D₂] [HasShift C ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
  [Preadditive D₁] [Preadditive D₂]
  (F₁ : C ⥤ D₁) (F₂ : C ⥤ D₂) [hF₁ : F₁.CommShift ℤ] [hF₂ : F₂.CommShift ℤ]
  (a₁ : D₁) (a₂ : D₂) (P : ObjectProperty C)

/-- A family of identifications `Hom(a₁, F₁ N) ≃+ Hom(a₂, F₂ N)`, one for each `N` in `P`,
natural in `N`. -/
structure NaturalHomIdentification where
  /-- The identification at `N`. -/
  equiv : ∀ N : C, P N → ((a₁ ⟶ F₁.obj N) ≃+ (a₂ ⟶ F₂.obj N))
  /-- Its naturality in `N`. -/
  naturality : ∀ {N N' : C} (hN : P N) (hN' : P N') (g : N ⟶ N') (x : a₁ ⟶ F₁.obj N),
    equiv N' hN' (x ≫ F₁.map g) = equiv N hN x ≫ F₂.map g

variable {F₁ F₂ a₁ a₂ P}
variable (θ : NaturalHomIdentification F₁ F₂ a₁ a₂ P)

/-- **The identification of shifted Hom-groups.** At `N` in `P` and `n : ℤ` it sends
`x : a₁ ⟶ (F₁ N)[n]` to `θ_{N[n]}(x ≫ (F₁(N[n]) ≅ (F₁ N)[n])⁻¹) ≫ (F₂(N[n]) ≅ (F₂ N)[n])`. -/
def transport (hP : ∀ (N : C) (n : ℤ), P N → P (N⟦n⟧)) (N : C) (hN : P N) (n : ℤ) :
    ShiftedHom a₁ (F₁.obj N) n ≃+ ShiftedHom a₂ (F₂.obj N) n where
  toFun x := θ.equiv (N⟦n⟧) (hP N n hN) (x ≫ (F₁.commShiftIso n).inv.app N) ≫
    (F₂.commShiftIso n).hom.app N
  invFun y := (θ.equiv (N⟦n⟧) (hP N n hN)).symm (y ≫ (F₂.commShiftIso n).inv.app N) ≫
    (F₁.commShiftIso n).hom.app N
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp [Preadditive.add_comp]

/-- The value of `transport θ hP N hN n` at `x` is
`θ_{N[n]}(x ≫ (F₁(N[n]) ≅ (F₁ N)[n])⁻¹) ≫ (F₂(N[n]) ≅ (F₂ N)[n])`. -/
theorem transport_apply (hP : ∀ (N : C) (n : ℤ), P N → P (N⟦n⟧)) (N : C) (hN : P N) (n : ℤ)
    (x : ShiftedHom a₁ (F₁.obj N) n) :
    transport θ hP N hN n x =
      θ.equiv (N⟦n⟧) (hP N n hN) (x ≫ (F₁.commShiftIso n).inv.app N) ≫
        (F₂.commShiftIso n).hom.app N := rfl

/-- **The identification of shifted Hom-groups is natural in `N`.** -/
theorem transport_naturality (hP : ∀ (N : C) (n : ℤ), P N → P (N⟦n⟧)) {N N' : C} (hN : P N)
    (hN' : P N') (g : N ⟶ N') (n : ℤ) (x : ShiftedHom a₁ (F₁.obj N) n) :
    transport θ hP N' hN' n (x ≫ (F₁.map g)⟦n⟧') =
      transport θ hP N hN n x ≫ (F₂.map g)⟦n⟧' := by
  rw [transport_apply, transport_apply, assoc, Functor.commShiftIso_inv_naturality,
    ← assoc, θ.naturality (hP N n hN) (hP N' n hN') (g⟦n⟧'), assoc, assoc,
    Functor.commShiftIso_hom_naturality]

/-- For `δ : N₃ ⟶ N₁[1]` and `1 + n = m`, the composite `(F N₃)[n] ⟶ (F N₁)[1][n] ⟶ (F N₁)[m]`
built from the image of `δ` under `F` is, through the commutation isomorphisms, the image under
`F` of `N₃[n] ⟶ N₁[1][n] ⟶ N₁[m]`. -/
theorem commShiftIso_inv_comp_map_shift {E : Type*} [Category E] [HasShift E ℤ]
    (F : C ⥤ E) [F.CommShift ℤ] {N₃ N₁ : C}
    (δ : ShiftedHom N₃ N₁ (1 : ℤ)) (n m : ℤ) (h : 1 + n = m) :
    (F.commShiftIso n).inv.app N₃ ≫
        F.map (δ⟦n⟧' ≫ (shiftFunctorAdd' C 1 n m h).inv.app N₁) =
      (δ.map F)⟦n⟧' ≫ (shiftFunctorAdd' E 1 n m h).inv.app (F.obj N₁) ≫
        (F.commShiftIso m).inv.app N₁ := by
  rw [← cancel_mono ((F.commShiftIso m).hom.app N₁)]
  simp only [assoc, Iso.inv_hom_id_app, comp_id]
  rw [F.commShiftIso_add' h, Functor.CommShift.isoAdd'_hom_app, Functor.map_comp, assoc,
    ← Functor.map_comp_assoc F ((shiftFunctorAdd' C 1 n m h).inv.app N₁), Iso.inv_hom_id_app,
    Functor.map_id, id_comp, ← assoc (F.map (δ⟦n⟧')), Functor.commShiftIso_hom_naturality]
  simp only [assoc, Iso.inv_hom_id_app_assoc, comp_id, ShiftedHom.map, Functor.map_comp]
  exact (congrArg _ (congrArg _ (comp_id _))).symm

/-- **The identification of shifted Hom-groups is compatible with connecting maps.** For
`δ : N₃ ⟶ N₁[1]` with `N₁`, `N₃` in `P` and `1 + n = m`, composing with the image of `δ` under
`F₁` on the source corresponds to composing with its image under `F₂` on the target. -/
theorem transport_comp_map (hP : ∀ (N : C) (n : ℤ), P N → P (N⟦n⟧)) {N₃ N₁ : C} (h₃ : P N₃)
    (h₁ : P N₁) (δ : ShiftedHom N₃ N₁ (1 : ℤ)) (n m : ℤ) (h : 1 + n = m)
    (x : ShiftedHom a₁ (F₁.obj N₃) n) :
    transport θ hP N₁ h₁ m (x.comp (δ.map F₁) h) =
      (transport θ hP N₃ h₃ n x).comp (δ.map F₂) h := by
  have key := θ.naturality (hP N₃ n h₃) (hP N₁ m h₁)
    (δ⟦n⟧' ≫ (shiftFunctorAdd' C 1 n m h).inv.app N₁) (x ≫ (F₁.commShiftIso n).inv.app N₃)
  rw [transport_apply, transport_apply]
  simp only [ShiftedHom.comp, assoc]
  rw [← commShiftIso_inv_comp_map_shift F₁ δ n m h, ← assoc x, key, assoc]
  congr 1
  have e2 := commShiftIso_inv_comp_map_shift F₂ δ n m h
  rw [← cancel_epi ((F₂.commShiftIso n).inv.app N₃), ← assoc, e2]
  simp only [assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
  exact congrArg _ (comp_id _)

/-! ### Natural bijections of Hom-sets are additive -/

section Equiv

variable {C' : Type u₀} {E₁ : Type u₁} {E₂ : Type u₂} [Category.{v₀} C'] [Category.{v₁} E₁]
  [Category.{v₂} E₂] (G₁ : C' ⥤ E₁) (G₂ : C' ⥤ E₂) (b₁ : E₁) (b₂ : E₂) (Q : ObjectProperty C')

/-- A family of bijections `Hom(b₁, G₁ N) ≃ Hom(b₂, G₂ N)`, one for each `N` in `Q`, natural in
`N`. -/
structure NaturalHomEquiv where
  /-- The bijection at `N`. -/
  equiv : ∀ N : C', Q N → ((b₁ ⟶ G₁.obj N) ≃ (b₂ ⟶ G₂.obj N))
  /-- Its naturality in `N`. -/
  naturality : ∀ {N N' : C'} (hN : Q N) (hN' : Q N') (g : N ⟶ N') (x : b₁ ⟶ G₁.obj N),
    equiv N' hN' (x ≫ G₁.map g) = equiv N hN x ≫ G₂.map g

variable {G₁ G₂ b₁ b₂ Q}

/-- The inverse family. -/
def NaturalHomEquiv.symm (θ : NaturalHomEquiv G₁ G₂ b₁ b₂ Q) :
    NaturalHomEquiv G₂ G₁ b₂ b₁ Q where
  equiv N hN := (θ.equiv N hN).symm
  naturality {N N'} hN hN' g y := by
    apply (θ.equiv N' hN').injective
    rw [Equiv.apply_symm_apply, θ.naturality hN hN', Equiv.apply_symm_apply]

/-- The composite of two families. -/
def NaturalHomEquiv.trans {E₃ : Type*} [Category E₃] {G₃ : C' ⥤ E₃} {b₃ : E₃}
    (θ : NaturalHomEquiv G₁ G₂ b₁ b₂ Q) (θ' : NaturalHomEquiv G₂ G₃ b₂ b₃ Q) :
    NaturalHomEquiv G₁ G₃ b₁ b₃ Q where
  equiv N hN := (θ.equiv N hN).trans (θ'.equiv N hN)
  naturality {N N'} hN hN' g x := by
    simp only [Equiv.trans_apply]
    rw [θ.naturality hN hN', θ'.naturality hN hN']

/-- Postcomposition with a natural isomorphism `G ≅ G'`. -/
def NaturalHomEquiv.ofIso {G G' : C' ⥤ E₁} (e : G ≅ G') :
    NaturalHomEquiv G G' b₁ b₁ Q where
  equiv N _ :=
    { toFun := fun x => x ≫ e.hom.app N
      invFun := fun y => y ≫ e.inv.app N
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  naturality {N N'} _ _ g x := by
    simp only [Equiv.coe_fn_mk, Category.assoc]
    rw [e.hom.naturality]

/-- Precomposition with an isomorphism `b' ≅ b`. -/
def NaturalHomEquiv.ofIsoSource {b' : E₁} (e : b' ≅ b₁) :
    NaturalHomEquiv G₁ G₁ b₁ b' Q where
  equiv N _ :=
    { toFun := fun x => e.hom ≫ x
      invFun := fun y => e.inv ≫ y
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  naturality {N N'} _ _ g x := by
    simp only [Equiv.coe_fn_mk, Category.assoc]

variable [Preadditive C'] [Preadditive E₁] [Preadditive E₂] [HasBinaryBiproducts C']
  [hG₁ : G₁.Additive] [hG₂ : G₂.Additive]

/-- **A natural bijection of Hom-sets out of fixed objects into additive functors is additive**,
on a class of objects closed under binary biproducts: the sum of `x` and `y` is the composite of
the map into the biproduct with components `x` and `y` with the image of the codiagonal. -/
theorem NaturalHomEquiv.map_add (θ : NaturalHomEquiv G₁ G₂ b₁ b₂ Q)
    (hQ : ∀ N N' : C', Q N → Q N' → Q (N ⊞ N')) {N : C'} (hN : Q N)
    (x y : b₁ ⟶ G₁.obj N) :
    θ.equiv N hN (x + y) = θ.equiv N hN x + θ.equiv N hN y := by
  have hB := hQ N N hN hN
  set z : b₁ ⟶ G₁.obj (N ⊞ N) := x ≫ G₁.map biprod.inl + y ≫ G₁.map biprod.inr with hz
  have hcodiag : z ≫ G₁.map (biprod.desc (𝟙 N) (𝟙 N)) = x + y := by
    simp only [hz, Preadditive.add_comp, Category.assoc, ← G₁.map_comp, biprod.inl_desc,
      biprod.inr_desc, G₁.map_id, Category.comp_id]
  have hfst : θ.equiv (N ⊞ N) hB z ≫ G₂.map biprod.fst = θ.equiv N hN x := by
    rw [← θ.naturality hB hN]
    congr 1
    simp only [hz, Preadditive.add_comp, Category.assoc, ← G₁.map_comp, biprod.inl_fst,
      biprod.inr_fst, G₁.map_id, G₁.map_zero, Category.comp_id, Limits.comp_zero, add_zero]
  have hsnd : θ.equiv (N ⊞ N) hB z ≫ G₂.map biprod.snd = θ.equiv N hN y := by
    rw [← θ.naturality hB hN]
    congr 1
    simp only [hz, Preadditive.add_comp, Category.assoc, ← G₁.map_comp, biprod.inl_snd,
      biprod.inr_snd, G₁.map_id, G₁.map_zero, Category.comp_id, Limits.comp_zero, zero_add]
  have hdecomp : θ.equiv (N ⊞ N) hB z =
      θ.equiv N hN x ≫ G₂.map biprod.inl + θ.equiv N hN y ≫ G₂.map biprod.inr := by
    rw [← hfst, ← hsnd]
    conv_lhs => rw [← Category.comp_id (θ.equiv (N ⊞ N) hB z), ← G₂.map_id, ← biprod.total,
      G₂.map_add, Preadditive.comp_add]
    simp only [G₂.map_comp, Category.assoc]
  rw [← hcodiag, θ.naturality hB hN, hdecomp, Preadditive.add_comp, Category.assoc, Category.assoc,
    ← G₂.map_comp, ← G₂.map_comp, biprod.inl_desc, biprod.inr_desc, G₂.map_id,
    Category.comp_id, Category.comp_id]

/-- A natural bijection of Hom-sets, on a class closed under binary biproducts, as a natural
identification of Hom-groups. -/
def NaturalHomEquiv.toIdentification (θ : NaturalHomEquiv G₁ G₂ b₁ b₂ Q)
    (hQ : ∀ N N' : C', Q N → Q N' → Q (N ⊞ N')) :
    NaturalHomIdentification G₁ G₂ b₁ b₂ Q where
  equiv N hN :=
    { θ.equiv N hN with
      map_add' := fun x y => θ.map_add hQ hN x y }
  naturality hN hN' g x := θ.naturality hN hN' g x

end Equiv

end CategoryTheory.ShiftedHom

end
