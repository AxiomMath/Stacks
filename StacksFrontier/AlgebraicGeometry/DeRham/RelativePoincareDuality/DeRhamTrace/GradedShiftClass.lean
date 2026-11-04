module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.PushedPairingShiftTarget

/-!
# Perfectness at every shift from a shift-stable class of pairings

Let `P₀` be push data for pairings (`CategoryTheory.Functor.PairingPushData`). A pairing is
perfect at every shift (`CategoryTheory.Functor.PairingPushData.AllPerf`) when its pushings along
all the push data reachable from `P₀` by shifts are perfect. Pushing along a shifted datum is
pushing the shifted pairing along the given one, so a pairing is perfect at every shift as soon as
it lies in a class of pairings stable under shifting whose members all push to perfect pairings
along `P₀` itself. This file records that reduction, together with the invariance of
perfectness of one pushing under isomorphisms of the paired objects and under signs, and the
behaviour of compatibility of pairings under composition and shifts.

## Main results

* `CategoryTheory.Functor.PairingCompatible.trans`
* `CategoryTheory.Functor.PairingCompatible.shiftedPairing`
* `CategoryTheory.Functor.bijective_pairingPrecomp_iff_of_pairingCompatible`
* `CategoryTheory.Functor.PairingPushData.perf_iff_of_pairingCompatible`
* `CategoryTheory.Functor.PairingPushData.allPerf_of_shiftStable`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

section Compatible

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D] {T : C₁ ⥤ C₂ ⥤ D}

/-- Compatibility of pairings composes along composites of the maps. -/
theorem PairingCompatible.trans {K₁ K₂ K₃ : C₁} {L₁ L₂ L₃ : C₂} {M : D}
    {φ₁ : (T.obj K₁).obj L₁ ⟶ M} {φ₂ : (T.obj K₂).obj L₂ ⟶ M} {φ₃ : (T.obj K₃).obj L₃ ⟶ M}
    {e₁ : K₁ ⟶ K₂} {e₁' : L₂ ⟶ L₁} {e₂ : K₂ ⟶ K₃} {e₂' : L₃ ⟶ L₂}
    (h₁ : T.PairingCompatible φ₁ φ₂ e₁ e₁') (h₂ : T.PairingCompatible φ₂ φ₃ e₂ e₂') :
    T.PairingCompatible φ₁ φ₃ (e₁ ≫ e₂) (e₂' ≫ e₁') := by
  have h₁' : (T.map e₁).app L₂ ≫ φ₂ = (T.obj K₁).map e₁' ≫ φ₁ := h₁
  have h₂' : (T.map e₂).app L₃ ≫ φ₃ = (T.obj K₂).map e₂' ≫ φ₂ := h₂
  unfold PairingCompatible
  rw [Functor.map_comp, NatTrans.comp_app, Category.assoc, h₂', ← NatTrans.naturality_assoc, h₁',
    Functor.map_comp, Category.assoc]

/-- Compatibility of a pairing with itself along identities. -/
theorem pairingCompatible_id {K : C₁} {L : C₂} {M : D} (φ : (T.obj K).obj L ⟶ M) :
    T.PairingCompatible φ φ (𝟙 K) (𝟙 L) := by
  simp [PairingCompatible]

/-- Compatible pairings along isomorphisms, read backwards. -/
theorem PairingCompatible.symm {K K' : C₁} {L L' : C₂} {M : D} {φ : (T.obj K).obj L ⟶ M}
    {φ' : (T.obj K').obj L' ⟶ M} {e : K ⟶ K'} {e' : L' ⟶ L} [IsIso e] [IsIso e']
    (h : T.PairingCompatible φ φ' e e') :
    T.PairingCompatible φ' φ (CategoryTheory.inv e) (CategoryTheory.inv e') := by
  have h' : (T.map e).app L' ≫ φ' = (T.obj K).map e' ≫ φ := h
  unfold PairingCompatible
  rw [← cancel_epi ((T.map e).app L), ← NatTrans.comp_app_assoc, ← Functor.map_comp,
    IsIso.hom_inv_id, Functor.map_id, NatTrans.id_app, Category.id_comp,
    ← NatTrans.naturality_assoc, h', ← Functor.map_comp_assoc, IsIso.inv_hom_id, Functor.map_id,
    Category.id_comp]

/-- Compatibility of pairings survives multiplying both by a sign. -/
theorem PairingCompatible.units_smul [Preadditive D] {K K' : C₁} {L L' : C₂} {M : D}
    {φ : (T.obj K).obj L ⟶ M} {φ' : (T.obj K').obj L' ⟶ M} {e : K ⟶ K'} {e' : L' ⟶ L}
    (h : T.PairingCompatible φ φ' e e') (ε : ℤˣ) :
    T.PairingCompatible (ε • φ) (ε • φ') e e' := by
  have h' : (T.map e).app L' ≫ φ' = (T.obj K).map e' ≫ φ := h
  unfold PairingCompatible
  rw [Linear.comp_units_smul, Linear.comp_units_smul, h']

/-- Pairings related by precomposition with `e ⊗ e''` are compatible along `e` and `e''⁻¹`. -/
theorem pairingCompatible_of_eq {K K' : C₁} {L L' : C₂} {M : D} {φ : (T.obj K).obj L ⟶ M}
    {φ' : (T.obj K').obj L' ⟶ M} (e : K ⟶ K') (e'' : L ⟶ L') [IsIso e'']
    (h : (T.map e).app L ≫ (T.obj K').map e'' ≫ φ' = φ) :
    T.PairingCompatible φ φ' e (CategoryTheory.inv e'') := by
  unfold PairingCompatible
  rw [← h, NatTrans.naturality_assoc, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
    Functor.map_id, Category.id_comp]

/-- **Perfectness of a pairing at `Z` is invariant under isomorphisms of the paired objects.** -/
theorem bijective_pairingPrecomp_iff_of_pairingCompatible {K K' : C₁} {L L' : C₂} {M : D}
    {φ : (T.obj K).obj L ⟶ M} {φ' : (T.obj K').obj L' ⟶ M} (e : K ⟶ K') (e' : L' ⟶ L)
    [IsIso e] [IsIso e'] (h : T.PairingCompatible φ φ' e e') (Z : C₁) :
    Function.Bijective (T.pairingPrecomp φ Z) ↔ Function.Bijective (T.pairingPrecomp φ' Z) := by
  have hA : Function.Bijective (fun v : Z ⟶ K => v ≫ e) := (asIso e).homToEquiv.bijective
  have hB : Function.Bijective (fun w : (T.obj Z).obj L ⟶ M => (T.obj Z).map e' ≫ w) :=
    ((T.obj Z).mapIso (asIso e')).homFromEquiv.symm.bijective
  have hcomp : T.pairingPrecomp φ' Z ∘ (fun v => v ≫ e) =
      (fun w => (T.obj Z).map e' ≫ w) ∘ T.pairingPrecomp φ Z :=
    funext fun v => h.pairingPrecomp_comp v
  rw [← Function.Bijective.of_comp_iff _ hA, hcomp, Function.Bijective.of_comp_iff' hB]

/-- `pairingCompatible_of_eq` for an isomorphism of the second objects. -/
theorem pairingCompatible_of_eq_iso {K K' : C₁} {L L' : C₂} {M : D} {φ : (T.obj K).obj L ⟶ M}
    {φ' : (T.obj K').obj L' ⟶ M} (e : K ⟶ K') (e'' : L ≅ L')
    (h : (T.map e).app L ≫ (T.obj K').map e''.hom ≫ φ' = φ) :
    T.PairingCompatible φ φ' e e''.inv := by
  have := pairingCompatible_of_eq e e''.hom h
  rwa [IsIso.Iso.inv_hom] at this

/-- `bijective_pairingPrecomp_iff_of_pairingCompatible` for isomorphisms of the paired objects. -/
theorem bijective_pairingPrecomp_iff_of_pairingCompatible_iso {K K' : C₁} {L L' : C₂} {M : D}
    {φ : (T.obj K).obj L ⟶ M} {φ' : (T.obj K').obj L' ⟶ M} (e : K ≅ K') (e' : L' ≅ L)
    (h : T.PairingCompatible φ φ' e.hom e'.hom) (Z : C₁) :
    Function.Bijective (T.pairingPrecomp φ Z) ↔ Function.Bijective (T.pairingPrecomp φ' Z) :=
  bijective_pairingPrecomp_iff_of_pairingCompatible e.hom e'.hom h Z

end Compatible

section Shift

variable {C₁ C₂ C : Type*} [Category* C₁] [Category* C₂] [Category* C]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] {T : C₁ ⥤ C₂ ⥤ C} [T.CommShift₂Int]

/-- **Compatibility of pairings is preserved by shifting**: the shifts of compatible pairings are
compatible along the shifted maps. -/
theorem PairingCompatible.shiftedPairing {K K' : C₁} {L L' : C₂} {M : C}
    {φ : (T.obj K).obj L ⟶ M} {φ' : (T.obj K').obj L' ⟶ M} {e : K ⟶ K'} {e' : L' ⟶ L}
    (h : T.PairingCompatible φ φ' e e') (n m : ℤ) (hnm : n + m = 0) :
    T.PairingCompatible (T.shiftedPairing φ n m hnm) (T.shiftedPairing φ' n m hnm) (e⟦n⟧')
      (e'⟦m⟧') := by
  have h' : (T.map e).app L' ≫ φ' = (T.obj K).map e' ≫ φ := h
  unfold PairingCompatible
  rw [shiftedPairing_eq_comp T φ' n m hnm, shiftedPairing_eq_comp T φ n m hnm,
    reassoc_of% (shiftedPairing_id_natural_left T e L' n m hnm), h',
    ← reassoc_of% (shiftedPairing_id_natural_right T K e' n m hnm)]

/-- The shift of a pairing multiplied by a sign is the shift multiplied by the sign. -/
theorem shiftedPairing_units_smul {K : C₁} {L : C₂} {M : C} (φ : (T.obj K).obj L ⟶ M)
    (ε : ℤˣ) (n m : ℤ) (hnm : n + m = 0) :
    T.shiftedPairing (ε • φ) n m hnm = ε • T.shiftedPairing φ n m hnm := by
  simp [shiftedPairing]

end Shift

namespace PairingPushData

variable {C₁ C₂ C D : Type*} [Category* C₁] [Category* C₂] [Category* C] [Category* D]
  [HasZeroObject C₁] [HasZeroObject C₂] [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [∀ n : ℤ, (shiftFunctor C₂ n).Additive]
  [Pretriangulated C₁] [Pretriangulated C₂]
  {T : C₁ ⥤ C₂ ⥤ C} {T' : D ⥤ D ⥤ D} {R : C ⥤ D}
  [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [T.CommShift₂Int]
  [∀ Z : D, (T'.obj Z).Additive]

omit [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [T.CommShift₂Int]
  [∀ Z : D, (T'.obj Z).Additive] in
/-- **Perfectness of a pushing is invariant under isomorphisms of the paired objects.** -/
theorem perf_iff_of_pairingCompatible (P : PairingPushData T T' R) {K K' : C₁} {L L' : C₂}
    {M : C} {N : D} (τ : R.obj M ⟶ N) {β : (T.obj K).obj L ⟶ M} {β' : (T.obj K').obj L' ⟶ M}
    (e : K ⟶ K') (e' : L' ⟶ L) [IsIso e] [IsIso e'] (h : T.PairingCompatible β β' e e') :
    P.Perf τ β ↔ P.Perf τ β' := by
  have key : ∀ Z : D,
      Function.Bijective (T'.pairingPrecomp (P.pushedPairing τ β) Z) ↔
        Function.Bijective (T'.pairingPrecomp (P.pushedPairing τ β') Z) := fun Z =>
    bijective_pairingPrecomp_iff_of_pairingCompatible _ _ (P.pairingCompatible_pushedPairing τ h) Z
  exact ⟨fun hβ Z => (key Z).1 (hβ Z), fun hβ Z => (key Z).2 (hβ Z)⟩

omit [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [T.CommShift₂Int]
  [∀ Z : D, (T'.obj Z).Additive] in
/-- Perfectness of a pushing is invariant under a sign. -/
theorem perf_units_smul_iff [R.Additive] (P : PairingPushData T T' R) {K : C₁} {L : C₂} {M : C}
    {N : D} (τ : R.obj M ⟶ N) (β : (T.obj K).obj L ⟶ M) (ε : ℤˣ) :
    P.Perf τ (ε • β) ↔ P.Perf τ β := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rw [one_smul]
  · rw [Units.neg_smul, one_smul]
    simp only [Perf, pushedPairing_neg, bijective_pairingPrecomp_neg_iff]

/-- Perfectness of a pushing into a shifted target is perfectness of the pushing of the shifted
pairing (`CategoryTheory.Functor.PairingPushData.pushedPairing_shiftTarget`). -/
theorem perf_shiftTarget_iff (P : PairingPushData T T' R) (m : ℤ) {K : C₁} {L : C₂} {M : C}
    {N : D} (τ : R.obj (M⟦m⟧) ⟶ N) (β : (T.obj K).obj L ⟶ M) :
    (P.shiftTarget m).Perf τ β ↔ P.Perf τ (((T.obj K).commShiftIso m).hom.app L ≫ β⟦m⟧') := by
  simp only [Perf, pushedPairing_shiftTarget]
  exact Iff.rfl

/-- **Perfectness at every shift from a shift-stable class.** If a class of pairings into `M` is
stable under shifting and all its members push to perfect pairings along `P₀`, then all its
members are perfect at every shift. -/
theorem allPerf_of_shiftStable (P₀ : PairingPushData T T' R) {M : C} {N : D} (τ : R.obj M ⟶ N)
    (𝒞 : ∀ {K : C₁} {L : C₂}, ((T.obj K).obj L ⟶ M) → Prop)
    (hshift : ∀ {K : C₁} {L : C₂} (β : (T.obj K).obj L ⟶ M), 𝒞 β →
      ∀ (a b : ℤ) (h : a + b = 0), 𝒞 (T.shiftedPairing β a b h))
    (hbase : ∀ {K : C₁} {L : C₂} (β : (T.obj K).obj L ⟶ M), 𝒞 β → P₀.Perf τ β)
    {K : C₁} {L : C₂} (β : (T.obj K).obj L ⟶ M) (hβ : 𝒞 β) : P₀.AllPerf τ β := by
  intro P hP
  induction hP generalizing K L with
  | refl => exact hbase β hβ
  | shift a b h _ ih =>
    exact (perf_shiftedPairing_iff _ a b h τ β).1 (ih _ (hshift β hβ a b h))

end PairingPushData

end CategoryTheory.Functor
