module

public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.PairingIsoCriterion

/-!
# The five lemma for pairings along two distinguished triangles

Let `T : C₁ ⥤ C₂ ⥤ D` be a bifunctor, written `K ⊗ L`, and `M` an object of `D`. A pairing
`φ : K ⊗ L ⟶ M` determines, for every `Z`, the map `(Z ⟶ K) ⟶ (Z ⊗ L ⟶ M)`, `v ↦ (v ⊗ 1) ≫ φ`;
for a tensor–internal-Hom adjunction these maps are all bijective exactly when the map
`K ⟶ R𝓗om(L, M)` determined by `φ` is an isomorphism
(`TensorHomAdjunction.isIso_homEquiv_symm_iff`), which is what it means for `φ` to be a
perfect pairing.

Two pairings `φ : K ⊗ L ⟶ M`, `φ' : K' ⊗ L' ⟶ M` are *compatible* along `e : K ⟶ K'` and
`e' : L' ⟶ L` when `φ' ∘ (e ⊗ 1) = φ ∘ (1 ⊗ e')` on `K ⊗ L'`. This is the notion of the proof of
[Stacks, Tag 0G8K]: there a distinguished triangle `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` is paired with a
distinguished triangle `L₃ ⟶ L₂ ⟶ L₁ ⟶ L₃[1]`, the pairings of `Kᵢ` with `Lᵢ` being compatible
along all the maps of the two triangles, and if the outer pairings are perfect then so is the
middle one, by the five lemma ([Stacks, Tag 014A]).

This file proves that statement. The five lemma is applied to the long exact sequences of
`Hom(Z, -)` on the first triangle and of `Hom(Z ⊗ -, M)` on the second one, so no exactness
property of `R𝓗om(-, M)` is needed, only that `Z ⊗ -` is a triangulated functor. The pairings at
the shifted vertices are the shifts of the given ones (`CategoryTheory.Functor.shiftedPairing`),
and the shift of a perfect pairing is perfect.

## Main definitions

* `CategoryTheory.Functor.pairingPrecomp`: the map `v ↦ (v ⊗ 1) ≫ φ`.
* `CategoryTheory.Functor.PairingCompatible`: compatibility of two pairings along two maps.
* `CategoryTheory.Functor.shiftedPairing`: the pairing `K[n] ⊗ L[m] ⟶ M`, `n + m = 0`, of a
  pairing `K ⊗ L ⟶ M`.

## Main results

* `CategoryTheory.Functor.bijective_pairingPrecomp_of_five`: the five lemma for pairings.
* `CategoryTheory.Functor.bijective_pairingPrecomp_shiftedPairing_iff`: the shift of a pairing
  is perfect at `Z` exactly when the pairing is perfect at `Z[m]`.
* `CategoryTheory.Functor.bijective_pairingPrecomp_of_triangles`: the five lemma for pairings
  along two distinguished triangles.
* `TensorHomAdjunction.isIso_homEquiv_symm_of_triangles`: the same, for the maps `K ⟶ R𝓗om(L, M)`
  determined by the pairings.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

section Basic

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D] (T : C₁ ⥤ C₂ ⥤ D)

/-- The map `(Z ⟶ K) ⟶ (Z ⊗ L ⟶ M)`, `v ↦ (v ⊗ 1) ≫ φ`, determined by a pairing
`φ : K ⊗ L ⟶ M`. -/
def pairingPrecomp {K : C₁} {L : C₂} {M : D} (φ : (T.obj K).obj L ⟶ M) (Z : C₁) :
    (Z ⟶ K) → ((T.obj Z).obj L ⟶ M) :=
  fun v => (T.map v).app L ≫ φ

/-- Two pairings `φ : K ⊗ L ⟶ M` and `φ' : K' ⊗ L' ⟶ M` are compatible along `e : K ⟶ K'` and
`e' : L' ⟶ L` when the two pairings they induce on `K ⊗ L'` agree:
`φ' ∘ (e ⊗ 1) = φ ∘ (1 ⊗ e')`. -/
def PairingCompatible {K K' : C₁} {L L' : C₂} {M : D} (φ : (T.obj K).obj L ⟶ M)
    (φ' : (T.obj K').obj L' ⟶ M) (e : K ⟶ K') (e' : L' ⟶ L) : Prop :=
  (T.map e).app L' ≫ φ' = (T.obj K).map e' ≫ φ

variable {T}

/-- Along compatible pairings, composing with `e` corresponds to precomposing with `1 ⊗ e'`. -/
theorem PairingCompatible.pairingPrecomp_comp {K K' : C₁} {L L' : C₂} {M : D}
    {φ : (T.obj K).obj L ⟶ M} {φ' : (T.obj K').obj L' ⟶ M} {e : K ⟶ K'} {e' : L' ⟶ L}
    (h : T.PairingCompatible φ φ' e e') {Z : C₁} (v : Z ⟶ K) :
    T.pairingPrecomp φ' Z (v ≫ e) = (T.obj Z).map e' ≫ T.pairingPrecomp φ Z v := by
  simp only [pairingPrecomp, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [show (T.map e).app L' ≫ φ' = (T.obj K).map e' ≫ φ from h, ← Category.assoc,
    ← Category.assoc, ← (T.map v).naturality e']

/-- Precomposing `v : K' ⟶ K` with `w : Z ⟶ K'` corresponds to precomposing with `w ⊗ 1`. -/
theorem pairingPrecomp_comp {K K' : C₁} {L : C₂} {M : D} (φ : (T.obj K).obj L ⟶ M) {Z : C₁}
    (w : Z ⟶ K') (v : K' ⟶ K) :
    T.pairingPrecomp φ Z (w ≫ v) = (T.map w).app L ≫ T.pairingPrecomp φ K' v := by
  simp [pairingPrecomp]

end Basic

section Five

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D] (T : C₁ ⥤ C₂ ⥤ D)

/-- The map `v ↦ (v ⊗ 1) ≫ φ` commutes with subtraction. -/
theorem pairingPrecomp_sub [∀ L, (T.flip.obj L).Additive] {K : C₁} {L : C₂} {M : D}
    (φ : (T.obj K).obj L ⟶ M) {Z : C₁} (v w : Z ⟶ K) :
    T.pairingPrecomp φ Z (v - w) = T.pairingPrecomp φ Z v - T.pairingPrecomp φ Z w := by
  have h := (T.flip.obj L).map_sub (f := v) (g := w)
  simp only [flip_obj_map] at h
  simp [pairingPrecomp, h, Preadditive.sub_comp]

/-- The map `v ↦ (v ⊗ 1) ≫ φ` commutes with addition. -/
theorem pairingPrecomp_add [∀ L, (T.flip.obj L).Additive] {K : C₁} {L : C₂} {M : D}
    (φ : (T.obj K).obj L ⟶ M) {Z : C₁} (v w : Z ⟶ K) :
    T.pairingPrecomp φ Z (v + w) = T.pairingPrecomp φ Z v + T.pairingPrecomp φ Z w := by
  have h := (T.flip.obj L).map_add (f := v) (g := w)
  simp only [flip_obj_map] at h
  simp [pairingPrecomp, h, Preadditive.add_comp]

/-- The map `v ↦ (v ⊗ 1) ≫ φ` sends `0` to `0`. -/
theorem pairingPrecomp_zero [∀ L, (T.flip.obj L).Additive] {K : C₁} {L : C₂} {M : D}
    (φ : (T.obj K).obj L ⟶ M) (Z : C₁) :
    T.pairingPrecomp φ Z 0 = 0 := by
  simpa using T.pairingPrecomp_sub φ (0 : Z ⟶ K) 0

/-- The map determined by the pairing `-φ` is the negative of the map determined by `φ`. -/
theorem pairingPrecomp_neg_pairing {K : C₁} {L : C₂} {M : D} (φ : (T.obj K).obj L ⟶ M) (Z : C₁) :
    T.pairingPrecomp (-φ) Z = fun v => -T.pairingPrecomp φ Z v := by
  funext v
  simp [pairingPrecomp]

/-- A pairing is perfect at `Z` exactly when its negative is. -/
theorem bijective_pairingPrecomp_neg_iff {K : C₁} {L : C₂} {M : D} (φ : (T.obj K).obj L ⟶ M)
    (Z : C₁) :
    Function.Bijective (T.pairingPrecomp (-φ) Z) ↔ Function.Bijective (T.pairingPrecomp φ Z) := by
  rw [pairingPrecomp_neg_pairing]
  exact ⟨fun h => (Function.Bijective.of_comp_iff' (Equiv.neg _).bijective _).1 h,
    fun h => (Equiv.neg _).bijective.comp h⟩

variable {T}

/-- **The five lemma for pairings.** Let `K₀ ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ K₄` and
`L₄ ⟶ L₃ ⟶ L₂ ⟶ L₁ ⟶ L₀` be sequences, the first exact at `K₂` and `K₃` for `Hom(Z, -)` with
`K₀ ⟶ K₁ ⟶ K₂` zero, the second exact at `L₁` and `L₂` for `Hom(Z ⊗ -, M)` with
`L₄ ⟶ L₃ ⟶ L₂` zero, and let `φᵢ : Kᵢ ⊗ Lᵢ ⟶ M` be pairings, consecutive ones compatible along
the maps of the two sequences. If the maps `v ↦ (v ⊗ 1) ≫ φᵢ` out of `Hom(Z, Kᵢ)` are bijective
for `i = 1, 3`, surjective for `i = 0` and injective for `i = 4`, then that for `i = 2` is
bijective. -/
theorem bijective_pairingPrecomp_of_five [∀ L, (T.flip.obj L).Additive]
    [∀ Z, (T.obj Z).PreservesZeroMorphisms]
    {K₀ K₁ K₂ K₃ K₄ : C₁} {L₀ L₁ L₂ L₃ L₄ : C₂} {M : D}
    {e₀ : K₀ ⟶ K₁} {e₁ : K₁ ⟶ K₂} {e₂ : K₂ ⟶ K₃} {e₃ : K₃ ⟶ K₄}
    {e₀' : L₁ ⟶ L₀} {e₁' : L₂ ⟶ L₁} {e₂' : L₃ ⟶ L₂} {e₃' : L₄ ⟶ L₃}
    {φ₀ : (T.obj K₀).obj L₀ ⟶ M} {φ₁ : (T.obj K₁).obj L₁ ⟶ M} {φ₂ : (T.obj K₂).obj L₂ ⟶ M}
    {φ₃ : (T.obj K₃).obj L₃ ⟶ M} {φ₄ : (T.obj K₄).obj L₄ ⟶ M}
    (c₀ : T.PairingCompatible φ₀ φ₁ e₀ e₀') (c₁ : T.PairingCompatible φ₁ φ₂ e₁ e₁')
    (c₂ : T.PairingCompatible φ₂ φ₃ e₂ e₂') (c₃ : T.PairingCompatible φ₃ φ₄ e₃ e₃')
    (h₀₁ : e₀ ≫ e₁ = 0) (h₃₂' : e₃' ≫ e₂' = 0) (Z : C₁)
    (hK₂ : ∀ v : Z ⟶ K₂, v ≫ e₂ = 0 → ∃ u, v = u ≫ e₁)
    (hK₃ : ∀ v : Z ⟶ K₃, v ≫ e₃ = 0 → ∃ u, v = u ≫ e₂)
    (hL₁ : ∀ g : (T.obj Z).obj L₁ ⟶ M, (T.obj Z).map e₁' ≫ g = 0 →
      ∃ h, g = (T.obj Z).map e₀' ≫ h)
    (hL₂ : ∀ g : (T.obj Z).obj L₂ ⟶ M, (T.obj Z).map e₂' ≫ g = 0 →
      ∃ h, g = (T.obj Z).map e₁' ≫ h)
    (s₀ : Function.Surjective (T.pairingPrecomp φ₀ Z))
    (b₁ : Function.Bijective (T.pairingPrecomp φ₁ Z))
    (b₃ : Function.Bijective (T.pairingPrecomp φ₃ Z))
    (i₄ : Function.Injective (T.pairingPrecomp φ₄ Z)) :
    Function.Bijective (T.pairingPrecomp φ₂ Z) := by
  have inj0 : ∀ x : Z ⟶ K₂, T.pairingPrecomp φ₂ Z x = 0 → x = 0 := by
    intro x hx
    have h3 : x ≫ e₂ = 0 := b₃.1 (by
      rw [c₂.pairingPrecomp_comp, hx, comp_zero, T.pairingPrecomp_zero])
    obtain ⟨y, rfl⟩ := hK₂ x h3
    have h1 : (T.obj Z).map e₁' ≫ T.pairingPrecomp φ₁ Z y = 0 := by
      rw [← c₁.pairingPrecomp_comp, hx]
    obtain ⟨z, hz⟩ := hL₁ _ h1
    obtain ⟨w, rfl⟩ := s₀ z
    have hw : w ≫ e₀ = y := b₁.1 (by rw [c₀.pairingPrecomp_comp, hz])
    rw [← hw, Category.assoc, h₀₁, comp_zero]
  refine ⟨fun x x' hxx' => ?_, fun b => ?_⟩
  · have := inj0 (x - x') (by rw [T.pairingPrecomp_sub, hxx', sub_self])
    exact sub_eq_zero.1 this
  · obtain ⟨a, ha⟩ := b₃.2 ((T.obj Z).map e₂' ≫ b)
    have h4 : a ≫ e₃ = 0 := i₄ (by
      rw [c₃.pairingPrecomp_comp, ha, ← Category.assoc, ← Functor.map_comp, h₃₂',
        Functor.map_zero, zero_comp, T.pairingPrecomp_zero])
    obtain ⟨a₂, rfl⟩ := hK₃ a h4
    have h2 : (T.obj Z).map e₂' ≫ (b - T.pairingPrecomp φ₂ Z a₂) = 0 := by
      rw [Preadditive.comp_sub, ← c₂.pairingPrecomp_comp, ha, sub_self]
    obtain ⟨c, hc⟩ := hL₂ _ h2
    obtain ⟨d, rfl⟩ := b₁.2 c
    refine ⟨a₂ + d ≫ e₁, ?_⟩
    rw [T.pairingPrecomp_add, c₁.pairingPrecomp_comp, ← hc]
    abel

end Five

section Shift

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] (T : C₁ ⥤ C₂ ⥤ D) [T.CommShift₂Int]

/-- **The shift of a pairing**: for `φ : K ⊗ L ⟶ M` and `n + m = 0`, the pairing
`K[n] ⊗ L[m] ⟶ (K[n] ⊗ L)[m] ⟶ ((K ⊗ L)[n])[m] = K ⊗ L ⟶ M`, commuting the shift out of the
second variable first and then out of the first. -/
noncomputable def shiftedPairing {K : C₁} {L : C₂} {M : D} (φ : (T.obj K).obj L ⟶ M)
    (n m : ℤ) (h : n + m = 0) : (T.obj (K⟦n⟧)).obj (L⟦m⟧) ⟶ M :=
  ((T.obj (K⟦n⟧)).commShiftIso m).hom.app L ≫
    (((T.flip.obj L).commShiftIso n).hom.app K)⟦m⟧' ≫
      (shiftFunctorCompIsoId D n m h).hom.app ((T.obj K).obj L) ≫ φ

/-- The identification `Z ⊗ L[m] ≅ (Z ⊗ L)[m] ≅ Z[m] ⊗ L`. -/
noncomputable def shiftRightIsoShiftLeft (Z : C₁) (L : C₂) (m : ℤ) :
    (T.obj Z).obj (L⟦m⟧) ≅ (T.obj (Z⟦m⟧)).obj L :=
  ((T.obj Z).commShiftIso m).app L ≪≫ ((T.flip.obj L).commShiftIso m).symm.app Z

/-- The shifted pairing at `Z` is the pairing at `Z[m]`, read through `Z ⊗ L[m] ≅ Z[m] ⊗ L` and
`Hom(Z, K[n]) ≅ Hom(Z[m], K)`. -/
theorem pairingPrecomp_shiftedPairing {K : C₁} {L : C₂} {M : D} (φ : (T.obj K).obj L ⟶ M)
    (n m : ℤ) (h : n + m = 0) {Z : C₁} (v : Z ⟶ K⟦n⟧) :
    T.pairingPrecomp (T.shiftedPairing φ n m h) Z v =
      (T.shiftRightIsoShiftLeft Z L m).hom ≫
        T.pairingPrecomp φ (Z⟦m⟧) (v⟦m⟧' ≫ (shiftFunctorCompIsoId C₁ n m h).hom.app K) := by
  have hG : (T.map ((shiftFunctorCompIsoId C₁ n m h).hom.app K)).app L =
      ((T.flip.obj L).commShiftIso m).hom.app (K⟦n⟧) ≫
        (((T.flip.obj L).commShiftIso n).hom.app K)⟦m⟧' ≫
        (shiftFunctorCompIsoId D n m h).hom.app ((T.obj K).obj L) :=
    (T.flip.obj L).map_shiftFunctorCompIsoId_hom_app K n m h
  have hN : (T.map (v⟦m⟧')).app L ≫ ((T.flip.obj L).commShiftIso m).hom.app (K⟦n⟧) =
      ((T.flip.obj L).commShiftIso m).hom.app Z ≫ ((T.map v).app L)⟦m⟧' :=
    ((T.flip.obj L).commShiftIso m).hom.naturality v
  have hτ : ((T.obj Z).commShiftIso m).hom.app L ≫ ((T.map v).app L)⟦m⟧' =
      (T.map v).app (L⟦m⟧) ≫ ((T.obj (K⟦n⟧)).commShiftIso m).hom.app L :=
    NatTrans.shift_app_comm (T.map v) m L
  simp only [pairingPrecomp, shiftedPairing, shiftRightIsoShiftLeft, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [hG]
  simp only [Functor.comp_obj, Functor.flip_obj_obj] at hN ⊢
  simp only [Category.assoc, reassoc_of% hN, Iso.inv_hom_id_app_assoc, ← reassoc_of% hτ]

/-- **The shift of a pairing is perfect at `Z` exactly when the pairing is perfect at `Z[m]`.** -/
theorem bijective_pairingPrecomp_shiftedPairing_iff {K : C₁} {L : C₂} {M : D}
    (φ : (T.obj K).obj L ⟶ M) (n m : ℤ) (h : n + m = 0) (Z : C₁) :
    Function.Bijective (T.pairingPrecomp (T.shiftedPairing φ n m h) Z) ↔
      Function.Bijective (T.pairingPrecomp φ (Z⟦m⟧)) := by
  have h₁ : Function.Bijective (fun w : Z⟦m⟧ ⟶ (K⟦n⟧)⟦m⟧ =>
      w ≫ (shiftFunctorCompIsoId C₁ n m h).hom.app K) :=
    (Iso.homToEquiv ((shiftFunctorCompIsoId C₁ n m h).app K)).bijective
  have hk : Function.Bijective
      (fun v : Z ⟶ K⟦n⟧ => v⟦m⟧' ≫ (shiftFunctorCompIsoId C₁ n m h).hom.app K) :=
    h₁.comp ⟨(shiftFunctor C₁ m).map_injective, (shiftFunctor C₁ m).map_surjective⟩
  have hf : Function.Bijective
      (fun g : (T.obj (Z⟦m⟧)).obj L ⟶ M => (T.shiftRightIsoShiftLeft Z L m).hom ≫ g) :=
    (Iso.homFromEquiv (T.shiftRightIsoShiftLeft Z L m).symm).bijective
  have e : T.pairingPrecomp (T.shiftedPairing φ n m h) Z =
      (fun g => (T.shiftRightIsoShiftLeft Z L m).hom ≫ g) ∘ T.pairingPrecomp φ (Z⟦m⟧) ∘
        (fun v : Z ⟶ K⟦n⟧ => v⟦m⟧' ≫ (shiftFunctorCompIsoId C₁ n m h).hom.app K) :=
    funext fun v => T.pairingPrecomp_shiftedPairing φ n m h v
  rw [e, Function.Bijective.of_comp_iff' hf, Function.Bijective.of_comp_iff _ hk]

end Shift

section Triangles

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [∀ n : ℤ, (shiftFunctor C₂ n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C₁] [Pretriangulated C₂] [Pretriangulated D]
  {T : C₁ ⥤ C₂ ⥤ D} [T.CommShift₂Int] [∀ Z, (T.obj Z).Additive] [∀ Z, (T.obj Z).IsTriangulated]
  [∀ L, (T.flip.obj L).Additive]

/-- **The five lemma for pairings along two distinguished triangles** ([Stacks, Tag 014A], as
used in the proof of [Stacks, Tag 0G8K]). Let `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` and
`L₃ ⟶ L₂ ⟶ L₁ ⟶ L₃[1]` be distinguished triangles and `φᵢ : Kᵢ ⊗ Lᵢ ⟶ M` pairings compatible
along the maps of the triangles, the connecting maps being paired through pairings
`φ₀ : K₃[-1] ⊗ L₃[1] ⟶ M` and `φ₄ : K₁[1] ⊗ L₁[-1] ⟶ M`. If `φ₀`, `φ₁`, `φ₃` and `φ₄` are
perfect at every `Z`, i.e. the maps `v ↦ (v ⊗ 1) ≫ φᵢ` are bijective, then so is `φ₂`. -/
theorem bijective_pairingPrecomp_of_triangles' (S : Triangle C₁) (hS : S ∈ distTriang C₁)
    (S' : Triangle C₂) (hS' : S' ∈ distTriang C₂) {M : D}
    {φ₀ : (T.obj (S.obj₃⟦(-1 : ℤ)⟧)).obj (S'.obj₁⟦(1 : ℤ)⟧) ⟶ M}
    {φ₁ : (T.obj S.obj₁).obj S'.obj₃ ⟶ M} {φ₂ : (T.obj S.obj₂).obj S'.obj₂ ⟶ M}
    {φ₃ : (T.obj S.obj₃).obj S'.obj₁ ⟶ M}
    {φ₄ : (T.obj (S.obj₁⟦(1 : ℤ)⟧)).obj (S'.obj₃⟦(-1 : ℤ)⟧) ⟶ M}
    (c₀ : T.PairingCompatible φ₀ φ₁ S.invRotate.mor₁ S'.mor₃)
    (c₁ : T.PairingCompatible φ₁ φ₂ S.mor₁ S'.mor₂)
    (c₂ : T.PairingCompatible φ₂ φ₃ S.mor₂ S'.mor₁)
    (c₃ : T.PairingCompatible φ₃ φ₄ S.mor₃ S'.invRotate.mor₁)
    (b₀ : ∀ Z, Function.Bijective (T.pairingPrecomp φ₀ Z))
    (b₁ : ∀ Z, Function.Bijective (T.pairingPrecomp φ₁ Z))
    (b₃ : ∀ Z, Function.Bijective (T.pairingPrecomp φ₃ Z))
    (b₄ : ∀ Z, Function.Bijective (T.pairingPrecomp φ₄ Z)) (Z : C₁) :
    Function.Bijective (T.pairingPrecomp φ₂ Z) := by
  have hS'Z := (T.obj Z).map_distinguished S' hS'
  refine bijective_pairingPrecomp_of_five c₀ c₁ c₂ c₃
    (comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ hS))
    (comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ hS')) Z
    (fun v hv => Triangle.coyoneda_exact₂ S hS v hv)
    (fun v hv => Triangle.coyoneda_exact₃ S hS v hv) (fun g hg => ?_)
    (fun g hg => Triangle.yoneda_exact₂ _ hS'Z g hg) (b₀ Z).2 (b₁ Z) (b₃ Z) (b₄ Z).1
  obtain ⟨h, hh⟩ := Triangle.yoneda_exact₃ _ hS'Z g hg
  exact ⟨_, hh.trans (Category.assoc _ _ _)⟩

/-- **The five lemma for pairings along two distinguished triangles**, with the connecting maps
paired through the shifts of the outer pairings (`CategoryTheory.Functor.shiftedPairing`): if
`φ₁` and `φ₃` are perfect at every `Z`, then so is `φ₂`. -/
theorem bijective_pairingPrecomp_of_triangles (S : Triangle C₁) (hS : S ∈ distTriang C₁)
    (S' : Triangle C₂) (hS' : S' ∈ distTriang C₂) {M : D}
    {φ₁ : (T.obj S.obj₁).obj S'.obj₃ ⟶ M} {φ₂ : (T.obj S.obj₂).obj S'.obj₂ ⟶ M}
    {φ₃ : (T.obj S.obj₃).obj S'.obj₁ ⟶ M}
    (c₀ : T.PairingCompatible (T.shiftedPairing φ₃ (-1) 1 (by omega)) φ₁ S.invRotate.mor₁
      S'.mor₃)
    (c₁ : T.PairingCompatible φ₁ φ₂ S.mor₁ S'.mor₂)
    (c₂ : T.PairingCompatible φ₂ φ₃ S.mor₂ S'.mor₁)
    (c₃ : T.PairingCompatible φ₃ (T.shiftedPairing φ₁ 1 (-1) (by omega)) S.mor₃
      S'.invRotate.mor₁)
    (b₁ : ∀ Z, Function.Bijective (T.pairingPrecomp φ₁ Z))
    (b₃ : ∀ Z, Function.Bijective (T.pairingPrecomp φ₃ Z)) (Z : C₁) :
    Function.Bijective (T.pairingPrecomp φ₂ Z) :=
  bijective_pairingPrecomp_of_triangles' S hS S' hS' c₀ c₁ c₂ c₃
    (fun Z => (T.bijective_pairingPrecomp_shiftedPairing_iff φ₃ (-1) 1 (by omega) Z).2 (b₃ _))
    b₁ b₃ (fun Z => (T.bijective_pairingPrecomp_shiftedPairing_iff φ₁ 1 (-1) (by omega) Z).2
      (b₁ _)) Z

end Triangles

end CategoryTheory.Functor

namespace Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction

open CategoryTheory.Functor

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C} (DY : TensorHomAdjunction T H)

/-- **The shift of a perfect pairing is perfect.** -/
theorem isIso_homEquiv_symm_shiftedPairing [T.CommShift₂Int] {K L M : C}
    (φ : (T.obj K).obj L ⟶ M) (hφ : IsIso ((DY.homEquiv K L M).symm φ)) (n m : ℤ)
    (h : n + m = 0) :
    IsIso ((DY.homEquiv (K⟦n⟧) (L⟦m⟧) M).symm (T.shiftedPairing φ n m h)) :=
  (DY.isIso_homEquiv_symm_iff _).2 fun Z =>
    (T.bijective_pairingPrecomp_shiftedPairing_iff φ n m h Z).2
      ((DY.isIso_homEquiv_symm_iff φ).1 hφ _)

/-- **The five lemma for perfect pairings along two distinguished triangles**
([Stacks, Tag 014A], as used in the proof of [Stacks, Tag 0G8K]): if the pairings of the outer
vertices of `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` with those of `L₃ ⟶ L₂ ⟶ L₁ ⟶ L₃[1]` are perfect and the
pairings are compatible along all maps of the two triangles, then the pairing of the middle
vertices is perfect. -/
theorem isIso_homEquiv_symm_of_triangles [T.CommShift₂Int] [∀ Z, (T.obj Z).Additive]
    [∀ Z, (T.obj Z).IsTriangulated] [∀ L, (T.flip.obj L).Additive]
    (S : Triangle C) (hS : S ∈ distTriang C) (S' : Triangle C) (hS' : S' ∈ distTriang C) {M : C}
    {φ₁ : (T.obj S.obj₁).obj S'.obj₃ ⟶ M} {φ₂ : (T.obj S.obj₂).obj S'.obj₂ ⟶ M}
    {φ₃ : (T.obj S.obj₃).obj S'.obj₁ ⟶ M}
    (c₀ : T.PairingCompatible (T.shiftedPairing φ₃ (-1) 1 (by omega)) φ₁ S.invRotate.mor₁
      S'.mor₃)
    (c₁ : T.PairingCompatible φ₁ φ₂ S.mor₁ S'.mor₂)
    (c₂ : T.PairingCompatible φ₂ φ₃ S.mor₂ S'.mor₁)
    (c₃ : T.PairingCompatible φ₃ (T.shiftedPairing φ₁ 1 (-1) (by omega)) S.mor₃
      S'.invRotate.mor₁)
    (h₁ : IsIso ((DY.homEquiv _ _ M).symm φ₁)) (h₃ : IsIso ((DY.homEquiv _ _ M).symm φ₃)) :
    IsIso ((DY.homEquiv _ _ M).symm φ₂) :=
  (DY.isIso_homEquiv_symm_iff _).2
    (bijective_pairingPrecomp_of_triangles S hS S' hS' c₀ c₁ c₂ c₃
      ((DY.isIso_homEquiv_symm_iff φ₁).1 h₁) ((DY.isIso_homEquiv_symm_iff φ₃).1 h₃))

end Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction
