module

public import StacksFrontier.Algebra.Homology.MapBifunctorShiftedPairing
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Shifts of pairings through a lax comparison

Let `G₁`, `G₂`, `G` be additive functors and `λ_{X,Y} : F'(G₁X, G₂Y) ⟶ G F(X, Y)` a family of
maps between two bifunctors. For a pairing `h : Tot(F(K, L)) ⟶ W` of cochain complexes, a map
`Tot(F'(G₁K, G₂L)) ⟶ GW` is *given by `λ` on the summands* when on `F'(G₁K^i, G₂L^j)` it is `λ`
followed by `G` of `h` on the summand `F(K^i, L^j)`; the naive cup product along a morphism of
ringed spaces followed by the direct image of `h` is of this kind. Since the functors `G₁`, `G₂`,
`G` commute with the shifts of complexes by identities in each degree, such maps commute with
the shift of pairings by `(a, b)` (`CategoryTheory.Functor.shiftedPairing`) and with the shift of
the second variable and of the target. This file also records elementary identities between
composites used to read these compatibilities in the derived category.

## Main results

* `CochainComplex.mapBifunctorMap_commShiftIso_shiftedPairing_eq_of_lax`
* `CochainComplex.mapBifunctorMap_commShiftIso_rightShift_eq_of_lax`
* `CategoryTheory.Functor.pairingCompatible_inv_of_eq`,
  `CategoryTheory.Functor.pairingCompatible_id_inv_of_eq`

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- An additive functor commutes with signs: `ℓ ≫ G(ε • x) = ε • (ℓ ≫ G x)`. -/
theorem CategoryTheory.Functor.comp_map_units_smul {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (G : C ⥤ D) [G.Additive] {W : D} {Y Z : C}
    (ℓ : W ⟶ G.obj Y) (ε : ℤˣ) (x : Y ⟶ Z) : ℓ ≫ G.map (ε • x) = ε • (ℓ ≫ G.map x) := by
  rw [Units.smul_def, Units.smul_def, G.map_zsmul, Preadditive.comp_zsmul]

namespace CochainComplex

variable {C₁ C₂ D C₁' C₂' D' : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Category* C₁'] [Category* C₂'] [Category* D']
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [Preadditive C₁'] [Preadditive C₂'] [Preadditive D']
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]
  (F' : C₁' ⥤ C₂' ⥤ D') [F'.Additive] [∀ (X₁ : C₁'), (F'.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁' ℤ) (K₂ : CochainComplex C₂' ℤ), HasMapBifunctor K₁ K₂ F']
  (G₁ : C₁ ⥤ C₁') (G₂ : C₂ ⥤ C₂') (G : D ⥤ D') [G₁.Additive] [G₂.Additive] [G.Additive]
  (lax : ∀ (X₁ : C₁) (X₂ : C₂), (F'.obj (G₁.obj X₁)).obj (G₂.obj X₂) ⟶ G.obj ((F.obj X₁).obj X₂))

/-- **Shifting a pairing commutes with a lax comparison.** If `g` and `g'` are given by `λ` on the
summands, with `h` and with its shift by `(a, b)` respectively, then `g'` is the shift of `g`
read through `G₁(K[a]) = (G₁K)[a]` and `G₂(L[b]) = (G₂L)[b]`. -/
theorem mapBifunctorMap_commShiftIso_shiftedPairing_eq_of_lax {K : CochainComplex C₁ ℤ}
    {L : CochainComplex C₂ ℤ} {W : CochainComplex D ℤ} (h : mapBifunctor K L F ⟶ W) (a b : ℤ)
    (hab : a + b = 0)
    (g : mapBifunctor ((G₁.mapHomologicalComplex _).obj K) ((G₂.mapHomologicalComplex _).obj L) F' ⟶
      (G.mapHomologicalComplex _).obj W)
    (g' : mapBifunctor ((G₁.mapHomologicalComplex _).obj (K⟦a⟧))
      ((G₂.mapHomologicalComplex _).obj (L⟦b⟧)) F' ⟶ (G.mapHomologicalComplex _).obj W)
    (hg : ∀ (i j k : ℤ) (hk : i + j = k), ιMapBifunctor _ _ F' i j k hk ≫ g.f k =
      lax (K.X i) (L.X j) ≫ G.map (ιMapBifunctor K L F i j k hk ≫ h.f k))
    (hg' : ∀ (i j k : ℤ) (hk : i + j = k), ιMapBifunctor _ _ F' i j k hk ≫ g'.f k =
      lax ((K⟦a⟧).X i) ((L⟦b⟧).X j) ≫
        G.map (ιMapBifunctor (K⟦a⟧) (L⟦b⟧) F i j k hk ≫
          (F.map₂CochainComplex.shiftedPairing h a b hab).f k)) :
    HomologicalComplex.mapBifunctorMap (((G₁.mapHomologicalComplex _).commShiftIso a).hom.app K)
        (((G₂.mapHomologicalComplex _).commShiftIso b).hom.app L) F' (ComplexShape.up ℤ) ≫
      F'.map₂CochainComplex.shiftedPairing g a b hab = g' := by
  ext k : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hk
  have hk' : i + j = k := hk
  refine (congrArg (_ ≫ ·) (HomologicalComplex.comp_f _ _ _)).trans ?_
  refine (HomologicalComplex.ι_mapBifunctorMap_assoc _ _ _ _ _ _ _ _ _).trans ?_
  have key := Functor.ι_shiftedPairing_map₂CochainComplex_f F' g a b hab i j k hk' (i + a) (j + b)
    rfl rfl
  refine (congrArg (_ ≫ _ ≫ ·) key).trans ?_
  refine Eq.trans ?_ (hg' i j k hk').symm
  have key' := Functor.ι_shiftedPairing_map₂CochainComplex_f F h a b hab i j k hk' (i + a) (j + b)
    rfl rfl
  refine Eq.trans ?_ (congrArg (_ ≫ G.map ·) key').symm
  rw [Functor.comp_map_units_smul, Linear.comp_units_smul, Linear.comp_units_smul]
  congr 1
  simp [CochainComplex.shiftFunctorObjXIso, hg]

/-- **Shifting the second variable and the target of a pairing commutes with a lax comparison.**
If `g` and `g'` are given by `λ` on the summands, with `h` and with its shift in the second
variable and the target respectively, then `g'` is the commutation of the total complex with the
shift followed by the shift of `g`, read through `G₂(L[m]) = (G₂L)[m]` and `G(W[m]) = (GW)[m]`. -/
theorem mapBifunctorMap_commShiftIso_rightShift_eq_of_lax {K : CochainComplex C₁ ℤ}
    {L : CochainComplex C₂ ℤ} {W : CochainComplex D ℤ} (h : mapBifunctor K L F ⟶ W) (m : ℤ)
    (g : mapBifunctor ((G₁.mapHomologicalComplex _).obj K) ((G₂.mapHomologicalComplex _).obj L) F' ⟶
      (G.mapHomologicalComplex _).obj W)
    (g' : mapBifunctor ((G₁.mapHomologicalComplex _).obj K)
      ((G₂.mapHomologicalComplex _).obj (L⟦m⟧)) F' ⟶ (G.mapHomologicalComplex _).obj (W⟦m⟧))
    (hg : ∀ (i j k : ℤ) (hk : i + j = k), ιMapBifunctor _ _ F' i j k hk ≫ g.f k =
      lax (K.X i) (L.X j) ≫ G.map (ιMapBifunctor K L F i j k hk ≫ h.f k))
    (hg' : ∀ (i j k : ℤ) (hk : i + j = k), ιMapBifunctor _ _ F' i j k hk ≫ g'.f k =
      lax (K.X i) ((L⟦m⟧).X j) ≫
        G.map (ιMapBifunctor K (L⟦m⟧) F i j k hk ≫
          (((F.map₂CochainComplex.obj K).commShiftIso m).hom.app L ≫ h⟦m⟧').f k)) :
    HomologicalComplex.mapBifunctorMap (𝟙 _)
        (((G₂.mapHomologicalComplex _).commShiftIso m).hom.app L) F' (ComplexShape.up ℤ) ≫
      ((F'.map₂CochainComplex.obj ((G₁.mapHomologicalComplex _).obj K)).commShiftIso m).hom.app
        ((G₂.mapHomologicalComplex _).obj L) ≫ g⟦m⟧' =
      g' ≫ ((G.mapHomologicalComplex _).commShiftIso m).hom.app W := by
  ext k : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hk
  have hk' : i + j = k := hk
  refine (congrArg (_ ≫ ·) ((HomologicalComplex.comp_f _ _ _).trans
    (congrArg (_ ≫ ·) (HomologicalComplex.comp_f _ _ _)))).trans ?_
  refine (HomologicalComplex.ι_mapBifunctorMap_assoc _ _ _ _ _ _ _ _ _).trans ?_
  have key := ι_mapBifunctorShift₂Iso_hom_f ((G₁.mapHomologicalComplex _).obj K)
    ((G₂.mapHomologicalComplex _).obj L) F' m i j k hk' (j + m) (k + m) rfl rfl
  refine (congrArg (_ ≫ _ ≫ ·) ((reassoc_of% key) _)).trans ?_
  refine Eq.trans ?_ ((congrArg (_ ≫ ·) (HomologicalComplex.comp_f _ _ _)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (hg' i j k hk')))).symm
  have key' := ι_mapBifunctorShift₂Iso_hom_f K L F m i j k hk' (j + m) (k + m) rfl rfl
  refine Eq.trans ?_ (congrArg (fun x => (_ ≫ G.map x) ≫ _)
    ((congrArg (_ ≫ ·) (HomologicalComplex.comp_f _ _ _)).trans ((reassoc_of% key') _))).symm
  simp only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj, shiftFunctor_obj_X',
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp,
    Linear.units_smul_comp, Functor.map_units_smul, Functor.map_comp, Linear.comp_units_smul]
  refine (Linear.units_smul_comp _ _ _).trans (congrArg ((i * m).negOnePow • ·) ?_)
  exact (hg i (j + m) (k + m) (by omega)).trans (congrArg (_ ≫ ·) (G.map_comp _ _))

end CochainComplex

namespace CategoryTheory.Functor

section Composites

variable {C₀ C₁ C₂ C : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C]

/-- The shift of a pairing followed by a map is the shifted pairing followed by that map. -/
theorem shiftedPairing_comp [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] (T : C₁ ⥤ C₂ ⥤ C) [T.CommShift₂Int] {K : C₁} {L : C₂}
    {M M' : C} (φ : (T.obj K).obj L ⟶ M) (t : M ⟶ M') (n m : ℤ) (h : n + m = 0) :
    T.shiftedPairing (φ ≫ t) n m h = T.shiftedPairing φ n m h ≫ t := by
  simp only [shiftedPairing, Category.assoc]

/-- Precomposing a pairing with `(u₁ ≫ v₁) ⊗ (u₂ ≫ v₂)` in two stages. -/
theorem map_comp_app_map_comp_eq (T : C₁ ⥤ C₂ ⥤ C) {K' K₀ K : C₁} {L' L₀ L : C₂} {M : C}
    (u₁ : K' ⟶ K₀) (v₁ : K₀ ⟶ K) (u₂ : L' ⟶ L₀) (v₂ : L₀ ⟶ L) (φ : (T.obj K).obj L ⟶ M)
    (ψ : (T.obj K₀).obj L₀ ⟶ M) (χ : (T.obj K').obj L' ⟶ M)
    (h₁ : (T.map v₁).app L₀ ≫ (T.obj K).map v₂ ≫ φ = ψ)
    (h₂ : (T.map u₁).app L' ≫ (T.obj K₀).map u₂ ≫ ψ = χ) :
    (T.map (u₁ ≫ v₁)).app L' ≫ (T.obj K).map (u₂ ≫ v₂) ≫ φ = χ := by
  rw [← h₂, ← h₁, Functor.map_comp, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    Category.assoc, NatTrans.naturality_assoc]

/-- A pairing precomposed with `Q(1) ⊗ 1` is unchanged. -/
theorem map_map_id_app_comp (T : C₁ ⥤ C₂ ⥤ C) (Q : C₀ ⥤ C₁) (K : C₀) {L : C₂} {Z : C}
    (f : (T.obj (Q.obj K)).obj L ⟶ Z) : (T.map (Q.map (𝟙 K))).app L ≫ f = f := by
  simp

/-- `t ≫ F(u) ≫ F(v) = t ≫ F(w)` when `u ≫ v = w`. -/
theorem comp_map_comp_map_eq (F : C₁ ⥤ C) {Z : C} {X Y W : C₁} (t : Z ⟶ F.obj X) (u : X ⟶ Y)
    (v : Y ⟶ W) (w : X ⟶ W) (h : u ≫ v = w) : t ≫ F.map u ≫ F.map v = t ≫ F.map w := by
  rw [← h, F.map_comp]

/-- Precomposing with `F(u ≫ v)` a commutation with the shift followed by a shifted composite, in
two stages. -/
theorem map_comp_comp_shift_map_comp_eq [HasShift C ℤ] (F : C₁ ⥤ C) {L' L₀ L : C₁} {X' X Y : C}
    (m : ℤ) (u : L' ⟶ L₀) (v : L₀ ⟶ L) (cs : F.obj L ⟶ X'⟦m⟧) (t : X' ⟶ X) (q : X ⟶ Y)
    (s : F.obj L₀ ⟶ X⟦m⟧) (χ : F.obj L' ⟶ Y⟦m⟧) (h₁ : F.map v ≫ cs ≫ t⟦m⟧' = s)
    (h₂ : F.map u ≫ s ≫ q⟦m⟧' = χ) : F.map (u ≫ v) ≫ cs ≫ (t ≫ q)⟦m⟧' = χ := by
  rw [← h₂, ← h₁, F.map_comp, Functor.map_comp]
  simp only [Category.assoc]

/-- A composite `x ≫ (t₁ ≫ F(w₂) ≫ c₁) ≫ r` computed from three commuting squares. -/
theorem comp_comp_map_comp_eq (F : C₁ ⥤ C) {A₀ A₁ E₁ E₂ : C} {B₀ B₁ B₂ B₃ : C₁} (x : A₀ ⟶ A₁)
    (t₁ : A₁ ⟶ F.obj B₁) (t₂ : A₀ ⟶ F.obj B₀) (w₁ : B₀ ⟶ B₁) (w₂ : B₁ ⟶ B₂)
    (c₁ : F.obj B₂ ⟶ E₁) (r : E₁ ⟶ E₂) (gs : B₂ ⟶ B₃) (c₂ : F.obj B₃ ⟶ E₂) (w : B₀ ⟶ B₃)
    (n₁ : x ≫ t₁ = t₂ ≫ F.map w₁) (n₂ : c₁ ≫ r = F.map gs ≫ c₂) (n₃ : w₁ ≫ w₂ ≫ gs = w) :
    x ≫ (t₁ ≫ F.map w₂ ≫ c₁) ≫ r = t₂ ≫ F.map w ≫ c₂ := by
  rw [← n₃, F.map_comp, F.map_comp]
  simp only [Category.assoc]
  rw [n₂, reassoc_of% n₁]

end Composites

section Compatible

variable {C₁ C₂ C : Type*} [Category* C₁] [Category* C₂] [Category* C] {T : C₁ ⥤ C₂ ⥤ C}

/-- Pairings related by precomposition with `x ⊗ y` are compatible along `x⁻¹` and `y`. -/
theorem pairingCompatible_inv_of_eq {K K' : C₁} {L L' : C₂} {M : C} (x : K' ⟶ K) [IsIso x]
    (y : L' ⟶ L) {φ : (T.obj K).obj L ⟶ M} {φ' : (T.obj K').obj L' ⟶ M}
    (h : (T.map x).app L' ≫ (T.obj K).map y ≫ φ = φ') :
    T.PairingCompatible φ φ' (CategoryTheory.inv x) y := by
  unfold PairingCompatible
  rw [← h, ← NatTrans.comp_app_assoc, ← Functor.map_comp, IsIso.inv_hom_id, Functor.map_id,
    NatTrans.id_app, Category.id_comp]

/-- Pairings related by precomposition with `1 ⊗ y` are compatible along `1` and `y⁻¹`. -/
theorem pairingCompatible_id_inv_of_eq {K : C₁} {L L' : C₂} {M : C} (y : L ⟶ L') [IsIso y]
    {φ : (T.obj K).obj L ⟶ M} {φ' : (T.obj K).obj L' ⟶ M} (h : (T.obj K).map y ≫ φ' = φ) :
    T.PairingCompatible φ φ' (𝟙 K) (CategoryTheory.inv y) := by
  unfold PairingCompatible
  rw [← h, ← Functor.map_comp_assoc, IsIso.inv_hom_id]
  simp

end Compatible

end CategoryTheory.Functor
