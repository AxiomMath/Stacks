module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.ToTensorShiftedPairing
public import StacksFrontier.Algebra.Homology.TruncatedTotalProductConnecting

/-!
# The pairings of the stupid truncations along the connecting maps, in the derived category

Let `Z` be a ringed space, `K`, `L`, `M` cochain complexes of `𝒪_Z`-modules and
`g : Tot(K ⊗ L) ⟶ M` a morphism of complexes, `M` vanishing in degrees `> n`. The products
`γ_p : Tot(σ^{≤p}K ⊗ σ^{≥q}L) ⟶ M` (`p + q = n`) and `Tot(K^p[-p] ⊗ L^q[-q]) ⟶ M` of
`StacksDraft.StupidTruncation.truncMul` and `StacksDraft.StupidTruncation.gradedMul` give pairings
`Q(σ^{≤p}K) ⊗^L Q(σ^{≥q}L) ⟶ QM` and `Q(K^p[-p]) ⊗^L Q(L^q[-q]) ⟶ QM` through the canonical map
to the total tensor complex. This file proves that these pairings are compatible along the
connecting maps of the distinguished triangles

`Q(K^p[-p]) ⟶ Q(σ^{≤p}K) ⟶ Q(σ^{≤p'}K) ⟶` and `Q(σ^{≥q+1}L) ⟶ Q(σ^{≥q}L) ⟶ Q(L^q[-q]) ⟶`

(`p = p' + 1`), the pairings at the shifted vertices being the shifts of the given ones
(`CategoryTheory.Functor.shiftedPairing`), the second one with a sign.

## Main results

* `StacksDraft.StupidTruncation.pairingCompatible_connectingLE`: the pairings are compatible along
  the connecting map of the first triangle and the inverse rotation of the second, the pairing at
  the shifted vertices being the shift of the pairing of the graded pieces.
* `StacksDraft.StupidTruncation.pairingCompatible_connectingGE`: the pairings are compatible along
  the inverse rotation of the first triangle and the connecting map of the second, the pairing at
  the shifted vertices being minus the shift of the pairing of the truncations.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace HomologicalComplex ComplexShape
open scoped Stacks.StandardDerivedModel
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.DerivedPullbackTensor (tensorComplexBifunctorOn shiftedPairing_toTensor_comp)

universe u

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasShift C ℤ] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive] (G : C ⥤ D) [G.CommShift ℤ] [G.Additive]

omit [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive] in
/-- **An additive functor commuting with the shifts carries the first morphism of the inverse
rotation of a triangle to that of the image triangle**, read on the connecting morphism
`δ : X ⟶ Y[1]`: minus the shift of `Gδ` followed by `(GY)[1][-1] ≅ GY` is, through
`G(X[-1]) ≅ (GX)[-1]`, the image of minus the shift of `δ` followed by `Y[1][-1] ≅ Y`. -/
theorem neg_shift_comp_unitIso_inv_eq_map {X Y : C} (δ : X ⟶ Y⟦(1 : ℤ)⟧) :
    -((G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app Y)⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId D (1 : ℤ) (-1) (by omega)).hom.app (G.obj Y)) =
      (G.commShiftIso (-1 : ℤ)).inv.app X ≫
        G.map (-(δ⟦(-1 : ℤ)⟧' ≫ (shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)).hom.app Y)) := by
  rw [← cancel_epi ((G.commShiftIso (-1 : ℤ)).hom.app X), Iso.hom_inv_id_app_assoc]
  have e₁ := G.map_shiftFunctorCompIsoId_hom_app Y (1 : ℤ) (-1) (by omega)
  have e₂ := (G.commShiftIso (-1 : ℤ)).hom.naturality δ
  simp only [comp_obj, comp_map] at e₂
  simp only [Functor.map_neg, Functor.map_comp, Preadditive.comp_neg, e₁, reassoc_of% e₂,
    Category.assoc]

/-- To prove `φ = T(1 ⊗ (e⁻¹ ≫ u)) ≫ ψ` for an isomorphism `e`, it suffices to prove
`T(1 ⊗ e) ≫ φ = T(1 ⊗ u) ≫ ψ`. -/
theorem eq_map_inv_comp_comp_of {C₁ C₂ D' : Type*} [Category* C₁] [Category* C₂] [Category* D']
    (T : C₁ ⥤ C₂ ⥤ D') {X : C₁} {Y Y' Y'' : C₂} (e : Y ≅ Y') (u : Y ⟶ Y'') {W : D'}
    {φ : (T.obj X).obj Y' ⟶ W} {ψ : (T.obj X).obj Y'' ⟶ W}
    (h : (T.obj X).map e.hom ≫ φ = (T.obj X).map u ≫ ψ) :
    φ = (T.obj X).map (e.inv ≫ u) ≫ ψ := by
  rw [Functor.map_comp, Category.assoc, ← h, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    Functor.map_id, Category.id_comp]

section Abstract

variable {C' D' : Type*} [Category* C'] [Category* D'] [HasShift C' ℤ] [HasShift D' ℤ]
  [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] (T : C' ⥤ C' ⥤ D') [T.CommShift₂Int]

/-- **Compatibility along a connecting morphism, from its shape on representatives.** Let
`β₁ : X₁ ⊗ Y ⟶ N` and `β₃ : X₃ ⊗ Y₁ ⟶ N` be pairings, `d ≫ a : X₃ ⟶ X₁' ⟶ X₁[1]` and
`b' ≫ ε : Y[-1] ⟶ Y' ⟶ Y₁` morphisms with `b' ≫ b = 1`. Suppose that, through `t`, the shift of
`β₁` precomposed with `a ⊗ b` is a map `s`, and that through `t₀` the pairings
`(d ⊗ 1) ≫ t` and `(1 ⊗ ε) ≫ β₃` are maps `x` and `y` with `x ≫ s = y`. Then `β₃` and the shift
of `β₁` are compatible along `d ≫ a` and `b' ≫ ε`. -/
theorem pairingCompatible_shiftedPairing_of_comp {X₁ X₁' X₃ Y Y' Y₁ : C'} {N W W₀ : D'}
    (β₁ : (T.obj X₁).obj Y ⟶ N) (β₃ : (T.obj X₃).obj Y₁ ⟶ N) (d : X₃ ⟶ X₁')
    (a : X₁' ⟶ X₁⟦(1 : ℤ)⟧) (b : Y' ⟶ Y⟦(-1 : ℤ)⟧) (b' : Y⟦(-1 : ℤ)⟧ ⟶ Y') (ε : Y' ⟶ Y₁)
    (hb : b' ≫ b = 𝟙 _) (t : (T.obj X₁').obj Y' ⟶ W) (t₀ : (T.obj X₃).obj Y' ⟶ W₀) (s : W ⟶ N)
    (x : W₀ ⟶ W) (y : W₀ ⟶ N)
    (E : (T.map a).app Y' ≫ (T.obj (X₁⟦(1 : ℤ)⟧)).map b ≫ T.shiftedPairing β₁ 1 (-1) (by omega) =
      t ≫ s)
    (N₁ : (T.map d).app Y' ≫ t = t₀ ≫ x) (N₂ : (T.obj X₃).map ε ≫ β₃ = t₀ ≫ y)
    (H : x ≫ s = y) :
    T.PairingCompatible β₃ (T.shiftedPairing β₁ 1 (-1) (by omega)) (d ≫ a) (b' ≫ ε) := by
  have ha : (T.map a).app (Y⟦(-1 : ℤ)⟧) =
      (T.obj X₁').map b' ≫ (T.map a).app Y' ≫ (T.obj (X₁⟦(1 : ℤ)⟧)).map b := by
    rw [NatTrans.naturality_assoc, ← Functor.map_comp, hb, Functor.map_id, Category.comp_id]
  unfold PairingCompatible
  rw [Functor.map_comp, NatTrans.comp_app, Category.assoc, ha, Category.assoc, Category.assoc, E,
    ← NatTrans.naturality_assoc, reassoc_of% N₁, Functor.map_comp, Category.assoc, N₂, H]

/-- **Compatibility along an inverse rotation, from its shape on representatives.** Let
`β₁ : X₁ ⊗ Y ⟶ N` and `β₃ : X₃ ⊗ Y₃ ⟶ N` be pairings, `c' ≫ e₁ : X₃[-1] ⟶ P ⟶ X₁` and
`d' ≫ a' : Y ⟶ Y₃' ⟶ Y₃[1]` morphisms with `c' ≫ c = 1`. Suppose that, through `t₂`, the shift of
`β₃` precomposed with `c ⊗ a'` is a map `s`, and that through `t₁` the pairings `(e₁ ⊗ 1) ≫ β₁`
and `(1 ⊗ d') ≫ t₂` are maps `x` and `y` with `x = -(y ≫ s)`. Then minus the shift of `β₃` and
`β₁` are compatible along `c' ≫ e₁` and `d' ≫ a'`. -/
theorem pairingCompatible_neg_shiftedPairing_of_comp {X₁ X₃ P Y Y₃ Y₃' : C'} {N W₁ W₂ : D'}
    (β₁ : (T.obj X₁).obj Y ⟶ N) (β₃ : (T.obj X₃).obj Y₃ ⟶ N) (c : P ⟶ X₃⟦(-1 : ℤ)⟧)
    (c' : X₃⟦(-1 : ℤ)⟧ ⟶ P) (e₁ : P ⟶ X₁) (d' : Y ⟶ Y₃') (a' : Y₃' ⟶ Y₃⟦(1 : ℤ)⟧)
    (hc : c' ≫ c = 𝟙 _) (t₁ : (T.obj P).obj Y ⟶ W₁) (t₂ : (T.obj P).obj Y₃' ⟶ W₂) (s : W₂ ⟶ N)
    (x : W₁ ⟶ N) (y : W₁ ⟶ W₂)
    (E : (T.map c).app Y₃' ≫ (T.obj (X₃⟦(-1 : ℤ)⟧)).map a' ≫
      T.shiftedPairing β₃ (-1) 1 (by omega) = t₂ ≫ s)
    (N₁ : (T.map e₁).app Y ≫ β₁ = t₁ ≫ x) (N₂ : (T.obj P).map d' ≫ t₂ = t₁ ≫ y)
    (H : x = -(y ≫ s)) :
    T.PairingCompatible (-T.shiftedPairing β₃ (-1) 1 (by omega)) β₁ (c' ≫ e₁) (d' ≫ a') := by
  have hE : (T.obj (X₃⟦(-1 : ℤ)⟧)).map a' ≫ T.shiftedPairing β₃ (-1) 1 (by omega) =
      (T.map c').app Y₃' ≫ t₂ ≫ s := by
    rw [← E, ← NatTrans.comp_app_assoc, ← Functor.map_comp, hc, Functor.map_id, NatTrans.id_app,
      Category.id_comp]
  unfold PairingCompatible
  rw [Functor.map_comp, NatTrans.comp_app, Category.assoc, N₁, H, Functor.map_comp,
    Category.assoc]
  simp only [Preadditive.comp_neg, neg_inj]
  rw [hE, NatTrans.naturality_assoc, reassoc_of% N₂]

end Abstract

end CategoryTheory.Functor

namespace StacksDraft.StupidTruncation

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {K L M : CochainComplex (ModulesOn Z) ℤ}
  (g : ((tensorComplexBifunctorOn Z).obj K).obj L ⟶ M) {n : ℤ}
  (hM : ∀ k, n < k → IsZero (M.X k))

include hM in
/-- The compatibility `pairingCompatible_connectingLE`, along the explicit morphisms of
complexes. -/
theorem pairingCompatible_connectingLE_aux (p' q : ℤ) (hpq : p' + 1 + q = n) :
    letI := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
    (derivedTensorProductFunctor Z.sheaf).PairingCompatible
      ((canonicalDerivedTensorProduct Z.sheaf).toTensor (K.stupidTrunc (embeddingUpIntLE p'))
          (L.stupidTrunc (embeddingUpIntGE (q + 1))) ≫
        DerivedCategory.Q.map (truncMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Z.sheaf) g hM p' (q + 1) (by omega)))
      ((derivedTensorProductFunctor Z.sheaf).shiftedPairing
        ((canonicalDerivedTensorProduct Z.sheaf).toTensor
            ((single _ (up ℤ) (p' + 1)).obj (K.X (p' + 1))) ((single _ (up ℤ) q).obj (L.X q)) ≫
          DerivedCategory.Q.map (gradedMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            Z.sheaf) g hM (p' + 1) q hpq)) 1 (-1) (by omega))
      (DerivedCategory.Q.map (stupidTruncLEδ K p') ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single _ (up ℤ) (p' + 1)).obj (K.X (p' + 1))))
      ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).inv.app ((single _ (up ℤ) q).obj (L.X q)) ≫
        DerivedCategory.Q.map (stupidTruncGEδShift L q)) := by
  let := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
  have h₁ := (canonicalDerivedTensorProduct Z.sheaf).toTensor_naturality (stupidTruncLEδ K p')
    (𝟙 (((single _ (up ℤ) q).obj (L.X q))⟦(-1 : ℤ)⟧))
  have h₂ := (canonicalDerivedTensorProduct Z.sheaf).toTensor_naturality
    (𝟙 (K.stupidTrunc (embeddingUpIntLE p'))) (stupidTruncGEδShift L q)
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h₁ h₂
  refine Functor.pairingCompatible_shiftedPairing_of_comp _ _ _ _ _ _ _ _
    (Iso.inv_hom_id_app _ _) _ _ _ _ _ (shiftedPairing_toTensor_comp Z _ 1 (-1) (by omega)) h₁
    (by rw [reassoc_of% h₂]; exact Category.assoc _ _ _) ?_
  exact Q_map_comp_connectingLE _ g hM p' q hpq

include hM in
/-- **The pairings of the stupid truncations are compatible along the connecting map of
`Q(K^p[-p]) ⟶ Q(σ^{≤p}K) ⟶ Q(σ^{≤p'}K) ⟶` and the inverse rotation of
`Q(σ^{≥q+1}L) ⟶ Q(σ^{≥q}L) ⟶ Q(L^q[-q]) ⟶`** (`p = p' + 1`, `p + q = n`), the pairing at the
shifted vertices being the shift of the pairing of the graded pieces. -/
theorem pairingCompatible_connectingLE (p' q : ℤ) (hpq : p' + 1 + q = n) :
    letI := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
    (derivedTensorProductFunctor Z.sheaf).PairingCompatible
      ((canonicalDerivedTensorProduct Z.sheaf).toTensor (K.stupidTrunc (embeddingUpIntLE p'))
          (L.stupidTrunc (embeddingUpIntGE (q + 1))) ≫
        DerivedCategory.Q.map (truncMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Z.sheaf) g hM p' (q + 1) (by omega)))
      ((derivedTensorProductFunctor Z.sheaf).shiftedPairing
        ((canonicalDerivedTensorProduct Z.sheaf).toTensor
            ((single _ (up ℤ) (p' + 1)).obj (K.X (p' + 1))) ((single _ (up ℤ) q).obj (L.X q)) ≫
          DerivedCategory.Q.map (gradedMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            Z.sheaf) g hM (p' + 1) q hpq)) 1 (-1) (by omega))
      (stupidTruncLESplitTriangleQ K (p' + 1) p' rfl).mor₃
      (stupidTruncGESplitTriangleQ L q).invRotate.mor₁ := by
  have hδ : (stupidTruncLESplitTriangleQ K (p' + 1) p' rfl).mor₃ =
      DerivedCategory.Q.map (stupidTruncLEδ K p') ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app _ := rfl
  have hε : (stupidTruncGESplitTriangleQ L q).invRotate.mor₁ =
      (DerivedCategory.Q.commShiftIso (-1 : ℤ)).inv.app _ ≫
        DerivedCategory.Q.map (stupidTruncGEδShift L q) :=
    Functor.neg_shift_comp_unitIso_inv_eq_map DerivedCategory.Q (stupidTruncGEδ L q)
  rw [hδ, hε]
  exact pairingCompatible_connectingLE_aux Z g hM p' q hpq

include hM in
/-- The compatibility `pairingCompatible_connectingGE`, along the explicit morphisms of
complexes. -/
theorem pairingCompatible_connectingGE_aux (p' q : ℤ) (hpq : p' + 1 + q = n) :
    letI := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
    (derivedTensorProductFunctor Z.sheaf).PairingCompatible
      (-(derivedTensorProductFunctor Z.sheaf).shiftedPairing
        ((canonicalDerivedTensorProduct Z.sheaf).toTensor (K.stupidTrunc (embeddingUpIntLE p'))
            (L.stupidTrunc (embeddingUpIntGE (q + 1))) ≫
          DerivedCategory.Q.map (truncMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            Z.sheaf) g hM p' (q + 1) (by omega))) (-1) 1 (by omega))
      ((canonicalDerivedTensorProduct Z.sheaf).toTensor
          ((single _ (up ℤ) (p' + 1)).obj (K.X (p' + 1))) ((single _ (up ℤ) q).obj (L.X q)) ≫
        DerivedCategory.Q.map (gradedMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Z.sheaf) g hM (p' + 1) q hpq))
      ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).inv.app (K.stupidTrunc (embeddingUpIntLE p')) ≫
        DerivedCategory.Q.map (stupidTruncLEδShift K p'))
      (DerivedCategory.Q.map (stupidTruncGEδ L q) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          (L.stupidTrunc (embeddingUpIntGE (q + 1)))) := by
  let := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
  have h₁ := (canonicalDerivedTensorProduct Z.sheaf).toTensor_naturality (stupidTruncLEδShift K p')
    (𝟙 ((single _ (up ℤ) q).obj (L.X q)))
  have h₂ := (canonicalDerivedTensorProduct Z.sheaf).toTensor_naturality
    (𝟙 ((K.stupidTrunc (embeddingUpIntLE p'))⟦(-1 : ℤ)⟧)) (stupidTruncGEδ L q)
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h₁ h₂
  refine Functor.pairingCompatible_neg_shiftedPairing_of_comp _ _ _ _ _ _ _ _
    (Iso.inv_hom_id_app _ _) _ _ _ _ _ (shiftedPairing_toTensor_comp Z _ (-1) 1 (by omega))
    (by rw [reassoc_of% h₁]; exact Category.assoc _ _ _) h₂ ?_
  exact Q_map_comp_connectingGE _ g hM p' q hpq

include hM in
/-- **The pairings of the stupid truncations are compatible along the inverse rotation of
`Q(K^p[-p]) ⟶ Q(σ^{≤p}K) ⟶ Q(σ^{≤p'}K) ⟶` and the connecting map of
`Q(σ^{≥q+1}L) ⟶ Q(σ^{≥q}L) ⟶ Q(L^q[-q]) ⟶`** (`p = p' + 1`, `p + q = n`), the pairing at the
shifted vertices being minus the shift of the pairing of the truncations. -/
theorem pairingCompatible_connectingGE (p' q : ℤ) (hpq : p' + 1 + q = n) :
    letI := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
    (derivedTensorProductFunctor Z.sheaf).PairingCompatible
      (-(derivedTensorProductFunctor Z.sheaf).shiftedPairing
        ((canonicalDerivedTensorProduct Z.sheaf).toTensor (K.stupidTrunc (embeddingUpIntLE p'))
            (L.stupidTrunc (embeddingUpIntGE (q + 1))) ≫
          DerivedCategory.Q.map (truncMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            Z.sheaf) g hM p' (q + 1) (by omega))) (-1) 1 (by omega))
      ((canonicalDerivedTensorProduct Z.sheaf).toTensor
          ((single _ (up ℤ) (p' + 1)).obj (K.X (p' + 1))) ((single _ (up ℤ) q).obj (L.X q)) ≫
        DerivedCategory.Q.map (gradedMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Z.sheaf) g hM (p' + 1) q hpq))
      (stupidTruncLESplitTriangleQ K (p' + 1) p' rfl).invRotate.mor₁
      (stupidTruncGESplitTriangleQ L q).mor₃ := by
  have hδ : (stupidTruncGESplitTriangleQ L q).mor₃ =
      DerivedCategory.Q.map (stupidTruncGEδ L q) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app _ := rfl
  have hε : (stupidTruncLESplitTriangleQ K (p' + 1) p' rfl).invRotate.mor₁ =
      (DerivedCategory.Q.commShiftIso (-1 : ℤ)).inv.app _ ≫
        DerivedCategory.Q.map (stupidTruncLEδShift K p') :=
    Functor.neg_shift_comp_unitIso_inv_eq_map DerivedCategory.Q (stupidTruncLEδ K p')
  rw [hδ, hε]
  exact pairingCompatible_connectingGE_aux Z g hM p' q hpq

end StacksDraft.StupidTruncation
