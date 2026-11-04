module

public import StacksFrontier.Algebra.Homology.TruncatedTotalProduct
public import StacksFrontier.Algebra.Homology.StupidTruncationSplitTriangles
public import StacksFrontier.Algebra.Homology.MapBifunctorShiftedPairing

/-!
# Products on stupid truncations along the connecting maps

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor, `K`, `L`, `M` cochain complexes and
`g : Tot(F(K, L)) ⟶ M` a morphism of complexes, where `M` vanishes in degrees `> n`, and let
`γ_p : Tot(F(σ^{≤p}K, σ^{≥q}L)) ⟶ M` (`p + q = n`) and `Tot(F(K^p[-p], L^q[-q])) ⟶ M` be the
products of `StacksDraft.StupidTruncation.truncMul` and `StacksDraft.StupidTruncation.gradedMul`.

The short exact sequences `K^p[-p] ⟶ σ^{≤p}K ⟶ σ^{≤p'}K` (`p' + 1 = p`) and
`σ^{≥q+1}L ⟶ σ^{≥q}L ⟶ L^q[-q]` are degreewise split, with connecting maps of complexes
`δ : σ^{≤p'}K ⟶ K^p[-p][1]` and `δ' : L^q[-q] ⟶ σ^{≥q+1}L[1]` given by the differentials of `K`
and `L` (`CochainComplex.homOfDegreewiseSplit`). This file proves that the products are
compatible along these connecting maps up to homotopy, the shifts of the pairings being those of
`CategoryTheory.Functor.shiftedPairing` for the total complex: these are the remaining two of the
four compatibilities of the five lemma in the proof of [Stacks, Tag 0G8K]. The homotopies are
the restrictions of `g` itself, with signs; that they are homotopies is the Leibniz rule, i.e.
that `g` is a morphism of complexes.

## Main definitions

* `StacksDraft.StupidTruncation.stupidTruncLEδ`, `StacksDraft.StupidTruncation.stupidTruncGEδ`:
  the connecting maps, and `StacksDraft.StupidTruncation.stupidTruncLEδShift`,
  `StacksDraft.StupidTruncation.stupidTruncGEδShift` the maps deduced from them as in
  `CategoryTheory.Pretriangulated.Triangle.invRotate`.
* `StacksDraft.StupidTruncation.mapBifunctorShiftedPairing`: the shift of a pairing of total
  complexes.
* `StacksDraft.StupidTruncation.homotopyConnectingLE` and
  `StacksDraft.StupidTruncation.homotopyConnectingGE`: the two homotopies.

## Main results

* `StacksDraft.StupidTruncation.ι_truncMul_f`, `StacksDraft.StupidTruncation.ι_gradedMul_f`:
  the products on the summands.
* `StacksDraft.StupidTruncation.stupidTruncLEδ_f`, `StacksDraft.StupidTruncation.stupidTruncGEδ_f`:
  the connecting maps are the differentials.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape
open CochainComplex (shiftFunctorObjXIso)

namespace StacksDraft.StupidTruncation

section Differentials

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C] (K : CochainComplex C ℤ)

/-- In retained degrees the differential of `σ^{≤a}K` is that of `K`. -/
theorem stupidTruncLE_d_eq (a i j : ℤ) (hi : i ≤ a) (hj : j ≤ a) :
    (K.stupidTrunc (embeddingUpIntLE a)).d i j =
      (stupidTruncLEXIso K a i hi).hom ≫ K.d i j ≫ (stupidTruncLEXIso K a j hj).inv := by
  have h := (K.πStupidTrunc (embeddingUpIntLE a)).comm i j
  rw [πStupidTruncLE_f_of_le K a i hi, πStupidTruncLE_f_of_le K a j hj] at h
  rw [← h, Iso.hom_inv_id_assoc]

/-- In retained degrees the differential of `σ^{≥a}K` is that of `K`. -/
theorem stupidTruncGE_d_eq (a i j : ℤ) (hi : a ≤ i) (hj : a ≤ j) :
    (K.stupidTrunc (embeddingUpIntGE a)).d i j =
      (stupidTruncGEXIso K a i hi).hom ≫ K.d i j ≫ (stupidTruncGEXIso K a j hj).inv := by
  have h := (ιStupidTrunc K (embeddingUpIntGE a)).comm i j
  rw [ιStupidTruncGE_f K a i hi, ιStupidTruncGE_f K a j hj] at h
  rw [← cancel_mono (stupidTruncGEXIso K a j hj).hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, h]

end Differentials

section Connecting

/-- The inverse of a morphism which is the underlying morphism of an isomorphism `e` is the
inverse of `e`, whatever the proof that it is invertible. -/
theorem inv_eq_inv_of_eq_hom {C : Type*} [Category* C] {X Y : C} {f : X ⟶ Y} (hf : IsIso f)
    (e : X ≅ Y) (h : f = e.hom) : @inv _ _ _ _ f hf = e.inv := by
  subst h
  simp

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ)

/-- Away from degree `p` the retraction of the canonical splitting of
`σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p]` inverts the comparison of truncations. -/
theorem stupidTruncGESplitting_r_of_ne (p n : ℤ) (hn : n ≠ p) :
    (stupidTruncGESplitting K p n).r =
      @inv _ _ _ _ ((stupidTruncGEMapLE K (show p ≤ p + 1 by omega)).f n) (by
        by_cases hpn : p < n
        · rw [stupidTruncGEMapLE_f K _ n (by omega)]
          infer_instance
        · exact IsZero.isIso
            (CochainComplex.isZero_of_isStrictlyGE
              (K.stupidTrunc (embeddingUpIntGE (p + 1))) (p + 1) n (by omega))
            (CochainComplex.isZero_of_isStrictlyGE
              (K.stupidTrunc (embeddingUpIntGE p)) p n (by omega)) _) := by
  simp only [stupidTruncGESplitting, dif_neg hn, ShortComplex.Splitting.ofIsIsoOfIsZero]
  rfl

/-- **The connecting map `σ^{≤p'}K ⟶ Kᵖ[-p][1]` is the differential of `K`**, `p = p' + 1`: its
component in degree `p'` is `d^{p'} : K^{p'} ⟶ Kᵖ`. -/
theorem homOfDegreewiseSplit_stupidTruncLE_f_self (p' : ℤ) :
    (CochainComplex.homOfDegreewiseSplit (stupidTruncLEShortComplex K (p' + 1) p' rfl)
      (stupidTruncLESplitting K (p' + 1) p' rfl)).f p' =
      (stupidTruncLEXIso K p' p' le_rfl).hom ≫ K.d p' (p' + 1) ≫
        (singleObjXSelf (up ℤ) (p' + 1) (K.X (p' + 1))).inv := by
  rw [CochainComplex.homOfDegreewiseSplit_f]
  dsimp only [CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.HomComplex.Cocycle.mk]
  rw [CochainComplex.HomComplex.Cochain.mk_v]
  rw [stupidTruncLESplitting_s_of_ne K (p' + 1) p' rfl p' (by omega),
    stupidTruncLESplitting_r_self]
  have e₁ : (stupidTruncLEMapLE K (show p' ≤ p' + 1 by omega)).f p' =
      (stupidTruncLEXIso K (p' + 1) p' (by omega)).hom ≫ (stupidTruncLEXIso K p' p' le_rfl).inv :=
    stupidTruncLEMapLE_f K _ p' le_rfl
  have e₂ := stupidTruncLEι_f K (p' + 1)
  have e₃ := stupidTruncLE_d_eq K (p' + 1) p' (p' + 1) (by omega) le_rfl
  simp only [ShortComplex.map_X₂, eval_obj, stupidTruncLEShortComplex] at e₁ e₂ e₃ ⊢
  rw [inv_eq_inv_of_eq_hom _ (stupidTruncLEXIso K (p' + 1) p' (by omega) ≪≫
      (stupidTruncLEXIso K p' p' le_rfl).symm) (by rw [e₁]; rfl),
    inv_eq_inv_of_eq_hom _ (singleObjXSelf (up ℤ) (p' + 1) (K.X (p' + 1)) ≪≫
      (stupidTruncLEXIso K (p' + 1) (p' + 1) le_rfl).symm) (by rw [e₂]; rfl), e₃]
  simp

/-- **The connecting map `Lᵠ[-q] ⟶ σ^{≥q+1}L[1]` is the differential of `L`**: its component in
degree `q` is `d^q : Lᵠ ⟶ L^{q+1}`. -/
theorem homOfDegreewiseSplit_stupidTruncGE_f_self (q : ℤ) :
    (CochainComplex.homOfDegreewiseSplit (stupidTruncGEShortComplex K q)
      (stupidTruncGESplitting K q)).f q =
      (singleObjXSelf (up ℤ) q (K.X q)).hom ≫ K.d q (q + 1) ≫
        (stupidTruncGEXIso K (q + 1) (q + 1) le_rfl).inv := by
  rw [CochainComplex.homOfDegreewiseSplit_f]
  dsimp only [CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.HomComplex.Cocycle.mk]
  rw [CochainComplex.HomComplex.Cochain.mk_v]
  rw [stupidTruncGESplitting_s_self, stupidTruncGESplitting_r_of_ne K q (q + 1) (by omega)]
  have e₁ : (stupidTruncGEMapLE K (show q ≤ q + 1 by omega)).f (q + 1) =
      (stupidTruncGEXIso K (q + 1) (q + 1) le_rfl).hom ≫
        (stupidTruncGEXIso K q (q + 1) (by omega)).inv :=
    stupidTruncGEMapLE_f K _ (q + 1) le_rfl
  have e₂ := stupidTruncGEπ_f K q
  have e₃ := stupidTruncGE_d_eq K q q (q + 1) le_rfl (by omega)
  simp only [ShortComplex.map_X₂, eval_obj, stupidTruncGEShortComplex] at e₁ e₂ e₃ ⊢
  rw [inv_eq_inv_of_eq_hom _ (stupidTruncGEXIso K q q le_rfl ≪≫
      (singleObjXSelf (up ℤ) q (K.X q)).symm) (by rw [e₂]; rfl),
    inv_eq_inv_of_eq_hom _ (stupidTruncGEXIso K (q + 1) (q + 1) le_rfl ≪≫
      (stupidTruncGEXIso K q (q + 1) (by omega)).symm) (by rw [e₁]; rfl), e₃]
  simp

/-- **The connecting map `σ^{≤p'}K ⟶ K^{p'+1}[-p'-1][1]`** of the canonically split short exact
sequence `K^{p'+1}[-p'-1] ⟶ σ^{≤p'+1}K ⟶ σ^{≤p'}K`. -/
def stupidTruncLEδ (p' : ℤ) :
    K.stupidTrunc (embeddingUpIntLE p') ⟶
      ((single C (up ℤ) (p' + 1)).obj (K.X (p' + 1)))⟦(1 : ℤ)⟧ :=
  CochainComplex.homOfDegreewiseSplit (stupidTruncLEShortComplex K (p' + 1) p' rfl)
    (stupidTruncLESplitting K (p' + 1) p' rfl)

/-- The connecting map of `K^{p'+1}[-p'-1] ⟶ σ^{≤p'+1}K ⟶ σ^{≤p'}K` is the differential
`d^{p'} : K^{p'} ⟶ K^{p'+1}`, read in any degree `m = p'`. -/
theorem stupidTruncLEδ_f (p' m : ℤ) (hm : m = p') :
    (stupidTruncLEδ K p').f m = (stupidTruncLEXIso K p' m hm.le).hom ≫ K.d m (p' + 1) ≫
      (singleObjXIsoOfEq (up ℤ) (p' + 1) (K.X (p' + 1)) (m + 1) (by omega)).inv := by
  subst hm
  exact homOfDegreewiseSplit_stupidTruncLE_f_self K m

/-- **The connecting map `Lᵠ[-q] ⟶ σ^{≥q+1}L[1]`** of the canonically split short exact sequence
`σ^{≥q+1}L ⟶ σ^{≥q}L ⟶ Lᵠ[-q]`. -/
def stupidTruncGEδ (q : ℤ) :
    (single C (up ℤ) q).obj (K.X q) ⟶ (K.stupidTrunc (embeddingUpIntGE (q + 1)))⟦(1 : ℤ)⟧ :=
  CochainComplex.homOfDegreewiseSplit (stupidTruncGEShortComplex K q) (stupidTruncGESplitting K q)

/-- The connecting map of `σ^{≥q+1}L ⟶ σ^{≥q}L ⟶ Lᵠ[-q]` is the differential
`d^q : Lᵠ ⟶ L^{q+1}`, read in any degree `m = q`. -/
theorem stupidTruncGEδ_f (q m : ℤ) (hm : m = q) :
    (stupidTruncGEδ K q).f m = (singleObjXIsoOfEq (up ℤ) q (K.X q) m hm).hom ≫ K.d q (m + 1) ≫
      (stupidTruncGEXIso K (q + 1) (m + 1) (by omega)).inv := by
  subst hm
  exact homOfDegreewiseSplit_stupidTruncGE_f_self K m

/-- The identifications `(σ^{≥a}K)^i ≅ K^i` commute with the isomorphisms `X i ≅ X j` induced by
an equality `i = j`. -/
theorem stupidTruncGEXIso_inv_comp_XIsoOfEq_hom (a i j : ℤ) (h : i = j) (hi : a ≤ i) :
    (stupidTruncGEXIso K a i hi).inv ≫ ((K.stupidTrunc (embeddingUpIntGE a)).XIsoOfEq h).hom =
      (K.XIsoOfEq h).hom ≫ (stupidTruncGEXIso K a j (h ▸ hi)).inv := by
  subst h
  simp

/-- The identifications `X ≅ (X[-p])^i` for `i = p` commute with the isomorphisms `X i ≅ X j`
induced by an equality `i = j`. -/
theorem singleObjXIsoOfEq_inv_comp_XIsoOfEq_hom (p : ℤ) (X : C) (i j : ℤ) (h : i = j)
    (hi : i = p) :
    (singleObjXIsoOfEq (up ℤ) p X i hi).inv ≫ (((single C (up ℤ) p).obj X).XIsoOfEq h).hom =
      (singleObjXIsoOfEq (up ℤ) p X j (h ▸ hi)).inv := by
  subst h
  simp

/-- The map `Lᵠ[-q][-1] ⟶ σ^{≥q+1}L` deduced from the connecting map, as in
`CategoryTheory.Pretriangulated.Triangle.invRotate`: minus the shift of the connecting map
followed by `σ^{≥q+1}L[1][-1] ≅ σ^{≥q+1}L`. -/
def stupidTruncGEδShift (q : ℤ) :
    ((single C (up ℤ) q).obj (K.X q))⟦(-1 : ℤ)⟧ ⟶ K.stupidTrunc (embeddingUpIntGE (q + 1)) :=
  -((stupidTruncGEδ K q)⟦(-1 : ℤ)⟧') ≫
    (shiftFunctorCompIsoId (CochainComplex C ℤ) 1 (-1) (by omega)).hom.app _

/-- The map `Lᵠ[-q][-1] ⟶ σ^{≥q+1}L` is minus the differential `d^q`, in degree `q + 1`. -/
theorem stupidTruncGEδShift_f (q j : ℤ) (hj : j + (-1) = q) :
    (stupidTruncGEδShift K q).f j = -((singleObjXIsoOfEq (up ℤ) q (K.X q) (j + (-1)) hj).hom ≫
      K.d q j ≫ (stupidTruncGEXIso K (q + 1) j (by omega)).inv) := by
  rw [stupidTruncGEδShift, neg_f_apply, comp_f, CochainComplex.shiftFunctor_map_f',
    stupidTruncGEδ_f K q (j + (-1)) hj, CochainComplex.shiftFunctorCompIsoId_hom_app_f,
    Category.assoc, Category.assoc, stupidTruncGEXIso_inv_comp_XIsoOfEq_hom,
    d_comp_XIsoOfEq_hom_assoc]

/-- The map `σ^{≤p'}K[-1] ⟶ K^{p'+1}[-p'-1]` deduced from the connecting map, as in
`CategoryTheory.Pretriangulated.Triangle.invRotate`: minus the shift of the connecting map
followed by `K^{p'+1}[-p'-1][1][-1] ≅ K^{p'+1}[-p'-1]`. -/
def stupidTruncLEδShift (p' : ℤ) :
    (K.stupidTrunc (embeddingUpIntLE p'))⟦(-1 : ℤ)⟧ ⟶
      (single C (up ℤ) (p' + 1)).obj (K.X (p' + 1)) :=
  -((stupidTruncLEδ K p')⟦(-1 : ℤ)⟧') ≫
    (shiftFunctorCompIsoId (CochainComplex C ℤ) 1 (-1) (by omega)).hom.app _

/-- The map `σ^{≤p'}K[-1] ⟶ K^{p'+1}[-p'-1]` is minus the differential `d^{p'}`, in degree
`p' + 1`. -/
theorem stupidTruncLEδShift_f (p' i : ℤ) (hi : i = p' + 1) :
    (stupidTruncLEδShift K p').f i =
      -((shiftFunctorObjXIso (K.stupidTrunc (embeddingUpIntLE p')) (-1) i p' (by omega)).hom ≫
        (stupidTruncLEXIso K p' p' le_rfl).hom ≫ K.d p' (p' + 1) ≫
          (singleObjXIsoOfEq (up ℤ) (p' + 1) (K.X (p' + 1)) i hi).inv) := by
  subst hi
  rw [stupidTruncLEδShift, neg_f_apply, comp_f, CochainComplex.shiftFunctor_map_f',
    CochainComplex.shiftFunctorCompIsoId_hom_app_f]
  have e : ∀ (m : ℤ) (hm : m = p'), (stupidTruncLEδ K p').f m =
      ((K.stupidTrunc (embeddingUpIntLE p')).XIsoOfEq hm).hom ≫
        (stupidTruncLEXIso K p' p' le_rfl).hom ≫ K.d p' (p' + 1) ≫
          (singleObjXIsoOfEq (up ℤ) (p' + 1) (K.X (p' + 1)) (m + 1) (by omega)).inv := by
    rintro m rfl
    rw [stupidTruncLEδ_f K m m rfl, XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  rw [e (p' + 1 + (-1)) (by omega), Category.assoc, Category.assoc, Category.assoc,
    singleObjXIsoOfEq_inv_comp_XIsoOfEq_hom]
  rfl

end Connecting

section Summands

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroObject C₁] [HasZeroMorphisms C₂] [HasZeroObject C₂]
  [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  [∀ (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ), HasMapBifunctor K L F (up ℤ)]
  {K : CochainComplex C₁ ℤ} {L : CochainComplex C₂ ℤ} {M : CochainComplex D ℤ}
  (g : mapBifunctor K L F (up ℤ) ⟶ M) {n : ℤ} (hM : ∀ k, n < k → IsZero (M.X k))

/-- **The product `γ_p` on a summand**: on `F((σ^{≤p}K)^i, (σ^{≥q}L)^j)`, `i ≤ p ≤ … `, `q ≤ j`, it
is the identification with `F(K^i, L^j)` followed by `g`. -/
theorem ι_truncMul_f (p q : ℤ) (hpq : p + q = n) (i j k : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi : i ≤ p) (hj : q ≤ j) :
    ιMapBifunctor (K.stupidTrunc (embeddingUpIntLE p)) (L.stupidTrunc (embeddingUpIntGE q)) F
        (up ℤ) i j k h ≫ (truncMul F g hM p q hpq).f k =
      (F.map (stupidTruncLEXIso K p i hi).hom).app _ ≫
        (F.obj (K.X i)).map (stupidTruncGEXIso L q j hj).hom ≫
          ιMapBifunctor K L F (up ℤ) i j k h ≫ g.f k := by
  rw [truncMul, ι_truncLEDesc_f _ _ _ i j k h hi, comp_f, ι_mapBifunctorMap_assoc,
    ιStupidTruncGE_f L q j hj]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp]

/-- **The product of the graded pieces on its summand**: on `F(K^p, L^q)` it is `g`. -/
theorem ι_gradedMul_f (p q : ℤ) (hpq : p + q = n) (k : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p, q) = k) :
    ιMapBifunctor ((single C₁ (up ℤ) p).obj (K.X p)) ((single C₂ (up ℤ) q).obj (L.X q)) F
        (up ℤ) p q k h ≫ (gradedMul F g hM p q hpq).f k =
      (F.map (singleObjXSelf (up ℤ) p (K.X p)).hom).app _ ≫
        (F.obj (K.X p)).map (singleObjXSelf (up ℤ) q (L.X q)).hom ≫
          ιMapBifunctor K L F (up ℤ) p q k h ≫ g.f k := by
  rw [gradedMul, descOfSection_f, ι_mapBifunctorMapSection_assoc, comp_f, ι_mapBifunctorMap_assoc,
    ι_truncMul_f F g hM p q hpq p q k h le_rfl le_rfl, stupidTruncGEπSection_self,
    stupidTruncLEι_f]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc, HomologicalComplex.id_f]
  simp only [NatTrans.naturality_assoc]
  simp only [← NatTrans.comp_app_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Category.assoc,
    Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]

end Summands

section Homotopies

private theorem ε₁_up_int (i j : ℤ) : ComplexShape.ε₁ (up ℤ) (up ℤ) (up ℤ) (i, j) = 1 := rfl

private theorem ε₂_up_int (i j : ℤ) :
    ComplexShape.ε₂ (up ℤ) (up ℤ) (up ℤ) (i, j) = i.negOnePow := rfl

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Abelian C₁] [Abelian C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  [∀ (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ), HasMapBifunctor K L F (up ℤ)]
  {K : CochainComplex C₁ ℤ} {L : CochainComplex C₂ ℤ} {M : CochainComplex D ℤ}
  (g : mapBifunctor K L F (up ℤ) ⟶ M) {n : ℤ} (hM : ∀ k, n < k → IsZero (M.X k))

variable {F} in
/-- **The shift of a pairing of total complexes**, `Tot(F(K[a], L[b])) ⟶ M` for
`g : Tot(F(K, L)) ⟶ M` and `a + b = 0`: the shifted pairing
(`CategoryTheory.Functor.shiftedPairing`) for the bifunctor `F.map₂CochainComplex`, read as a
morphism out of the total complex. -/
def mapBifunctorShiftedPairing {K' : CochainComplex C₁ ℤ} {L' : CochainComplex C₂ ℤ}
    (φ : mapBifunctor K' L' F (up ℤ) ⟶ M) (a b : ℤ) (h : a + b = 0) :
    mapBifunctor (K'⟦a⟧) (L'⟦b⟧) F (up ℤ) ⟶ M :=
  F.map₂CochainComplex.shiftedPairing φ a b h

variable {F} in
/-- The shift of a pairing of total complexes on a summand: on `F(K[a]^i, L[b]^j)` it is
`(-1)^{ib}` times `φ` on `F(K^{i+a}, L^{j+b})`. -/
theorem ι_mapBifunctorShiftedPairing_f {K' : CochainComplex C₁ ℤ} {L' : CochainComplex C₂ ℤ}
    (φ : mapBifunctor K' L' F (up ℤ) ⟶ M) (a b : ℤ) (h : a + b = 0) (i j k : ℤ)
    (hk : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (i' j' : ℤ) (hi' : i' = i + a)
    (hj' : j' = j + b) :
    ιMapBifunctor (K'⟦a⟧) (L'⟦b⟧) F (up ℤ) i j k hk ≫
        (mapBifunctorShiftedPairing φ a b h).f k =
      (i * b).negOnePow • ((F.map (K'.shiftFunctorObjXIso a i i' hi').hom).app _ ≫
        (F.obj _).map (L'.shiftFunctorObjXIso b j j' hj').hom ≫
          ιMapBifunctor K' L' F (up ℤ) i' j' k
            (by change i + j = k at hk; change i' + j' = k; omega) ≫
            φ.f k) :=
  Functor.ι_shiftedPairing_map₂CochainComplex_f F φ a b h i j k hk i' j' hi' hj'

/-- The homotopy for the compatibility of the products along the connecting map of
`K^p[-p] ⟶ σ^{≤p}K ⟶ σ^{≤p'}K`: on the summand `F((σ^{≤p'}K)^i, (L^q[-q][-1])^{q+1})` of
`Tot(F(σ^{≤p'}K, L^q[-q][-1]))` it is `(-1)^i` times `g` on the summand `F(K^i, L^q)`. -/
def connectingLECochain (p' q : ℤ) :
    CochainComplex.HomComplex.Cochain
      (mapBifunctor (K.stupidTrunc (embeddingUpIntLE p'))
        (((single C₂ (up ℤ) q).obj (L.X q))⟦(-1 : ℤ)⟧) F (up ℤ)) M (-1) :=
  CochainComplex.HomComplex.Cochain.mk fun k k' hk => mapBifunctorDesc fun i j h =>
    if hi : i ≤ p' then
      if hj : j + (-1) = q then
        i.negOnePow • ((F.map (stupidTruncLEXIso K p' i hi).hom).app _ ≫
          (F.obj (K.X i)).map (singleObjXIsoOfEq (up ℤ) q (L.X q) (j + (-1)) hj).hom ≫
            ιMapBifunctor K L F (up ℤ) i q k' (by change i + j = k at h; change i + q = k'; omega) ≫
              g.f k')
      else 0
    else 0

/-- On the summand `F((σ^{≤p'}K)^i, (L^q[-q][-1])^j)` with `i ≤ p'` and `j - 1 = q`, the cochain
`connectingLECochain` is `(-1)^i` times `g` on the summand `F(K^i, L^q)`. -/
@[reassoc]
theorem ι_connectingLECochain_v (p' q i j k k' : ℤ) (hk : k + (-1) = k')
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi : i ≤ p') (hj : j + (-1) = q) :
    ιMapBifunctor _ _ F (up ℤ) i j k h ≫ (connectingLECochain F g p' q).v k k' hk =
      i.negOnePow • ((F.map (stupidTruncLEXIso K p' i hi).hom).app _ ≫
        (F.obj (K.X i)).map (singleObjXIsoOfEq (up ℤ) q (L.X q) (j + (-1)) hj).hom ≫
          ιMapBifunctor K L F (up ℤ) i q k' (by change i + j = k at h; change i + q = k'; omega) ≫
            g.f k') := by
  rw [connectingLECochain, CochainComplex.HomComplex.Cochain.mk_v, ι_mapBifunctorDesc, dif_pos hi,
    dif_pos hj]

/-- The cochain `connectingLECochain` vanishes on the summands `F((σ^{≤p'}K)^i, (L^q[-q][-1])^j)`
with `p' < i`. -/
theorem ι_connectingLECochain_v_eq_zero (p' q i j k k' : ℤ) (hk : k + (-1) = k')
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi : p' < i) :
    ιMapBifunctor _ _ F (up ℤ) i j k h ≫ (connectingLECochain F g p' q).v k k' hk = 0 := by
  rw [connectingLECochain, CochainComplex.HomComplex.Cochain.mk_v, ι_mapBifunctorDesc,
    dif_neg (by omega)]

/-- The first composite of `homotopyConnectingLE`, on a summand away from the top degree of
`σ^{≤p'}K`. -/
theorem ι_connectingLE_left_eq_zero (p' q : ℤ) (hpq : p' + 1 + q = n) (i j k : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi : i ≠ p') :
    ιMapBifunctor _ _ F (up ℤ) i j k h ≫
      (mapBifunctorMap (stupidTruncLEδ K p') (𝟙 (((single C₂ (up ℤ) q).obj (L.X q))⟦(-1 : ℤ)⟧))
          F (up ℤ) ≫
        mapBifunctorShiftedPairing (gradedMul F g hM (p' + 1) q hpq) 1 (-1) (by omega)).f k =
      0 := by
  have hk : i + j = k := h
  rw [comp_f, ι_mapBifunctorMap_assoc,
    ι_mapBifunctorShiftedPairing_f _ 1 (-1) _ i j k h (i + 1) (j + (-1)) rfl rfl]
  have hz : IsZero ((F.obj (((single C₁ (up ℤ) (p' + 1)).obj (K.X (p' + 1))).X (i + 1))).obj
      (((single C₂ (up ℤ) q).obj (L.X q)).X (j + (-1)))) :=
    Functor.map_isZero (F.flip.obj _) (isZero_single_obj_X (up ℤ) _ _ _ (by omega))
  rw [hz.eq_of_src (ιMapBifunctor _ _ F (up ℤ) (i + 1) (j + (-1)) k _ ≫ _) 0]
  simp

/-- The first composite of `homotopyConnectingLE`, on the summand in the top degree `p'` of
`σ^{≤p'}K`: it is `(-1)^{p'}` times `g` precomposed with `d^{p'} ⊗ 1`. -/
theorem ι_connectingLE_left_self (p' q : ℤ) (hpq : p' + 1 + q = n) (j k : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p', j) = k) (hj : j + (-1) = q) :
    ιMapBifunctor _ _ F (up ℤ) p' j k h ≫
      (mapBifunctorMap (stupidTruncLEδ K p') (𝟙 (((single C₂ (up ℤ) q).obj (L.X q))⟦(-1 : ℤ)⟧))
          F (up ℤ) ≫
        mapBifunctorShiftedPairing (gradedMul F g hM (p' + 1) q hpq) 1 (-1) (by omega)).f k =
      p'.negOnePow • ((F.map ((stupidTruncLEXIso K p' p' le_rfl).hom ≫ K.d p' (p' + 1))).app _ ≫
        (F.obj (K.X (p' + 1))).map (singleObjXIsoOfEq (up ℤ) q (L.X q) (j + (-1)) hj).hom ≫
          ιMapBifunctor K L F (up ℤ) (p' + 1) q k
            (by change p' + j = k at h; change p' + 1 + q = k; omega) ≫
            g.f k) := by
  have hk : p' + j = k := h
  rw [comp_f, ι_mapBifunctorMap_assoc,
    ι_mapBifunctorShiftedPairing_f _ 1 (-1) _ p' j k h (p' + 1) q rfl (by omega), ι_gradedMul_f,
    stupidTruncLEδ_f K p' p' rfl]
  simp only [id_f, CategoryTheory.Functor.map_id, Category.id_comp, Linear.comp_units_smul,
    mul_neg, mul_one, Int.negOnePow_neg]
  congr 1
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
    NatTrans.naturality_assoc]
  simp [singleObjXSelf, singleObjXIsoOfEq, CochainComplex.shiftFunctorObjXIso, XIsoOfEq,
    eqToHom_map, eqToHom_app]

/-- The second composite of `homotopyConnectingLE` on a summand: it is minus `g` precomposed with
`1 ⊗ d^q`. -/
theorem ι_connectingLE_right (p' q : ℤ) (hpq : p' + 1 + q = n) (i j k : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi : i ≤ p') (hj : j + (-1) = q) :
    ιMapBifunctor _ _ F (up ℤ) i j k h ≫
      (mapBifunctorMap (𝟙 (K.stupidTrunc (embeddingUpIntLE p'))) (stupidTruncGEδShift L q) F
          (up ℤ) ≫
        truncMul F g hM p' (q + 1) (by omega)).f k =
      -((F.map (stupidTruncLEXIso K p' i hi).hom).app _ ≫
        (F.obj (K.X i)).map ((singleObjXIsoOfEq (up ℤ) q (L.X q) (j + (-1)) hj).hom ≫ L.d q j) ≫
          ιMapBifunctor K L F (up ℤ) i j k h ≫ g.f k) := by
  rw [comp_f, ι_mapBifunctorMap_assoc, ι_truncMul_f F g hM p' (q + 1) _ i j k h hi (by omega),
    stupidTruncGEδShift_f L q j hj]
  simp only [id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    CategoryTheory.Functor.map_neg, Preadditive.neg_comp, CategoryTheory.Functor.map_comp,
    Category.assoc, NatTrans.naturality_assoc]
  congr 2
  simp only [← Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The differential of the total complex on a summand: `d₁ + d₂` with the signs of `up ℤ`. -/
private theorem ι_mapBifunctor_comp_d {K' : CochainComplex C₁ ℤ} {L' : CochainComplex C₂ ℤ}
    (i i' j j' k k' : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi : i + 1 = i')
    (hj : j + 1 = j') (hk : k + 1 = k') :
    ιMapBifunctor K' L' F (up ℤ) i j k h ≫ (mapBifunctor K' L' F (up ℤ)).d k k' =
      (F.map (K'.d i i')).app _ ≫ ιMapBifunctor K' L' F (up ℤ) i' j k'
          (by change i + j = k at h; change i' + j = k'; omega) +
        i.negOnePow • ((F.obj (K'.X i)).map (L'.d j j') ≫
          ιMapBifunctor K' L' F (up ℤ) i j' k'
            (by change i + j = k at h; change i + j' = k'; omega)) := by
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq _ _ F (up ℤ) (show (up ℤ).Rel i i' from hi) j k'
      (by change i + j = k at h; change i' + j = k'; omega),
    mapBifunctor.d₂_eq _ _ F (up ℤ) i (show (up ℤ).Rel j j' from hj) k'
      (by change i + j = k at h; change i + j' = k'; omega)]
  simp only [ε₁_up_int, ε₂_up_int, one_smul]

/-- The composite of the homotopy with the differential of `M`, on a summand. -/
theorem ι_connectingLECochain_v_d (p' q i j k : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi : i ≤ p') (hj : j + (-1) = q) :
    ιMapBifunctor _ _ F (up ℤ) i j k h ≫ (connectingLECochain F g p' q).v k (k - 1) (by omega) ≫
        M.d (k - 1) k =
      i.negOnePow • ((F.map ((stupidTruncLEXIso K p' i hi).hom ≫ K.d i (i + 1))).app _ ≫
        (F.obj (K.X (i + 1))).map (singleObjXIsoOfEq (up ℤ) q (L.X q) (j + (-1)) hj).hom ≫
          ιMapBifunctor K L F (up ℤ) (i + 1) q k
            (by change i + j = k at h; change i + 1 + q = k; omega) ≫ g.f k) +
        (F.map (stupidTruncLEXIso K p' i hi).hom).app _ ≫
          (F.obj (K.X i)).map ((singleObjXIsoOfEq (up ℤ) q (L.X q) (j + (-1)) hj).hom ≫ L.d q j) ≫
            ιMapBifunctor K L F (up ℤ) i j k h ≫ g.f k := by
  have hk : i + j = k := h
  rw [ι_connectingLECochain_v_assoc F g p' q i j k (k - 1) _ h hi hj, Linear.units_smul_comp]
  simp only [Category.assoc]
  rw [Hom.comm,
    reassoc_of% ι_mapBifunctor_comp_d F i (i + 1) q (q + 1) (k - 1) k _ rfl rfl (by omega)]
  obtain rfl : j = q + 1 := by omega
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, Preadditive.comp_add,
    Preadditive.add_comp, smul_add, smul_smul, Int.units_mul_self, one_smul, Category.assoc,
    CategoryTheory.Functor.map_comp, NatTrans.comp_app, NatTrans.naturality_assoc]

/-- The composite of the differential of the total complex with the homotopy, on a summand. -/
theorem ι_d_connectingLECochain_v (p' q i j k : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi : i ≤ p') (hj : j + (-1) = q) :
    ιMapBifunctor _ _ F (up ℤ) i j k h ≫
        (mapBifunctor (K.stupidTrunc (embeddingUpIntLE p'))
          (((single C₂ (up ℤ) q).obj (L.X q))⟦(-1 : ℤ)⟧) F (up ℤ)).d k (k + 1) ≫
          (connectingLECochain F g p' q).v (k + 1) k (by omega) =
      if hi' : i + 1 ≤ p' then
        (i + 1).negOnePow • ((F.map ((stupidTruncLEXIso K p' i hi).hom ≫ K.d i (i + 1))).app _ ≫
          (F.obj (K.X (i + 1))).map (singleObjXIsoOfEq (up ℤ) q (L.X q) (j + (-1)) hj).hom ≫
            ιMapBifunctor K L F (up ℤ) (i + 1) q k
              (by change i + j = k at h; change i + 1 + q = k; omega) ≫ g.f k)
      else 0 := by
  have hk : i + j = k := h
  rw [reassoc_of% ι_mapBifunctor_comp_d F i (i + 1) j (j + 1) k (k + 1) h rfl rfl rfl,
    Preadditive.add_comp]
  simp only [CochainComplex.shiftFunctor_obj_d', single_obj_d, smul_zero,
    CategoryTheory.Functor.map_zero, zero_comp, smul_zero, add_zero,
    Category.assoc]
  split_ifs with hi'
  · rw [ι_connectingLECochain_v F g p' q (i + 1) j (k + 1) k _ _ hi' hj,
      Linear.comp_units_smul, stupidTruncLE_d_eq K p' i (i + 1) hi hi']
    congr 1
    dsimp only [CochainComplex.shiftFunctor_obj_X', CochainComplex.shiftFunctor_obj_X]
    simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
      Iso.map_inv_hom_id_app_assoc]
  · rw [ι_connectingLECochain_v_eq_zero F g p' q (i + 1) j (k + 1) k _ _ (by omega), comp_zero]

/-- **The products are compatible along the connecting maps `σ^{≤p'}K ⟶ K^p[-p][1]` and
`L^q[-q][-1] ⟶ σ^{≥q+1}L`, up to homotopy** (`p = p' + 1`, `p + q = n`): on
`Tot(F(σ^{≤p'}K, L^q[-q][-1]))`, the connecting map of `K^p[-p] ⟶ σ^{≤p}K ⟶ σ^{≤p'}K` followed by
the shift of the product of the graded pieces is homotopic to the map deduced from the connecting
map of `σ^{≥q+1}L ⟶ σ^{≥q}L ⟶ L^q[-q]` followed by `γ_{p'}`. -/
def homotopyConnectingLE (p' q : ℤ) (hpq : p' + 1 + q = n) :
    Homotopy
      (mapBifunctorMap (stupidTruncLEδ K p') (𝟙 (((single C₂ (up ℤ) q).obj (L.X q))⟦(-1 : ℤ)⟧))
          F (up ℤ) ≫
        mapBifunctorShiftedPairing (gradedMul F g hM (p' + 1) q hpq) 1 (-1) (by omega))
      (mapBifunctorMap (𝟙 (K.stupidTrunc (embeddingUpIntLE p'))) (stupidTruncGEδShift L q) F
          (up ℤ) ≫
        truncMul F g hM p' (q + 1) (by omega)) :=
  (CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm ⟨connectingLECochain F g p' q, by
    refine CochainComplex.HomComplex.Cochain.ext₀ _ _ (fun k => ?_)
    rw [CochainComplex.HomComplex.Cochain.add_v, CochainComplex.HomComplex.Cochain.ofHom_v,
      CochainComplex.HomComplex.Cochain.ofHom_v,
      CochainComplex.HomComplex.δ_v (-1) 0 (by omega) _ k k (add_zero k) (k - 1) (k + 1)
        (by omega) rfl]
    ext i j h
    have hk : i + j = k := h
    by_cases hj : j + (-1) = q
    swap
    · exact (Functor.map_isZero _
        (isZero_single_obj_X (up ℤ) q (L.X q) (j + (-1)) hj)).eq_of_src _ _
    by_cases hi : i ≤ p'
    swap
    · exact (Functor.map_isZero (F.flip.obj _) (CochainComplex.isZero_of_isStrictlyLE
        (K.stupidTrunc (embeddingUpIntLE p')) p' i (by omega))).eq_of_src _ _
    simp only [Preadditive.comp_add, Int.negOnePow_zero, one_smul]
    rw [ι_connectingLECochain_v_d F g p' q i j k h hi hj,
      ι_d_connectingLECochain_v F g p' q i j k h hi hj,
      ι_connectingLE_right F g hM p' q hpq i j k h hi hj]
    by_cases hi' : i = p'
    · subst hi'
      rw [ι_connectingLE_left_self F g hM i q hpq j k h hj, dif_neg (by omega)]
      abel
    · rw [ι_connectingLE_left_eq_zero F g hM p' q hpq i j k h hi', dif_pos (by omega),
        Int.negOnePow_succ, Units.neg_smul]
      abel⟩

/-- The differential of a shifted complex, read through the identifications of terms. -/
theorem _root_.CochainComplex.shift_d_comp_shiftFunctorObjXIso_hom {C : Type*} [Category* C]
    [Preadditive C] (K : CochainComplex C ℤ) (a x y x₀ y₀ : ℤ) (hx : x₀ = x + a)
    (hy : y₀ = y + a) :
    (K⟦a⟧).d x y ≫ (K.shiftFunctorObjXIso a y y₀ hy).hom =
      a.negOnePow • ((K.shiftFunctorObjXIso a x x₀ hx).hom ≫ K.d x₀ y₀) := by
  subst hx hy
  simp [CochainComplex.shiftFunctor_obj_d']

/-- The homotopy for the compatibility of the products along the connecting map of
`σ^{≥q+1}L ⟶ σ^{≥q}L ⟶ L^q[-q]`: on the summand `F((σ^{≤p'}K[-1])^i, (L^q[-q])^q)` of
`Tot(F(σ^{≤p'}K[-1], L^q[-q]))` it is minus `g` on the summand `F(K^{i-1}, L^q)`. -/
def connectingGECochain (p' q : ℤ) :
    CochainComplex.HomComplex.Cochain
      (mapBifunctor ((K.stupidTrunc (embeddingUpIntLE p'))⟦(-1 : ℤ)⟧)
        ((single C₂ (up ℤ) q).obj (L.X q)) F (up ℤ)) M (-1) :=
  CochainComplex.HomComplex.Cochain.mk fun k k' hk => mapBifunctorDesc fun i j h =>
    if hi : i + (-1) ≤ p' then
      if hj : j = q then
        -((F.map ((shiftFunctorObjXIso (K.stupidTrunc (embeddingUpIntLE p')) (-1) i (i + (-1))
              rfl).hom ≫ (stupidTruncLEXIso K p' (i + (-1)) hi).hom)).app _ ≫
          (F.obj (K.X (i + (-1)))).map (singleObjXIsoOfEq (up ℤ) q (L.X q) j hj).hom ≫
            ιMapBifunctor K L F (up ℤ) (i + (-1)) q k'
              (by change i + j = k at h; change i + (-1) + q = k'; omega) ≫ g.f k')
      else 0
    else 0

/-- On the summand `F((σ^{≤p'}K[-1])^i, (L^q[-q])^j)` with `i - 1 ≤ p'` and `j = q`, the cochain
`connectingGECochain` is minus `g` on the summand `F(K^{i-1}, L^q)`. -/
@[reassoc]
theorem ι_connectingGECochain_v (p' q i j k k' i₀ : ℤ) (hk : k + (-1) = k')
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi₀ : i₀ = i + (-1)) (hi : i₀ ≤ p')
    (hj : j = q) :
    ιMapBifunctor _ _ F (up ℤ) i j k h ≫ (connectingGECochain F g p' q).v k k' hk =
      -((F.map ((shiftFunctorObjXIso (K.stupidTrunc (embeddingUpIntLE p')) (-1) i i₀ hi₀).hom ≫
          (stupidTruncLEXIso K p' i₀ hi).hom)).app _ ≫
        (F.obj (K.X i₀)).map (singleObjXIsoOfEq (up ℤ) q (L.X q) j hj).hom ≫
          ιMapBifunctor K L F (up ℤ) i₀ q k'
            (by change i + j = k at h; change i₀ + q = k'; omega) ≫ g.f k') := by
  subst hi₀
  rw [connectingGECochain, CochainComplex.HomComplex.Cochain.mk_v, ι_mapBifunctorDesc, dif_pos hi,
    dif_pos hj]

/-- The cochain `connectingGECochain` vanishes on the summands `F((σ^{≤p'}K[-1])^i, (L^q[-q])^j)`
with `p' < i - 1`. -/
theorem ι_connectingGECochain_v_eq_zero (p' q i j k k' : ℤ) (hk : k + (-1) = k')
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi : p' < i + (-1)) :
    ιMapBifunctor _ _ F (up ℤ) i j k h ≫ (connectingGECochain F g p' q).v k k' hk = 0 := by
  rw [connectingGECochain, CochainComplex.HomComplex.Cochain.mk_v, ι_mapBifunctorDesc,
    dif_neg (by omega)]

/-- The first composite of `homotopyConnectingGE`, on a summand away from the degree
`p' + 1` of `K^{p'+1}[-p'-1]`. -/
theorem ι_connectingGE_left_eq_zero (p' q : ℤ) (hpq : p' + 1 + q = n) (i j k : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi : i ≠ p' + 1) :
    ιMapBifunctor _ _ F (up ℤ) i j k h ≫
      (mapBifunctorMap (stupidTruncLEδShift K p') (𝟙 ((single C₂ (up ℤ) q).obj (L.X q))) F (up ℤ) ≫
        gradedMul F g hM (p' + 1) q hpq).f k = 0 := by
  rw [comp_f, ι_mapBifunctorMap_assoc]
  have hz : IsZero ((F.obj (((single C₁ (up ℤ) (p' + 1)).obj (K.X (p' + 1))).X i)).obj
      (((single C₂ (up ℤ) q).obj (L.X q)).X j)) :=
    Functor.map_isZero (F.flip.obj _) (isZero_single_obj_X (up ℤ) _ _ _ hi)
  rw [hz.eq_of_src (ιMapBifunctor _ _ F (up ℤ) i j k _ ≫ _) 0]
  simp

/-- The first composite of `homotopyConnectingGE` on the summand in degree `p' + 1` of
`σ^{≤p'}K[-1]`: it is minus `g` precomposed with `d^{p'} ⊗ 1`. -/
theorem ι_connectingGE_left_self (p' q : ℤ) (hpq : p' + 1 + q = n) (j k : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p' + 1, j) = k) (hj : j = q) :
    ιMapBifunctor _ _ F (up ℤ) (p' + 1) j k h ≫
      (mapBifunctorMap (stupidTruncLEδShift K p') (𝟙 ((single C₂ (up ℤ) q).obj (L.X q))) F (up ℤ) ≫
        gradedMul F g hM (p' + 1) q hpq).f k =
      -((F.map ((shiftFunctorObjXIso (K.stupidTrunc (embeddingUpIntLE p')) (-1) (p' + 1) p'
          (by omega)).hom ≫ (stupidTruncLEXIso K p' p' le_rfl).hom ≫ K.d p' (p' + 1))).app _ ≫
        (F.obj (K.X (p' + 1))).map (singleObjXIsoOfEq (up ℤ) q (L.X q) j hj).hom ≫
          ιMapBifunctor K L F (up ℤ) (p' + 1) q k
            (by change p' + 1 + j = k at h; change p' + 1 + q = k; omega) ≫ g.f k) := by
  subst hj
  rw [comp_f, ι_mapBifunctorMap_assoc, ι_gradedMul_f, stupidTruncLEδShift_f K p' (p' + 1) rfl]
  simp only [id_f, CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_neg, NatTrans.app_neg, Preadditive.neg_comp]
  congr 1
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]
  simp [singleObjXSelf, singleObjXIsoOfEq, eqToHom_map, eqToHom_app]

/-- The second composite of `homotopyConnectingGE` (up to sign) on a summand: it is `(-1)^i`
times `g` precomposed with `1 ⊗ d^q`. -/
theorem ι_connectingGE_right (p' q : ℤ) (hpq : p' + 1 + q = n) (i j k i₀ : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi₀ : i₀ = i + (-1)) (hi : i₀ ≤ p')
    (hj : j = q) :
    ιMapBifunctor _ _ F (up ℤ) i j k h ≫
      (mapBifunctorMap (𝟙 ((K.stupidTrunc (embeddingUpIntLE p'))⟦(-1 : ℤ)⟧)) (stupidTruncGEδ L q)
          F (up ℤ) ≫
        mapBifunctorShiftedPairing (truncMul F g hM p' (q + 1) (by omega)) (-1) 1 (by omega)).f k =
      i.negOnePow • ((F.map ((shiftFunctorObjXIso (K.stupidTrunc (embeddingUpIntLE p')) (-1) i i₀
          hi₀).hom ≫ (stupidTruncLEXIso K p' i₀ hi).hom)).app _ ≫
        (F.obj (K.X i₀)).map ((singleObjXIsoOfEq (up ℤ) q (L.X q) j hj).hom ≫ L.d q (j + 1)) ≫
          ιMapBifunctor K L F (up ℤ) i₀ (j + 1) k
            (by change i + j = k at h; change i₀ + (j + 1) = k; omega) ≫ g.f k) := by
  rw [comp_f, ι_mapBifunctorMap_assoc,
    ι_mapBifunctorShiftedPairing_f _ (-1) 1 _ i j k h i₀ (j + 1) hi₀ rfl,
    ι_truncMul_f F g hM p' (q + 1) _ i₀ (j + 1) k _ hi (by omega), stupidTruncGEδ_f L q j hj]
  simp only [id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, mul_one,
    Linear.comp_units_smul]
  congr 1
  simp only [CochainComplex.shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_hom,
    CategoryTheory.Functor.map_id, Category.id_comp]
  dsimp only [CochainComplex.shiftFunctor_obj_X', CochainComplex.shiftFunctor_obj_X]
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
    NatTrans.naturality_assoc]
  simp only [← Functor.map_comp_assoc, Category.assoc, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id]

/-- The composite of the homotopy with the differential of `M`, on a summand. -/
theorem ι_connectingGECochain_v_d (p' q i j k i₀ : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi₀ : i₀ = i + (-1)) (hi : i₀ ≤ p')
    (hj : j = q) :
    ιMapBifunctor _ _ F (up ℤ) i j k h ≫ (connectingGECochain F g p' q).v k (k - 1) (by omega) ≫
        M.d (k - 1) k =
      -((F.map ((shiftFunctorObjXIso (K.stupidTrunc (embeddingUpIntLE p')) (-1) i i₀ hi₀).hom ≫
          (stupidTruncLEXIso K p' i₀ hi).hom ≫ K.d i₀ i)).app _ ≫
        (F.obj (K.X i)).map (singleObjXIsoOfEq (up ℤ) q (L.X q) j hj).hom ≫
          ιMapBifunctor K L F (up ℤ) i q k
            (by change i + j = k at h; change i + q = k; omega) ≫ g.f k +
        i₀.negOnePow • ((F.map ((shiftFunctorObjXIso (K.stupidTrunc (embeddingUpIntLE p')) (-1) i
            i₀ hi₀).hom ≫ (stupidTruncLEXIso K p' i₀ hi).hom)).app _ ≫
          (F.obj (K.X i₀)).map ((singleObjXIsoOfEq (up ℤ) q (L.X q) j hj).hom ≫ L.d q (q + 1)) ≫
            ιMapBifunctor K L F (up ℤ) i₀ (q + 1) k
              (by change i + j = k at h; change i₀ + (q + 1) = k; omega) ≫ g.f k)) := by
  have hk : i + j = k := h
  rw [ι_connectingGECochain_v_assoc F g p' q i j k (k - 1) i₀ _ h hi₀ hi hj]
  simp only [Preadditive.neg_comp, Category.assoc]
  rw [Hom.comm,
    reassoc_of% ι_mapBifunctor_comp_d F i₀ i q (q + 1) (k - 1) k _ (by omega) rfl (by omega)]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, Preadditive.comp_add,
    Preadditive.add_comp, Category.assoc, CategoryTheory.Functor.map_comp, NatTrans.comp_app,
    NatTrans.naturality_assoc]

/-- The composite of the differential of the total complex with the homotopy, on a summand. -/
theorem ι_d_connectingGECochain_v (p' q i j k i₀ : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi₀ : i₀ = i + (-1)) (hi : i₀ ≤ p')
    (hj : j = q) :
    ιMapBifunctor _ _ F (up ℤ) i j k h ≫
        (mapBifunctor ((K.stupidTrunc (embeddingUpIntLE p'))⟦(-1 : ℤ)⟧)
          ((single C₂ (up ℤ) q).obj (L.X q)) F (up ℤ)).d k (k + 1) ≫
          (connectingGECochain F g p' q).v (k + 1) k (by omega) =
      if hi' : i ≤ p' then
        (F.map ((shiftFunctorObjXIso (K.stupidTrunc (embeddingUpIntLE p')) (-1) i i₀ hi₀).hom ≫
            (stupidTruncLEXIso K p' i₀ hi).hom ≫ K.d i₀ i)).app _ ≫
          (F.obj (K.X i)).map (singleObjXIsoOfEq (up ℤ) q (L.X q) j hj).hom ≫
            ιMapBifunctor K L F (up ℤ) i q k
              (by change i + j = k at h; change i + q = k; omega) ≫ g.f k
      else 0 := by
  have hk : i + j = k := h
  rw [reassoc_of% ι_mapBifunctor_comp_d F i (i + 1) j (j + 1) k (k + 1) h rfl rfl rfl,
    Preadditive.add_comp]
  simp only [single_obj_d, CategoryTheory.Functor.map_zero, zero_comp, smul_zero, add_zero,
    Category.assoc]
  split_ifs with hi'
  · rw [ι_connectingGECochain_v F g p' q (i + 1) j (k + 1) k i _ _ (by omega) hi' hj,
      Preadditive.comp_neg]
    have e := CochainComplex.shift_d_comp_shiftFunctorObjXIso_hom
      (K.stupidTrunc (embeddingUpIntLE p')) (-1) i (i + 1) i₀ i hi₀ (by omega)
    rw [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul] at e
    rw [← NatTrans.comp_app_assoc, ← Functor.map_comp, reassoc_of% e,
      stupidTruncLE_d_eq K p' i₀ i hi hi']
    simp only [Preadditive.neg_comp, CategoryTheory.Functor.map_neg, NatTrans.app_neg,
      Preadditive.neg_comp, neg_neg, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [ι_connectingGECochain_v_eq_zero F g p' q (i + 1) j (k + 1) k _ _ (by omega), comp_zero]

/-- **The products are compatible along the connecting maps `σ^{≤p'}K[-1] ⟶ K^p[-p]` and
`L^q[-q] ⟶ σ^{≥q+1}L[1]`, up to homotopy and sign** (`p = p' + 1`, `p + q = n`): on
`Tot(F(σ^{≤p'}K[-1], L^q[-q]))`, the map deduced from the connecting map of
`K^p[-p] ⟶ σ^{≤p}K ⟶ σ^{≤p'}K` followed by the product of the graded pieces is homotopic to
minus the connecting map of `σ^{≥q+1}L ⟶ σ^{≥q}L ⟶ L^q[-q]` followed by the shift of `γ_{p'}`. -/
def homotopyConnectingGE (p' q : ℤ) (hpq : p' + 1 + q = n) :
    Homotopy
      (mapBifunctorMap (stupidTruncLEδShift K p') (𝟙 ((single C₂ (up ℤ) q).obj (L.X q))) F (up ℤ) ≫
        gradedMul F g hM (p' + 1) q hpq)
      (-(mapBifunctorMap (𝟙 ((K.stupidTrunc (embeddingUpIntLE p'))⟦(-1 : ℤ)⟧))
          (stupidTruncGEδ L q) F (up ℤ) ≫
        mapBifunctorShiftedPairing (truncMul F g hM p' (q + 1) (by omega)) (-1) 1 (by omega))) :=
  (CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm ⟨connectingGECochain F g p' q, by
    refine CochainComplex.HomComplex.Cochain.ext₀ _ _ (fun k => ?_)
    rw [CochainComplex.HomComplex.Cochain.add_v, CochainComplex.HomComplex.Cochain.ofHom_v,
      CochainComplex.HomComplex.Cochain.ofHom_v,
      CochainComplex.HomComplex.δ_v (-1) 0 (by omega) _ k k (add_zero k) (k - 1) (k + 1)
        (by omega) rfl]
    ext i j h
    have hk : i + j = k := h
    by_cases hj : j = q
    swap
    · exact (Functor.map_isZero _ (isZero_single_obj_X (up ℤ) q (L.X q) j hj)).eq_of_src _ _
    by_cases hi : i + (-1) ≤ p'
    swap
    · exact (Functor.map_isZero (F.flip.obj _) (CochainComplex.isZero_of_isStrictlyLE
        (K.stupidTrunc (embeddingUpIntLE p')) p' (i + (-1)) (by omega))).eq_of_src _ _
    simp only [Preadditive.comp_add, Int.negOnePow_zero, one_smul, neg_f_apply,
      Preadditive.comp_neg]
    by_cases hip : i + (-1) = p'
    · obtain rfl : i = p' + 1 := by omega
      rw [ι_connectingGECochain_v_d F g p' q (p' + 1) j k p' h (by omega) le_rfl hj,
        ι_d_connectingGECochain_v F g p' q (p' + 1) j k p' h (by omega) le_rfl hj,
        ι_connectingGE_right F g hM p' q hpq (p' + 1) j k p' h (by omega) le_rfl hj,
        ι_connectingGE_left_self F g hM p' q hpq j k h hj, dif_neg (by omega), Int.negOnePow_succ,
        Units.neg_smul]
      subst hj
      abel
    · have hs : i.negOnePow = -(i + (-1)).negOnePow := by
        rw [← Int.negOnePow_succ]
        congr 1
        omega
      rw [ι_connectingGECochain_v_d F g p' q i j k (i + (-1)) h rfl hi hj,
        ι_d_connectingGECochain_v F g p' q i j k (i + (-1)) h rfl hi hj,
        ι_connectingGE_right F g hM p' q hpq i j k (i + (-1)) h rfl hi hj,
        ι_connectingGE_left_eq_zero F g hM p' q hpq i j k h (by omega), dif_pos (by omega), hs,
        Units.neg_smul]
      subst hj
      abel⟩


end Homotopies

section Derived

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Abelian C₁] [Abelian C₂] [Abelian D] {hD : HasDerivedCategory D}
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  [∀ (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ), HasMapBifunctor K L F (up ℤ)]
  {K : CochainComplex C₁ ℤ} {L : CochainComplex C₂ ℤ} {M : CochainComplex D ℤ}
  (g : mapBifunctor K L F (up ℤ) ⟶ M) {n : ℤ} (hM : ∀ k, n < k → IsZero (M.X k))

/-- The homotopy `homotopyConnectingLE` in the derived category. -/
theorem Q_map_comp_connectingLE (p' q : ℤ) (hpq : p' + 1 + q = n) :
    (DerivedCategory.Q (C := D)).map (mapBifunctorMap (stupidTruncLEδ K p')
        (𝟙 (((single C₂ (up ℤ) q).obj (L.X q))⟦(-1 : ℤ)⟧)) F (up ℤ)) ≫
      (DerivedCategory.Q (C := D)).map (F.map₂CochainComplex.shiftedPairing
        (gradedMul F g hM (p' + 1) q hpq) 1 (-1) (by omega)) =
    (DerivedCategory.Q (C := D)).map (mapBifunctorMap (𝟙 (K.stupidTrunc (embeddingUpIntLE p')))
        (stupidTruncGEδShift L q) F (up ℤ)) ≫
      (DerivedCategory.Q (C := D)).map (truncMul F g hM p' (q + 1) (by omega)) :=
  (Functor.map_comp _ _ _).symm.trans
    ((DerivedCategory.Q_map_eq_of_homotopy D (homotopyConnectingLE F g hM p' q hpq)).trans
      (Functor.map_comp _ _ _))

/-- The homotopy `homotopyConnectingGE` in the derived category. -/
theorem Q_map_comp_connectingGE (p' q : ℤ) (hpq : p' + 1 + q = n) :
    (DerivedCategory.Q (C := D)).map (mapBifunctorMap (stupidTruncLEδShift K p')
        (𝟙 ((single C₂ (up ℤ) q).obj (L.X q))) F (up ℤ)) ≫
      (DerivedCategory.Q (C := D)).map (gradedMul F g hM (p' + 1) q hpq) =
    -((DerivedCategory.Q (C := D)).map
        (mapBifunctorMap (𝟙 ((K.stupidTrunc (embeddingUpIntLE p'))⟦(-1 : ℤ)⟧))
          (stupidTruncGEδ L q) F (up ℤ)) ≫
      (DerivedCategory.Q (C := D)).map (F.map₂CochainComplex.shiftedPairing
        (truncMul F g hM p' (q + 1) (by omega)) (-1) 1 (by omega))) :=
  (Functor.map_comp _ _ _).symm.trans
    ((DerivedCategory.Q_map_eq_of_homotopy D (homotopyConnectingGE F g hM p' q hpq)).trans
      ((Functor.map_neg _).trans (congrArg Neg.neg (Functor.map_comp _ _ _))))

end Derived

end StacksDraft.StupidTruncation
