module

public import StacksFrontier.Algebra.Homology.BifunctorDegreewiseSplitDesc
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso

/-!
# Products on stupid truncations

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor, `K`, `L`, `M` cochain complexes and
`g : Tot(F(K, L)) ⟶ M` a morphism of complexes, where `M` vanishes in degrees `> n`. For
`p + q = n` the restriction `Tot(F(K, σ^{≥q}L)) ⟶ Tot(F(K, L)) ⟶ M` vanishes on the summands
`F(K^i, L^j)` with `i > p` for degree reasons, so it factors through
`Tot(F(σ^{≤p}K, σ^{≥q}L))`; this is the map

`γ_p : Tot(F(σ^{≤p}K, σ^{≥q}L)) ⟶ M`

of the proof of [Stacks, Tag 0G8K] (`StacksDraft.StupidTruncation.truncMul`), for `g` the wedge
product of the de Rham complex of a morphism of relative dimension `n`. Restricted to the top
term `K^p[-p]` of `σ^{≤p}K` it factors through the bottom term `L^q[-q]` of `σ^{≥q}L`, giving the
product of the graded pieces `Tot(F(K^p[-p], L^q[-q])) ⟶ M`
(`StacksDraft.StupidTruncation.gradedMul`), which on the summand `F(K^p, L^q)` is `g`.

These maps are compatible along the maps of the short exact sequences
`K^p[-p] ⟶ σ^{≤p}K ⟶ σ^{≤p-1}K` and `σ^{≥q+1}L ⟶ σ^{≥q}L ⟶ L^q[-q]`
(`StacksDraft.StupidTruncation.mapBifunctorMap_stupidTruncLEι_truncMul` and
`StacksDraft.StupidTruncation.mapBifunctorMap_stupidTruncLEMapLE_truncMul`): these are two of the
four compatibilities of the five lemma in the proof of [Stacks, Tag 0G8K].

## Main definitions

* `StacksDraft.StupidTruncation.truncMul`: `Tot(F(σ^{≤p}K, σ^{≥q}L)) ⟶ M`.
* `StacksDraft.StupidTruncation.gradedMul`: `Tot(F(K^p[-p], L^q[-q])) ⟶ M`.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape

namespace StacksDraft.StupidTruncation

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroObject C₁] [HasZeroMorphisms C₂] [HasZeroObject C₂]
  [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  [∀ (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ), HasMapBifunctor K L F (up ℤ)]
  {K : CochainComplex C₁ ℤ} {L : CochainComplex C₂ ℤ} {M : CochainComplex D ℤ}
  (g : mapBifunctor K L F (up ℤ) ⟶ M) {n : ℤ} (hM : ∀ k, n < k → IsZero (M.X k))

omit [HasZeroObject C₁] in
include hM in
/-- For `p + q = n`, the restriction of `g` to `Tot(F(K, σ^{≥q}L))` vanishes on the summands
`F(K^i, (σ^{≥q}L)^j)` with `i > p`: either `j < q` and the summand vanishes, or `i + j > n` and
the target vanishes. -/
theorem ι_mapBifunctorMap_ιStupidTrunc_comp_eq_zero (p q : ℤ) (hpq : p + q = n) (i j k : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi : p < i) :
    ιMapBifunctor K (L.stupidTrunc (embeddingUpIntGE q)) F (up ℤ) i j k h ≫
      (mapBifunctorMap (𝟙 K) (ιStupidTrunc L (embeddingUpIntGE q)) F (up ℤ) ≫ g).f k = 0 := by
  have hk : i + j = k := h
  by_cases hj : q ≤ j
  · exact (hM k (by omega)).eq_of_tgt _ _
  · exact (Functor.map_isZero _ (CochainComplex.isZero_of_isStrictlyGE
      (L.stupidTrunc (embeddingUpIntGE q)) q j (by omega))).eq_of_src _ _

/-- **The product `γ_p : Tot(F(σ^{≤p}K, σ^{≥q}L)) ⟶ M`** of [Stacks, Tag 0G8K], for `p + q = n`:
the factorisation of `Tot(F(K, σ^{≥q}L)) ⟶ Tot(F(K, L)) ⟶ M` through the projection
`K ⟶ σ^{≤p}K`. -/
def truncMul (p q : ℤ) (hpq : p + q = n) :
    mapBifunctor (K.stupidTrunc (embeddingUpIntLE p)) (L.stupidTrunc (embeddingUpIntGE q)) F
      (up ℤ) ⟶ M :=
  truncLEDesc F K (L.stupidTrunc (embeddingUpIntGE q)) p
    (mapBifunctorMap (𝟙 K) (ιStupidTrunc L (embeddingUpIntGE q)) F (up ℤ) ≫ g)
    (ι_mapBifunctorMap_ιStupidTrunc_comp_eq_zero F g hM p q hpq)

/-- The product `γ_p` is characterised by `Tot(F(π, 1)) ≫ γ_p = Tot(F(1, ι)) ≫ g`. -/
@[reassoc (attr := simp)]
theorem mapBifunctorMap_πStupidTrunc_truncMul (p q : ℤ) (hpq : p + q = n) :
    mapBifunctorMap (K.πStupidTrunc (embeddingUpIntLE p)) (𝟙 _) F (up ℤ) ≫
        truncMul F g hM p q hpq =
      mapBifunctorMap (𝟙 K) (ιStupidTrunc L (embeddingUpIntGE q)) F (up ℤ) ≫ g :=
  mapBifunctorMap_πStupidTrunc_truncLEDesc _ _ _

omit [HasZeroObject C₂] in
/-- Maps out of `Tot(F(σ^{≤p}K, L'))` agree as soon as they agree after `Tot(F(π, 1))`. -/
theorem mapBifunctor_stupidTruncLE_hom_ext (p : ℤ) {L' : CochainComplex C₂ ℤ}
    {N : CochainComplex D ℤ}
    {u v : mapBifunctor (K.stupidTrunc (embeddingUpIntLE p)) L' F (up ℤ) ⟶ N}
    (h : mapBifunctorMap (K.πStupidTrunc (embeddingUpIntLE p)) (𝟙 L') F (up ℤ) ≫ u =
      mapBifunctorMap (K.πStupidTrunc (embeddingUpIntLE p)) (𝟙 L') F (up ℤ) ≫ v) : u = v :=
  have : Epi (mapBifunctorMap (K.πStupidTrunc (embeddingUpIntLE p)) (𝟙 L') F (up ℤ)) :=
    epi_mapBifunctorMap_πStupidTrunc F
  (cancel_epi _).1 h

/-- **The products `γ_p` are compatible along `σ^{≤p}K ⟶ σ^{≤p'}K` and
`σ^{≥q+1}L ⟶ σ^{≥q}L`**, for `p' + 1 = p` and `p + q = n`: both restrictions to
`Tot(F(σ^{≤p}K, σ^{≥q+1}L))` agree. -/
theorem mapBifunctorMap_stupidTruncLEMapLE_truncMul (p p' : ℤ) (hp : p' + 1 = p) (q : ℤ)
    (hpq : p + q = n) :
    mapBifunctorMap (stupidTruncLEMapLE K (show p' ≤ p by omega)) (𝟙 _) F (up ℤ) ≫
        truncMul F g hM p' (q + 1) (by omega) =
      mapBifunctorMap (𝟙 _) (stupidTruncGEMapLE L (show q ≤ q + 1 by omega)) F (up ℤ) ≫
        truncMul F g hM p q hpq := by
  refine mapBifunctor_stupidTruncLE_hom_ext F p ?_
  have e₁ : mapBifunctorMap (K.πStupidTrunc (embeddingUpIntLE p)) (𝟙 _) F (up ℤ) ≫
      mapBifunctorMap (stupidTruncLEMapLE K (show p' ≤ p by omega))
        (𝟙 (L.stupidTrunc (embeddingUpIntGE (q + 1)))) F (up ℤ) =
      mapBifunctorMap (K.πStupidTrunc (embeddingUpIntLE p')) (𝟙 _) F (up ℤ) := by
    rw [mapBifunctorMap_comp, π_stupidTruncLEMapLE, Category.comp_id]
  have e₂ : mapBifunctorMap (K.πStupidTrunc (embeddingUpIntLE p)) (𝟙 _) F (up ℤ) ≫
      mapBifunctorMap (𝟙 _) (stupidTruncGEMapLE L (show q ≤ q + 1 by omega)) F (up ℤ) =
      mapBifunctorMap (𝟙 K) (stupidTruncGEMapLE L (show q ≤ q + 1 by omega)) F (up ℤ) ≫
        mapBifunctorMap (K.πStupidTrunc (embeddingUpIntLE p)) (𝟙 _) F (up ℤ) := by
    rw [mapBifunctorMap_comp, mapBifunctorMap_comp, Category.comp_id, Category.id_comp,
      Category.id_comp, Category.comp_id]
  rw [reassoc_of% e₁, reassoc_of% e₂, mapBifunctorMap_πStupidTrunc_truncMul,
    mapBifunctorMap_πStupidTrunc_truncMul, mapBifunctorMap_comp_assoc, Category.id_comp,
    stupidTruncGEMapLE_ι]

open Classical in
/-- The degreewise sections of the projection `σ^{≥q}L ⟶ L^q[-q]`: the identification of terms
in degree `q`, and zero elsewhere, where `L^q[-q]` vanishes. -/
def stupidTruncGEπSection (L : CochainComplex C₂ ℤ) (q : ℤ) (j : ℤ) :
    ((single C₂ (up ℤ) q).obj (L.X q)).X j ⟶ (L.stupidTrunc (embeddingUpIntGE q)).X j :=
  if h : j = q then eqToHom (by rw [h]) ≫ (singleObjXSelf (up ℤ) q (L.X q)).hom ≫
      (stupidTruncGEXIso L q q le_rfl).inv ≫ eqToHom (by rw [h])
  else 0

omit [HasZeroObject C₁] [HasZeroMorphisms C₁] in
/-- In degree `q`, the section `stupidTruncGEπSection L q q` is the identification
`(L^q[-q])^q ≅ L^q ≅ (σ^{≥q}L)^q`. -/
theorem stupidTruncGEπSection_self (L : CochainComplex C₂ ℤ) (q : ℤ) :
    stupidTruncGEπSection L q q = (singleObjXSelf (up ℤ) q (L.X q)).hom ≫
      (stupidTruncGEXIso L q q le_rfl).inv := by
  simp [stupidTruncGEπSection]

omit [HasZeroObject C₁] [HasZeroMorphisms C₁] in
/-- In every degree `j`, `stupidTruncGEπSection L q j` is a section of the projection
`(σ^{≥q}L)^j ⟶ (L^q[-q])^j`. -/
theorem stupidTruncGEπSection_comp (L : CochainComplex C₂ ℤ) (q : ℤ) (j : ℤ) :
    stupidTruncGEπSection L q j ≫ (stupidTruncGEπ L q).f j = 𝟙 _ := by
  by_cases h : j = q
  · subst h
    rw [stupidTruncGEπSection_self, stupidTruncGEπ_f]
    simp
  · exact (isZero_single_obj_X (up ℤ) q (L.X q) j h).eq_of_src _ _

omit [HasZeroObject C₁] [HasZeroMorphisms C₁] in
/-- In degree `q`, the section `stupidTruncGEπSection L q q` is also a retraction of the projection
`(σ^{≥q}L)^q ⟶ (L^q[-q])^q`. -/
theorem stupidTruncGEπ_f_comp_section_self (L : CochainComplex C₂ ℤ) (q : ℤ) :
    (stupidTruncGEπ L q).f q ≫ stupidTruncGEπSection L q q = 𝟙 _ := by
  rw [stupidTruncGEπSection_self, stupidTruncGEπ_f]
  simp

include hM in
/-- For `p + q = n`, the restriction of `γ_p` to `Tot(F(K^p[-p], σ^{≥q}L))` vanishes on the
summands `F((K^p[-p])^i, (σ^{≥q}L)^j)` with `j ≠ q`. -/
theorem ι_mapBifunctorMap_stupidTruncLEι_truncMul_eq_zero (p q : ℤ) (hpq : p + q = n)
    (i j k : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hj : j ≠ q) :
    ιMapBifunctor ((single C₁ (up ℤ) p).obj (K.X p)) (L.stupidTrunc (embeddingUpIntGE q)) F
        (up ℤ) i j k h ≫
      (mapBifunctorMap (stupidTruncLEι K p) (𝟙 _) F (up ℤ) ≫ truncMul F g hM p q hpq).f k =
        0 := by
  have hk : i + j = k := h
  by_cases hi : i = p
  · by_cases hj' : q ≤ j
    · exact (hM k (by omega)).eq_of_tgt _ _
    · exact (Functor.map_isZero _ (CochainComplex.isZero_of_isStrictlyGE
        (L.stupidTrunc (embeddingUpIntGE q)) q j (by omega))).eq_of_src _ _
  · exact (Functor.map_isZero (F.flip.obj _)
      (isZero_single_obj_X (up ℤ) p (K.X p) i hi)).eq_of_src _ _

/-- For `p + q = n`, the restriction of `γ_p` to `Tot(F(K^p[-p], σ^{≥q}L))` is unchanged by
precomposition with the projection to `Tot(F(K^p[-p], L^q[-q]))` followed by the degreewise section
induced by `stupidTruncGEπSection L q`. -/
theorem mapBifunctorMap_stupidTruncGEπ_f_comp_section (p q : ℤ) (hpq : p + q = n) (k : ℤ) :
    (mapBifunctorMap (𝟙 ((single C₁ (up ℤ) p).obj (K.X p))) (stupidTruncGEπ L q) F (up ℤ)).f k ≫
        mapBifunctorMapSection F (up ℤ) (fun _ => 𝟙 _) (stupidTruncGEπSection L q) k ≫
          (mapBifunctorMap (stupidTruncLEι K p) (𝟙 _) F (up ℤ) ≫ truncMul F g hM p q hpq).f k =
      (mapBifunctorMap (stupidTruncLEι K p) (𝟙 _) F (up ℤ) ≫ truncMul F g hM p q hpq).f k := by
  ext i j h
  rw [ι_mapBifunctorMap_f_comp_mapBifunctorMapSection_assoc]
  by_cases hj : j = q
  · subst hj
    rw [stupidTruncGEπ_f_comp_section_self]
    simp
  · rw [ι_mapBifunctorMap_stupidTruncLEι_truncMul_eq_zero F g hM p q hpq i j k h hj]
    simp

/-- **The product of the graded pieces `Tot(F(K^p[-p], L^q[-q])) ⟶ M`**, for `p + q = n`: the
factorisation of the restriction of `γ_p` to `Tot(F(K^p[-p], σ^{≥q}L))` through the projection
`σ^{≥q}L ⟶ L^q[-q]`. -/
def gradedMul (p q : ℤ) (hpq : p + q = n) :
    mapBifunctor ((single C₁ (up ℤ) p).obj (K.X p)) ((single C₂ (up ℤ) q).obj (L.X q)) F
      (up ℤ) ⟶ M :=
  descOfSection (mapBifunctorMap (𝟙 _) (stupidTruncGEπ L q) F (up ℤ))
    (mapBifunctorMapSection F (up ℤ) (fun _ => 𝟙 _) (stupidTruncGEπSection L q))
    (mapBifunctorMapSection_comp _ _ F (up ℤ) _ _ (fun _ => Category.id_comp _)
      (stupidTruncGEπSection_comp L q))
    (mapBifunctorMap (stupidTruncLEι K p) (𝟙 _) F (up ℤ) ≫ truncMul F g hM p q hpq)
    (mapBifunctorMap_stupidTruncGEπ_f_comp_section F g hM p q hpq)

/-- **The products `γ_p` and that of the graded pieces are compatible along `K^p[-p] ⟶ σ^{≤p}K`
and `σ^{≥q}L ⟶ L^q[-q]`**: both restrictions to `Tot(F(K^p[-p], σ^{≥q}L))` agree. -/
@[reassoc]
theorem mapBifunctorMap_stupidTruncLEι_truncMul (p q : ℤ) (hpq : p + q = n) :
    mapBifunctorMap (stupidTruncLEι K p) (𝟙 _) F (up ℤ) ≫ truncMul F g hM p q hpq =
      mapBifunctorMap (𝟙 _) (stupidTruncGEπ L q) F (up ℤ) ≫ gradedMul F g hM p q hpq :=
  (comp_descOfSection _ _ _ _ _).symm

end StacksDraft.StupidTruncation
