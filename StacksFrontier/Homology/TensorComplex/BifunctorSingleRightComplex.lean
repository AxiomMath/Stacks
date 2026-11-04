module

public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRight

/-!
# `Tot(F(K, N[0]))` is `F(-, N)` applied degreewise to `K`

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor between preadditive categories preserving zero morphisms in
each variable, let `K` be a cochain complex in `C₁` and let `N` be an object of `C₂`. The
degree-`i` term of `Tot(F(K, N[0]))` is `F(K^i, N)`, and the differential is `F(d_K, N)`: the
total differential is the sum of two terms, and the one coming from the second variable vanishes
because `N[0]` has zero differential. The sign the first term would carry is `+1` in the Koszul
convention, so the comparison is an isomorphism of complexes onto the degreewise image of `K`
under `F(-, N)`.

## Main results

* `HomologicalComplex.singleRightι_d`: the total differential of `Tot(F(K, N[0]))` on the
  nonvanishing summand is `F(d_K, N)`.
* `HomologicalComplex.mapBifunctorSingleRightIso`: `Tot(F(K, N[0])) ≅ F(-, N)` applied
  degreewise to `K`, as an isomorphism of complexes.

## References

* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe v₁ v₂ v u₁ u₂ u

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u} [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{v} D] [Preadditive C₁] [Preadditive C₂] [Preadditive D] [HasZeroObject C₂]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ M : C₁, (F.obj M).PreservesZeroMorphisms]
  (K : CochainComplex C₁ ℤ) (N : C₂)
  [HasMapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)]

/-- The inclusion of the summand of bidegree `(i, 0)` into the degree-`i` term of
`Tot(F(K, N[0]))`. It is the only summand that does not vanish. -/
def singleRightι (i : ℤ) :
    (F.obj (K.X i)).obj (((CochainComplex.singleFunctor C₂ 0).obj N).X 0) ⟶
      (mapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj N) F
        (ComplexShape.up ℤ)).X i :=
  ιMapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ) i 0 i
    (by simp)

/-- The projection of the degree-`i` term of `Tot(F(K, N[0]))` onto the summand of bidegree
`(i, 0)`. -/
def singleRightπ (i : ℤ) :
    (mapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj N) F
        (ComplexShape.up ℤ)).X i ⟶
      (F.obj (K.X i)).obj (((CochainComplex.singleFunctor C₂ 0).obj N).X 0) :=
  mapBifunctorDesc fun a b hab =>
    if h : b = 0 then by
      subst h
      have ha : a = i := by simpa using hab
      subst ha
      exact 𝟙 _
    else 0

/-- The inclusion of the summand of bidegree `(i, 0)` followed by the projection onto it is the
identity. -/
theorem singleRightι_π (i : ℤ) :
    singleRightι F K N i ≫ singleRightπ F K N i = 𝟙 _ := by
  simp [singleRightι, singleRightπ]

/-- Two maps out of the degree-`i` term of `Tot(F(K, N[0]))` are equal if they agree after
precomposing with the inclusion of the summand of bidegree `(i, 0)`. -/
private theorem singleRight_hom_ext {i : ℤ} {Z : D}
    {f g : (mapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj N) F
      (ComplexShape.up ℤ)).X i ⟶ Z} (h : singleRightι F K N i ≫ f = singleRightι F K N i ≫ g) :
    f = g := by
  refine mapBifunctor.hom_ext fun a b hab => ?_
  by_cases hb : b = 0
  · subst hb
    have ha : a = i := by simpa using hab
    subst ha
    exact h
  · exact (isZero_obj_obj_single_obj_X_right F K N a b hb).eq_of_src _ _

/-- The projection onto the summand of bidegree `(i, 0)` followed by the inclusion of it is the
identity of the degree-`i` term of `Tot(F(K, N[0]))`. -/
theorem singleRightπ_ι (i : ℤ) :
    singleRightπ F K N i ≫ singleRightι F K N i = 𝟙 _ := by
  refine singleRight_hom_ext F K N ?_
  rw [← Category.assoc, singleRightι_π, Category.id_comp, Category.comp_id]

/-- The inverse of `mapBifunctorSingleRightXIso F K N i` is `F(K^i, -)` applied to the inverse of
`singleObjXSelf`, followed by `singleRightι F K N i`. -/
theorem mapBifunctorSingleRightXIso_inv (i : ℤ) :
    (mapBifunctorSingleRightXIso F K N i).inv =
      (F.obj (K.X i)).map (singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫
        singleRightι F K N i :=
  rfl

/-- The total differential of `Tot(F(K, N[0]))` carries the summand of bidegree `(i, 0)` to the
summand of bidegree `(j, 0)` by `F(d_K, N)`, with no sign. -/
theorem singleRightι_d (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    singleRightι F K N i ≫
        (mapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj N) F
          (ComplexShape.up ℤ)).d i j =
      (F.map (K.d i j)).app (((CochainComplex.singleFunctor C₂ 0).obj N).X 0) ≫
        singleRightι F K N j := by
  have hd₂ : mapBifunctor.d₂ K ((CochainComplex.singleFunctor C₂ 0).obj N) F
      (ComplexShape.up ℤ) i 0 j = 0 := by
    rw [mapBifunctor.d₂_eq' K ((CochainComplex.singleFunctor C₂ 0).obj N) F
      (ComplexShape.up ℤ) i (show (ComplexShape.up ℤ).Rel 0 1 by simp) j]
    simp
  rw [mapBifunctor.d_eq, Preadditive.comp_add, singleRightι, mapBifunctor.ι_D₁,
    mapBifunctor.ι_D₂, hd₂, add_zero,
    mapBifunctor.d₁_eq K ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)
      hij 0 j (by simp)]
  simp [singleRightι]

/-- `F(-, N)` applied degreewise to `K` is isomorphic to `Tot(F(K, N[0]))`. -/
def singleRightIsoMapBifunctor [(F.flip.obj N).Additive] :
    ((F.flip.obj N).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      mapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ) :=
  Hom.isoOfComponents (fun i => (mapBifunctorSingleRightXIso F K N i).symm) fun i j hij => by
    rw [Iso.symm_hom, Iso.symm_hom, mapBifunctorSingleRightXIso_inv,
      mapBifunctorSingleRightXIso_inv,
      Category.assoc, singleRightι_d F K N i j hij]
    simp only [Functor.mapHomologicalComplex_obj_d, Functor.flip_obj_map, ← Category.assoc]
    exact congrArg (fun g => g ≫ singleRightι F K N j)
      ((F.map (K.d i j)).naturality (singleObjXSelf (ComplexShape.up ℤ) 0 N).inv)

/-- `Tot(F(K, N[0]))` is isomorphic to `F(-, N)` applied degreewise to `K`. -/
def mapBifunctorSingleRightIso [(F.flip.obj N).Additive] :
    mapBifunctor K ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ) ≅
      ((F.flip.obj N).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  (singleRightIsoMapBifunctor F K N).symm

/-- The isomorphism `Tot(F(K, N[0])) ≅ F(-, N)(K)` is natural in `K`. -/
@[reassoc]
lemma mapBifunctorSingleRightIso_hom_naturality [(F.flip.obj N).Additive]
    {K' : CochainComplex C₁ ℤ}
    [HasMapBifunctor K' ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)]
    (φ : K ⟶ K') :
    mapBifunctorMap φ (𝟙 _) F (ComplexShape.up ℤ) ≫ (mapBifunctorSingleRightIso F K' N).hom =
      (mapBifunctorSingleRightIso F K N).hom ≫
        ((F.flip.obj N).mapHomologicalComplex (ComplexShape.up ℤ)).map φ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  refine singleRight_hom_ext F K N ?_
  have h₁ : ∀ (L : CochainComplex C₁ ℤ)
      [HasMapBifunctor L ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)],
      singleRightι F L N i ≫ (mapBifunctorSingleRightIso F L N).hom.f i =
        (F.obj (L.X i)).map (singleObjXSelf (ComplexShape.up ℤ) 0 N).hom := by
    intro L _
    have h := (mapBifunctorSingleRightXIso F L N i).inv_hom_id
    rw [mapBifunctorSingleRightXIso_inv, Category.assoc] at h
    show singleRightι F L N i ≫ (mapBifunctorSingleRightXIso F L N i).hom = _
    rw [← cancel_epi ((F.obj (L.X i)).map (singleObjXSelf (ComplexShape.up ℤ) 0 N).inv), h,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  unfold singleRightι at h₁ ⊢
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ι_mapBifunctorMap_assoc, h₁,
    reassoc_of% (h₁ K)]
  simp only [HomologicalComplex.id_f, Functor.mapHomologicalComplex_map_f, Functor.flip_obj_map]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact ((F.map (φ.f i)).naturality _).symm

end HomologicalComplex

end
