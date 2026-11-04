module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import StacksFrontier.Algebra.Homology.ComplexShapeSignsNat

/-!
# Total complexes of `ℕ`-indexed complexes and the extension by zero

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor preserving zero morphisms in each variable, and let `K` and
`L` be `ℕ`-indexed cochain complexes. There are two ways to form a `ℤ`-indexed total complex of
`F(K, L)`: extend `K` and `L` by zero to `ℤ`-indexed complexes and take the `ℤ`-indexed total
complex, or take the `ℕ`-indexed total complex and extend it by zero. This file constructs the
comparison

`Tot(F(K.extend, L.extend)) ⟶ Tot(F(K, L)).extend`

and proves that it is natural in `K` and `L`. On the summand `F(K^p, L^q)` with `p, q ≥ 0` it is
the inclusion of the summand of the same bidegree; every summand with a negative index vanishes.
The two sign conventions of [Stacks, Tag 012Z] agree on natural numbers, which is what makes the
comparison a morphism of complexes.

## Main definitions

* `HomologicalComplex.MapBifunctorExtend.component`: the component of the comparison on one
  summand.
* `HomologicalComplex.MapBifunctorExtend.restrictionHom`: the comparison as a morphism of
  `ℕ`-indexed complexes out of the restriction of the `ℤ`-indexed total complex.
* `HomologicalComplex.mapBifunctorExtendHom`: **the comparison**
  `Tot(F(K.extend, L.extend)) ⟶ Tot(F(K, L)).extend`.

## Main results

* `HomologicalComplex.mapBifunctorExtendHom_naturality`: the comparison is natural in both
  complexes.

## References

* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
-/

@[expose] public noncomputable section

open CategoryTheory Limits ComplexShape

namespace HomologicalComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroObject C₁] [HasZeroMorphisms C₂] [HasZeroObject C₂]
  [Preadditive D] [HasZeroObject D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]

namespace MapBifunctorExtend

/-- The extension by zero of an `ℕ`-indexed complex is zero in negative degrees. -/
private theorem isZero_extend_X_of_neg {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasZeroObject C] (K : CochainComplex C ℕ) (i : ℤ) (hi : i < 0) :
    IsZero ((K.extend embeddingUpNat).X i) :=
  K.isZero_extend_X embeddingUpNat i fun n hn => by
    change (n : ℤ) = i at hn
    omega

variable (K : CochainComplex C₁ ℕ) (L : CochainComplex C₂ ℕ)

/-- A summand `F(K^i, L^j)` of the `ℤ`-indexed total complex of the two extensions by zero
vanishes as soon as one of its indices is negative. -/
lemma isZero_summand (i j : ℤ) (h : i < 0 ∨ j < 0) :
    IsZero ((F.obj ((K.extend embeddingUpNat).X i)).obj ((L.extend embeddingUpNat).X j)) := by
  rcases h with h | h
  · exact (F.map_isZero (isZero_extend_X_of_neg K i h)).obj _
  · exact (F.obj _).map_isZero (isZero_extend_X_of_neg L j h)

variable [HasMapBifunctor K L F (up ℕ)]

/-- The component of the comparison on the summand `F(K^i, L^j)` of total degree `n`: for
`i, j ≥ 0` the inclusion of the summand of the same bidegree of the `ℕ`-indexed total complex,
read through the identifications of the extensions in nonnegative degrees, and zero otherwise,
the summand being zero then. -/
def component (n : ℕ) (i j : ℤ) (_ : i + j = (n : ℤ)) :
    (F.obj ((K.extend embeddingUpNat).X i)).obj ((L.extend embeddingUpNat).X j) ⟶
      (mapBifunctor K L F (up ℕ)).X n :=
  if h : 0 ≤ i ∧ 0 ≤ j then
    (F.map (K.extendXIso embeddingUpNat (i' := i) (i := i.toNat)
        (by simpa using Int.toNat_of_nonneg h.1)).hom).app _ ≫
      (F.obj (K.X i.toNat)).map (L.extendXIso embeddingUpNat (i' := j) (i := j.toNat)
        (by simpa using Int.toNat_of_nonneg h.2)).hom ≫
      ιMapBifunctor K L F (up ℕ) i.toNat j.toNat n (by dsimp; omega)
  else 0

/-- On a summand whose indices are natural numbers the component is the inclusion of the summand
of the same bidegree. -/
lemma component_natCast (n p q : ℕ) (h : (p : ℤ) + (q : ℤ) = (n : ℤ)) :
    component F K L n p q h =
      (F.map (K.extendXIso embeddingUpNat (i' := (p : ℤ)) (i := p) (by simp)).hom).app _ ≫
        (F.obj (K.X p)).map (L.extendXIso embeddingUpNat (i' := (q : ℤ)) (i := q) (by simp)).hom ≫
        ιMapBifunctor K L F (up ℕ) p q n (by dsimp; omega) := by
  rw [component, dif_pos ⟨Int.natCast_nonneg p, Int.natCast_nonneg q⟩]
  rfl

/-- On a summand with a negative index the component is zero. -/
lemma component_neg (n : ℕ) (i j : ℤ) (h : i + j = (n : ℤ)) (h' : ¬ (0 ≤ i ∧ 0 ≤ j)) :
    component F K L n i j h = 0 :=
  dif_neg h'

variable [HasMapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat) F (up ℤ)]

/-- The comparison in degree `n`, as a morphism out of the `ℤ`-indexed total complex, given by its
components on the summands. -/
def restrictionf (n : ℕ) :
    (mapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat) F (up ℤ)).X (n : ℤ) ⟶
      (mapBifunctor K L F (up ℕ)).X n :=
  mapBifunctorDesc (fun i j hij => component F K L n i j hij)

/-- On the summand `F(K^i, L^j)` the comparison `restrictionf` in degree `n` is `component`. -/
@[reassoc (attr := simp)]
lemma ι_restrictionf (n : ℕ) (i j : ℤ) (hij : i + j = (n : ℤ)) :
    ιMapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat) F (up ℤ) i j (n : ℤ) hij ≫
        restrictionf F K L n =
      component F K L n i j hij :=
  ι_mapBifunctorDesc _ i j hij

/-- The Koszul sign `(-1)^p` of [Stacks, Tag 012Z] read in `ℤ` is the one read in `ℕ`. -/
lemma ε_up_ℤ_natCast (p : ℕ) : (up ℤ).ε (p : ℤ) = (up ℕ).ε p := by
  rw [ε_up_ℤ]
  show Int.negOnePow (p : ℤ) = (-1 : ℤˣ) ^ p
  ext
  rw [Int.coe_negOnePow_natCast]
  push_cast
  rfl

/-- **The comparison as a morphism of `ℕ`-indexed complexes** out of the restriction of the
`ℤ`-indexed total complex of the two extensions. -/
def restrictionHom :
    (mapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat) F (up ℤ)).restriction
        embeddingUpNat ⟶ mapBifunctor K L F (up ℕ) where
  f n := restrictionf F K L n
  comm' m m' hmm' := by
    obtain rfl : m + 1 = m' := hmm'
    change restrictionf F K L m ≫ (mapBifunctor K L F (up ℕ)).d m (m + 1) =
      (mapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat) F (up ℤ)).d (m : ℤ)
          ((m + 1 : ℕ) : ℤ) ≫ restrictionf F K L (m + 1)
    refine mapBifunctor.hom_ext fun i j hij => ?_
    have hij' : i + j = (m : ℤ) := hij
    by_cases h : 0 ≤ i ∧ 0 ≤ j
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, (p : ℤ) = i := ⟨i.toNat, Int.toNat_of_nonneg h.1⟩
      obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = j := ⟨j.toNat, Int.toNat_of_nonneg h.2⟩
      have hpq : p + q = m := by omega
      simp only [ι_restrictionf_assoc, component_natCast, mapBifunctor.d_eq,
        Preadditive.comp_add, Preadditive.add_comp, Category.assoc, mapBifunctor.ι_D₁,
        mapBifunctor.ι_D₂, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
      rw [mapBifunctor.d₁_eq K L F (up ℕ) (show (up ℕ).Rel p (p + 1) from rfl) q (m + 1)
          (by dsimp; omega),
        mapBifunctor.d₂_eq K L F (up ℕ) p (show (up ℕ).Rel q (q + 1) from rfl) (m + 1)
          (by dsimp; omega),
        mapBifunctor.d₁_eq _ _ F (up ℤ)
          (show (up ℤ).Rel (p : ℤ) ((p + 1 : ℕ) : ℤ) by simp) (q : ℤ)
          ((m + 1 : ℕ) : ℤ) (by dsimp; omega),
        mapBifunctor.d₂_eq _ _ F (up ℤ) (p : ℤ)
          (show (up ℤ).Rel (q : ℤ) ((q + 1 : ℕ) : ℤ) by simp)
          ((m + 1 : ℕ) : ℤ) (by dsimp; omega)]
      have e₁ : ComplexShape.ε₁ (up ℕ) (up ℕ) (up ℕ) (p, q) = 1 := rfl
      have e₁' : ComplexShape.ε₁ (up ℤ) (up ℤ) (up ℤ) ((p : ℤ), (q : ℤ)) = 1 := rfl
      have e₂ : ComplexShape.ε₂ (up ℤ) (up ℤ) (up ℤ) ((p : ℤ), (q : ℤ)) =
          ComplexShape.ε₂ (up ℕ) (up ℕ) (up ℕ) (p, q) := ε_up_ℤ_natCast p
      rw [e₁, e₁', e₂, one_smul, one_smul]
      simp only [Units.smul_def, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc,
        ι_restrictionf, component_natCast]
      congr 1
      · rw [extend_d_eq K embeddingUpNat (i := p) (j := p + 1) (by simp) (by simp)]
        simp only [Category.assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp, Iso.inv_hom_id,
          Category.comp_id]
        simp only [NatTrans.comp_app, Category.assoc, NatTrans.naturality_assoc, Functor.map_comp]
      · congr 1
        rw [extend_d_eq L embeddingUpNat (i := q) (j := q + 1) (by simp) (by simp)]
        simp only [Functor.map_comp, Category.assoc, NatTrans.naturality_assoc,
          Iso.map_inv_hom_id_assoc]
    · rw [ι_restrictionf_assoc, component_neg F K L m i j hij h, zero_comp]
      exact ((isZero_summand F K L i j (by omega)).eq_of_src _ _).symm

/-- The component of `restrictionHom` in degree `n` is `restrictionf`. -/
lemma restrictionHom_f (n : ℕ) : (restrictionHom F K L).f n = restrictionf F K L n := rfl

/-- The comparison `restrictionHom` lifts to the extension by zero along `embeddingUpNat`. -/
lemma hasLift_restrictionHom : embeddingUpNat.HasLift (restrictionHom F K L) := by
  intro j hj i' hi'
  by_cases h : 0 ≤ i'
  · exact absurd (Int.toNat_of_nonneg h) (hj.notMem hi' i'.toNat)
  · refine mapBifunctor.hom_ext fun a b hab => ?_
    rw [comp_zero]
    have hab' : a + b = i' := hab
    exact (isZero_summand F K L a b (by omega)).eq_of_src _ _

end MapBifunctorExtend

open MapBifunctorExtend

variable (K : CochainComplex C₁ ℕ) (L : CochainComplex C₂ ℕ) [HasMapBifunctor K L F (up ℕ)]
  [HasMapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat) F (up ℤ)]

/-- **The comparison `Tot(F(K.extend, L.extend)) ⟶ Tot(F(K, L)).extend`** between the `ℤ`-indexed
total complex of the extensions by zero of two `ℕ`-indexed complexes and the extension by zero of
their `ℕ`-indexed total complex. On a summand `F(K^p, L^q)` with `p, q ≥ 0` it is the inclusion of
the summand of the same bidegree. -/
def mapBifunctorExtendHom :
    mapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat) F (up ℤ) ⟶
      (mapBifunctor K L F (up ℕ)).extend embeddingUpNat :=
  embeddingUpNat.liftExtend (restrictionHom F K L) (hasLift_restrictionHom F K L)

/-- On the summand `F(K^p, L^q)` the comparison is the inclusion of the summand of the same
bidegree, read through the identifications of the extensions in nonnegative degrees. -/
@[reassoc]
lemma ι_mapBifunctorExtendHom_f (n p q : ℕ) (h : (p : ℤ) + (q : ℤ) = (n : ℤ)) :
    ιMapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat) F (up ℤ) p q (n : ℤ) h ≫
        (mapBifunctorExtendHom F K L).f (n : ℤ) =
      (F.map (K.extendXIso embeddingUpNat (i' := (p : ℤ)) (i := p) (by simp)).hom).app _ ≫
        (F.obj (K.X p)).map (L.extendXIso embeddingUpNat (i' := (q : ℤ)) (i := q) (by simp)).hom ≫
        ιMapBifunctor K L F (up ℕ) p q n (by dsimp; omega) ≫
        ((mapBifunctor K L F (up ℕ)).extendXIso embeddingUpNat (i' := (n : ℤ)) (i := n)
          (by simp)).inv := by
  have hX : ((mapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat) F
      (up ℤ)).restrictionXIso embeddingUpNat (i := n) (i' := (n : ℤ)) (by simp)).inv ≫
        (restrictionHom F K L).f n = restrictionf F K L n :=
    Category.id_comp _
  rw [mapBifunctorExtendHom, embeddingUpNat.liftExtend_f _ _ (i' := (n : ℤ)) (i := n) (by simp),
    reassoc_of% hX, ι_restrictionf_assoc, component_natCast]
  simp only [Category.assoc]

/-- On a summand with a negative index the comparison vanishes. -/
@[reassoc]
lemma ι_mapBifunctorExtendHom_f_eq_zero (n i j : ℤ) (h : i + j = n) (h' : i < 0 ∨ j < 0) :
    ιMapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat) F (up ℤ) i j n h ≫
        (mapBifunctorExtendHom F K L).f n = 0 :=
  (isZero_summand F K L i j h').eq_of_src _ _

variable {F} {K L} {K' : CochainComplex C₁ ℕ} {L' : CochainComplex C₂ ℕ}
  [HasMapBifunctor K' L' F (up ℕ)]
  [HasMapBifunctor (K'.extend embeddingUpNat) (L'.extend embeddingUpNat) F (up ℤ)]

/-- **The comparison is natural in both complexes.** -/
@[reassoc]
theorem mapBifunctorExtendHom_naturality (f : K ⟶ K') (g : L ⟶ L') :
    mapBifunctorMap (extendMap f embeddingUpNat) (extendMap g embeddingUpNat) F (up ℤ) ≫
        mapBifunctorExtendHom F K' L' =
      mapBifunctorExtendHom F K L ≫ extendMap (mapBifunctorMap f g F (up ℕ)) embeddingUpNat := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine mapBifunctor.hom_ext fun i j hij => ?_
    have hij' : i + j = (m : ℤ) := hij
    simp only [comp_f]
    by_cases h : 0 ≤ i ∧ 0 ≤ j
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
      obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le h.2
      rw [ι_mapBifunctorMap_assoc, ι_mapBifunctorExtendHom_f, ι_mapBifunctorExtendHom_f_assoc,
        extendMap_f _ embeddingUpNat (i := p) (i' := (p : ℤ)) (by simp),
        extendMap_f _ embeddingUpNat (i := q) (i' := (q : ℤ)) (by simp),
        extendMap_f _ embeddingUpNat (i := m) (i' := (m : ℤ)) (by simp)]
      simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_assoc,
        Iso.map_inv_hom_id_app_assoc, Iso.map_inv_hom_id_assoc, ι_mapBifunctorMap_assoc,
        NatTrans.naturality_assoc]
    · rw [ι_mapBifunctorExtendHom_f_eq_zero_assoc F K L _ i j hij (by omega), zero_comp,
        ι_mapBifunctorMap_assoc, ι_mapBifunctorExtendHom_f_eq_zero F K' L' _ i j hij (by omega),
        comp_zero, comp_zero]
  · exact (isZero_extend_X_of_neg _ n (not_le.1 hn)).eq_of_tgt _ _

end HomologicalComplex

end
