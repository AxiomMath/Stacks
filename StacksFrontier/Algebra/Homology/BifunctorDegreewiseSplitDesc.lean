module

public import Mathlib.Algebra.Homology.Bifunctor
public import StacksFrontier.Algebra.Homology.StupidTruncationLE

/-!
# Descent along degreewise split epimorphisms of total complexes

Let `P : A ⟶ B` be a morphism of complexes with sections `s k : B^k ⟶ A^k` of each `P^k`, not
assumed to commute with the differentials. A morphism of complexes `φ : A ⟶ M` which is
unchanged by the idempotents `P^k ∘ s^k` of `A^k` factors as `φ = P ≫ γ` with `γ^k = s^k ≫ φ^k`,
and `γ` is a morphism of complexes (`HomologicalComplex.descOfSection`).

For a bifunctor `F` and morphisms of complexes `f₁ : K₁ ⟶ L₁`, `f₂ : K₂ ⟶ L₂` with degreewise
sections, the induced map of total complexes `Tot(F(K₁, K₂)) ⟶ Tot(F(L₁, L₂))` has the sections
assembled from them on the summands (`HomologicalComplex.mapBifunctorMapSection`). Applied to the
projection `K ⟶ σ^{≤p}K` onto a stupid truncation, whose components are isomorphisms in degrees
`≤ p` and maps to zero objects above `p`, this gives the factorisation of a map
`Tot(F(K, L)) ⟶ M` through `Tot(F(σ^{≤p}K, L))` as soon as it vanishes on the summands
`F(K^i, L^j)` with `i > p` (`StacksDraft.StupidTruncation.truncLEDesc`).

This is how the multiplication `Tot(Ω^• ⊗ σ_{≥n-p}Ω^•) ⟶ Ω^•` of the de Rham complex of a
morphism of relative dimension `n` factors through `Tot(σ_{≤p}Ω^• ⊗ σ_{≥n-p}Ω^•)` in the proof
of [Stacks, Tag 0G8K]: it vanishes on the summands `Ω^i ⊗ Ω^j` with `i > p`, `j ≥ n - p` for
degree reasons.

## Main definitions

* `HomologicalComplex.descOfSection`: descent along a degreewise split epimorphism.
* `HomologicalComplex.mapBifunctorMapSection`: the sections of a map of total complexes.
* `StacksDraft.StupidTruncation.truncLEDesc`: the factorisation through `Tot(F(σ^{≤p}K, L))`.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

section DescOfSection

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  {A B M : HomologicalComplex C c} (P : A ⟶ B) (s : ∀ k, B.X k ⟶ A.X k)
  (hs : ∀ k, s k ≫ P.f k = 𝟙 _) (φ : A ⟶ M) (hφ : ∀ k, P.f k ≫ s k ≫ φ.f k = φ.f k)

/-- **Descent along a degreewise split epimorphism.** For `P : A ⟶ B` with degreewise sections
`s` and a morphism of complexes `φ : A ⟶ M` unchanged by the idempotents `P^k ∘ s^k`, the
morphism of complexes `B ⟶ M` with components `s^k ≫ φ^k`. -/
def descOfSection : B ⟶ M where
  f k := s k ≫ φ.f k
  comm' i j _ := by
    calc (s i ≫ φ.f i) ≫ M.d i j = s i ≫ A.d i j ≫ P.f j ≫ s j ≫ φ.f j := by
          rw [hφ j, Category.assoc, Hom.comm]
      _ = B.d i j ≫ s j ≫ φ.f j := by
          rw [← Hom.comm_assoc, reassoc_of% (hs i)]

/-- The components of `descOfSection P s hs φ hφ` are `s^k ≫ φ^k`. -/
theorem descOfSection_f (k : ι) : (descOfSection P s hs φ hφ).f k = s k ≫ φ.f k :=
  rfl

/-- The morphism `descOfSection P s hs φ hφ` satisfies `P ≫ descOfSection P s hs φ hφ = φ`. -/
@[reassoc (attr := simp)]
theorem comp_descOfSection : P ≫ descOfSection P s hs φ hφ = φ := by
  ext k
  exact hφ k

include hs in
/-- A morphism of complexes with degreewise sections is an epimorphism. -/
theorem epi_of_section : Epi P :=
  epi_of_epi_f P fun k => (IsSplitEpi.mk' ⟨s k, hs k⟩).epi

end DescOfSection

section MapBifunctor

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  {K₁ L₁ : HomologicalComplex C₁ c₁} {K₂ L₂ : HomologicalComplex C₂ c₂}
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]
  (s₁ : ∀ i, L₁.X i ⟶ K₁.X i) (s₂ : ∀ i, L₂.X i ⟶ K₂.X i)

/-- **The sections of a map of total complexes** assembled from degreewise sections `s₁`, `s₂`
of `f₁` and `f₂`: on the summand `F(L₁^{i₁}, L₂^{i₂})` it is `F(s₁, s₂)` followed by the inclusion
of `F(K₁^{i₁}, K₂^{i₂})`. -/
def mapBifunctorMapSection (j : J) :
    (mapBifunctor L₁ L₂ F c).X j ⟶ (mapBifunctor K₁ K₂ F c).X j :=
  mapBifunctorDesc fun i₁ i₂ h => (F.map (s₁ i₁)).app (L₂.X i₂) ≫
    (F.obj (K₁.X i₁)).map (s₂ i₂) ≫ ιMapBifunctor K₁ K₂ F c i₁ i₂ j h

/-- On the summand `F(L₁^{i₁}, L₂^{i₂})`, `mapBifunctorMapSection F c s₁ s₂` is `F(s₁, s₂)`
followed by the inclusion of `F(K₁^{i₁}, K₂^{i₂})`. -/
@[reassoc (attr := simp)]
theorem ι_mapBifunctorMapSection (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctor L₁ L₂ F c i₁ i₂ j h ≫ mapBifunctorMapSection F c s₁ s₂ j =
      (F.map (s₁ i₁)).app (L₂.X i₂) ≫ (F.obj (K₁.X i₁)).map (s₂ i₂) ≫
        ιMapBifunctor K₁ K₂ F c i₁ i₂ j h :=
  ι_mapBifunctorDesc _ _ _ _

/-- Degreewise sections of `f₁` and `f₂` give degreewise sections of the map of total
complexes. -/
theorem mapBifunctorMapSection_comp (hs₁ : ∀ i, s₁ i ≫ f₁.f i = 𝟙 _)
    (hs₂ : ∀ i, s₂ i ≫ f₂.f i = 𝟙 _) (j : J) :
    mapBifunctorMapSection F c s₁ s₂ j ≫ (mapBifunctorMap f₁ f₂ F c).f j = 𝟙 _ := by
  ext i₁ i₂ h
  rw [ι_mapBifunctorMapSection_assoc, ι_mapBifunctorMap, Category.comp_id,
    NatTrans.naturality_assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp, hs₁,
    ← Functor.map_comp_assoc, hs₂]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- The idempotent `P ∘ s` of `Tot(F(K₁, K₂))`, for `P` the map of total complexes and `s` its
sections, acts on the summand `F(K₁^{i₁}, K₂^{i₂})` by `F(f₁ ∘ s₁, f₂ ∘ s₂)`. -/
@[reassoc]
theorem ι_mapBifunctorMap_f_comp_mapBifunctorMapSection (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ (mapBifunctorMap f₁ f₂ F c).f j ≫
        mapBifunctorMapSection F c s₁ s₂ j =
      (F.map (f₁.f i₁ ≫ s₁ i₁)).app (K₂.X i₂) ≫ (F.obj (K₁.X i₁)).map (f₂.f i₂ ≫ s₂ i₂) ≫
        ιMapBifunctor K₁ K₂ F c i₁ i₂ j h := by
  rw [ι_mapBifunctorMap_assoc, ι_mapBifunctorMapSection, NatTrans.naturality_assoc,
    ← NatTrans.comp_app_assoc, ← Functor.map_comp, ← Functor.map_comp_assoc]

end MapBifunctor

end HomologicalComplex

namespace StacksDraft.StupidTruncation

open HomologicalComplex ComplexShape

section TruncLE

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroObject C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ) (p : ℤ)
  [HasMapBifunctor K L F (up ℤ)] [HasMapBifunctor (K.stupidTrunc (embeddingUpIntLE p)) L F (up ℤ)]

open Classical in
/-- The degreewise sections of the projection `K ⟶ σ^{≤p}K`: the identification of terms in
degrees `≤ p` and zero above `p`, where `σ^{≤p}K` vanishes. -/
def πStupidTruncLESection (i : ℤ) : (K.stupidTrunc (embeddingUpIntLE p)).X i ⟶ K.X i :=
  if h : i ≤ p then (stupidTruncLEXIso K p i h).hom else 0

/-- In degrees `i ≤ p`, the section `πStupidTruncLESection K p i` is the identification
`stupidTruncLEXIso K p i h` of `(σ^{≤p}K)^i` with `K^i`. -/
theorem πStupidTruncLESection_of_le (i : ℤ) (h : i ≤ p) :
    πStupidTruncLESection K p i = (stupidTruncLEXIso K p i h).hom :=
  dif_pos h

/-- In degrees `i > p`, the section `πStupidTruncLESection K p i` is zero. -/
theorem πStupidTruncLESection_of_lt (i : ℤ) (h : p < i) : πStupidTruncLESection K p i = 0 :=
  dif_neg (by omega)

/-- In degrees `i ≤ p`, the projection `K ⟶ σ^{≤p}K` is the inverse of the identification
`stupidTruncLEXIso K p i h`. -/
theorem πStupidTruncLE_f_of_le (i : ℤ) (h : i ≤ p) :
    (K.πStupidTrunc (embeddingUpIntLE p)).f i = (stupidTruncLEXIso K p i h).inv :=
  πStupidTrunc_f K (embeddingUpIntLE p) _

/-- `πStupidTruncLESection K p i` is a section of the projection `K^i ⟶ (σ^{≤p}K)^i`. -/
theorem πStupidTruncLESection_comp (i : ℤ) :
    πStupidTruncLESection K p i ≫ (K.πStupidTrunc (embeddingUpIntLE p)).f i = 𝟙 _ := by
  by_cases h : i ≤ p
  · rw [πStupidTruncLESection_of_le K p i h, πStupidTruncLE_f_of_le K p i h, Iso.hom_inv_id]
  · exact (CochainComplex.isZero_of_isStrictlyLE (K.stupidTrunc (embeddingUpIntLE p)) p i
      (by omega)).eq_of_src _ _

/-- In degrees `i ≤ p`, `πStupidTruncLESection K p i` is also a retraction of the projection
`K^i ⟶ (σ^{≤p}K)^i`. -/
theorem πStupidTruncLE_f_comp_section_of_le (i : ℤ) (h : i ≤ p) :
    (K.πStupidTrunc (embeddingUpIntLE p)).f i ≫ πStupidTruncLESection K p i = 𝟙 _ := by
  rw [πStupidTruncLESection_of_le K p i h, πStupidTruncLE_f_of_le K p i h, Iso.inv_hom_id]

variable {K L p} in
/-- The section of `Tot(F(K, L)) ⟶ Tot(F(σ^{≤p}K, L))` composed with a map out of `Tot(F(K, L))`
vanishing on the summands `F(K^i, L^j)` with `i > p` gives back the map. -/
theorem mapBifunctorMap_πStupidTrunc_f_comp_section {M : CochainComplex D ℤ}
    (g : mapBifunctor K L F (up ℤ) ⟶ M)
    (hg : ∀ (i j k : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k), p < i →
      ιMapBifunctor K L F (up ℤ) i j k h ≫ g.f k = 0) (k : ℤ) :
    (mapBifunctorMap (K.πStupidTrunc (embeddingUpIntLE p)) (𝟙 L) F (up ℤ)).f k ≫
        mapBifunctorMapSection F (up ℤ) (πStupidTruncLESection K p) (fun j => 𝟙 (L.X j)) k ≫
          g.f k = g.f k := by
  ext i j h
  rw [ι_mapBifunctorMap_f_comp_mapBifunctorMapSection_assoc]
  by_cases hi : i ≤ p
  · rw [πStupidTruncLE_f_comp_section_of_le K p i hi]
    simp
  · rw [πStupidTruncLESection_of_lt K p i (by omega), hg i j k h (by omega)]
    simp

/-- **The factorisation through `Tot(F(σ^{≤p}K, L))`** of a map `g : Tot(F(K, L)) ⟶ M`
vanishing on the summands `F(K^i, L^j)` with `i > p`: the unique map `γ` with
`Tot(F(π, 1)) ≫ γ = g`, `π : K ⟶ σ^{≤p}K` the projection. -/
def truncLEDesc {M : CochainComplex D ℤ} (g : mapBifunctor K L F (up ℤ) ⟶ M)
    (hg : ∀ (i j k : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k), p < i →
      ιMapBifunctor K L F (up ℤ) i j k h ≫ g.f k = 0) :
    mapBifunctor (K.stupidTrunc (embeddingUpIntLE p)) L F (up ℤ) ⟶ M :=
  descOfSection (mapBifunctorMap (K.πStupidTrunc (embeddingUpIntLE p)) (𝟙 L) F (up ℤ))
    (mapBifunctorMapSection F (up ℤ) (πStupidTruncLESection K p) fun j => 𝟙 (L.X j))
    (mapBifunctorMapSection_comp _ _ F (up ℤ) _ _ (πStupidTruncLESection_comp K p)
      fun _ => Category.id_comp _) g
    (mapBifunctorMap_πStupidTrunc_f_comp_section F g hg)

variable {K L p}

/-- The factorisation `truncLEDesc F K L p g hg` composed after `Tot(F(π, 1))`, for
`π : K ⟶ σ^{≤p}K` the projection, is `g`. -/
@[reassoc (attr := simp)]
theorem mapBifunctorMap_πStupidTrunc_truncLEDesc {M : CochainComplex D ℤ}
    (g : mapBifunctor K L F (up ℤ) ⟶ M)
    (hg : ∀ (i j k : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k), p < i →
      ιMapBifunctor K L F (up ℤ) i j k h ≫ g.f k = 0) :
    mapBifunctorMap (K.πStupidTrunc (embeddingUpIntLE p)) (𝟙 L) F (up ℤ) ≫
      truncLEDesc F K L p g hg = g :=
  comp_descOfSection _ _ _ _ _

/-- On a summand `F((σ^{≤p}K)^i, L^j)` with `i ≤ p`, the factorisation is the identification of
`(σ^{≤p}K)^i` with `K^i` followed by `g` on the summand `F(K^i, L^j)`. -/
theorem ι_truncLEDesc_f {M : CochainComplex D ℤ} (g : mapBifunctor K L F (up ℤ) ⟶ M)
    (hg : ∀ (i j k : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k), p < i →
      ιMapBifunctor K L F (up ℤ) i j k h ≫ g.f k = 0)
    (i j k : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = k) (hi : i ≤ p) :
    ιMapBifunctor (K.stupidTrunc (embeddingUpIntLE p)) L F (up ℤ) i j k h ≫
        (truncLEDesc F K L p g hg).f k =
      (F.map (stupidTruncLEXIso K p i hi).hom).app (L.X j) ≫
        ιMapBifunctor K L F (up ℤ) i j k h ≫ g.f k := by
  rw [truncLEDesc, descOfSection_f, ι_mapBifunctorMapSection_assoc,
    πStupidTruncLESection_of_le K p i hi, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The map `Tot(F(K, L)) ⟶ Tot(F(σ^{≤p}K, L))` induced by the projection is an epimorphism. -/
theorem epi_mapBifunctorMap_πStupidTrunc :
    Epi (mapBifunctorMap (K.πStupidTrunc (embeddingUpIntLE p)) (𝟙 L) F (up ℤ)) :=
  epi_of_section _ _ (mapBifunctorMapSection_comp _ _ F (up ℤ) _ _
    (πStupidTruncLESection_comp K p) fun _ => Category.id_comp _)

end TruncLE

end StacksDraft.StupidTruncation
