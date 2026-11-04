module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import StacksFrontier.AlgebraicGeometry.Crystalline.AlphaPCoverCohomologyBound

/-!
# Annihilating the mapping cone of a morphism split up to a scalar

Let `c : K ⟶ L` be a morphism of cochain complexes, `a : ℤ`, and suppose that there is a
morphism of complexes `e : L ⟶ K` with `c ≫ e = a • 𝟙 K`, together with a homotopy `h`
from `a • 𝟙 L` to `e ≫ c` such that `c ≫ h = 0`.  Then `a • 𝟙` of the mapping cone of `c`
is null-homotopic: on `mappingCone c = K[1] ⊕ L` the null-homotopy is `(x, y) ↦ (e y, h y)`.
Consequently `a` annihilates every cone of `c` in the derived category, and, by the octahedron
axiom, `a ^ n` annihilates every cone of a composite of `n` such morphisms.

## Main definitions and results

* `Stacks.SplitCone.Data c a`: the data `(e, h)` above, with `h` a cochain of degree `-1`.
* `Stacks.SplitCone.Data.ofHomotopy`: the same data from a `Homotopy (a • 𝟙 L) (e ≫ c)`.
* `Stacks.SplitCone.Data.homotopy`: the null-homotopy `Homotopy (a • 𝟙 (mappingCone c)) 0`.
* `Stacks.SplitCone.Data.smul_id_Q_obj_mappingCone_eq_zero`: `a • 𝟙` vanishes on the image of
  `mappingCone c` in the derived category.
* `Stacks.SplitCone.Data.smul_id_eq_zero_of_distinguished`: `a` annihilates the third term of
  every distinguished triangle on `Q.map c`.
* `Stacks.SplitCone.smul_id_eq_zero_of_arrowIso`: the cone annihilation property transported
  along an isomorphism of arrows.
* `Stacks.SplitCone.mul_smul_id_eq_zero_of_comp_Q`: `a * b` annihilates every cone of a
  composite of a morphism split up to `a` and one split up to `b` (the octahedron axiom, through
  `Stacks.Triangulated.mul_smul_id_eq_zero_of_comp`).
* `Stacks.SplitCone.pow_smul_id_eq_zero_of_chainComp_Q`: `a ^ n` annihilates every cone of the
  composite of a chain of `n` such morphisms.
* `Stacks.SplitCone.Data.extendNat`: the data for `ℕ`-indexed complexes, transported to their
  extensions to `ℤ`-indexed complexes, and `smul_id_eq_zero_of_distinguished_extendNat`, the
  resulting annihilation of the cones in the derived category.
-/

@[expose] public section

open CategoryTheory Category Limits Preadditive Pretriangulated CochainComplex
  CochainComplex.HomComplex

namespace Stacks.SplitCone

section Cone

variable {C : Type*} [Category* C] [Preadditive C] {K L : CochainComplex C ℤ}

/-- `Cochain.ofHom` commutes with integer scalar multiplication. -/
lemma ofHom_zsmul_eq {F G : CochainComplex C ℤ} (a : ℤ) (f : F ⟶ G) :
    Cochain.ofHom (a • f) = a • Cochain.ofHom f := by
  ext p
  simp

/-- The data splitting `c : K ⟶ L` up to the scalar `a`: a morphism `e : L ⟶ K` with
`c ≫ e = a • 𝟙 K` and a cochain `h` of degree `-1` on `L` with `δ h = a • 𝟙 L - e ≫ c`
(that is, `h` is a homotopy from `a • 𝟙 L` to `e ≫ c`, see `Cochain.equivHomotopy`) and
`c ≫ h = 0`. -/
structure Data (c : K ⟶ L) (a : ℤ) where
  /-- The splitting of `c` up to `a`. -/
  e : L ⟶ K
  /-- The homotopy from `a • 𝟙 L` to `e ≫ c`. -/
  h : Cochain L L (-1)
  /-- `e` splits `c` up to `a`. -/
  comp_e : c ≫ e = a • 𝟙 K
  /-- `h` is a homotopy from `a • 𝟙 L` to `e ≫ c`. -/
  δ_h : δ (-1) 0 h = Cochain.ofHom (a • 𝟙 L) - Cochain.ofHom (e ≫ c)
  /-- `c ≫ h = 0`. -/
  comp_h : (Cochain.ofHom c).comp h (zero_add _) = 0

variable {c : K ⟶ L} {a : ℤ}

/-- The data `Data c a` from a morphism `e`, a `Homotopy (a • 𝟙 L) (e ≫ c)` and the vanishing
of `c ≫ h` degreewise. -/
@[simps]
noncomputable def Data.ofHomotopy (e : L ⟶ K) (hce : c ≫ e = a • 𝟙 K)
    (ho : Homotopy (a • 𝟙 L) (e ≫ c)) (hch : ∀ i j, c.f i ≫ ho.hom i j = 0) : Data c a where
  e := e
  h := Cochain.ofHomotopy ho
  comp_e := hce
  δ_h := δ_ofHomotopy ho
  comp_h := by
    ext p q hpq
    simp [Cochain.ofHomotopy, hch]

namespace Data

variable [HomologicalComplex.HasHomotopyCofiber c] (D : Data c a)

/-- The null-homotopy of `a • 𝟙 (mappingCone c)` as a cochain of degree `-1`: on
`K[1] ⊕ L` it sends `(x, y)` to `(e y, h y)`. -/
noncomputable def cochain : Cochain (mappingCone c) (mappingCone c) (-1) :=
  (mappingCone.snd c).comp ((Cochain.ofHom D.e).comp (mappingCone.inl c) (zero_add _) +
    D.h.comp (Cochain.ofHom (mappingCone.inr c)) (add_zero _)) (zero_add _)

/-- The differential of `Data.cochain` is `a • 𝟙 (mappingCone c)`. -/
lemma δ_cochain : δ (-1) 0 D.cochain = Cochain.ofHom (a • 𝟙 (mappingCone c)) := by
  have hce : (Cochain.ofHom c).comp (Cochain.ofHom D.e) (zero_add 0) =
      a • Cochain.ofHom (𝟙 K) := by
    rw [← Cochain.ofHom_comp, D.comp_e, ofHom_zsmul_eq]
  rw [cochain, δ_zero_cochain_comp _ _ _ (neg_add_cancel 1), δ_add, δ_ofHom_comp,
    mappingCone.δ_inl, δ_comp_ofHom, D.δ_h, mappingCone.δ_snd]
  simp only [ofHom_zsmul_eq, Cochain.ofHom_comp, Cochain.sub_comp, Cochain.comp_add,
    Cochain.smul_comp, Cochain.neg_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    Cochain.comp_assoc_of_second_is_zero_cochain]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom c) (Cochain.ofHom D.e),
    hce, ← Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom c) D.h, D.comp_h]
  simp only [Cochain.comp_sub, Cochain.comp_smul, Cochain.id_comp, Cochain.zero_comp,
    Cochain.smul_comp, Cochain.comp_zero, neg_zero, add_zero,
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul, neg_neg]
  rw [← mappingCone.id, smul_add]
  abel

/-- **`a • 𝟙` of the mapping cone is null-homotopic.** -/
noncomputable def homotopy : Homotopy (a • 𝟙 (mappingCone c)) 0 :=
  (Cochain.equivHomotopy _ _).symm ⟨D.cochain, by rw [D.δ_cochain, Cochain.ofHom_zero, add_zero]⟩

end Data

end Cone

section Triangulated

variable {𝒯 : Type*} [Category* 𝒯] [Preadditive 𝒯] [HasZeroObject 𝒯] [HasShift 𝒯 ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor 𝒯 n).Additive] [Pretriangulated 𝒯]

omit [HasZeroObject 𝒯] [HasShift 𝒯 ℤ] [∀ (n : ℤ), (CategoryTheory.shiftFunctor 𝒯 n).Additive]
  [Pretriangulated 𝒯] in
/-- An integer annihilating an object annihilates every object isomorphic to it. -/
lemma smul_id_eq_zero_of_iso {X Y : 𝒯} (i : X ≅ Y) {a : ℤ} (h : a • 𝟙 X = 0) : a • 𝟙 Y = 0 := by
  have : a • 𝟙 Y = i.inv ≫ (a • 𝟙 X) ≫ i.hom := by simp
  rw [this, h, zero_comp, comp_zero]

/-- **Transport along an isomorphism of arrows.**  If `a` annihilates the third term of every
distinguished triangle on `α'`, and `α` is isomorphic to `α'` as an arrow, then `a` annihilates
the third term of every distinguished triangle on `α`. -/
theorem smul_id_eq_zero_of_arrowIso {A B A' B' : 𝒯} {α : A ⟶ B} {α' : A' ⟶ B'}
    (φ : Arrow.mk α ≅ Arrow.mk α') (a : ℤ)
    (hα' : ∀ (Z : 𝒯) (v : B' ⟶ Z) (w : Z ⟶ A'⟦(1 : ℤ)⟧),
      Triangle.mk α' v w ∈ distTriang 𝒯 → a • 𝟙 Z = 0)
    {Z : 𝒯} (v : B ⟶ Z) (w : Z ⟶ A⟦(1 : ℤ)⟧) (hZ : Triangle.mk α v w ∈ distTriang 𝒯) :
    a • 𝟙 Z = 0 := by
  obtain ⟨Z', v', w', hZ'⟩ := distinguished_cocone_triangle α'
  obtain ⟨i, -⟩ := exists_iso_of_arrow_iso _ _ hZ hZ' φ
  exact smul_id_eq_zero_of_iso (Triangle.π₃.mapIso i).symm (hα' Z' v' w' hZ')

end Triangulated

section Derived

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {K L : CochainComplex C ℤ} {c : K ⟶ L} {a : ℤ}

namespace Data

/-- **`a` annihilates the mapping cone of `c` in the derived category.** -/
theorem smul_id_Q_obj_mappingCone_eq_zero (D : Data c a) :
    a • 𝟙 (DerivedCategory.Q.obj (mappingCone c)) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_zsmul,
    DerivedCategory.Q_map_eq_of_homotopy _ D.homotopy, Functor.map_zero]

/-- **`a` annihilates every cone of `Q.map c`.**  For every distinguished triangle
`Q.obj K ⟶ Q.obj L ⟶ Z ⟶ (Q.obj K)⟦1⟧` in the derived category whose first morphism is
`Q.map c`, `a • 𝟙 Z = 0`. -/
theorem smul_id_eq_zero_of_distinguished (D : Data c a) {Z : DerivedCategory C}
    (v : DerivedCategory.Q.obj L ⟶ Z) (w : Z ⟶ (DerivedCategory.Q.obj K)⟦(1 : ℤ)⟧)
    (hZ : Triangle.mk (DerivedCategory.Q.map c) v w ∈ distTriang _) :
    a • 𝟙 Z = 0 := by
  obtain ⟨i, -⟩ := exists_iso_of_arrow_iso _ _
    (DerivedCategory.mappingCone_triangle_distinguished c) hZ (Iso.refl _)
  exact smul_id_eq_zero_of_iso (Triangle.π₃.mapIso i) D.smul_id_Q_obj_mappingCone_eq_zero

end Data

/-- **The iterated version.**  Let `Y 0 ⟶ Y 1 ⟶ ⋯` be a chain of morphisms of cochain complexes
each of which is split up to `a` (`D i : Data (g i) a`).  Then `a ^ n` annihilates the third term
of every distinguished triangle in the derived category on the composite of the images of the
first `n` stages. -/
theorem pow_smul_id_eq_zero_of_chainComp_Q (Y : ℕ → CochainComplex C ℤ)
    (g : ∀ i : ℕ, Y i ⟶ Y (i + 1)) (D : ∀ i, Data (g i) a) (n : ℕ)
    {Z : DerivedCategory C}
    (v : DerivedCategory.Q.obj (Y n) ⟶ Z) (w : Z ⟶ (DerivedCategory.Q.obj (Y 0))⟦(1 : ℤ)⟧)
    (hZ : Triangle.mk (Stacks.Triangulated.chainComp (fun i ↦ DerivedCategory.Q.obj (Y i))
      (fun i ↦ DerivedCategory.Q.map (g i)) n) v w ∈ distTriang _) :
    a ^ n • 𝟙 Z = 0 :=
  Stacks.Triangulated.pow_smul_id_eq_zero_of_chainComp _ _ a
    (fun i _ v w hT ↦ (D i).smul_id_eq_zero_of_distinguished v w hT) n v w hZ

/-- **The composite of two split morphisms.**  If `c` is split up to `a` and `c'` up to `b`,
then `a * b` annihilates every cone of `Q.map (c ≫ c')` in the derived category. -/
theorem mul_smul_id_eq_zero_of_comp_Q {M : CochainComplex C ℤ} {c' : L ⟶ M} {b : ℤ}
    (D : Data c a) (D' : Data c' b) {Z : DerivedCategory C}
    (v : DerivedCategory.Q.obj M ⟶ Z) (w : Z ⟶ (DerivedCategory.Q.obj K)⟦(1 : ℤ)⟧)
    (hZ : Triangle.mk (DerivedCategory.Q.map (c ≫ c')) v w ∈ distTriang _) :
    (a * b) • 𝟙 Z = 0 :=
  Stacks.Triangulated.mul_smul_id_eq_zero_of_comp _ _ a b
    (fun _ v w hT ↦ D.smul_id_eq_zero_of_distinguished v w hT)
    (fun _ v w hT ↦ D'.smul_id_eq_zero_of_distinguished v w hT) v w
    (by simpa only [Functor.map_comp] using hZ)

end Derived

section Nat

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  {K L : CochainComplex C ℕ} {c : K ⟶ L} {a : ℤ}

/-- The extension of `a • 𝟙 M` along `ℕ → ℤ` is `a • 𝟙` of the extension. -/
lemma extendMap_zsmul_id (M : CochainComplex C ℕ) (a : ℤ) :
    HomologicalComplex.extendMap (a • 𝟙 M) ComplexShape.embeddingUpNat = a • 𝟙 _ := by
  ext i'
  by_cases hi : ∃ i, ComplexShape.embeddingUpNat.f i = i'
  · obtain ⟨i, hi⟩ := hi
    simp [HomologicalComplex.extendMap_f _ _ hi]
  · exact (M.isZero_extend_X _ i' (by tauto)).eq_of_src _ _

/-- **The `ℕ`-indexed case.**  A morphism `c : K ⟶ L` of `ℕ`-indexed cochain complexes with
`e : L ⟶ K`, `c ≫ e = a • 𝟙 K`, a homotopy `ho` from `a • 𝟙 L` to `e ≫ c` (so
`ho.hom (n + 1) n : L.X (n + 1) ⟶ L.X n`) and `c ≫ ho = 0` degreewise, gives the splitting
data of its extension `extendMap c embeddingUpNat` to `ℤ`-indexed complexes (which is
`(embeddingUpNat.extendFunctor C).map c` by definition). -/
noncomputable def Data.extendNat (e : L ⟶ K) (hce : c ≫ e = a • 𝟙 K)
    (ho : Homotopy (a • 𝟙 L) (e ≫ c)) (hch : ∀ i j, c.f i ≫ ho.hom i j = 0) :
    Data (HomologicalComplex.extendMap c ComplexShape.embeddingUpNat) a where
  e := HomologicalComplex.extendMap e ComplexShape.embeddingUpNat
  h := Cochain.ofHomotopy (ho.extend ComplexShape.embeddingUpNat)
  comp_e := by rw [← HomologicalComplex.extendMap_comp, hce, extendMap_zsmul_id]
  δ_h := by
    rw [δ_ofHomotopy, extendMap_zsmul_id, HomologicalComplex.extendMap_comp]
  comp_h := by
    ext i' j' hij
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v, Cochain.ofHomotopy,
      Cochain.mk_v]
    by_cases hi : ∃ i, ComplexShape.embeddingUpNat.f i = i'
    · obtain ⟨i, rfl⟩ := hi
      by_cases hj : ∃ j, ComplexShape.embeddingUpNat.f j = j'
      · obtain ⟨j, rfl⟩ := hj
        rw [Homotopy.extend_hom_eq _ _ rfl rfl, HomologicalComplex.extendMap_f _ _ rfl]
        simp only [assoc, Iso.inv_hom_id_assoc, reassoc_of% hch, zero_comp, comp_zero]
      · exact (L.isZero_extend_X _ j' (by tauto)).eq_of_tgt _ _
    · exact (K.isZero_extend_X _ i' (by tauto)).eq_of_src _ _

/-- **`a` annihilates every cone of the extension of an `ℕ`-indexed split morphism.**  With the
hypotheses of `Data.extendNat`, `a` annihilates the third term of every distinguished triangle
in the derived category on `Q.map (extendMap c embeddingUpNat)`. -/
theorem smul_id_eq_zero_of_distinguished_extendNat {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℕ} {c : K ⟶ L} {a : ℤ}
    (e : L ⟶ K) (hce : c ≫ e = a • 𝟙 K)
    (ho : Homotopy (a • 𝟙 L) (e ≫ c)) (hch : ∀ i j, c.f i ≫ ho.hom i j = 0)
    {Z : DerivedCategory C}
    (v : DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat) ⟶ Z)
    (w : Z ⟶ (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧)
    (hZ : Triangle.mk (DerivedCategory.Q.map
      (HomologicalComplex.extendMap c ComplexShape.embeddingUpNat)) v w ∈ distTriang _) :
    a • 𝟙 Z = 0 :=
  (Data.extendNat e hce ho hch).smul_id_eq_zero_of_distinguished v w hZ

end Nat

end Stacks.SplitCone
