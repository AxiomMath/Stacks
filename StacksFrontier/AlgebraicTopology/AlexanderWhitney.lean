module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import StacksFrontier.AlgebraicTopology.SimplexCategory.Subinterval

/-!
# The Alexander–Whitney map

Let `C` be a preadditive monoidal category in which the tensor product is additive in each
variable, and let `M` and `N` be simplicial objects of `C`. The category of simplicial objects
carries the degreewise tensor product, and the category of chain complexes carries the total
tensor product, the direct sum of the `(p, q)` terms with `p + q = n` in degree `n`, with its
signed differential. The *Alexander–Whitney map* compares the two: in degree `n` its `(p, q)`
component restricts `M` to the front `p` vertices and `N` to the back `q` vertices,

`M_n ⊗ N_n ⟶ M_p ⊗ N_q`,

and no sign is needed. The resulting degreewise map is a morphism of chain complexes.

## Main definitions

* `AlgebraicTopology.awTerm`: the `(p, q)` component of the map in degree `m`, zero unless
  `p + q = m`.
* `AlgebraicTopology.alexanderWhitney`: the morphism of chain complexes.

## Main results

* `AlgebraicTopology.alexanderWhitney_naturality_right`: the map is natural in the second
  simplicial object.
* `AlgebraicTopology.alexanderWhitney_f_zero`: in degree zero the map is the inclusion of the
  unique summand.

## Implementation notes

The summands are indexed by `Finset.antidiagonal`, which keeps every index additive: the
differential of the tensor complex moves the summand `(p + 1, q)` to `(p, q)` and the summand
`(p, q + 1)` to `(p, q)`, and `Finset.Nat.sum_antidiagonal_succ` and its primed companion
rewrite the two sums over the antidiagonal of `n + 1` as sums over the antidiagonal of `n`
without any truncated subtraction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite SimplexCategory

open scoped Simplicial

universe v u

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]

variable (M N : SimplicialObject C)

/-- The `(p, q)` component of the Alexander–Whitney map in degree `m`: the first factor is
restricted to the front `p` vertices and the second to the back `q` vertices, and the result is
included in the `(p, q)` summand of the tensor complex. It is zero unless `p + q = m`. -/
public def awTerm (m : ℕ) (x : ℕ × ℕ) :
    M _⦋m⦌ ⊗ N _⦋m⦌ ⟶
      (HomologicalComplex.tensorObj ((alternatingFaceMapComplex C).obj M)
        ((alternatingFaceMapComplex C).obj N)).X m :=
  if h : x.1 + x.2 = m then
    (M.map (subinterval (n := m) 0 x.1 (by omega)).op ⊗ₘ
        N.map (subinterval (n := m) x.1 x.2 (by omega)).op) ≫
      HomologicalComplex.ιTensorObj ((alternatingFaceMapComplex C).obj M)
        ((alternatingFaceMapComplex C).obj N) x.1 x.2 m h
  else 0

omit [HasZeroObject C] in
public lemma awTerm_eq (m : ℕ) (x : ℕ × ℕ) (h : x.1 + x.2 = m) (h₁ : 0 + x.1 ≤ m)
    (h₂ : x.1 + x.2 ≤ m) :
    awTerm M N m x =
      (M.map (subinterval (n := m) 0 x.1 h₁).op ⊗ₘ
          N.map (subinterval (n := m) x.1 x.2 h₂).op) ≫
        HomologicalComplex.ιTensorObj ((alternatingFaceMapComplex C).obj M)
        ((alternatingFaceMapComplex C).obj N) x.1 x.2 m h := by
  rw [awTerm, dite_eq_left h]

omit [HasZeroObject C] in
public lemma awTerm_eq_zero (m : ℕ) (x : ℕ × ℕ) (h : x.1 + x.2 ≠ m) :
    awTerm M N m x = 0 := by
  rw [awTerm, dite_eq_right h]


/-! ### Bookkeeping lemmas -/

variable {M N}

omit [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C] [HasZeroObject C]
  [HasFiniteCoproducts C] in
/-- A face map of a simplicial object followed by the restriction along a morphism of
`SimplexCategory` is the restriction along the composite. -/
private lemma delta_comp_map (X : SimplicialObject C) {p q : ℕ} (i : Fin (q + 2))
    (f : ⦋p⦌ ⟶ ⦋q⦌) : X.δ i ≫ X.map f.op = X.map (f ≫ δ i).op := by
  rw [SimplicialObject.δ, ← X.map_comp, ← op_comp]

omit [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C] [HasZeroObject C]
  [HasFiniteCoproducts C] in
/-- The restriction along a morphism of `SimplexCategory` followed by a face map is the
restriction along the composite. -/
private lemma map_comp_delta (X : SimplicialObject C) {p q : ℕ} (f : ⦋p + 1⦌ ⟶ ⦋q⦌)
    (i : Fin (p + 2)) : X.map f.op ≫ X.δ i = X.map (δ i ≫ f).op := by
  rw [SimplicialObject.δ, ← X.map_comp, ← op_comp]

omit [MonoidalCategory C] [MonoidalPreadditive C] [HasZeroObject C]
  [HasFiniteCoproducts C] in
/-- An integer multiple distributes over a finite sum of morphisms. -/
private lemma zsmul_finsetSum {ι : Type*} (s : Finset ι) (c : ℤ) {X Y : C} (f : ι → (X ⟶ Y)) :
    c • (∑ i ∈ s, f i) = ∑ i ∈ s, c • f i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, smul_add, ih]

omit [HasZeroObject C] [HasFiniteCoproducts C] in
private lemma zsmul_tensorHom (c : ℤ) {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    (c • f) ⊗ₘ g = c • (f ⊗ₘ g) := by
  rw [tensorHom_def, tensorHom_def, ← Preadditive.zsmul_comp]
  congr 1
  exact (tensorRight Y).map_zsmul

omit [HasZeroObject C] [HasFiniteCoproducts C] in
private lemma tensorHom_zsmul (c : ℤ) {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    f ⊗ₘ (c • g) = c • (f ⊗ₘ g) := by
  rw [tensorHom_def, tensorHom_def, ← Preadditive.comp_zsmul]
  congr 1
  exact (tensorLeft X).map_zsmul

variable (M N)


/-! ### The chain map property -/

omit [HasZeroObject C] [HasFiniteCoproducts C] in
/-- The term of the differential of the tensor complex coming from the first factor, on the
summand `(a + 1, b)`: the alternating sum of the faces of `⦋a + 1⦌`, separated into the terms
matching the faces of the degreewise tensor product below the cut and the term at the last
vertex. -/
private lemma aw_front (a b n : ℕ) (hab : a + b = n) :
    (M.map (subinterval (n := n + 1) 0 (a + 1) (by omega)).op ≫
        AlternatingFaceMapComplex.objD M a) ⊗ₘ
      N.map (subinterval (n := n + 1) (a + 1) b (by omega)).op =
      (∑ j : Fin (a + 1), (-1 : ℤ) ^ (j : ℕ) •
        (M.map ((δ j.castSucc ≫ subinterval (n := n + 1) 0 (a + 1) (by omega)).op) ⊗ₘ
          N.map (subinterval (n := n + 1) (a + 1) b (by omega)).op)) +
        (-1 : ℤ) ^ (a + 1) • (M.map (subinterval (n := n + 1) 0 a (by omega)).op ⊗ₘ
          N.map (subinterval (n := n + 1) (a + 1) b (by omega)).op) := by
  simp only [AlternatingFaceMapComplex.objD, Preadditive.comp_sum, Preadditive.comp_zsmul,
    sum_tensor, zsmul_tensorHom, map_comp_delta]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  congr 1
  rw [δ_last_comp_subinterval_zero (a := a) (by omega) (by omega) (Fin.last (a + 1)) (by simp)]

omit [HasZeroObject C] [HasFiniteCoproducts C] in
/-- The term of the differential of the tensor complex coming from the second factor, on the
summand `(a, b + 1)`: the alternating sum of the faces of `⦋b + 1⦌`, separated into the term at
the zeroth vertex and the terms matching the faces of the degreewise tensor product above the
cut. -/
private lemma aw_back (a b n : ℕ) (hab : a + b = n) :
    (-1 : ℤ) ^ a • (M.map (subinterval (n := n + 1) 0 a (by omega)).op ⊗ₘ
        (N.map (subinterval (n := n + 1) a (b + 1) (by omega)).op ≫
          AlternatingFaceMapComplex.objD N b)) =
      (-1 : ℤ) ^ a • (M.map (subinterval (n := n + 1) 0 a (by omega)).op ⊗ₘ
        N.map (subinterval (n := n + 1) (a + 1) b (by omega)).op) +
        ∑ k : Fin (b + 1), (-1 : ℤ) ^ (a + 1 + (k : ℕ)) •
        (M.map (subinterval (n := n + 1) 0 a (by omega)).op ⊗ₘ
          N.map ((δ k.succ ≫ subinterval (n := n + 1) a (b + 1) (by omega)).op)) := by
  simp only [AlternatingFaceMapComplex.objD, Preadditive.comp_sum, Preadditive.comp_zsmul,
    tensor_sum, tensorHom_zsmul, map_comp_delta]
  rw [Fin.sum_univ_succ, smul_add, zsmul_finsetSum]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, smul_smul]
  congr 1
  · rw [δ_zero_comp_subinterval (a := a) (b := b) (by omega) (by omega) 0 (by simp)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← pow_add, show a + ((k : ℕ) + 1) = a + 1 + (k : ℕ) from by omega]

omit [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C] in
/-- The alternating sum of the faces of the degreewise tensor product, restricted to the summand
`(a, b)`, split at the cut point `a`. -/
private lemma aw_faces (a b n : ℕ) (hab : a + b = n) :
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((M.δ i ≫ M.map (subinterval (n := n) 0 a (by omega)).op) ⊗ₘ
          (N.δ i ≫ N.map (subinterval (n := n) a b (by omega)).op)) =
      (∑ j : Fin (a + 1), (-1 : ℤ) ^ (j : ℕ) •
        (M.map ((δ j.castSucc ≫ subinterval (n := n + 1) 0 (a + 1) (by omega)).op) ⊗ₘ
          N.map (subinterval (n := n + 1) (a + 1) b (by omega)).op)) +
        ∑ k : Fin (b + 1), (-1 : ℤ) ^ (a + 1 + (k : ℕ)) •
        (M.map (subinterval (n := n + 1) 0 a (by omega)).op ⊗ₘ
          N.map ((δ k.succ ≫ subinterval (n := n + 1) a (b + 1) (by omega)).op)) := by
  simp only [delta_comp_map]
  rw [← Fin.sum_congr' _ (show a + 1 + (b + 1) = n + 2 by omega), Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.val_cast, Fin.val_castAdd]
    rw [subinterval_zero_comp_δ_of_le (a := a) (by omega) (by omega) _ j.castSucc (by simp),
      subinterval_comp_δ_of_le (a := a) (b := b) (by omega) (by omega) _ (by simpa using j.is_le)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.val_cast, Fin.val_natAdd]
    rw [subinterval_zero_comp_δ_of_lt (a := a) (by omega) (by omega) _ (by simp; omega),
      subinterval_comp_δ_of_lt (a := a) (b := b) (by omega) (by omega) _ k.succ (by simp; omega)]

omit [HasZeroObject C] [HasFiniteCoproducts C] in
/-- The identity at the heart of the chain map property: on the summand `(a, b)` of degree `n`
the two terms of the differential of the tensor complex add up to the alternating sum of the
faces of the degreewise tensor product. -/
private lemma aw_step (a b n : ℕ) (hab : a + b = n) :
    ((M.map (subinterval (n := n + 1) 0 (a + 1) (by omega)).op ≫
        AlternatingFaceMapComplex.objD M a) ⊗ₘ
      N.map (subinterval (n := n + 1) (a + 1) b (by omega)).op) +
        (-1 : ℤ) ^ a • (M.map (subinterval (n := n + 1) 0 a (by omega)).op ⊗ₘ
        (N.map (subinterval (n := n + 1) a (b + 1) (by omega)).op ≫
          AlternatingFaceMapComplex.objD N b)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((M.δ i ≫ M.map (subinterval (n := n) 0 a (by omega)).op) ⊗ₘ
          (N.δ i ≫ N.map (subinterval (n := n) a b (by omega)).op)) := by
  rw [aw_front M N a b n hab, aw_back M N a b n hab, aw_faces M N a b n hab,
    pow_succ, mul_neg_one, neg_smul]
  abel

/-- The Alexander–Whitney map in degree `m`. -/
public def awApp (m : ℕ) :
    M _⦋m⦌ ⊗ N _⦋m⦌ ⟶
      (HomologicalComplex.tensorObj ((alternatingFaceMapComplex C).obj M)
        ((alternatingFaceMapComplex C).obj N)).X m :=
  ∑ x ∈ Finset.antidiagonal m, awTerm M N m x


omit [HasZeroObject C] in
/-- The Alexander–Whitney map intertwines the alternating sum of the faces of the degreewise
tensor product with the differential of the tensor complex. -/
private lemma awApp_comm (n : ℕ) :
    awApp M N (n + 1) ≫ (HomologicalComplex.tensorObj ((alternatingFaceMapComplex C).obj M)
        ((alternatingFaceMapComplex C).obj N)).d (n + 1) n =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (M.δ i ⊗ₘ N.δ i)) ≫ awApp M N n := by
  have h0₁ : awTerm M N (n + 1) (0, n + 1) ≫
      HomologicalComplex.mapBifunctor.D₁ ((alternatingFaceMapComplex C).obj M)
        ((alternatingFaceMapComplex C).obj N) (curriedTensor C) (ComplexShape.down ℕ)
        (n + 1) n = 0 := by
    rw [awTerm_eq M N (n + 1) (0, n + 1) (by omega) (by omega) (by omega)]
    simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁]
    rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _
      (by rw [ChainComplex.next_nat_zero]; simp), comp_zero]
  have h0₂ : awTerm M N (n + 1) (n + 1, 0) ≫
      HomologicalComplex.mapBifunctor.D₂ ((alternatingFaceMapComplex C).obj M)
        ((alternatingFaceMapComplex C).obj N) (curriedTensor C) (ComplexShape.down ℕ)
        (n + 1) n = 0 := by
    rw [awTerm_eq M N (n + 1) (n + 1, 0) (by omega) (by omega) (by omega)]
    simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₂]
    rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _
      (by rw [ChainComplex.next_nat_zero]; simp), comp_zero]
  rw [awApp, awApp, HomologicalComplex.mapBifunctor.d_eq, Preadditive.sum_comp,
    Preadditive.comp_sum]
  simp only [Preadditive.comp_add]
  rw [Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.sum_antidiagonal_succ', h0₁, h0₂, zero_add, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hab : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  rw [awTerm_eq M N (n + 1) (p.1 + 1, p.2) (by omega) (by omega) (by omega),
    awTerm_eq M N (n + 1) (p.1, p.2 + 1) (by omega) (by omega) (by omega),
    awTerm_eq M N n p hab (by omega) (by omega)]
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.down ℕ).Rel (p.1 + 1) p.1 from rfl) _ _
      (show ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (p.1, p.2) = n from hab),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
      (show (ComplexShape.down ℕ).Rel (p.2 + 1) p.2 from rfl) _
      (show ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (p.1, p.2) = n from hab),
    show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (p.1 + 1, p.2) = 1 from rfl,
    show ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (p.1, p.2 + 1) = (-1 : ℤˣ) ^ p.1 from rfl]
  simp only [curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_id, ← id_tensorHom,
    one_smul, Units.smul_def, Units.val_pow_eq_pow_val, Units.coe_neg_one,
    alternatingFaceMapComplex_obj_X, alternatingFaceMapComplex_obj_d]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Preadditive.sum_comp,
    tensorHom_comp_tensorHom_assoc, Category.comp_id]
  simp only [← Preadditive.zsmul_comp, ← Preadditive.add_comp, ← Preadditive.sum_comp]
  rw [aw_step M N p.1 p.2 n hab]

/-- The Alexander–Whitney map: a morphism from the alternating face map complex of the degreewise
tensor product of two simplicial objects to the total tensor product of their alternating face
map complexes. -/
public def alexanderWhitney :
    (alternatingFaceMapComplex C).obj (M ⊗ N) ⟶
      HomologicalComplex.tensorObj ((alternatingFaceMapComplex C).obj M)
        ((alternatingFaceMapComplex C).obj N) where
  f := awApp M N
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    have hd : ((alternatingFaceMapComplex C).obj (M ⊗ N)).d (j + 1) j =
        ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (M.δ i ⊗ₘ N.δ i) :=
      alternatingFaceMapComplex_obj_d (M ⊗ N) j
    exact (awApp_comm M N j).trans (congrArg (fun f => f ≫ awApp M N j) hd).symm


/-! ### Naturality, the degree-zero term, and the summand inclusions -/

omit [HasZeroObject C] in
/-- The inclusion of the `(p, q)` summand of a tensor complex is an isomorphism as soon as all
the other summands in that degree vanish. -/
public lemma isIso_ιTensorObj (K L : ChainComplex C ℕ) (p q m : ℕ) (h : p + q = m)
    (hz : ∀ p' q' : ℕ, p' + q' = m → q' ≠ q → IsZero (K.X p' ⊗ L.X q')) :
    IsIso (HomologicalComplex.ιTensorObj K L p q m h) := by
  have hp : ∀ i₁ i₂ : ℕ, i₁ + i₂ = m → i₂ = q → i₁ = p := fun i₁ i₂ h' hq => by omega
  refine ⟨HomologicalComplex.mapBifunctorDesc
    (fun i₁ i₂ h' => if hq : i₂ = q then eqToHom (by
      obtain rfl := hp i₁ i₂ h' hq
      obtain rfl := hq
      rfl) else 0), ?_, ?_⟩
  · rw [HomologicalComplex.ι_mapBifunctorDesc, dite_eq_left rfl, eqToHom_refl]
    rfl
  · refine HomologicalComplex.mapBifunctor.hom_ext fun i₁ i₂ h' => ?_
    rw [Category.comp_id, HomologicalComplex.ι_mapBifunctorDesc_assoc]
    by_cases hq : i₂ = q
    · obtain rfl := hp i₁ i₂ h' hq
      obtain rfl := hq
      rw [dite_eq_left rfl, eqToHom_refl, Category.id_comp]
    · rw [dite_eq_right hq, zero_comp]
      exact (hz i₁ i₂ h' hq).eq_of_src _ _

omit [HasZeroObject C] in
/-- The Alexander–Whitney map is natural in the second simplicial object. -/
public lemma awApp_naturality_right {N' : SimplicialObject C} (g : N ⟶ N') (m : ℕ) :
    awApp M N m ≫ (HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
        ((alternatingFaceMapComplex C).map g)).f m =
      (M _⦋m⦌ ◁ g.app (op ⦋m⦌)) ≫ awApp M N' m := by
  rw [awApp, awApp, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have h : x.1 + x.2 = m := Finset.mem_antidiagonal.mp hx
  rw [awTerm_eq M N m x h (by omega) (by omega), awTerm_eq M N' m x h (by omega) (by omega),
    Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
    alternatingFaceMapComplex_map_f, alternatingFaceMapComplex_obj_X,
    MonoidalCategory.id_whiskerRight, curriedTensor_obj_obj, Category.id_comp]
  rw [← id_tensorHom, ← id_tensorHom, ← Category.assoc, ← Category.assoc,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
    g.naturality (subinterval (n := m) x.1 x.2 (by omega)).op]

omit [HasZeroObject C] in
/-- The Alexander–Whitney map is natural in the second simplicial object. -/
public lemma alexanderWhitney_naturality_right {N' : SimplicialObject C} (g : N ⟶ N') :
    alexanderWhitney M N ≫ HomologicalComplex.tensorHom
        (𝟙 ((alternatingFaceMapComplex C).obj M)) ((alternatingFaceMapComplex C).map g) =
      (alternatingFaceMapComplex C).map (M ◁ g) ≫ alexanderWhitney M N' := by
  ext m
  exact awApp_naturality_right M N g m

omit [HasZeroObject C] in
/-- In degree zero the Alexander–Whitney map is the inclusion of the unique summand, hence an
isomorphism. -/
public lemma alexanderWhitney_f_zero_eq :
    (alexanderWhitney M N).f 0 = HomologicalComplex.ιTensorObj
      ((alternatingFaceMapComplex C).obj M) ((alternatingFaceMapComplex C).obj N) 0 0 0 rfl := by
  change awApp M N 0 = _
  have h : ∀ (X : SimplicialObject C) (f : ⦋0⦌ ⟶ ⦋0⦌), X.map f.op = 𝟙 (X _⦋0⦌) := fun X f => by
    rw [Subsingleton.elim f (𝟙 _), op_id, X.map_id]
  rw [awApp, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
    awTerm_eq M N 0 (0, 0) rfl (by omega) (by omega), h M, h N,
    MonoidalCategory.id_tensorHom_id, Category.id_comp]

public instance isIso_alexanderWhitney_f_zero : IsIso ((alexanderWhitney M N).f 0) := by
  rw [alexanderWhitney_f_zero_eq]
  exact isIso_ιTensorObj _ _ 0 0 0 rfl (fun p' q' h hq => absurd (by omega) hq)

end AlgebraicTopology
