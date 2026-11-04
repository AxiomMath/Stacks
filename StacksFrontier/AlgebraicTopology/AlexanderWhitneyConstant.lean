module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.AlgebraicTopology.AlexanderWhitney

/-!
# The Alexander–Whitney map of a constant second factor

For a constant simplicial object `A` the alternating face map complex of the degreewise tensor
product `M ⊗ A` is the complex `M` tensored by `A`, and the Alexander–Whitney map is an
isomorphism onto it. The precise form of this statement proved here is that composing the
Alexander–Whitney map with the augmentation of the constant factor is an isomorphism of
complexes; since the augmentation is a homotopy equivalence, and so stays one after tensoring,
the Alexander–Whitney map of a constant second factor is a quasi-isomorphism.

## Main definitions

* `AlgebraicTopology.tensorHomotopyEquivRight`: tensoring on the left with a fixed complex
  sends a homotopy equivalence to a homotopy equivalence.
* `AlgebraicTopology.constAugmentationEquiv`: the augmentation of the alternating face map
  complex of a constant simplicial object onto the single complex, as a homotopy equivalence.

## Main results

* `AlgebraicTopology.quasiIso_alexanderWhitney_const`: for a constant second factor the
  Alexander–Whitney map is a quasi-isomorphism.

## Implementation notes

The homotopy equivalence of the augmentation is Mathlib's extra degeneracy of the constant
augmented simplicial object; that it survives tensoring is Mathlib's homotopy
`HomologicalComplex.mapBifunctorMapHomotopy₂` in the second variable of the tensor bifunctor.
Only the summand `(n, 0)` of the tensor complex with the single complex is nonzero, and the
composite picks it out, which is why the composite is an isomorphism in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite SimplexCategory

open scoped Simplicial

universe v u

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]

/-! ### Tensoring a homotopy equivalence -/

omit [HasZeroObject C] in
/-- Tensoring on the left with a fixed complex preserves composition. -/
public lemma tensorHom_id_comp (K : ChainComplex C ℕ) {L L' L'' : ChainComplex C ℕ}
    (f : L ⟶ L') (g : L' ⟶ L'') :
    HomologicalComplex.tensorHom (𝟙 K) f ≫ HomologicalComplex.tensorHom (𝟙 K) g =
      HomologicalComplex.tensorHom (𝟙 K) (f ≫ g) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun i₁ i₂ h => ?_
  simp [HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap]

omit [HasZeroObject C] in
/-- Tensoring on the left with a fixed complex preserves the identity. -/
public lemma tensorHom_id_id (K L : ChainComplex C ℕ) :
    HomologicalComplex.tensorHom (𝟙 K) (𝟙 L) = 𝟙 (HomologicalComplex.tensorObj K L) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun i₁ i₂ h => ?_
  simp [HomologicalComplex.ι_mapBifunctorMap]

/-- Tensoring on the left with a fixed complex sends a homotopy equivalence of complexes to a
homotopy equivalence. -/
public def tensorHomotopyEquivRight (K : ChainComplex C ℕ) {L L' : ChainComplex C ℕ}
    (e : HomotopyEquiv L L') :
    HomotopyEquiv (HomologicalComplex.tensorObj K L) (HomologicalComplex.tensorObj K L') where
  hom := HomologicalComplex.tensorHom (𝟙 K) e.hom
  inv := HomologicalComplex.tensorHom (𝟙 K) e.inv
  homotopyHomInvId := by
    rw [tensorHom_id_comp]
    exact (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K) e.homotopyHomInvId
      (curriedTensor C) (ComplexShape.down ℕ)).trans (Homotopy.ofEq (tensorHom_id_id K L))
  homotopyInvHomId := by
    rw [tensorHom_id_comp]
    exact (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K) e.homotopyInvHomId
      (curriedTensor C) (ComplexShape.down ℕ)).trans (Homotopy.ofEq (tensorHom_id_id K L'))

/-! ### The constant second factor -/

/-- The augmentation of the alternating face map complex of a constant simplicial object onto
the single complex, as a homotopy equivalence: the constant augmented simplicial object has an
extra degeneracy. -/
public def constAugmentationEquiv (A : C) :
    HomotopyEquiv ((alternatingFaceMapComplex C).obj ((SimplicialObject.const C).obj A))
      ((ChainComplex.single₀ C).obj A) :=
  (SimplicialObject.Augmented.ExtraDegeneracy.const A).homotopyEquiv

omit [MonoidalCategory C] [MonoidalPreadditive C] [HasFiniteCoproducts C] in
public lemma constAugmentationEquiv_hom_f_zero (A : C) :
    (constAugmentationEquiv A).hom.f 0 = 𝟙 A := by
  rw [constAugmentationEquiv]
  exact AlternatingFaceMapComplex.ε_app_f_zero (SimplicialObject.Augmented.const.obj A)

omit [MonoidalCategory C] [MonoidalPreadditive C] [HasFiniteCoproducts C] in
public lemma constAugmentationEquiv_hom_f_succ (A : C) (n : ℕ) :
    (constAugmentationEquiv A).hom.f (n + 1) = 0 :=
  AlternatingFaceMapComplex.ε_app_f_succ (SimplicialObject.Augmented.const.obj A) n

variable (M : SimplicialObject C)

/-- Only the `(n, 0)` summand of the tensor product with a single complex is nonzero, so its
inclusion is an isomorphism. -/
public lemma isIso_ιTensorObj_single₀ (A : C) (n : ℕ) :
    IsIso (HomologicalComplex.ιTensorObj ((alternatingFaceMapComplex C).obj M)
      ((ChainComplex.single₀ C).obj A) n 0 n (by omega)) := by
  refine isIso_ιTensorObj _ _ n 0 n (by omega) fun p' q' h hq => ?_
  exact Functor.map_isZero (tensorLeft _)
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 A q' hq)

/-- The degree-zero component of the augmentation of a constant simplicial object is an
isomorphism. -/
public instance isIso_constAugmentationEquiv_hom_f_zero (A : C) :
    IsIso ((constAugmentationEquiv A).hom.f 0) :=
  ⟨𝟙 A, by simp [constAugmentationEquiv_hom_f_zero], by
    simp [constAugmentationEquiv_hom_f_zero]⟩

/-- The Alexander–Whitney map of a constant second factor, composed with the augmentation of
that factor, is an isomorphism in every degree: only the summand `(n, 0)` of the tensor product
with the single complex survives, and on it the map is built from identities. -/
public instance isIso_awApp_const_comp (A : C) (n : ℕ) :
    IsIso (awApp M ((SimplicialObject.const C).obj A) n ≫
      (HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
        (constAugmentationEquiv A).hom).f n) := by
  rw [awApp, Preadditive.sum_comp,
    Finset.sum_eq_single_of_mem (n, 0) (Finset.mem_antidiagonal.mpr (by omega)) ?_]
  · rw [awTerm_eq M ((SimplicialObject.const C).obj A) n (n, 0) (by omega) (by omega) (by omega),
      Category.assoc]
    have hFR : IsIso (M.map (subinterval (n := n) 0 n (by omega)).op) := by
      rw [subinterval_zero_self, op_id, M.map_id]
      infer_instance
    have hBK : IsIso (((SimplicialObject.const C).obj A).map
        (subinterval (n := n) n 0 (by omega)).op) := ⟨𝟙 A, by simp, by simp⟩
    have hι : IsIso (HomologicalComplex.ιTensorObj ((alternatingFaceMapComplex C).obj M)
        ((alternatingFaceMapComplex C).obj ((SimplicialObject.const C).obj A)) n 0 n (by omega) ≫
        (HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
          (constAugmentationEquiv A).hom).f n) := by
      rw [HomologicalComplex.ι_mapBifunctorMap]
      have := isIso_ιTensorObj_single₀ M A n
      simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
        MonoidalCategory.id_whiskerRight]
      infer_instance
    infer_instance
  · rintro ⟨p, q⟩ hx hne
    have h : p + q = n := Finset.mem_antidiagonal.mp hx
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · exact absurd (Prod.ext (by omega) h0) hne
      · exact ⟨q - 1, by omega⟩
    rw [awTerm_eq M ((SimplicialObject.const C).obj A) n (p, q + 1) h (by simpa using (by omega))
        (by simpa using (by omega)),
      Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
      alternatingFaceMapComplex_obj_X, MonoidalCategory.id_whiskerRight, curriedTensor_obj_obj,
      constAugmentationEquiv_hom_f_succ, MonoidalPreadditive.whiskerLeft_zero, comp_zero,
      zero_comp]

public instance isIso_alexanderWhitney_const_comp (A : C) :
    IsIso (alexanderWhitney M ((SimplicialObject.const C).obj A) ≫
      HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
        (constAugmentationEquiv A).hom) := by
  have h : ∀ n : ℕ, IsIso ((alexanderWhitney M ((SimplicialObject.const C).obj A) ≫
      HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
        (constAugmentationEquiv A).hom).f n) := fun n => isIso_awApp_const_comp M A n
  exact HomologicalComplex.Hom.isIso_of_components _

variable [CategoryWithHomology C]

/-- **The Alexander–Whitney map of a constant second factor is a quasi-isomorphism.** -/
public instance quasiIso_alexanderWhitney_const (A : C) :
    QuasiIso (alexanderWhitney M ((SimplicialObject.const C).obj A)) := by
  have h₂ : QuasiIso (HomologicalComplex.tensorHom
      (𝟙 ((alternatingFaceMapComplex C).obj M)) (constAugmentationEquiv A).hom) :=
    _root_.homotopyEquivalences_le_quasiIso C (ComplexShape.down ℕ) _
      ⟨tensorHomotopyEquivRight ((alternatingFaceMapComplex C).obj M) (constAugmentationEquiv A),
        rfl⟩
  exact quasiIso_of_comp_right (alexanderWhitney M ((SimplicialObject.const C).obj A))
    (HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
      (constAugmentationEquiv A).hom)

end AlgebraicTopology

end
