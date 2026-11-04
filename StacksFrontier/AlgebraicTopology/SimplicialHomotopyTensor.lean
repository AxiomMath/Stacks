module

public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Tensoring a simplicial homotopy

If `C` is monoidal then `SimplicialObject C` carries the pointwise tensor product, and a
simplicial homotopy between two morphisms `f g : X ⟶ Y` can be tensored on the left with a
simplicial object `M`: the components of the tensored homotopy are `M.σ i ⊗ₘ H.h i`, the
degeneracies of `M` supplying the simplicial direction in which the homotopy moves. This is the
reason a *simplicial* contraction of a simplicial object survives tensoring, whereas a
contraction of its alternating face map complex does not.

## Main definitions

* `CategoryTheory.SimplicialObject.Homotopy.ofEq`: transport along equalities of the two
  morphisms connected by a homotopy.
* `CategoryTheory.SimplicialObject.Homotopy.whiskerLeft`: the tensored homotopy.
* `CategoryTheory.SimplicialObject.Homotopy.whiskerLeftNullHomotopy`: tensoring a null-homotopy
  of the identity.

## Main results

* `CategoryTheory.SimplicialObject.Homotopy.isZero_homology_of_nullHomotopy`: if the identity of
  a simplicial object is simplicially homotopic to zero, its alternating face map complex has
  vanishing homology in every degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicTopology

open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject.Homotopy

variable {C : Type u} [Category.{v} C] {X Y : SimplicialObject C} {f g : X ⟶ Y}

/-- A simplicial homotopy connects any two morphisms equal to the ones it connects. -/
public def ofEq {f' g' : X ⟶ Y} (H : Homotopy f g) (hf : f = f') (hg : g = g') :
    Homotopy f' g' where
  h := H.h
  h_zero_comp_δ_zero n := hg ▸ H.h_zero_comp_δ_zero n
  h_last_comp_δ_last n := hf ▸ H.h_last_comp_δ_last n
  h_succ_comp_δ_castSucc_of_lt := H.h_succ_comp_δ_castSucc_of_lt
  h_succ_comp_δ_castSucc_succ := H.h_succ_comp_δ_castSucc_succ
  h_castSucc_comp_δ_succ_of_lt := H.h_castSucc_comp_δ_succ_of_lt
  h_comp_σ_castSucc_of_le := H.h_comp_σ_castSucc_of_le
  h_comp_σ_succ_of_lt := H.h_comp_σ_succ_of_lt

section Monoidal

variable [MonoidalCategory C]

/-- A simplicial homotopy `H` between `f g : X ⟶ Y`, tensored on the left with a simplicial
object `M`: the component in degree `n` at `i` is `M.σ i ⊗ₘ H.h i`. -/
public def whiskerLeft (M : SimplicialObject C) (H : Homotopy f g) :
    Homotopy (M ◁ f) (M ◁ g) where
  h i := M.σ i ⊗ₘ H.h i
  h_zero_comp_δ_zero n := by
    change (M.σ 0 ⊗ₘ H.h 0) ≫ (M.δ 0 ⊗ₘ Y.δ 0) = M.obj (op ⦋n⦌) ◁ g.app (op ⦋n⦌)
    rw [tensorHom_comp_tensorHom, M.δ_comp_σ_self' (by simp), H.h_zero_comp_δ_zero,
      id_tensorHom]
  h_last_comp_δ_last n := by
    change (M.σ (Fin.last n) ⊗ₘ H.h (Fin.last n)) ≫
        (M.δ (Fin.last (n + 1)) ⊗ₘ Y.δ (Fin.last (n + 1))) =
      M.obj (op ⦋n⦌) ◁ f.app (op ⦋n⦌)
    rw [tensorHom_comp_tensorHom, M.δ_comp_σ_succ' (by simp), H.h_last_comp_δ_last,
      id_tensorHom]
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    change (M.σ j.succ ⊗ₘ H.h j.succ) ≫ (M.δ i.castSucc ⊗ₘ Y.δ i.castSucc) =
      (M.δ i ⊗ₘ X.δ i) ≫ (M.σ j ⊗ₘ H.h j)
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, M.δ_comp_σ_of_le hij,
      H.h_succ_comp_δ_castSucc_of_lt i j hij]
  h_succ_comp_δ_castSucc_succ j := by
    change (M.σ j.succ ⊗ₘ H.h j.succ) ≫ (M.δ j.castSucc.succ ⊗ₘ Y.δ j.castSucc.succ) =
      (M.σ j.castSucc ⊗ₘ H.h j.castSucc) ≫ (M.δ j.castSucc.succ ⊗ₘ Y.δ j.castSucc.succ)
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      M.δ_comp_σ_self' (Fin.succ_castSucc j), M.δ_comp_σ_succ' rfl,
      H.h_succ_comp_δ_castSucc_succ]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    change (M.σ j.castSucc ⊗ₘ H.h j.castSucc) ≫ (M.δ i.succ ⊗ₘ Y.δ i.succ) =
      (M.δ i ⊗ₘ X.δ i) ≫ (M.σ j ⊗ₘ H.h j)
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, M.δ_comp_σ_of_gt hji,
      H.h_castSucc_comp_δ_succ_of_lt i j hji]
  h_comp_σ_castSucc_of_le i j hij := by
    change (M.σ j ⊗ₘ H.h j) ≫ (M.σ i.castSucc ⊗ₘ Y.σ i.castSucc) =
      (M.σ i ⊗ₘ X.σ i) ≫ (M.σ j.succ ⊗ₘ H.h j.succ)
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, M.σ_comp_σ hij,
      H.h_comp_σ_castSucc_of_le i j hij]
  h_comp_σ_succ_of_lt i j hji := by
    change (M.σ j ⊗ₘ H.h j) ≫ (M.σ i.succ ⊗ₘ Y.σ i.succ) =
      (M.σ i ⊗ₘ X.σ i) ≫ (M.σ j.castSucc ⊗ₘ H.h j.castSucc)
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ← M.σ_comp_σ hji,
      H.h_comp_σ_succ_of_lt i j hji]

end Monoidal

section Preadditive

variable [Preadditive C] [CategoryWithHomology C]

/-- If zero is simplicially homotopic to the identity of a simplicial object, then its
alternating face map complex has vanishing homology in every degree. -/
public lemma isZero_homology_of_nullHomotopy {Z : SimplicialObject C}
    (H : Homotopy (0 : Z ⟶ Z) (𝟙 Z)) (n : ℕ) :
    IsZero (((alternatingFaceMapComplex C).obj Z).homology n) := by
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  simpa using (H.toChainHomotopy.homologyMap_eq n).symm

end Preadditive

/-- Left tensoring a null-homotopy: if zero is simplicially homotopic to the identity of `Z`,
the same holds for `M ⊗ Z`. -/
public def whiskerLeftNullHomotopy [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
    (M : SimplicialObject C) {Z : SimplicialObject C} (H : Homotopy (0 : Z ⟶ Z) (𝟙 Z)) :
    Homotopy (0 : M ⊗ Z ⟶ M ⊗ Z) (𝟙 (M ⊗ Z)) :=
  (H.whiskerLeft M).ofEq
    (by
      ext n : 2
      exact MonoidalPreadditive.whiskerLeft_zero)
    (MonoidalCategory.whiskerLeft_id M Z)

end CategoryTheory.SimplicialObject.Homotopy

namespace CategoryTheory.SimplicialObject

/-- Left whiskering by a simplicial object annihilates the zero morphism. -/
public lemma whiskerLeft_eq_zero {C : Type u} [Category.{v} C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] (M : SimplicialObject C)
    {A A' : SimplicialObject C} : M ◁ (0 : A ⟶ A') = 0 := by
  ext n : 2
  exact MonoidalPreadditive.whiskerLeft_zero

end CategoryTheory.SimplicialObject

end
