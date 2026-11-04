module

public import StacksFrontier.CategoryTheory.Sites.CechCofreeProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverComplex

/-!
# Positive-degree Čech cohomology of a cofree presheaf, for a family with chosen products

Let `D : ι → C` be a family of objects whose finite nonempty products exist, and let
`Stacks.CechSite.FinalCover.complexFunctor D` be its Čech complex. This file proves that the
positive-degree Čech cohomology of a *cofree* presheaf
`Stacks.CategoryTheory.CechComplex.cofree obj val` vanishes, and hence that of any retract of a
product of presheaves isomorphic to single-object cofree presheaves.

The argument is the one of `StacksFrontier/CategoryTheory/Sites/CechCofree.lean`, which proves the
same for Mathlib's Čech complex of a family in a category with all finite products: the Čech
complex of `cofree obj val` is degreewise the product of the `val k` over the pairs consisting of
an index `k` and a tuple of factorisations of `obj k` through members of `D`, the differential
becomes the alternating sum of the face maps of those tuples, and prepending a factorisation is a
contracting homotopy. Only the universal property of the products `D_x` of the members of the
family is used, so nothing changes when the other finite products of `C` are missing.

## Main results

* `Stacks.CechSite.FinalCover.isZero_homology_complexFunctor_cofree` — positive-degree Čech
  cohomology of a cofree presheaf vanishes.
* `Stacks.CechSite.FinalCover.isZero_homology_complexFunctor_of_retract_of_pi` — the same for a
  retract of a product of presheaves each isomorphic to a single-object cofree presheaf.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 03AW](https://stacks.math.columbia.edu/tag/03AW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryTheory Stacks.CategoryTheory.CechComplex

universe t w v v' u u'

namespace Stacks.CechSite.FinalCover

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] {κ : Type t}
  {ι : Type w} (D : ι → C) [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]

/-! ### Factorisations through members of the family -/

/-- `thru D V` is the type of pairs consisting of an index `i` and a morphism `V ⟶ D i`: the ways
in which `V` factors through a member of the family. -/
abbrev thru (V : C) : Type max w v := Σ i : ι, (V ⟶ D i)

variable {D} in
/-- The tuple of indices underlying a tuple of factorisations. -/
def thruIdx {V : C} {m : ℕ} (y : Fin m → thru D V) : Fin m → ι := fun a ↦ (y a).1

omit [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))] in
/-- The indices of a reindexed tuple of factorisations are the reindexed indices. -/
@[simp]
theorem thruIdx_comp {V : C} {m m' : ℕ} (y : Fin m → thru D V) (h : Fin m' → Fin m) :
    thruIdx (y ∘ h) = thruIdx y ∘ h := rfl

variable {D} in
/-- The morphism `V ⟶ inter D (thruIdx y)` assembled from a tuple of factorisations. -/
noncomputable def thruSec {V : C} {n : ℕ} (y : Fin (n + 1) → thru D V) :
    V ⟶ inter D (thruIdx y) :=
  interLift D fun a ↦ (y a).2

/-- The components of the morphism assembled from a tuple of factorisations. -/
@[reassoc (attr := simp)]
theorem thruSec_comp_interπ {V : C} {n : ℕ} (y : Fin (n + 1) → thru D V) (a : Fin (n + 1)) :
    thruSec y ≫ interπ D (thruIdx y) a = (y a).2 :=
  interLift_comp_interπ D _ a

/-- Reindexing a tuple of factorisations reindexes the assembled morphism. -/
@[reassoc]
theorem thruSec_comp_interMap {V : C} {n m : ℕ} (y : Fin (n + 1) → thru D V)
    (h : Fin (m + 1) → Fin (n + 1)) :
    thruSec y ≫ interMap D (thruIdx y) h = thruSec (y ∘ h) :=
  inter_hom_ext D fun a ↦ by
    rw [Category.assoc, interMap_comp_interπ, thruSec_comp_interπ]
    exact (thruSec_comp_interπ D (y ∘ h) a).symm

/-- A morphism `a : V ⟶ inter D x` is recovered from the tuple of factorisations it induces. -/
@[simp]
theorem thruSec_ofHom {V : C} {n : ℕ} (x : Fin (n + 1) → ι) (a : V ⟶ inter D x) :
    thruSec (fun b ↦ (⟨x b, a ≫ interπ D x b⟩ : thru D V)) = a :=
  inter_hom_ext D fun b ↦ thruSec_comp_interπ D _ b

/-! ### The Čech complex of a cofree presheaf -/

section CechCofree

variable [Preadditive A] [HasProducts.{w} A] [HasProducts.{t} A] [HasProducts.{v} A]
  (obj : κ → C) (val : κ → A)

/-- The projection of the degree `n` term of the Čech complex of `cofree obj val` onto the copy
of `val k` indexed by a tuple `y` of `n + 1` factorisations of `obj k` through members of `D`. -/
noncomputable def cofreeProj (n : ℕ) (k : κ) (y : Fin (n + 1) → thru D (obj k)) :
    ((complexFunctor D A).obj (cofree obj val)).X n ⟶ val k :=
  π D (cofree obj val) n (thruIdx y) ≫ cofreeπ obj val k (thruSec y)

/-- The morphism into the degree `n` term of the Čech complex of `cofree obj val` determined by a
family of morphisms indexed by an index `k` and a tuple of `n + 1` factorisations. -/
noncomputable def cofreeCechLift {n : ℕ} {T : A}
    (f : ∀ (k : κ), (Fin (n + 1) → thru D (obj k)) → (T ⟶ val k)) :
    T ⟶ ((complexFunctor D A).obj (cofree obj val)).X n :=
  lift D (cofree obj val) fun x ↦ cofreeObjLift obj val fun k p ↦
    f k fun a ↦ ⟨x a, p ≫ interπ D x a⟩

/-- The components of `cofreeCechLift`. -/
@[reassoc (attr := simp)]
theorem cofreeCechLift_comp_cofreeProj {n : ℕ} {T : A}
    (f : ∀ (k : κ), (Fin (n + 1) → thru D (obj k)) → (T ⟶ val k)) (k : κ)
    (y : Fin (n + 1) → thru D (obj k)) :
    cofreeCechLift D obj val f ≫ cofreeProj D obj val n k y = f k y := by
  rw [cofreeProj, cofreeCechLift, ← Category.assoc, lift_comp_π, cofreeObjLift_comp_cofreeπ]
  exact congrArg (f k) (funext fun a ↦ by rw [thruSec_comp_interπ]; rfl)

/-- Two morphisms into a Čech term of a cofree presheaf agree as soon as all their components
agree. -/
theorem cofree_cech_hom_ext {n : ℕ} {T : A}
    {f g : T ⟶ ((complexFunctor D A).obj (cofree obj val)).X n}
    (h : ∀ k y, f ≫ cofreeProj D obj val n k y = g ≫ cofreeProj D obj val n k y) : f = g :=
  hom_ext D (cofree obj val) fun x ↦ cofree_obj_hom_ext obj val fun k a ↦ by
    have hk := h k fun b ↦ (⟨x b, a ≫ interπ D x b⟩ : thru D (obj k))
    rw [cofreeProj, thruSec_ofHom, ← Category.assoc, ← Category.assoc] at hk
    exact hk

/-- **The Čech differential of a cofree presheaf** is the alternating sum of the face maps of the
tuples of factorisations. -/
theorem d_comp_cofreeProj (n : ℕ) (k : κ) (z : Fin (n + 2) → thru D (obj k)) :
    ((complexFunctor D A).obj (cofree obj val)).d n (n + 1) ≫
        cofreeProj D obj val (n + 1) k z =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        cofreeProj D obj val n k (z ∘ i.succAbove) := by
  dsimp only [cofreeProj]
  rw [← Category.assoc, d_comp_π, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.zsmul_comp, Category.assoc, cofree_map_comp_cofreeπ, Quiver.Hom.unop_op,
    thruSec_comp_interMap]
  rfl

/-- The factorisation prepended by the contracting homotopy. It depends only on `k`, the choice
being made from a proof of a proposition. -/
noncomputable def cofreePick {n : ℕ} (k : κ) (y : Fin (n + 1) → thru D (obj k)) :
    thru D (obj k) :=
  (⟨y 0⟩ : Nonempty (thru D (obj k))).some

omit [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))] [Preadditive A]
  [HasProducts.{w} A] [HasProducts.{t} A] [HasProducts.{v} A] in
/-- The prepended factorisation does not depend on the tuple that exhibited it. -/
theorem cofreePick_eq {n m : ℕ} (k : κ) (y : Fin (n + 1) → thru D (obj k))
    (y' : Fin (m + 1) → thru D (obj k)) : cofreePick D obj k y = cofreePick D obj k y' := rfl

/-- The contracting homotopy of the Čech complex of a cofree presheaf. -/
noncomputable def cofreeContraction (n : ℕ) :
    ((complexFunctor D A).obj (cofree obj val)).X (n + 1) ⟶
      ((complexFunctor D A).obj (cofree obj val)).X n :=
  cofreeCechLift D obj val fun k y ↦
    cofreeProj D obj val (n + 1) k (Fin.cons (cofreePick D obj k y) y)

/-- The components of the contracting homotopy. -/
@[reassoc (attr := simp)]
theorem cofreeContraction_comp_cofreeProj (n : ℕ) (k : κ) (y : Fin (n + 1) → thru D (obj k)) :
    cofreeContraction D obj val n ≫ cofreeProj D obj val n k y =
      cofreeProj D obj val (n + 1) k (Fin.cons (cofreePick D obj k y) y) :=
  cofreeCechLift_comp_cofreeProj D obj val _ k y

/-- **The contraction identity**: in every degree `n + 1` the identity of the Čech complex of a
cofree presheaf is the sum of the two composites with the contracting homotopy. -/
theorem d_comp_cofreeContraction_add (n : ℕ) :
    ((complexFunctor D A).obj (cofree obj val)).d (n + 1) (n + 2) ≫
        cofreeContraction D obj val (n + 1) +
      cofreeContraction D obj val n ≫ ((complexFunctor D A).obj (cofree obj val)).d n (n + 1) =
      𝟙 (((complexFunctor D A).obj (cofree obj val)).X (n + 1)) := by
  refine cofree_cech_hom_ext D obj val fun k y ↦ ?_
  rw [Preadditive.add_comp, Category.id_comp, Category.assoc,
    cofreeContraction_comp_cofreeProj, d_comp_cofreeProj, Fin.sum_univ_succ,
    cons_comp_succAbove_zero, Category.assoc, d_comp_cofreeProj, Preadditive.comp_sum]
  have hcancel : ∀ j : Fin (n + 2),
      (-1 : ℤ) ^ ((j.succ : Fin (n + 3)) : ℕ) • cofreeProj D obj val (n + 1) k
          (Fin.cons (cofreePick D obj k y) y ∘ (j.succ).succAbove) +
        cofreeContraction D obj val n ≫
          ((-1 : ℤ) ^ (j : ℕ) • cofreeProj D obj val n k (y ∘ j.succAbove)) = 0 := fun j ↦ by
    rw [Fin.cons_comp_succ_succAbove, Preadditive.comp_zsmul, cofreeContraction_comp_cofreeProj,
      Fin.val_succ, pow_succ, mul_neg_one, neg_smul, cofreePick_eq D obj k (y ∘ j.succAbove) y]
    exact neg_add_cancel _
  rw [add_assoc, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun j _ ↦ hcancel j,
    Finset.sum_const_zero, add_zero]
  simp

end CechCofree

/-! ### Vanishing -/

section Vanishing

variable [Abelian A] [HasProducts.{w} A] [HasProducts.{t} A] [HasProducts.{v} A]
  (obj : κ → C) (val : κ → A)

/-- **Positive-degree Čech cohomology of a cofree presheaf vanishes.** -/
theorem isZero_homology_complexFunctor_cofree (n : ℕ) (hn : 0 < n) :
    IsZero (((complexFunctor D A).obj (cofree obj val)).homology n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 2) (by simp) (by simp)]
  exact ShortComplex.exact_of_contraction _ (cofreeContraction D obj val (m + 1))
    (cofreeContraction D obj val m) (d_comp_cofreeContraction_add D obj val m)

omit [HasProducts.{t} A] [HasProducts.{v} A] in
/-- A retract of a presheaf with vanishing Čech cohomology in a degree has vanishing Čech
cohomology in that degree. -/
theorem isZero_homology_complexFunctor_of_retract_of_isZero {P Q : Cᵒᵖ ⥤ A} (n : ℕ)
    (hQ : IsZero (((complexFunctor D A).obj Q).homology n)) (s : P ⟶ Q) (r : Q ⟶ P)
    (hsr : s ≫ r = 𝟙 P) : IsZero (((complexFunctor D A).obj P).homology n) := by
  have hid : HomologicalComplex.homologyMap ((complexFunctor D A).map s) n ≫
      HomologicalComplex.homologyMap ((complexFunctor D A).map r) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp, hsr,
      CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  have hz := hQ.eq_zero_of_tgt (HomologicalComplex.homologyMap ((complexFunctor D A).map s) n)
  exact (IsZero.iff_id_eq_zero _).2 (by rw [← hid, hz, zero_comp])

/-- **Positive-degree Čech cohomology of a retract of a product of presheaves isomorphic to
single-object cofree presheaves vanishes.** -/
theorem isZero_homology_complexFunctor_of_retract_of_pi (P : Cᵒᵖ ⥤ A) (Q : κ → (Cᵒᵖ ⥤ A))
    (e : ∀ k, Q k ≅ cofreeOne (obj k) (val k)) (s : P ⟶ ∏ᶜ Q) (r : (∏ᶜ Q) ⟶ P)
    (hsr : s ≫ r = 𝟙 P) (n : ℕ) (hn : 0 < n) :
    IsZero (((complexFunctor D A).obj P).homology n) :=
  isZero_homology_complexFunctor_of_retract_of_isZero D n
    (isZero_homology_complexFunctor_cofree D obj val n hn)
    (s ≫ (piIsoCofree obj val Q e).hom) ((piIsoCofree obj val Q e).inv ≫ r)
    (by rw [Category.assoc, Iso.hom_inv_id_assoc, hsr])

end Vanishing

end Stacks.CechSite.FinalCover

end
