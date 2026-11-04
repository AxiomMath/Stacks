module

public import Mathlib.Algebra.Homology.Augment
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# Acyclicity of the augmented complex of a simplex on a nonempty index set

The augmented alternating-face complex of a contractible simplicial object is acyclic. Three
forms are recorded: a chain complex with a degreewise contracting homotopy is acyclic; the
alternating-face complex of an augmented simplicial object carrying an extra degeneracy, augmented
by its own augmentation, is acyclic; and the concrete coproduct model
`… → ∐_{t : Fin 2 → I x} A x → ∐_{t : Fin 1 → I x} A x → ∐_x A x → 0`
is acyclic as soon as every index type `I x` is nonempty.

## Main results

* `acyclic_of_contraction`: a chain complex over `ℕ` with a contraction is acyclic.
* `acyclic_augment_of_extraDegeneracy`: the augmented alternating-face complex of an augmented
  simplicial object with a Mathlib `ExtraDegeneracy` is acyclic.
* `acyclic_of_simplexCoproduct`: the coproduct model of the simplex on a family of nonempty
  index types is acyclic.

## Implementation notes

`acyclic_of_simplexCoproduct` takes the complex as a black box `K` together with isomorphisms
identifying `K.X n` with the coproduct over `Σ x, Fin n → I x` and an identification of the
differential as the alternating sum of the face maps `t ↦ t ∘ Fin.succAbove k`. This avoids
constructing a simplicial object — only the faces are needed, not the full simplicial identities.
Degree `n` is the coproduct over `n`-tuples, so degree `0` is `∐ x, A x`: the complex is already
the augmented one, with the augmentation as `K.d 1 0`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

open scoped Simplicial

universe v u v' u'

namespace AlgebraicTopology.SimplexCoproductAcyclicity

variable {C : Type u} [Category.{v} C]

/-- The faces of an augmented simplicial object all become the same map after composing with the
augmentation, since the augmentation lands in a constant simplicial object. -/
public theorem δ_comp_hom_app {X : SimplicialObject.Augmented C} {n : ℕ} (i : Fin (n + 2)) :
    X.left.δ i ≫ X.hom.app (op ⦋n⦌) = X.hom.app (op ⦋n + 1⦌) := by
  simp [SimplicialObject.δ]

variable [Preadditive C]

/-- The first differential of the alternating-face complex of an augmented simplicial object
annihilates the augmentation, so the complex may be augmented by it. -/
public theorem d_one_zero_comp_hom_app (X : SimplicialObject.Augmented C) :
    (AlternatingFaceMapComplex.obj X.left).d 1 0 ≫ X.hom.app (op ⦋0⦌) = 0 := by
  rw [AlternatingFaceMapComplex.obj_d_eq]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, δ_comp_hom_app]
  simp

variable [CategoryWithHomology C]

/-- A chain complex over `ℕ` with a contraction `s` -- maps `s n : K_n ⟶ K_{n+1}` splitting the
differential, so that `s 0 ≫ d₁₀ = 𝟙` and `d ≫ s + s ≫ d = 𝟙` in every degree -- is acyclic,
since the contraction is a null-homotopy of the identity. -/
public theorem acyclic_of_contraction (K : ChainComplex C ℕ)
    (s : ∀ n : ℕ, K.X n ⟶ K.X (n + 1)) (h₀ : s 0 ≫ K.d 1 0 = 𝟙 _)
    (h : ∀ n : ℕ, K.d (n + 1) n ≫ s n + s (n + 1) ≫ K.d (n + 2) (n + 1) = 𝟙 _) :
    K.Acyclic := by
  classical
  let H : Homotopy (𝟙 K) 0 :=
    { hom i := Pi.single (i + 1) (s i)
      zero i j hij := Pi.single_eq_of_ne (Ne.symm hij) _
      comm i := by
        cases i with
        | zero =>
          rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex]
          simpa using h₀.symm
        | succ i =>
          rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
          simpa [add_comm] using (h i).symm }
  intro i
  refine (K.exactAt_iff_isZero_homology i).2 ((IsZero.iff_id_eq_zero _).2 ?_)
  simpa using H.homologyMap_eq i

/-- If an augmented simplicial object has an extra degeneracy, then its alternating-face complex,
augmented by the augmentation, is acyclic: the extra degeneracy is the contraction. -/
public theorem acyclic_augment_of_extraDegeneracy (X : SimplicialObject.Augmented C)
    (ed : X.ExtraDegeneracy) :
    ((AlternatingFaceMapComplex.obj X.left).augment (X.hom.app (op ⦋0⦌))
      (d_one_zero_comp_hom_app X)).Acyclic := by
  refine acyclic_of_contraction _ (fun n => match n with | 0 => ed.s' | n + 1 => ed.s n)
    ed.s'_comp_ε ?_
  intro n
  cases n with
  | zero =>
    simp only [ChainComplex.augment_d_succ_succ, AlternatingFaceMapComplex.obj_d_eq]
    change (show X.left _⦋0⦌ ⟶ X.right from X.hom.app (op ⦋0⦌)) ≫ ed.s' +
      ed.s 0 ≫ (∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) • X.left.δ k) = 𝟙 _
    simp [Fin.sum_univ_succ, ed.s₀_comp_δ₁]
  | succ n =>
    simp only [ChainComplex.augment_d_succ_succ, AlternatingFaceMapComplex.obj_d_eq]
    change (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • X.left.δ k) ≫ ed.s n +
      ed.s (n + 1) ≫ (∑ k : Fin (n + 3), (-1 : ℤ) ^ (k : ℕ) • X.left.δ k) = 𝟙 _
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Preadditive.comp_sum,
      Preadditive.comp_zsmul]
    rw [Fin.sum_univ_succ (n := n + 2)]
    simp only [Fin.val_zero, pow_zero, one_smul, ed.s_comp_δ₀, Fin.val_succ, pow_succ,
      mul_neg_one, neg_smul, ed.s_comp_δ, Finset.sum_neg_distrib]
    abel

/-- **Acyclicity of the augmented simplex complex.** Let `I x` be a nonempty index type for each
`x : α` and `A x` an object of `C`. A chain complex whose degree-`n` term is the coproduct over
`Σ x, Fin n → I x` of `A x`, with differential the alternating sum of the face maps deleting one
entry of the tuple, is acyclic: prepending a chosen index contracts it. -/
public theorem acyclic_of_simplexCoproduct {α : Type u'} (I : α → Type v')
    [∀ x, Nonempty (I x)] (A : α → C) [HasCoproducts.{max u' v'} C] (K : ChainComplex C ℕ)
    (e : ∀ n : ℕ, (∐ fun t : Σ x, Fin n → I x => A t.1) ≅ K.X n)
    (hd : ∀ (n : ℕ) (t : Σ x, Fin (n + 1) → I x),
      Sigma.ι (fun t : Σ x, Fin (n + 1) → I x => A t.1) t ≫ (e (n + 1)).hom ≫ K.d (n + 1) n =
        ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
          (Sigma.ι (fun t : Σ x, Fin n → I x => A t.1) ⟨t.1, t.2 ∘ k.succAbove⟩ ≫ (e n).hom)) :
    K.Acyclic := by
  classical
  let c : ∀ x, I x := fun x => Classical.arbitrary (I x)
  let g (n : ℕ) (x : α) (q : Fin n → I x) : A x ⟶ K.X n :=
    Sigma.ι (fun t : Σ x, Fin n → I x => A t.1) ⟨x, q⟩ ≫ (e n).hom
  let s (n : ℕ) : K.X n ⟶ K.X (n + 1) :=
    (e n).inv ≫ Sigma.desc fun t : Σ x, Fin n → I x => g (n + 1) t.1 (Fin.cons (c t.1) t.2)
  have hs (n : ℕ) (x : α) (q : Fin n → I x) :
      g n x q ≫ s n = g (n + 1) x (Fin.cons (c x) q) := by simp [g, s]
  have hrm : ∀ (m : ℕ) (x : α) (q : Fin (m + 1) → I x) (k : Fin (m + 1)),
      Fin.removeNth k q = q ∘ k.succAbove := fun _ _ _ _ => rfl
  have hd' (n : ℕ) (x : α) (q : Fin (n + 1) → I x) :
      g (n + 1) x q ≫ K.d (n + 1) n =
        ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • g n x (q ∘ k.succAbove) :=
    (Category.assoc _ _ _).trans (hd n ⟨x, q⟩)
  refine acyclic_of_contraction K s ?_ ?_
  · refine (cancel_epi (e 0).hom).1 (Sigma.hom_ext _ _ fun t => ?_)
    simp only [← Category.assoc]
    change (g 0 t.1 t.2 ≫ s 0) ≫ K.d 1 0 = g 0 t.1 t.2 ≫ 𝟙 _
    rw [hs, hd', Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, Category.comp_id]
    rw [show (Fin.cons (c t.1) t.2) ∘ (0 : Fin 1).succAbove = t.2 from Subsingleton.elim _ _]
  · intro n
    refine (cancel_epi (e (n + 1)).hom).1 (Sigma.hom_ext _ _ fun t => ?_)
    simp only [Preadditive.comp_add, ← Category.assoc]
    change (g (n + 1) t.1 t.2 ≫ K.d (n + 1) n) ≫ s n +
      (g (n + 1) t.1 t.2 ≫ s (n + 1)) ≫ K.d (n + 2) (n + 1) = g (n + 1) t.1 t.2 ≫ 𝟙 _
    rw [hd', hs, hd']
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, hs, Category.comp_id]
    rw [Fin.sum_univ_succ (n := n + 1)]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
      Finset.sum_neg_distrib, Fin.cons_comp_succ_succAbove, hrm]
    abel

end AlgebraicTopology.SimplexCoproductAcyclicity

end
