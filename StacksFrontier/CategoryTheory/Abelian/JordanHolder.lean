module

public import Mathlib.Order.JordanHolder
public import StacksCore.CategoryTheory.Abelian.JordanHolder
public import StacksFrontier.CategoryTheory.Subobject.Butterfly
public import StacksFrontier.CategoryTheory.Subobject.CokernelOfLE
import StacksCore.Tactic.StacksAttribute

/-!
# The Jordan–Hölder lemma in an abelian category

Stacks 0FCK: in an abelian category, two finite filtrations
`0 = A₀ ⊆ A₁ ⊆ ⋯ ⊆ Aₙ = X` and `0 = B₀ ⊆ B₁ ⊆ ⋯ ⊆ Bₘ = X` of an object `X` with simple
successive quotients `Aᵢ₊₁/Aᵢ` and `Bⱼ₊₁/Bⱼ` have the same length, and their quotients agree
up to a permutation and isomorphism.

The proof applies mathlib's order-theoretic `CompositionSeries.jordan_holder` to the lattice
`Subobject X`, which is a Jordan–Hölder lattice because it is modular (the instance in
`StacksCore.CategoryTheory.Abelian.Subobject`), with covering `A ⋖ B` as its maximality relation.
Two bridges translate between the lattice and the category:

* `Subobject.covBy_iff_simple_cokernel_ofLE`: for `A ≤ B`, `B` covers `A` exactly when the
  quotient `B/A` is simple. The forward direction is `Subobject.simple_cokernel_ofLE`; the
  converse, proved here, is what turns a filtration with simple quotients into a composition
  series.
* `Subobject.cokernelSupIsoInf`: the second isomorphism theorem `(x ⊔ y)/x ≅ y/(x ⊓ y)`, which
  turns the formal equivalence `JordanHolderLattice.Iso` of intervals into isomorphism of
  their quotients.

## Main results

* `CategoryTheory.Subobject.covBy_of_simple_cokernel_ofLE`,
  `CategoryTheory.Subobject.covBy_iff_simple_cokernel_ofLE`.
* `CategoryTheory.Subobject.cokernelSupIsoInf`.
* `CategoryTheory.Subobject.jordan_holder`: Stacks 0FCK.
-/

@[expose] public section

namespace CategoryTheory.Subobject

open Limits

variable {C : Type*} [Category* C] [Abelian C] {X : C}

/-- If the quotient `B/A` of subobjects `A ≤ B` is simple, then `B` covers `A`. A subobject
`A ≤ Z ≤ B` maps to the simple object `B/A` either by zero, and then `Z ≤ A`, or onto it, and
then `B = Z + A = Z`. -/
lemma covBy_of_simple_cokernel_ofLE {A B : Subobject X} (h : A ≤ B)
    [Simple (cokernel (ofLE A B h))] : A ⋖ B := by
  have hlt : A < B := lt_of_le_of_ne h fun hAB => by
    subst hAB
    refine Simple.not_isZero (cokernel (ofLE A A h)) ?_
    have : Epi (ofLE A A h) := by rw [ofLE_refl]; infer_instance
    exact isZero_cokernel_of_epi _
  refine ⟨hlt, fun Z hAZ hZB => ?_⟩
  let u := ofLE Z B hZB.le
  let π := cokernel.π (ofLE A B h)
  by_cases hu : u ≫ π = 0
  · have hf := (comp_cokernel_π_eq_zero_iff (ofLE A B h) (ofLE_arrow h) u).1 hu
    rw [ofLE_arrow] at hf
    exact hAZ.not_ge (le_of_factors hf)
  · have : Epi (u ≫ π) := epi_of_nonzero_to_simple hu
    obtain ⟨T, w, _, z, hz⟩ := surjective_up_to_refinements_of_epi (u ≫ π) π
    have h1 : (w - z ≫ u) ≫ π = 0 := by
      rw [Preadditive.sub_comp, hz, Category.assoc, sub_self]
    have h2 : A.Factors ((w - z ≫ u) ≫ B.arrow) :=
      (comp_cokernel_π_eq_zero_iff (ofLE A B h) (ofLE_arrow h) _).1 h1
    have h3 : Z.Factors ((z ≫ u) ≫ B.arrow) := by
      rw [Category.assoc, ofLE_arrow]
      exact factors_comp_arrow z
    have h4 : Z.Factors (w ≫ B.arrow) := by
      have := factors_add _ _ (factors_of_le _ hAZ.le h2) h3
      rwa [← Preadditive.add_comp, sub_add_cancel] at this
    exact hZB.not_ge (le_of_factors (factors_of_epi_comp w _ h4))

/-- For subobjects `A ≤ B`, `B` covers `A` if and only if the quotient `B/A` is simple. -/
lemma covBy_iff_simple_cokernel_ofLE {A B : Subobject X} (h : A ≤ B) :
    A ⋖ B ↔ Simple (cokernel (ofLE A B h)) :=
  ⟨simple_cokernel_ofLE h, fun _ => covBy_of_simple_cokernel_ofLE h⟩

/-- The second isomorphism theorem for subobjects: `(x ⊔ y)/x ≅ y/(x ⊓ y)`, both being
quotients of `y`, by the same kernel `x ⊓ y`. -/
lemma nonempty_cokernelSupIsoInf (x y : Subobject X) :
    Nonempty (cokernel (ofLE x (x ⊔ y) _root_.le_sup_left) ≅
      cokernel (ofLE (x ⊓ y) y _root_.inf_le_right)) := by
  have : Epi (ofLE y (x ⊔ y) _root_.le_sup_right ≫
      cokernel.π (ofLE x (x ⊔ y) _root_.le_sup_left)) :=
    epi_ofLE_comp_cokernel_π _ (ofLE_arrow _) _root_.le_sup_right (_root_.sup_comm x y).le le_rfl
  have : Epi (𝟙 (y : C) ≫ cokernel.π (ofLE (x ⊓ y) y _root_.inf_le_right)) := by
    rw [Category.id_comp]
    infer_instance
  obtain ⟨e, -⟩ := exists_iso_cokernel_of_factors_iff (ofLE x (x ⊔ y) _root_.le_sup_left)
    (ofLE_arrow _) (ofLE (x ⊓ y) y _root_.inf_le_right) (ofLE_arrow _)
    (ofLE y (x ⊔ y) _root_.le_sup_right) (𝟙 _) (fun g => by
      simp only [ofLE_arrow, Category.id_comp, inf_factors]
      exact ⟨fun hg => ⟨hg, factors_comp_arrow g⟩, fun hg => hg.1⟩)
  exact ⟨e⟩

/-- The second isomorphism theorem for subobjects of an object of an abelian category:
`(x ⊔ y)/x ≅ y/(x ⊓ y)`. -/
noncomputable def cokernelSupIsoInf (x y : Subobject X) :
    cokernel (ofLE x (x ⊔ y) _root_.le_sup_left) ≅ cokernel (ofLE (x ⊓ y) y _root_.inf_le_right) :=
  (nonempty_cokernelSupIsoInf x y).some

/-- Intervals `p`, `q` of `Subobject X` related by the Jordan–Hölder equivalence
`JordanHolderLattice.Iso` have isomorphic quotients `(p.1 ⊔ p.2)/p.1 ≅ (q.1 ⊔ q.2)/q.1`. -/
lemma nonempty_iso_of_jordanHolderLatticeIso {p q : Subobject X × Subobject X}
    (hpq : JordanHolderLattice.Iso p q) :
    Nonempty (cokernel (ofLE p.1 (p.1 ⊔ p.2) _root_.le_sup_left) ≅
      cokernel (ofLE q.1 (q.1 ⊔ q.2) _root_.le_sup_left)) := by
  refine JordanHolderLattice.Iso.rel
    (fun p q : Subobject X × Subobject X =>
      Nonempty (cokernel (ofLE p.1 (p.1 ⊔ p.2) _root_.le_sup_left) ≅
        cokernel (ofLE q.1 (q.1 ⊔ q.2) _root_.le_sup_left)))
    ⟨Iso.refl _⟩ (fun ⟨e⟩ => ⟨e.symm⟩) (fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩) (fun {x y} _ => ?_) hpq
  exact ⟨cokernelOfLEIsoOfEq (W' := x) (N' := x ⊔ y) _ _ rfl (_root_.sup_left_idem x y) ≪≫
    cokernelSupIsoInf x y ≪≫
    cokernelOfLEIsoOfEq _ _ rfl (_root_.sup_eq_right.2 _root_.inf_le_right).symm⟩

/-- **Stacks 0FCK (Jordan–Hölder).** Let `X` be an object of an abelian category with two
filtrations `0 = a 0 ⊆ a 1 ⊆ ⋯ ⊆ a n = X` and `0 = b 0 ⊆ b 1 ⊆ ⋯ ⊆ b m = X` by subobjects whose
successive quotients `a (i + 1) / a i` and `b (j + 1) / b j` are simple. Then `n = m`, and there
is a permutation `σ : Fin n ≃ Fin m` with `a (i + 1) / a i ≅ b (σ i + 1) / b (σ i)` for every `i`.

Stacks indexes the quotients `Sᵢ = Aᵢ/Aᵢ₋₁` by `1 ≤ i ≤ n`; here the quotient `a (i + 1) / a i`
is indexed by `i : Fin n`. Stacks assumes `X` satisfies the equivalent conditions of 0FCJ
(Artinian and Noetherian); by 0FCJ (`isArtinianObject_and_isNoetherianObject_iff_exists_filtration`)
this already follows from either filtration, so it is not assumed separately. -/
@[stacks 0FCK "the quotient `a (i + 1) / a i` is indexed by `i : Fin n`; the Artinian and \
Noetherian hypothesis of Stacks follows from the filtrations by 0FCJ and is not assumed"]
theorem jordan_holder (a : ℕ → Subobject X) (n : ℕ) (ha : ∀ i, i < n → a i ≤ a (i + 1))
    (ha0 : a 0 = ⊥) (han : a n = ⊤)
    (hsa : ∀ i (hi : i < n), Simple (cokernel (ofLE _ _ (ha i hi))))
    (b : ℕ → Subobject X) (m : ℕ) (hb : ∀ j, j < m → b j ≤ b (j + 1))
    (hb0 : b 0 = ⊥) (hbm : b m = ⊤)
    (hsb : ∀ j (hj : j < m), Simple (cokernel (ofLE _ _ (hb j hj)))) :
    n = m ∧ ∃ σ : Fin n ≃ Fin m, ∀ i : Fin n,
      Nonempty (cokernel (ofLE _ _ (ha i i.2)) ≅ cokernel (ofLE _ _ (hb (σ i) (σ i).2))) := by
  let s : CompositionSeries (Subobject X) :=
    { length := n
      toFun := fun i => a i
      step := fun i => by
        have := hsa i i.2
        exact covBy_of_simple_cokernel_ofLE (A := a i) (B := a (i + 1)) (ha i i.2) }
  let t : CompositionSeries (Subobject X) :=
    { length := m
      toFun := fun j => b j
      step := fun j => by
        have := hsb j j.2
        exact covBy_of_simple_cokernel_ofLE (A := b j) (B := b (j + 1)) (hb j j.2) }
  obtain ⟨σ, hσ⟩ := CompositionSeries.jordan_holder s t
    (show a 0 = b 0 by rw [ha0, hb0]) (show a n = b m by rw [han, hbm])
  refine ⟨by simpa using Fintype.card_congr σ, σ, fun i => ?_⟩
  obtain ⟨e⟩ := nonempty_iso_of_jordanHolderLatticeIso (hσ i)
  exact ⟨cokernelOfLEIsoOfEq _ _ rfl (_root_.sup_eq_right.2 (ha i i.2)).symm ≪≫ e ≪≫
    cokernelOfLEIsoOfEq _ _ rfl (_root_.sup_eq_right.2 (hb _ (σ i).2))⟩

end CategoryTheory.Subobject
