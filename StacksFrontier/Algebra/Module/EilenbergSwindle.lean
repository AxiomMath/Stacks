module

public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

@[expose] public section

/-
# Problem Description

Eilenberg's lemma (the Eilenberg swindle), Stacks Project Tag 0GVF.

Fix a (not necessarily commutative) ring `R` with unit, and work in the category
of left `R`-modules. Let `P`, `Q`, `F` be left `R`-modules. Suppose that

* `P ⊕ Q ≅ F`, and
* `F` is a free left `R`-module that is **not** finitely generated.

Then `P ⊕ F ≅ F`.
-/

-- # Background and context (as comments)
--
-- * Source. Stacks Project Tag 0GVF, "Eilenberg's lemma" (the Eilenberg swindle),
--   attributed to Eilenberg via Bass.
--
-- * The hypothesis that `F` is free and non-finitely-generated is used to obtain an
--   isomorphism `F ≅ F^(ℕ)` with a countably infinite direct sum of copies of `F`.
--   The standard proof runs:
--     `P ⊕ F ≅ P ⊕ (P ⊕ Q)^(ℕ) = P ⊕ (Q ⊕ P) ⊕ (Q ⊕ P) ⊕ ⋯ ≅ (P ⊕ Q)^(ℕ) ≅ F`.
--
-- * Generality of the ring. The statement and its proof do not require `R` to be
--   commutative; we formalize over an arbitrary ring `R`.
--
-- * What is to be proven. The conclusion is purely the existence of an `R`-module
--   isomorphism `P ⊕ F ≅ F` (equivalently a `LinearEquiv` between `P × F` and `F`);
--   no naturality or compatibility with the given data is required.
--
-- * Edge case (`R = 0`). If `R` is the zero ring, every module is the zero module and
--   no free module can fail to be finitely generated, so the hypotheses are vacuous
--   and the statement holds trivially.

-- # Main Definition(s)
--
-- We use the standard Mathlib notions:
-- * The external direct sum `P ⊕ Q` of two left `R`-modules is modeled by the product
--   type `P × Q` (the binary biproduct in the category of `R`-modules).
-- * "`F` is free" is `Module.Free R F`: `F` admits a basis.
-- * "`F` is finitely generated" is `Module.Finite R F`; "non-finitely-generated" is
--   its negation.
-- * "`A ≅ B`" (isomorphic as left `R`-modules) is `Nonempty (A ≃ₗ[R] B)`.

-- # Main Statement(s)

/-- Codomain product split of a finsupp:
`(α →₀ M × N) ≃ₗ[R] (α →₀ M) × (α →₀ N)`. -/
noncomputable def prodSplit (R α M N : Type*) [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] :
    (α →₀ M × N) ≃ₗ[R] (α →₀ M) × (α →₀ N) where
  toFun f := (f.mapRange Prod.fst rfl, f.mapRange Prod.snd rfl)
  invFun p := Finsupp.zipWith Prod.mk rfl p.1 p.2
  left_inv f := by ext a <;> simp
  right_inv := by rintro ⟨g, h⟩; ext a <;> simp
  map_add' x y := by ext a <;> simp
  map_smul' c x := by ext a <;> simp

/-- Shift isomorphism `(ℕ →₀ A) ≃ₗ[R] A × (ℕ →₀ A)`.
(Named `finsuppShiftNat` to avoid a clash with `CategoryTheory.shift` in the
stacks environment.) -/
noncomputable def finsuppShiftNat (R A : Type*) [Semiring R] [AddCommMonoid A]
    [Module R A] : (ℕ →₀ A) ≃ₗ[R] A × (ℕ →₀ A) :=
  (Finsupp.domLCongr
      (Classical.choice (nonempty_equiv_of_countable (α := Unit ⊕ ℕ) (β := ℕ))).symm).trans
    ((Finsupp.sumFinsuppLEquivProdFinsupp R).trans
      ((Finsupp.uniqueLinearEquiv R A ()).prodCongr (LinearEquiv.refl R _)))

/-- **Eilenberg's lemma / Eilenberg swindle (Stacks Tag 0GVF).**
Let `R` be a ring and `P`, `Q`, `F` left `R`-modules with `P ⊕ Q ≅ F`, where `F` is a
free left `R`-module that is not finitely generated. Then `P ⊕ F ≅ F`. -/
@[stacks 0GVF]
theorem eilenberg_swindle {R : Type*} [Ring R] (P Q F : Type*) [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [AddCommGroup F] [Module R F] [Module.Free R F]
    (h : Nonempty ((P × Q) ≃ₗ[R] F)) (hnfg : ¬ Module.Finite R F) :
    Nonempty ((P × F) ≃ₗ[R] F) := by
  obtain ⟨hPQ⟩ := h
  let b := Module.Free.chooseBasis R F
  have : Infinite (Module.Free.ChooseBasisIndex R F) :=
    not_finite_iff_infinite.mp fun _ ↦ hnfg (.of_basis b)
  obtain ⟨eNι⟩ : Nonempty (ℕ × Module.Free.ChooseBasisIndex R F ≃
      Module.Free.ChooseBasisIndex R F) := by
    rw [← Cardinal.eq, Cardinal.mk_prod, Cardinal.mk_eq_aleph0]
    simp
  let eS : F ≃ₗ[R] (ℕ →₀ P × Q) :=
    ((Finsupp.mapRange.linearEquiv b.repr).trans ((Finsupp.curryLinearEquiv R).symm.trans
      ((Finsupp.domLCongr eNι).trans b.repr.symm))).symm.trans
      (Finsupp.mapRange.linearEquiv hPQ.symm)
  let split := prodSplit R ℕ P Q
  exact ⟨((LinearEquiv.refl R P).prodCongr eS).trans
    ((((LinearEquiv.refl R P).prodCongr split).trans
      ((LinearEquiv.prodAssoc R P (ℕ →₀ P) (ℕ →₀ Q)).symm.trans
        (((finsuppShiftNat R P).symm.prodCongr (LinearEquiv.refl R _)).trans
          split.symm))).trans eS.symm)⟩
