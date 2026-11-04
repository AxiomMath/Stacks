module

public import StacksCore.Algebra.Homology.HomotopyCategory.Shift

/-! # Homotopies of chain complexes as a torsor under `Mor(A_•, B[1]_•)`

Stacks tag 011C. For morphisms `a b : A_• ⟶ B_•` of chain complexes, the set of homotopies from
`a` to `b` is either empty or a principal homogeneous space under the group of morphisms of
complexes `A_• ⟶ B[1]_•`; taking `b = a` and the zero homotopy as base point gives the bijection
between self-homotopies of `a` and that group.

This is the chain-complex twin of tag 011I, which is in
`StacksCore.Algebra.Homology.HomotopyCategory.HomComplexShift`. Note `B[1]`, not `B[-1]`: a homotopy
of chain complexes is a family `h_i : A_i ⟶ B_{i+1}`, because `Homotopy.hom i j` is required to
vanish unless `c.Rel j i`, which for `ComplexShape.down ℤ` reads `i + 1 = j`. The asymmetry with
011I is exactly the chain/cochain convention and nothing more.

**The sign of tag 011G is what makes the tag true.** The Stacks project's own computation is that
a self-homotopy satisfies `0 = d_{i+1} ∘ h_i + h_{i-1} ∘ d_i`, and that this is the condition for
`h` to be a morphism into `B[1]`. That reading needs `d_{B[1]} = -d_B`, which is the `k = 1` case
of the `(-1)^k` in `ChainComplex.shiftFunctor` (011A). Without it the family would be an
*anti*-morphism of complexes and the tag would be false as stated; the unsigned variant is not
provable.

Both clauses of the tag are the single construction `Homotopy.equivHomShiftChain`, which is the
bijection *based at* a chosen homotopy `h₀` — that is what "principal homogeneous space" says once
a point exists, nonemptiness being the hypothesis rather than part of the conclusion. The name
carries a `Chain` suffix because 011I already occupies `Homotopy.equivHomShift`, and Lean does not
overload on argument type.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {A B : ChainComplex C ℤ} {a b : A ⟶ B}

/-- The difference of two homotopies from `a` to `b`, as a morphism of complexes `A_• ⟶ B[1]_•`.
The homotopy relations for `h` and `h₀` differ by the relation making this a chain map. -/
def homotopySub (h₀ h : Homotopy a b) : A ⟶ B⟦(1 : ℤ)⟧ where
  f i := (h.hom i (i + 1) - h₀.hom i (i + 1)) ≫ (B.shiftFunctorObjXIso 1 i (i + 1) rfl).inv
  comm' i j (hij : j + 1 = i) := by
    subst hij
    have e1 := h.comm (j + 1)
    have e2 := h₀.comm (j + 1)
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (j + 1) j by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (j + 1 + 1) (j + 1) by simp)] at e1 e2
    rw [e1] at e2
    simp only [shiftFunctor_obj_d', Int.negOnePow_one, Units.neg_smul, one_smul,
      shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id,
      Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_neg]
    have e3 : A.d (j + 1) j ≫ h.hom j (j + 1) + h.hom (j + 1) (j + 1 + 1) ≫ B.d (j + 1 + 1) (j + 1)
        = A.d (j + 1) j ≫ h₀.hom j (j + 1) + h₀.hom (j + 1) (j + 1 + 1) ≫ B.d (j + 1 + 1) (j + 1) :=
      add_right_cancel e2
    rw [neg_sub, sub_eq_sub_iff_add_eq_add, e3]
    abel

@[simp]
lemma homotopySub_f (h₀ h : Homotopy a b) (i : ℤ) :
    (homotopySub h₀ h).f i =
      (h.hom i (i + 1) - h₀.hom i (i + 1)) ≫ (B.shiftFunctorObjXIso 1 i (i + 1) rfl).inv := rfl

/-- Translating a homotopy from `a` to `b` by a morphism of complexes `A_• ⟶ B[1]_•`. This is the
inverse of `homotopySub h₀`, and exhibits the action of the group on the set of homotopies. -/
def homotopyAdd (h₀ : Homotopy a b) (f : A ⟶ B⟦(1 : ℤ)⟧) : Homotopy a b where
  hom i j := if hij : i + 1 = j then f.f i ≫ (B.XIsoOfEq hij).hom + h₀.hom i j else 0
  zero i j hij := dite_eq_right hij
  comm i := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by lia⟩
    have e0 := h₀.comm (j + 1)
    have hf := f.comm (j + 1) j
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (j + 1) j by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (j + 1 + 1) (j + 1) by simp)] at e0 ⊢
    rw [dite_eq_left (rfl : j + 1 = j + 1), dite_eq_left (rfl : j + 1 + 1 = j + 1 + 1)]
    simp only [XIsoOfEq_rfl, Iso.refl_hom]
    -- the identities sit at `B.X (j+1)`, the arrows at `(B⟦1⟧).X j`; `comp_id` cannot fire until
    -- the two spellings are made to agree
    dsimp only [shiftFunctor_obj_X']
    rw [Category.comp_id, Category.comp_id]
    simp only [shiftFunctor_obj_d', Int.negOnePow_one, Units.neg_smul, one_smul,
      Preadditive.comp_neg] at hf
    rw [Preadditive.comp_add, Preadditive.add_comp, e0, ← hf]
    abel

@[simp]
lemma homotopyAdd_hom (h₀ : Homotopy a b) (f : A ⟶ B⟦(1 : ℤ)⟧) (i j : ℤ) (hij : i + 1 = j) :
    (homotopyAdd h₀ f).hom i j = f.f i ≫ (B.XIsoOfEq hij).hom + h₀.hom i j :=
  dite_eq_left hij

end ChainComplex

namespace Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {A B : ChainComplex C ℤ} {a b : A ⟶ B}

/-- **Stacks 011C**, second sentence. Given one homotopy `h₀` from `a` to `b`, the homotopies from
`a` to `b` correspond to the morphisms of complexes `A_• ⟶ B[1]_•`, by `h ↦ h - h₀`. Together with
the fact that the target is a group, this is the assertion that the homotopies from `a` to `b`
form a principal homogeneous space under it whenever they are nonempty. -/
@[stacks 011C, implicit_reducible]
def equivHomShiftChain (h₀ : Homotopy a b) : Homotopy a b ≃ (A ⟶ B⟦(1 : ℤ)⟧) where
  toFun := ChainComplex.homotopySub h₀
  invFun := ChainComplex.homotopyAdd h₀
  left_inv h := by
    ext i j
    by_cases hij : i + 1 = j
    · subst hij
      simp [ChainComplex.homotopyAdd, ChainComplex.homotopySub,
        ChainComplex.shiftFunctorObjXIso]
    · dsimp only [ChainComplex.homotopyAdd]
      rw [dite_eq_right hij, h.zero i j hij]
  right_inv f := by
    ext i
    simp [ChainComplex.homotopyAdd, ChainComplex.homotopySub,
      ChainComplex.shiftFunctorObjXIso]

/-- **Stacks 011C**, first sentence. The self-homotopies of `a` correspond to the morphisms of
complexes `A_• ⟶ B[1]_•`. -/
@[stacks 011C "first sentence, the `b = a` case based at the zero homotopy"]
def equivHomShiftChainSelf (a : A ⟶ B) : Homotopy a a ≃ (A ⟶ B⟦(1 : ℤ)⟧) :=
  equivHomShiftChain (Homotopy.refl a)

/-- The morphism attached to `h` has components `h.hom p (p+1) - h₀.hom p (p+1)`: the bijection is
subtraction of homotopies, degreewise, as in the Stacks project. -/
theorem equivHomShiftChain_f (h₀ h : Homotopy a b) (p : ℤ) :
    (equivHomShiftChain h₀ h).f p
      = (h.hom p (p + 1) - h₀.hom p (p + 1)) ≫ (B.shiftFunctorObjXIso 1 p (p + 1) rfl).inv := rfl

/-- The inverse of the bijection adds `f` to the base point, degreewise. -/
theorem equivHomShiftChain_symm_hom (h₀ : Homotopy a b) (f : A ⟶ B⟦(1 : ℤ)⟧) (p q : ℤ)
    (hpq : p + 1 = q) :
    ((equivHomShiftChain h₀).symm f).hom p q = f.f p ≫ (B.XIsoOfEq hpq).hom + h₀.hom p q :=
  ChainComplex.homotopyAdd_hom h₀ f p q hpq

/-- The base point goes to `0`: this is what makes `equivHomShiftChain h₀` a trivialisation of the
torsor at `h₀` rather than merely a bijection of sets. -/
@[simp]
theorem equivHomShiftChain_self (h₀ : Homotopy a b) : equivHomShiftChain h₀ h₀ = 0 := by
  ext p
  simp [equivHomShiftChain_f]

/-- Changing the base point translates the bijection, which is the remaining torsor axiom. -/
theorem equivHomShiftChain_sub (h₀ h₁ h : Homotopy a b) :
    equivHomShiftChain h₀ h - equivHomShiftChain h₀ h₁ = equivHomShiftChain h₁ h := by
  ext p
  simp [equivHomShiftChain_f]

end Homotopy
