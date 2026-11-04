module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-! # Homotopies as a torsor under `Mor(A^•, B[-1]^•)`

Stacks tag 011I. For morphisms `a b : A^• ⟶ B^•` of cochain complexes, the set of homotopies from
`a` to `b` is either empty or a principal homogeneous space under the group of morphisms of
complexes `A^• ⟶ B[-1]^•`; taking `b = a` and the zero homotopy as base point gives the bijection
between self-homotopies of `a` and that group.

Both clauses are one construction here. `Homotopy.equivHomShift` is the bijection *based at* a
chosen homotopy `h₀`, which is exactly what "principal homogeneous space" says once a point
exists — nonemptiness is the hypothesis, not part of the conclusion. `equivHomShiftSelf` is the
`b = a` case with `Homotopy.refl a` as base point, which is the first sentence of the tag.

The identification is the one the Stacks project describes: `Homotopy.equivHomShift_f` records
that the morphism attached to `h` has components `h.hom p (p-1) - h₀.hom p (p-1)`, the difference
of the two homotopies, and `equivHomShift_self` that the base point goes to `0`.

Note `B[-1]`, not `B[1]`: the chain-complex twin 011C uses `B[1]`, and the asymmetry is real —
each shifts by one in the direction its homotopies move. That twin is
`Homotopy.equivHomShiftChain`, in `StacksCore.Algebra.Homology.HomotopyCategory.HomotopyShift`. It
shares no proof with this file: the `HomComplex`/`Cochain`/`Cocycle` tower used here is
`CochainComplex`-only, so 011C is built directly from `Homotopy` and the `ChainComplex` shift of
011A instead. The `Chain` suffix on its name is forced — Lean does not overload on argument type,
and `Homotopy.equivHomShift` is taken by this file.
-/

@[expose] public section

open CategoryTheory CochainComplex.HomComplex

universe v u

namespace Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {A B : CochainComplex C ℤ} {a b : A ⟶ B}

/-- **Stacks 011I**, second sentence. Given one homotopy `h₀` from `a` to `b`, the homotopies from
`a` to `b` correspond to the morphisms of complexes `A^• ⟶ B[-1]^•`, by `h ↦ h - h₀`. Together
with the fact that the target is a group, this is the assertion that the homotopies from `a` to
`b` form a principal homogeneous space under it whenever they are nonempty. -/
@[stacks 011I, implicit_reducible]
noncomputable def equivHomShift (h₀ : Homotopy a b) : Homotopy a b ≃ (A ⟶ B⟦(-1 : ℤ)⟧) :=
  (Cochain.equivHomotopy a b).trans
    (((Equiv.subtypeEquiv (Equiv.subRight (Cochain.ofHomotopy h₀)) (fun z => by
        have h0 : Cochain.ofHom a = δ (-1) 0 (Cochain.ofHomotopy h₀) + Cochain.ofHom b :=
          (Cochain.equivHomotopy a b h₀).2
        rw [Cocycle.mem_iff (-1) 0 (by norm_num)]
        simp only [Equiv.subRight_apply, δ_sub, sub_eq_zero]
        constructor
        · intro hz; rw [h0] at hz; simpa [eq_comm (a := δ (-1) 0 z), sub_eq_iff_eq_add] using hz
        · intro hz; rw [h0, hz])) :
      { z : Cochain A B (-1) // Cochain.ofHom a = δ (-1) 0 z + Cochain.ofHom b } ≃
        Cocycle A B (-1)).trans
      (Cocycle.equivHomShift (K := A) (L := B) (n := -1)).toEquiv.symm)

/-- **Stacks 011I**, first sentence. The self-homotopies of `a` correspond to the morphisms of
complexes `A^• ⟶ B[-1]^•`. -/
noncomputable def equivHomShiftSelf (a : A ⟶ B) : Homotopy a a ≃ (A ⟶ B⟦(-1 : ℤ)⟧) :=
  equivHomShift (Homotopy.refl a)

/-- The cocycle underlying `equivHomShift h₀ h` is the difference of the two homotopies. -/
theorem equivHomShift_eq (h₀ h : Homotopy a b) :
    equivHomShift h₀ h = Cocycle.equivHomShift.symm
      (Cocycle.mk (Cochain.ofHomotopy h - Cochain.ofHomotopy h₀) 0 (by norm_num)
        (by simp [δ_sub, δ_ofHomotopy])) := rfl

/-- The morphism attached to `h` has components `h.hom p (p-1) - h₀.hom p (p-1)`: the bijection is
subtraction of homotopies, degreewise, as in the Stacks project. -/
theorem equivHomShift_f (h₀ h : Homotopy a b) (p : ℤ) :
    (equivHomShift h₀ h).f p
      = (h.hom p (p + (-1)) - h₀.hom p (p + (-1))) ≫
        (B.shiftFunctorObjXIso (-1) p (p + (-1)) rfl).inv := by
  rw [equivHomShift_eq, Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f, Cocycle.rightShift_coe,
    Cochain.rightShift_v _ _ _ (zero_add (-1)) p p (add_zero p) (p + (-1)) rfl]
  -- change (Cochain.ofHomotopy h - Cochain.ofHomotopy h₀).v _ _ _ ≫ _ = _
  simp only [Int.reduceNeg, CochainComplex.shiftFunctor_obj_X', Cochain.ofHomotopy, Cocycle.mk_coe,
    Cochain.sub_v, Cochain.mk_v, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv]

/-- The base point goes to `0`: this is what makes `equivHomShift h₀` a trivialisation of the
torsor at `h₀` rather than merely a bijection of sets. -/
@[simp]
theorem equivHomShift_self (h₀ : Homotopy a b) : equivHomShift h₀ h₀ = 0 := by
  ext p
  simp [equivHomShift_f]

end Homotopy
