module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The strength of an internal-hom adjunction

For an adjunction `- ⊗ M ⊣ H` in a monoidal category `C` and objects `K`, `L` of `C`, the
*strength* is the morphism `K ⊗ H(L) ⟶ H(K ⊗ L)` adjoint to the associator followed by `K ⊗ -`
of the counit. It is the diagonal morphism of [Stacks, Tag 0BYS] in its purely
adjunction-theoretic form.

## Main results

* `CategoryTheory.MonoidalCategory.internalHomStrength`: the strength `K ⊗ H(L) ⟶ H(K ⊗ L)`.
* `CategoryTheory.MonoidalCategory.isIso_internalHomStrength_of_source_dual`: the strength is an
  isomorphism when `M` has a left dual.

## Implementation notes

`Stacks.DerivedTensorHomDiagonal` in `StacksFrontier/Homology/HomComplex/Evaluation/TensorHom.lean`
carries a private copy of this construction for its own use; this module is the public one.

## References

* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- **The strength of an internal-hom adjunction.**  For an adjunction `- ⊗ M ⊣ H` in a
monoidal category, the morphism `K ⊗ H(L) ⟶ H(K ⊗ L)` adjoint to the associator followed by
`K ⊗ -` of the counit.  This is the diagonal morphism of [Stacks, Tag 0BYS] in its purely
adjunction-theoretic form. -/
noncomputable def internalHomStrength {M : C} {H : C ⥤ C} (a : tensorRight M ⊣ H) (K L : C) :
    K ⊗ H.obj L ⟶ H.obj (K ⊗ L) :=
  a.homEquiv _ _ ((α_ K (H.obj L) M).hom ≫ K ◁ a.counit.app L)

/-- **The strength is invertible when the internal-hom source is dualizable.**  If `M` has a
left dual `N` then `- ⊗ N` is a right adjoint of `- ⊗ M`, hence isomorphic to `H`, and the
strength becomes the associator. -/
theorem isIso_internalHomStrength_of_source_dual {M N : C} [ExactPairing M N] {H : C ⥤ C}
    (a : tensorRight M ⊣ H) (K L : C) : IsIso (internalHomStrength a K L) := by
  let b := tensorRightAdjunction M N
  let e := b.rightAdjointUniq a
  have he (X : C) : e.hom.app X ▷ M ≫ a.counit.app X = b.counit.app X :=
    b.rightAdjointUniq_hom_app_counit a X
  have hh : K ◁ e.hom.app L ≫ internalHomStrength a K L =
      (α_ K L N).inv ≫ e.hom.app (K ⊗ L) := by
    apply (a.homEquiv _ _).symm.injective
    rw [a.homEquiv_naturality_left_symm, a.homEquiv_naturality_left_symm]
    simp only [internalHomStrength, Equiv.symm_apply_apply]
    rw [a.homEquiv_symm_apply]
    show (K ◁ e.hom.app L) ▷ M ≫ (α_ K (H.obj L) M).hom ≫ K ◁ a.counit.app L =
      (α_ K L N).inv ▷ M ≫ e.hom.app (K ⊗ L) ▷ M ≫ a.counit.app (K ⊗ L)
    rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, he, he]
    have hc (X : C) : b.counit.app X = (α_ X N M).hom ≫ X ◁ ε_ M N ≫ (ρ_ X).hom := by
      show (𝟙 (X ⊗ N)) ▷ M ≫ _ = _
      simp
    rw [hc, hc]
    monoidal
  have : IsIso (K ◁ e.hom.app L ≫ internalHomStrength a K L) := by rw [hh]; infer_instance
  exact IsIso.of_isIso_comp_left (K ◁ e.hom.app L) _

end CategoryTheory.MonoidalCategory

end
