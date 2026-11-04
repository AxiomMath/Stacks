module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.CategoryTheory.Monoidal.RigidAdjunction

/-!
# The internal hom out of a dualizable object is tensoring by its dual

Let `C` be a braided monoidal closed category and let `X` be an object admitting a dual, i.e.
let `X` and `X'` form an exact pairing. Then `- ⊗ X'` and `X ⟶[C] -` are both right adjoint to
`- ⊗ X` — the first by `CategoryTheory.tensorRightAdjunction`, the second by
`CategoryTheory.tensorRightIhomAdjunction` — so they are canonically isomorphic:

`(X ⟶[C] A) ≅ A ⊗ X'`.

This is the identification that makes the internal hom out of a dualizable object computable, and
it specialises at `A = 𝟙_ C` to `CategoryTheory.rightDualIsoIhomUnit`.

## Main definitions

* `CategoryTheory.ihomIsoTensorRight`: the natural isomorphism `- ⊗ X' ≅ X ⟶[C] -`.

## Main results

* `CategoryTheory.uncurry_ihomIsoTensorRight_hom_app`: the component of the isomorphism at `A`,
  read through the closed structure: uncurrying it is the braiding of `X` past `A ⊗ X'` followed
  by the evaluation of the pairing. This is the computation rule a consumer needs, since the
  isomorphism is produced by `CategoryTheory.Adjunction.rightAdjointUniq` and is otherwise
  opaque.
* `CategoryTheory.tensorRightIhomAdjunction_homEquiv_symm` and
  `CategoryTheory.tensorRightAdjunction_counit_app` are the two unfoldings it is assembled from:
  the hom-set bijection of `tensorRightIhomAdjunction` is uncurrying precomposed with the
  braiding, and the counit of `tensorRightAdjunction` is the evaluation of the pairing.

## Implementation notes

`CategoryTheory.rightDualIsoIhomUnit` in
`StacksFrontier.CategoryTheory.Monoidal.Rigid` is the case `A = 𝟙_ C` of this isomorphism, and is
built the same way; it is left as it stands rather than re-derived here, so that nothing
depending on it changes.

Only `BraidedCategory` is needed, not `SymmetricCategory`: the braiding enters through
`CategoryTheory.tensorRightIhomAdjunction`, which rewrites the closed structure's adjunction
`- ⊗ X ⊣ (X ⟶[C] -)` from the left-tensoring convention of `MonoidalClosed` to the
right-tensoring convention of `tensorRightAdjunction`.

## References

* [Stacks Project, Tag 0FFR](https://stacks.math.columbia.edu/tag/0FFR)
* [Stacks Project, Tag 0GWJ](https://stacks.math.columbia.edu/tag/0GWJ)
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonoidalClosed

noncomputable section

namespace CategoryTheory

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

/-- The hom-set bijection of `tensorRightIhomAdjunction` is uncurrying, precomposed with the
braiding which converts between tensoring on the right and on the left. -/
lemma tensorRightIhomAdjunction_homEquiv_symm (X Z A : C) (g : Z ⟶ (ihom X).obj A) :
    ((tensorRightIhomAdjunction X).homEquiv Z A).symm g = (β_ X Z).inv ≫ uncurry g := by
  rw [tensorRightIhomAdjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  rfl

omit [BraidedCategory C] [MonoidalClosed C] in
/-- The counit of the adjunction attached to an exact pairing is the evaluation of the pairing. -/
lemma tensorRightAdjunction_counit_app (X X' A : C) [ExactPairing X X'] :
    (tensorRightAdjunction X X').counit.app A
      = (α_ A X' X).hom ≫ A ◁ ε_ X X' ≫ (ρ_ A).hom := by
  rw [← Adjunction.homEquiv_symm_id, tensorRightAdjunction_homEquiv]
  simp [tensorRightHomEquiv]

/-- **The internal hom out of a dualizable object is tensoring by its dual.** For an exact
pairing `(X, X')` the functors `- ⊗ X'` and `X ⟶[C] -` are both right adjoint to `- ⊗ X`, hence
isomorphic. -/
def ihomIsoTensorRight (X X' : C) [ExactPairing X X'] : tensorRight X' ≅ ihom X :=
  (tensorRightAdjunction X X').rightAdjointUniq (tensorRightIhomAdjunction X)

/-- The component of `ihomIsoTensorRight` at `A`, read through the closed structure: uncurrying
`A ⊗ X' ⟶ (X ⟶[C] A)` braids the argument `X` past `A ⊗ X'` and then evaluates it against the
`X'` factor. -/
lemma uncurry_ihomIsoTensorRight_hom_app (X X' : C) [ExactPairing X X'] (A : C) :
    uncurry ((ihomIsoTensorRight X X').hom.app A)
      = (β_ X (A ⊗ X')).hom ≫ (α_ A X' X).hom ≫ A ◁ ε_ X X' ≫ (ρ_ A).hom := by
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (tensorRightAdjunction X X') (tensorRightIhomAdjunction X) A
  rw [tensorRightIhomAdjunction_homEquiv_symm, tensorRightAdjunction_counit_app,
    Iso.inv_comp_eq] at h
  exact h.trans (by simp)

end CategoryTheory
