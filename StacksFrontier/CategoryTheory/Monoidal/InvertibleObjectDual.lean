module

public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.CategoryTheory.Monoidal.RigidAdjunction

/-!
# An invertible object and its inverse form an exact pairing

Let `C` be a monoidal category and let `L` be an object admitting a two-sided tensor inverse
`L'`, i.e. a `CategoryTheory.MonoidalCategory.HasInverse L` — isomorphisms `L ⊗ L' ≅ 𝟙_ C` and
`L' ⊗ L ≅ 𝟙_ C`, with no compatibility between them. Then `L'` is a **left dual** of `L` in the
sense of Categories, Definition 0FFP: there are a coevaluation `η : 𝟙_ C ⟶ L ⊗ L'` and an
evaluation `ε : L' ⊗ L ⟶ 𝟙_ C` satisfying the two triangle identities, which is Mathlib's
`CategoryTheory.ExactPairing L L'`.

The coevaluation of the pairing produced below *is* `h.isoLeft.inv`, which
`HasInverse.coevaluation_exactPairing` records; the evaluation, however, is **not**
`h.isoRight.hom`. An exact pairing is more than a pair of isomorphisms: with the coevaluation
fixed, the evaluation is determined, and the one the `HasInverse` datum happens to carry need not
be it. The adjunction below supplies the one that is.

## Main results

* `CategoryTheory.MonoidalCategory.HasInverse.hasInverseInv`: the inverse of an invertible object
  is invertible, with inverse the object itself.
* `CategoryTheory.MonoidalCategory.HasInverse.tensorRightAdjunction`: the adjunction
  `tensorRight L ⊣ tensorRight L'` whose hom-set bijection is
  `f ↦ (unit iso) ≫ f ▷ L'`, written out so that its tensor compatibility is checkable.
* `CategoryTheory.MonoidalCategory.HasInverse.isTensorCompatible`: that adjunction is compatible
  with the tensor structure in the sense of `CategoryTheory.Adjunction.IsTensorCompatible`
  (Stacks 0FFR).
* `CategoryTheory.MonoidalCategory.HasInverse.exactPairing`: hence `ExactPairing L h.inv`.
* `CategoryTheory.MonoidalCategory.HasInverse.coevaluation_exactPairing`: its coevaluation is the
  given isomorphism `𝟙_ C ≅ L ⊗ L'`, which pins the pairing down rather than leaving it an
  unconstrained inhabitant of its type.
* `CategoryTheory.MonoidalCategory.IsInvertible.exists_exactPairing`: an invertible object has a
  left dual.
* `CategoryTheory.MonoidalCategory.hasInverseUnit`: the unit object is invertible, so the
  hypothesis of the two preceding results has an inhabitant over every monoidal category and
  neither is vacuous.

## Implementation notes

This is a step of the proof of Stacks 0FPG, clause (1) ⟹ clause (2) — the source's "then `N` is
a left dual for `M` in the monoidal category `D(𝒪_X)` and we conclude that `M` is perfect by
Lemma 0FPD" — and not a clause of any tag, so nothing here carries a `@[stacks …]` attribute.

The route is the converse half of Stacks 0FFR, `CategoryTheory.Adjunction.IsTensorCompatible`
of `StacksFrontier.CategoryTheory.Monoidal.RigidAdjunction`: a tensor-compatible adjunction
`tensorRight L ⊣ tensorRight L'` *is* an exact pairing. Going through it avoids the usual
difficulty, that the candidate `η := h.isoLeft.inv` and `ε := h.isoRight.hom` read off a
`HasInverse` do **not** satisfy the triangle identities — the evaluation has to be corrected by
an automorphism of the unit, and the adjunction performs that correction.

The adjunction is **not** `h.tensorRightEquivalence.toAdjunction`. `CategoryTheory.Equivalence.mk`
replaces the unit it is given by `CategoryTheory.Equivalence.adjointifyη` of it, so the unit of
that adjunction is a long composite rather than the natural isomorphism `unitIso` below, and
tensor compatibility — which is a statement about the hom-set bijection — becomes unreadable.
Here the bijection is built by hand out of `unitIso` and the full faithfulness of
`tensorRight L'`, so `homEquiv_apply` is an equation one can rewrite with, and the tensor
compatibility reduces to `unitIso_whiskerLeft`, a single pentagon-and-naturality identity.

## References

* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 0FFR](https://stacks.math.columbia.edu/tag/0FFR)
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

namespace CategoryTheory.MonoidalCategory

open CategoryTheory MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace HasInverse

variable {L : C} (h : HasInverse L)

/-- The inverse of an invertible object is invertible, with inverse the object itself. -/
def hasInverseInv : HasInverse h.inv where
  inv := L
  isoLeft := h.isoRight
  isoRight := h.isoLeft

/-- Tensoring on the right by the inverse of an invertible object is an equivalence. -/
theorem isEquivalence_tensorRight_inv : (tensorRight h.inv).IsEquivalence :=
  h.hasInverseInv.tensorRightEquivalence.isEquivalence_functor

/-- The full faithfulness of `- ⊗ L'`, which makes `f ↦ f ▷ L'` a bijection on hom-sets. -/
def fullyFaithfulTensorRightInv : (tensorRight h.inv).FullyFaithful :=
  have := h.isEquivalence_tensorRight_inv
  .ofFullyFaithful _

/-- The unit isomorphism `A ≅ (A ⊗ L) ⊗ L'` of the two-sided inverse: the right unitor followed
by the inverse of `L ⊗ L' ≅ 𝟙_ C` and the associator. -/
def unitIso (A : C) : A ≅ (A ⊗ L) ⊗ h.inv :=
  (ρ_ A).symm ≪≫ whiskerLeftIso A h.isoLeft.symm ≪≫ (α_ A L h.inv).symm

/-- The forward map of `unitIso A` is `(ρ_ A).inv ≫ A ◁ h.isoLeft.inv ≫ (α_ A L h.inv).inv`. -/
theorem unitIso_hom (A : C) :
    (h.unitIso A).hom = (ρ_ A).inv ≫ A ◁ h.isoLeft.inv ≫ (α_ A L h.inv).inv :=
  rfl

/-- `unitIso` is natural: it is the unit of the pair of tensoring functors. -/
theorem unitIso_naturality {A B : C} (f : A ⟶ B) :
    f ≫ (h.unitIso B).hom = (h.unitIso A).hom ≫ (f ▷ L) ▷ h.inv := by
  simp only [unitIso_hom, Category.assoc]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left]

/-- **The pentagon-and-naturality identity behind tensor compatibility.** The unit isomorphism
at `W ⊗ A`, followed by the associator, is the unit isomorphism at `A` whiskered by `W`. -/
theorem unitIso_whiskerLeft (W A : C) :
    (h.unitIso (W ⊗ A)).hom ≫ (α_ W A L).hom ▷ h.inv
      = W ◁ (h.unitIso A).hom ≫ (α_ W (A ⊗ L) h.inv).inv := by
  simp only [unitIso_hom, whiskerLeft_comp, Category.assoc]
  rw [show (ρ_ (W ⊗ A)).inv = W ◁ (ρ_ A).inv ≫ (α_ W A (𝟙_ C)).inv from by monoidal,
    Category.assoc, ← associator_inv_naturality_right_assoc,
    show (α_ W A (L ⊗ h.inv)).inv ≫ (α_ (W ⊗ A) L h.inv).inv ≫ (α_ W A L).hom ▷ h.inv
      = W ◁ (α_ A L h.inv).inv ≫ (α_ W (A ⊗ L) h.inv).inv from by monoidal]

/-- The hom-set bijection `Mor(A ⊗ L, B) ≃ Mor(A, B ⊗ L')` of a two-sided inverse: compose the
unit isomorphism with the image under the fully faithful functor `- ⊗ L'`. -/
def homEquiv (A B : C) : (A ⊗ L ⟶ B) ≃ (A ⟶ B ⊗ h.inv) :=
  (h.fullyFaithfulTensorRightInv.homEquiv (X := A ⊗ L) (Y := B)).trans
    (Iso.homCongr (h.unitIso A).symm (Iso.refl (B ⊗ h.inv)))

/-- The bijection `homEquiv` sends `f : A ⊗ L ⟶ B` to `(unitIso A).hom ≫ f ▷ L'`. -/
theorem homEquiv_apply (A B : C) (f : A ⊗ L ⟶ B) :
    h.homEquiv A B f = (h.unitIso A).hom ≫ f ▷ h.inv := by
  simp [homEquiv, fullyFaithfulTensorRightInv, Functor.FullyFaithful.homEquiv,
    Iso.homCongr]

/-- **The adjunction `- ⊗ L ⊣ - ⊗ L'` of a two-sided inverse**, with the hom-set bijection
`homEquiv` on the nose. Its naturality in the source variable is the naturality of `unitIso`, and
in the target variable is the functoriality of `- ▷ L'`. -/
def tensorRightAdjunction : tensorRight L ⊣ tensorRight h.inv :=
  Adjunction.mkOfHomEquiv
    { homEquiv := h.homEquiv
      homEquiv_naturality_left_symm := fun {A' A B} f g => by
        rw [Equiv.symm_apply_eq, h.homEquiv_apply]
        change _ = (h.unitIso A').hom ≫ (f ▷ L ≫ (h.homEquiv A B).symm g) ▷ h.inv
        rw [comp_whiskerRight, ← Category.assoc, ← h.unitIso_naturality, Category.assoc,
          ← h.homEquiv_apply, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun {A B B'} f g => by
        simp only [h.homEquiv_apply]
        change _ = ((h.unitIso A).hom ≫ f ▷ h.inv) ≫ g ▷ h.inv
        rw [comp_whiskerRight, Category.assoc] }

/-- The hom-set bijection of `tensorRightAdjunction` is `homEquiv`. -/
theorem tensorRightAdjunction_homEquiv (A B : C) :
    (h.tensorRightAdjunction).homEquiv A B = h.homEquiv A B := by
  rw [tensorRightAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- **The adjunction of a two-sided inverse is compatible with the tensor structure**, in the
sense of Stacks 0FFR: tensoring on the left by an object commutes with the hom-set bijection.
This is `unitIso_whiskerLeft` together with the naturality of the associator. -/
theorem isTensorCompatible : (h.tensorRightAdjunction).IsTensorCompatible := by
  intro W Z Z' f
  rw [h.tensorRightAdjunction_homEquiv, h.tensorRightAdjunction_homEquiv, h.homEquiv_apply,
    h.homEquiv_apply, comp_whiskerRight, ← Category.assoc, h.unitIso_whiskerLeft,
    whiskerLeft_comp]
  simp only [Category.assoc]
  rw [associator_inv_naturality_middle]

/-- **An invertible object is a left dual of its inverse.** For a two-sided tensor inverse `L'`
of `L` in a monoidal category, `L` and `L'` form an exact pairing: `L'` is a left dual of `L` in
the sense of Categories, Definition 0FFP, with coevaluation `𝟙_ C ⟶ L ⊗ L'` and evaluation
`L' ⊗ L ⟶ 𝟙_ C`.

This is the converse half of Stacks 0FFR applied to the adjunction `- ⊗ L ⊣ - ⊗ L'`. -/
@[instance_reducible]
def exactPairing : ExactPairing L h.inv :=
  h.isTensorCompatible.exactPairing

/-- **The coevaluation of the pairing is the given isomorphism `𝟙_ C ≅ L ⊗ L'`.** This pins the
pairing down on the coevaluation side: it is not an unconstrained morphism of its type, but the
inverse of the isomorphism the `HasInverse` datum carries. The evaluation is *not* `h.isoRight`;
see the module docstring. -/
theorem coevaluation_exactPairing :
    letI := h.exactPairing
    (η_ L h.inv : 𝟙_ C ⟶ L ⊗ h.inv) = h.isoLeft.inv := by
  let := h.exactPairing
  change h.tensorRightAdjunction.tensorCoevaluation = _
  rw [Adjunction.tensorCoevaluation_def, h.tensorRightAdjunction_homEquiv, h.homEquiv_apply,
    unitIso_hom, Category.assoc, Category.assoc,
    show (α_ (𝟙_ C) L h.inv).inv ≫ (λ_ L).hom ▷ h.inv = (λ_ (L ⊗ h.inv)).hom from by monoidal,
    leftUnitor_naturality, unitors_equal, Iso.inv_hom_id_assoc]

end HasInverse

/-- **An invertible object of a monoidal category has a left dual.** This is the step of the
proof of Stacks 0FPG which turns clause (1), the invertibility of `M`, into the hypothesis of
Stacks 0FPD, that `M` admits a left dual. -/
theorem IsInvertible.exists_exactPairing {L : C} (h : IsInvertible L) :
    ∃ N : C, Nonempty (ExactPairing L N) :=
  h.elim fun h => ⟨h.inv, ⟨h.exactPairing⟩⟩


/-! ### Non-vacuity of the hypothesis

`HasInverse` and `IsInvertible` are the hypotheses of the two results above, so their content
depends on those data having inhabitants. The unit object supplies one over every monoidal
category, assuming nothing.
-/

/-- **The unit object is invertible**, its own two-sided tensor inverse by the left unitor. -/
def hasInverseUnit : HasInverse (𝟙_ C) where
  inv := 𝟙_ C
  isoLeft := λ_ (𝟙_ C)
  isoRight := λ_ (𝟙_ C)

/-- The unit object of a monoidal category is invertible. -/
theorem isInvertible_unit : IsInvertible (𝟙_ C) := ⟨hasInverseUnit⟩

/-- The exact pairing of the unit object with itself produced by `HasInverse.exactPairing`: an
inhabitant of its conclusion over every monoidal category. -/
@[instance_reducible]
def exactPairingUnitOfHasInverse : ExactPairing (𝟙_ C) (hasInverseUnit (C := C)).inv :=
  (hasInverseUnit (C := C)).exactPairing

end CategoryTheory.MonoidalCategory

end


