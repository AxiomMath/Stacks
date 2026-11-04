module

public import StacksFrontier.CategoryTheory.Monoidal.InternalEndMonoid
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomDual

/-!
# The external tensor product of endomorphisms of dualizable objects is invertible

Let `C` be a symmetric monoidal closed category and let `X` and `Y` be objects admitting duals.
Then the comparison morphism of monoid objects

`End X ⊗ End Y ⟶ End (X ⊗ Y)`

of `StacksFrontier.CategoryTheory.Monoidal.InternalEndMonoid` is an isomorphism, so `End X ⊗ End Y`
and `End (X ⊗ Y)` are isomorphic as monoid objects. For sheaves of `𝒪_S`-modules on a scheme this
is `End(E) ⊗ End(F) ≅ End(E ⊗ F)` for finite locally free `E` and `F`, which is what makes
Brauer equivalence transitive.

## The shape of the proof

Write `ξ` for the counit `(B ⊗ X') ⊗ X ⟶ B` of the adjunction attached to an exact pairing
`(X, X')` — `pairingCounit` below, which `CategoryTheory.tensorRightAdjunction_counit_app`
identifies with the counit. Under the identification
`CategoryTheory.ihomIsoTensorRight` of the internal hom out of `X` with tensoring by `X'`, the
comparison becomes a morphism between two tensor products of duals, and the content of the
theorem is one identity between composites of braidings, associators and the two evaluations.

That identity is proved by reducing the two evaluations to a *single* one at a time. The
decisive point is that the dual of `X ⊗ Y` is `Y' ⊗ X'`, in that order, so that
`pairingCounit_tensorPairing` — the splitting of `ξ` for the tensor pairing into the `X`-step
and the `Y`-step — involves **no braiding at all** and is pure coherence. What remains is a
one-evaluation statement, `pairingCounit_slide`: contracting `(X', X)` after moving `X` left
past a spectator `Z` is the same as contracting it after moving `X'` right past `Z`. That in
turn is `evaluation_slide`, which is naturality of the braiding against a morphism to the unit.

## Main definitions

* `CategoryTheory.pairingCounit`: the counit `(B ⊗ X') ⊗ X ⟶ B` of an exact pairing, written
  out.
* `CategoryTheory.tensorPairingShuffle`: the braiding isomorphism
  `(B₁ ⊗ X') ⊗ (B₂ ⊗ Y') ≅ (B₁ ⊗ B₂) ⊗ (Y' ⊗ X')` which the comparison becomes under the dual
  description of the internal hom.

## Main results

* `CategoryTheory.MonoidalClosed.isIso_tensorInternalEnd_of_exactPairing` and
  `CategoryTheory.MonoidalClosed.isIso_tensorInternalEnd`: **the comparison
  `End X ⊗ End Y ⟶ End (X ⊗ Y)` is an isomorphism when `X` and `Y` admit duals.** Combined with
  `CategoryTheory.MonoidalClosed.tensorInternalEndIso` this gives the isomorphism of monoid
  objects.

* `CategoryTheory.pairingCounit_tensorPairing`: the braiding-free splitting of the counit of a
  tensor pairing.
* `CategoryTheory.pairingCounit_slide`, `CategoryTheory.evaluation_slide` and
  `CategoryTheory.braiding_comp_whiskerLeft_toUnit`: the one-evaluation inputs.
* `CategoryTheory.tensorμ_comp_braiding_tensorHom`: `MonoidalCategory.tensorμ` commutes with the
  braiding, generalising `CategoryTheory.SymmetricCategory.tensorμ_braid_swap` from the
  diagonal case.

## Implementation notes

Every step which differs only by associators and unitors is closed by the `monoidal` tactic,
including steps in which braidings and evaluations occur, since `monoidal` normalises the
coherence stretches around opaque morphisms. Steps which move a braiding are the explicitly
named lemmas. This is the organisation of `MonoidalCategory.tensor_associativity`, and it is
what keeps any single block small: there is no braided or symmetric coherence tactic.

`pairingCounit_tensorRight` is used as a rewrite rule oriented towards smaller second arguments;
it terminates because the second argument of `pairingCounit` strictly decreases.

## References

* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J)
* [Stacks Project, Tag 0FFR](https://stacks.math.columbia.edu/tag/0FFR)
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonoidalClosed

noncomputable section

namespace CategoryTheory

variable {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C]

/-- The counit `(B ⊗ X') ⊗ X ⟶ B` of the adjunction attached to an exact pairing `(X, X')`,
written out; see `CategoryTheory.tensorRightAdjunction_counit_app`. -/
def pairingCounit (X X' B : C) [ExactPairing X X'] : (B ⊗ X') ⊗ X ⟶ B :=
  (α_ B X' X).hom ≫ B ◁ ε_ X X' ≫ (ρ_ B).hom

/-- A morphism to the unit absorbs the braiding: braiding past `Z` and then applying it is the
same as applying it and then discarding the unit. -/
lemma braiding_comp_whiskerLeft_toUnit {A Z : C} (h : A ⟶ 𝟙_ C) :
    (β_ A Z).hom ≫ Z ◁ h ≫ (ρ_ Z).hom = h ▷ Z ≫ (λ_ Z).hom := by
  rw [← BraidedCategory.braiding_naturality_left_assoc]
  simp

/-- **Contracting a pairing slides past a spectator.** Moving `X` left past `Z` and then
contracting it with `X'` agrees with moving `X'` right past `Z` and then contracting. -/
lemma evaluation_slide (X X' Z : C) [ExactPairing X X'] :
    (α_ X' Z X).inv ≫ (β_ X' Z).hom ▷ X ≫ (α_ Z X' X).hom ≫ Z ◁ ε_ X X' ≫ (ρ_ Z).hom
      = X' ◁ (β_ Z X).hom ≫ (α_ X' X Z).inv ≫ ε_ X X' ▷ Z ≫ (λ_ Z).hom := by
  have h := braiding_comp_whiskerLeft_toUnit (A := X' ⊗ X) (Z := Z) (ε_ X X')
  rw [BraidedCategory.braiding_tensor_left_hom] at h
  simp only [Category.assoc] at h
  rw [← h, Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    SymmetricCategory.symmetry]
  simp

omit [SymmetricCategory C] in
/-- The counit of an exact pairing is natural in the carried object. -/
lemma pairingCounit_naturality (X X' : C) [ExactPairing X X'] {B B' : C} (h : B ⟶ B') :
    (h ▷ X') ▷ X ≫ pairingCounit X X' B' = pairingCounit X X' B ≫ h := by
  rw [pairingCounit, pairingCounit, associator_naturality_left_assoc,
    ← whisker_exchange_assoc]
  simp

omit [SymmetricCategory C] in
/-- The counit of an exact pairing on a tensor product acts on the right factor. -/
lemma pairingCounit_tensorRight (X X' B₁ B₂ : C) [ExactPairing X X'] :
    pairingCounit X X' (B₁ ⊗ B₂)
      = ((α_ B₁ B₂ X').hom ▷ X) ≫ (α_ B₁ (B₂ ⊗ X') X).hom
        ≫ (B₁ ◁ pairingCounit X X' B₂) := by
  simp [pairingCounit]

omit [SymmetricCategory C] in
/-- **The counit of a tensor pairing splits, with no braiding.** Because the dual of `X ⊗ Y` is
`Y' ⊗ X'` in that order, contracting it is contracting `(X, X')` and then `(Y, Y')`, with only
associators in between. -/
lemma pairingCounit_tensorPairing (X X' Y Y' B : C) [ExactPairing X X'] [ExactPairing Y Y'] :
    pairingCounit (X ⊗ Y) (Y' ⊗ X') B
      = 𝟙 _ ⊗≫ ((pairingCounit X X' (B ⊗ Y')) ▷ Y) ⊗≫ pairingCounit Y Y' B := by
  simp only [pairingCounit, ExactPairing.tensor_evaluation, monoidalComp, Category.assoc,
    MonoidalCategory.whiskerLeft_comp, comp_whiskerRight]
  monoidal

/-- `pairingCounit` after interleaving with `MonoidalCategory.tensorμ` slides the spectator `Z`
across the contraction. -/
lemma pairingCounit_slide (X X' B Z Y : C) [ExactPairing X X'] :
    tensorμ (B ⊗ X') Z X Y ≫ (pairingCounit X X' B ▷ (Z ⊗ Y))
      = (((α_ B X' Z).hom ≫ B ◁ (β_ X' Z).hom ≫ (α_ B Z X').inv) ▷ (X ⊗ Y))
        ⊗≫ (pairingCounit X X' (B ⊗ Z) ▷ Y) ⊗≫ 𝟙 _ := by
  calc tensorμ (B ⊗ X') Z X Y ≫ (pairingCounit X X' B ▷ (Z ⊗ Y))
      = 𝟙 _ ⊗≫ (B ◁ ((X' ◁ (β_ Z X).hom ≫ (α_ X' X Z).inv ≫ ε_ X X' ▷ Z
          ≫ (λ_ Z).hom) ▷ Y)) ⊗≫ 𝟙 _ := by
        simp only [pairingCounit, tensorμ, monoidalComp, Category.assoc,
          MonoidalCategory.whiskerLeft_comp, comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ (B ◁ (((α_ X' Z X).inv ≫ (β_ X' Z).hom ▷ X ≫ (α_ Z X' X).hom
          ≫ Z ◁ ε_ X X' ≫ (ρ_ Z).hom) ▷ Y)) ⊗≫ 𝟙 _ := by rw [evaluation_slide]
    _ = _ := by
        simp only [pairingCounit, monoidalComp, Category.assoc,
          MonoidalCategory.whiskerLeft_comp, comp_whiskerRight]
        monoidal

/-- `MonoidalCategory.tensorμ` commutes with the braiding. This generalises
`CategoryTheory.SymmetricCategory.tensorμ_braid_swap`, which is the case `P = X`, `Q = Y`. -/
lemma tensorμ_comp_braiding_tensorHom (X Y P Q : C) :
    tensorμ X Y P Q ≫ ((β_ X P).hom ⊗ₘ (β_ Y Q).hom)
      = (β_ (X ⊗ Y) (P ⊗ Q)).hom ≫ tensorμ P Q X Y := by
  have key : P ◁ (α_ X Q Y).inv ≫ P ◁ ((β_ X Q).hom ▷ Y) ≫ P ◁ ((β_ Q X).hom ▷ Y)
      ≫ P ◁ (α_ X Q Y).hom = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight_assoc,
      SymmetricCategory.symmetry]
    simp
  simp [tensorμ, tensorHom_def, reassoc_of% key]

/-- The braiding isomorphism `(B₁ ⊗ X') ⊗ (B₂ ⊗ Y') ≅ (B₁ ⊗ B₂) ⊗ (Y' ⊗ X')`: it moves the dual
factor `X'` to the right past `B₂ ⊗ Y'`. -/
def tensorPairingShuffle (B₁ X' B₂ Y' : C) :
    (B₁ ⊗ X') ⊗ (B₂ ⊗ Y') ≅ (B₁ ⊗ B₂) ⊗ (Y' ⊗ X') :=
  α_ B₁ X' (B₂ ⊗ Y') ≪≫ whiskerLeftIso B₁ (β_ X' (B₂ ⊗ Y')) ≪≫
    whiskerLeftIso B₁ (α_ B₂ Y' X') ≪≫ (α_ B₁ B₂ (Y' ⊗ X')).symm

/-- **The two contractions agree.** Interleaving and contracting in each variable separately is
contracting the tensor pairing after the shuffle. -/
lemma pairingCounit_tensorμ (X X' Y Y' B₁ B₂ : C) [ExactPairing X X'] [ExactPairing Y Y'] :
    tensorμ (B₁ ⊗ X') (B₂ ⊗ Y') X Y
        ≫ (pairingCounit X X' B₁ ⊗ₘ pairingCounit Y Y' B₂)
      = ((tensorPairingShuffle B₁ X' B₂ Y').hom ▷ (X ⊗ Y))
        ≫ pairingCounit (X ⊗ Y) (Y' ⊗ X') (B₁ ⊗ B₂) := by
  rw [tensorHom_def, ← Category.assoc, pairingCounit_slide, pairingCounit_tensorPairing]
  simp only [pairingCounit_tensorRight, tensorPairingShuffle, monoidalComp, Category.assoc,
    Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, MonoidalCategory.whiskerLeft_comp,
    comp_whiskerRight]
  monoidal

namespace MonoidalClosed

variable [MonoidalClosed C]

/-- The component of `CategoryTheory.ihomIsoTensorRight` at `B`, with its domain spelled
`B ⊗ X'`: the isomorphism `B ⊗ X' ≅ (X ⟶[C] B)` for an exact pairing `(X, X')`. -/
def ihomDualHom (X X' B : C) [ExactPairing X X'] : B ⊗ X' ⟶ (ihom X).obj B :=
  (ihomIsoTensorRight X X').hom.app B

/-- The morphism `ihomDualHom X X' B : B ⊗ X' ⟶ (X ⟶[C] B)` is an isomorphism. -/
instance isIso_ihomDualHom (X X' B : C) [ExactPairing X X'] : IsIso (ihomDualHom X X' B) :=
  inferInstanceAs (IsIso ((ihomIsoTensorRight X X').hom.app B))

/-- `ihomDualHom`, uncurried, braids the argument into place and contracts the pairing. -/
lemma uncurry_ihomDualHom (X X' B : C) [ExactPairing X X'] :
    uncurry (ihomDualHom X X' B) = (β_ X (B ⊗ X')).hom ≫ pairingCounit X X' B := by
  rw [ihomDualHom, uncurry_ihomIsoTensorRight_hom_app, pairingCounit]

/-- **The comparison `End X ⊗ End Y ⟶ End (X ⊗ Y)`, read through the dual description of the
internal hom in each variable, is the shuffle isomorphism.** -/
lemma ihomDualHom_comp_tensorInternalEnd (X X' Y Y' : C)
    [ExactPairing X X'] [ExactPairing Y Y'] :
    (ihomDualHom X X' X ⊗ₘ ihomDualHom Y Y' Y) ≫ tensorInternalEnd X Y
      = (tensorPairingShuffle X X' Y Y').hom ≫ ihomDualHom (X ⊗ Y) (Y' ⊗ X') (X ⊗ Y) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_tensorInternalEnd, uncurry_natural_left,
    uncurry_ihomDualHom]
  simp only [tensorμ_natural_right_assoc, tensorHom_comp_tensorHom, ← uncurry_eq,
    uncurry_ihomDualHom]
  rw [← Category.assoc, ← tensorHom_comp_tensorHom, ← Category.assoc,
    tensorμ_comp_braiding_tensorHom, Category.assoc, pairingCounit_tensorμ,
    ← Category.assoc, ← BraidedCategory.braiding_naturality_right]

/-- **The external tensor product of endomorphisms of dualizable objects is invertible.** -/
theorem isIso_tensorInternalEnd_of_exactPairing (X X' Y Y' : C)
    [ExactPairing X X'] [ExactPairing Y Y'] : IsIso (tensorInternalEnd X Y) := by
  have e : tensorInternalEnd X Y
      = inv (ihomDualHom X X' X ⊗ₘ ihomDualHom Y Y' Y)
        ≫ (tensorPairingShuffle X X' Y Y').hom
        ≫ ihomDualHom (X ⊗ Y) (Y' ⊗ X') (X ⊗ Y) := by
    rw [← ihomDualHom_comp_tensorInternalEnd X X' Y Y', IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- The comparison `End X ⊗ End Y ⟶ End (X ⊗ Y)` is an isomorphism when `X` and `Y` have right
duals. -/
instance isIso_tensorInternalEnd (X Y : C) [HasRightDual X] [HasRightDual Y] :
    IsIso (tensorInternalEnd X Y) :=
  isIso_tensorInternalEnd_of_exactPairing X Xᘁ Y Yᘁ

/-- The comparison `End X ⊗ End Y ⟶ End (X ⊗ Y)` is an isomorphism as soon as right duals of `X`
and `Y` merely exist. -/
theorem isIso_tensorInternalEnd_of_nonempty_hasRightDual (X Y : C)
    (hX : Nonempty (HasRightDual X)) (hY : Nonempty (HasRightDual Y)) :
    IsIso (tensorInternalEnd X Y) := by
  obtain ⟨hX⟩ := hX
  obtain ⟨hY⟩ := hY
  exact isIso_tensorInternalEnd X Y

end MonoidalClosed

end CategoryTheory
