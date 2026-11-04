module

public import Mathlib.CategoryTheory.Shift.CommShiftTwo

/-!
# Postcomposing a bifunctor that commutes with the shifts

Let `G : C₁ ⥤ C₂ ⥤ D` be a bifunctor commuting with the shifts in both variables in the sense of
`CategoryTheory.Functor.CommShift₂`, and let `H : D ⥤ D'` commute with the shift.  This file
proves that the postcomposite `G ⋙ (whiskeringRight C₂ D D').obj H`, i.e.
`(X₁, X₂) ↦ H((G X₁) X₂)`, again commutes with the shifts in both variables.

## Main results

* `CategoryTheory.Functor.map_shiftComm_hom`: **an additive-monoid-indexed `CommShift` structure on
  `H : D ⥤ D'` is compatible with `CategoryTheory.shiftComm`**, the isomorphism exchanging two
  shifts.
* `CategoryTheory.Functor.CommShift₂.postcomp`: the conclusion, for an arbitrary pair of
  `CategoryTheory.CommShift₂Setup`s related by the compatibility `hε` of their sign elements.
* `CategoryTheory.Functor.CommShift₂.postcompInt`: the conclusion for the standard `ℤ` setups
  `CategoryTheory.CommShift₂Setup.int` on both sides, i.e. a
  `CategoryTheory.Functor.CommShift₂Int`, for an additive `H`.

## Implementation notes

The sign lives entirely in the `ε` field of the `CommShift₂Setup`s, and `postcomp` transports it
rather than choosing it: it relates the sign of the setup on `D` to the sign of the setup on `D'`
through `H`. At the standard `ℤ` setups `CategoryTheory.CommShift₂Setup.int` both are
`(-1) ^ (m * n)`, so `postcompInt` needs only that an additive functor preserves
`Int.negOnePow • 𝟙`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/


@[expose] public section

namespace CategoryTheory

open Category

variable {C₁ C₂ D D' : Type*} [Category* C₁] [Category* C₂] [Category* D] [Category* D']

namespace Functor

/-! ### A `CommShift` structure is compatible with `shiftComm` -/

section ShiftComm

variable {M : Type*} [AddCommMonoid M] [HasShift D M] [HasShift D' M]

/-- `CategoryTheory.shiftComm`, expanded as the two `shiftFunctorAdd'` isomorphisms at the two
orders of the sum.  This is `CategoryTheory.shiftFunctorComm_eq` evaluated at an object. -/
private theorem shiftComm_hom_eq {W : Type*} [Category W] [HasShift W M] (X : W) (m n : M) :
    (shiftComm X m n).hom =
      (shiftFunctorAdd' W m n (m + n) rfl).inv.app X ≫
        (shiftFunctorAdd' W n m (m + n) (add_comm n m)).hom.app X := by
  rw [show shiftComm X m n = (shiftFunctorComm W m n).app X from rfl,
    shiftFunctorComm_eq W m n (m + n) rfl]
  rfl

/-- **A functor commuting with the shift by a commutative monoid is compatible with the
isomorphism `CategoryTheory.shiftComm` exchanging two shifts.**

Both sides of the equation are maps `H.obj (Z⟦m⟧⟦n⟧) ⟶ (H.obj Z)⟦n⟧⟦m⟧`: on the left the
exchange happens in `D` and the commutation isomorphisms are then applied in the order `m`, `n`;
on the right they are applied in the order `n`, `m` and the exchange happens in `D'`. -/
theorem map_shiftComm_hom (H : D ⥤ D') [H.CommShift M] (Z : D) (m n : M) :
    H.map (shiftComm Z m n).hom ≫ (H.commShiftIso m).hom.app (Z⟦n⟧) ≫
          ((H.commShiftIso n).hom.app Z)⟦m⟧' =
      (H.commShiftIso n).hom.app (Z⟦m⟧) ≫ ((H.commShiftIso m).hom.app Z)⟦n⟧' ≫
        (shiftComm (H.obj Z) m n).hom := by
  have hu : ∀ (p q : M) (hpq : p + q = m + n),
      (H.commShiftIso (m + n)).hom.app Z =
        H.map ((shiftFunctorAdd' D p q (m + n) hpq).hom.app Z) ≫
          (H.commShiftIso q).hom.app (Z⟦p⟧) ≫
            ((H.commShiftIso p).hom.app Z)⟦q⟧' ≫
              (shiftFunctorAdd' D' p q (m + n) hpq).inv.app (H.obj Z) := by
    intro p q hpq
    rw [H.commShiftIso_add' hpq, CommShift.isoAdd'_hom_app]
  have e₁ := hu m n rfl
  have e₂ := hu n m (add_comm n m)
  have h₂ : H.map ((shiftFunctorAdd' D n m (m + n) (add_comm n m)).hom.app Z) ≫
        (H.commShiftIso m).hom.app (Z⟦n⟧) ≫ ((H.commShiftIso n).hom.app Z)⟦m⟧' =
      (H.commShiftIso (m + n)).hom.app Z ≫
        (shiftFunctorAdd' D' n m (m + n) (add_comm n m)).hom.app (H.obj Z) := by
    rw [e₂]
    simp
  rw [shiftComm_hom_eq, shiftComm_hom_eq, H.map_comp, assoc, h₂, e₁]
  simp only [← assoc, ← H.map_comp, Iso.inv_hom_id_app]
  simp

/-- The `CategoryTheory.Iso.inv` form of `map_shiftComm_hom`: a functor commuting with the shift by
a commutative monoid is compatible with the inverse of `CategoryTheory.shiftComm`. -/
@[reassoc]
theorem map_shiftComm_inv (H : D ⥤ D') [H.CommShift M] (Z : D) (m n : M) :
    H.map (shiftComm Z m n).inv ≫ (H.commShiftIso n).hom.app (Z⟦m⟧) ≫
          ((H.commShiftIso m).hom.app Z)⟦n⟧' =
      (H.commShiftIso m).hom.app (Z⟦n⟧) ≫ ((H.commShiftIso n).hom.app Z)⟦m⟧' ≫
        (shiftComm (H.obj Z) m n).inv := by
  rw [← Iso.symm_hom, ← Iso.symm_hom (shiftComm (H.obj Z) m n), shiftComm_symm, shiftComm_symm]
  exact H.map_shiftComm_hom Z n m

end ShiftComm

/-! ### Postcomposition of a bifunctor -/

section Postcomp

variable {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
  [HasShift D' M]

/-- `G.flip` evaluated at `X₂` and then `X₁` is `G` evaluated at `X₁` and then `X₂`. -/
private theorem flip_obj_obj_eq (G : C₁ ⥤ C₂ ⥤ D) (X₁ : C₁) (X₂ : C₂) :
    (G.flip.obj X₂).obj X₁ = (G.obj X₁).obj X₂ := rfl

/-- **A bifunctor commuting with the shifts in both variables, postcomposed with a functor
commuting with the shift, again commutes with the shifts in both variables**, provided the two
`CategoryTheory.CommShift₂Setup`s have signs matching under `H`.

This is the postcomposition counterpart of `CategoryTheory.Functor.CommShift₂.precomp₁` and
`precomp₂`. -/
@[instance_reducible]
def CommShift₂.postcomp (G : C₁ ⥤ C₂ ⥤ D) (H : D ⥤ D') [H.CommShift M]
    (h : CommShift₂Setup D M) (h' : CommShift₂Setup D' M) [G.CommShift₂ h]
    (hε : ∀ (m n : M) (Z : D),
      H.map ((h.ε m n).val.app Z) = (h'.ε m n).val.app (H.obj Z)) :
    (G ⋙ (whiskeringRight C₂ D D').obj H).CommShift₂ h' where
  commShiftObj X₁ := CommShift.comp (G.obj X₁) H
  commShift_map f := inferInstanceAs (NatTrans.CommShift (whiskerRight (G.map f) H) M)
  commShiftFlipObj X₂ := CommShift.comp (G.flip.obj X₂) H
  commShift_flip_map g :=
    inferInstanceAs (NatTrans.CommShift (whiskerRight (G.flip.map g) H) M)
  comm X₁ X₂ m n := by
    -- Spell the three functors as honest composites, so that
    -- `Functor.commShiftIso_comp_hom_app` applies.  The `CommShift` instances agree with the
    -- fields above on the nose.
    change ((G.obj (X₁⟦m⟧) ⋙ H).commShiftIso n).hom.app X₂ ≫
        (((G.flip.obj X₂ ⋙ H).commShiftIso m).hom.app X₁)⟦n⟧' =
      ((G.flip.obj (X₂⟦n⟧) ⋙ H).commShiftIso m).hom.app X₁ ≫
        (((G.obj X₁ ⋙ H).commShiftIso n).hom.app X₂)⟦m⟧' ≫
          (shiftComm (H.obj ((G.obj X₁).obj X₂)) m n).inv ≫
            (h'.ε m n).val.app ((H.obj ((G.obj X₁).obj X₂))⟦m⟧⟦n⟧)
    have hcen : ∀ {W W' : D'} (u : W ⟶ W'),
        (h'.ε m n).val.app W ≫ u = u ≫ (h'.ε m n).val.app W' :=
      fun u => ((h'.ε m n).val.naturality u).symm
    simp only [commShiftIso_comp_hom_app, map_comp, assoc]
    rw [← commShiftIso_hom_naturality_assoc, ← commShiftIso_hom_naturality_assoc,
      ← H.map_comp_assoc, G.commShift₂_comm h X₁ X₂ m n]
    simp only [map_comp, assoc, hε m n (((G.obj X₁).obj X₂)⟦m⟧⟦n⟧), hcen,
      flip_obj_obj_eq, comp_obj]
    rw [H.map_shiftComm_inv_assoc ((G.obj X₁).obj X₂) m n]

/-- **A bifunctor commuting with the shifts by `ℤ` in both variables, postcomposed with an
additive functor commuting with the shift, again commutes with the shifts by `ℤ` in both
variables.**  This is `CommShift₂.postcomp` at the standard setups
`CategoryTheory.CommShift₂Setup.int` on both sides. -/
noncomputable instance CommShift₂.postcompInt [Preadditive D] [Preadditive D']
    [HasShift C₁ ℤ] [HasShift C₂ ℤ]
    [HasShift D ℤ] [HasShift D' ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive]
    [∀ (n : ℤ), (shiftFunctor D' n).Additive] (G : C₁ ⥤ C₂ ⥤ D) (H : D ⥤ D') [H.CommShift ℤ]
    [H.Additive] [G.CommShift₂Int] :
    (G ⋙ (whiskeringRight C₂ D D').obj H).CommShift₂Int :=
  CommShift₂.postcomp G H CommShift₂Setup.int CommShift₂Setup.int fun m n Z => by
    simp only [CommShift₂Setup.int_ε, CatCenter.app_neg_one_zpow, Units.smul_def,
      H.map_zsmul, map_id]

end Postcomp

/-! ### The shape of [Stacks, Tag 079U]

The four bifunctors whose sign coherence Tag 079U needs are, abstractly: with `B` playing
`D(𝒪_Y)`, `E` playing `D(𝒪_X)`, `A` the K-flat models of `K(𝒪_Y)`, `T` and `S` the derived
tensor products on `B` and `E`, `P` the derived pullback `Lf^*` and `L` the K-flat localization
`kFlatQY`,

* `F₁' = T ⋙ (whiskeringRight B B E).obj P`, i.e. `(K, L) ↦ Lf^*(K ⊗^𝐋_{𝒪_Y} L)`;
* `F₂' = P ⋙ (S ⋙ (whiskeringLeft B E E).obj P)`, i.e. `(K, L) ↦ Lf^*K ⊗^𝐋_{𝒪_X} Lf^*L`;
* `F₁`, `F₂`, those two restricted to the models by `L` in both variables.

The `example`s below check that **all four follow by instance search alone** from `T.CommShift₂Int`
and `S.CommShift₂Int` (the sign coherence of the derived tensor product), `P.CommShift ℤ`,
`P.Additive` and `L.CommShift ℤ`. -/


section Tag079U

noncomputable section

variable {A B E : Type*} [Category A] [Category B] [Category E]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift E ℤ] [Preadditive B] [Preadditive E]
  [∀ n : ℤ, (shiftFunctor B n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
  (T : B ⥤ B ⥤ B) [T.CommShift₂Int] (S : E ⥤ E ⥤ E) [S.CommShift₂Int]
  (P : B ⥤ E) [P.CommShift ℤ] [P.Additive] (L : A ⥤ B) [L.CommShift ℤ]

example : (T ⋙ (whiskeringRight B B E).obj P).CommShift₂Int := by infer_instance

example : (P ⋙ (S ⋙ (whiskeringLeft B E E).obj P)).CommShift₂Int := by infer_instance

example : (L ⋙ ((T ⋙ (whiskeringRight B B E).obj P) ⋙
    (whiskeringLeft A B E).obj L)).CommShift₂Int := by infer_instance

example : (L ⋙ ((P ⋙ (S ⋙ (whiskeringLeft B E E).obj P)) ⋙
    (whiskeringLeft A B E).obj L)).CommShift₂Int := by infer_instance

end

end Tag079U

end Functor

end CategoryTheory
