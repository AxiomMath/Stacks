module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Two adjunctions indexed by equal parameters

Let `L t ⊣ R t` be a family of adjunctions between two fixed categories, indexed by a type `T`,
and let `h : t = t'` in `T`. The two adjunctions `L t ⊣ R t` and `L t' ⊣ R t'` are then
transports of one another, but the transport is *dependent*: both adjoints move, so the morphism
a transposition is applied to and the morphism it produces both change type. This file records
that transposition commutes with the transport, in both directions.

What makes these cheap is that they are stated over the family: with `t` and `t'` variables the
equality can be eliminated by `subst`, after which every transport is the identity. At a use
site no rewrite fires, because the two hom-set bijections and the morphisms they are applied to
all have types mentioning the index being rewritten.

`CategoryTheory.Adjunction.homEquiv_eq_rec` of
`StacksFrontier/CategoryTheory/Adjunction/Mates.lean` is the non-dependent half of this: there the
left adjoint is fixed and only the right adjoint is transported, so only the *value* of the
transposition changes type and no family is needed.

## Main results

* `CategoryTheory.Adjunction.homEquiv_eqToIso_hom_app_comp_of_eq`: transposing along the
  adjunction at `t`, after precomposing with the identification of the two left adjoints, is
  transposing along the adjunction at `t'` followed by the identification of the two right
  adjoints.
* `CategoryTheory.Adjunction.homEquiv_symm_eqToIso_inv_app_comp_of_eq`: the same for the inverse
  transposition.
* `CategoryTheory.Adjunction.homEquiv_eqToIso_inv_app_comp_of_eq`: the first statement for a
  morphism out of the left adjoint at `t` rather than at `t'`, so that the transport appears
  read backwards on the source.

## Implementation notes

These are general statements about a family of adjunctions, and instantiating them *directly* at
a family of large categories can be unaffordable: the unifier is then asked to see through the
definitional unfoldings of the two adjoints at a concrete index while the categories and their
instances are still metavariables. The remedy is to interpose a statement of the same shape for
the particular family, with the two categories fixed and the index still a variable, and to
instantiate that;
`Stacks.Sheaves.RingedToposModules.homEquiv_pullbackAdjPushforwardModules_of_eq` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposModulesHomEq.lean` is such a statement.
-/

@[expose] public section

open CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {T : Type w}
  {L : T → C ⥤ D} {R : T → D ⥤ C}

/-- **Two adjunctions indexed by equal parameters.** Transposing along the adjunction at `t`,
after precomposing with the identification of the two left adjoints, is transposing along the
adjunction at `t'` followed by the identification of the two right adjoints. This is how a
transposition crosses an equality of the data the adjunction is built from, without the unifier
being asked to see through that equality. -/
theorem homEquiv_eqToIso_hom_app_comp_of_eq (A : (t : T) → L t ⊣ R t) {t t' : T} (h : t = t')
    (X : C) (Y : D) (k : (L t').obj X ⟶ Y) :
    (A t).homEquiv X Y ((eqToIso (congrArg L h)).hom.app X ≫ k) =
      (A t').homEquiv X Y k ≫ (eqToIso (congrArg R h)).inv.app Y := by
  subst h
  simp

/-- **Two adjunctions indexed by equal parameters, for the inverse transposition.** -/
theorem homEquiv_symm_eqToIso_inv_app_comp_of_eq (A : (t : T) → L t ⊣ R t) {t t' : T}
    (h : t = t') (X : C) (Y : D) (k : X ⟶ (R t').obj Y) :
    ((A t).homEquiv X Y).symm (k ≫ (eqToIso (congrArg R h)).inv.app Y) =
      (eqToIso (congrArg L h)).hom.app X ≫ ((A t').homEquiv X Y).symm k := by
  subst h
  simp

/-- **Two adjunctions indexed by equal parameters, with the transport applied on the source of
the morphism being transposed.** Transposing along the adjunction at `t'`, after precomposing
with the identification of the two left adjoints read backwards, is transposing along the
adjunction at `t` followed by the identification of the two right adjoints.

This is `CategoryTheory.Adjunction.homEquiv_eqToIso_hom_app_comp_of_eq` with the morphism given
out of the left adjoint at `t` rather than at `t'`. It is a separate statement rather than that
one followed by a cancellation of the two transports, because the cancellation has to be
performed at the index where the adjunction is used, and there it is a dependent rewrite whose
term the kernel does not finish checking. -/
theorem homEquiv_eqToIso_inv_app_comp_of_eq (A : (t : T) → L t ⊣ R t) {t t' : T} (h : t = t')
    (X : C) (Y : D) (k : (L t).obj X ⟶ Y) :
    (A t').homEquiv X Y ((eqToIso (congrArg L h)).inv.app X ≫ k) =
      (A t).homEquiv X Y k ≫ (eqToIso (congrArg R h)).hom.app Y := by
  subst h
  simp

end CategoryTheory.Adjunction

end
