module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorByBaseModule

/-!
# The base-change unitor on the unit section

Let `α : R ⟶ R'` be a morphism of presheaves of rings and `L` a left adjoint of restriction of
scalars along `α` — informally `L` is `R' ⊗_R -`.  The *base-change unitor* `L(R) ≅ R'` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/BaseChangeUnitor.lean` is
`Stacks.PresheafOfModules.ChangeOfRings.baseChangeUnitor`, the morphism underlying it being
`unitComparison α adj`.

This file computes that comparison **on the unit section**, in both directions.  The forward
direction is what the development lacked: `unitComparison` is defined as an adjoint transpose and
`Stacks.PresheafOfModules.ChangeOfRings.isIso_unitComparison` is proved through
`isIso_iff_coyoneda_map_bijective` — abstractly, via Yoneda — so the *inverse* is never
constructed and no description of it on sections can be expected.  Keeping the comparison forward
is therefore the only route to a section-level statement, and the two facts that make it work are
already present: `unitComparison` is the transpose of `unitToRestrictScalarsUnit α`, which carries
`1` to `1`.

## Main results

* `Stacks.PresheafOfModules.ChangeOfRings.unitComparison_app_unit_app_one`: **the comparison
  carries the unit section forward to the unit section.**  For any left adjoint of restriction of
  scalars, the composite of the adjunction unit with the comparison sends `1` to `1`.
* `Stacks.TensorByBaseModule.changeOfRingsUnitIso_hom_app_unit_app_one`: the same statement for
  the unitor `O(U) ⊗_R R ≅ O(U)` of `Stacks.TensorByBaseModule.changeOfRingsUnitIso`, which is the
  base-change unitor at the change-of-rings adjunction.
* `Stacks.TensorByBaseModule.changeOfRingsUnitIso_inv_app_one`: **the unitor's inverse on `1`.**
  It is the image of `1` under the adjunction unit — informally `1 ⊗ 1` — obtained from the
  forward statement and `Iso.hom_inv_id`, without any description of the inverse.

## Implementation notes

*Why the proofs are terms and not `rw` chains.*  `changeOfRingsUnitIso` is `baseChangeUnitor`
applied to `changeOfRingsAdjunction θ`, whose right adjoint is spelled
`Stacks.PresheafOfModules.ChangeOfRings.restrictScalars θ` where `baseChangeUnitor` asks for
`PresheafOfModules.restrictScalars (Functor.whiskerRight θ (forget₂ CommRingCat RingCat))`.  The
two agree definitionally but not syntactically, and `rw [changeOfRingsUnitIso,
baseChangeUnitor_hom]` fails with *"the target expression is not type-correct under the
`implicit` transparency level"*: the rewrite's motive does not typecheck at that transparency.  A
term-mode proof needs no motive, so each statement below is discharged by a single application
and the two spellings meet by defeq where they are allowed to;
`changeOfRingsUnitIso_hom_app_unit_app_one` then checks in 0.2 s.

**The general rule, worth stating plainly because this is the second instance of it met in one
day:** when a rewrite's motive would have to cross two spellings of one object, use term mode —
a term needs no motive.  `rw` must build a motive by abstracting the rewritten subterm out of the
goal, and that motive is elaborated at `implicit` transparency, where two definitionally equal
spellings of the same functor are not interchangeable; a term application is checked at default
transparency, where they are.  The failure is reported as the target not being type-correct, which
reads like a malformed goal and is not one.

*Why the unit section is written through the adjunction unit* rather than as `1 ⊗ₜ 1`.  The
sections of `𝟙_ (PMod O)` carry no `OfNat … 1` instance, so `1` does not elaborate there; and
writing the element as `1 ⊗ₜ[R] 1` forces a choice between the `Algebra R (O.val.obj X)` instance
of `Stacks.TensorByBaseModule.coefficientAlgebraOfHom` and the
`(θ.app X).hom.toAlgebra` of `changeOfRingsAdjunction_unit_app_apply`, which are the same instance
by different routes and do not unify during elaboration.  Stating the element as the image of `1`
under the adjunction unit avoids both, and
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction_unit_app_apply` is available to
rewrite it to `1 ⊗ₜ 1` at any consumer that has fixed its instance.

*What the first consumer needs.*  The step these were proved for is
step 1 of the reduction in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeCanonical.lean`: that the
presheaf-level `s ↦ s ⊗ m`, namely
`(tensorByBaseModulePresheafOfHomUnitIso R J O 𝓕 θ).inv ≫
(tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map (spanHom m)`, carries `s` to
`s ⊗ₜ (1 ⊗ₜ m)`.  Unfolding `tensorByBaseModulePresheafOfHomUnitIso`,
`tensorByBaseModulePresheafOfHom` and `constantModuleUnitIso` — *and nothing else*, so that
`changeOfRingsUnitIso` stays folded and `changeOfRingsUnitIso_inv_app_one` can fire — puts the
goal in exactly four factors applied to `s`:

```
(ρ_ (𝓕.val.obj X)).inv ≫
  𝓕.val.obj X ◁ (changeOfRingsUnitIso R J O θ).inv.app X ≫
  𝓕.val.obj X ◁ ((changeOfRings θ).map (isoMk (fun _ ↦ Iso.refl _) _).inv).app X ≫
  𝓕.val.obj X ◁ ((changeOfRings θ).map
    ((constantModulePresheaf R).map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m)))).app X
```

Two things about finishing it.  First, **`simp` does not move that goal at all**,
even given `ModuleCat.MonoidalCategory.rightUnitor_inv_apply`,
`ModuleCat.MonoidalCategory.whiskerLeft_apply`, `ModuleCat.hom_comp`, `LinearMap.comp_apply` and
the lemmas of this file: the composite is not split and no factor fires.  The reason is the module
system's exposure discipline — a build of such a goal reports *"the following definitions were not
unfolded because their definition is not exposed: `inv`"* — so the factors have to be taken apart
by explicit `rw`s or term steps, not by `simp`.  Second, the third and fourth factors need a
description of `changeOfRings θ` applied to a *morphism*, on sections.

**That description exists.**  It is
`Stacks.PresheafOfModules.ChangeOfRings.cofHom_app_tmul`
(`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/ChangeOfRingsAdjunction.lean:289`), which reads
`((cofHom θ φ).app X).hom (a ⊗ₜ x) = a ⊗ₜ (φ.app X).hom x`, and `changeOfRings θ` has `cofHom θ`
for its action on morphisms by definition (`changeOfRings`, ibid. :332), so the statement
`(((changeOfRings θ).map φ).app X).hom (a ⊗ₜ x) = a ⊗ₜ (φ.app X).hom x` is *that lemma applied
directly* — with no bridging step, no `rfl` in the proof and no `change`.  What the step needs
beyond it is only the assembly: the remaining two factors, the identity and `1 • m = m`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u u' v' w₂ u₂ v₂

namespace Stacks.PresheafOfModules.ChangeOfRings

open _root_.PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R')
  {L : _root_.PresheafOfModules.{u} R ⥤ _root_.PresheafOfModules.{u} R'}
  (adj : L ⊣ _root_.PresheafOfModules.restrictScalars.{u} α)

/-- **The base-change comparison carries the unit section forward to the unit section.**

`unitComparison α adj` is the adjoint transpose of
`Stacks.PresheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit α`, so composing the unit of
the adjunction with it *is* that morphism; and that morphism carries `1` to `1` by
`Stacks.PresheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_app_one`.

This is the forward description that makes section-level statements about the base-change unitor
possible.  Its inverse admits none: `isIso_unitComparison` is proved through
`isIso_iff_coyoneda_map_bijective`, so the inverse is never constructed. -/
theorem unitComparison_app_unit_app_one (X : Cᵒᵖ) :
    Hom.app (unitComparison α adj) X
        (Hom.app (adj.unit.app (unit R)) X (1 : R.obj X)) = (1 : R'.obj X) := by
  have h := homEquiv_unitComparison α adj
  rw [Adjunction.homEquiv_unit] at h
  have h2 := congrArg (fun φ => Hom.app φ X (1 : R.obj X)) h
  rw [unitToRestrictScalarsUnit_app_one] at h2
  exact h2

end Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.TensorByBaseModule

open _root_.PresheafOfModules
open Stacks.PresheafOfModules.ChangeOfRings

variable {C : Type u₂} [Category.{v₂} C] (R : Type w₂) [CommRing R]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  (O : Sheaf J CommRingCat.{w₂})
  (θ : constantRingPresheaf (C := C) R ⟶ O.val)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The unitor `O(U) ⊗_R R ≅ O(U)` carries the unit section forward to `1`.**  This is
`Stacks.PresheafOfModules.ChangeOfRings.unitComparison_app_unit_app_one` at the change-of-rings
adjunction, `Stacks.TensorByBaseModule.changeOfRingsUnitIso` being the base-change unitor there.

The proof is a bare application: see the implementation notes for why a `rw` with
`changeOfRingsUnitIso` and `baseChangeUnitor_hom` fails on its motive. -/
theorem changeOfRingsUnitIso_hom_app_unit_app_one (X : Cᵒᵖ) :
    Hom.app (changeOfRingsUnitIso R J O θ).hom X
        (Hom.app ((changeOfRingsAdjunction θ).unit.app
          (unit (ringPresheaf (constantRingPresheaf (C := C) R)))) X
            (1 : (ringPresheaf (constantRingPresheaf (C := C) R)).obj X)) =
      (1 : O.val.obj X) :=
  unitComparison_app_unit_app_one _ (changeOfRingsAdjunction θ) X

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The inverse of the unitor `O(U) ⊗_R R ≅ O(U)` on `1`**: it is the image of `1` under the
unit of the change-of-rings adjunction, which
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction_unit_app_apply` computes as
`1 ⊗ₜ 1`.

Nothing about the inverse is used: the statement follows from the forward description
`changeOfRingsUnitIso_hom_app_unit_app_one` and `CategoryTheory.Iso.hom_inv_id`, which is what
makes it available at all — the inverse is produced by `isIso_iff_coyoneda_map_bijective` and has
no formula. -/
theorem changeOfRingsUnitIso_inv_app_one (X : Cᵒᵖ) :
    Hom.app (changeOfRingsUnitIso R J O θ).inv X (1 : O.val.obj X) =
      Hom.app ((changeOfRingsAdjunction θ).unit.app
        (unit (ringPresheaf (constantRingPresheaf (C := C) R)))) X
          (1 : (ringPresheaf (constantRingPresheaf (C := C) R)).obj X) := by
  refine Eq.trans (congrArg (Hom.app (changeOfRingsUnitIso R J O θ).inv X)
    (changeOfRingsUnitIso_hom_app_unit_app_one R J O θ X)).symm ?_
  exact congrArg (fun φ => Hom.app φ X _) (changeOfRingsUnitIso R J O θ).hom_inv_id

end Stacks.TensorByBaseModule

end

end
