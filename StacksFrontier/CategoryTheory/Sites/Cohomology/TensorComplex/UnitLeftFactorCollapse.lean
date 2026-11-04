module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.LocalSections
public import StacksFrontier.Algebra.Homology.KoszulSymmetric
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorUnitors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences

/-!
# The total tensor complex with the structure sheaf as its *left* factor

Let `(C, O)` be a ringed site and let `B` be a cochain complex of `O`-modules. This file records
that the collapse

`Tot(O[0] ⊗_O B) ≅ B`

of the total tensor complex against the structure sheaf placed in degree zero, **with the
structure sheaf as the left tensor factor**, is already available: it is the left unitor `λ_ B`
of the monoidal structure of Tag 0FNG on cochain complexes, read at the spelling
`Stacks.SheafOfModules.Tensor.tensorComplex` that the currying isomorphism of Tag 0A90 is
stated for. Both identifications needed to see that are `rfl`, and they are recorded below.

## Why this file exists

Three places in the derived-internal-Hom cluster record this collapse as **absent**, and that is
wrong. The implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation` say "the chain-level
left unit collapse `Tot(O_X[0] ⊗_{O_X} B) ≅ B` does not exist", listing only the right-factor
collapses `Stacks.SheafOfModules.tensorComplexUnitIso`,
`AlgebraicGeometry.RingedSite.tensorTotalUnitIso` and
`AlgebraicGeometry.RingedSite.diagonalTensorUnit`, and offering for the left factor only the
*degreewise* statement `AlgebraicGeometry.RingedSite.tensorTotalUnitFactorIso` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorUnitFactor`, whose module
notes call the chain-level form deliberately omitted on account of a Koszul sign. The sign
observation is about the construction in *that* file — there the collapse is assembled out of
`isIso_ιTotal_of_unitFactor` and `sheafTensorUnitIsoLeft`, and the surviving term of the total
differential is then the signed one — and it is correct about that construction. It does not
apply to the monoidal left unitor, which exists for every `ComplexShape` with `TensorSigns`:
Mathlib's `HomologicalComplex.Monoidal.leftUnitor` is built from
`CategoryTheory.GradedObject.Monoidal.leftUnitor` and its differential square
`HomologicalComplex.Monoidal.leftUnitor'_inv_comm` disposes of the sign with
`ComplexShape.ε_zero`, the trivialised factor sitting in degree `0`.

That unitor is moreover the one the surrounding files already consume:
`CochainComplex.KFlatMonoidal.leftUnitor_derivedTensorIso` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure` identifies the
left unitor of `D(O)` with exactly this `λ_` through the K-flat comparison. So the chain level
and the derived level already speak of the same left unitor, and what is needed is only the
identification of its *source* with `Tot(O[0] ⊗_O B)` — which is `rfl`.

## Main definitions

* `AlgebraicGeometry.RingedSite.structureSheafComplexTensorLeftIso`: the collapse
  `Tot(O[0] ⊗_O B) ≅ B`, at the `tensorComplex` spelling.

## Main results

* `AlgebraicGeometry.RingedSite.tensorUnit_eq_structureSheafComplex`: the monoidal unit of
  cochain complexes of `O`-modules *is* the structure sheaf complex.
* `AlgebraicGeometry.RingedSite.tensorComplex_obj_obj_eq_tensorObj`: the total tensor complex
  bifunctor *is* the monoidal product.
* `AlgebraicGeometry.RingedSite.leftUnitor_inv_f_val_app`: the inverse collapse sends a local
  section `b` of `B^r` to the local pure tensor `1 ⊗ b`.
* `AlgebraicGeometry.RingedSite.leftUnitor_hom_f_val_app`: the collapse sends the local pure
  tensor `r ⊗ b` to `r • b`, and
  `AlgebraicGeometry.RingedSite.leftUnitor_hom_f_val_app_one` is that at `r = 1`. These are what
  a consumer needs, local pure tensors determining a morphism out of the total tensor complex
  (`AlgebraicGeometry.RingedSite.homSection_tensor_ext`).
* `AlgebraicGeometry.RingedSite.leftUnitor_inv_f`: the degreewise shape of the inverse collapse,
  the left unitor of the degree-`r` term followed by the summand inclusion.
* `AlgebraicGeometry.RingedSite.sheafLeftUnitor_inv_val_app`: the inverse left unitor of
  `Mod(O)` on local sections, which is where `SheafOfModules.leftUnitor_sheafTensor_eq_iso` is
  consumed.
* `AlgebraicGeometry.RingedSite.leftUnitor_inv_f_val_app`: the inverse collapse sends a local
  section `b` of `B^r` to the local pure tensor `1 ⊗ b`.
* `AlgebraicGeometry.RingedSite.leftUnitor_hom_f_val_app`: the collapse sends the local pure
  tensor `r ⊗ b` to `r • b`, and
  `AlgebraicGeometry.RingedSite.leftUnitor_hom_f_val_app_one` is that at `r = 1`. These are what
  a consumer needs, local pure tensors determining a morphism out of the total tensor complex.
* `AlgebraicGeometry.RingedSite.leftUnitor_inv_f`: the degreewise shape of the inverse collapse,
  the left unitor of the degree-`r` term followed by the summand inclusion.
* `AlgebraicGeometry.RingedSite.sheafLeftUnitor_inv_val_app`: the inverse left unitor of
  `Mod(O)` on local sections, which is where
  `SheafOfModules.leftUnitor_sheafTensor_eq_iso` is consumed.

## Implementation notes

The monoidal structure on `Mod(O)` in force is `SheafOfModules.monoidalCategorySheafTensor`,
whose curried tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor` and whose unit is
`SheafOfModules.unit`, both by equality rather than by isomorphism
(`SheafOfModules.curriedTensor_sheafTensor`, `SheafOfModules.tensorUnit_sheafTensor`); the
monoidal structure on complexes is `CochainComplex.symmetricCategory` over it, whose tensor
product is `HomologicalComplex.Monoidal.tensorObj`, i.e. `HomologicalComplex.mapBifunctor`
against the curried tensor product, and whose unit is `HomologicalComplex.single` at `0` of the
unit. Both equalities below are therefore `rfl`, and nothing is transported.

No `@[stacks]` attribute: Tag 0FNG asserts the monoidal structure on complexes, which is
`CochainComplex.symmetricCategory` and already carries it, and Tag 0A90 asserts the currying
isomorphism; neither asserts this identification of spellings, which is bookkeeping.

The universes are the diagonal `RingedSite.{u, u, u}` of the derived-internal-Hom cluster. The
sections universe of `SheafOfModules.monoidalCategorySheafTensor` is pinned as `max u v` of the
site universes, and on the diagonal that is `u` on the nose, so no universe obligation arises
here — unlike at a general `RingedSite.{u, v, w}`, where the instance would have to be pinned
by hand.

## References

* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The monoidal unit of cochain complexes of `O`-modules is the structure sheaf complex.**
The unit of `CochainComplex.symmetricCategory` is `HomologicalComplex.single` at degree zero of
the unit of `Mod(O)`, and the unit of `SheafOfModules.monoidalCategorySheafTensor` is
`SheafOfModules.unit`; so the unit complex is `structureSheafComplex` on the nose. -/
theorem tensorUnit_eq_structureSheafComplex :
    (𝟙_ (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)) =
      structureSheafComplex X :=
  rfl

/-- **The total tensor complex bifunctor is the monoidal product of cochain complexes.** The
tensor product of `CochainComplex.symmetricCategory` is `HomologicalComplex.mapBifunctor`
against the curried tensor product of `Mod(O)`, which is
`Stacks.SheafOfModules.Tensor.sheafTensor`; so it is
`Stacks.SheafOfModules.Tensor.tensorComplex` on the nose. -/
theorem tensorComplex_obj_obj_eq_tensorObj
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B = A ⊗ B :=
  rfl

/-- **The total tensor complex collapses against the structure sheaf in its LEFT factor:**
`Tot(O[0] ⊗_O B) ≅ B`.

This is the left unitor of the monoidal structure of Tag 0FNG on cochain complexes, read at the
`Stacks.SheafOfModules.Tensor.tensorComplex` spelling of the total tensor complex — the spelling
the currying isomorphism `AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso` of Tag 0A90 is
stated for, and the one `Stacks.SheafOfModules.Tensor.tensorComplexSection` describes on local
pure tensors. It is the left-hand companion of
`Stacks.SheafOfModules.tensorComplexUnitIso`, and unlike that one it is not constructed here:
the two identifications `tensorUnit_eq_structureSheafComplex` and
`tensorComplex_obj_obj_eq_tensorObj` make `λ_ B` have this type already. -/
def structureSheafComplexTensorLeftIso
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj (structureSheafComplex X)).obj B ≅ B :=
  λ_ B

/-- The collapse is the left unitor, by definition. -/
theorem structureSheafComplexTensorLeftIso_eq
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    structureSheafComplexTensorLeftIso X B = λ_ B :=
  rfl

/-! ### The collapse on local sections

What a consumer of the collapse needs is its effect on the local pure tensors
`Stacks.SheafOfModules.Tensor.tensorComplexSection` of the total tensor complex, since those
determine a morphism out of it (`AlgebraicGeometry.RingedSite.homSection_tensor_ext`). The
description is the expected one, `r ⊗ b ↦ r • b`, and it is what the currying isomorphism of
Tag 0A90 at a structure-sheaf source has to be compared against.

The chain goes through the degreewise formula `HomologicalComplex.leftUnitor'_inv` for Mathlib's
left unitor and the section formula
`Stacks.SheafOfModules.tensorSheafUnitLeftIso_inv_app` for the left unitor of `Mod(O)`, the two
being joined by `SheafOfModules.leftUnitor_sheafTensor_eq_iso`.

Every step below past the first is in term mode, and deliberately: the summand inclusion of the
monoidal product is spelled `HomologicalComplex.ιTensorObj` with the unit complex written
`HomologicalComplex.tensorUnit`, while `tensorComplexSection` is spelled with
`HomologicalComplex.ιMapBifunctor` and `structureSheafComplex`. The two are equal by `rfl`, but
the goals that mention both are not type-correct at `implicit` transparency, so no rewriting
tactic can act on them; `exact`-level defeq pays the crossing once per declaration instead. -/

/-- step 1: the component of the inverse left unitor is the presheaf-level left unitor of the
degree-`r` term followed by the summand inclusion. -/
theorem leftUnitor_inv_f (r : ℤ) :
    (λ_ B).inv.f r =
      (λ_ (B.X r)).inv ≫
        HomologicalComplex.ιMapBifunctor (structureSheafComplex X) B
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) 0 r r (by simp) := by
  have h1 : (λ_ B).inv.f r =
      (λ_ (B.X r)).inv ≫
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv ▷ B.X r) ≫
          HomologicalComplex.ιTensorObj
            (HomologicalComplex.tensorUnit
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
            B 0 r r (zero_add r) :=
    HomologicalComplex.leftUnitor'_inv B r
  have hw : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv ▷ B.X r = 𝟙 _ :=
    id_whiskerRight _ _
  have h2 : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv ▷ B.X r) ≫
          HomologicalComplex.ιTensorObj
            (HomologicalComplex.tensorUnit
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
            B 0 r r (zero_add r) =
      HomologicalComplex.ιMapBifunctor (structureSheafComplex X) B
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) 0 r r (by simp) :=
    (congrArg (fun w => w ≫ HomologicalComplex.ιTensorObj
        (HomologicalComplex.tensorUnit
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
        B 0 r r (zero_add r)) hw).trans (Category.id_comp _)
  exact h1.trans (congrArg (fun z => (λ_ (B.X r)).inv ≫ z) h2)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- step 2: the inverse left unitor of `Mod(O)` on local sections. -/
theorem sheafLeftUnitor_inv_val_app
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (W : X.C)
    (b : A.val.obj (op W)) :
    (λ_ A).inv.val.app (op W) b =
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val ⊗ A.val)).app (op W)
          ((1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) ⊗ₜ[
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] b) := by
  rw [show (λ_ A).inv = (Stacks.SheafOfModules.tensorSheafUnitLeftIso X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property A).inv from
    congrArg Iso.inv (SheafOfModules.leftUnitor_sheafTensor_eq_iso X.O A)]
  exact Stacks.SheafOfModules.tensorSheafUnitLeftIso_inv_app X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property A (op W) b

/-- step 3: the inverse left unitor of complexes sends a local section `b` of `B^r` to the
local pure tensor of the unit section with `b`. -/
theorem leftUnitor_inv_f_val_app (r : ℤ) (W : X.C) (b : (B.X r).val.obj (op W)) :
    ((λ_ B).inv.f r).val.app (op W) b =
      tensorComplexSection X 0 r r (zero_add r) (structureSheafOne X W) b :=
  (congrArg (fun φ => φ.val.app (op W) b) (leftUnitor_inv_f X B r)).trans
    ((AlgebraicGeometry.RingedSite.val_app_comp_apply X (λ_ (B.X r)).inv
        (HomologicalComplex.ιMapBifunctor (structureSheafComplex X) B
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) 0 r r (by simp))
        (op W) b).trans
      (congrArg ((HomologicalComplex.ιMapBifunctor (structureSheafComplex X) B
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) 0 r r
            (by simp)).val.app (op W))
        (sheafLeftUnitor_inv_val_app X (B.X r) W b)))

/-- step 4: the left unitor of complexes sends the local pure tensor of the unit section with
`b` back to `b`. -/
theorem leftUnitor_hom_f_val_app_one (r : ℤ) (W : X.C) (b : (B.X r).val.obj (op W)) :
    ((λ_ B).hom.f r).val.app (op W)
        (tensorComplexSection X 0 r r (zero_add r) (structureSheafOne X W) b) = b :=
  (congrArg (((λ_ B).hom.f r).val.app (op W))
      (leftUnitor_inv_f_val_app X B r W b).symm).trans
    ((AlgebraicGeometry.RingedSite.val_app_comp_apply X ((λ_ B).inv.f r) ((λ_ B).hom.f r)
        (op W) b).symm.trans
      (congrArg (fun (φ : B ⟶ B) => (φ.f r).val.app (op W) b) (λ_ B).inv_hom_id))

/-- step 5: the left unitor of complexes on an arbitrary local pure tensor. -/
theorem leftUnitor_hom_f_val_app (r : ℤ) (W : X.C)
    (k : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W))
    (b : (B.X r).val.obj (op W)) :
    ((λ_ B).hom.f r).val.app (op W)
        (tensorComplexSection X 0 r r (zero_add r) k b) = k • b := by
  have hk : tensorComplexSection X (K := structureSheafComplex X) (L := B) 0 r r (zero_add r) k b =
      k • tensorComplexSection X (K := structureSheafComplex X) (L := B) 0 r r (zero_add r)
        (structureSheafOne X W) b :=
    (congrArg (fun z => tensorComplexSection X 0 r r (zero_add r) z b)
        (show k = k • structureSheafOne X W from (mul_one k).symm)).trans
      (tensorComplexSection_smul_left X 0 r r (zero_add r) k (structureSheafOne X W) b)
  refine (congrArg (((λ_ B).hom.f r).val.app (op W)) hk).trans ?_
  refine Eq.trans (map_smul _ k _) ?_
  exact congrArg (fun z => k • z) (leftUnitor_hom_f_val_app_one X B r W b)

end AlgebraicGeometry.RingedSite

end
