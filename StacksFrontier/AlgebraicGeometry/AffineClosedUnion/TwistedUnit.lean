module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.TwistedSections
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism

/-!
# The twisted unit is the unit of `i^* ⊣ i_*`

`StacksDraft.AlgebraicGeometry.F3b.AffineClosedUnion.TwistedSections` builds, for a closed
immersion `i : Z ⟶ X` of schemes and a sheaf of `𝒪_X`-modules `L`, a canonical map

`Stacks.AffineClosedUnion.twistedUnit i L : L ⟶ i_*(i^*L)`

as the twist by `L` of the comparison `𝒪_X ⟶ i_*𝒪_Z`, conjugated by the left unit constraint of
the sheaf tensor product and by the projection formula at `i`.  It is the canonical map by
construction, but nothing there identifies it with
`(AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L`, and until that
identification is available a consumer cannot read its sections as restriction.  This file
proves it.

## The route

Transposing under `i^* ⊣ i_*` is what makes the computation finite.  Writing `η` for the unit of
that adjunction, `ε : i^*𝒪_X ⟶ 𝒪_Z` for Mathlib's `SheafOfModules.pullbackObjUnitToUnit`, `λ` for
the left unit constraint and `c` for the pullback tensor comparison of [Stacks, Tag 01CD]:

1. the comparison `𝒪_X ⟶ i_*𝒪_Z` is `η_{𝒪_X} ≫ i_*ε`
   (`Stacks.AffineProjectionFormula.unitToPushforwardStructure_eq`), because Mathlib defines `ε`
   as its adjoint transpose;
2. tensoring that factorisation with `L` and composing with the projection formula, naturality
   of the projection-formula map in its first argument
   (`Stacks.AffineProjectionFormula.projectionFormulaMap_natural`) moves `i_*ε` past it, and
   its compatibility with the tensorized unit
   (`Stacks.AffineProjectionFormula.projectionFormulaMap_natural_unit`) turns what is left into
   the adjoint transpose of `c`;
3. so the whole composite is the transpose of `c ≫ (ε ⊗ 𝟙) ≫ λ`, and the claim becomes the one
   piece of actual coherence: **the pullback tensor comparison is compatible with the left unit
   constraints and with `ε`.**  That is
   `Stacks.AffineProjectionFormula.comparisonTranspose_comp_structureUnitor`, and it is proved on
   sections: a morphism out of a sheaf tensor product is determined by its effect on the
   sheafification-unit images of pure tensors, and on `x ⊗ y` both sides are `i^♯x · η y`.

Step 3 is where the two inputs quoted in `TwistedSections` are used:
`Stacks.RingedSpace.comparisonTranspose_unit_tmul` for the left side and
`Stacks.RingedSpace.pullbackUnit_smul` for the right, with Mathlib's
`SheafOfModules.unitToPushforwardObjUnit_val_app_apply` identifying `ε` of a pulled-back section
with the image of the section under `i^♯`.

Steps 1-3 need no hypothesis on `i` at all and are stated here for an arbitrary morphism of
ringed spaces; only `Stacks.AffineClosedUnion.twistedUnit` itself, whose definition uses the
projection formula as an *isomorphism*, needs `i` to be a closed immersion.

## Implementation notes

**Instance search is not the obstacle here, and that is worth recording because it is where the
cost of the `TwistedSections` construction actually sat.**  There the right-adjointness of
`i_*` at the `AlgebraicGeometry.Scheme.Modules` spelling had to be supplied by hand; at the
`RingedSpaceModuleAdjunction.structureSheafHom` spelling it is found, through Mathlib's
`SheafOfModules.instIsRightAdjointPushforward`.  Concretely, with
`φ = AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom i`,
`SheafOfModules.pullbackObjUnitToUnit φ` dies with `synthInstanceFailed` on
`(SheafOfModules.pushforward φ).IsRightAdjoint`; with `φ = structureSheafHom f` for a morphism
of ringed spaces it elaborates with nothing supplied.  So everything below is stated for a
morphism of ringed spaces, and no local instance is declared.

What *is* an obstacle is elaboration across two spellings of the structure sheaf of rings; the
crossing is free for conversion and not for elaboration.  `Stacks.RingedSpace.structureRingSheaf`
is a
reducible abbreviation, so `(structureRingSheaf W).obj.obj U` carries the `CommRing` instance the
`TensorProduct` lemmas need; `structureSheafRing` — the spelling
`RingedSpaceModuleAdjunction.structureSheafHom`, hence Mathlib's
`SheafOfModules.unitToPushforwardObjUnit`, is typed at — is a semireducible definition and does
not.  The instance is found for the first and not for the second, and a `rw` by a
product-category identity whose two sides were elaborated at the two spellings fails with
*"the target expression is not type-correct under the `implicit` transparency level"*.  The cure
is the usual one, a declared return type:
`Stacks.AffineProjectionFormula.unitToPushforwardStructure` is Mathlib's morphism with its
codomain declared at the `structureRingSheaf` spelling, after which the rewrites below match at
that crossing.
Likewise `Stacks.AffineProjectionFormula.structureUnitor` declares the left unit constraint at
that spelling, and `Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor`, stated over
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`, is applied to it directly — no
  bridging declaration is written and
none is needed.

**A third spelling of the sheaf of rings arrives with the tensor bifunctor, and it decides how
the coherence below is proved.**  `Stacks.SheafOfModules.Tensor.sheafTensor` is a bifunctor over
`Stacks.SheafOfModules.Tensor.ringSheaf`, so the product-category argument of its uncurrying is
typed there and not at `structureRingSheaf`.  The two are definitionally equal, and
`Tensor.ringSheaf` is a semireducible definition, so any goal applying the uncurried bifunctor to
a pair built from `structureModule` — which is what the statement of
`tensorSheaf_map_unitToPushforwardStructure_comp_projection` already is — is type-correct at
`default` and not at the `implicit` transparency level that `rw` matches and checks motives at.
No reducibility attribute is declared for it: the proof is written forward instead, out of
`CategoryTheory.Category.assoc`, `CategoryTheory.Functor.map_comp` and `congrArg`, composed with
`Eq.trans`, all of which are checked at `default` transparency, so the transparency question
never arises.  The two steps that a rewrite would have performed inside the product category are
stated over `Tensor.ringSheaf` from the start, as the local `hsplit` and `hnatural`: each has the
uncurried bifunctor already applied, so its own elaboration fixes the seating, and it is proved
from `unitToPushforwardStructure_eq` and `projectionFormulaMap_natural` by `congrArg`.  This also
disposes of the `@[reassoc]` question: the reassociated variant of
`Stacks.AffineProjectionFormula.projectionFormulaMap_natural` is not used at all, the
unreassociated lemma being applied as a term and the composite associated by hand.

The scalar of the left unit constraint is handled by
`Stacks.AffineProjectionFormula.structureUnitor_tensorSheafUnit_tmul`, which generalises
`Stacks.SheafOfModules.Invertible.toSheafify_tensorProductLeftUnitor` from the unit
section to an arbitrary scalar; the scalar is carried across by
`Stacks.SheafOfModules.toUnit_smul` and `TensorProduct.smul_tmul`.  Its first tensor factor is
taken as a free variable together with an equation naming it, so that the lemma applies to the
two different closed terms the computation produces there without a rewrite having to find them.

## Main definitions

* `Stacks.AffineProjectionFormula.structureModule`: the structure sheaf as a sheaf of modules
  over itself, and `Stacks.AffineProjectionFormula.structureUnitor` the left unit constraint
  `𝒪_W ⊗ M ≅ M`, both at the `Stacks.RingedSpace.structureRingSheaf` spelling.
* `Stacks.AffineProjectionFormula.pullbackStructureComparison`: the canonical `f^*𝒪_X ⟶ 𝒪_Z`.
* `Stacks.AffineProjectionFormula.unitToPushforwardStructure`: the canonical `𝒪_X ⟶ f_*𝒪_Z`.

## Main results

* `Stacks.AffineProjectionFormula.comparisonTranspose_comp_structureUnitor`: **the coherence** of
  the pullback tensor comparison with the left unit constraints.
* `Stacks.AffineProjectionFormula.tensorSheaf_map_unitToPushforwardStructure_comp_projection`:
  the twisted comparison, for an arbitrary morphism of ringed spaces, equals the left unit
  constraint followed by the unit of `f^* ⊣ f_*`.
* `Stacks.AffineClosedUnion.twistedUnit_eq_unit`: **the obligation `TwistedSections` recorded.**
  `twistedUnit i L` is `(Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L`.
* `Stacks.AffineClosedUnion.twistedUnit_app_apply`: consequently its sections are the sections of
  the unit, i.e. `Stacks.RingedSpace.pullbackUnit`.
* `Stacks.AffineClosedUnion.existsUnique_unit_app_eq_zero_of_inf_eq_bot`: the vanishing form of
  the twisted square with the unit of the adjunction in place of `twistedUnit`, which is the form
  a consumer of [Stacks, Tag 09NX] can use.

No `@[stacks]` attribute is attached to anything here, for the reason `TwistedSections` gives: the
twisted square is the statement of no tag, and this is a coherence internal to its construction.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf PresheafOfModules.tensorObj
  Stacks.SheafOfModules.Tensor.ringSheaf

open CategoryTheory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace
open PresheafOfModules (Hom)
open scoped TensorProduct
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AffineProjectionFormula

/-- The structure sheaf of a ringed space as a sheaf of modules over itself. -/
abbrev structureModule (W : RingedSpace.{u, u}) : SheafOfModules.{u} (structureRingSheaf W) :=
  SheafOfModules.unit (structureRingSheaf W)

/-- The left unit constraint `𝒪_W ⊗_{𝒪_W} M ≅ M` of the sheaf tensor product, at the
`Stacks.RingedSpace.structureRingSheaf` spelling. -/
abbrev structureUnitor {W : RingedSpace.{u, u}} (M : SheafOfModules.{u} (structureRingSheaf W)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf))).obj (structureModule W, M) ≅ M :=
  Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor W.presheaf
    (structureSheafRing W).property M

section RingedSpace

variable {X Z : RingedSpace.{u, u}} (f : Z ⟶ X)

/-- The canonical map `f^*𝒪_X ⟶ 𝒪_Z` for a morphism of ringed spaces: Mathlib's
`SheafOfModules.pullbackObjUnitToUnit`, which is the adjoint transpose of `𝒪_X ⟶ f_*𝒪_Z`. -/
def pullbackStructureComparison :
    (pullbackFunctor f).obj (structureModule X) ⟶ structureModule Z :=
  SheafOfModules.pullbackObjUnitToUnit.{u} (structureSheafHom f)

/-- The canonical map `𝒪_X ⟶ f_*𝒪_Z` for a morphism of ringed spaces: Mathlib's
`SheafOfModules.unitToPushforwardObjUnit`, with its type declared at the
`Stacks.RingedSpace.structureRingSheaf` spelling. -/
def unitToPushforwardStructure :
    structureModule X ⟶ (pushforwardFunctor f).obj (structureModule Z) :=
  SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)

/-- The canonical `𝒪_X ⟶ f_*𝒪_Z` factors through the unit of `f^* ⊣ f_*`, because Mathlib
defines `f^*𝒪_X ⟶ 𝒪_Z` as its adjoint transpose. -/
theorem unitToPushforwardStructure_eq :
    unitToPushforwardStructure f = (pullbackAdjunction f).unit.app (structureModule X) ≫
        (pushforwardFunctor f).map (pullbackStructureComparison f) :=
  (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (structureSheafHom f)).symm.trans (Adjunction.homEquiv_unit ..)

/-- **`f^*𝒪_X ⟶ 𝒪_Z` carries a pulled-back section to the image of the section under `f^♯`.**
This is the section-level content of Mathlib's `unitToPushforwardObjUnit_val_app_apply`, read
through the factorisation above. -/
theorem pullbackStructureComparison_pullbackUnit (U : (Opens X.carrier)ᵒᵖ)
    (a : ToType ((structureModule X).val.obj U)) :
    Hom.app (pullbackStructureComparison f).val ((opensMap f).op.obj U)
        (pullbackUnit f (structureModule X) U a) =
      Stacks.SheafOfModules.toUnit _ (sharp f U a) :=
  (PresheafOfModules.hom_congr_apply'
    (congrArg (fun g : _ ⟶ _ => SheafOfModules.Hom.val g)
      (unitToPushforwardStructure_eq f)) U a).symm.trans
    (SheafOfModules.unitToPushforwardObjUnit_val_app_apply (structureSheafHom f) a)

end RingedSpace

/-- **The left unit constraint on the sheafification-unit image of a pure tensor**: it carries
`a ⊗ m` to `a • m`.  The lemma
`Stacks.SheafOfModules.Invertible.toSheafify_tensorProductLeftUnitor` is the case `a = 1`; the
scalar is carried across by `Stacks.SheafOfModules.toUnit_smul` and `TensorProduct.smul_tmul`.
The first tensor factor is a free variable `a'` named by `ha`, so that the lemma applies without
a rewrite having to locate it. -/
theorem structureUnitor_tensorSheafUnit_tmul {W : RingedSpace.{u, u}}
    (M : SheafOfModules.{u} (structureRingSheaf W)) (U : (Opens W.carrier)ᵒᵖ)
    (a : ToType ((structureRingSheaf W).obj.obj U)) (m : ToType (M.val.obj U))
    (a' : ToType ((structureModule W).val.obj U))
    (ha : a' = Stacks.SheafOfModules.toUnit U a) :
    Hom.app (structureUnitor M).hom.val U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf (W)) (𝟙 (Stacks.RingedSpace.structureRingSheaf (W)).obj)).unit.app (PresheafOfModules.tensorObj (O := (W).presheaf) ((structureModule W)).val (M).val)) U (a' ⊗ₜ m)) = a • m := by
  rw [ha]
  letI : TensorProduct.CompatibleSMul (W.presheaf.obj U)
      ((structureRingSheaf W).obj.obj U) ((structureModule W).val.obj U) (M.val.obj U) := by
    change TensorProduct.CompatibleSMul (W.presheaf.obj U)
      (W.presheaf.obj U) ((structureModule W).val.obj U) (M.val.obj U)
    infer_instance
  have h1 : a • Stacks.SheafOfModules.unitOne (S := structureRingSheaf W) U
      = Stacks.SheafOfModules.toUnit (S := structureRingSheaf W) U a :=
    (Stacks.SheafOfModules.toUnit_smul U a 1).trans (by rw [mul_one])
  rw [← h1]
  refine (congrArg (fun tensorValue => Hom.app (structureUnitor M).hom.val U
    (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf W)
      (𝟙 (structureRingSheaf W).obj)).unit.app
        (PresheafOfModules.tensorObj (O := W.presheaf) (structureModule W).val M.val))
      U tensorValue))
    (TensorProduct.smul_tmul (R := W.presheaf.obj U) (a : W.presheaf.obj U)
      (Stacks.SheafOfModules.unitOne (S := structureRingSheaf W) U) m)).trans ?_
  exact Stacks.SheafOfModules.Invertible.toSheafify_tensorProductLeftUnitor
    W.presheaf (structureSheafRing W).property M U (a • m)

section Coherence

variable {X Z : RingedSpace.{u, u}} (f : Z ⟶ X)

/-- **The pullback tensor comparison is compatible with the left unit constraints.**  In
transposed form: the adjoint transpose of `c : f^*(𝒪_X ⊗ L) ⟶ f^*𝒪_X ⊗ f^*L`, followed by
`f^*𝒪_X ⟶ 𝒪_Z` in the first factor and then the left unit constraint on `Z`, is the left unit
constraint on `X` followed by the unit of `f^* ⊣ f_*`.

A morphism out of a sheaf tensor product is determined by its effect on the
sheafification-unit images of pure tensors, and on `x ⊗ y` both sides are `f^♯x · η y`: on the
left by `Stacks.RingedSpace.comparisonTranspose_unit_tmul` and
`pullbackStructureComparison_pullbackUnit`, on the right by
`Stacks.RingedSpace.pullbackUnit_smul`. -/
theorem comparisonTranspose_comp_structureUnitor
    (L : SheafOfModules.{u} (structureRingSheaf X)) :
    comparisonTranspose f (structureModule X) L ≫
        (pushforwardFunctor f).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map
              (pullbackStructureComparison f ×ₘ 𝟙 ((pullbackFunctor f).obj L)) ≫
            (structureUnitor ((pullbackFunctor f).obj L)).hom) =
      (structureUnitor L).hom ≫ (pullbackAdjunction f).unit.app L := by
  refine PresheafOfModules.sheafification_hom_ext
    (PresheafOfModules.tensorObj_hom_ext fun U x y => ?_)
  have key : ∀ (x : ToType ((structureModule X).val.obj U)) (y : ToType (L.val.obj U)),
      Hom.app (structureUnitor ((pullbackFunctor f).obj L)).hom.val ((opensMap f).op.obj U)
          (Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map
              (pullbackStructureComparison f ×ₘ 𝟙 ((pullbackFunctor f).obj L))).val
            ((opensMap f).op.obj U)
            (Hom.app (comparisonTranspose f (structureModule X) L).val U
              (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf (X)) (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app (PresheafOfModules.tensorObj (O := (X).presheaf) ((structureModule X)).val (L).val)) U (x ⊗ₜ y))))
        = Hom.app ((pullbackAdjunction f).unit.app L).val U
            (Hom.app (structureUnitor L).hom.val U
              (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf (X)) (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app (PresheafOfModules.tensorObj (O := (X).presheaf) ((structureModule X)).val (L).val)) U (x ⊗ₜ y))) := by
    intro x y
    have a1 : Hom.app (comparisonTranspose f (structureModule X) L).val U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf (X)) (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app (PresheafOfModules.tensorObj (O := (X).presheaf) ((structureModule X)).val (L).val)) U (x ⊗ₜ y))
        = Hom.app ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf (Z)) (𝟙 (Stacks.RingedSpace.structureRingSheaf (Z)).obj)).unit.app (PresheafOfModules.tensorObj (O := (Z).presheaf) (((pullbackFunctor f).obj (structureModule X))).val (((pullbackFunctor f).obj L)).val)) ((opensMap f).op.obj U)
            (pullbackUnit f (structureModule X) U x ⊗ₜ pullbackUnit f L U y) :=
      comparisonTranspose_unit_tmul f (structureModule X) L U x y
    have a2 : Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map
            (pullbackStructureComparison f ×ₘ 𝟙 ((pullbackFunctor f).obj L))).val
          ((opensMap f).op.obj U)
          (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf (Z)) (𝟙 (Stacks.RingedSpace.structureRingSheaf (Z)).obj)).unit.app (PresheafOfModules.tensorObj (O := (Z).presheaf) (((pullbackFunctor f).obj (structureModule X))).val (((pullbackFunctor f).obj L)).val)) ((opensMap f).op.obj U)
            (pullbackUnit f (structureModule X) U x ⊗ₜ pullbackUnit f L U y))
        = Hom.app ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf (Z)) (𝟙 (Stacks.RingedSpace.structureRingSheaf (Z)).obj)).unit.app (PresheafOfModules.tensorObj (O := (Z).presheaf) ((structureModule Z)).val (((pullbackFunctor f).obj L)).val))
            ((opensMap f).op.obj U)
            (Hom.app (pullbackStructureComparison f).val ((opensMap f).op.obj U)
                (pullbackUnit f (structureModule X) U x) ⊗ₜ
              pullbackUnit f L U y) :=
      tensorSheaf_map_unit_tmul Z (pullbackStructureComparison f)
        (𝟙 ((pullbackFunctor f).obj L)) ((opensMap f).op.obj U) _ _
    have a3 := structureUnitor_tensorSheafUnit_tmul ((pullbackFunctor f).obj L)
      ((opensMap f).op.obj U) (sharp f U x) (pullbackUnit f L U y)
      (Hom.app (pullbackStructureComparison f).val ((opensMap f).op.obj U)
        (pullbackUnit f (structureModule X) U x))
      (pullbackStructureComparison_pullbackUnit f U x)
    have a4 := structureUnitor_tensorSheafUnit_tmul L U
      (x : ToType ((structureRingSheaf X).obj.obj U)) y x rfl
    rw [a1, a2, a3, a4]
    exact (pullbackUnit_smul f L U x y).symm
  exact key x y

/-- **The twisted comparison, for an arbitrary morphism of ringed spaces.**  Tensoring
`𝒪_X ⟶ f_*𝒪_Z` with `L` and composing with the projection formula and the left unit constraint
on `Z` gives the left unit constraint on `X` followed by the unit of `f^* ⊣ f_*`.

Naturality of the projection-formula map in its first argument moves `f_*(f^*𝒪_X ⟶ 𝒪_Z)` past
it; its compatibility with the tensorized unit identifies what remains with the adjoint
transpose of the pullback tensor comparison; and
`comparisonTranspose_comp_structureUnitor` finishes. -/
theorem tensorSheaf_map_unitToPushforwardStructure_comp_projection
    (L : SheafOfModules.{u} (structureRingSheaf X)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map (unitToPushforwardStructure f ×ₘ 𝟙 L) ≫
        (projectionFormulaMap f (structureModule Z) L ≫
          (pushforwardFunctor f).map (structureUnitor ((pullbackFunctor f).obj L)).hom) =
      (structureUnitor L).hom ≫ (pullbackAdjunction f).unit.app L := by
  have hsplit :
      ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
            (unitToPushforwardStructure f ×ₘ 𝟙 L) =
        ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
            ((pullbackAdjunction f).unit.app (structureModule X) ×ₘ 𝟙 L) ≫
          ((Functor.uncurry.obj
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
            ((pushforwardFunctor f).map (pullbackStructureComparison f) ×ₘ 𝟙 L) := by
    rw [← CategoryTheory.Functor.map_comp]
    exact congrArg _ (CategoryTheory.Prod.hom_ext (unitToPushforwardStructure_eq f)
      (Category.comp_id (𝟙 L)).symm)
  have hnatural :
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
            ((pushforwardFunctor f).map (pullbackStructureComparison f) ×ₘ 𝟙 L) ≫
          projectionFormulaMap f (structureModule Z) L =
        projectionFormulaMap f ((pullbackFunctor f).obj (structureModule X)) L ≫
          (pushforwardFunctor f).map
            (((Functor.uncurry.obj
                  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map
              (pullbackStructureComparison f ×ₘ 𝟙 ((pullbackFunctor f).obj L))) :=
    (projectionFormulaMap_natural f (pullbackStructureComparison f) (𝟙 L)).trans
      (congrArg
        (fun pullbackIdentity =>
          projectionFormulaMap f ((pullbackFunctor f).obj (structureModule X)) L ≫
            (pushforwardFunctor f).map
              (((Functor.uncurry.obj
                    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map
                (pullbackStructureComparison f ×ₘ pullbackIdentity)))
        ((pullbackFunctor f).map_id L))
  refine (congrArg (· ≫ _) hsplit).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (fun middle => _ ≫ middle ≫ _) hnatural).trans ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (congrArg (fun pushforwardComposite => _ ≫ _ ≫ pushforwardComposite)
    (CategoryTheory.Functor.map_comp _ _ _).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _)
    (projectionFormulaMap_natural_unit f (structureModule X) L)).trans ?_
  exact (congrArg (fun t => t ≫ (pushforwardFunctor f).map
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map
          (pullbackStructureComparison f ×ₘ 𝟙 ((pullbackFunctor f).obj L)) ≫
        (structureUnitor ((pullbackFunctor f).obj L)).hom))
    (homEquiv_comparison f (structureModule X) L)).trans
    (comparisonTranspose_comp_structureUnitor f L)

end Coherence

end Stacks.AffineProjectionFormula

namespace Stacks.AffineClosedUnion

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (L : X.Modules)

/-- **The coherence `TwistedSections` recorded as owed.**  `Stacks.AffineClosedUnion.twistedUnit`
— the twist by `L` of `𝒪_X ⟶ i_*𝒪_Z`, conjugated by the left unit constraint and the projection
formula — **is** the unit of `i^* ⊣ i_*` at `L`.

All five crossings between the `AlgebraicGeometry.Scheme.Modules` spelling and the
`Stacks.RingedSpace` spelling the projection formula is stated at are definitional, including the
two adjunctions, so this is the ringed-space statement
`Stacks.AffineProjectionFormula.tensorSheaf_map_unitToPushforwardStructure_comp_projection` with
the inverse of the left unit constraint cancelled. -/
theorem twistedUnit_eq_unit :
    twistedUnit i L = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L := by
  rw [twistedUnit, Iso.inv_comp_eq]
  have comparison := Stacks.AffineProjectionFormula.tensorSheaf_map_unitToPushforwardStructure_comp_projection
    i.toLRSHom.toShHom L
  exact (congrArg (fun tensorMap => tensorMap ≫ (twistPushforwardIso i L).hom)
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, u, u, u, u} X.sheaf
      (unitToPushforwardStructureSheaf i) (𝟙 L)).symm).trans comparison

/-- **The sections of the twisted unit are restriction**, which is what a consumer of the twisted
square needs: over an open `V`, `twistedUnit i L` carries a section of `L` to its image under the
unit of `i^* ⊣ i_*`, i.e. to `Stacks.RingedSpace.pullbackUnit`. -/
theorem twistedUnit_app_apply (V : X.Opens) (c : Γ(L, V)) :
    (twistedUnit i L).app V c =
      pullbackUnit i.toLRSHom.toShHom L (Opposite.op V) c :=
  by rw [twistedUnit_eq_unit]; rfl

variable (I₁ I₂ : X.IdealSheafData)

/-- **The vanishing form of the twisted square, with the unit of the adjunction in place of
`Stacks.AffineClosedUnion.twistedUnit`.**  This is
`Stacks.AffineClosedUnion.existsUnique_twisted_app_eq_zero_of_inf_eq_bot` read through
`twistedUnit_eq_unit`, and it is the form the proof of [Stacks, Tag 09NX] consumes: a section of
`i₂^*L` over the preimage of `V` vanishing on the scheme-theoretic intersection is the
restriction of a unique section of `L` over `V` vanishing on the first closed subscheme. -/
theorem existsUnique_unit_app_eq_zero_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
        (V : X.Opens)
    (b : Γ((Scheme.Modules.pullback I₂.subschemeι).obj L, I₂.subschemeι ⁻¹ᵁ V))
    (hb : (twistedRestrict (AlgebraicGeometry.Scheme.IdealSheafData.inclusion
        (le_sup_right : I₂ ≤ I₁ ⊔ I₂)) I₂.subschemeι
      (AlgebraicGeometry.Scheme.IdealSheafData.inclusion_subschemeι _) L).app V b = 0) :
    ∃! c : Γ(L, V),
      ((Scheme.Modules.pullbackPushforwardAdjunction I₁.subschemeι).unit.app L).app V c = 0 ∧
        ((Scheme.Modules.pullbackPushforwardAdjunction I₂.subschemeι).unit.app L).app V c = b :=
  (twistedUnit_eq_unit I₁.subschemeι L) ▸ (twistedUnit_eq_unit I₂.subschemeι L) ▸
    existsUnique_twisted_app_eq_zero_of_inf_eq_bot I₁ I₂ h L V b hb

end Stacks.AffineClosedUnion

end
