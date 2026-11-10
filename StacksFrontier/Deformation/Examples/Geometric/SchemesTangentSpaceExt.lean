module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentExtStandardModel
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationSolutionRealization
public import StacksFrontier.Deformation.Examples.Geometric.SchemesInfinitesimalAutomorphismsTrivial
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionClasses
public import StacksFrontier.Homology.Injectives.FilteredComplex.HomComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tangent space of the deformation category of a scheme (Stacks 0DY9, second display)

Let `X` be a scheme over a field `k`. The second display of [Stacks Project, Tag 0DY9] is

`T𝓓_X = Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`.

The source's proof: `T𝓓_X` is the set of isomorphism classes of flat deformations of `X` over
`k[ε]`, and by [Stacks Project, Tag 0D14] (1) that set is a principal homogeneous space under
`Ext¹_{𝒪_X}(NL_{X/k}, f^*𝒞_{Spec k/Spec k[ε]}) = Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`; the trivial
deformation `X ×_{Spec k} Spec k[ε]` is a base point.

## Main definitions

* `Deformation.Examples.tangentBaseCoordinate`: the identification with `DualNumber k` of the dual
  numbers `(artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)` at which the tangent
  space of [Stacks Project, Tag 06SR] is read (written `tangentBase` in this file).
* `Deformation.Examples.schemeTangentSpace`: `T𝓓_X`.
* `Deformation.Examples.tangentTrivialFiberObj`: the trivial deformation over the tangent base.
* `Deformation.Examples.tangentPulledIdealIso`: `f^* 𝒥 ≅ 𝒪_X` for the closed point of `Spec k[ε]`.
* `Deformation.Examples.schemeTangentSpaceEquivExt`: **the second display of
  [Stacks Project, Tag 0DY9]**, `T𝓓_X ≃ Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`.

## Main results

* `Deformation.Examples.schemeTangentSpaceEquivExt_classOf`: the identification is the difference
  class of [Stacks Project, Tag 08UC] against the trivial deformation.
* `Deformation.Examples.schemeTangentSpaceEquivExt_trivial`: the trivial deformation goes to `0`.

## Implementation notes

The identification is a bijection of sets. It is not asserted to be `k`-linear for the canonical
vector-space structure of [Stacks Project, Tag 06IH] on `T𝓓_X`: that structure is defined through
the whole functor `V ↦ 𝓓_X(k[V])`, and linearity would need the difference class of
[Stacks Project, Tag 08UC] to be natural in the coefficient module, which is not available.

## References

* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 0D14](https://stacks.math.columbia.edu/tag/0D14)
* [Stacks Project, Tag 06SR](https://stacks.math.columbia.edu/tag/06SR)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpaceThickening

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### The tangent base -/

/-- The dual numbers `k[ε]`, as the object of `𝒞_Λ` at which the tangent space of
[Stacks Project, Tag 06SR] is read. -/
local notation "tangentBase" =>
  CategoryTheory.Functor.obj (artinianSquareZeroExtensionFunctor Λ k) (FGModuleCat.of k k)

/-- The tangent base is isomorphic in `𝒞_Λ` to the dual-number object
`Deformation.artinianDualNumbers`, by the identification of `k` with `ULift k`. -/
noncomputable def tangentBaseIsoDualNumbers :
    tangentBase ≅ Deformation.artinianDualNumbers.{u, u, u} Λ k :=
  (artinianSquareZeroExtensionFunctor Λ k).mapIso
    (ULift.moduleEquiv.{u, u, u} (R := k) (M := k)).symm.toFGModuleCatIso

/-- **The dual-number coordinate of the tangent base.** -/
noncomputable def tangentBaseCoordinate :
    ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k) : Type u) ≃ₐ[Λ]
      DualNumber k :=
  (AlgEquiv.ofAlgHom (tangentBaseIsoDualNumbers (Λ := Λ) (k := k)).hom.hom
      (tangentBaseIsoDualNumbers (Λ := Λ) (k := k)).inv.hom
      (by rw [← ArtinianLocalAlgCat.comp_hom, Iso.inv_hom_id, ArtinianLocalAlgCat.id_hom])
      (by rw [← ArtinianLocalAlgCat.comp_hom, Iso.hom_inv_id, ArtinianLocalAlgCat.id_hom])).trans
    artinianDualNumbersCoordinate

/-- The maximal ideal of the tangent base has square zero. -/
theorem maximalIdeal_tangentBase_sq_eq_bot :
    IsLocalRing.maximalIdeal
      ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k) : Type u) ^ 2 = ⊥ :=
  maximalIdeal_sq_eq_bot_of_dualNumberEquiv tangentBaseCoordinate

/-- The constant inclusion `k → k[ε]` into the tangent base. -/
noncomputable def tangentInclusion :
    residueFieldObject.{u, u, u} Λ k ⟶ tangentBase :=
  dualNumbersInclusion.{u, u, u} ≫ (tangentBaseIsoDualNumbers (Λ := Λ) (k := k)).inv

/-! ### The tangent space -/

variable (X : Over (Spec (CommRingCat.of k)))

/-- The cofiberedness of the deformation category of `X` ([Stacks Project, Tag 0DY8]). -/
theorem schemeDeformation_cofibered :
    IsCofiberedInGroupoids
      (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)).p :=
  (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation.cofibered

/-- **The tangent space `T𝓓_X` of the deformation category of `X`**: the value at the dual
numbers of the functor of isomorphism classes ([Stacks Project, Tag 06SR]). -/
abbrev schemeTangentSpace : Type (u + 1) :=
  artinianTangentSpace Λ k
    (isomorphismClasses
      (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
      (schemeDeformation_cofibered X))

/-- The tangent space is the set of isomorphism classes of the fibre over the dual numbers. -/
def schemeTangentSpaceEquivFiberClasses :
    schemeTangentSpace (Λ := Λ) (k := k) X ≃
      Quotient (isIsomorphicSetoid
        ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber tangentBase)) :=
  Equiv.cast (isomorphismClasses_obj _ (schemeDeformation_cofibered X) tangentBase)

/-- The trivial deformation `X ×_{Spec k} Spec k[ε]` over the tangent base. -/
noncomputable def tangentTrivialDeformation : SchemeDeformationCategory (Λ := Λ) (k := k) X :=
  baseChangeDeformation (residueTrivialDeformation X) tangentInclusion

/-- The trivial deformation, as a point of the fibre over the tangent base. -/
abbrev tangentTrivialFiberObj :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber tangentBase :=
  ⟨tangentTrivialDeformation X, rfl⟩

/-! ### The coefficients -/

/-- **`f^* 𝒥 = 𝒪_X` for the closed point of `Spec k[ε]`**: the conormal sheaf of the closed point
is the structure sheaf of `Spec k` ([`Deformation.Examples.residueConormalIsoUnit`]), and the
pullback of a structure sheaf is the structure sheaf. -/
noncomputable def tangentPulledIdealIso :
    SchemeDeformationCategory.pulledIdeal (tangentBase) X ≅
      structureSheafModules X.left :=
  haveI := residueSpecMap_isClosedImmersion (tangentBase)
  (modulePullback X.hom.toLRSHom.toShHom).mapIso
      (Stacks.Immersion.conormalSheafSelfIso (residueSpecMap tangentBase) ≪≫
        residueConormalIsoUnit tangentBase tangentBaseCoordinate) ≪≫
    modulePullbackUnitIso X.hom.toLRSHom.toShHom

/-- Changing the coefficients of `Ext¹_{𝒪_X}(NL_{X/k}, -)` along `f^* 𝒥 ≅ 𝒪_X`. -/
noncomputable def tangentExtCoefficientsAddEquiv :
    Scheme.naiveCotangentExt X.hom
        (SchemeDeformationCategory.pulledIdeal (tangentBase) X) 1 ≃+
      Scheme.naiveCotangentExt X.hom (structureSheafModules X.left) 1 :=
  Stacks.Injectives.homCongrAddEquiv (Iso.refl _)
    ((shiftFunctor _ (1 : ℤ)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (tangentPulledIdealIso (Λ := Λ) X)))

/-! ### From a torsor structure on the solutions to the tangent space -/

/-- The solutions of the deformation problem of Stacks 08U7 attached to the tangent base:
the closed point `Spec k ⊂ Spec k[ε]`, the structure morphism of `X`, the module `f^* 𝒥` and the
identity. -/
abbrev TangentSolution :=
  DeformationSolution (residueSpecMap (tangentBase)).toLRSHom.toShHom
    (residueSpecMap_isFirstOrderThickening tangentBase maximalIdeal_tangentBase_sq_eq_bot)
    X.hom.toLRSHom.toShHom (SchemeDeformationCategory.pulledIdeal tangentBase X) (𝟙 _)

/-- The tangent space is the set of isomorphism classes of solutions, for any setoid on solutions
whose relation is the isomorphism of solutions. -/
noncomputable def schemeTangentSpaceEquivSolutionClasses (r : Setoid (TangentSolution (Λ := Λ) X))
    (hr : ∀ Q₁ Q₂, r Q₁ Q₂ ↔ Isomorphic Q₁ Q₂) :
    schemeTangentSpace (Λ := Λ) (k := k) X ≃ Quotient r :=
  (schemeTangentSpaceEquivFiberClasses X).trans
    (fiberClassesEquivSolutionClasses maximalIdeal_tangentBase_sq_eq_bot r hr)

/-- The class of the trivial deformation among the isomorphism classes of solutions. -/
noncomputable abbrev trivialSolutionClass (r : Setoid (TangentSolution (Λ := Λ) X)) : Quotient r :=
  Quotient.mk r (fiberSolution maximalIdeal_tangentBase_sq_eq_bot (tangentTrivialFiberObj X))

/-- **A principal homogeneous structure on the isomorphism classes of solutions identifies the
tangent space with the acting group**, the class of the trivial deformation going to `0`. -/
noncomputable def schemeTangentSpaceEquivOfAddTorsor (r : Setoid (TangentSolution (Λ := Λ) X))
    (hr : ∀ Q₁ Q₂, r Q₁ Q₂ ↔ Isomorphic Q₁ Q₂) {E : Type*} [AddGroup E]
    (T : AddTorsor E (Quotient r)) :
    schemeTangentSpace (Λ := Λ) (k := k) X ≃ E :=
  letI := T
  (schemeTangentSpaceEquivSolutionClasses X r hr).trans
    (Equiv.vaddConst (trivialSolutionClass X r)).symm

/-- The identification of `schemeTangentSpaceEquivOfAddTorsor` sends the class of a point of the
fibre to its difference with the trivial deformation. -/
theorem schemeTangentSpaceEquivOfAddTorsor_classOf (r : Setoid (TangentSolution (Λ := Λ) X))
    (hr : ∀ Q₁ Q₂, r Q₁ Q₂ ↔ Isomorphic Q₁ Q₂) {E : Type*} [AddGroup E]
    (T : AddTorsor E (Quotient r))
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber tangentBase) :
    letI := T
    schemeTangentSpaceEquivOfAddTorsor X r hr T
        (classOf (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) X))
          (schemeDeformation_cofibered X) x) =
      Quotient.mk r (fiberSolution maximalIdeal_tangentBase_sq_eq_bot x) -ᵥ
        trivialSolutionClass X r := by
  let := T
  have hc : schemeTangentSpaceEquivSolutionClasses X r hr
      (classOf (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) X))
        (schemeDeformation_cofibered X) x) =
      Quotient.mk r (fiberSolution maximalIdeal_tangentBase_sq_eq_bot x) := by
    have h := classOf_eq
      (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
      (schemeDeformation_cofibered X) x
    exact congrArg (fiberClassesEquivSolutionClasses maximalIdeal_tangentBase_sq_eq_bot r hr) h
  change (Equiv.vaddConst (trivialSolutionClass X r)).symm
    (schemeTangentSpaceEquivSolutionClasses X r hr _) = _
  rw [hc]
  rfl

/-- The identification of `schemeTangentSpaceEquivOfAddTorsor` sends the class of the trivial
deformation to `0`. -/
theorem schemeTangentSpaceEquivOfAddTorsor_trivial (r : Setoid (TangentSolution (Λ := Λ) X))
    (hr : ∀ Q₁ Q₂, r Q₁ Q₂ ↔ Isomorphic Q₁ Q₂) {E : Type*} [AddGroup E]
    (T : AddTorsor E (Quotient r)) :
    schemeTangentSpaceEquivOfAddTorsor X r hr T
        (classOf (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) X))
          (schemeDeformation_cofibered X) (tangentTrivialFiberObj X)) = 0 := by
  let := T
  rw [schemeTangentSpaceEquivOfAddTorsor_classOf, vsub_self]

/-- **The tangent space as `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`, from a principal homogeneous structure on
the isomorphism classes of solutions under `Ext¹_{𝒪_X}(NL_{X/k}, f^* 𝒥)`** (the acting group of
[Stacks Project, Tag 08UC], at the standard model of the derived category): the difference with
the trivial deformation, read at the model of the derived category in force for `𝒪_X`-modules
([`AlgebraicGeometry.Scheme.extOneNaiveCotangentAddEquiv`]) and with coefficients `𝒪_X` through
`f^* 𝒥 ≅ 𝒪_X`. -/
noncomputable def schemeTangentSpaceEquivExtOfAddTorsor (r : Setoid (TangentSolution (Λ := Λ) X))
    (hr : ∀ Q₁ Q₂, r Q₁ Q₂ ↔ Isomorphic Q₁ Q₂)
    (T : AddTorsor (extOneNaiveCotangent X.hom.toLRSHom.toShHom
      (SchemeDeformationCategory.pulledIdeal (tangentBase) X)) (Quotient r)) :
    schemeTangentSpace (Λ := Λ) (k := k) X ≃
      Scheme.naiveCotangentExt X.hom (structureSheafModules X.left) 1 :=
  (schemeTangentSpaceEquivOfAddTorsor X r hr T).trans
    ((Scheme.extOneNaiveCotangentAddEquiv X.hom _).trans
      (tangentExtCoefficientsAddEquiv (Λ := Λ) X)).toEquiv

/-- The identification of `schemeTangentSpaceEquivExtOfAddTorsor` sends the class of the trivial
deformation to `0`. -/
theorem schemeTangentSpaceEquivExtOfAddTorsor_trivial (r : Setoid (TangentSolution (Λ := Λ) X))
    (hr : ∀ Q₁ Q₂, r Q₁ Q₂ ↔ Isomorphic Q₁ Q₂)
    (T : AddTorsor (extOneNaiveCotangent X.hom.toLRSHom.toShHom
      (SchemeDeformationCategory.pulledIdeal (tangentBase) X)) (Quotient r)) :
    schemeTangentSpaceEquivExtOfAddTorsor X r hr T
        (classOf (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) X))
          (schemeDeformation_cofibered X) (tangentTrivialFiberObj X)) = 0 := by
  simp only [schemeTangentSpaceEquivExtOfAddTorsor, Equiv.trans_apply,
    schemeTangentSpaceEquivOfAddTorsor_trivial, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
    map_zero]

/-! ### The second display of Stacks 0DY9 -/

/-- The trivial deformation provides a solution. -/
instance nonempty_tangentSolution : Nonempty (TangentSolution (Λ := Λ) (k := k) X) :=
  ⟨fiberSolution maximalIdeal_tangentBase_sq_eq_bot (tangentTrivialFiberObj X)⟩

/-- **Stacks Project, Tag 0DY9, second display, as a bijection.** For a scheme `X` over the field
`k`,

`T𝓓_X = Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`.

`T𝓓_X` is the tangent space of the deformation category of `X` of [Stacks Project, Tag 0DY7]:
the value at the dual numbers `k[ε]` of its functor of isomorphism classes
([Stacks Project, Tag 06SR]), that is, the set of isomorphism classes of flat deformations of `X`
over `k[ε]`. `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)` is `AlgebraicGeometry.Scheme.naiveCotangentExt` of the
structure morphism of `X` with coefficients `𝒪_X`, in degree `1`.

The identification is the source's proof: a flat deformation of `X` over `k[ε]` is a solution of
the deformation problem of [Stacks Project, Tag 08U7] for `Spec k ⊂ Spec k[ε]` with ideal
`f^* 𝒞_{Spec k/Spec k[ε]} = 𝒪_X` (`Deformation.Examples.fiberClassesEquivSolutionClasses`, the
reduction made in the proof of [Stacks Project, Tag 0D14]); the isomorphism classes of solutions
are principal homogeneous under `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)` ([Stacks Project, Tag 08UC],
`AlgebraicGeometry.RingedSpaceThickening.solutionClassesAddTorsor`); and the class of a
deformation is sent to its difference with the trivial deformation `X ×_{Spec k} Spec k[ε]`, which
therefore goes to `0` (`Deformation.Examples.schemeTangentSpaceEquivExt_trivial`). The `k`-linear
form of the display is `Deformation.Examples.schemeTangentSpaceLinearEquivExt`. -/
@[sga "7 VI 4.16" "(b), special case"]
noncomputable def schemeTangentSpaceEquivExt :
    schemeTangentSpace (Λ := Λ) (k := k) X ≃
      Scheme.naiveCotangentExt X.hom (structureSheafModules X.left) 1 :=
  schemeTangentSpaceEquivExtOfAddTorsor X isomorphicSetoid (fun _ _ => Iff.rfl)
    solutionClassesAddTorsor

/-- **The identification of the second display of Stacks 0DY9 is the difference class.** On the
class of a flat deformation over `k[ε]` it is the difference class of [Stacks Project, Tag 08UC]
of its solution against that of the trivial deformation, read at the model of the derived category
of `𝒪_X`-modules in force and with coefficients `𝒪_X`. -/
theorem schemeTangentSpaceEquivExt_classOf
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber tangentBase) :
    schemeTangentSpaceEquivExt (Λ := Λ) X
        (classOf (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) X))
          (schemeDeformation_cofibered X) x) =
      tangentExtCoefficientsAddEquiv (Λ := Λ) X
        (Scheme.extOneNaiveCotangentAddEquiv X.hom _
          (differenceClass (fiberSolution maximalIdeal_tangentBase_sq_eq_bot x)
            (fiberSolution maximalIdeal_tangentBase_sq_eq_bot (tangentTrivialFiberObj X)))) := by
  let := (solutionClassesAddTorsor : AddTorsor _ (SolutionClasses
    (residueSpecMap (tangentBase)).toLRSHom.toShHom
    (residueSpecMap_isFirstOrderThickening tangentBase maximalIdeal_tangentBase_sq_eq_bot)
    X.hom.toLRSHom.toShHom (SchemeDeformationCategory.pulledIdeal tangentBase X) (𝟙 _)))
  have h := schemeTangentSpaceEquivOfAddTorsor_classOf X isomorphicSetoid (fun _ _ => Iff.rfl)
    solutionClassesAddTorsor x
  change tangentExtCoefficientsAddEquiv (Λ := Λ) X (Scheme.extOneNaiveCotangentAddEquiv X.hom _
    (schemeTangentSpaceEquivOfAddTorsor X isomorphicSetoid (fun _ _ => Iff.rfl)
      solutionClassesAddTorsor _)) = _
  rw [h]
  rfl

/-- **The identification of the second display of Stacks 0DY9 sends the trivial deformation to
`0`.** -/
theorem schemeTangentSpaceEquivExt_trivial :
    schemeTangentSpaceEquivExt (Λ := Λ) X
        (classOf (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) X))
          (schemeDeformation_cofibered X) (tangentTrivialFiberObj X)) = 0 :=
  schemeTangentSpaceEquivExtOfAddTorsor_trivial X isomorphicSetoid (fun _ _ => Iff.rfl)
    solutionClassesAddTorsor

end Deformation.Examples

end
