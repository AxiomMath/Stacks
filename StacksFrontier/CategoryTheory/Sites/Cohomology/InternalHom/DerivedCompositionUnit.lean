module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualDevissage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.QuasiIsoInvariance
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit
import StacksCore.Tactic.StacksAttribute

/-! # The unit law for the composition morphism of derived internal Hom

Let `(C, O)` be a ringed site.

**This file carries no `@[stacks]` attribute, and that is deliberate.** Stacks 0A98 asserts
only that the canonical morphism

`RSheafHom(L, M) ⊗^L_O RSheafHom(K, L) ⟶ RSheafHom(K, M)`

exists; Stacks 0A91 asserts only that its chain-level counterpart
`Tot(SheafHom(L, M) ⊗_O SheafHom(K, L)) ⟶ SheafHom(K, M)` exists. Neither tag, and no other
tag of the Stacks Project, asserts that either morphism is unital or associative. The source
itself records the gap: the proof of [Stacks, Tag 0FVB] invokes associativity of the
composition of Stacks 0A8V — the ringed space form of 0A98 — with the words "(insert future
reference here)". The unitality proved below is therefore content *beyond* its neighbouring
tags, not a formalization of any of them, and tagging it would be a false claim of coverage.

## The unit law

The composition morphism of internal Hom complexes, read at the structure sheaf as its source
object and precomposed with the unit section of the tensor factor, is precomposition:

`AlgebraicGeometry.RingedSite.compositionMap_structureSheafUnit` says that for complexes `L`,
`M` and a morphism `g : O[0] ⟶ L`, the composite

`SheafHom(L, M) ⟶ Tot(SheafHom(L, M) ⊗_O O[0]) ⟶ Tot(SheafHom(L, M) ⊗_O SheafHom(O[0], L))
  ⟶ SheafHom(O[0], M)`

— the unit section of the tensor factor, then the section of `SheafHom(O[0], L)` named by `g`,
then the composition morphism of Stacks 0A91 — is `SheafHom(g, M)`. Taking `L = O[0]` and
`g = 𝟙` this is exactly the statement that composing with the identity section is the
identity, in the second (source-side) variable of the composition morphism; it is the **right**
unit law. The left unit law, which would insert the identity section of `SheafHom(M, M)` into
the first tensor factor, is not proved here: see "What this file does not contain".

The first arrow above is an isomorphism — `AlgebraicGeometry.RingedSite.tensorTotalUnitIso`,
the collapse `W ≅ Tot(W ⊗_O O[0])` of the total tensor complex against the structure sheaf in
degree zero, with no sign, since the structure sheaf sits in degree zero and the Koszul sign of
the total complex is carried by the second factor's differential. So the unit law above
determines the composition morphism out of the structure sheaf completely.

Transporting that along the K-injective model comparison of a derived internal Hom datum gives
`AlgebraicGeometry.RingedSite.derivedSheafHomComposition_structureSheafSource`, the unit law
for Stacks 0A98 at a structure-sheaf source, and
`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomComposition_structureSheaf`: the derived
composition morphism `RSheafHom(O, M) ⊗^L_O RSheafHom(O, O) ⟶ RSheafHom(O, M)` is invertible.

## The consequence for Stacks 08JJ

The canonical map of Stacks 08JD, `Φ_L : M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)`, is *defined* as the
composition morphism of Stacks 0A98 at intermediate object the structure sheaf, so the unit law
computes it at `L = O`:
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_structureSheaf` is the
invertibility of `Φ_O`, and
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_iso_structureSheaf` the
invertibility of `Φ_L` for every `L` isomorphic to the structure sheaf. This is the base case
of the dévissage of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualDevissage`, whose
section "What this file does not contain" records that the dévissage establishes invertibility
at no nonzero object precisely because no unitality statement for Stacks 0A98 was available.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorTotalStructureSheafUnit`: the morphism
  `W ⟶ Tot(W ⊗_O O[0])`, `w ↦ w ⊗ 1`.
* `AlgebraicGeometry.RingedSite.tensorTotalStructureSheafCollapse`: the morphism
  `Tot(W ⊗_O O[0]) ⟶ W`, `w ⊗ b ↦ b · w`.
* `AlgebraicGeometry.RingedSite.tensorTotalUnitIso`: the two are mutually inverse.

## Main results

* `AlgebraicGeometry.RingedSite.compositionMap_structureSheafUnit`: the chain-level unit law,
  and `AlgebraicGeometry.RingedSite.compositionMap_structureSheafSource_eq`, the same identity
  with the unit isomorphism moved to the other side.
* `AlgebraicGeometry.RingedSite.derivedSheafHomComposition_structureSheafSource`: the unit law
  for the derived composition morphism of Stacks 0A98, on K-injective models.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomComposition_structureSheaf`: derived
  composition `RSheafHom(O, M) ⊗^L_O RSheafHom(O, O) ⟶ RSheafHom(O, M)` is invertible.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_structureSheaf` and
  `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_iso_structureSheaf`: the
  base case of the dévissage of Stacks 08JJ.

## Implementation notes

Neither of the two morphisms of `tensorTotalUnitIso` is a new construction: the unit
`W ⟶ Tot(W ⊗_O O[0])` is the diagonal morphism of Stacks 0A93 at second argument the structure
sheaf, followed by evaluation at the unit section, and the collapse `Tot(W ⊗_O O[0]) ⟶ W` is
the composition morphism of Stacks 0A91 at `K = L = O[0]`, `M = W`, read through
`AlgebraicGeometry.RingedSite.structureSheafHomIso` in both tensor factors and in the target.
So the whole file is an identity between morphisms already in the library, and the degreewise
collapse of a total tensor complex against a complex concentrated in one degree is not needed.

Every statement about sections is made at a *free* total degree, with an equation
`t + r = c` as a hypothesis, rather than at the degree `t + r`. This is what keeps the
computation free of transports: the degree `n + 0` produced by a pure tensor with a degree-zero
section is not syntactically `n`, and with a free degree variable it can be made `n` by
substitution instead. `compositionMap_tensorTotalSectionAt` is
`AlgebraicGeometry.RingedSite.compositionMap_tensorTotalSection` in that form.

## What this file does not contain

**The left unit law is not proved.** It would say that inserting the identity section of
`SheafHom(M, M)` into the *first* tensor factor of the composition morphism is the identity on
`SheafHom(K, M)`. The identity section of `SheafHom(M, M)` is not in the library, and the right
unit law avoids needing it: at `L = O[0]` the section of `SheafHom(O[0], O[0])` playing that
role is the image of the unit section under the isomorphism
`AlgebraicGeometry.RingedSite.structureSheafHomIso`, which the library does have, so the only
identity section used below is one of an internal Hom complex *out of* the structure sheaf. The
left unit law is also not what the consumer of this file needs: the canonical map of
Stacks 08JD is the composition morphism with the structure sheaf as its *intermediate* object,
and the dévissage
of Stacks 08JJ runs over its source object, so the base case is a right unit law.

**The right unit law is proved at a structure-sheaf source only.** The general form would read:
for an arbitrary object `K` of `D(O)`, the canonical unit `O ⟶ RSheafHom(K, K)` inserted into
the second tensor factor of `RSheafHom(K, M) ⊗^L_O RSheafHom(K, K) ⟶ RSheafHom(K, M)` is the
right unit constraint. That is not proved here, and the obstruction is the same missing identity
section: at a general `K` the unit is the class of the identity section of `SheafHom(A, A)` for
a representative `A`, and no such section is in the library. Nothing is lost for the consumer:
the canonical map of Stacks 08JD is derived composition whose *source* object is the object
being dualized and whose *intermediate* object is the structure sheaf, so its base case at
`L = O` is the composition morphism with `O` as both source and intermediate object, which is
the case treated below.

**Associativity is not proved either**, and the Stacks Project does not state it; see the first
paragraph.

**The unit law is not identified with the monoidal right unitor.** The collapse
`tensorTotalStructureSheafCollapse` is not compared with
`Stacks.SheafOfModules.tensorComplexUnitIso`, and so the derived unit law below is not stated
as "composition with the unit is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso`". Both collapses are
isomorphisms and both are inverse to formation of the pure tensor with `1`, so they agree; but
`tensorComplexUnitIso` is assembled from `CochainComplex.KFlatBifunctor.totalSingleIso` and
`Stacks.SheafOfModules.rowComplexUnitIso` and has no description on local sections, and
supplying one is a separate piece of work. Nothing below needs it: invertibility of the
composition morphism, which is what the dévissage base case consumes, does not.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A93](https://stacks.math.columbia.edu/tag/0A93)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open CochainComplex.HomComplex

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

/-! ## The total tensor product against the structure sheaf in degree zero -/

section Collapse

variable (W : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The pure tensor with the unit section.** The morphism `W ⟶ Tot(W ⊗_O O[0])` sending a
local section `w` to `w ⊗ 1`: the diagonal morphism of Stacks 0A93 at second argument the
structure sheaf, followed by evaluation at the unit section. -/
def tensorTotalStructureSheafUnit : W ⟶ tensorTotal X W (structureSheafComplex X) :=
  diagonalMap X W (structureSheafComplex X) ≫
    structureSheafHomEvaluation X (tensorTotal X W (structureSheafComplex X))

/-- The unit morphism sends a local section to its pure tensor with the unit section. -/
lemma tensorTotalStructureSheafUnit_apply (U : X.C) (n : ℤ)
    (w : (W.X n).val.obj (op U)) :
    ((tensorTotalStructureSheafUnit X W).f n).val.app (op U) w =
      tensorTotalSectionAt X W (structureSheafComplex X) U n 0 n (add_zero n) w
        (structureSheafOne X U) := by
  show ((structureSheafHomEvaluation X (tensorTotal X W (structureSheafComplex X))).f n).val.app
      (op U) (((diagonalMap X W (structureSheafComplex X)).f n).val.app (op U) w) = _
  rw [structureSheafHomEvaluation_apply, diagonalMap_applyHomSection]

/-- **The collapse of the total tensor product against the structure sheaf.** The morphism
`Tot(W ⊗_O O[0]) ⟶ W` sending a pure tensor `w ⊗ b` to `b · w`: the composition morphism of
Stacks 0A91 at `K = L = O[0]` and `M = W`, read through the identification of an internal Hom
complex out of the structure sheaf with its target in both tensor factors and in the target. -/
def tensorTotalStructureSheafCollapse : tensorTotal X W (structureSheafComplex X) ⟶ W :=
  tensorTotalMap X (structureSheafHomIso X W).inv
      (structureSheafHomIso X (structureSheafComplex X)).inv ≫
    compositionMap X (structureSheafComplex X) (structureSheafComplex X) W ≫
    structureSheafHomEvaluation X W

end Collapse

/-- `compositionMap` sends a local pure tensor to the composite of its two factors, with the
total degree given as a variable. -/
lemma compositionMap_tensorTotalSectionAt
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (p q c : ℤ)
    (h : p + q = c)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    ((compositionMap X K L M).f c).val.app (op U)
        (tensorTotalSectionAt X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj U p q c h
          β γ) =
      compositionSection X U p q c h β γ := by
  subst h
  exact compositionMap_tensorTotalSection X K L M U p q β γ

/-- The local pure tensor with the zero section of the first factor vanishes. -/
lemma tensorTotalSectionAt_zero_left
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (U : X.C) (t r c : ℤ)
    (h : t + r = c) (b : (B.X r).val.obj (op U)) :
    tensorTotalSectionAt X A B U t r c h 0 b = 0 :=
  (congrArg ((tensorTotalTmulMap X A B t r c h).app (op U))
      (TensorProduct.zero_tmul (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
        ((A.X t).val.obj (op U) : Type u) b)).trans (map_zero _)

/-- A section of the structure sheaf complex in a nonzero degree vanishes. -/
lemma structureSheafComplex_section_eq_zero (U : X.C) {r : ℤ} (hr : r ≠ 0)
    (b : ((structureSheafComplex X).X r).val.obj (op U)) : b = 0 := by
  have hz : IsZero ((structureSheafComplex X).X r) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ r hr
  have hval : (0 : ((structureSheafComplex X).X r) ⟶ ((structureSheafComplex X).X r)).val
      = 0 := rfl
  simpa [hval] using congrArg (fun φ : ((structureSheafComplex X).X r) ⟶ _ ↦ φ.val.app (op U) b)
    (hz.eq_of_src (𝟙 ((structureSheafComplex X).X r)) 0)

/-- Evaluating at the unit section undoes the identification of a complex with the internal Hom
complex out of the structure sheaf. -/
lemma applyHomSection_structureSheafHomIso_inv
    (W : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (n : ℤ)
    (w : (W.X n).val.obj (op U)) :
    applyHomSection X (sheafHomComplex X (structureSheafComplex X) W) U n 0 n (zero_add n)
        (((structureSheafHomIso X W).inv.f n).val.app (op U) w) (structureSheafOne X U) = w :=
  congrArg (fun φ : W ⟶ W ↦ (φ.f n).val.app (op U) w) (structureSheafHomIso X W).inv_hom_id

/-! ## The collapse is inverse to the pure tensor with the unit section -/

section UnitIso

variable (W : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The collapse sends the pure tensor `β ⊗ b` to the evaluation at `b` of the section of
`SheafHom(O[0], W)` named by `β`. -/
private lemma tensorTotalStructureSheafCollapse_apply (U : X.C) (t r c : ℤ) (h : t + r = c)
    (β : (W.X t).val.obj (op U))
    (b : ((structureSheafComplex X).X r).val.obj (op U)) :
    ((tensorTotalStructureSheafCollapse X W).f c).val.app (op U)
        (tensorTotalSectionAt X W (structureSheafComplex X) U t r c h β b) =
      applyHomSection X (sheafHomComplex X (structureSheafComplex X) W) U t r c (by omega)
        (((structureSheafHomIso X W).inv.f t).val.app (op U) β) b := by
  show ((structureSheafHomEvaluation X W).f c).val.app (op U)
      (((compositionMap X (structureSheafComplex X) (structureSheafComplex X) W).f c).val.app
        (op U)
        (((tensorTotalMap X (structureSheafHomIso X W).inv
            (structureSheafHomIso X (structureSheafComplex X)).inv).f c).val.app (op U)
          (tensorTotalSectionAt X W (structureSheafComplex X) U t r c h β b))) = _
  rw [tensorTotalMap_tensorTotalSectionAt, compositionMap_tensorTotalSectionAt,
    structureSheafHomEvaluation_apply,
    compositionSection_apply X U t r c 0 r c h (zero_add r) (by omega),
    applyHomSection_structureSheafHomIso_inv]

/-- Evaluation at the zero section of the source vanishes. -/
private lemma applyHomSection_zero_right
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L)
    (U : X.C) (n p q : ℤ) (hpq : p + n = q) (f : (H.obj.X n).val.obj (op U)) :
    applyHomSection X H U n p q hpq f 0 = 0 :=
  map_zero _

/-- **The unit section generates the degree-zero sections of the structure sheaf complex**: a
section is the multiple of the unit section by itself, read as a section of the structure
sheaf. -/
private lemma structureSheafOne_smul (U : X.C)
    (b : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) :
    (b • structureSheafOne X U : ((structureSheafComplex X).X 0).val.obj (op U)) =
      show ((structureSheafComplex X).X 0).val.obj (op U) from b := by
  show b * 1 = b
  exact mul_one b

/-- **The collapse undoes the pure tensor with the unit section, on local pure tensors.** -/
private lemma tensorTotalStructureSheafCollapse_unit_apply (U : X.C) (t r c : ℤ) (h : t + r = c)
    (β : (W.X t).val.obj (op U))
    (b : ((structureSheafComplex X).X r).val.obj (op U)) :
    ((tensorTotalStructureSheafUnit X W).f c).val.app (op U)
        (((tensorTotalStructureSheafCollapse X W).f c).val.app (op U)
          (tensorTotalSectionAt X W (structureSheafComplex X) U t r c h β b)) =
      tensorTotalSectionAt X W (structureSheafComplex X) U t r c h β b := by
  rw [tensorTotalStructureSheafCollapse_apply, tensorTotalStructureSheafUnit_apply]
  by_cases hr : r = 0
  · subst hr
    obtain rfl : c = t := by omega
    -- `t` has been eliminated in favour of `c`.
    obtain ⟨s, rfl⟩ : ∃ s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U),
        b = s • structureSheafOne X U := ⟨_, (structureSheafOne_smul X U _).symm⟩
    rw [applyHomSection_smul_right, applyHomSection_structureSheafHomIso_inv,
      tensorTotalSectionAt_smul_left, tensorTotalSectionAt_smul_right]
  · rw [structureSheafComplex_section_eq_zero X U hr b, applyHomSection_zero_right,
      tensorTotalSectionAt_zero_left, tensorTotalSectionAt_zero_right]

/-- **The pure tensor with the unit section followed by the collapse is the identity.** -/
lemma tensorTotalStructureSheafUnit_collapse :
    tensorTotalStructureSheafUnit X W ≫ tensorTotalStructureSheafCollapse X W = 𝟙 W := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext (LinearMap.ext fun w ↦ ?_))
  show ((tensorTotalStructureSheafCollapse X W).f n).val.app U
      (((tensorTotalStructureSheafUnit X W).f n).val.app U w) = w
  rw [tensorTotalStructureSheafUnit_apply, tensorTotalStructureSheafCollapse_apply]
  exact applyHomSection_structureSheafHomIso_inv X W U.unop n w

/-- **The collapse followed by the pure tensor with the unit section is the identity.** -/
lemma tensorTotalStructureSheafCollapse_unit :
    tensorTotalStructureSheafCollapse X W ≫ tensorTotalStructureSheafUnit X W =
      𝟙 (tensorTotal X W (structureSheafComplex X)) := by
  refine tensorTotal_hom_ext X fun U t r β b ↦ ?_
  exact tensorTotalStructureSheafCollapse_unit_apply X W U t r (t + r) rfl β b

/-- **The total tensor product against the structure sheaf in degree zero is trivial.** The
pure tensor with the unit section is an isomorphism `W ≅ Tot(W ⊗_O O[0])`, with inverse the
collapse. -/
def tensorTotalUnitIso : W ≅ tensorTotal X W (structureSheafComplex X) where
  hom := tensorTotalStructureSheafUnit X W
  inv := tensorTotalStructureSheafCollapse X W
  hom_inv_id := tensorTotalStructureSheafUnit_collapse X W
  inv_hom_id := tensorTotalStructureSheafCollapse_unit X W

end UnitIso

/-! ## The unit law for the composition morphism of internal Hom complexes -/

section ChainLevel

variable {L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- `applyHomSection_structureSheafHomIso_inv` with the section named through a morphism into
the complex, which is the form the unit law produces it in. -/
private lemma applyHomSection_structureSheafHomIso_inv_comp
    (g : structureSheafComplex X ⟶ L) (U : X.C) :
    applyHomSection X (sheafHomComplex X (structureSheafComplex X) L) U 0 0 0 (by omega)
        (((g ≫ (structureSheafHomIso X L).inv).f 0).val.app (op U) (structureSheafOne X U))
        (structureSheafOne X U) =
      (g.f 0).val.app (op U) (structureSheafOne X U) :=
  applyHomSection_structureSheafHomIso_inv X L U 0 _

/-- **The unit law for the composition morphism of internal Hom complexes of Stacks 0A91.**
For complexes `L`, `M` and a morphism `g : O[0] ⟶ L`, the composite

`SheafHom(L, M) ⟶ Tot(SheafHom(L, M) ⊗_O O[0]) ⟶ Tot(SheafHom(L, M) ⊗_O SheafHom(O[0], L))
  ⟶ SheafHom(O[0], M)`

— the pure tensor with the unit section, then the section of `SheafHom(O[0], L)` named by `g`,
then the composition morphism — is `SheafHom(g, M)`, precomposition with `g`.

At `L = O[0]` and `g = 𝟙` the middle arrow carries the unit section to the *identity* section of
`SheafHom(O[0], O[0])`, and the statement is that composing with the identity is the identity:
this is the right unit law for Stacks 0A91. Nothing in the Stacks Project asserts it; see the
module docstring. -/
theorem compositionMap_structureSheafUnit (g : structureSheafComplex X ⟶ L) :
    tensorTotalStructureSheafUnit X (sheafHomComplex X L M).obj ≫
        tensorTotalMap X (𝟙 (sheafHomComplex X L M).obj)
          (g ≫ (structureSheafHomIso X L).inv) ≫
        compositionMap X (structureSheafComplex X) L M =
      homMap X g (𝟙 M) := by
  rw [← cancel_mono (structureSheafHomEvaluation X M)]
  refine HomologicalComplex.hom_ext _ _ fun n ↦ SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext (LinearMap.ext fun β ↦ ?_))
  show ((structureSheafHomEvaluation X M).f n).val.app U
      (((compositionMap X (structureSheafComplex X) L M).f n).val.app U
        (((tensorTotalMap X (𝟙 (sheafHomComplex X L M).obj)
            (g ≫ (structureSheafHomIso X L).inv)).f n).val.app U
          (((tensorTotalStructureSheafUnit X (sheafHomComplex X L M).obj).f n).val.app U β))) =
    ((structureSheafHomEvaluation X M).f n).val.app U
      (((homMap X g (𝟙 M)).f n).val.app U β)
  rw [tensorTotalStructureSheafUnit_apply, tensorTotalMap_tensorTotalSectionAt,
    compositionMap_tensorTotalSectionAt, structureSheafHomEvaluation_apply,
    structureSheafHomEvaluation_apply,
    compositionSection_apply X U.unop n 0 n 0 0 n (add_zero n) rfl (zero_add n),
    applyHomSection_structureSheafHomIso_inv_comp,
    applyHomSection_homMap X g (𝟙 M) U.unop n 0 n (zero_add n) β _]
  rfl

/-- **The composition morphism out of the structure sheaf, computed.** It is the collapse of
the total tensor product against the structure sheaf followed by precomposition with `g`. This
is `compositionMap_structureSheafUnit` with the isomorphism
`AlgebraicGeometry.RingedSite.tensorTotalUnitIso` moved to the other side; in this form the
right-hand side is manifestly a quasi-isomorphism whenever `SheafHom(g, M)` is one. -/
theorem compositionMap_structureSheafSource_eq (g : structureSheafComplex X ⟶ L) :
    tensorTotalMap X (𝟙 (sheafHomComplex X L M).obj)
          (g ≫ (structureSheafHomIso X L).inv) ≫
        compositionMap X (structureSheafComplex X) L M =
      tensorTotalStructureSheafCollapse X (sheafHomComplex X L M).obj ≫ homMap X g (𝟙 M) := by
  rw [← compositionMap_structureSheafUnit X g, ← Category.assoc,
    tensorTotalStructureSheafCollapse_unit, Category.id_comp]

end ChainLevel

/-! ## The unit law for derived composition -/

section Derived

variable
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ N, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj N).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))]
  (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} X)
  (Hd : DerivedInternalHom.{u, d} X)

/-- **The unit law for the composition morphism of Stacks 0A98 at a structure-sheaf source.**
For K-injective complexes `J` and `I` and a morphism `g : O[0] ⟶ J`, derived composition

`RSheafHom(QJ, QI) ⊗^L_O RSheafHom(O, QJ) ⟶ RSheafHom(O, QI)`,

precomposed in its right tensor factor with the section of `RSheafHom(O, QJ)` named by `g`, is
the collapse of the total tensor product against the structure sheaf followed by precomposition
with `g`. This is the chain-level unit law `compositionMap_structureSheafUnit` transported along
the K-injective model comparison of `Hd`, exactly as the `comparison` field of
`AlgebraicGeometry.RingedSite.DerivedSheafHomComposition` does.

This file attaches no `@[stacks]` attribute: Stacks 0A98 asserts only the existence of the
composition morphism, and no tag of the Stacks Project asserts unitality. See the module
docstring. -/
theorem derivedSheafHomComposition_structureSheafSource
    (J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsKInjective] [I.IsKInjective]
    (g : structureSheafComplex X ⟶ J) :
    (T.tensor.obj ((Hd.hom.obj (op (DerivedCategory.Q.obj J))).obj
            (DerivedCategory.Q.obj I))).map
          (DerivedCategory.Q.map (g ≫ (structureSheafHomIso X J).inv) ≫
            (Hd.homComparison (structureSheafComplex X) J).inv) ≫
        derivedSheafHomComposition X T Hd (DerivedCategory.Q.obj (structureSheafComplex X))
          (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj I) ≫
        (Hd.homComparison (structureSheafComplex X) I).hom =
      (derivedEvaluationSourceComparison X T Hd (structureSheafComplex X) J I
          (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
        DerivedCategory.Q.map
          (tensorTotalStructureSheafCollapse X (sheafHomComplex X J I).obj ≫
            homMap X g (𝟙 I)) := by
  rw [derivedSheafHomComposition_kFlatModel X T Hd (structureSheafComplex X) J I
      (structureSheafComplex X) (Stacks.SheafOfModules.isKFlat_single_unit X.O)
      (g ≫ (structureSheafHomIso X J).inv),
    ← CategoryTheory.Functor.map_comp, compositionMap_structureSheafSource_eq]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ N, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj N).Additive]
  [∀ (K₁ K₂ : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
  HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (ComplexShape.up ℤ)] in
/-- Precomposition with a quasi-isomorphism out of the structure sheaf, on internal Hom
complexes into a K-injective complex, becomes invertible in the derived category. -/
private lemma isIso_Q_map_homMap_structureSheaf
    (J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsKInjective] [I.IsKInjective]
    (g : structureSheafComplex X ⟶ J) (hg : IsIso (DerivedCategory.Q.map g)) :
    IsIso (DerivedCategory.Q.map (homMap X g (𝟙 I))) := by
  have hq : QuasiIso g := (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).mp hg
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr (homMap_quasiIso X (𝟙 I) g)

/-- **Derived composition at a structure-sheaf source and intermediate object is invertible, on
K-injective models.** -/
lemma isIso_derivedSheafHomComposition_structureSheafModels
    (J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsKInjective] [I.IsKInjective]
    (g : structureSheafComplex X ⟶ J) (hg : IsIso (DerivedCategory.Q.map g)) :
    IsIso (derivedSheafHomComposition X T Hd (DerivedCategory.Q.obj (structureSheafComplex X))
      (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj I)) := by
  have hg' : IsIso (DerivedCategory.Q.map (g ≫ (structureSheafHomIso X J).inv)) := by
    rw [CategoryTheory.Functor.map_comp]
    have := hg
    have : IsIso (DerivedCategory.Q.map (structureSheafHomIso X J).inv) :=
      Functor.map_isIso _ _
    infer_instance
  have hpre : IsIso ((T.tensor.obj ((Hd.hom.obj (op (DerivedCategory.Q.obj J))).obj
      (DerivedCategory.Q.obj I))).map
        (DerivedCategory.Q.map (g ≫ (structureSheafHomIso X J).inv) ≫
          (Hd.homComparison (structureSheafComplex X) J).inv)) := by
    have : IsIso (DerivedCategory.Q.map (g ≫ (structureSheafHomIso X J).inv) ≫
        (Hd.homComparison (structureSheafComplex X) J).inv) := by
      have := hg'
      infer_instance
    exact Functor.map_isIso _ _
  have hrhs : IsIso ((derivedEvaluationSourceComparison X T Hd (structureSheafComplex X) J I
        (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
      DerivedCategory.Q.map
        (tensorTotalStructureSheafCollapse X (sheafHomComplex X J I).obj ≫
          homMap X g (𝟙 I))) := by
    have h₁ : IsIso (DerivedCategory.Q.map
        (tensorTotalStructureSheafCollapse X (sheafHomComplex X J I).obj)) := by
      have : IsIso (tensorTotalStructureSheafCollapse X (sheafHomComplex X J I).obj) :=
        (tensorTotalUnitIso X (sheafHomComplex X J I).obj).isIso_inv
      exact Functor.map_isIso _ _
    have h₂ := isIso_Q_map_homMap_structureSheaf X J I g hg
    rw [CategoryTheory.Functor.map_comp]
    infer_instance
  have key := derivedSheafHomComposition_structureSheafSource X T Hd J I g
  have hcomp : IsIso
      ((T.tensor.obj ((Hd.hom.obj (op (DerivedCategory.Q.obj J))).obj
            (DerivedCategory.Q.obj I))).map
          (DerivedCategory.Q.map (g ≫ (structureSheafHomIso X J).inv) ≫
            (Hd.homComparison (structureSheafComplex X) J).inv) ≫
        derivedSheafHomComposition X T Hd (DerivedCategory.Q.obj (structureSheafComplex X))
          (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj I) ≫
        (Hd.homComparison (structureSheafComplex X) I).hom) := by
    rw [key]; exact hrhs
  rw [isIso_comp_left_iff, isIso_comp_right_iff] at hcomp
  exact hcomp

/-- Invertibility of derived composition is transported along an isomorphism of the intermediate
object, by the dinaturality of Stacks 0A98. -/
private lemma isIso_derivedSheafHomComposition_of_isoMiddle
    {K L L' M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (l : L ⟶ L') [IsIso l]
    (h : IsIso (derivedSheafHomComposition X T Hd K L' M)) :
    IsIso (derivedSheafHomComposition X T Hd K L M) := by
  have h₂ : IsIso ((T.tensor.map ((Hd.hom.map l.op).app M)).app
      ((Hd.hom.obj (op K)).obj L)) := inferInstance
  have hL : IsIso ((T.tensor.obj ((Hd.hom.obj (op L')).obj M)).map
        ((Hd.hom.obj (op K)).map l) ≫
      (derivedSheafHomCompositionConstruction X T Hd).comp K L' M) := by
    have : IsIso ((derivedSheafHomCompositionConstruction X T Hd).comp K L' M) := h
    infer_instance
  rw [(derivedSheafHomCompositionConstruction X T Hd).dinatural_middle l,
    isIso_comp_left_iff] at hL
  exact hL

/-- Invertibility of derived composition is transported along an isomorphism of the target
object, by the covariant naturality of Stacks 0A98. -/
private lemma isIso_derivedSheafHomComposition_of_isoTarget
    {K L M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : M ⟶ M') [IsIso m]
    (h : IsIso (derivedSheafHomComposition X T Hd K L M)) :
    IsIso (derivedSheafHomComposition X T Hd K L M') := by
  have h₂ : IsIso ((T.tensor.map ((Hd.hom.obj (op L)).map m)).app
      ((Hd.hom.obj (op K)).obj L)) := inferInstance
  have hL : IsIso ((derivedSheafHomCompositionConstruction X T Hd).comp K L M ≫
      (Hd.hom.obj (op K)).map m) := by
    have : IsIso ((derivedSheafHomCompositionConstruction X T Hd).comp K L M) := h
    infer_instance
  rw [(derivedSheafHomCompositionConstruction X T Hd).natural_target m,
    isIso_comp_left_iff] at hL
  exact hL

/-- **The unit law for Stacks 0A98: derived composition at a structure-sheaf source and
intermediate object is invertible.** The composition morphism

`RSheafHom(O, M) ⊗^L_O RSheafHom(O, O) ⟶ RSheafHom(O, M)`

is an isomorphism for every object `M` of `D(O)`. Both `RSheafHom(O, -)` and the second tensor
factor are trivial, and the content is that the composition morphism is, through those
identifications, the unit constraint rather than an arbitrary endomorphism: that is the unit law
`compositionMap_structureSheafUnit`, transported along the K-injective and K-flat models by
`derivedSheafHomComposition_structureSheafSource` and then along the chosen representatives by
the dinaturality and the covariant naturality of Stacks 0A98. -/
theorem isIso_derivedSheafHomComposition_structureSheaf
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (derivedSheafHomComposition X T Hd (DerivedCategory.Q.obj (structureSheafComplex X))
      (DerivedCategory.Q.obj (structureSheafComplex X)) M) := by
  obtain ⟨g, hgeq⟩ := exists_Q_map_eq_of_isKInjective X
    (A := structureSheafComplex X)
    (I := kInjectiveModel X (DerivedCategory.Q.obj (structureSheafComplex X)))
    (kInjectiveModelIso X (DerivedCategory.Q.obj (structureSheafComplex X))).inv
  have hg : IsIso (DerivedCategory.Q.map g) := by
    rw [hgeq]
    infer_instance
  have h0 := isIso_derivedSheafHomComposition_structureSheafModels X T Hd
    (kInjectiveModel X (DerivedCategory.Q.obj (structureSheafComplex X)))
    (kInjectiveModel X M) g hg
  have hmid := isIso_derivedSheafHomComposition_of_isoMiddle X T Hd
    (kInjectiveModelIso X (DerivedCategory.Q.obj (structureSheafComplex X))).inv h0
  exact isIso_derivedSheafHomComposition_of_isoTarget X T Hd
    (kInjectiveModelIso X M).hom hmid

end Derived

/-! ## The base case of the dévissage of Stacks 08JJ -/

section TensorDual

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-- **The canonical map of Stacks 08JD is invertible at the structure sheaf.** For every object
`M` of `D(O)` the map

`Φ_O : M ⊗^L_O O^∨ ⟶ RSheafHom(O, M)`

of `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom` is an isomorphism. It is by
definition the composition morphism of Stacks 0A98 at intermediate object the structure sheaf,
precomposed with the identification of `M` with `RSheafHom(O, M)`, so this is the unit law
`isIso_derivedSheafHomComposition_structureSheaf` with an isomorphism in front.

**This is the base case of the dévissage of Stacks 08JJ** carried out in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualDevissage`, whose
section "What this file does not contain" records that the only object at which invertibility
was established there is the zero object, for want of a unitality statement for Stacks 0A98. -/
theorem isIso_derivedTensorDualToSheafHom_structureSheaf
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (derivedTensorDualToSheafHom X T (derivedStructureSheaf X) M) := by
  have hcomp : IsIso (derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X)
      (derivedStructureSheaf X) (derivedStructureSheaf X) M) :=
    isIso_derivedSheafHomComposition_structureSheaf X T (derivedInternalHomOfBifunctor X) M
  have hpre : IsIso ((T.tensor.map (derivedStructureSheafHomIso X M).inv).app
      (derivedDual X (derivedStructureSheaf X))) := by
    have : IsIso (T.tensor.map (derivedStructureSheafHomIso X M).inv) := Functor.map_isIso _ _
    infer_instance
  show IsIso ((T.tensor.map (derivedStructureSheafHomIso X M).inv).app
      (derivedDual X (derivedStructureSheaf X)) ≫
    derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X)
      (derivedStructureSheaf X) (derivedStructureSheaf X) M)
  infer_instance

/-- **The canonical map of Stacks 08JD is invertible at every object isomorphic to the structure
sheaf.** This is the previous statement together with the closure of the class under isomorphism
of `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_iso`; it is the form in
which the dévissage of Stacks 08JJ consumes the base case. -/
theorem isIso_derivedTensorDualToSheafHom_of_iso_structureSheaf
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : L ≅ derivedStructureSheaf X)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (derivedTensorDualToSheafHom X T L M) :=
  isIso_derivedTensorDualToSheafHom_of_iso X T e M
    (isIso_derivedTensorDualToSheafHom_structureSheaf X T M)

end TensorDual

end AlgebraicGeometry.RingedSite

end
