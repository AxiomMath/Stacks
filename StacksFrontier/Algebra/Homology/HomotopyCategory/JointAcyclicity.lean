module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseShortExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Acyclicity detected by a family of exact functors

`Stacks.Adequate.plus_subcategoryAcyclic_eq_inverseImage` reads acyclicity of a complex off its
image under **one** exact functor that reflects isomorphisms. A functor category has no such
single functor: the evaluations at the objects of the index category reflect isomorphisms only
*jointly*, which is `CategoryTheory.JointlyReflectIsomorphisms`. This module supplies the
acyclicity statement over a jointly reflecting family, and specialises it to the evaluations of a
presheaf of modules.

That specialisation is what reads acyclicity of a complex of module-valued functors on all
algebras of a ring as a condition over each single algebra, which is the form in which
[Stacks, Tag 06ZR] compares it with universal acyclicity on the geometric side.

## Main results

* `Stacks.Homology.isZero_of_forall_isZero_map` — a jointly reflecting family of additive
  functors reflects zero objects.
* `Stacks.Homology.acyclic_iff_forall_map` — a cochain complex is acyclic exactly when all its
  images under a jointly reflecting family of exact functors are.
* `Stacks.Homology.plus_acyclic_iff_forall_map` — the same in the bounded below homotopy
  category.
* `Stacks.Homology.plus_acyclic_presheafOfModules_iff` — **a complex of presheaves of modules is
  acyclic exactly when its complex of sections over every object is acyclic.**

## Implementation notes

The family is indexed by a type and its targets are allowed to vary with the index, since the
evaluations of a presheaf of modules land in the module categories of varying rings. The
reflection hypothesis is taken as an explicit `CategoryTheory.JointlyReflectIsomorphisms`
argument rather than an instance, there being no reason for instance search to find it.

The proofs are those of `Stacks.Adequate.isZero_of_isZero_map` and
`Stacks.Adequate.acyclic_map_iff` with the single functor replaced by the family and
`CategoryTheory.isIso_of_reflects_iso` by
`CategoryTheory.JointlyReflectIsomorphisms.isIso_iff`.

## References

* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ v₂ u₂ w

namespace Stacks.Homology

section Joint

variable {C : Type u₁} [Category.{v₁} C] {I : Type w} {D : I → Type u₂}
  [∀ i, Category.{v₂} (D i)]

/-- **A jointly reflecting family of additive functors reflects zero objects.** If every `F i X`
is zero then every `F i` carries the zero endomorphism of `X` to an isomorphism, so the zero
endomorphism of `X` is one. -/
public theorem isZero_of_forall_isZero_map [Preadditive C] [∀ i, Preadditive (D i)]
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).Additive] (hF : JointlyReflectIsomorphisms F) {X : C}
    (h : ∀ i, IsZero ((F i).obj X)) : IsZero X := by
  have h₁ : ∀ i, IsIso ((F i).map (0 : X ⟶ X)) := fun i => by
    rw [(F i).map_zero, ← (IsZero.iff_id_eq_zero _).mp (h i)]
    infer_instance
  have h₂ := (hF.isIso_iff (0 : X ⟶ X)).2 h₁
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : X ⟶ X), zero_comp]

/-- **A jointly reflecting family of exact functors detects acyclicity.** Homology commutes with
each `F i` by `CategoryTheory.ShortComplex.mapHomologyIso`, and the family reflects the vanishing
of a homology object by `Stacks.Homology.isZero_of_forall_isZero_map`. -/
public theorem acyclic_iff_forall_map [Abelian C] [∀ i, Abelian (D i)]
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).Additive] [∀ i, (F i).PreservesHomology]
    (hF : JointlyReflectIsomorphisms F) (K : CochainComplex C ℤ) :
    K.Acyclic ↔
      ∀ i, (((F i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  constructor
  · intro hK i n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((F i).map_isZero
        ((HomologicalComplex.exactAt_iff_isZero_homology K n).mp (hK n))).of_iso
      ((K.sc n).mapHomologyIso (F i))
  · intro h n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact isZero_of_forall_isZero_map F hF fun i =>
      ((HomologicalComplex.exactAt_iff_isZero_homology _ n).mp (h i n)).of_iso
        ((K.sc n).mapHomologyIso (F i)).symm

/-- A bounded below object of the homotopy category given by a cochain complex `L` is acyclic
exactly when `L` is. -/
private theorem subcategoryAcyclic_iff_acyclic {A : Type*} [Category A] [Abelian A]
    (K : HomotopyCategory.Plus A) (L : CochainComplex A ℤ)
    (h : K.obj = (HomotopyCategory.quotient A _).obj L) :
    HomotopyCategory.Plus.subcategoryAcyclic A K ↔ L.Acyclic := by
  change HomotopyCategory.subcategoryAcyclic A K.obj ↔ _
  rw [h, HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]

/-- `Stacks.Homology.acyclic_iff_forall_map` in the bounded below homotopy category. -/
public theorem plus_acyclic_iff_forall_map [Abelian C] [∀ i, Abelian (D i)]
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).Additive] [∀ i, (F i).PreservesHomology]
    (hF : JointlyReflectIsomorphisms F) (K : HomotopyCategory.Plus C) :
    HomotopyCategory.Plus.subcategoryAcyclic C K ↔
      ∀ i, HomotopyCategory.Plus.subcategoryAcyclic (D i)
        ((F i).mapHomotopyCategoryPlus.obj K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective K
  rw [subcategoryAcyclic_iff_acyclic _ K.obj rfl, acyclic_iff_forall_map F hF K.obj]
  exact forall_congr' fun i =>
    (subcategoryAcyclic_iff_acyclic _ (((F i).mapHomologicalComplex _).obj K.obj) rfl).symm

end Joint

/-! ### The evaluations of a presheaf of modules -/

section Presheaf

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u₂})

/-- Evaluation of a presheaf of modules preserves homology, being exact: it preserves finite
limits and finite colimits, by Mathlib's
`CategoryTheory.PresheafOfModules.evaluation_preservesFiniteLimits` and
`CategoryTheory.PresheafOfModules.evaluation_preservesFiniteColimits`. -/
public instance preservesHomology_presheafOfModules_evaluation (X : Cᵒᵖ) :
    (PresheafOfModules.evaluation.{u₂} R X).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- **A complex of presheaves of modules is acyclic exactly when its complex of sections over
every object of the index category is acyclic.** The evaluations are exact and jointly reflect
isomorphisms, being jointly faithful (`PresheafOfModules.jointlyFaithful_evaluation`) into a
balanced category (`CategoryTheory.JointlyFaithful.jointlyReflectsIsomorphisms`), so
`Stacks.Homology.plus_acyclic_iff_forall_map` applies to them. -/
@[sga "4 V 2.3.1" "more general"]
public theorem plus_acyclic_presheafOfModules_iff
    (K : HomotopyCategory.Plus (PresheafOfModules.{u₂} R)) :
    HomotopyCategory.Plus.subcategoryAcyclic (PresheafOfModules.{u₂} R) K ↔
      ∀ X : Cᵒᵖ, HomotopyCategory.Plus.subcategoryAcyclic (ModuleCat.{u₂} ↥(R.obj X))
        ((PresheafOfModules.evaluation.{u₂} R X).mapHomotopyCategoryPlus.obj K) :=
  plus_acyclic_iff_forall_map (fun X : Cᵒᵖ => PresheafOfModules.evaluation.{u₂} R X)
    PresheafOfModules.jointlyFaithful_evaluation.jointlyReflectsIsomorphisms K

end Presheaf

end Stacks.Homology

end
