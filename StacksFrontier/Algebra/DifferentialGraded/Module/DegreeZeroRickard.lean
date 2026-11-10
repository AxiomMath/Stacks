module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroDerivedStructure
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceCompactGenerator
public import StacksFrontier.Homology.Perfect.Characterizing

/-! # Rickard's criterion for ordinary algebras

Let `R` be a commutative ring and let `A` and `B` be `R`-algebras, not assumed commutative.
[Stacks, Tag 09SC] compares the existence of an `R`-linear triangulated equivalence
`D(A) → D(B)` with the existence of an object `P` of `D(B)` which is perfect, which detects
vanishing, and whose graded endomorphism algebra is `A` in degree zero and vanishes elsewhere.

This file proves the implication `(1) ⇒ (2)`, by reading both derived categories in the
differential graded world and applying [Stacks, Tag 09S8] there.

## Main results

* `DifferentialGradedModule.exists_isPerfect_and_detectsZero_of_derivedEquivalence`:
  **Stacks 09SC, the implication (1) ⇒ (2).**

## Implementation notes

*Which derived category `D(A)` is.* Throughout Chapter 22 a differential graded module is a
*right* module, so `D(A)` for an ordinary algebra `A` is the derived category of right
`A`-modules, which is `DerivedCategory (ModuleCat Aᵐᵒᵖ)`. That reading is what makes clause
(2)(c) say what the source says: for right modules `End_{D(B)}(B) = B`, whereas for left modules
it would be `Bᵐᵒᵖ`. Accordingly `A` itself — and not its opposite — is the degree-zero
differential graded algebra used on the `D(A)` side: the comparison
`DifferentialGradedModule.degreeZeroDerivedEquivalence` for the identification
`DifferentialGradedAlgebra.instIsOppositeAlgebraOp` of `A` with the opposite of `Aᵐᵒᵖ` reads
`D(degreeZero R A, d) ≌ D(Mod-A)`, and `(degreeZero R A).A` is `A`.

*Universes.* The base ring, the two algebras and the modules all live in a single universe `u`,
which is the encoding of the differential graded chapter (Tag 09JJ) and of
`DifferentialGradedAlgebra.degreeZero`; compactness is taken with respect to coproducts indexed
by `Type u`, matching Tags 09R9, 09S7 and 09S8. The two derived categories are the standard
models, `HasDerivedCategory.standard`, which is also the model Tag 07LT is stated at.

*What is assumed of the equivalence, against the source's condition (1).* The source's (1) is an
`R`-linear equivalence of triangulated categories. What is assumed below is additivity,
`R`-linearity and commutation with the translation; `CategoryTheory.Functor.IsTriangulated` is
not used, and it implies `CategoryTheory.Functor.Additive`. This is the same reading of (1) as in
the library's `(1) ⇒ (2)` of Tag 09S8,
`DifferentialGradedModule.exists_isCompactObject_and_isWeakGenerator_of_derivedEquivalence`.

*Clause (2)(a).* "Representable by a finite complex of finite projective `B`-modules" is
`StacksDraft.Perfect.IsPerfect`, and it is obtained from compactness in `D(Mod-B)` by Tag 07LT,
`StacksDraft.Perfect.isPerfect_iff_isCompactObject`, which holds over an arbitrary ring. The
route through [Stacks, Tag 09RB] that the source's proof takes is *not* used: this project has
machine-checked that the literal implication (1) ⇒ (2) of Tag 09RB is false.

*Vanishing of an `Ext` group* is `Subsingleton` of the corresponding shifted `Hom` group, and
vanishing of an object is `CategoryTheory.Limits.IsZero`; Tag 09S8 spells the same conditions as
"every morphism is zero", and the two are interchanged by
`DifferentialGradedModule.subsingleton_hom_iff_forall_eq_zero`.

*The converse is not proved here.* Deducing (2) ⇒ (1) from Tag 09S8's converse needs the
degree-zero comparison to be *triangulated*, not merely shift-commuting, because the equivalence
Tag 09S8 produces has to be conjugated into the ordinary derived categories and clause (1) asks
for a triangulated equivalence. That exactness is
`DifferentialGradedModule.degreeZeroDerivedEquivalence_functor_exact`, and the converse itself is
`DifferentialGradedModule.exists_derivedEquivalence_of_isPerfect_and_detectsZero`, in
`StacksFrontier/Algebra/DifferentialGraded/Module/DegreeZeroRickardConverse.lean`, which also
packages the equivalence of (1) and (2) as
`DifferentialGradedModule.derivedEquivalence_iff_exists_isPerfect_and_detectsZero`.

## References

* [Stacks Project, Tag 09SC](https://stacks.math.columbia.edu/tag/09SC), the lemma whose first
  implication is proved here.
* [Stacks Project, Tag 09S8](https://stacks.math.columbia.edu/tag/09S8), Rickard's criterion for
  differential graded algebras, and [Tag 07LT](https://stacks.math.columbia.edu/tag/07LT), the
  identification of perfect with compact objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ModuleCat.Algebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

/-- A `Hom` group of a preadditive category is a singleton exactly when all its elements are
zero. -/
theorem subsingleton_hom_iff_forall_eq_zero {C : Type*} [Category* C] [Preadditive C]
    (X Y : C) : Subsingleton (X ⟶ Y) ↔ ∀ f : X ⟶ Y, f = 0 :=
  ⟨fun _ f => Subsingleton.elim f 0, fun h => ⟨fun f g => (h f).trans (h g).symm⟩⟩

/-- A shift-commuting equivalence identifies the shifted `Hom` groups: `Hom(P, K[i])` is a
singleton exactly when `Hom(E P, (E K)[i])` is. -/
theorem subsingleton_shiftHom_iff_obj {C : Type*} [Category* C] {D : Type*} [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (E : C ≌ D) [E.functor.CommShift ℤ] (P K : C) (i : ℤ) :
    Subsingleton (P ⟶ K⟦i⟧) ↔
      Subsingleton (E.functor.obj P ⟶ (E.functor.obj K)⟦i⟧) :=
  (E.fullyFaithfulFunctor.homEquiv.trans
    (((E.functor.commShiftIso i).app K).homToEquiv)).subsingleton_congr

/-- A shift-commuting equivalence transports the property of detecting vanishing: an object `P`
detects vanishing in `C` exactly when its image detects vanishing in `D`. -/
theorem detectsZero_iff_obj {C : Type*} [Category* C] {D : Type*} [Category* D]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ] (E : C ≌ D) [E.functor.CommShift ℤ] (P : C) :
    (∀ K : C, (∀ i : ℤ, Subsingleton (P ⟶ K⟦i⟧)) → IsZero K) ↔
      (∀ K : D, (∀ i : ℤ, Subsingleton (E.functor.obj P ⟶ K⟦i⟧)) → IsZero K) := by
  refine ⟨fun h K hK => ?_, fun h K hK => ?_⟩
  · have h' : IsZero (E.inverse.obj K) := h _ fun i =>
      (subsingleton_shiftHom_iff_obj E P _ i).mpr
        ((((CategoryTheory.shiftFunctor D i).mapIso (E.counitIso.app K)).homToEquiv
          (Z := E.functor.obj P)).subsingleton_congr.mpr (hK i))
    exact (E.functor.map_isZero h').of_iso (E.counitIso.app K).symm
  · exact IsZero.of_full_of_faithful_of_isZero E.functor K
      (h _ fun i => (subsingleton_shiftHom_iff_obj E P K i).mp (hK i))

section Rickard

variable {R : Type u} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  {B : Type u} [Ring B] [Algebra R B]

/-- The homogeneous components of `degreeZero R A` vanish away from degree zero: the algebra is
concentrated in degree zero, which is Tag 09S8's hypothesis `A = H^0(A)`. -/
theorem degreeZero_grading_eq_bot (i : ℤ) (hi : i ≠ 0) : (degreeZero R A).grading i = ⊥ :=
  degreeZeroGrading_eq_bot R A hi

/-- **Stacks 09SC, the implication (1) ⇒ (2).** Let `R` be a commutative ring and let `A` and `B`
be `R`-algebras, not assumed commutative. Let

`E : D(Mod-A) ≌ D(Mod-B)`

be an additive, `R`-linear, shift-commuting equivalence of the derived categories of right
modules. Then there is an object `P` of `D(Mod-B)` such that

* `P` can be represented by a finite complex of finite projective right `B`-modules, that is, `P`
  is perfect;
* an object `K` of `D(Mod-B)` with `Ext^i_B(P, K) = 0` for every `i : ℤ` is zero;
* `Ext^i_B(P, P) = 0` for `i ≠ 0`, and the endomorphism `R`-algebra of `P` is `A`.

The object `P` is produced by Tag 09S8 inside the differential graded world and carried across
the degree-zero comparison `DifferentialGradedModule.degreeZeroDerivedEquivalence`; perfectness
is compactness by Tag 07LT.

The source's condition (1) is an equivalence of `R`-linear triangulated categories; what is
assumed here is less, namely additivity, `R`-linearity and commutation with the translation,
`CategoryTheory.Functor.IsTriangulated` not being used. The converse implication is not proved
here: see the implementation notes of this file. -/
@[stacks 09SC "(1) ⇒ (2), with D(A) read as the derived category of right A-modules, clause \
(2)(a) as StacksDraft.Perfect.IsPerfect, Ext vanishing as Subsingleton of the shifted Hom group \
and the degree-zero clause of (2)(c) as an isomorphism of R-algebras A ≃ₐ[R] End P; NOT \
(2) ⇒ (1), which needs CategoryTheory.Functor.IsTriangulated for \
DifferentialGradedModule.degreeZeroDerivedEquivalence, and NOT part (3)"]
theorem exists_isPerfect_and_detectsZero_of_derivedEquivalence
    (E : DerivedCategory (ModuleCat.{u} Aᵐᵒᵖ) ≌ DerivedCategory (ModuleCat.{u} Bᵐᵒᵖ))
    [E.functor.Additive] [E.functor.Linear R] [E.functor.CommShift ℤ] :
    ∃ P : DerivedCategory (ModuleCat.{u} Bᵐᵒᵖ),
      StacksDraft.Perfect.IsPerfect P ∧
      (∀ K : DerivedCategory (ModuleCat.{u} Bᵐᵒᵖ),
        (∀ i : ℤ, Subsingleton (P ⟶ K⟦i⟧)) → IsZero K) ∧
      (∀ i : ℤ, i ≠ 0 → Subsingleton (P ⟶ P⟦i⟧)) ∧
      Nonempty (A ≃ₐ[R] End P) := by
  let EA := degreeZeroDerivedEquivalence (R := R) (S := A) (A := Aᵐᵒᵖ)
  let EB := degreeZeroDerivedEquivalence (R := R) (S := B) (A := Bᵐᵒᵖ)
  have := EB.commShiftInverse ℤ
  let G : derivedCategory' (degreeZero R A) ≌ derivedCategory' (degreeZero R B) :=
    EA.trans (E.trans EB.symm)
  have : G.functor.Additive := by
    change (EA.functor ⋙ E.functor ⋙ EB.inverse).Additive
    infer_instance
  have : G.functor.Linear R := by
    change (EA.functor ⋙ E.functor ⋙ EB.inverse).Linear R
    infer_instance
  have : G.functor.CommShift ℤ := by
    infer_instance
  obtain ⟨P₀, hcompact, hgen, hvan, ⟨ealg⟩, -⟩ :=
    exists_isCompactObject_and_isWeakGenerator_of_derivedEquivalence
      (degreeZero R A) (degreeZero R B) degreeZero_grading_eq_bot G
  refine ⟨EB.functor.obj P₀, ?_, ?_, ?_,
    ⟨ealg.trans (EB.fullyFaithfulFunctor.algEquivEndOfFullyFaithful _)⟩⟩
  · exact (StacksDraft.Perfect.isPerfect_iff_isCompactObject _).2
      ((isCompactObject_iff_isCompactObject_obj EB.functor P₀).1 hcompact)
  · exact (detectsZero_iff_obj EB P₀).1 fun K hK =>
      hgen K fun i f => (subsingleton_hom_iff_forall_eq_zero _ _).1 (hK i) f
  · exact fun i hi => (subsingleton_shiftHom_iff_obj EB P₀ P₀ i).1
      ((subsingleton_hom_iff_forall_eq_zero _ _).2 (hvan i hi))

end Rickard

end DifferentialGradedModule

end
