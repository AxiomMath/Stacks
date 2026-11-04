module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCoproducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCompact
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleRepresents
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksCore.Tactic.StacksAttribute

/-! # The image of the regular module under an equivalence of derived categories

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let
`F : D(A, d) ⥤ D(B, d)` be an equivalence commuting with the translation. Put `N = F(A)`, the
image of the regular module. [Stacks, Tag 09S9] observes that `N` inherits from `A` everything
that hypothesis (2) of [Stacks, Tag 09S7] asks of a bimodule: `N` is represented by a
differential graded `B`-module, it is a compact object of `D(B, d)`, it generates `D(B, d)`, and
`H^k(A) = Hom_{D(B, d)}(N, N[k])` for every `k ∈ ℤ`.

## Main results

* `DifferentialGradedModule.exists_dgModule_iso`: every object of `D(B, d)` is isomorphic to the
  image of a differential graded `B`-module, the localization functor being essentially
  surjective.
* `DifferentialGradedModule.exists_dgModule_iso_obj_q_regularModule`: **Stacks 09S9**, `N = F(A)`
  is represented by a differential graded `B`-module.
* `DifferentialGradedModule.isCompactObject_obj_q_regularModule`: **Stacks 09S9**, `N = F(A)` is
  a compact object of `D(B, d)`.
* `DifferentialGradedModule.isWeakTriangulatedGenerator_singleton_obj_q_regularModule`:
  **Stacks 09S9**, `N = F(A)` generates `D(B, d)`.
* `DifferentialGradedModule.cohomologyEquivDerivedHomObjRegular`: **Stacks 09S9**, the bijection
  `H^k(A) ≃ Hom_{D(B, d)}(N, N[k])`.
* `DifferentialGradedModule.eq_zero_of_hom_obj_q_regularModule_shift`: when `A = H^0(A)`, every
  morphism `N ⟶ N[i]` with `i ≠ 0` vanishes. This is clause (c) of condition (2) of
  [Stacks, Tag 09S8], in the direction (1) ⟹ (2) of that tag.

## Implementation notes

*Hypotheses.* The source assumes `F` is an `R`-linear equivalence of triangulated categories.
None of the four conclusions above needs the `R`-linearity, and none needs `F` to carry
distinguished triangles to distinguished triangles: what is used is that `F` is an additive
equivalence commuting with the translation. The statements below assume only that, so they are
more general than the source's. The `R`-linear equivalence of Tag 09S7 satisfies them, its
`R`-linearity being `DifferentialGraded.Bimodule.derivedTensorEquivalence_linear`.

*What is not formalized here.* The remainder of the source's remark is the observation that a
left `A`-module structure on `N`, compatible with the differential and commuting with the right
`B`-action, is the one ingredient still missing before Tag 09S7 applies, together with the claim
that it exists when `F` lifts to a functor of differential graded categories. Those are not
proved here, so `N` is not produced as a differential graded `(A, B)`-bimodule.

*The shape of the cohomology statement.* `DifferentialGradedAlgebra.Cohomology` carries no
additive or multiplicative structure in this development, so the identification
`H^k(A) = Hom_{D(B, d)}(N, N[k])` is a bijection of types, exactly as the
`DifferentialGradedModule.cohomologyEquivDerivedHom` it is transported from.

## References

* [Stacks Project, Tag 09S9](https://stacks.math.columbia.edu/tag/09S9), the remark proved here.
* [Stacks Project, Tag 09S7](https://stacks.math.columbia.edu/tag/09S7) for the hypotheses the
  conclusions match.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- Every object of the derived category of a differential graded algebra is isomorphic to the
image of a differential graded module: the localization functor is essentially surjective and
the quotient functor onto `K(B, d)` is the identity on objects. -/
theorem exists_dgModule_iso (B : DifferentialGradedAlgebra R) (X : derivedCategory' B) :
    ∃ M : DifferentialGradedModule B,
      Nonempty (X ≅ (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj M) := by
  have := Localization.essSurj (quasiIsomorphisms' B).Q (quasiIsomorphisms' B)
  exact ⟨((quasiIsomorphisms' B).Q.objPreimage X).as,
    ⟨((quasiIsomorphisms' B).Q.objObjPreimageIso X).symm⟩⟩

variable (A B : DifferentialGradedAlgebra R) (F : derivedCategory' A ⥤ derivedCategory' B)

/-- **Stacks 09S9.** The image `N = F(A)` of the regular module under a functor
`F : D(A, d) ⥤ D(B, d)` is represented by a differential graded `B`-module. -/
@[stacks 09S9 "N = F(A) is represented by a differential graded B-module"]
theorem exists_dgModule_iso_obj_q_regularModule :
    ∃ N : DifferentialGradedModule B,
      Nonempty (F.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ≅
        (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N) :=
  exists_dgModule_iso B _

/-- **Stacks 09S9.** The image `N = F(A)` of the regular module under an additive equivalence
`F : D(A, d) ⥤ D(B, d)` is a compact object of `D(B, d)`: the regular module is compact
(`DifferentialGradedModule.isCompactObject_q_regularModule`) and compactness is invariant under
an additive equivalence. -/
@[stacks 09S9 "N = F(A) is a compact object of D(B, d)"]
theorem isCompactObject_obj_q_regularModule [F.IsEquivalence] [F.Additive] :
    IsCompactObject.{u}
      (F.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))) :=
  (isCompactObject_iff_isCompactObject_obj F _).1 (isCompactObject_q_regularModule A)

/-- **Stacks 09S9.** The image `N = F(A)` of the regular module under an additive equivalence
`F : D(A, d) ⥤ D(B, d)` commuting with the translation generates `D(B, d)`: an object receiving
only zero morphisms from the shifts of `N` is zero.

The regular module generates `D(A, d)` (`DifferentialGradedModule`
`.isWeakTriangulatedGenerator_q_regularModule`), so it suffices to carry a vanishing hypothesis
on `K` back along `F`: a morphism `A ⟶ (F⁻¹K)[n]` becomes, under `F` and the commutation with
the translation, a morphism `N ⟶ K[n]`, hence vanishes, hence vanishes itself because `F` is
faithful. Then `F⁻¹K` is zero and so is `K`. -/
@[stacks 09S9 "N = F(A) generates D(B, d)"]
theorem isWeakTriangulatedGenerator_singleton_obj_q_regularModule
    [F.IsEquivalence] [F.Additive] [F.CommShift ℤ] :
    ObjectProperty.IsWeakTriangulatedGenerator (ObjectProperty.singleton
      (F.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))) := by
  rw [ObjectProperty.isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero]
  intro K hK
  have hgen := (ObjectProperty.isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero
    ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))).1
      (isWeakTriangulatedGenerator_q_regularModule A)
  have hZ : IsZero (F.asEquivalence.inverse.obj K) := by
    refine hgen _ fun n f => ?_
    let v := (F.commShiftIso n).app (F.asEquivalence.inverse.obj K) ≪≫
      (CategoryTheory.shiftFunctor (derivedCategory' B) n).mapIso (F.asEquivalence.counitIso.app K)
    have h : F.map f = 0 := by
      simpa using congrArg (· ≫ v.inv) (hK n _ : F.map f ≫ v.hom = 0)
    exact F.map_injective (h.trans (F.map_zero _ _).symm)
  exact (F.map_isZero hZ).of_iso (F.asEquivalence.counitIso.app K).symm

/-- **Stacks 09S9.** For a fully faithful `F : D(A, d) ⥤ D(B, d)` commuting with the translation
and `N = F(A)` the image of the regular module, `H^k(A) = Hom_{D(B, d)}(N, N[k])` for every
`k ∈ ℤ`.

This transports the bijection `H^k(A) ≃ Hom_{D(A, d)}(A, A[k])` of
`DifferentialGradedModule.cohomologyEquivDerivedHom` along `F`, using the shift comparison
`DifferentialGradedModule.regularShiftCompare` at the source and the commutation of `F` with the
translation at the target. -/
@[stacks 09S9 "H^k(A) = Hom_{D(B,d)}(N, N[k])"]
def cohomologyEquivDerivedHomObjRegular [F.Full] [F.Faithful] [F.CommShift ℤ] (k : ℤ) :
    A.Cohomology k ≃
      (F.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
        (F.obj
          ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))⟦k⟧) :=
  (((cohomologyEquivDerivedHom A k).trans
        ((Iso.refl _).homCongr (regularShiftCompare A k))).trans
      (CategoryTheory.Functor.FullyFaithful.ofFullyFaithful F).homEquiv).trans
    ((Iso.refl _).homCongr ((F.commShiftIso k).app _))

/-- A differential graded algebra with no homogeneous elements of degree `k` has vanishing
degree-`k` cohomology: every degree-`k` cocycle is zero, so there is at most one cohomology
class. -/
theorem subsingleton_cohomology_of_grading_eq_bot (C : DifferentialGradedAlgebra R) {k : ℤ}
    (hk : C.grading k = ⊥) : Subsingleton (C.Cohomology k) := by
  have hzero : ∀ a : C.Cocycle k, (a.1 : C.A) = 0 := fun a =>
    (Submodule.mem_bot R).mp (hk ▸ a.1.2)
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.ind with | _ a => ?_
  induction y using Quotient.ind with | _ b => ?_
  exact congrArg (Quotient.mk _) (Subtype.ext (Subtype.ext ((hzero a).trans (hzero b).symm)))

/-- **Clause (c) of condition (2) of [Stacks, Tag 09S8], in the direction (1) ⟹ (2).** Let
`(A, d)` be concentrated in degree zero, so that `A = H^0(A)`, and let
`F : D(A, d) ⥤ D(B, d)` be fully faithful and commute with the translation. Then every morphism
`N ⟶ N[i]` with `i ≠ 0` out of `N = F(A)` vanishes.

The hypothesis makes `H^i(A)` vanish for `i ≠ 0`, and
`DifferentialGradedModule.cohomologyEquivDerivedHomObjRegular` identifies it with
`Hom_{D(B, d)}(N, N[i])`. -/
theorem eq_zero_of_hom_obj_q_regularModule_shift [F.Full] [F.Faithful] [F.CommShift ℤ]
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) {i : ℤ} (hi : i ≠ 0)
    (f : F.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
      (F.obj
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))⟦i⟧) :
    f = 0 :=
  have := (cohomologyEquivDerivedHomObjRegular A B F i).subsingleton_congr.mp
    (subsingleton_cohomology_of_grading_eq_bot A (hA i hi))
  Subsingleton.elim _ _

end DifferentialGradedModule

end
