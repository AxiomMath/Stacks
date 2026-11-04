module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory
public import StacksCore.Tactic.StacksAttribute

/-! # Cohomology detects isomorphisms in the derived category

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. A morphism of
`D(A, d)` is an isomorphism exactly when degree-zero cohomology of each of its shifts is an
isomorphism of `R`-modules — that is, when it is an isomorphism on cohomology in every degree.

This is the step "it suffices to show that `H^n(M) → H^n(M')` is an isomorphism for all `n`" used
throughout the chapter, and in particular in the proof of [Stacks, Tag 09R9]. The library's form of
Tag 09KW gives it for morphisms *represented by a homomorphism of differential graded modules*
(`DifferentialGradedModule.degreeZeroHomology_shift_map_isIso_iff`, read through
`DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms'`); what is proved here is the statement
for an arbitrary morphism of `D(A, d)`, which is what a consumer applying it to the unit of an
adjunction needs.

## Main results

* `DifferentialGradedModule.quasiIsomorphisms_iff_forall_isIso_degreeZeroCohomology`: on
  `K(A, d)`, a morphism is a quasi-isomorphism exactly when degree-zero cohomology of each of its
  shifts is an isomorphism.
* `DifferentialGradedModule.isIso_iff_forall_isIso_degreeZeroCohomology`: on `D(A, d)`, a morphism
  is an isomorphism under the same condition.

## Implementation notes

*On `K(A, d)` this is the homological-kernel criterion.* Degree-zero cohomology is a homological
functor on the homotopy category
(`DifferentialGradedModule.degreeZeroHomologyOnHomotopy_isHomological`), the acyclic modules are
its homological kernel
(`DifferentialGradedModule.homologicalKernel_degreeZeroHomology_eq_acyclic`), and the
quasi-isomorphisms are the morphisms attached to that subcategory
(`DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms'`). So the statement is
`CategoryTheory.Functor.mem_homologicalKernel_trW_iff` for the tautological shift sequence, and
it holds for *every* morphism of `K(A, d)` with no representability assumption.

*On `D(A, d)` it is the calculus of fractions.* An arbitrary morphism of the localization is not
of the form `Q(g)`; but the quasi-isomorphisms have a left calculus of fractions
(`DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions'`), so after transporting
along `CategoryTheory.Functor.objObjPreimageIso` at both ends,
`CategoryTheory.Localization.exists_leftFraction` writes the morphism as `Q(f)` followed by the
inverse of `Q(s)` with `s` a quasi-isomorphism.
Both the hypothesis and the conclusion are insensitive to composing with an isomorphism, so the
statement reduces to the one for `Q(f)`, and then to the one for `f` on `K(A, d)` — the passage
across the localization being `DifferentialGradedModule.degreeZeroCohomologyOnLocalizationIso'`
together with the shift comparison of the localization functor.

## References

* [Stacks Project, Tag 09KW](https://stacks.math.columbia.edu/tag/09KW); it is used in this form
  in the proof of [Tag 09R9](https://stacks.math.columbia.edu/tag/09R9).
-/

@[expose] public noncomputable section

open CategoryTheory

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- Two morphisms related by a commuting square whose vertical maps are isomorphisms are
isomorphisms together. -/
private theorem isIso_iff_of_square {C : Type*} [Category C] {X Y Z W : C}
    {u : X ⟶ Y} {v : Z ⟶ W} (a : X ≅ Z) (b : Y ≅ W)
    (h : u ≫ b.hom = a.hom ≫ v) : IsIso u ↔ IsIso v :=
  (MorphismProperty.isomorphisms C).arrow_mk_iso_iff (Arrow.isoMk' u v a b h.symm)

/-- **Cohomology detects quasi-isomorphisms on the homotopy category.** A morphism of `K(A, d)` is
a quasi-isomorphism exactly when degree-zero cohomology of each of its shifts is an isomorphism.
No representability is assumed of the morphism. -/
@[stacks 09KW "cohomology detects quasi-isomorphisms"]
theorem quasiIsomorphisms_iff_forall_isIso_degreeZeroCohomology {X Y : HomotopyCategory A}
    (g : X ⟶ Y) :
    quasiIsomorphisms' A g ↔
      ∀ n : ℤ, IsIso ((degreeZeroCohomologyOnHomotopy' A).map (g⟦n⟧')) := by
  rw [← acyclic_trW_eq_quasiIsomorphisms' A,
    ← homologicalKernel_degreeZeroHomology_eq_acyclic A]
  let := degreeZeroHomologyOnHomotopy_isHomological A
  let : (degreeZeroHomologyOnHomotopy A).ShiftSequence ℤ :=
    Functor.ShiftSequence.tautological _ ℤ
  exact (degreeZeroHomologyOnHomotopy A).mem_homologicalKernel_trW_iff g

/-- Degree-zero cohomology on `D(A, d)` of a shift of the image of a morphism of `K(A, d)` is an
isomorphism exactly when degree-zero cohomology on `K(A, d)` of the corresponding shift is. -/
theorem isIso_degreeZeroCohomologyOnLocalization_map_shift_Q_map_iff
    {X Y : HomotopyCategory A} (g : X ⟶ Y) (n : ℤ) :
    IsIso ((degreeZeroCohomologyOnLocalization' A).map
        (((quasiIsomorphisms' A).Q.map g)⟦n⟧')) ↔
      IsIso ((degreeZeroCohomologyOnHomotopy' A).map (g⟦n⟧')) := by
  have hsq : (quasiIsomorphisms' A).Q.map (g⟦n⟧') ≫
      ((quasiIsomorphisms' A).Q.commShiftIso n).hom.app Y =
      ((quasiIsomorphisms' A).Q.commShiftIso n).hom.app X ≫
        ((quasiIsomorphisms' A).Q.map g)⟦n⟧' :=
    ((quasiIsomorphisms' A).Q.commShiftIso n).hom.naturality g
  have h1 : IsIso ((degreeZeroCohomologyOnLocalization' A).map
        ((quasiIsomorphisms' A).Q.map (g⟦n⟧'))) ↔
      IsIso ((degreeZeroCohomologyOnLocalization' A).map
        (((quasiIsomorphisms' A).Q.map g)⟦n⟧')) :=
    isIso_iff_of_square
      ((degreeZeroCohomologyOnLocalization' A).mapIso
        (((quasiIsomorphisms' A).Q.commShiftIso n).app X))
      ((degreeZeroCohomologyOnLocalization' A).mapIso
        (((quasiIsomorphisms' A).Q.commShiftIso n).app Y))
      (by
        simp only [Functor.mapIso_hom, Iso.app_hom, ← Functor.map_comp]
        exact congrArg _ hsq)
  rw [← h1]
  exact NatIso.isIso_map_iff (degreeZeroCohomologyOnLocalizationIso' A) (g⟦n⟧')

/-- **Cohomology detects isomorphisms in the derived category.** A morphism of `D(A, d)` is an
isomorphism exactly when degree-zero cohomology of each of its shifts is an isomorphism of
`R`-modules.

This is the general-morphism form: the morphism is an arbitrary morphism of the localization, not
one represented by a homomorphism of differential graded modules.

No tag is carried: this is a consequence of Tag 09KW — saturation of the multiplicative system
together with the identification of the quasi-isomorphisms as the morphisms inducing isomorphisms
on all cohomology — and not one of its assertions. It is the form in which the proof of
[Stacks, Tag 09R9] uses it. -/
theorem isIso_iff_forall_isIso_degreeZeroCohomology {X Y : derivedCategory' A} (φ : X ⟶ Y) :
    IsIso φ ↔ ∀ n : ℤ, IsIso ((degreeZeroCohomologyOnLocalization' A).map (φ⟦n⟧')) := by
  refine ⟨fun _ _ => inferInstance, fun h => ?_⟩
  have := Localization.essSurj (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)
  set eX := (quasiIsomorphisms' A).Q.objObjPreimageIso X
  set eY := (quasiIsomorphisms' A).Q.objObjPreimageIso Y
  obtain ⟨α, hα⟩ := Localization.exists_leftFraction (quasiIsomorphisms' A).Q
    (quasiIsomorphisms' A) (eX.hom ≫ φ ≫ eY.inv)
  have hfac : (eX.hom ≫ φ ≫ eY.inv) ≫ (quasiIsomorphisms' A).Q.map α.s =
      (quasiIsomorphisms' A).Q.map α.f := by
    rw [hα]
    exact MorphismProperty.LeftFraction.map_comp_map_s α _ _
  have : IsIso ((quasiIsomorphisms' A).Q.map α.s) :=
    Localization.inverts (quasiIsomorphisms' A).Q (quasiIsomorphisms' A) _ α.hs
  have : IsIso ((quasiIsomorphisms' A).Q.map α.f) := by
    refine Localization.inverts (quasiIsomorphisms' A).Q (quasiIsomorphisms' A) _
      ((quasiIsomorphisms_iff_forall_isIso_degreeZeroCohomology A α.f).2 fun n => ?_)
    rw [← isIso_degreeZeroCohomologyOnLocalization_map_shift_Q_map_iff, ← hfac]
    have := h n
    simp only [Functor.map_comp]
    infer_instance
  have : IsIso ((eX.hom ≫ φ ≫ eY.inv) ≫ (quasiIsomorphisms' A).Q.map α.s) := by rwa [hfac]
  have : IsIso (eX.hom ≫ φ ≫ eY.inv) :=
    IsIso.of_isIso_comp_right _ ((quasiIsomorphisms' A).Q.map α.s)
  rw [show φ = eX.inv ≫ (eX.hom ≫ φ ≫ eY.inv) ≫ eY.hom by simp]
  infer_instance

end DifferentialGradedModule

end
