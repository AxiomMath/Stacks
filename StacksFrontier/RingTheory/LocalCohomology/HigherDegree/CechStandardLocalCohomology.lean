module

public import StacksFrontier.RingTheory.LocalCohomology.CechModel
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.OrderedCechComparison

/-!
# Čech cohomology of the standard covering of the complement is local cohomology, shifted

Let `A` be a commutative ring, let `I = (f₁, …, f_r)` be a finitely generated ideal and let
`U = Spec A \ V(I)`, covered by the standard opens `D(f_i)`. Two facts about that covering are
proved separately:

* its Čech complex, in the explicit cochain model and in Mathlib's product model, computes the
  same cohomology as the *alternating* Čech complex
  (`Stacks.Cech.orderedCechHomologyIso`, from Stacks 01FJ and Stacks 01FM);
* the alternating Čech complex of the covering with coefficients in `M̃` is the extended
  alternating Čech complex `C^•(f₁, …, f_r; M)` of the ring, shifted by one
  (`Stacks.LocalCohomology.orderedCechHomologyIsoCechComplexHomology`).

This file puts them together and then applies the Čech formula for local cohomology of
Stacks 0A6R: in every degree `n ≥ 1`,

`Ȟ^n(𝒰, M̃) ≅ H^{n+1}_{V(I)}(M)`,

as abelian groups. This is the algebraic half of the comparison of Stacks 0DWR in degrees above
one: what remains, to turn it into a statement about the sheaf cohomology of `M̃` on `U`, is the
identification of Mathlib's Čech complex of the covering — a complex of abelian groups, for a
family of *opens of the prime spectrum* — with the module-valued Čech complex of Stacks 01EP
used by `StacksFrontier/RingTheory/LocalCohomology/HigherDegree/CechSheafCohomology.lean`, whose
family lives in the slice category over `U`. Both are instances of the same construction
`CategoryTheory.cechComplexFunctor`, and the degreewise description of
`StacksFrontier/CategoryTheory/Sites/CechComplex.lean` applies to both; that comparison is not
proved here.

## Main definitions

* `Stacks.LocalCohomology.cechStandardHomologyIsoCechComplexHomology` — **Čech cohomology of the
  standard covering in degree `q + 1` is the degree-`q+2` cohomology of
  `C^•(f₁, …, f_r; M)`.**

## Main results

* `Stacks.LocalCohomology.nonempty_cechStandardHomology_iso_localCohomologyModule` — **Čech
  cohomology of the standard covering of `U = Spec A \ V(I)` is local cohomology with support in
  `V(I)`, shifted by one**, in every degree above zero.
* `Stacks.LocalCohomology.isZero_cechStandardHomology_iff_isZero_localCohomologyModule` — the
  vanishing form of the same statement, which is what a criterion for the cohomological
  dimension of an ideal consumes.

## Implementation notes

The comparison with local cohomology is an isomorphism of *abelian groups*, not of `A`-modules.
The reason is the one step that is not `A`-linear by construction: the comparison of the
alternating with the full Čech complex of a covering is proved in Stacks 01FM for presheaves of
abelian groups, as a homotopy equivalence built from the sorting permutations, and the library
has it only there. Every other step is a map of `A`-modules. For the intended consumer — the
criterion for the cohomological dimension of an ideal, where both sides of the relevant clause
are vanishing statements — that is enough: `IsZero` in `AddCommGrpCat`, `Subsingleton` and
`IsZero` in `ModuleCat` are interchangeable, and
`Stacks.LocalCohomology.isZero_cechStandardHomology_iff_isZero_localCohomologyModule` is stated
in that form.

The Čech formula for local cohomology is used through
`Stacks.LocalCohomology.nonempty_homology_localCohomology_iso_cechHomology`, which is a
`Nonempty` statement, so the conclusion is `Nonempty` as well; the degree shift between the
integer-indexed extended complex and the natural-number-indexed Čech complex is
`HomologicalComplex.extendHomologyIso`.

No Stacks tag attribute is placed here.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (M : ModuleCat.{max u v} A)

/-- **Čech cohomology of the standard covering is the cohomology of the algebraic Čech complex,
shifted by one.** In degree `q + 1` the Čech cohomology of the covering of
`U = Spec A \ V(f₁, …, f_r)` by the basic opens `D(f_i)`, with coefficients in `M̃`, is the
degree-`q+2` cohomology of the extended alternating Čech complex `C^•(f₁, …, f_r; M)`. -/
def cechStandardHomologyIsoCechComplexHomology (q : ℕ) :
    ((CategoryTheory.cechComplexFunctor (cechStandardOpen f)).obj
        (associatedAbPresheaf M)).homology (q + 1) ≅
      (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}).obj
        ((_root_.Cech.cechComplex f (M : Type _)).homology (q + 2)) :=
  (Stacks.Cech.orderedCechHomologyIso (cechStandardOpen f) (associatedAbPresheaf M)
      (q + 1)).symm ≪≫
    orderedCechHomologyIsoCechComplexHomology f M q

/-- The degree-`q+2` cohomology of the extended alternating Čech complex, read in integer
degrees, is the degree-`q+2` cohomology of the natural-number-indexed complex. -/
def extendedCechHomologyIso (q : ℕ) :
    (extendedCechComplex f M).homology ((q : ℤ) + 2) ≅
      (_root_.Cech.cechComplex f (M : Type _)).homology (q + 2) :=
  HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat
    (by change ((q + 2 : ℕ) : ℤ) = (q : ℤ) + 2; push_cast; ring)

/-- **Čech cohomology of the standard covering of `U = Spec A \ V(I)` is local cohomology with
support in `V(I)`, shifted by one**, in every degree above zero: for a finite family generating
`I`, the degree-`q+1` Čech cohomology of the covering by the basic opens `D(f_i)` with
coefficients in `M̃` is `H^{q+2}_{V(I)}(M)`, as an abelian group.

The two inputs are the comparison of the Čech complex of the covering with the algebraic Čech
complex of the family, and the Čech formula of Stacks 0A6R computing local cohomology by that
algebraic complex. -/
theorem nonempty_cechStandardHomology_iso_localCohomologyModule (I : Ideal A) (hI : I.FG)
    (hIf : Ideal.span (Set.range f) = I) (q : ℕ) :
    Nonempty (((CategoryTheory.cechComplexFunctor (cechStandardOpen f)).obj
        (associatedAbPresheaf M)).homology (q + 1) ≅
      (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}).obj
        (localCohomologyModule A I hI M ((q : ℤ) + 2))) := by
  obtain ⟨e⟩ := nonempty_homology_localCohomology_iso_cechHomology f M I hI hIf ((q : ℤ) + 2)
  exact ⟨cechStandardHomologyIsoCechComplexHomology f M q ≪≫
    (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}).mapIso
      ((extendedCechHomologyIso f M q).symm ≪≫ e.symm)⟩

/-- **Čech cohomology of the standard covering of `U = Spec A \ V(I)` is local cohomology with
support in `V(I)`, shifted by one**, as a named isomorphism in every degree above zero: the
choice-free form of
`Stacks.LocalCohomology.nonempty_cechStandardHomology_iso_localCohomologyModule`.

The Čech formula of Stacks 0A6R is used through
`Stacks.LocalCohomology.localCohomologyIsoExtendedCechHomology`, which carries a map. -/
def cechStandardHomologyIsoLocalCohomologyModule (I : Ideal A) (hI : I.FG)
    (hIf : Ideal.span (Set.range f) = I) (q : ℕ) :
    ((CategoryTheory.cechComplexFunctor (cechStandardOpen f)).obj
        (associatedAbPresheaf M)).homology (q + 1) ≅
      (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}).obj
        (localCohomologyModule A I hI M ((q : ℤ) + 2)) :=
  cechStandardHomologyIsoCechComplexHomology f M q ≪≫
    (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}).mapIso
      ((extendedCechHomologyIso f M q).symm ≪≫
        (localCohomologyIsoExtendedCechHomology f M I hI hIf ((q : ℤ) + 2)).symm)

/-- **The vanishing form of the comparison.** For `n = q + 1 ≥ 1` the degree-`n` Čech cohomology
of the standard covering vanishes exactly when `H^{n+1}_{V(I)}(M)` does. A forgetful functor
cannot create or destroy a zero object here: an object of `AddCommGrpCat` or of `ModuleCat` is
zero exactly when it is a subsingleton. -/
theorem isZero_cechStandardHomology_iff_isZero_localCohomologyModule (I : Ideal A) (hI : I.FG)
    (hIf : Ideal.span (Set.range f) = I) (q : ℕ) :
    IsZero (((CategoryTheory.cechComplexFunctor (cechStandardOpen f)).obj
        (associatedAbPresheaf M)).homology (q + 1)) ↔
      IsZero (localCohomologyModule A I hI M ((q : ℤ) + 2)) := by
  obtain ⟨e⟩ := nonempty_cechStandardHomology_iso_localCohomologyModule f M I hI hIf q
  rw [AddCommGrpCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  exact ((forget AddCommGrpCat.{max u v}).mapIso e).toEquiv.subsingleton_congr

end Stacks.LocalCohomology

end
