module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomDerivedTriangulated
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion

/-!
# Tag 09LK with no derivability hypothesis, over a category with K-injective resolutions

Let `A` be an abelian category whose morphisms are sets, let `K` be a cochain complex in `A` and
let `E = End(K)` be its endomorphism differential graded algebra. Tag 09LK's functor
`R Hom(K, -) : D(A) ⥤ D(E, d)` is built in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomVariant.lean` from the hypothesis that
the right derived functor of the differential-graded-module-valued
`Hom(K, -) : K(A) ⥤ D(E, d)` is defined everywhere — a *strengthening* of the hypothesis the
source states, which is everywhere-definedness of the abelian-group-valued
`Hom(K, -) : K(A) ⥤ D(Ab)`. The implementation notes of that file record why the strengthening
is there: the source's reason for passing from one to the other gives only conservativity of the
forgetful functor `D(E, d) ⥤ D(Ab)`, and conservativity moves no essential-constancy witness.

This file removes the hypothesis altogether — not by weakening it, and not by assuming the
source's instead, but by *discharging* it — whenever every cochain complex in `A` admits a
quasi-isomorphism towards a K-injective complex. That is a condition on `A` alone. It mentions
neither `K`, nor the Hom functor, nor the derived category of differential graded modules, and it
is automatic in a Grothendieck abelian category, where the K-injective resolution functor of
`StacksFrontier/Homology/Injectives/KInjective/FunctorialResolution.lean` supplies it.

## Why the hypothesis is free there

Tag 070Y, `CategoryTheory.Functor.exists_isRightDerivedValueAt_and_isIso_of_isKInjective`, says
that for an *arbitrary* functor `F` out of `K(A)` and a K-injective complex `I`, the right
derived functor of `F` is defined at every object of `K(A)` joined to `I` by a quasi-isomorphism
in either direction. Nothing is asked of `F`: a K-injective complex is a terminal object of the
category of quasi-isomorphisms out of it, by `CochainComplex.isLocal_quasiIso`, so the ind-object
of Tag 05S9 has a terminal index and is essentially constant for trivial reasons.

So a K-injective resolution of a representative complex of `X` exhibits a value at `X`, and
everywhere-definedness of `R Hom(K, -)` in `D(E, d)` — the hypothesis of
`CochainComplex.derivedHomFunctor` — becomes a theorem rather than an assumption. Every clause
Tag 09LK registers under it follows by substitution, and so, by
`CochainComplex.isRightDerivable_homToDerivedCategoryForget_quasiIso`, does the source's own
hypothesis.

What this does *not* do is prove the implication the source asserts. The source's hypothesis on
the `D(Ab)`-valued functor is not used here and is not what makes the argument run; K-injective
resolutions give both hypotheses at once, and in their absence the gap recorded in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomVariant.lean` stands exactly as before.

## Main results

* `CochainComplex.isRightDerivable_homToDerivedCategory_of_exists_isKInjective`: if every complex
  in `A` admits a quasi-isomorphism towards a K-injective complex then the right derived functor
  of `Hom(K, -) : K(A) ⥤ D(E, d)` is defined at every object of `K(A)`.
* `CochainComplex.isRightDerivable_homToDerivedCategory_of_isGrothendieckAbelian`: the same for a
  Grothendieck abelian category, where K-injective resolutions exist.
* `CochainComplex.derivedHomFunctor_isRightDerivedFunctor_of_exists_isKInjective`,
  `CochainComplex.derivedHomFunctor_isTriangulated_of_exists_isKInjective` and
  `derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor_of_exists_isKInjective` in the same
  namespace: Tag 09LK's functor, its universal property, its exactness and its reduction to the
  usual one on associated complexes, with no derivability hypothesis.
* `CochainComplex.isRightDerivable_homToDerivedCategoryForget_of_exists_isKInjective`: the
  source's own hypothesis is likewise free there.

## Implementation notes

The statements below are the existing declarations of
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomVariant.lean` and
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomDerivedTriangulated.lean` applied to the
derivability *theorem*, not re-proofs of them: the functor named in each conclusion is
`CochainComplex.derivedHomFunctor` itself, so there is one canonical functor in the library and
not a second copy of it under a second hypothesis. The derived hypothesis is bound by a `let` in
each statement, which keeps the conclusions inside the column limit and keeps the functor and its
unit visibly the same two terms.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), the statement whose
  hypothesis is discharged here; [Tag 070K](https://stacks.math.columbia.edu/tag/070K) and
  [Tag 070Y](https://stacks.math.columbia.edu/tag/070Y), the right derived functor of an
  arbitrary functor on a category with K-injective resolutions, and
  [Tag 05S9](https://stacks.math.columbia.edu/tag/05S9) for being defined at an object.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w w' w'' u

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Abelian A] (K : CochainComplex A ℤ)

/-- **The hypothesis of Tag 09LK's functor is free over a category with K-injective
resolutions.** If every cochain complex in `A` admits a quasi-isomorphism towards a K-injective
complex, then the right derived functor of the differential-graded-module-valued
`Hom(K, -) : K(A) ⥤ D(E, d)` is defined at every object of `K(A)`.

Nothing is asked of `K` or of the functor. An object of `K(A)` is the homotopy class of a complex,
a K-injective resolution of that complex is a quasi-isomorphism out of the object, and Tag 070Y
exhibits a value of the right derived functor of an arbitrary functor at any object joined to a
K-injective complex by a quasi-isomorphism — the index of the resolution being a terminal object
of the category of quasi-isomorphisms out of the object. -/
theorem isRightDerivable_homToDerivedCategory_of_exists_isKInjective
    (hres : ∀ X : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : X ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  intro X
  obtain ⟨L, rfl⟩ := _root_.HomotopyCategory.quotient_obj_surjective X
  obtain ⟨I, f, hI, hf⟩ := hres L
  let _ := hI
  let _ := hf
  exact (Functor.exists_isRightDerivedValueAt_and_isIso_of_isKInjective
    (homToDerivedCategory A K) I).2 _
    (Or.inl ⟨(_root_.HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f, by
      rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]; exact hf⟩)

/-- **The hypothesis of Tag 09LK's functor is free over a Grothendieck abelian category.** Every
complex in such a category has a K-injective resolution, by
`Stacks.Injectives.exists_kInjective_resolution_of_grothendieck`. -/
theorem isRightDerivable_homToDerivedCategory_of_isGrothendieckAbelian
    [IsGrothendieckAbelian.{w'', 0, u} A] :
    (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  isRightDerivable_homToDerivedCategory_of_exists_isKInjective A K
    Stacks.Injectives.exists_kInjective_resolution_of_grothendieck

variable [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- **The source's own hypothesis is free over a category with K-injective resolutions.** Tag
09LK assumes the right derived functor of the abelian-group-valued
`Hom(K, -) : K(A) ⥤ D(Ab)` to be everywhere defined; K-injective resolutions give that too,
either directly by Tag 070Y or through
`CochainComplex.isRightDerivable_homToDerivedCategoryForget_quasiIso` from the previous
result. -/
theorem isRightDerivable_homToDerivedCategoryForget_of_exists_isKInjective
    [CategoryWithHomology A]
    (hres : ∀ X : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : X ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    (homToDerivedCategoryForget A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  isRightDerivable_homToDerivedCategoryForget_quasiIso A K
    (isRightDerivable_homToDerivedCategory_of_exists_isKInjective A K hres)

end CochainComplex

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Abelian A] [HasDerivedCategory.{w'} A]
  (K : CochainComplex A ℤ)

/-- **Stacks 09LK's functor and its universal property, for an abelian category with K-injective
resolutions.**
Over an abelian category in which every complex admits a quasi-isomorphism towards a K-injective
complex, the canonical functor `R Hom(K, -) : D(A) ⥤ D(E, d)` of
`CochainComplex.derivedHomFunctor` exists outright, together with its canonical comparison
`CochainComplex.derivedHomFunctorUnit`, and that comparison exhibits it as a right derived functor
of `Hom(K, -) : K(A) ⥤ D(E, d)` — a left Kan extension along the localization `K(A) ⥤ D(A)`.

The deviation recorded on `CochainComplex.derivedHomFunctor` is not present here: no derivability
of anything is assumed, so in particular the `D(E, d)`-valued functor is not assumed derivable.
The hypothesis is a condition on `A`, and it implies the source's hypothesis by
`CochainComplex.isRightDerivable_homToDerivedCategoryForget_of_exists_isKInjective`.

This is NOT tagged, deliberately. Section 09LJ, the situation Tag 09LK is stated in, assumes only
that `A` is an abelian category; the existence of K-injective resolutions is an extra input on
`A`, strictly stronger than the source's hypothesis, which it implies by Tag 070Y. So this proves
Tag 09LK for an abelian category admitting such resolutions — every Grothendieck abelian one, by
Tag 079P — rather than Tag 09LK as stated. A registration may sit only on a declaration that
proves its tag under the source's own hypotheses, so this one carries no attribute.
-/
theorem derivedHomFunctor_isRightDerivedFunctor_of_exists_isKInjective
    (hres : ∀ X : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : X ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    letI h := isRightDerivable_homToDerivedCategory_of_exists_isKInjective A K hres
    (derivedHomFunctor A K h).IsRightDerivedFunctor (derivedHomFunctorUnit A K h)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  derivedHomFunctor_isRightDerivedFunctor A K _

/-- **Stacks 09LK's exactness, for an abelian category with K-injective resolutions.** Over an
Over an abelian category in which every complex admits a quasi-isomorphism towards a K-injective
complex, Tag 09LK's functor `R Hom(K, -) : D(A) ⥤ D(E, d)` is exact as a functor of triangulated
categories: it commutes with the translation by `CochainComplex.derivedHomFunctorCommShift` and
carries distinguished triangles to distinguished triangles by
`CochainComplex.derivedHomFunctor_isTriangulated`.

This is NOT tagged, deliberately. Section 09LJ, the situation Tag 09LK is stated in, assumes only
that `A` is an abelian category; the existence of K-injective resolutions is an extra input on
`A`, strictly stronger than the source's hypothesis, which it implies by Tag 070Y. So this proves
Tag 09LK for an abelian category admitting such resolutions — every Grothendieck abelian one, by
Tag 079P — rather than Tag 09LK as stated. A registration may sit only on a declaration that
proves its tag under the source's own hypotheses, so this one carries no attribute.
-/
theorem derivedHomFunctor_isTriangulated_of_exists_isKInjective
    (hres : ∀ X : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : X ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    letI h := isRightDerivable_homToDerivedCategory_of_exists_isKInjective A K hres
    letI := derivedHomFunctorCommShift A K h
    (derivedHomFunctor A K h).IsTriangulated :=
  derivedHomFunctor_isTriangulated A K _

variable [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- **Stacks 09LK's reduction clause, for an abelian category with K-injective resolutions.** Over
an abelian
Over an abelian category in which every complex admits a quasi-isomorphism towards a K-injective
complex, Tag 09LK's functor `R Hom(K, -) : D(A) ⥤ D(E, d)` followed by the forgetful functor `D(E,
d) ⥤ D(Ab)` taking associated complexes is a right derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)`:
the construction reduces to the usual one on taking associated complexes of abelian groups.

This is NOT tagged, deliberately. Section 09LJ, the situation Tag 09LK is stated in, assumes only
that `A` is an abelian category; the existence of K-injective resolutions is an extra input on
`A`, strictly stronger than the source's hypothesis, which it implies by Tag 070Y. So this proves
Tag 09LK for an abelian category admitting such resolutions — every Grothendieck abelian one, by
Tag 079P — rather than Tag 09LK as stated. A registration may sit only on a declaration that
proves its tag under the source's own hypotheses, so this one carries no attribute.
-/
theorem derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor_of_exists_isKInjective
    (hres : ∀ X : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : X ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    letI h := isRightDerivable_homToDerivedCategory_of_exists_isKInjective A K hres
    (derivedHomFunctor A K h ⋙
        DifferentialGradedModule.derivedForget (endAlgebra A K)).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedHomFunctorUnit A K h)
          (DifferentialGradedModule.derivedForget (endAlgebra A K)) ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor A K _

end CochainComplex

end
