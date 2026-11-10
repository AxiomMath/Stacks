module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomKInjective
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomLiftComparison

/-!
# Tag 09LK assembled over a category with K-injective resolutions

Let `A` be an abelian category whose morphisms are sets, let `K` be a cochain complex in `A` and
let `E = End(K)` be its endomorphism differential graded algebra. Tag 09LK asserts three things
at once: that there is a functor `R̃ = R Hom(K, -) : D(A) ⥤ D(E, d)` with the universal property
of a right derived functor of `Hom(K, -) : K(A) ⥤ D(E, d)`, that it is exact, and that composing
it with the forgetful functor `U : D(E, d) ⥤ D(Ab)` recovers the usual abelian-group-valued
derived Hom.

The three are available separately, under the hypothesis that every cochain complex in `A` admits
a quasi-isomorphism towards a K-injective complex, in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomKInjective.lean`. This file puts them
into one statement, and adds the fourth thing the source's third assertion is really about: the
*canonical comparison*

`θ : R Hom(K, -) ⟶ R̃ ⋙ U`

out of the abelian-group-valued derived Hom — the descent of the forgotten unit along the
universal property of `R Hom(K, -) : D(A) ⥤ D(Ab)` — is an isomorphism, honestly so, as an
`IsIso` on that one canonical morphism and as a natural isomorphism built from it.

## What makes `θ` invertible here, and what is avoided

Step 3 of the source's proof passes from the `D(Ab)`-valued hypothesis to the `D(E, d)`-valued
one, which is reflection of essential constancy along `U`. That is false — see
`CategoryTheory.EssentiallyConstantInd.not_reflects_isEssentiallyConstantInd_of_map_eq_zero` and
`CategoryTheory.Functor.exists_fullyFaithful_not_reflecting`, the latter refuting it even for a
full and faithful functor — and nothing here uses it. `U` is not asked to be full, faithful,
conservative, or to reflect anything.

What is used instead is that a K-injective resolution makes the index category of Tag 05S9 have a
weakly terminal object, at which the derived value is attained; the witness is assembled from
index-category data, which is the same category before and after applying `U`, so no morphism is
ever lifted along `U`. Concretely:
`CochainComplex.derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor_of_exists_isKInjective`
gives `R̃ ⋙ U` the left Kan extension property outright, and
`CochainComplex.isIso_derivedHomForgetComparison_of_isRightDerivedFunctor` reads that off `θ`.
In particular the hypothesis `CochainComplex.DerivedHomLiftIdentification` of
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomLiftComparison.lean` is *not* used: it
is equivalent to the conclusion, and is there for constructions of `R̃` that compute the cohomology
of their values rather than arriving with a Kan extension property.

## Main definitions

* `CochainComplex.derivedHomFunctorForgetUnit`: the comparison `β`, the unit of Tag 09LK's
  functor read in `D(Ab)`.
* `CochainComplex.derivedHomFunctorForgetComparison`: **`θ` itself.**
* `CochainComplex.derivedHomFunctorForgetComparisonIsoOfExistsIsKInjective`: `θ` as a natural
  isomorphism `R Hom(K, -) ≅ R̃ ⋙ U`, over a category with K-injective resolutions.

## Main results

* `CochainComplex.isIso_derivedHomFunctorForgetComparison_of_exists_isKInjective`: `θ` is
  invertible.
* `CochainComplex.derivedHom_isRightDerivedFunctor_isTriangulated_isIso_of_exists_isKInjective`:
  **the assembled statement.** From the existence of K-injective resolutions alone, all four of:
  the universal property of `R̃`, its exactness, the reduction of `R̃ ⋙ U` to the usual derived
  Hom, and the invertibility of `θ`.

## Implementation notes

The exactness conjunct is stated against `CategoryTheory.Functor.IsTriangulated`, whose instance
arguments include additivity of the translations of `D(E, d)`. That instance is found through
`CategoryTheory.Localization.pretriangulated` from the pretriangulated structure of the homotopy
category of differential graded modules, and its synthesis fails in this import closure unless
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'` is given priority — the same
local boost that
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomCoproducts.lean` and a dozen other files
of this development carry, for the same reason. Nothing about the statements depends on it.

## What is still owed

The hypothesis is a condition on `A` alone, and it is strictly stronger than the one the source
states — it implies it, by Tag 070Y. So none of these declarations is tagged: Section 09LJ, the
situation Tag 09LK is stated in, assumes only that `A` is an abelian category, and a registration
may sit only on a declaration that proves its tag under the source's own hypotheses. Tag 09LK as
stated remains open here, and the reason is the refutation recorded above, which is a gap in the
source's own argument and not in this development.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), the three assertions
  assembled here; [Tag 09LJ](https://stacks.math.columbia.edu/tag/09LJ), its situation;
  [Tag 070Y](https://stacks.math.columbia.edu/tag/070Y), the right derived functor of an arbitrary
  functor at an object with a K-injective resolution;
  [Tag 05S9](https://stacks.math.columbia.edu/tag/05S9), being defined at an object;
  [Tag 079P](https://stacks.math.columbia.edu/tag/079P), the existence of K-injective resolutions
  in a Grothendieck abelian category.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w w'' w' u

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Abelian A] [HasDerivedCategory.{w'} A]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  (h : (homToDerivedCategory A K).IsRightDerivable
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
  (hf : (homToDerivedCategoryForget A K).IsRightDerivable
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))

/-- **The comparison `β` of Tag 09LK's reduction clause.** The canonical unit
`Hom(K, -) ⟶ Q ⋙ R Hom(K, -)` of Tag 09LK's `D(E, d)`-valued functor, pushed along the forgetful
functor `U : D(E, d) ⥤ D(Ab)` and reassociated, so a comparison
`Hom(K, -) ⟶ Q ⋙ (R̃ ⋙ U)` of functors valued in `D(Ab)`.

This is the unit with respect to which
`CochainComplex.derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor` states the reduction
clause, and the unit `θ` descends. -/
abbrev derivedHomFunctorForgetUnit :
    homToDerivedCategoryForget A K ⟶ DerivedCategory.Qh ⋙
      derivedHomFunctor A K h ⋙ DifferentialGradedModule.derivedForget (endAlgebra A K) :=
  Functor.whiskerRight (derivedHomFunctorUnit A K h)
      (DifferentialGradedModule.derivedForget (endAlgebra A K)) ≫
    (Functor.associator _ _ _).hom

/-- **Tag 09LK's comparison `θ : R Hom(K, -) ⟶ R̃ ⋙ U`.** The abelian-group-valued derived Hom
`R Hom(K, -) : D(A) ⥤ D(Ab)` is a left Kan extension of `Hom(K, -) : K(A) ⥤ D(Ab)` along the
localization; its universal property descends the comparison
`CochainComplex.derivedHomFunctorForgetUnit` to a natural transformation out of it.

Nothing is assumed of `U`: the comparison runs out of the `D(Ab)`-valued functor, not towards
it. -/
abbrev derivedHomFunctorForgetComparison :
    derivedHomForgetFunctor A K hf ⟶
      derivedHomFunctor A K h ⋙ DifferentialGradedModule.derivedForget (endAlgebra A K) :=
  derivedHomForgetComparison A K (DifferentialGradedModule.derivedForget (endAlgebra A K))
    (derivedHomFunctor A K h) hf (derivedHomFunctorForgetUnit A K h)

/-- **Tag 09LK's `θ` is invertible over a category with K-injective resolutions.** If every
cochain complex in `A` admits a quasi-isomorphism towards a K-injective complex, then the
canonical comparison `θ : R Hom(K, -) ⟶ R̃ ⋙ U` out of the abelian-group-valued derived Hom is an
isomorphism.

The proof is a substitution, not an argument: K-injective resolutions already give `R̃ ⋙ U` the
left Kan extension property with unit `β`, by
`CochainComplex.derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor_of_exists_isKInjective`,
and the canonical comparison out of a left Kan extension towards another one is invertible. No
reflection of essential constancy along `U` occurs, and in particular the hypothesis
`CochainComplex.DerivedHomLiftIdentification` is not used.

This is NOT tagged, deliberately: the existence of K-injective resolutions is strictly stronger
than Tag 09LK's own hypothesis, which it implies by Tag 070Y, and Section 09LJ assumes only that
`A` is an abelian category. -/
theorem isIso_derivedHomFunctorForgetComparison_of_exists_isKInjective
    (hres : ∀ X : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : X ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    letI h := isRightDerivable_homToDerivedCategory_of_exists_isKInjective A K hres
    letI hf := isRightDerivable_homToDerivedCategoryForget_of_exists_isKInjective A K hres
    IsIso (derivedHomFunctorForgetComparison A K h hf) :=
  isIso_derivedHomForgetComparison_of_isRightDerivedFunctor A K
    (DifferentialGradedModule.derivedForget (endAlgebra A K)) _ _ _
    (derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor_of_exists_isKInjective A K hres)

/-- **Tag 09LK's `θ` as a natural isomorphism**, over a category with K-injective resolutions:
`R Hom(K, -) ≅ R̃ ⋙ U` in `D(A) ⥤ D(Ab)`, the underlying morphism being the canonical
comparison `CochainComplex.derivedHomFunctorForgetComparison` and nothing else.

This is NOT tagged, deliberately, for the reason recorded on
`CochainComplex.isIso_derivedHomFunctorForgetComparison_of_exists_isKInjective`. -/
def derivedHomFunctorForgetComparisonIsoOfExistsIsKInjective
    (hres : ∀ X : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : X ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    letI h := isRightDerivable_homToDerivedCategory_of_exists_isKInjective A K hres
    letI hf := isRightDerivable_homToDerivedCategoryForget_of_exists_isKInjective A K hres
    derivedHomForgetFunctor A K hf ≅
      derivedHomFunctor A K h ⋙ DifferentialGradedModule.derivedForget (endAlgebra A K) :=
  derivedHomForgetComparisonIsoOfIsRightDerivedFunctor A K
    (DifferentialGradedModule.derivedForget (endAlgebra A K)) _ _ _
    (derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor_of_exists_isKInjective A K hres)

/-- **Stacks 09LK, assembled, for an abelian category with K-injective resolutions.** Let `A` be
an abelian category in which every cochain complex admits a quasi-isomorphism towards a
K-injective complex — every Grothendieck abelian one, by Tag 079P. Then, from that hypothesis
alone, all four of:

* `R̃ = R Hom(K, -) : D(A) ⥤ D(E, d)` of `CochainComplex.derivedHomFunctor`, with its canonical
  comparison, is a right derived functor of `Hom(K, -) : K(A) ⥤ D(E, d)` — a left Kan extension
  along the localization `K(A) ⥤ D(A)`;
* `R̃` is exact, commuting with the translation by `CochainComplex.derivedHomFunctorCommShift` and
  carrying distinguished triangles to distinguished triangles;
* `R̃ ⋙ U`, for `U : D(E, d) ⥤ D(Ab)` the forgetful functor taking associated complexes, is a
  right derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)` with the forgotten unit `β`; and
* the canonical comparison `θ : R Hom(K, -) ⟶ R̃ ⋙ U` out of the abelian-group-valued derived Hom
  is an isomorphism, `CochainComplex.derivedHomFunctorForgetComparisonIsoOfExistsIsKInjective`
  being it as an iso.

The first three conjuncts are the three clauses of
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomKInjective.lean`; the fourth is the one
the source's third assertion is really about, and is the one that would need reflection of
essential constancy along `U` if it were approached from the source's hypothesis instead of from
K-injective resolutions.

This is NOT tagged, deliberately. The hypothesis is a condition on `A` alone and is strictly
stronger than Tag 09LK's own, which it implies by Tag 070Y; Section 09LJ, the situation the tag
is stated in, assumes only that `A` is an abelian category. A registration may sit only on a
declaration that proves its tag under the source's own hypotheses. -/
theorem derivedHom_isRightDerivedFunctor_isTriangulated_isIso_of_exists_isKInjective
    (hres : ∀ X : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : X ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    letI h := isRightDerivable_homToDerivedCategory_of_exists_isKInjective A K hres
    letI hf := isRightDerivable_homToDerivedCategoryForget_of_exists_isKInjective A K hres
    letI := derivedHomFunctorCommShift A K h
    (derivedHomFunctor A K h).IsRightDerivedFunctor (derivedHomFunctorUnit A K h)
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
      (derivedHomFunctor A K h).IsTriangulated ∧
      (derivedHomFunctor A K h ⋙
          DifferentialGradedModule.derivedForget (endAlgebra A K)).IsRightDerivedFunctor
        (derivedHomFunctorForgetUnit A K h)
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
      IsIso (derivedHomFunctorForgetComparison A K h hf) :=
  ⟨derivedHomFunctor_isRightDerivedFunctor_of_exists_isKInjective A K hres,
    derivedHomFunctor_isTriangulated_of_exists_isKInjective A K hres,
    derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor_of_exists_isKInjective A K hres,
    isIso_derivedHomFunctorForgetComparison_of_exists_isKInjective A K hres⟩

/-- **Stacks 09LK, assembled, for a Grothendieck abelian category.** K-injective resolutions
exist there by `Stacks.Injectives.exists_kInjective_resolution_of_grothendieck`, so the previous
statement applies verbatim.

This is NOT tagged, deliberately, for the reason recorded on
`CochainComplex.derivedHom_isRightDerivedFunctor_isTriangulated_isIso_of_exists_isKInjective`. -/
theorem derivedHom_isRightDerivedFunctor_isTriangulated_isIso_of_isGrothendieckAbelian
    [IsGrothendieckAbelian.{w'', 0, u} A] :
    letI hres := Stacks.Injectives.exists_kInjective_resolution_of_grothendieck (C := A)
    letI h := isRightDerivable_homToDerivedCategory_of_exists_isKInjective A K hres
    letI hf := isRightDerivable_homToDerivedCategoryForget_of_exists_isKInjective A K hres
    letI := derivedHomFunctorCommShift A K h
    (derivedHomFunctor A K h).IsRightDerivedFunctor (derivedHomFunctorUnit A K h)
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
      (derivedHomFunctor A K h).IsTriangulated ∧
      (derivedHomFunctor A K h ⋙
          DifferentialGradedModule.derivedForget (endAlgebra A K)).IsRightDerivedFunctor
        (derivedHomFunctorForgetUnit A K h)
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
      IsIso (derivedHomFunctorForgetComparison A K h hf) :=
  derivedHom_isRightDerivedFunctor_isTriangulated_isIso_of_exists_isKInjective A K
    Stacks.Injectives.exists_kInjective_resolution_of_grothendieck

end CochainComplex

end
