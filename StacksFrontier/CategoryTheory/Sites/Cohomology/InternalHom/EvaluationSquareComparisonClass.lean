module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StrictlyPerfectHomComparisonClass
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StrictlyPerfectHomComparisonEvaluation

/-! # The left leg of the evaluation square of Tag 0GM7, as a hypercohomology class

The evaluation square of Tag 0GM7 is reduced in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StrictlyPerfectHomComparisonEvaluation`
to its hypothesis `hcurry` at a K-flat source: for complexes `B`, `C` of `O`-modules with `B`
K-flat, a K-flat `P` and a morphism of complexes `p : P ⟶ SheafHom(B, C)` whose class is
invertible, the square is the statement that the bijection of Stacks 08DI carries
`Q p ≫ σ` to the one-sided K-flat comparison of Stacks 06YU followed by the class of the
cochain-level transpose of `p`, where `σ` is the comparison of Stacks 08DM.

The bijection of Stacks 08DI is Stacks 08JA inverted, then degree-zero global hypercohomology of
the currying isomorphism of Stacks 08DJ, then Stacks 08JA again
(`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_globalSections`), so the left-hand side of
the square is determined by the Stacks 08JA *preimage* of `Q p ≫ σ`.  That preimage is what this
file supplies, and it absorbs `p`: the comparison of Stacks 08DM is by construction the class of
a morphism of internal Hom complexes followed by two isomorphisms of `D(O)`, so `Q p ≫ σ` is the
class of **one** morphism of complexes `p ≫ SheafHom(1, 𝜀_C)` followed by those same two
isomorphisms, and `AlgebraicGeometry.RingedSite.derivedGlobalSectionsClassOfHomComp` applies
with `P` in place of `SheafHom(B, C)`.

Consequently the left-hand side of the square is rewritten below as Stacks 08JA of the value of
the currying isomorphism of Stacks 08DJ on an **explicit** class, with no bijection and no
augmentation left in it.

## Main definitions

* `AlgebraicGeometry.RingedSite.precomposedHomComparisonClass`: the degree-zero global
  hypercohomology class of `RSheafHom(QP, RSheafHom(QB, QC))` attached to `Q p ≫ σ`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_precomposedHomComparisonClass`:
  Stacks 08JA carries that class to `Q p ≫ σ`.  This is the companion of
  `RingedSite.derivedSheafHomGlobalSectionsEquiv_strictlyPerfectHomComparisonClass` with the
  source released from `SheafHom(B, C)` to an arbitrary K-flat `P` mapping to it, which is what
  the reduction of the square to a K-flat source asks for.
* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_Q_map_comp_of_globalSectionsEquiv`:
  **the left-hand side of the square, with the bijection of Stacks 08DI eliminated.**  For any
  `σ` and any class `x` that Stacks 08JA carries to `Q p ≫ σ`, the value of the bijection of
  Stacks 08DI at `Q p ≫ σ` is Stacks 08JA of the value of the currying isomorphism of
  Stacks 08DJ on `x`.  The two results compose: `x` is `precomposedHomComparisonClass` and the
  hypothesis is the result above.

## Implementation notes

*The datum `D` is a variable, and the comparison `σ` is a variable too.*  Nothing in the class or
in its Stacks 08JA value uses what the derived internal Hom datum is, so `D` is a variable.  The
second result has to speak about `derivedCurryHomEquiv`, which is built from
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` directly, and writing
`strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) B C` into that statement
**exhausts `maxRecDepth`** (the error lands on the declaration's name column, so it is
the statement and not the proof).  Carrying `σ` and the class as variables with the Stacks 08JA
identification as a *hypothesis* removes the identification entirely, and the two results then
compose at the consumer's instantiation.  This is the discipline of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StrictlyPerfectHomComparisonEvaluation`,
which carries `σ` as a variable for the same reason.

*The last step is `Eq.trans` against the library lemma, not a rewrite into it.*  With the
hypothesis rewritten first (`rw [← hx]; exact derivedCurryHomEquiv_globalSections …`) the closing
`exact` **exhausts `maxRecDepth`**; with that lemma supplied as the second leg of an
`Eq.trans` and the hypothesis discharged afterwards, the same proof checks in seconds.  The
difference is which side of the equation the unifier has to descend into: as the second leg of
`Eq.trans` the lemma's right-hand side is syntactically the goal's, and only the small left leg
is left to prove.

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08DJ](https://stacks.math.columbia.edu/tag/08DJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (D : DerivedInternalHom X)
  (B C P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The Stacks 08JA preimage of `Q p ≫ σ`, where `σ` is the comparison of Stacks 08DM.**  The
comparison is by construction the class of the morphism of internal Hom complexes induced by the
K-injective augmentation `𝜀_C : C ⟶ R C`, followed by two isomorphisms of `D(O)`; so for a
morphism of complexes `p : P ⟶ SheafHom(B, C)` with `P` K-flat, `Q p ≫ σ` is the class of the
single morphism of complexes `p ≫ SheafHom(1, 𝜀_C)` followed by those same two isomorphisms.

This is `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparisonClass` with the source released
from `SheafHom(B, C)` to `P`; at `P = SheafHom(B, C)` and `p = 𝟙` the two agree. -/
def precomposedHomComparisonClass
    (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (hP : Stacks.SheafOfModules.IsKFlat X.O P)
    (p : P ⟶ (sheafHomComplex X B C).obj) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj P))).obj
          ((D.hom.obj (op (DerivedCategory.Q.obj B))).obj (DerivedCategory.Q.obj C))))
      : Type u) :=
  haveI := isKInjective_sheafHomComplex_of_isKFlat X B ((kInjectiveResolution X).obj C) hB
  derivedGlobalSectionsClassOfHomComp X P
    (sheafHomComplex X B ((kInjectiveResolution X).obj C)).obj hP
    (p ≫ homMap X (𝟙 B) ((kInjectiveAugmentation X).app C))
    ((D.homComparison B ((kInjectiveResolution X).obj C)).inv ≫
      inv ((D.hom.obj (op (DerivedCategory.Q.obj B))).map
        (DerivedCategory.Q.map ((kInjectiveAugmentation X).app C))))

/-- **Stacks 08JA carries `precomposedHomComparisonClass` to `Q p ≫ σ`.**  The factorization of
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison` into the class of a morphism of
internal Hom complexes followed by two isomorphisms of `D(O)` is its definition, so this is
`derivedSheafHomGlobalSectionsEquiv_derivedGlobalSectionsClassOfHomComp`
at that factorization precomposed with `p`, and the functoriality of `DerivedCategory.Q`. -/
theorem derivedSheafHomGlobalSectionsEquiv_precomposedHomComparisonClass
    (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (hP : Stacks.SheafOfModules.IsKFlat X.O P)
    (p : P ⟶ (sheafHomComplex X B C).obj) :
    derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj P)
        ((D.hom.obj (op (DerivedCategory.Q.obj B))).obj (DerivedCategory.Q.obj C))
        (precomposedHomComparisonClass X D B C P hB hP p) =
      DerivedCategory.Q.map p ≫ strictlyPerfectHomComparison X D B C := by
  have := isKInjective_sheafHomComplex_of_isKFlat X B ((kInjectiveResolution X).obj C) hB
  refine (derivedSheafHomGlobalSectionsEquiv_derivedGlobalSectionsClassOfHomComp X P
    (sheafHomComplex X B ((kInjectiveResolution X).obj C)).obj hP
    (p ≫ homMap X (𝟙 B) ((kInjectiveAugmentation X).app C)) _).trans ?_
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

/-- **The left-hand side of the evaluation square of Tag 0GM7, with the bijection of Stacks 08DI
eliminated.**  The bijection is Stacks 08JA inverted, then degree-zero global hypercohomology of
the currying isomorphism of Stacks 08DJ, then Stacks 08JA again, so its value at `Q p ≫ σ` is
Stacks 08JA of the value of that isomorphism on the Stacks 08JA preimage of `Q p ≫ σ`, which is
`AlgebraicGeometry.RingedSite.precomposedHomComparisonClass`.

This is what the square still owes, in a form with no bijection and no K-injective augmentation
left in it: the remaining content is the computation of
`AlgebraicGeometry.RingedSite.derivedCurryGlobalEquiv` on that one explicit class. -/
theorem derivedCurryHomEquiv_Q_map_comp_of_globalSectionsEquiv
    (σ : DerivedCategory.Q.obj (sheafHomComplex X B C).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
        (DerivedCategory.Q.obj C))
    (p : P ⟶ (sheafHomComplex X B C).obj)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj P))).obj
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
            (DerivedCategory.Q.obj C)))) : Type u))
    (hx : derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj P)
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
          (DerivedCategory.Q.obj C)) x =
      DerivedCategory.Q.map p ≫ σ) :
    derivedCurryHomEquiv X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj C) (DerivedCategory.Q.map p ≫ σ) =
      derivedSheafHomGlobalSectionsEquiv X
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj B))
        (DerivedCategory.Q.obj C)
        (derivedCurryGlobalEquiv X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj C) x) := by
  refine Eq.trans ?_ (derivedCurryHomEquiv_globalSections X (DerivedCategory.Q.obj P)
    (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) x)
  rw [hx]

end AlgebraicGeometry.RingedSite

end
