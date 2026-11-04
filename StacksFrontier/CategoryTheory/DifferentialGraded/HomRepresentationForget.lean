module

public import StacksFrontier.Algebra.DifferentialGraded.Module.ComplexesHomotopySquare
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedForgetful
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomRepresentation

/-!
# `Hom(x, -)` in `D(ModuleCat R)`, computed on closed degree-zero morphisms

Let `A` be a differential graded category over a commutative ring `R`, let `x` be an object of
`A` and let `H` be the representable differential graded module functor `Hom(x, -)` of
[Stacks, Tag 09LE] with its endomorphism algebra `E = End(x)`. Composing the induced functor on
homotopy classes with the localization of the differential graded `E`-modules at the
quasi-isomorphisms and with the forgetful functor `D(E, d) ⥤ D(ModuleCat R)` gives a functor

`K(A) ⥤ D(ModuleCat R)`,

which is the functor that [Stacks, Tag 09LK] right derives when `A` is the differential graded
category of complexes. This file computes its restriction along `DGCategory.compToK`: it is the
underlying complex of `Hom(x, -)` on closed degree-zero morphisms, read in `D(ModuleCat R)`.

## Why this is not immediate

`DGCategory.HomRepresentation.homotopyFunctor` is pinned by
`DGCategory.HomRepresentation.homotopyFunctor_eq` to be the induced functor on homotopy classes
followed by `(DifferentialGradedModule.homotopyCategoryEquivalence E).inverse`, and that inverse
is manufactured by `CategoryTheory.Functor.asEquivalence` out of essential surjectivity: its
action on objects factors through `Exists.choose`, so it computes on nothing and no amount of
unfolding evaluates it. What replaces unfolding is
`DifferentialGradedModule.complexesQuotientSquareIso`, which transposes that inverse to the other
side of the square and leaves only the comparison of categories of complexes — an honest
hand-built equivalence. The other two steps are then the two factorizations recorded with the
forgetful functor, `DifferentialGradedModule.derivedForgetFactorization` and
`DifferentialGradedModule.forgetHomotopyToDerivedCategoryIso`.

## Main definitions

* `DGCategory.HomRepresentation.forgetSquareIso`: **the identification**, a natural isomorphism
  of functors `Comp(A) ⥤ D(ModuleCat R)`.

## Implementation notes

The base ring's universe and the universe of the morphism modules of `A` are forced equal, since
`DifferentialGradedModule.quasiIsomorphisms'` is stated for a differential graded module whose
underlying module lives in the universe of the base ring. The universe of the *objects* of `A` is
unconstrained. For the differential graded category of complexes in a category with morphisms in
`Type 0` over `R = ℤ` both are `0`, so the condition is vacuous there.

## References

* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE), the functor
  `Hom(x, -)`; [Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), which right derives it.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule

namespace DGCategory.HomRepresentation

universe w v u

variable {R : Type u} [CommRing R] {A : DGCategory.{u, v, u} R} {x : A.Obj}
  (H : HomRepresentation A x) [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- **`Hom(x, -)` in `D(ModuleCat R)`, on closed degree-zero morphisms.** Restricted along the
canonical functor from the category of complexes to the homotopy category, the composite of the
induced functor on homotopy classes with the localization at the quasi-isomorphisms and the
forgetful functor `D(E, d) ⥤ D(ModuleCat R)` is the underlying complex of `Hom(x, -)`, read in
`D(ModuleCat R)`. -/
def forgetSquareIso :
    DGCategory.compToK A ⋙ H.homotopyFunctor ⋙ (quasiIsomorphisms' H.algebra).Q ⋙
        derivedForget H.algebra ≅
      H.complexesFunctor ⋙ forgetToCochainComplex H.algebra ⋙ DerivedCategory.Q := by
  have key : DGCategory.compToK A ⋙ H.homotopyFunctor ≅
      H.complexesFunctor ⋙ toHomotopyCategory H.algebra := by
    rw [H.homotopyFunctor_eq, H.complexesFunctor_eq]
    exact Functor.isoWhiskerLeft H.functor.onComp
      (complexesQuotientSquareIso H.algebra).symm
  have step : toHomotopyCategory H.algebra ⋙ (quasiIsomorphisms' H.algebra).Q ⋙
      derivedForget H.algebra ≅ forgetToCochainComplex H.algebra ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft (toHomotopyCategory H.algebra)
        (derivedForgetFactorization H.algebra) ≪≫
      forgetHomotopyToDerivedCategoryIso H.algebra
  exact Functor.isoWhiskerRight key
      ((quasiIsomorphisms' H.algebra).Q ⋙ derivedForget H.algebra) ≪≫
    Functor.isoWhiskerLeft H.complexesFunctor step

end DGCategory.HomRepresentation

end
