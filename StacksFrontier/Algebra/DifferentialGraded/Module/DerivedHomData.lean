module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomDerivedTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomVariant

/-!
# The data Tag 09LK asks for, packaged, and the single implication it still rests on

Let `A` be an abelian category with a chosen derived category, let `K` be a cochain complex in
`A` and let `E = End(K)` be its endomorphism differential graded algebra. Tag 09LK asserts that
if the right derived functor of the **abelian-group-valued** `Hom(K, -) : K(A) ⥤ D(Ab)` is
everywhere defined, then there is a canonical exact functor
`R Hom(K, -) : D(A) ⥤ D(E, d)` which reduces to the usual one on taking associated complexes.

This file packages that conclusion as two structures — one for the forgetful functor
`D(E, d) ⥤ D(Ab)` that the phrase *on taking associated complexes* refers to, one for the exact
functor itself — and settles the first of them outright. For the second, every field is
constructed from the declarations already available in this tree, under the hypothesis that the
**differential-graded-module-valued** `Hom(K, -) : K(A) ⥤ D(E, d)` is everywhere right
derivable. The gap between the two hypotheses is isolated as a single named predicate,
`CochainComplex.ReflectsHomDerivability`, and nothing else is missing: granted it, the whole of
Tag 09LK's conclusion follows from the tag's own hypothesis.

## Main definitions

* `DifferentialGradedModule.DerivedForgetData`: a forgetful functor `D(A, d) ⥤ D(ModuleCat R)`
  together with the identification of its value on an ordinary differential graded module with
  the underlying complex of that module. This is the first datum Tag 09LK's conclusion refers
  to.
* `CochainComplex.DerivedHomData`: the functor `R Hom(K, -) : D(A) ⥤ D(E, d)` together with
  everything Tag 09LK asserts about it — its commutation with the translation, its exactness,
  its canonical comparison with `Hom(K, -)` on the homotopy category, the universal property
  exhibiting it as a right derived functor, and the same universal property after taking
  associated complexes.
* `CochainComplex.ReflectsHomDerivability`: the implication from everywhere-definedness of the
  right derived functor of the `D(Ab)`-valued `Hom(K, -)` to that of the `D(E, d)`-valued one.
  This is the one statement separating what is proved here from Tag 09LK.

## Main results

* `DifferentialGradedModule.derivedForgetData`: **the forgetful functor datum exists**, with no
  hypothesis beyond a differential graded algebra and a chosen derived category of complexes of
  modules over its base ring. It is `DifferentialGradedModule.derivedForget`, and the
  identification is the composite of its two descents.
* `CochainComplex.derivedHomData`: **all of Tag 09LK's data, from the `D(E, d)`-valued
  derivability hypothesis.** Every one of the six fields is discharged.
* `CochainComplex.derivedHomData_of_reflectsHomDerivability`: **Tag 09LK, granted
  `CochainComplex.ReflectsHomDerivability`.** From the tag's own hypothesis — right derivability
  of the `D(Ab)`-valued functor — and that implication, the whole package follows.

## Implementation notes

*What is open.* `CochainComplex.ReflectsHomDerivability` is not proved here and is not known to
this development. Being right derivable at `X` means Deligne's ind-object
`(s : X ⟶ X') ↦ Hom(K, X')` is essentially constant, so the predicate asks for essential
constancy of an ind-object in `D(E, d)` to be *reflected* from its image in `D(Ab)`. What this
tree has towards that is: reflection along a functor that is full and faithful with idempotent-
complete source, `CategoryTheory.Functor.IsRightDerivable.of_comp`, which does not apply because
the forgetful functor is neither full nor faithful; reflection of *eventual* constancy along any
conservative functor, `CategoryTheory.EssentiallyConstantInd.isEventuallyConstantFrom_of_comp`,
which does apply to the forgetful functor by
`DifferentialGradedModule.derivedForget_reflectsIsomorphisms` but concludes about the wrong
property, essential constancy of a filtered ind-object being strictly weaker than eventual
constancy; and a conservative functor for which the reflection fails,
`CategoryTheory.Functor.isRightDerivable_comp_and_not_isRightDerivable_of_map_eq_zero`. That
last one is not a refutation of the predicate below: its functor is not the forgetful functor of
a differential graded algebra, and is neither additive nor exact. The predicate is open in both
directions.

*The converse direction is unconditional,* and is
`CochainComplex.isRightDerivable_homToDerivedCategoryForget`: derivability of the `D(E, d)`-valued
functor implies derivability of the `D(Ab)`-valued one, because a value of a right derived
functor is carried along postcomposition with an arbitrary functor.

*Universes, and the restriction this file carries.* Tag 09LJ's situation is only *let `A` be an
abelian category*, with no condition on size. The statements below take `A : Type u` with
`[Category.{0} A]`, so the objects of `A` are in an arbitrary universe but its morphisms are in
`Type 0`. The restriction is not about `A`: it comes from the differential graded tree being
written at the single-universe encoding, in which a differential graded algebra over `R : Type u`
has its carrier in `Type u` and its modules have underlying complexes of `ModuleCat.{u} R` — see
the universe note of `StacksFrontier/Algebra/DifferentialGraded/Module/DerivedForgetful.lean`. The
base ring here is `ℤ : Type 0`, so the carrier of `E = End(K)` must be in `Type 0`, and the
carrier of `E` is the morphism complex `Hom(K, K)` of `A`. Removing the restriction is a change
to the encoding of differential graded modules, not to anything below.

## References

* [The Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
* [The Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE)
-/

@[expose] public noncomputable section

open CategoryTheory

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe w u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- **The forgetful functor `D(A, d) ⥤ D(Ab)` of Tag 09LK, as a datum.** A functor from the
derived category of right differential graded `A`-modules to the derived category of complexes
of modules over the base ring, together with the identification of its value on an ordinary
differential graded module — read in `D(A, d)` through the homotopy category — with the
underlying complex of that module.

The identification is what pins the functor down: it is the phrase *on taking associated
complexes* in Tag 09LK's conclusion. -/
structure DerivedForgetData where
  /-- The forgetful functor on derived categories. -/
  functor : derivedCategory' A ⥤ DerivedCategory (ModuleCat.{u} R)
  /-- Its value on an ordinary differential graded module is the underlying complex. -/
  factorization :
    toHomotopyCategory.{u, u, u} A ⋙ (quasiIsomorphisms' A).Q ⋙ functor ≅
      forgetToCochainComplex A ⋙ DerivedCategory.Q

/-- **The forgetful functor datum of Tag 09LK exists**, with no hypothesis beyond a differential
graded algebra over a commutative ring and a chosen derived category of complexes of modules
over that ring.

The functor is `DifferentialGradedModule.derivedForget`, the underlying-complex functor descended
through the quotient by homotopy and then through the localization at the quasi-isomorphisms, and
the identification is the composite of those two descents,
`DifferentialGradedModule.derivedForgetFactorization` and
`DifferentialGradedModule.forgetHomotopyToDerivedCategoryIso`. -/
@[stacks 09LK "the forgetful functor D(E, d) ⥤ D(Ab) of the conclusion, together with the \
identification of its value on an ordinary differential graded module with the underlying \
complex of that module, which is the phrase `on taking associated complexes`"]
def derivedForgetData : DerivedForgetData A where
  functor := derivedForget A
  factorization :=
    Functor.isoWhiskerLeft (toHomotopyCategory.{u, u, u} A) (derivedForgetFactorization A) ≪≫
      forgetHomotopyToDerivedCategoryIso A

/-- The functor of `DifferentialGradedModule.derivedForgetData A` is
`DifferentialGradedModule.derivedForget A`. -/
@[simp]
theorem derivedForgetData_functor : (derivedForgetData A).functor = derivedForget A := rfl

end DifferentialGradedModule

namespace CochainComplex

universe w'

variable (A : Type u) [Category.{0} A] [Abelian A] [HasDerivedCategory.{w'} A]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- **The conclusion of Tag 09LK, as a datum.** For `K` a cochain complex in an abelian category
`A` and `E = End(K)` its endomorphism differential graded algebra: the canonical functor
`R Hom(K, -) : D(A) ⥤ D(E, d)`, together with everything the tag asserts about it.

The six fields are the tag's conclusion read clause by clause. The functor itself; that it
commutes with the translation and is exact, which together say it is *an exact functor of
triangulated categories*; its canonical comparison with `Hom(K, -)` on the homotopy category, and
the universal property saying that the comparison exhibits it as the *right derived functor*
`R Hom(K, -)`; and finally the same universal property after composing with the forgetful functor
`D(E, d) ⥤ D(Ab)`, which is the clause that the construction *reduces to the usual one on taking
associated complexes*. -/
structure DerivedHomData where
  /-- The functor `R Hom(K, -) : D(A) ⥤ D(E, d)`. -/
  functor : DerivedCategory A ⥤ DifferentialGradedModule.derivedCategory' (endAlgebra A K)
  /-- It commutes with the translation. -/
  commShift : functor.CommShift ℤ
  /-- It is exact as a functor of triangulated categories. -/
  exact : letI := commShift; functor.IsTriangulated
  /-- The canonical comparison with `Hom(K, -) : K(A) ⥤ D(E, d)`. -/
  comparison : homToDerivedCategory A K ⟶ DerivedCategory.Qh ⋙ functor
  /-- The comparison exhibits the functor as the right derived functor of `Hom(K, -)`. -/
  isRightDerived :
    functor.IsRightDerivedFunctor comparison (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  /-- On taking associated complexes the construction reduces to the usual derived Hom: after
  the forgetful functor `D(E, d) ⥤ D(Ab)` it is a right derived functor of
  `Hom(K, -) : K(A) ⥤ D(Ab)`. -/
  underlyingIsRightDerived :
    (functor ⋙ DifferentialGradedModule.derivedForget (endAlgebra A K)).IsRightDerivedFunctor
      (Functor.whiskerRight comparison
          (DifferentialGradedModule.derivedForget (endAlgebra A K)) ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- **All of Tag 09LK's data, from right derivability of the `D(E, d)`-valued `Hom(K, -)`.**
Every field is discharged: the functor is `CochainComplex.derivedHomFunctor`, the commutation
with the translation is `CochainComplex.derivedHomFunctorCommShift`, the exactness is
`CochainComplex.derivedHomFunctor_isTriangulated`, the comparison is
`CochainComplex.derivedHomFunctorUnit`, the universal property is
`CochainComplex.derivedHomFunctor_isRightDerivedFunctor` and the reduction to the usual derived
Hom is `CochainComplex.derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor`.

This is NOT tagged. Tag 09LK assumes right derivability of the **abelian-group-valued**
`Hom(K, -) : K(A) ⥤ D(Ab)`; this declaration assumes it of the **differential-graded-module-
valued** `Hom(K, -) : K(A) ⥤ D(E, d)`. The former follows from the latter, by
`CochainComplex.isRightDerivable_homToDerivedCategoryForget`; the converse is
`CochainComplex.ReflectsHomDerivability`, which is open. So the hypothesis here is not known to
be the tag's own, and a registration may sit only on a declaration proving its tag under the
source's hypotheses. -/
def derivedHomData
    (h : (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    DerivedHomData A K where
  functor := derivedHomFunctor A K h
  commShift := derivedHomFunctorCommShift A K h
  exact := derivedHomFunctor_isTriangulated A K h
  comparison := derivedHomFunctorUnit A K h
  isRightDerived := derivedHomFunctor_isRightDerivedFunctor A K h
  underlyingIsRightDerived := derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor A K h

/-- The functor of `CochainComplex.derivedHomData A K h` is
`CochainComplex.derivedHomFunctor A K h`. -/
@[simp]
theorem derivedHomData_functor
    (h : (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    (derivedHomData A K h).functor = derivedHomFunctor A K h := rfl

/-- The comparison of `CochainComplex.derivedHomData A K h` is
`CochainComplex.derivedHomFunctorUnit A K h`. -/
@[simp]
theorem derivedHomData_comparison
    (h : (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    (derivedHomData A K h).comparison = derivedHomFunctorUnit A K h := rfl

/-- **The one implication separating this development from Tag 09LK.** If the right derived
functor of the abelian-group-valued `Hom(K, -) : K(A) ⥤ D(Ab)` — the composite of the
differential-graded-module-valued one with the forgetful functor — is defined at every object of
`K(A)`, then so is the right derived functor of the differential-graded-module-valued
`Hom(K, -) : K(A) ⥤ D(E, d)`.

Being defined at `X` means Deligne's ind-object `(s : X ⟶ X') ↦ Hom(K, X')` is essentially
constant, so this asks essential constancy of an ind-object in `D(E, d)` to be reflected from
its image in `D(Ab)`. The reverse implication is unconditional and is
`CochainComplex.isRightDerivable_homToDerivedCategoryForget`. This direction is open: it is the
step Tag 09LK's own proof takes, justified there by compatibility of the forgetful functor with
cohomology, which yields exactly its conservativity,
`DifferentialGradedModule.isIso_iff_isIso_derivedForget_map`, and conservativity alone does not
suffice — see the implementation notes of this file. -/
def ReflectsHomDerivability : Prop :=
  (homToDerivedCategoryForget A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) →
    (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- **Tag 09LK, granted `CochainComplex.ReflectsHomDerivability`.** From the tag's own
hypothesis — that the right derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)` is everywhere defined
— and that one implication, the whole of the tag's conclusion follows: the canonical exact
functor `R Hom(K, -) : D(A) ⥤ D(E, d)` with its comparison, its universal property, and its
reduction to the usual derived Hom on associated complexes.

This is NOT tagged, because `CochainComplex.ReflectsHomDerivability` is an extra hypothesis
beyond the tag's. It records that nothing else is missing. -/
def derivedHomData_of_reflectsHomDerivability (hrefl : ReflectsHomDerivability A K)
    (h : (homToDerivedCategoryForget A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    DerivedHomData A K :=
  derivedHomData A K (hrefl h)

omit [HasDerivedCategory A] in
/-- `CochainComplex.ReflectsHomDerivability` is exactly the converse of the unconditional
implication `CochainComplex.isRightDerivable_homToDerivedCategoryForget`: together they would
make the two derivability hypotheses of Tag 09LK equivalent. -/
theorem reflectsHomDerivability_iff_iff :
    ReflectsHomDerivability A K ↔
      ((homToDerivedCategoryForget A K).IsRightDerivable
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ↔
        (homToDerivedCategory A K).IsRightDerivable
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :=
  ⟨fun hrefl => ⟨hrefl, isRightDerivable_homToDerivedCategoryForget A K _⟩, fun h => h.1⟩

end CochainComplex

end
