module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomVariant
public import StacksFrontier.CategoryTheory.Functor.Derived.EverywhereDefinedTriangulated
public import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology of a value of derived Hom is a colimit of cohomology of Hom complexes

Let `B` be a preadditive category whose morphisms are sets, let `K` be a cochain complex in `B`
and let `W` be a class of morphisms of the homotopy category `K(B)`. The functor
`Hom(K, -) : K(B) ⥤ D(Ab)` of
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomVariant.lean` is the one whose right
derived functor Tag 09LK assumes to be everywhere defined; being defined at an object `X` means,
by Tag 05S9, that the ind-object `(s : X ⟶ Y) ↦ Hom(K, Y)` indexed by `X/W` is essentially
constant, with the value exhibited by a cocone.

This file records what taking cohomology does to such a value. Essential constancy of an
ind-object is preserved by postcomposition with an *arbitrary* functor, by Tag 05SH, so for every
`n` the image of the exhibiting cocone under `H^n` exhibits a value of the right derived functor
of `H^n Hom(K, -)`, and in particular is a colimit cocone:

`H^n` of the value at `X` `= colim_{(s : X ⟶ Y) ∈ X/W} H^n Hom(K, Y)`.

Nothing is assumed of `H^n`, of `W`, or of the ambient categories beyond what the functor itself
needs. The point is the direction: the witness moves *forwards* along a functor. Nothing here
transports a witness backwards, and nothing here needs to; the three routes through reflection of
essential constancy, and the reasons each is closed, are recorded in
`StacksFrontier/CategoryTheory/Functor/Derived/ValueReflection.lean` and
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomEventualConstancy.lean`.

## Main results

* `CochainComplex.isRightDerivedValueAt_homToDerivedCategoryForget_comp_homologyFunctor`: a
  cocone exhibiting a value of the right derived functor of `Hom(K, -) : K(B) ⥤ D(Ab)` at `X` is
  carried by `H^n` to a cocone exhibiting a value of the right derived functor of
  `H^n Hom(K, -) : K(B) ⥤ Mod_ℤ` at `X`.
* `CochainComplex.isColimitMapCoconeHomologyFunctor`: consequently that image cocone is a colimit
  cocone, which is the displayed formula — the degree-`n` cohomology of the value is the colimit
  over `X/W` of the degree-`n` cohomology of the Hom complexes.
* `CochainComplex.isColimitMapCoconeHomologyType`: the same colimit read in types and lifted to an
  arbitrary universe, which is the form in which it is compared with a colimit of morphism sets.
* `CochainComplex.isRightDerivedValueAt_derivedHomForgetUnitCocone`: under Tag 09LK's own
  hypothesis the comparison cocone at `X`, whose vertex is the value `R Hom(K, -)(Q(X))` of the
  assembled functor, is a value of the right derived functor in the sense of Tag 05S9. This is
  what lets the two statements above be read at the assembled functor rather than at an
  unspecified cocone.

## Main definitions

* `CochainComplex.derivedHomForgetFunctor`: the abelian-group-valued derived Hom
  `R Hom(K, -) : D(A) ⥤ D(Ab)`, constructed from Tag 09LK's own hypothesis — everywhere-definedness
  of the right derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)` — and from nothing stronger.
* `CochainComplex.derivedHomForgetFunctorUnit`: its canonical comparison
  `Hom(K, -) ⟶ Qh ⋙ R Hom(K, -)`.

## Implementation notes

*Which hypothesis is assumed.* The functor assembled here is the abelian-group-valued one, and
the hypothesis assumed of it is everywhere-definedness of *its own* right derived functor, which
is the hypothesis Tag 09LK states. This is weaker than the corrected hypothesis under which
`CochainComplex.derivedHomFunctor` of
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomVariant.lean` produces the
differential-graded-module-valued functor; by
`CochainComplex.isRightDerivable_homToDerivedCategoryForget_quasiIso` the corrected hypothesis
implies this one, so everything here applies in that case too, and the implication is not used in
the other direction.

*Why the universe lift.* The colimit of `CochainComplex.isColimitMapCoconeHomologyFunctor` is a
colimit of `ℤ`-modules whose carriers are sets, that is, it lives in the universe of the
morphisms of `B`. The colimit it is to be compared with is a colimit of morphism sets of a
localization of `K(B)`, which lives in the universe of the morphisms of that localization, and
the two universes are independent. `CochainComplex.isColimitMapCoconeHomologyType` therefore
composes with the forgetful functor to types and with `CategoryTheory.uliftFunctor`, which
preserves colimits of every size; the lift is performed on the *functor* being applied to the
value, so it is again an instance of the same preservation statement and needs no further
argument.

*Why the class of morphisms is arbitrary.* Nothing in the proof uses that `W` is the class of
quasi-isomorphisms, so the statements are made for an arbitrary class, as are the reduction
clauses of `StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomVariant.lean`.

## References

* [Stacks Project, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9), being defined at an
  object; [Tag 05PT](https://stacks.math.columbia.edu/tag/05PT) and
  [Tag 05SH](https://stacks.math.columbia.edu/tag/05SH), the preservation of essential constancy
  by an arbitrary functor; [Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose hypothesis
  is everywhere-definedness of the functor considered here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace CochainComplex

variable (B : Type u) [Category.{0} B] [Preadditive B] (K : CochainComplex B ℤ)
  [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  (W : MorphismProperty (HomotopyCategory B (ComplexShape.up ℤ)))

/-- **Cohomology preserves a value of the right derived functor of `Hom(K, -)`.** If the cocone
`c` exhibits a value at `X` of the right derived functor of the abelian-group-valued
`Hom(K, -) : K(B) ⥤ D(Ab)` in the sense of Tag 05S9, then its image under `H^n` exhibits a value
at `X` of the right derived functor of `H^n Hom(K, -)`.

This is Tag 05SH: essential constancy of an ind-object is preserved by postcomposition with an
arbitrary functor, so no property of `H^n` is used. -/
theorem isRightDerivedValueAt_homToDerivedCategoryForget_comp_homologyFunctor (n : ℤ)
    {X : HomotopyCategory B (ComplexShape.up ℤ)}
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙
      homToDerivedCategoryForget B K)}
    (h : (homToDerivedCategoryForget B K).IsRightDerivedValueAt W X c) :
    (homToDerivedCategoryForget B K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).IsRightDerivedValueAt W X
      ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).mapCocone c) :=
  h.comp _

/-- **The cohomology of a value of derived Hom, as a colimit.** The image under `H^n` of a cocone
exhibiting a value at `X` of the right derived functor of `Hom(K, -) : K(B) ⥤ D(Ab)` is a colimit
cocone: the degree-`n` cohomology of the value is the colimit over `X/W` of the degree-`n`
cohomology of the Hom complexes `Hom(K, Y)`. -/
def isColimitMapCoconeHomologyFunctor (n : ℤ)
    {X : HomotopyCategory B (ComplexShape.up ℤ)}
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙
      homToDerivedCategoryForget B K)}
    (h : (homToDerivedCategoryForget B K).IsRightDerivedValueAt W X c) :
    IsColimit ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).mapCocone c) :=
  (isRightDerivedValueAt_homToDerivedCategoryForget_comp_homologyFunctor B K W n h).isColimit

/-- The colimit of `CochainComplex.isColimitMapCoconeHomologyFunctor` read in types and lifted to
an arbitrary universe `v`: the underlying set of the degree-`n` cohomology of the value at `X` is
the colimit over `X/W` of the underlying sets of the degree-`n` cohomology of the Hom complexes.

The lift is there so that this colimit can be compared with a colimit of morphism sets of a
localization of `K(B)`, whose universe is independent of that of the morphisms of `B`. -/
def isColimitMapCoconeHomologyType (n : ℤ)
    {X : HomotopyCategory B (ComplexShape.up ℤ)}
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙
      homToDerivedCategoryForget B K)}
    (h : (homToDerivedCategoryForget B K).IsRightDerivedValueAt W X c) :
    IsColimit ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n ⋙
      forget (ModuleCat.{0} ℤ) ⋙ uliftFunctor.{v}).mapCocone c) :=
  (h.comp _).isColimit

end CochainComplex

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Abelian A] [HasDerivedCategory.{v} A]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

omit [HasDerivedCategory A] in
/-- Tag 09LK's own hypothesis in the form Mathlib's Kan extensions need: if the right derived
functor of the abelian-group-valued `Hom(K, -) : K(A) ⥤ D(Ab)` is defined at every object of
`K(A)`, then that functor has a left Kan extension along the localization at the
quasi-isomorphisms. -/
theorem hasRightDerivedFunctor_homToDerivedCategoryForget
    (h : (homToDerivedCategoryForget A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    (homToDerivedCategoryForget A K).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  have := (homToDerivedCategoryForget A K).hasPointwiseRightDerivedFunctor_of_isRightDerivable
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) h
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor
    (homToDerivedCategoryForget A K) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- **The abelian-group-valued derived Hom of Tag 09LK's hypothesis.** The canonical functor
`R Hom(K, -) : D(A) ⥤ D(Ab)`, for `K` a cochain complex in an abelian category `A`: the right
derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)` along the localization `K(A) ⥤ D(A)` at the
quasi-isomorphisms, constructed from everywhere-definedness of that right derived functor and
from nothing stronger. -/
def derivedHomForgetFunctor
    (h : (homToDerivedCategoryForget A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    DerivedCategory A ⥤ DerivedCategory (ModuleCat.{0} ℤ) :=
  have := hasRightDerivedFunctor_homToDerivedCategoryForget A K h
  (homToDerivedCategoryForget A K).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- The canonical comparison `Hom(K, -) ⟶ Qh ⋙ R Hom(K, -)` exhibiting
`CochainComplex.derivedHomForgetFunctor` as the right derived functor. -/
def derivedHomForgetFunctorUnit
    (h : (homToDerivedCategoryForget A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    homToDerivedCategoryForget A K ⟶
      DerivedCategory.Qh ⋙ derivedHomForgetFunctor A K h :=
  have := hasRightDerivedFunctor_homToDerivedCategoryForget A K h
  (homToDerivedCategoryForget A K).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- The universal property pinning down `CochainComplex.derivedHomForgetFunctor`: together with
its canonical comparison it is a right derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)`, i.e. a left
Kan extension along the localization `K(A) ⥤ D(A)`. -/
theorem derivedHomForgetFunctor_isRightDerivedFunctor
    (h : (homToDerivedCategoryForget A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    (derivedHomForgetFunctor A K h).IsRightDerivedFunctor (derivedHomForgetFunctorUnit A K h)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  have := hasRightDerivedFunctor_homToDerivedCategoryForget A K h
  inferInstanceAs
    (((homToDerivedCategoryForget A K).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).IsRightDerivedFunctor
      ((homToDerivedCategoryForget A K).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))

/-- The comparison cocone at `X` of Tag 05S9 for the abelian-group-valued derived Hom: its vertex
is the value `R Hom(K, -)(Q(X))` of `CochainComplex.derivedHomForgetFunctor` and its leg at
`(s : X ⟶ Y)` is the canonical comparison at `Y` followed by the inverse of the isomorphism
`Q(s)`. -/
abbrev derivedHomForgetUnitCocone
    (h : (homToDerivedCategoryForget A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    Cocone (MorphismProperty.Under.forget
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
      Under.forget X ⋙ homToDerivedCategoryForget A K) :=
  Functor.derivedUnitCocone (homToDerivedCategoryForget A K)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh
    (derivedHomForgetFunctor A K h) (derivedHomForgetFunctorUnit A K h) X

/-- **Under Tag 09LK's own hypothesis the assembled functor computes the values.** The comparison
cocone at `X`, whose vertex is `R Hom(K, -)(Q(X))`, is a value of the right derived functor of
`Hom(K, -) : K(A) ⥤ D(Ab)` at `X` in the sense of Tag 05S9. -/
theorem isRightDerivedValueAt_derivedHomForgetUnitCocone
    (h : (homToDerivedCategoryForget A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    (homToDerivedCategoryForget A K).IsRightDerivedValueAt
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) X
      (derivedHomForgetUnitCocone A K h X) :=
  have := derivedHomForgetFunctor_isRightDerivedFunctor A K h
  Functor.isRightDerivedValueAt_derivedUnitCocone (homToDerivedCategoryForget A K)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh
    (derivedHomForgetFunctor A K h) (derivedHomForgetFunctorUnit A K h) h X

end CochainComplex

end
