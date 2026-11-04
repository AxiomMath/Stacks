module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedCochainComplex
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedEvaluation
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomReflector
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaHomCohomology

/-!
# The cohomology of the forgetful image of a derived right module, explicitly

Step 3 of the replacement proof of [Stacks, Tag 09LK]
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomLiftComparison.lean`) asks for an
identification `φ` whose source is

`H^n(U(R̃(q X)))`,

the degree-`n` homology, taken in `D(ModuleCat R)`, of the forgetful image of a value of the
lift. The chain that computes it
(`DGCategory.RightModule.chainEquivReflectorEvaluation`) starts instead from the *explicit*
cohomology `DGCategory.RightModule.gradedCohomology` of a right differential graded module —
cocycles modulo coboundaries of the complex `M X` — because that is what the differential graded
Yoneda lemma identifies with a Hom group of the homotopy category.

This file identifies the two. It is pure bookkeeping about three existing identifications, and it
assumes nothing: no hypothesis on the differential graded category beyond the existence of the
derived category of complexes of `R`-modules, and in particular nothing from Tag 09LK.

## The three identifications composed

* `DGCategory.RightModule.derivedEvaluationForgetCompIso`: restricting
  `ev_X : D(C) ⥤ D(ModuleCat R)` along the quotient functor of `D(C)` gives evaluation at `X`
  followed by the localization of complexes of `R`-modules;
* `DerivedCategory.homologyFunctorFactorsh` and
  `HomotopyCategory.homologyFunctorFactors`: the homology of the derived category is the homology
  of the complex;
* `DGCategory.RightModule.gradedCohomologyIso`: the homology of the complex `M X` is the
  degree-`n` cocycles of `M X` modulo the coboundaries.

Only the first is specific to differential graded modules; the other two are Mathlib's and this
file's own earlier bookkeeping.

## Main definitions

* `DGCategory.RightModule.derivedEvaluationForgetHomologyIso`: **the identification at the level
  of functors**, so that its naturality is available by `NatTrans.naturality` rather than being
  reproved. This is the form the assembly of `(*)` needs: the identification has to be natural in
  the module variable for the naturality clause of
  `CochainComplex.derivedHomLiftIdentificationOfNaturality` to be discharged by whiskering.
* `DGCategory.RightModule.derivedForgetGradedCohomologyIso`: **the identification of the two
  groups**, `H^n(ev_X (Q_C M)) ≅ H^n(M X)` with the right-hand side the explicit cohomology.
* `DGCategory.RightModule.endDerivedForgetGradedCohomologyIso`: the same at the one-object
  differential graded category `E = C(K, K)` and the forgetful functor
  `DGCategory.endDerivedForget` out of `D(E)`, which is the `U` of step 3. Its right-hand side is
  literally the source of `DGCategory.RightModule.chainEquivReflectorEvaluation`.
* `DGCategory.derivedHomReflectorGradedCohomologyIso`: **the junction on the source**, at the
  `R̃` that steps 1 and 2 produce: `H^n(U(R̃(q X))) ≅ H^n(ev_K (L (Φ X)))`.

## What is still owed

This settles the *source* of `(*)`, and nothing else. Two things remain, and neither is here:

* the target. The chain lands in a Hom group of a localization of `K(C)` at `Φ⁻¹ N`; step 3 asks
  for one of `D(A)`. For `C = Comp^dg(A)` the identification of the two subcategories is
  `DGCategory.RightModule.yonedaInverseImage_eq_of_isTriangulated`, but reading a localization of
  `K(C)` as `D(A)` also needs the comparison of `K(C)` with `K(A)`,
  `CochainComplex.homotopyCategoryEquivalence`, carried through the shift.
* the elementwise formula `unit_app_id` of
  `CochainComplex.derivedHomLiftIdentificationOfNaturality`: that the composite agrees with Tag
  09LC's identification on the image of the comparison `β`. That is the mathematics of the
  replacement proof, and it is not proved in this development.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public noncomputable section

namespace DGCategory

universe w v u v₁ v₂ r

open CategoryTheory CategoryTheory.Limits

namespace RightModule

variable {R : Type r} [CommRing R] (C : DGCategory.{v, u} R)
  [HasDerivedCategory.{w} (ModuleCat.{v} R)]

attribute [local implicit_reducible] DGCategory.K

/-- **The cohomology of the forgetful image, as an isomorphism of functors on
`K(Mod^dg(C))`.** Taking the degree-`n` homology in `D(ModuleCat R)` of the forgetful image
`ev_X : D(C) ⥤ D(ModuleCat R)` of the class of a right differential graded module is taking the
degree-`n` homology of the complex `M X` in the homotopy category of complexes of `R`-modules.

Stated between functors rather than objects on purpose: the identification `(*)` that step 3 of
[Stacks, Tag 09LK] consumes has a naturality clause
(`CochainComplex.derivedHomLiftIdentificationOfNaturality`), and discharging it by whiskering
needs every link of the identification to be natural in the module variable. -/
def derivedEvaluationForgetHomologyIso (X : C.Obj) (n : ℤ) :
    derivedQ C ⋙ derivedEvaluationForget C X ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{v} R) n ≅
      cochainComplexOnK.{v} X ⋙
        HomotopyCategory.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedEvaluationForgetCompIso C X)
        (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n) ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (cochainComplexOnK.{v} X)
          (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{v} R) n)

/-- **The cohomology of the forgetful image of a derived right differential graded module is the
explicit cohomology of its complex.** For `M` an object of `K(Mod^dg(C))` and `X` an object of
`C`, the degree-`n` homology of `ev_X (Q_C M)` in `D(ModuleCat R)` is the module of degree-`n`
cocycles of the complex `M X` modulo the degree-`n` coboundaries.

The left-hand side is the source of the identification `φ` of
`CochainComplex.DerivedHomLiftIdentification`; the right-hand side is the source of the chain
`DGCategory.RightModule.chainEquivReflectorEvaluation`. Nothing is assumed: this is the
composition of `DGCategory.RightModule.derivedEvaluationForgetHomologyIso` with the comparison of
the homotopy category with the category of complexes and with
`DGCategory.RightModule.gradedCohomologyIso`. -/
def derivedForgetGradedCohomologyIso (M : (rightModuleCategory.{v} C).K) (X : C.Obj) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj
        ((derivedEvaluationForget C X).obj ((derivedQ C).obj M)) ≅
      ModuleCat.of R (gradedCohomology M X n) :=
  (derivedEvaluationForgetHomologyIso C X n).app M ≪≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{v} R) (ComplexShape.up ℤ) n).app
      (cochainComplex (C := C) M X) ≪≫
    gradedCohomologyIso M X n

/-- **The identification is natural in the module.** For `f : M ⟶ N` in `K(Mod^dg(C))`, the
degree-`n` homology of the forgetful image of `Q_C f` corresponds to the degree-`n` homology of
the map of complexes `f X`.

This is `NatTrans.naturality` for
`DGCategory.RightModule.derivedEvaluationForgetHomologyIso`; it is recorded separately because
it, and not the objectwise isomorphism, is what the naturality clause of
`CochainComplex.derivedHomLiftIdentificationOfNaturality` consumes. -/
theorem derivedEvaluationForgetHomologyIso_hom_naturality (X : C.Obj) (n : ℤ)
    {M N : (rightModuleCategory.{v} C).K} (f : M ⟶ N) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
          ((derivedEvaluationForget C X).map ((derivedQ C).map f)) ≫
        (derivedEvaluationForgetHomologyIso C X n).hom.app N =
      (derivedEvaluationForgetHomologyIso C X n).hom.app M ≫
        (HomotopyCategory.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n).map
          ((cochainComplexOnK.{v} X).map f) :=
  (derivedEvaluationForgetHomologyIso C X n).hom.naturality f

variable (K : C.Obj)

/-- **The source of step 3's identification `φ`, computed.** At the one-object differential
graded category `E = C(K, K)` and the forgetful functor `U = ` `DGCategory.endDerivedForget` out
of `D(E)`, the degree-`n` homology of `U (Q_E (ev_K M))` is the explicit degree-`n` cohomology of
`ev_K M`.

That right-hand side is literally the source of
`DGCategory.RightModule.chainEquivReflectorEvaluation`, so this is the junction between step 3's
`φ` and the chain that is supposed to produce it. The object `e` of `E` is an argument because
the chain carries one; `E` has a single object, so it is no choice. -/
def endDerivedForgetGradedCohomologyIso (M : (rightModuleCategory.{v} C).K)
    (e : (endDGCategory C K).Obj) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj
        ((endDerivedForget C K).obj
          ((derivedQ (endDGCategory C K)).obj ((evaluationOnK.{v} C K).obj M))) ≅
      ModuleCat.of R (gradedCohomology ((evaluationDGFunctor.{v} C K).obj M) e n) :=
  derivedForgetGradedCohomologyIso (endDGCategory C K) ((evaluationOnK.{v} C K).obj M) e n

end RightModule

/-! ### At the reflector of steps 1 and 2 -/

section Reflector

variable {R : Type r} [CommRing R] (C : DGCategory.{v, u} R) (K : C.Obj)
  [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (L : (rightModuleCategory.{v} C).K ⥤ (rightModuleCategory.{v} C).K)
  [L.CommShift ℤ] [L.IsTriangulated]
  {S : Type*} [Category.{v₁} S] [Limits.HasZeroObject S] [HasShift S ℤ] [Preadditive S]
  [∀ n : ℤ, (shiftFunctor S n).Additive] [Pretriangulated S] [IsTriangulated S]
  (Φ : S ⥤ (rightModuleCategory.{v} C).K) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  (Z : ObjectProperty S) [Z.IsTriangulated]
  {DA : Type*} [Category.{v₂} DA] [Limits.HasZeroObject DA] [HasShift DA ℤ] [Preadditive DA]
  [∀ n : ℤ, (shiftFunctor DA n).Additive] [Pretriangulated DA]
  (q : S ⥤ DA) [q.IsLocalization Z.trW] [q.CommShift ℤ] [q.IsTriangulated]

/-- **The source of step 3's `φ` is the source of the chain, at the reflector of steps 1 and 2.**
For `R̃ = DGCategory.derivedHomReflector` the functor steps 1 and 2 of [Stacks, Tag 09LK] produce
and `U = DGCategory.endDerivedForget` the forgetful functor out of `D(C(K, K))`, the group

`H^n(U(R̃(q X)))`

that the identification `(*)` of step 3 is a map out of is the explicit degree-`n` cohomology of
the reflected evaluation `ev_K (L (Φ X))`, which is the group that
`DGCategory.RightModule.chainEquivReflectorEvaluation` is a bijection out of.

So the two halves of `(*)` meet on their common source. What is still owed is the identification
of the two *targets* — the chain lands in a Hom group of a localization of `K(C)` at
`Φ⁻¹ N`, step 3 asks for one of `D(A)` — and, above all, the elementwise formula
`unit_app_id` of `CochainComplex.derivedHomLiftIdentificationOfNaturality`: that the composite
agrees with Tag 09LC's identification on the image of the comparison `β`. Neither is supplied
here. -/
def derivedHomReflectorGradedCohomologyIso (hΦ : ∀ X, Z X → Limits.IsZero ((Φ ⋙ L).obj X))
    (X : S) (e : (endDGCategory C K).Obj) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj
        ((endDerivedForget C K).obj
          ((derivedHomReflector C K L Φ Z q hΦ).obj (q.obj X))) ≅
      ModuleCat.of R (RightModule.gradedCohomology
        ((evaluationDGFunctor.{v} C K).obj (L.obj (Φ.obj X))) e n) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).mapIso
      ((endDerivedForget C K).mapIso
        ((derivedHomReflectorCompIso C K L Φ Z q hΦ).app X)) ≪≫
    RightModule.endDerivedForgetGradedCohomologyIso C K (L.obj (Φ.obj X)) e n

end Reflector

end DGCategory

end
