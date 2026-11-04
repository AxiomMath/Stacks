module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomLiftComparison
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedCochainComplex
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomReflectorExists

/-!
# Step 3 of Tag 09LK at the reflector's target

Step 3 of the replacement proof of [Stacks, Tag 09LK]
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomLiftComparison.lean`) is stated for an
abstract lift: a category `E`, a functor `U : E ⥤ D(Ab)`, a functor `R̃ : D(A) ⥤ E` and a
comparison `β : Hom(K, -) ⟶ Q ⋙ (R̃ ⋙ U)`. Steps 1 and 2
(`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/DerivedHomReflectorExists.lean`)
produce an `R̃` landing in `D(E)` for `E = C(K, K)` the endomorphism differential graded category
of an object of a differential graded category `C` over `ℤ`. The functor `U` that joins them is
`DGCategory.endDerivedForget`, the forgetful functor
`D(C(K, K)) ⥤ D(ModuleCat ℤ)` of
`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/DerivedCochainComplex.lean`. This
file records that junction: step 3's interface is instantiable at those two functors.

## What is and is not supplied here

The comparison `θ` and step 3's conclusion are instantiated. The two data that step 3 consumes
besides `U` and `R̃` are carried as hypotheses here, which is exactly what it means for the
interface to be instantiable rather than discharged:

* the comparison `β`. Steps 1 and 2 supply a unit
  `Φ ⋙ ev_K ⋙ Q_E ⟶ q ⋙ R̃`, which is a unit `V ⟶ Q ⋙ R̃` for `V = Φ ⋙ ev_K ⋙ Q_E`; turning it
  into a `β` needs the identification `ι : V ⋙ U ≅ Hom(K, -)` of that `V`, read in `D(Ab)`, with
  the abelian-group-valued `Hom(K, -)`. It is a hypothesis here only because `Φ` is abstract
  here: for an arbitrary exact functor into `K(Mod^dg(C))` there is no such identification. At
  the `Φ` the proof uses — the differential graded Yoneda functor `X ↦ h_X` into the modules over
  `C = Comp^dg(A)`, with `L = K` — it is `CochainComplex.homDerivedLiftForgetIso`, the
  computation `ev_K (h_X) = C(K, X)` of `CochainComplex.homEvaluationComparisonIso` read through
  the comparison of differential graded and ordinary homotopy categories. The junction with that
  value substituted is
  `DGCategory.RightModule.exists_isIso_derivedHomForgetComparison_of_yonedaHomotopyFunctor` in
  `StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/DerivedHomForgetReflector.lean`.
* the identification `(*)`, `CochainComplex.DerivedHomLiftIdentification`. It is *equivalent* to
  step 3's conclusion (`CochainComplex.derivedHomLiftIdentificationOfIsRightDerivedFunctor` is
  the converse), so assuming it would be circular; it is the computation
  `H^n(ev_K (L h_X)) ≅ Hom_{D(A)}(Q K, (Q X)⟦n⟧)` that the construction of `R̃` has to supply.
  This one really is open:
  `StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomAssembly.lean` reduces it to a single
  elementwise formula, and that formula is not proved anywhere in this development.

## The universe residue

`DGCategory.endDerivedForget` imposes nothing: it exists for `C : DGCategory.{0, u} ℤ` at any
`u`, since its target `D(ModuleCat.{0} ℤ)` is fixed by the module universe of `C`'s morphism
complexes alone. The condition `C : DGCategory.{0, 0} ℤ` in the combined statement below is
inherited from step 1 — `DGCategory.exists_isTriangulated_derivedHomReflector` asks for
`C : DGCategory.{v, v} R` with the generating family indexed by `Type v` — and is automatic for
a differential graded algebra, whose single object lives in any universe.

## Main definitions

* `DGCategory.RightModule.derivedHomForgetComparisonAtReflector`: **step 3's comparison `θ` with
  `U` the forgetful functor out of `D(C(K, K))`.**
* `DGCategory.RightModule.derivedHomForgetUnitOfLiftInterface`: the comparison `β` obtained from
  a lift of `Hom(K, -)` through that `U` together with a unit, which is the shape steps 1 and 2
  deliver.

## Main results

* `DGCategory.RightModule.isIso_derivedHomForgetComparisonAtReflector`: step 3's conclusion at
  those values — the comparison is an isomorphism, given `(*)`.
* `DGCategory.RightModule.exists_isIso_derivedHomForgetComparison_of_reflector`: the junction in
  one statement. Under the hypotheses of steps 1 and 2 there are an exact
  `R̃ : D(A) ⥤ D(C(K, K))` and a unit `η` for it such that, for every lift identification `ν` and
  every `(*)` at the `β` those two build, step 3's comparison out of the abelian-group-valued
  derived Hom is an isomorphism. The unit is bound with `R̃` rather than the comparison `β` being
  quantified over, because `(*)` is only supplyable at the reflector's own unit.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public noncomputable section

namespace DGCategory

universe w w' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace RightModule

variable (A : Type u) [Category.{0} A] [Abelian A] [HasDerivedCategory.{w'} A]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  (C : DGCategory.{0, 0} ℤ) (L : C.Obj)
  (Rt : DerivedCategory A ⥤ RightModule.derivedCategory (endDGCategory C L))

/-- **The comparison `β` from a lift and a unit.** A lift `V : K(A) ⥤ D(C(K, K))` of the
abelian-group-valued `Hom(K, -)` through the forgetful functor, exhibited by `ι`, together with
a unit `η : V ⟶ Q ⋙ R̃`, gives the comparison that step 3 consumes. Steps 1 and 2 of the
replacement proof deliver the `η`, for `V` the differential graded Yoneda functor followed by
evaluation at `K` and the quotient functor of `D(C(K, K))`; the `ι` is not produced there. -/
def derivedHomForgetUnitOfLiftInterface
    (V : HomotopyCategory A (ComplexShape.up ℤ) ⥤
      RightModule.derivedCategory (endDGCategory C L))
    (ι : V ⋙ endDerivedForget C L ≅ CochainComplex.homToDerivedCategoryForget A K)
    (η : V ⟶ DerivedCategory.Qh ⋙ Rt) :
    CochainComplex.homToDerivedCategoryForget A K ⟶
      DerivedCategory.Qh ⋙ Rt ⋙ endDerivedForget C L :=
  CochainComplex.derivedHomForgetUnitOfLift A K (endDerivedForget C L) Rt V ι η

variable (h : (CochainComplex.homToDerivedCategoryForget A K).IsRightDerivable
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
  (β : CochainComplex.homToDerivedCategoryForget A K ⟶
    DerivedCategory.Qh ⋙ Rt ⋙ endDerivedForget C L)

/-- **Step 3's comparison `θ`, with `U` the forgetful functor out of `D(C(K, K))`.** Tag 09LK's
own hypothesis makes the abelian-group-valued `Hom(K, -) : K(A) ⥤ D(Ab)` right derivable; its
universal property turns the comparison `β` into `θ : R Hom(K, -) ⟶ R̃ ⋙ U`. Nothing is assumed
of `R̃`. -/
def derivedHomForgetComparisonAtReflector :
    CochainComplex.derivedHomForgetFunctor A K h ⟶ Rt ⋙ endDerivedForget C L :=
  CochainComplex.derivedHomForgetComparison A K (endDerivedForget C L) Rt h β

/-- **Step 3's conclusion at the reflector's target.** Given the identification `(*)` of the
cohomology of the values of the lift with the morphism groups of `D(A)`, the comparison `θ` out
of the abelian-group-valued derived Hom is an isomorphism. -/
theorem isIso_derivedHomForgetComparisonAtReflector
    (D : CochainComplex.DerivedHomLiftIdentification A K (endDerivedForget C L) Rt β) :
    IsIso (derivedHomForgetComparisonAtReflector A K C L Rt h β) :=
  CochainComplex.isIso_derivedHomForgetComparison A K (endDerivedForget C L) Rt h β D

/-- **The junction of steps 1 and 2 with step 3.** Let `C` be a differential graded category over
`ℤ` whose objects and morphism modules live in one universe, let `L` be an object of it and `G` a
family of objects indexed by that universe, and let `Φ : K(A) ⥤ K(Mod^dg(C))` be an exact functor
carrying the acyclic complexes into the localizing subcategory generated by the representables
`h_{G i}`. Then steps 1 and 2 produce an exact `R̃ : D(A) ⥤ D(C(L, L))`, and for that `R̃`,
every comparison `β` and every identification `(*)`, step 3's comparison out of the
abelian-group-valued derived Hom is an isomorphism.

The hypotheses are exactly those of
`DGCategory.exists_isTriangulated_derivedHomReflector` at `S = K(A)`, `Z` the acyclic complexes
and `q = Q`; what this adds is that the functor `U` the conclusion of step 3 needs now exists,
so the two halves meet.

The comparison `β` is *not* quantified over. Steps 1 and 2 supply one specific unit — the
reflector's own `η : Φ ⋙ ev_L ⋙ Q_E ⟶ Q ⋙ R̃` — and the identification `(*)` is only ever
supplyable for the `β` built from that `η`; a statement quantifying over all `β` would be asking
for `(*)` at comparisons no construction produces. So `η` is existentially bound alongside `R̃`,
and the only datum left free is the lift identification `ν`, which is
`CochainComplex.homEvaluationComparisonIso` read in `D(Ab)`. At the differential graded Yoneda
functor that `ν` is available, and
`DGCategory.RightModule.exists_isIso_derivedHomForgetComparison_of_yonedaHomotopyFunctor` is
this statement with it substituted. -/
theorem exists_isIso_derivedHomForgetComparison_of_reflector {ι : Type} (G : ι → C.Obj)
    (Φ : HomotopyCategory A (ComplexShape.up ℤ) ⥤ (rightModuleCategory.{0} C).K)
    [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (hZ : ∀ X, HomotopyCategory.subcategoryAcyclic A X → yonedaLocalizing C G (Φ.obj X)) :
    ∃ (Rt' : DerivedCategory A ⥤ RightModule.derivedCategory (endDGCategory C L))
      (_ : Rt'.CommShift ℤ) (_ : Rt'.IsTriangulated)
      (η : Φ ⋙ evaluationOnK.{0} C L ⋙ RightModule.derivedQ (endDGCategory C L) ⟶
        DerivedCategory.Qh ⋙ Rt'),
      ∀ (ν : (Φ ⋙ evaluationOnK.{0} C L ⋙ RightModule.derivedQ (endDGCategory C L)) ⋙
          endDerivedForget C L ≅ CochainComplex.homToDerivedCategoryForget A K)
        (_ : CochainComplex.DerivedHomLiftIdentification A K (endDerivedForget C L) Rt'
          (derivedHomForgetUnitOfLiftInterface A K C L Rt' _ ν η)),
        IsIso (derivedHomForgetComparisonAtReflector A K C L Rt' h
          (derivedHomForgetUnitOfLiftInterface A K C L Rt' _ ν η)) := by
  obtain ⟨_, _, _, _, Rt', cs, tri, η, _⟩ := exists_isTriangulated_derivedHomReflector C L G Φ
    (HomotopyCategory.subcategoryAcyclic A) DerivedCategory.Qh hZ
  exact ⟨Rt', cs, tri, η, fun _ D =>
    isIso_derivedHomForgetComparisonAtReflector A K C L Rt' h _ D⟩

end RightModule

end DGCategory

end
