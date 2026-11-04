module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange

/-!
# Local cohomology of a ring and change of rings

Let `A → B` be a homomorphism of commutative rings and let `I ⊆ A` be a finitely generated
ideal, with `Z = V(I) ⊆ Spec(A)` and `Y = V(IB) ⊆ Spec(B)` the corresponding closed subsets.
Then derived extension of scalars carries `RΓ_Z(A)` to `RΓ_Y(B)`.

## Main definitions

* `Dualizing.localCohomologyOfRing` — the local cohomology of the regular module, viewed in the
  ambient derived category.
* `Dualizing.localCohomologyOfRingLifted` — the same after transporting the regular module into
  a larger module universe.

## Main results

* `Dualizing.localCohomologyOfRingBaseChangeIso` — the change-of-rings isomorphism for two rings
  in one universe.
* `Dualizing.localCohomologyOfRingLiftedBaseChangeIso` — the same comparison for rings in
  independent universes.

## Implementation notes

The source writes a chain of four equal objects,
`RΓ_I(A) ⊗ᴸ_A B = RΓ_Z(A) ⊗ᴸ_A B = RΓ_Y(B) = RΓ_{IB}(B)`. Its closed subsets `Z = V(I)` and
`Y = V(IB)` are encoded by the ideal arguments of `Dualizing.localCohomologyFunctor`, so the
middle equality — the only one between two local-cohomology terms — is what this file proves; it
is expressed as an isomorphism in `D(B)` rather than as an equality. Derived tensor product with
`B` is represented by derived extension of scalars. The two outer terms are the *derived
`I`-power torsion* functor `RΓ_I`, a different functor from `RΓ_Z`; they are added and
identified with these ones in
`StacksFrontier.RingTheory.Dualizing.LocalCohomologyNoetherian.ChangeOfRingsTorsion`, which needs
both rings Noetherian, and the composed four-term chain is
`Dualizing.derivedPowerTorsionOfRingBaseChangeIso` there.

The hypothesis here is finite generation of `I` rather than Noetherianity of `A`, which is
weaker and still covers the source's case. For rings in independent universes the two regular
modules do not live in a common module category, so they are transported into one by the
universe-lifting functor; the resulting statement specialises to the first one up to that
transport.

## References

* [Stacks Project, Tag 0957](https://stacks.math.columbia.edu/tag/0957)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uA uB v

namespace Dualizing

/-- The local cohomology `RΓ_{V(I)}(A)` of a ring along a finitely generated ideal, viewed in
the ambient derived category of `A`-modules. -/
abbrev localCohomologyOfRing (A : Type uA) [CommRing A] (I : Ideal A) (hI : I.FG) :
    DerivedCategory (ModuleCat.{uA} A) :=
  (derivedPowerTorsionProperty A I hI).ι.obj
    ((localCohomologyFunctor A I hI).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{uA} A) 0).obj (ModuleCat.of A A)))

/-- The local cohomology `RΓ_{V(I)}(A)` of a ring along a finitely generated ideal, taken after
transporting the regular module into the module universe `max uA v`. -/
abbrev localCohomologyOfRingLifted (A : Type uA) [CommRing A] (I : Ideal A) (hI : I.FG) :
    DerivedCategory (ModuleCat.{max uA v} A) :=
  (derivedPowerTorsionProperty A I hI).ι.obj
    ((localCohomologyFunctor A I hI).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max uA v} A) 0).obj
        ((ModuleCat.uliftFunctor.{v, uA} A).obj (ModuleCat.of A A))))

/-- **Stacks 0957.** Local cohomology of the regular module commutes with derived extension of
scalars along a homomorphism of commutative rings, for a finitely generated ideal. -/
@[stacks 0957 "base change on regular modules"]
def localCohomologyOfRingBaseChangeIso (A B : Type uA) [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (hI : I.FG) :
    (derivedExtensionScalarsGeneral.{uA, 0, uA} f).functor.obj (localCohomologyOfRing A I hI) ≅
      localCohomologyOfRing B (I.map f) (hI.map f) := by
  let M : ModuleCat.{uA} A := ModuleCat.of A A
  let N : ModuleCat.{uA} B := ModuleCat.of B B
  let P : CochainComplex (ModuleCat.{uA} A) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat.{uA} A) 0).obj M
  let D := totalDerivedExtensionScalars.{uA, uA, 0} f
  let F : ModuleCat.{uA} A ⥤ ModuleCat.{uA} B := ModuleCat.extendScalars.{uA, uA, uA} f
  let hMN : F.obj M ≅ N := by
    letI : Algebra A B := f.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso
  haveI : P.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    change IsZero (((HomologicalComplex.single (ModuleCat.{uA} A)
      (ComplexShape.up ℤ) 0).obj M).X i)
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i (ne_of_gt hi)
  haveI : ∀ i : ℤ, Projective (P.X i) := by
    intro i
    change Projective (((HomologicalComplex.single (ModuleCat.{uA} A)
      (ComplexShape.up ℤ) 0).obj M).X i)
    infer_instance
  let ecomp : D.functor.obj (DerivedCategory.Q.obj P) ≅
      (extensionOfScalarsComplexGeneral f).obj P :=
    @asIso _ _ _ _ (D.comparison.app P) (D.comparison_isIso_of_projective P 0)
  let esingle := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M
  let e : (derivedExtensionScalarsGeneral.{uA, 0, uA} f).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{uA} A) 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{uA} B) 0).obj N :=
    ecomp ≪≫ DerivedCategory.Q.mapIso esingle ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{uA} B) 0).mapIso hMN
  let e₀ := (Stacks.LocalCohomology.localCohomologyBaseChangeIso.{uA, uA, 0} f I hI).app
    ((DerivedCategory.singleFunctor (ModuleCat.{uA} A) 0).obj (ModuleCat.of A A))
  simpa [localCohomologyOfRing] using e₀ ≪≫
    (localCohomologyFunctor B (I.map f) (hI.map f) ⋙
      (derivedPowerTorsionProperty B (I.map f) (hI.map f)).ι).mapIso e

/-- **Stacks 0957.** The change-of-rings isomorphism for local cohomology of the regular module,
for two rings in independent universes, after transporting both regular modules into a common
module universe. -/
@[stacks 0957 "base change across universes"]
def localCohomologyOfRingLiftedBaseChangeIso (A : Type uA) (B : Type uB) [CommRing A]
    [CommRing B] (f : A →+* B) (I : Ideal A) (hI : I.FG) :
    (derivedExtensionScalarsGeneral.{uA, max uA uB, uB} f).functor.obj
        (localCohomologyOfRingLifted.{uA, max uA uB} A I hI) ≅
      localCohomologyOfRingLifted.{uB, max uA uB} B (I.map f) (hI.map f) := by
  let M : ModuleCat.{max uA uB} A :=
    (ModuleCat.uliftFunctor.{max uA uB, uA} A).obj (ModuleCat.of A A)
  let N := (ModuleCat.uliftFunctor.{max uA uB, uB} B).obj (ModuleCat.of B B)
  let P : CochainComplex (ModuleCat.{max uA uB} A) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat.{max uA uB} A) 0).obj M
  let D := totalDerivedExtensionScalars.{uA, uB, max uA uB} f
  let F : ModuleCat.{max uA uB} A ⥤ ModuleCat.{max uA uB} B :=
    ModuleCat.extendScalars.{uA, uB, max uA uB} f
  let hMN : F.obj M ≅ N := by
    letI : Algebra A B := f.toAlgebra
    exact (((ULift.moduleEquiv : ULift.{max uA uB, uA} A ≃ₗ[A] A).baseChange A B).trans
      ((TensorProduct.AlgebraTensorModule.rid A B B).trans
        (ULift.moduleEquiv.symm : B ≃ₗ[B] ULift.{max uA uB, uB} B))).toModuleIso
  haveI : P.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    change IsZero (((HomologicalComplex.single (ModuleCat.{max uA uB} A)
      (ComplexShape.up ℤ) 0).obj M).X i)
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i (ne_of_gt hi)
  haveI : ∀ i : ℤ, Projective (P.X i) := by
    intro i
    change Projective (((HomologicalComplex.single (ModuleCat.{max uA uB} A)
      (ComplexShape.up ℤ) 0).obj M).X i)
    infer_instance
  let ecomp : D.functor.obj (DerivedCategory.Q.obj P) ≅
      (extensionOfScalarsComplexGeneral f).obj P :=
    @asIso _ _ _ _ (D.comparison.app P) (D.comparison_isIso_of_projective P 0)
  let esingle := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M
  let e : (derivedExtensionScalarsGeneral.{uA, max uA uB, uB} f).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB} A) 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max uA uB} B) 0).obj N :=
    ecomp ≪≫ DerivedCategory.Q.mapIso esingle ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{max uA uB} B) 0).mapIso hMN
  let e₀ := (Stacks.LocalCohomology.localCohomologyBaseChangeIso.{uA, uB, max uA uB} f I hI).app
    ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB} A) 0).obj M)
  simpa [localCohomologyOfRingLifted, M, N] using e₀ ≪≫
    (localCohomologyFunctor B (I.map f) (hI.map f) ⋙
      (derivedPowerTorsionProperty B (I.map f) (hI.map f)).ι).mapIso e

end Dualizing

end
