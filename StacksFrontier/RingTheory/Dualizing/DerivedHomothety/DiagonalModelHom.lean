module

public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.FiniteDual

/-!
# Internal derived Hom out of a ring is restricted derived coextension

Let `Δ : S →+* A` be a homomorphism of commutative rings and let `A_S` denote `A`, placed in
degree zero and read as an object of `D(S)` by restriction of scalars along `Δ`. For an object
`Z` of `D(S)` the library offers two constructions of `RHom_S(A, Z)`: the *internal* derived Hom
of [stacks 0A63], evaluated at `A_S` by the canonical K-flat/K-injective model bifunctor
`StacksDraft.DerivedHom.DerivedInternalHom.Model.hom`, which stays inside `D(S)`; and the total
right derived functor `Dualizing.derivedHom` of coextension of scalars of [stacks 0A70], which
lands in `D(A)`. This file identifies the first with the restriction of scalars along `Δ` of the
second.

## Main results

* `Dualizing.modelHomIsoRestrictScalarsDerivedHom` — the isomorphism
  `RHom_S(A_S, Z) ≅ RHom_S(A, Z)` of objects of `D(S)`, computed from a K-injective complex
  representing `Z`.
* `Dualizing.nonempty_modelHomIsoRestrictScalarsDerivedHom` — the same for an arbitrary object
  `Z` of `D(S)`, a K-injective representative being always available.
* `Dualizing.nonempty_modelHom_iso_iff` — consequently the two objects are isomorphic to the
  same objects of `D(S)`.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {S A : Type u} [CommRing S] [CommRing A]

/-- The target ring of `Δ : S →+* A`, placed in degree zero and read in `D(S)` by derived
restriction of scalars, is represented by the single cochain complex on
`Dualizing.targetAsModule Δ`. -/
noncomputable def sourceSingleRestrictScalarsIsoQ (Δ : S →+* A) :
    (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj (targetAsModule.{u, u} Δ)) :=
  ((ModuleCat.restrictScalars.{u} Δ).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of A A) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).mapIso
      ((ModuleCat.restrictScalars.{u} Δ).mapIso
        (ULift.moduleEquiv.{u, u, u} (R := A) (M := A)).symm.toModuleIso) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} S) 0).app (targetAsModule.{u, u} Δ)

/-- For a homomorphism of commutative rings `Δ : S →+* A` and an object `Z` of `D(S)` represented
by a K-injective complex `I`, the internal derived Hom `RHom_S(A_S, Z)` of [stacks 0A63], taken in
`D(S)` at the derived restriction `A_S` of `A[0]`, is the restriction of scalars along `Δ` of the
derived coextension `RHom_S(A, Z)` of [stacks 0A70]. -/
noncomputable def modelHomIsoRestrictScalarsDerivedHom (Δ : S →+* A)
    {Z : DerivedCategory (ModuleCat.{u} S)} (I : CochainComplex (ModuleCat.{u} S) ℤ)
    (hI : I.IsKInjective) (e : Z ≅ DerivedCategory.Q.obj I) :
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom S).obj
        (Opposite.op ((ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))), Z) ≅
      (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj
        ((derivedHom.{u, u, u} Δ).obj Z) :=
  letI := hI
  Stacks.DerivedHom.BaseChange.homModelIso
      ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj (targetAsModule.{u, u} Δ)) I
      (sourceSingleRestrictScalarsIsoQ Δ) e ≪≫
    (DerivedCategory.Q.mapIso (coextendComplexIsoHomComplexSingle.{u, u} Δ I)).symm ≪≫
    ((ModuleCat.restrictScalars.{u} Δ).mapDerivedCategoryFactors.app
      ((coextendComplex.{u, u, u} Δ).obj I)).symm ≪≫
    (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.mapIso
      ((derivedHom.{u, u, u} Δ).mapIso e ≪≫
        derivedHomObjIsoCoextend.{u, u} Δ I hI).symm

/-- For a homomorphism of commutative rings `Δ : S →+* A` and any object `Z` of `D(S)`, the
internal derived Hom `RHom_S(A_S, Z)` is isomorphic to the restriction of scalars along `Δ` of the
derived coextension `RHom_S(A, Z)`. -/
theorem nonempty_modelHomIsoRestrictScalarsDerivedHom (Δ : S →+* A)
    (Z : DerivedCategory (ModuleCat.{u} S)) :
    Nonempty
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom S).obj
          (Opposite.op ((ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))), Z) ≅
        (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj
          ((derivedHom.{u, u, u} Δ).obj Z)) := by
  obtain ⟨I, q, hq, hI⟩ :=
    CochainComplex.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage Z)
  have := hq
  exact ⟨modelHomIsoRestrictScalarsDerivedHom Δ I hI
    ((DerivedCategory.Q.objObjPreimageIso Z).symm ≪≫ asIso (DerivedCategory.Q.map q))⟩

/-- The internal derived Hom `RHom_S(A_S, Z)` is isomorphic to a given object of `D(S)` exactly
when the restriction of scalars of the derived coextension `RHom_S(A, Z)` is. -/
theorem nonempty_modelHom_iso_iff (Δ : S →+* A) (Z W : DerivedCategory (ModuleCat.{u} S)) :
    Nonempty
        ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom S).obj
          (Opposite.op ((ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))), Z) ≅
          W) ↔
      Nonempty
        ((ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj
          ((derivedHom.{u, u, u} Δ).obj Z) ≅ W) :=
  let ⟨f⟩ := nonempty_modelHomIsoRestrictScalarsDerivedHom Δ Z
  ⟨fun ⟨h⟩ => ⟨f.symm ≪≫ h⟩, fun ⟨h⟩ => ⟨f ≪≫ h⟩⟩

end Dualizing

end
