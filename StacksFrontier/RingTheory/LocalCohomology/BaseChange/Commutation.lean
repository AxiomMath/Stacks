module

public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange.DerivedLoc
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange.KFlatLoc

/-!
# Derived extension of scalars commutes with localization away from an element

Let `f : A →+* B` be a homomorphism of commutative rings, let `a ∈ A` and `b = f a`. Then

`(K[1/a]) ⊗ᴸ_A B = (K ⊗ᴸ_A B)[1/b]`

for every `K` in `D(A)`.

## Main definitions

* `Stacks.LocalCohomology.extendLocCxIso`: degreewise extension of scalars commutes with
  degreewise localization away from `a`.
* `Stacks.LocalCohomology.derivedExtendLocIso`: the isomorphism
  `(K[1/a]) ⊗ᴸ_A B ≅ (K ⊗ᴸ_A B)[1/b]`.

## Main results

* `Stacks.LocalCohomology.nonempty_derivedExtendLocIso`: the two sides are isomorphic.

## References

* [Stacks Project, Tag 0ALZ](https://stacks.math.columbia.edu/tag/0ALZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedTensor CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uA uB v

namespace Stacks.LocalCohomology

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)

/-- Degreewise extension of scalars along `f`, on complexes. -/
abbrev extendCx : CochainComplex (ModuleCat.{max uA uB v} A) ℤ ⥤
    CochainComplex (ModuleCat.{max uA uB v} B) ℤ :=
  (extensionScalars.{uA, uB, v} f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Degreewise extension of scalars commutes with degreewise localization away from `a`. -/
def extendLocCxIso (a : A) (P : CochainComplex (ModuleCat.{max uA uB v} A) ℤ) :
    (extendCx.{uA, uB, v} f).obj ((locComplexFunctor.{uA, max uB v} a).obj P) ≅
      (locComplexFunctor.{uB, max uA v} (f a)).obj ((extendCx.{uA, uB, v} f).obj P) :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ extendLocIso.{uA, uB, v} f a (P.X i))
    (fun i j _ ↦ ((extendLocNatIso.{uA, uB, v} f a).hom.naturality (P.d i j)).symm)

/-- Derived extension of scalars commutes with localization away from an element: for every `Z`
in `D(A)`, `(Z[1/a]) ⊗ᴸ_A B` and `(Z ⊗ᴸ_A B)[1/f a]` are isomorphic. -/
lemma nonempty_derivedExtendLocIso (a : A) (Z : DerivedCategory (ModuleCat.{max uA uB v} A)) :
    Nonempty ((derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.obj
        ((derivedLoc.{uA, max uB v} a).obj Z) ≅
      (derivedLoc.{uB, max uA v} (f a)).obj
        ((derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.obj Z)) := by
  classical
  obtain ⟨P, g, hPkf, -, hg, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{uA, max uB v}
      (DerivedCategory.Q.objPreimage Z)
  have hiso : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hg
  let e : DerivedCategory.Q.obj P ≅ Z :=
    asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso Z
  have hcP : IsIso ((derivedExtensionScalarsGeneral.{uA, v, uB} f).comparison.app P) :=
    (derivedExtensionScalarsGeneral.{uA, v, uB} f).comparison_isIso_of_kFlat P hPkf
  have hcL : IsIso ((derivedExtensionScalarsGeneral.{uA, v, uB} f).comparison.app
      ((locComplexFunctor.{uA, max uB v} a).obj P)) :=
    (derivedExtensionScalarsGeneral.{uA, v, uB} f).comparison_isIso_of_kFlat _
      (kFlat_locComplex.{uA, max uB v} a P hPkf)
  exact ⟨(derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.mapIso
      ((derivedLoc.{uA, max uB v} a).mapIso e.symm) ≪≫
    (derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.mapIso
      ((locFunctor.{uA, max uB v} a).mapDerivedCategoryFactors.app P) ≪≫
    asIso ((derivedExtensionScalarsGeneral.{uA, v, uB} f).comparison.app
      ((locComplexFunctor.{uA, max uB v} a).obj P)) ≪≫
    DerivedCategory.Q.mapIso (extendLocCxIso.{uA, uB, v} f a P) ≪≫
    ((locFunctor.{uB, max uA v} (f a)).mapDerivedCategoryFactors.app
      ((extendCx.{uA, uB, v} f).obj P)).symm ≪≫
    (derivedLoc.{uB, max uA v} (f a)).mapIso
      (asIso ((derivedExtensionScalarsGeneral.{uA, v, uB} f).comparison.app P)).symm ≪≫
    (derivedLoc.{uB, max uA v} (f a)).mapIso
      ((derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.mapIso e)⟩

/-- Derived extension of scalars commutes with localization away from an element. -/
def derivedExtendLocIso (a : A) (Z : DerivedCategory (ModuleCat.{max uA uB v} A)) :
    (derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.obj
        ((derivedLoc.{uA, max uB v} a).obj Z) ≅
      (derivedLoc.{uB, max uA v} (f a)).obj
        ((derivedExtensionScalarsGeneral.{uA, v, uB} f).functor.obj Z) :=
  Classical.choice (nonempty_derivedExtendLocIso.{uA, uB, v} f a Z)

end Stacks.LocalCohomology

end
