module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsAgreement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomsFromCocycles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.StrictlyPerfectIsKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomKFlatSite
import StacksCore.Tactic.StacksAttribute

/-! # The comparison `strictlyPerfectHomComparison` as a degree-zero global hypercohomology class

Let `(C, O)` be a ringed site and let `E`, `F` be complexes of `O`-modules. The comparison of the
class of the internal Hom complex with the derived internal Hom

`σ : Q(SheafHom(E, F)) ⟶ RSheafHom(QE, QF)`

is `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`, and
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv` identifies the degree-zero global
hypercohomology of a derived internal Hom with a group of morphisms of `D(O)`,

`H⁰(C, RSheafHom(L, M)) = Hom_{D(O)}(L, M)`.

This file exhibits the class of `H⁰(C, RSheafHom(Q(SheafHom(E, F)), RSheafHom(QE, QF)))` that this
identification carries to `σ`. The morphism `σ` is the class of the morphism of complexes
`SheafHom(E, 𝜀_F)`, with `𝜀_F : F ⟶ R F` the K-injective augmentation, followed by an isomorphism
of `D(O)`, and its class is the class of `SheafHom(E, 𝜀_F)` pushed along that isomorphism. The
description takes two K-flatness hypotheses: `hE` on `E` and `hEF` on `SheafHom(E, F)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsClassOfHomComp`: the degree-zero global
  hypercohomology class of `RSheafHom(QA, M)` attached to a morphism of complexes `f : A ⟶ J`
  into a K-injective complex followed by an arbitrary morphism `ψ : QJ ⟶ M` of `D(O)`, for `A`
  K-flat.
* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparisonClass`: the class corresponding to
  `σ`, the above at `A = SheafHom(E, F)`, `J = SheafHom(E, R F)`.

## Main results

* `derivedSheafHomGlobalSectionsEquiv_apply_eq_ofKFlat`: at the class of a K-flat complex and the
  class of a K-injective complex, `derivedSheafHomGlobalSectionsEquiv` agrees with
  `derivedSheafHomGlobalSectionsEquivOfKFlat`.
* `derivedSheafHomGlobalSectionsEquiv_derivedGlobalSectionsClassOfHomComp`:
  `derivedSheafHomGlobalSectionsEquiv` sends `derivedGlobalSectionsClassOfHomComp` to
  `Q.map f ≫ ψ`.
* `derivedSheafHomGlobalSectionsEquiv_strictlyPerfectHomComparisonClass` and
  `derivedSheafHomGlobalSectionsEquiv_symm_strictlyPerfectHomComparison`:
  `derivedSheafHomGlobalSectionsEquiv` carries `strictlyPerfectHomComparisonClass` to
  `strictlyPerfectHomComparison`, and equivalently its inverse carries the comparison to that
  class.
* `derivedSheafHomGlobalSectionsEquiv_strictlyPerfectHomComparisonClass_of_isStrictlyPerfect`:
  the same at a strictly perfect `E` and a K-flat `F`, with both K-flatness hypotheses
  discharged.

All names are in the namespace `AlgebraicGeometry.RingedSite`.

## References

* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 0GM5](https://stacks.math.columbia.edu/tag/0GM5)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
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

/-! ### The identification at a K-flat and a K-injective complex -/

/-- At the class of a K-flat complex `A` and the class of a K-injective complex `I`, the
identification `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv` agrees with
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat` at `A` and `I`. -/
theorem derivedSheafHomGlobalSectionsEquiv_apply_eq_ofKFlat
    {A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) x =
      derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA x := by
  have h0 : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedSheafHomObjectsModelIso X (Iso.refl (DerivedCategory.Q.obj A))
            (Iso.refl (DerivedCategory.Q.obj I))).hom) x = x := by
    rw [AlgebraicGeometry.RingedSite.derivedSheafHomObjectsModelIso_refl]
    simp
  refine (derivedSheafHomGlobalSectionsEquiv_apply_of_isKFlat X hA (Iso.refl _)
    (Iso.refl _) x).trans ?_
  refine (congrArg (fun z => (Iso.refl (DerivedCategory.Q.obj A)).inv ≫
    derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA z ≫
      (Iso.refl (DerivedCategory.Q.obj I)).hom) h0).trans ?_
  simp

/-! ### The class of a morphism of complexes followed by a morphism of `D(O)` -/

/-- The degree-zero global hypercohomology class of `RSheafHom(QA, M)` attached to a morphism of
complexes followed by a morphism of `D(O)`. For `A` K-flat, `J` K-injective, `f : A ⟶ J` a
morphism of complexes and `ψ : QJ ⟶ M` an arbitrary morphism of `D(O)`, it is the class of `f`
(`AlgebraicGeometry.RingedSite.derivedGlobalSectionsClassOfHomOfKFlat`) pushed along the covariant
functoriality of the derived internal Hom in `ψ`. -/
def derivedGlobalSectionsClassOfHomComp
    (A J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (f : A ⟶ J)
    {M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (ψ : DerivedCategory.Q.obj J ⟶ M) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj M)) : Type u) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
    ((derivedModuleGlobalSections X).map
      (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map ψ))
    (derivedGlobalSectionsClassOfHomOfKFlat X A J hA f)

/-- The identification `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv` sends
`derivedGlobalSectionsClassOfHomComp X A J hA f ψ` to `Q.map f ≫ ψ`, for `A` K-flat, `J`
K-injective, `f : A ⟶ J` a morphism of complexes and `ψ : QJ ⟶ M` a morphism of `D(O)`. -/
theorem derivedSheafHomGlobalSectionsEquiv_derivedGlobalSectionsClassOfHomComp
    (A J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (f : A ⟶ J)
    {M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (ψ : DerivedCategory.Q.obj J ⟶ M) :
    derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj A) M
        (derivedGlobalSectionsClassOfHomComp X A J hA f ψ) =
      DerivedCategory.Q.map f ≫ ψ :=
  (derivedSheafHomGlobalSectionsEquiv_naturality_target X (DerivedCategory.Q.obj A) ψ _).trans
    (congrArg (fun φ => φ ≫ ψ)
      ((derivedSheafHomGlobalSectionsEquiv_apply_eq_ofKFlat X hA _).trans
        (derivedSheafHomGlobalSectionsEquivOfKFlat_derivedGlobalSectionsClassOfHomOfKFlat
          X A J hA f)))

/-! ### The comparison as a class -/

variable (D : DerivedInternalHom X)
  (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The degree-zero global hypercohomology class of
`RSheafHom(Q(SheafHom(E, F)), RSheafHom(QE, QF))` corresponding to the comparison
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`, for `E` K-flat (`hE`) and
`SheafHom(E, F)` K-flat (`hEF`): the class of the morphism of internal Hom complexes induced by
the K-injective augmentation `𝜀_F : F ⟶ R F`, pushed along the inverse of the K-injective model
comparison of the derived internal Hom and the inverse of the map that `𝜀_F` induces on derived
internal Hom. -/
def strictlyPerfectHomComparisonClass
    (hE : Stacks.SheafOfModules.IsKFlat X.O E)
    (hEF : Stacks.SheafOfModules.IsKFlat X.O (sheafHomComplex X E F).obj) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj
            (op (DerivedCategory.Q.obj (sheafHomComplex X E F).obj))).obj
          ((D.hom.obj (op (DerivedCategory.Q.obj E))).obj (DerivedCategory.Q.obj F))))
      : Type u) :=
  haveI := isKInjective_sheafHomComplex_of_isKFlat X E ((kInjectiveResolution X).obj F) hE
  derivedGlobalSectionsClassOfHomComp X (sheafHomComplex X E F).obj
    (sheafHomComplex X E ((kInjectiveResolution X).obj F)).obj hEF
    (homMap X (𝟙 E) ((kInjectiveAugmentation X).app F))
    ((D.homComparison E ((kInjectiveResolution X).obj F)).inv ≫
      inv ((D.hom.obj (op (DerivedCategory.Q.obj E))).map
        (DerivedCategory.Q.map ((kInjectiveAugmentation X).app F))))

/-- The identification `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv` carries
`strictlyPerfectHomComparisonClass` to the comparison
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`. -/
theorem derivedSheafHomGlobalSectionsEquiv_strictlyPerfectHomComparisonClass
    (hE : Stacks.SheafOfModules.IsKFlat X.O E)
    (hEF : Stacks.SheafOfModules.IsKFlat X.O (sheafHomComplex X E F).obj) :
    derivedSheafHomGlobalSectionsEquiv X
        (DerivedCategory.Q.obj (sheafHomComplex X E F).obj)
        ((D.hom.obj (op (DerivedCategory.Q.obj E))).obj (DerivedCategory.Q.obj F))
        (strictlyPerfectHomComparisonClass X D E F hE hEF) =
      strictlyPerfectHomComparison X D E F :=
  have := isKInjective_sheafHomComplex_of_isKFlat X E ((kInjectiveResolution X).obj F) hE
  derivedSheafHomGlobalSectionsEquiv_derivedGlobalSectionsClassOfHomComp X
    (sheafHomComplex X E F).obj (sheafHomComplex X E ((kInjectiveResolution X).obj F)).obj hEF
    (homMap X (𝟙 E) ((kInjectiveAugmentation X).app F)) _

/-- The inverse of `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv` sends the
comparison `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison` to
`strictlyPerfectHomComparisonClass`. -/
theorem derivedSheafHomGlobalSectionsEquiv_symm_strictlyPerfectHomComparison
    (hE : Stacks.SheafOfModules.IsKFlat X.O E)
    (hEF : Stacks.SheafOfModules.IsKFlat X.O (sheafHomComplex X E F).obj) :
    (derivedSheafHomGlobalSectionsEquiv X
        (DerivedCategory.Q.obj (sheafHomComplex X E F).obj)
        ((D.hom.obj (op (DerivedCategory.Q.obj E))).obj
          (DerivedCategory.Q.obj F))).symm (strictlyPerfectHomComparison X D E F) =
      strictlyPerfectHomComparisonClass X D E F hE hEF :=
  (AddEquiv.symm_apply_eq _).2
    (derivedSheafHomGlobalSectionsEquiv_strictlyPerfectHomComparisonClass X D E F hE hEF).symm

/-! ### Both hypotheses at a strictly perfect source -/

section StrictlyPerfect

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-- At a strictly perfect `E` and a K-flat `F`, the identification
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv` carries
`strictlyPerfectHomComparisonClass` to `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`,
with the K-flatness of `E` given by `AlgebraicGeometry.RingedSite.kFlat_of_isStrictlyPerfect` and
that of `SheafHom(E, F)` by `AlgebraicGeometry.RingedSite.isKFlat_sheafHomComplex_of_isKFlat`. -/
theorem derivedSheafHomGlobalSectionsEquiv_strictlyPerfectHomComparisonClass_of_isStrictlyPerfect
    (hsp : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) E)
    (hF : Stacks.SheafOfModules.IsKFlat X.O F) :
    derivedSheafHomGlobalSectionsEquiv X
        (DerivedCategory.Q.obj (sheafHomComplex X E F).obj)
        ((D.hom.obj (op (DerivedCategory.Q.obj E))).obj (DerivedCategory.Q.obj F))
        (strictlyPerfectHomComparisonClass X D E F (kFlat_of_isStrictlyPerfect X E hsp)
          (isKFlat_sheafHomComplex_of_isKFlat X E F hsp.bounded
            (fun i => IsDirectSummandOfFiniteFree.isFiniteFreeSummand X
              (hsp.termDirectSummand i)) hF)) =
      strictlyPerfectHomComparison X D E F :=
  derivedSheafHomGlobalSectionsEquiv_strictlyPerfectHomComparisonClass X D E F _ _

end StrictlyPerfect

end AlgebraicGeometry.RingedSite

end
