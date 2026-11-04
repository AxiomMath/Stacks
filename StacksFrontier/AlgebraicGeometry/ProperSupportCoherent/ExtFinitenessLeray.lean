module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.HypercohomologyOverABase
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections

/-!
# Derived global sections over the base ring factor through the derived direct image

Let `A` be a commutative ring and let `f : X ⟶ Spec A` be a scheme over `A`. Derived sections over
`f⁻¹ V` are derived sections over `V` of the derived direct image. At `V = ⊤` and with the scalars
restricted from `Γ(Spec A, 𝒪)` to `A` this reads

`RΓ(X, -) ≅ RΓ(Spec A, Rf_* -)`

as functors `D(𝒪_X) ⥤ D(A)`.

## Main results

* `AlgebraicGeometry.homotopyCompBaseIso`: the comparison of the two ways of composing a functor
  read on homotopy categories with an exact functor.
* `AlgebraicGeometry.derivedPreimageSectionsBaseIso`: derived sections over `f⁻¹ ⊤`, read over
  `A`, are `AlgebraicGeometry.derivedGlobalSectionsOver f`.
* `AlgebraicGeometry.derivedSectionsBaseIso`: derived sections over `⊤` of `Spec A`, read over
  `A`, are `AlgebraicGeometry.derivedGlobalSectionsOver (𝟙 (Spec A))`.
* `AlgebraicGeometry.derivedGlobalSectionsOverPushforwardIso`: `RΓ(X, -) ≅ RΓ(Spec A, Rf_* -)`
  over the base ring.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0G9P](https://stacks.math.columbia.edu/tag/0G9P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-! ### A generic comparison of homotopy-category composites -/

section Generic

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

/-- The comparison of the two ways of composing a functor read on homotopy categories with an
exact functor: the associators, `mapHomotopyCategoryCompIso` and `mapDerivedCategoryFactorsh`. -/
def homotopyCompBaseIso (P : C ⥤ D) [P.Additive] (G : D ⥤ E) [G.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    (H : C ⥤ E) [H.Additive] (e : P ⋙ G ≅ H) :
    (P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ G.mapDerivedCategory ≅
      H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (P.mapHomotopyCategory (ComplexShape.up ℤ))
      G.mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)) DerivedCategory.Qh

end Generic

/-! ### Derived global sections on the source, in the ringed-space spelling -/

/-- Derived sections over `f⁻¹ ⊤`, read over the base ring, are `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`. -/
def derivedPreimageSectionsBaseIso :
    derivedPreimageSections f.toLRSHom.toShHom ⊤ ⋙
        (ModuleCat.restrictScalars
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).mapDerivedCategory ≅
      (homotopyBaseSections f).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ)) := by
  haveI := Stacks.Cohomology.SiteCohomologyPresheaf.isRightDerivedFunctor_totalRightDerived_comp
    (homotopyPreimageSections f.toLRSHom.toShHom ⊤)
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).mapDerivedCategory
  exact Functor.rightDerivedNatIso _ _
    (Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedCompUnit
      (homotopyPreimageSections f.toLRSHom.toShHom ⊤)
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).mapDerivedCategory)
    ((homotopyBaseSections f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))
    (homotopyCompBaseIso (preimageSections f.toLRSHom.toShHom ⊤)
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (baseSections f) (Iso.refl _))

/-! ### Derived global sections on the affine base, in the ringed-space spelling -/

/-- Derived sections over `⊤` of `Spec A`, read over the base ring, are
`RΓ(Spec A, -) : D(𝒪_{Spec A}) ⥤ D(A)`. -/
def derivedSectionsBaseIso :
    derivedSectionsOverOpen (Spec (CommRingCat.of A)).toRingedSpace ⊤ ⋙
        (ModuleCat.restrictScalars
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).mapDerivedCategory ≅
      (homotopyBaseSections (𝟙 (Spec (CommRingCat.of A)))).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (structureSheafRing (Spec (CommRingCat.of A)).toRingedSpace))
          (ComplexShape.up ℤ)) := by
  haveI := Stacks.Cohomology.SiteCohomologyPresheaf.isRightDerivedFunctor_totalRightDerived_comp
    (homotopySectionsOverOpen (Spec (CommRingCat.of A)).toRingedSpace ⊤)
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).mapDerivedCategory
  exact Functor.rightDerivedNatIso _ _
    (Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedCompUnit
      (homotopySectionsOverOpen (Spec (CommRingCat.of A)).toRingedSpace ⊤)
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).mapDerivedCategory)
    ((homotopyBaseSections (𝟙 (Spec (CommRingCat.of A)))).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (structureSheafRing (Spec (CommRingCat.of A)).toRingedSpace))
        (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (structureSheafRing (Spec (CommRingCat.of A)).toRingedSpace))
      (ComplexShape.up ℤ))
    (homotopyCompBaseIso (sectionsOverOpen (Spec (CommRingCat.of A)).toRingedSpace ⊤)
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (baseSections (𝟙 (Spec (CommRingCat.of A)))) (Iso.refl _))

/-! ### Leray over the base ring -/

/-- For a scheme `f : X ⟶ Spec A` the `A`-linear derived global sections of `X` are the
`A`-linear derived global sections of `Spec A` applied to the unbounded derived direct image:

`RΓ(X, -) ≅ RΓ(Spec A, Rf_* -) : D(𝒪_X) ⥤ D(A)`. -/
def derivedGlobalSectionsOverPushforwardIso :
    derivedGlobalSectionsOver f ≅
      derivedPushforwardModules f ⋙
        derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A))) :=
  (derivedPreimageSectionsBaseIso f).symm ≪≫
    Functor.isoWhiskerRight
      (derivedSectionsPushforwardIso f.toLRSHom.toShHom ⊤).symm
      (ModuleCat.restrictScalars
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedPushforward f.toLRSHom.toShHom)
      (derivedSectionsBaseIso (A := A))

end AlgebraicGeometry

end
