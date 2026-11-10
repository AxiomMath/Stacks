module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSections
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import
StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived global sections over a base ring of a complex with right-acyclic terms

Let `X` be a quasi-compact quasi-separated scheme over a commutative ring `A` and let `K` be a
cochain complex of quasi-coherent `𝒪_X`-modules each of whose terms is right acyclic for
`Γ(X, -)`. Then the complex of `A`-linear global sections computes `A`-linear derived global
sections: the canonical comparison `Γ(X, K) ⟶ RΓ(X, K)` is an isomorphism in `D(A)`.

This is [Stacks, Tag 0G9P], whose conclusion lives in `D(Γ(X, 𝒪_X))`, transported along
restriction of scalars to the base. Restriction of scalars is exact, so the composite of
`RΓ(X, -) : D(𝒪_X) ⥤ D(Γ(X, 𝒪_X))` with the functor it induces on derived categories is again a
right derived functor, of `A`-linear global sections; and two right derived functors of
isomorphic functors are invertible on exactly the same objects.

## Main results

* `CategoryTheory.Functor.isIso_rightDerivedUnit_app_of_iso`: right derived functors of
  isomorphic functors have units invertible at the same objects.
* `AlgebraicGeometry.isIso_derivedGlobalSectionsOverUnit_app_of_termwise_acyclic`: a complex of
  quasi-coherent modules with right-acyclic terms computes `A`-linear derived global sections.

## References

* [Stacks Project, Tag 0G9P](https://stacks.math.columbia.edu/tag/0G9P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology (sectionsFunctor)
open Stacks.Cohomology.SiteCohomologyPresheaf

universe u

namespace CategoryTheory.Functor

/-- **Right derived functors of isomorphic functors are invertible at the same objects.** The
isomorphism of right derived functors induced by `τ` is compatible with the two units, so
invertibility of one unit at `Z` forces invertibility of the other. -/
theorem isIso_rightDerivedUnit_app_of_iso {C D H : Type*}
    [Category C] [Category D] [Category H]
    {F F' : C ⥤ H} {L : C ⥤ D} (RF RF' : D ⥤ H)
    (α : F ⟶ L ⋙ RF) (α' : F' ⟶ L ⋙ RF') (W : MorphismProperty C) [L.IsLocalization W]
    [RF.IsRightDerivedFunctor α W] [RF'.IsRightDerivedFunctor α' W]
    (τ : F ≅ F') (Z : C) (h : IsIso (α.app Z)) :
    IsIso (α'.app Z) := by
  have key := rightDerivedNatTrans_app RF RF' α α' W τ.hom Z
  have hnat : IsIso ((rightDerivedNatTrans RF RF' α α' W τ.hom).app (L.obj Z)) :=
    inferInstanceAs (IsIso ((rightDerivedNatIso RF RF' α α' W τ).hom.app (L.obj Z)))
  have : IsIso (τ.hom.app Z ≫ α'.app Z) := by
    rw [← key]
    infer_instance
  exact IsIso.of_isIso_comp_left (τ.hom.app Z) (α'.app Z)

end CategoryTheory.Functor

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- Restriction of scalars along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`. Composing global sections with
it is `A`-linear global sections `AlgebraicGeometry.globalSectionsOver`. -/
abbrev restrictScalarsOver : ModuleCat.{u} Γ(X, ⊤) ⥤ ModuleCat.{u} A :=
  ModuleCat.restrictScalars (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)

/-- Restriction of scalars to `A` preserves finite limits. -/
instance preservesFiniteLimits_restrictScalarsOver :
    PreservesFiniteLimits (restrictScalarsOver f) :=
  ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩

/-- Restriction of scalars to `A` preserves finite colimits. -/
instance preservesFiniteColimits_restrictScalarsOver :
    PreservesFiniteColimits (restrictScalarsOver f) :=
  ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩

/-- **A complex of quasi-coherent modules with right-acyclic terms computes `A`-linear derived
global sections.** This is [Stacks, Tag 0G9P] over a base ring: the canonical comparison
`Γ(X, K) ⟶ RΓ(X, K)` is invertible in `D(A)`. -/
theorem isIso_derivedGlobalSectionsOverUnit_app_of_termwise_acyclic
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]
    (K : CochainComplex X.Modules ℤ) (hqc : ∀ n, (K.X n).IsQuasicoherent)
    (hacyclic : ∀ n, (sectionsFunctor X ⊤).rightAcyclic (K.X n)) :
    IsIso ((derivedGlobalSectionsOverUnit f).app
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K)) := by
  let W := HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)
  let T := restrictScalarsOver f
  let Fh := (sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have hΓ : IsIso ((Fh.totalRightDerivedUnit DerivedCategory.Qh W).app
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K)) :=
    isIso_to_derivedGlobalSections_of_termwise_acyclic X K hqc hacyclic
      (Fh.totalRightDerived DerivedCategory.Qh W)
      (Fh.totalRightDerivedUnit DerivedCategory.Qh W)
  have hcomp : IsIso ((totalRightDerivedCompUnit Fh T.mapDerivedCategory).app
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K)) := by
    rw [totalRightDerivedCompUnit_app]
    exact Functor.map_isIso _ _
  have := isRightDerivedFunctor_totalRightDerived_comp Fh T.mapDerivedCategory
  exact Functor.isIso_rightDerivedUnit_app_of_iso _ _
    (totalRightDerivedCompUnit Fh T.mapDerivedCategory) (derivedGlobalSectionsOverUnit f) W
    (mapDerivedCategorySourceIso (sectionsFunctor X ⊤) T) _ hcomp

end AlgebraicGeometry

end
