module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPushforwardForget

/-!
# The derived internal hom and the derived pushforward

This file records [Stacks, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP), which defines

1. for a ringed site `(C, O)`, sheaves of differential graded `O`-algebras `𝒜`, `ℬ` and a
   differential graded `(𝒜, ℬ)`-bimodule `𝒩`, the *derived internal hom*
   `RSheafHom_ℬ(𝒩, -) : D(ℬ, d) ⥤ D(𝒜, d)`, the right derived extension of the internal hom functor
   `SheafHom^dg_ℬ(𝒩, -)`;
2. for a morphism of ringed topoi `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)`, a sheaf of differential
   graded `O_C`-algebras `𝒜`, one of `O_D`-algebras `ℬ` and a homomorphism `φ : ℬ ⟶ f_*𝒜`, the
   *derived pushforward* `Rf_* : D(𝒜, d) ⥤ D(ℬ, d)`, the right derived extension of `f_*`.

The two functors are `SheafOfModules.DifferentialGradedModule.derivedSheafHom` and
`SheafOfModules.DifferentialGradedModule.derivedToposPushforward`; each part below says that the
functor with its comparison map is the right derived functor of the functor it extends (followed
by the localization), and that it is computed on graded injective K-injective modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.derivedSheafHom_isRightDerivedFunctor`: Tag 0FTP (1).
* `SheafOfModules.DifferentialGradedModule.derivedToposPushforward_isRightDerivedFunctor`:
  Tag 0FTP (2).

## Implementation notes

A homomorphism of sheaves of differential graded algebras in this development is a morphism of
complexes respecting the graded multiplication, with no unit condition; the homomorphisms of
differential graded algebras of the source preserve `1`, so part (2) is stated for a unital `φ`.
The ringed sites and topoi, and the modules, are taken in one universe, where the derived
categories `D(𝒜, d)` are constructed.

## References

* [Stacks Project, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP)
* [Stacks Project, Tag 0FTN](https://stacks.math.columbia.edu/tag/0FTN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe u

namespace SheafOfModules.DifferentialGradedModule

open Stacks.Sheaves.RingedToposModules

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
  AlgebraicGeometry.RingedTopos.hasSheafify_addCommGrpCat
  AlgebraicGeometry.RingedTopos.wEqualsLocallyBijective_addCommGrpCat
  AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat

/-- **Stacks Project, Tag 0FTP (1): the derived internal hom.** Let `(C, O)` be a ringed site, let
`𝒜`, `ℬ` be sheaves of differential graded `O`-algebras and let `𝒩` be a differential graded
`(𝒜, ℬ)`-bimodule. The derived internal hom `RSheafHom_ℬ(𝒩, -) : D(ℬ, d) ⥤ D(𝒜, d)`, with its
comparison map, is the right derived functor of the internal hom functor
`K(SheafHom^dg_ℬ(𝒩, -)) : K(Mod(ℬ, d)) ⥤ K(Mod(𝒜, d))` followed by the localization, and its value
on a graded injective K-injective module `ℐ` is `SheafHom^dg_ℬ(𝒩, ℐ)`. -/
@[stacks 0FTP "(1) derived internal hom"]
theorem derivedSheafHom_isRightDerivedFunctor {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (N : DifferentialGradedBimodule.{u, u, u} A B) :
    (derivedSheafHom N).IsRightDerivedFunctor (derivedSheafHomUnit N)
        (quasiIsomorphisms.{u, u, u} B) ∧
      ∀ I : DifferentialGradedModule.{u, u, u} B, IsDGInjective I →
        IsIso ((derivedSheafHomUnit N).app ((HomotopyCategory.quotient B).obj I)) :=
  ⟨inferInstance, fun _ hI => isIso_derivedSheafHomUnit_app N hI⟩

/-- **Stacks Project, Tag 0FTP (2): the derived pushforward.** Let
`(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, let `𝒜` be a sheaf of
differential graded `O_C`-algebras, `ℬ` one of `O_D`-algebras and `φ : ℬ ⟶ f_*𝒜` a homomorphism
of sheaves of differential graded `O_D`-algebras; these preserve `1` in the source, which is the
hypothesis `unital`. The derived pushforward `Rf_* : D(𝒜, d) ⥤ D(ℬ, d)`, with its comparison map,
is the right derived functor of the pushforward `K(f_*) : K(Mod(𝒜, d)) ⥤ K(Mod(ℬ, d))` followed by
the localization, and its value on a graded injective K-injective module `ℐ` is `f_*ℐ`. -/
@[stacks 0FTP "(2) derived pushforward"]
theorem derivedToposPushforward_isRightDerivedFunctor
    {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
    (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))
    (B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O))
    (φ : B ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := Y.O)
      (toposDirectImageModules (X := X) (Y := Y) f) A) (unital : φ.IsUnital) :
    (derivedToposPushforward f A B φ unital).IsRightDerivedFunctor
        (derivedToposPushforwardUnit f A B φ unital) (quasiIsomorphisms.{u, u, u} A) ∧
      ∀ I : DifferentialGradedModule.{u, u, u} A, IsDGInjective I →
        IsIso ((derivedToposPushforwardUnit f A B φ unital).app
          ((HomotopyCategory.quotient A).obj I)) :=
  ⟨inferInstance, fun _ hI => isIso_derivedToposPushforwardUnit_app f A B φ unital hI⟩

end SheafOfModules.DifferentialGradedModule

end
