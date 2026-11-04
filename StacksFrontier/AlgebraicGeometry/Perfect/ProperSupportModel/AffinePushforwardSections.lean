module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSections
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.AlgebraicGeometry.LeraySectionsCollapse.Basic

/-!
# Derived global sections over the base along an affine morphism

Let `A` be a ring, `f : X ⟶ Spec A` a morphism of schemes and `i : Z ⟶ X` an affine morphism of
schemes. For a quasi-coherent `𝒪_Z`-module `H` this file constructs an isomorphism

`RΓ(Z, H) ≅ RΓ(X, i_* H)`

in `D(A)`, the left side read over `A` through `i ≫ f` and the right side through `f`. Here
`RΓ(-, -)` is `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.derivedGlobalSectionsOverBase`,
the model of derived global sections over an affine base in which [Stacks, Tag 07VK] and
[Stacks, Tag 07VL] are stated.

This is [Stacks, Tag 089W] read in `D(A)` rather than degreewise. No hypothesis on `X`, `Z` or
`f` is needed beyond affineness of `i`; in particular no separatedness.

## Main definitions

* `baseSections`: global sections of an `𝒪_Y`-module as an `A`-module through `p : Y ⟶ Spec A`.
* `derivedGlobalSectionsOverBaseIsoPlus`: `RΓ(Y, F)` over `A` is the right derived functor of
  `baseSections p` on `D⁺` at `F[0]`.
* `derivedGlobalSectionsOverBaseMapIso`: `RΓ(Y, -)` over `A` on an isomorphism of modules.
* `derivedGlobalSectionsOverBasePushforwardIso`: **`RΓ(Z, H) ≅ RΓ(X, i_* H)`**.

## Main results

* `rightAcyclic_baseSections_pushforward`: the direct image of an injective module has acyclic
  global sections over the base.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.Cohomology.FlasqueAcyclic.evaluation_additive

variable {A : Type u} [CommRing A]

/-- Global sections of an `𝒪_Y`-module as a module over `Γ(Y, 𝒪_Y)`: evaluation at `⊤`, with
its target spelled `ModuleCat Γ(Y, ⊤)`. -/
def evTop (Y : Scheme.{u}) : Y.Modules ⥤ ModuleCat.{u} Γ(Y, ⊤) :=
  _root_.SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)

/-- Evaluation at `⊤` is additive. -/
instance (Y : Scheme.{u}) : (evTop Y).Additive :=
  Stacks.Cohomology.FlasqueAcyclic.evaluation_additive _ _

/-- Evaluation at `⊤` preserves finite limits. -/
instance (Y : Scheme.{u}) : PreservesFiniteLimits (evTop Y) := by
  change PreservesFiniteLimits (_root_.SheafOfModules.evaluation Y.ringCatSheaf (op ⊤))
  infer_instance

/-- Restriction of scalars along the structural ring map `A ⟶ Γ(Y, 𝒪_Y)` of `p : Y ⟶ Spec A`. -/
def baseRestrict {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) :
    ModuleCat.{u} Γ(Y, ⊤) ⥤ ModuleCat.{u} A :=
  ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom p).hom

section Instances

variable {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))

/-- Restriction of scalars along `A ⟶ Γ(Y, 𝒪_Y)` is additive. -/
instance : (baseRestrict p).Additive := inferInstanceAs (ModuleCat.restrictScalars _).Additive

/-- Restriction of scalars along `A ⟶ Γ(Y, 𝒪_Y)` preserves finite limits. -/
instance : PreservesFiniteLimits (baseRestrict p) :=
  inferInstanceAs (PreservesFiniteLimits (ModuleCat.restrictScalars _))

/-- Restriction of scalars along `A ⟶ Γ(Y, 𝒪_Y)` preserves finite colimits. -/
instance : PreservesFiniteColimits (baseRestrict p) :=
  inferInstanceAs (PreservesFiniteColimits (ModuleCat.restrictScalars _))

end Instances

/-- Global sections of an `𝒪_Y`-module, read as an `A`-module through `p : Y ⟶ Spec A`. -/
def baseSections {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) : Y.Modules ⥤ ModuleCat.{u} A :=
  evTop Y ⋙ baseRestrict p

/-- Global sections over the base form an additive functor. -/
instance {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) : (baseSections p).Additive :=
  inferInstanceAs (evTop Y ⋙ baseRestrict p).Additive

/-- **`RΓ(Y, F)` read over `A` is the right derived functor of `baseSections p` at `F[0]`.** -/
def derivedGlobalSectionsOverBaseIsoPlus {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))
    (F : Y.Modules) :
    derivedGlobalSectionsOverBase p F ≅ DerivedCategory.Plus.ι.obj
      ((baseSections p).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj F)) :=
  DerivedCategory.Plus.ι.mapIso
      (((baseRestrict p).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app _).symm) ≪≫
    DerivedCategory.Plus.ι.mapIso
      ((Functor.rightDerivedFunctorPlusCompIsoOfExact (evTop Y) (baseRestrict p)
        (baseSections p) (Iso.refl _)).app _)

/-- `RΓ(Y, -)` over the base applied to an isomorphism of `𝒪_Y`-modules: the image of the
isomorphism under the derived global sections functor, read over `A`. -/
def derivedGlobalSectionsOverBaseMapIso {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))
    {F F' : Y.Modules} (t : F ≅ F') :
    derivedGlobalSectionsOverBase p F ≅ derivedGlobalSectionsOverBase p F' :=
  (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom p).hom).mapDerivedCategory.mapIso
    (DerivedCategory.Plus.ι.mapIso
      ((Stacks.Cohomology.CechDerived.derivedGlobalSectionsFunctor Y.ringCatSheaf ⊤).mapIso t))

section Affine

variable {X Z : Scheme.{u}} (f : X ⟶ Spec (.of A)) (i : Z ⟶ X)

/-- Global sections over the base of an `𝒪_Z`-module are those of its direct image along `i`:
the two functors agree on the nose. -/
def baseSectionsCompIso :
    baseSections (i ≫ f) ≅ Scheme.Modules.pushforward i ⋙ baseSections f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Restriction of scalars along `A ⟶ Γ(X, 𝒪_X)` preserves homology. -/
instance : (baseRestrict f).PreservesHomology := Functor.preservesHomologyOfExact _

/-- Global sections over the base preserve finite limits. -/
instance : PreservesFiniteLimits (baseSections f) :=
  comp_preservesFiniteLimits (evTop X) (baseRestrict f)

/-- **The direct image of an injective module has acyclic global sections over the base**
([Stacks, Tag 01EX] part (2), read over `A`). -/
theorem rightAcyclic_baseSections_pushforward (I : Z.Modules) (hI : Injective I) :
    (baseSections f).rightAcyclic ((Scheme.Modules.pushforward i).obj I) :=
  Stacks.LeraySections.rightAcyclic_of_exact_comp (evTop X) (baseRestrict f) (baseSections f)
    (Iso.refl _)
    (Stacks.Cohomology.AffineComparison.rightAcyclic_moduleGlobalSections_pushforward_obj i I hI)

variable [IsAffineHom i]

/-- **`RΓ(Z, H) ≅ RΓ(X, i_* H)` over the base, for an affine morphism `i`** ([Stacks, Tag 089W],
in `D(A)`). Let `f : X ⟶ Spec A`, let `i : Z ⟶ X` be affine and let `H` be a quasi-coherent
`𝒪_Z`-module. Then the derived global sections of `H`, read over `A` through `i ≫ f`, are those
of `i_* H`, read over `A` through `f`. -/
def derivedGlobalSectionsOverBasePushforwardIso (H : Z.Modules) [H.IsQuasicoherent] :
    derivedGlobalSectionsOverBase (i ≫ f) H ≅
      derivedGlobalSectionsOverBase f ((Scheme.Modules.pushforward i).obj H) :=
  derivedGlobalSectionsOverBaseIsoPlus (i ≫ f) H ≪≫
    DerivedCategory.Plus.ι.mapIso
      ((Functor.rightDerivedFunctorPlusNatIso (baseSectionsCompIso f i)).app _) ≪≫
    DerivedCategory.Plus.ι.mapIso
      ((Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic (Scheme.Modules.pushforward i)
        (baseSections f) (rightAcyclic_baseSections_pushforward f i)).app _) ≪≫
    DerivedCategory.Plus.ι.mapIso
      ((baseSections f).rightDerivedFunctorPlus.mapIso
        (Stacks.Cohomology.AffineComparison.rightDerivedFunctorPlusObjSingleIso
          (Scheme.Modules.pushforward i) H
          (Stacks.Cohomology.AffineComparison.rightAcyclic_pushforward_of_isAffineHom i H))) ≪≫
    (derivedGlobalSectionsOverBaseIsoPlus f _).symm

end Affine

end Stacks.AlgebraicGeometry.ProperSupportModel
