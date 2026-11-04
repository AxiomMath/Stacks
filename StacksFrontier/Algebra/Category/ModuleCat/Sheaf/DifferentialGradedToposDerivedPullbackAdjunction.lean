module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPullbackComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforwardAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedSheafHom

/-!
# The derived pullback is left adjoint to the derived pushforward

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, let `A` be a sheaf of
differential graded `O_C`-algebras, let `B` be a sheaf of differential graded `O_D`-algebras and
let `φ : B ⟶ f_*A` be a homomorphism of sheaves of differential graded algebras. This file proves
[Stacks, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR): the derived pushforward
`Rf_* : D(A, d) ⥤ D(B, d)` of Tag 0FTP is right adjoint to the derived pullback
`Lf^* : D(B, d) ⥤ D(A, d)` of Tag 0FTG.

The source's proof is Derived Categories, Lemma 13.30.1 (Tag 0FND, Mathlib's
`CategoryTheory.Adjunction.derived`) applied to the adjunction `f^* ⊣ f_*` of differential graded
modules (Tag 0FRU) descended to the homotopy categories. Here `f^*M` is the constructed pullback
`f^*M ⊗_{f^*B} A`, and its adjunction to the direct image is
`SheafOfModules.DifferentialGradedModule.toposBaseChangeAdjunction`; `Lf^*` is the functor of
Tag 0FTF at the diagonal bimodule, the left derived functor of `M ↦ (f^*M ⊗_{f^*B} A) ⊗_A A`,
so that adjunction is read through `f^*M ⊗_A A ≅ f^*M`.

The two absoluteness conditions of `CategoryTheory.Adjunction.derived` hold because `Lf^*` is
computed on good modules (Tags 0FSA, 0FSH) and `Rf_*` on graded injective K-injective modules
(Tag 0FT0).

## Main definitions

* `SheafOfModules.DifferentialGradedModule.homotopyToposPullbackPushforwardAdjunction`: the
  adjunction `f^* ⊣ f_*` on homotopy categories.
* `SheafOfModules.DifferentialGradedModule.derivedPullbackRingedToposAdjunction`: **Tag 0FTR**,
  `Lf^* ⊣ Rf_*`.

## References

* [Stacks Project, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FND](https://stacks.math.columbia.edu/tag/0FND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules

universe u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

attribute [local instance] AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat
  quasiIsomorphisms_hasRightCalculusOfFractions_topos

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
  {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  (φ : B ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := Y.O)
    (toposDirectImageModules (X := X) (Y := Y) f) A) (hφ : φ.IsUnital)

/-- **The adjunction `f^* ⊣ f_*` on homotopy categories**: the adjunction of differential graded
modules between the pullback `M ↦ f^*M ⊗_{f^*B} A` and the direct image (Tag 0FRU), read through
`f^*M ⊗_A A ≅ f^*M` and descended along the two quotient functors, both functors preserving
homotopy. -/
def homotopyToposPullbackPushforwardAdjunction :
    homotopyToposPullbackTensor f φ hφ A.diagonalBimodule ⊣
      homotopyToposPushforward (toposDirectImageModules (X := X) (Y := Y) f) φ hφ :=
  HomotopyCategory.descendAdjunction
    ((toposBaseChangeAdjunction f φ hφ).ofNatIsoLeft
      (toposPullbackTensorDiagonalNatIso f φ hφ).symm)
    (preservesHomotopic_toposPushforward _ φ hφ)
    (preservesHomotopic_toposPullbackTensor f φ hφ A.diagonalBimodule)

/-- The absoluteness of the derived pullback needed to derive the adjunction: `Rf_* ∘ Lf^*` is
still a left derived functor, `Lf^*` being computed on good modules. -/
instance isLeftDerivedFunctor_derivedPullbackRingedTopos_comp_derivedToposPushforward :
    (derivedPullbackRingedTopos f φ hφ ⋙ derivedToposPushforward f A B φ hφ).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedPullbackRingedToposCounit f φ hφ)
          (derivedToposPushforward f A B φ hφ))
      (quasiIsomorphisms.{u, u, u} B) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions
    (quasiIsomorphisms.{u, u, u} B) (IsGoodObj (B := B)) (exists_isGoodObj_quasiIso (B := B))
    (homotopyToposPullbackTensor f φ hφ A.diagonalBimodule ⋙ toDerivedCategory A)
    (fun s hs hZ hZ' => isIso_goodDerivedSource_map _
      (preservesHomotopic_toposPullbackTensor f φ hφ A.diagonalBimodule)
      (quasiIso_toposPullbackTensor_map_of_isGood f φ hφ A.diagonalBimodule) s hs hZ hZ')
    (toDerivedCategory.{u, u, u} B) (derivedPullbackRingedTopos f φ hφ)
    (derivedPullbackRingedToposCounit f φ hφ) (derivedToposPushforward f A B φ hφ)

/-- The absoluteness of the derived pushforward needed to derive the adjunction: `Lf^* ∘ Rf_*`
is still a right derived functor, `Rf_*` being computed on graded injective K-injective modules
(Tag 0FT0). -/
instance isRightDerivedFunctor_derivedToposPushforward_comp_derivedPullbackRingedTopos :
    (derivedToposPushforward f A B φ hφ ⋙ derivedPullbackRingedTopos f φ hφ).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedToposPushforwardUnit f A B φ hφ)
          (derivedPullbackRingedTopos f φ hφ) ≫ (Functor.associator _ _ _).hom)
      (quasiIsomorphisms.{u, u, u} A) :=
  Functor.isRightDerivedFunctor_comp_of_coresolutions (quasiIsomorphisms.{u, u, u} A)
    (derivedToposPushforwardUnit f A B φ hφ) (derivedPullbackRingedTopos f φ hφ)
    (exists_quasiIso_bijective_toDerivedCategory_map (X := X.toRingedSite) A)

/-- **Stacks Project, Tag 0FTR.** Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of
ringed topoi, let `A` be a differential graded `O_C`-algebra, let `B` be a differential graded
`O_D`-algebra and let `φ : B ⟶ f_*A` be a homomorphism of differential graded `O_D`-algebras.
Then `Rf_* : D(A, d) ⥤ D(B, d)` is right adjoint to `Lf^* : D(B, d) ⥤ D(A, d)`.

`Lf^*` is the derived pullback of Tag 0FTG (2), `derivedPullbackRingedTopos`, and `Rf_*` the
derived pushforward of Tag 0FTP (2), `derivedToposPushforward`. The adjunction is derived
(Tag 0FND, `CategoryTheory.Adjunction.derived`) from the adjunction `f^* ⊣ f_*` of homotopy
categories, `homotopyToposPullbackPushforwardAdjunction`, which is Tag 0FRU descended. -/
@[stacks 0FTR]
def derivedPullbackRingedToposAdjunction :
    derivedPullbackRingedTopos f φ hφ ⊣ derivedToposPushforward f A B φ hφ :=
  (homotopyToposPullbackPushforwardAdjunction f φ hφ).derived (quasiIsomorphisms.{u, u, u} B)
    (quasiIsomorphisms.{u, u, u} A) (derivedPullbackRingedToposCounit f φ hφ)
    (derivedToposPushforwardUnit f A B φ hφ)

end SheafOfModules.DifferentialGradedModule

end
