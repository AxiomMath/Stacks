module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.DerivedDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductOfToposHom

/-!
# The relative cup product on `D(X_étale, Λ)`

For a morphism of schemes `f : X ⟶ Y` and a commutative ring `Λ`, the relative cup product of
[Stacks, Tag 0B6C]

`Rf_*K ⊗^L_Λ Rf_*L ⟶ Rf_*(K ⊗^L_Λ L)`

for `K`, `L` in `D(X_étale, Λ)`, where `Rf_*` is the unbounded derived direct image
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded` and `⊗^L_Λ` is
`Stacks.EtaleCohomology.etaleDerivedTensor`. It is the relative cup product of the morphism of
ringed topoi `(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)`
(`Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct`), read on `D(X_étale, Λ)`
and `D(Y_étale, Λ)` through `Stacks.EtaleCohomology.etaleDerivedEquivalence` and the comparison
`Stacks.EtaleCohomology.etaleDerivedPushforwardIso` of derived direct images.

## Main definitions

* `Stacks.EtaleCohomology.etaleRingedRelativeCupProduct`: the relative cup product of the
  morphism of constant ringed topoi, as a natural transformation of bifunctors.
* `Stacks.EtaleCohomology.etaleRelativeCupProduct`: the relative cup product on
  `D(X_étale, Λ)`, as a natural transformation of bifunctors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.Cohomology.RelativeCupProductOfToposHom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The relative cup product of [Stacks, Tag 0B6C] for the morphism of constant ringed topoi**
`(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)`, as a natural transformation of bifunctors. -/
def etaleRingedRelativeCupProduct :
    (etaleRingedDerivedPushforward.{u, r} Λ f ⋙
        Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (etaleRingedSite.{u, r} Λ Y).O) ⋙
      (Functor.whiskeringLeft _ _ _).obj (etaleRingedDerivedPushforward.{u, r} Λ f) ⟶
    Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (etaleRingedSite.{u, r} Λ X).O ⋙
      (Functor.whiskeringRight _ _ _).obj (etaleRingedDerivedPushforward.{u, r} Λ f) where
  app K :=
    { app := fun L => relativeCupProduct (etaleRingedSiteHom.{u, r} Λ f).ringedToposHom K L
      naturality := fun _ _ l =>
        relativeCupProduct_naturality_right (etaleRingedSiteHom.{u, r} Λ f).ringedToposHom K l }
  naturality _ _ k := by
    ext L
    exact relativeCupProduct_naturality_left (etaleRingedSiteHom.{u, r} Λ f).ringedToposHom k L

/-- **The relative cup product of [Stacks, Tag 0B6C] on `D(X_étale, Λ)`**:
`Rf_*K ⊗^L_Λ Rf_*L ⟶ Rf_*(K ⊗^L_Λ L)`, natural in `K` and `L`. -/
def etaleRelativeCupProduct :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙ etaleDerivedTensor.{u, r} Λ Y) ⋙
        (Functor.whiskeringLeft _ _ _).obj (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f) ⟶
      etaleDerivedTensor.{u, r} Λ X ⋙
        (Functor.whiskeringRight _ _ _).obj (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f) :=
  TensorHomAdjunction.transportCup (etaleDerivedEquivalence.{u, r} Λ X)
    (etaleDerivedEquivalence.{u, r} Λ Y) (etaleDerivedPushforwardIso.{u, r} Λ f)
    (etaleRingedRelativeCupProduct.{u, r} Λ f)

end Stacks.EtaleCohomology

end
