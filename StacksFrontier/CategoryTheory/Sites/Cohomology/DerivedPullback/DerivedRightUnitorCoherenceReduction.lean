module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedUnitorCoherenceUnitPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightUnitorNaturality
public import StacksFrontier.AlgebraicGeometry.Duality.RightUnitorCoherenceInvariance

/-!
# The right-unitor coherence of Stacks 07A4 needs checking on flat K-flat models only

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a functor of the
underlying sites which is a morphism of sites, and let `ν : Lf^*(𝒪_D[0]) ≅ 𝒪_C[0]` be an
isomorphism. The **right-unitor coherence** of the comparison of [Stacks, Tag 07A4] at an object
`Z` of `D(𝒪_D)` is the equation

`Lf^*(Z ⊗^𝐋_{𝒪_D} 𝒪_D) ⟶ Lf^*Z ⊗^𝐋_{𝒪_C} Lf^*𝒪_D`, then `𝟙 ⊗ ν`, then `ρ_C`, equals `Lf^*ρ_D`.

This file shows that it holds at every `Z` as soon as it holds at `Z = Q P` for every K-flat
complex `P` of `𝒪_D`-modules with flat terms.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.DerivedRightUnitorCoherenceAt`: the right-unitor coherence of
  [Stacks, Tag 07A4] at one object of `D(𝒪_D)`, written out as a proposition.

## Main results

* `Stacks.Sheaves.DerivedPullback.derivedRightUnitorCoherence_of_flatKFlat`: **the coherence at
  every object of `D(𝒪_D)`, from the coherence at `Q P` for K-flat `P` with flat terms only.**

## Implementation notes

The right unitors are the components of the natural isomorphism
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso`, whose naturality on
both `D(𝒪_D)` and `D(𝒪_C)` the reduction uses.

The essentially surjective functor along which the equation is reduced is
`Stacks.Sheaves.DerivedPullback.flatKFlatModelsQ`, a localization functor by
`Stacks.Sheaves.DerivedPullback.flatKFlatModelsQ_isLocalization`; its value at a model is
identified with `Q` of the underlying complex by `DerivedCategory.quotientCompQhIso`.

The derived tensor product and its unitor are stated for an `AlgebraicGeometry.RingedSite`; they
are used here at the ringed site `⟨X.C, X.J, X.O⟩` built from the three fields of the ringed
topos.

## References

* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite

open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **The right-unitor coherence of [Stacks, Tag 07A4] at one object `Z` of `D(𝒪_D)`.** The
comparison of [Stacks, Tag 07A4] at `(Z, 𝒪_D[0])`, followed by `𝟙 ⊗ ν` for a unit comparison
`ν : Lf^*(𝒪_D[0]) ≅ 𝒪_C[0]` and by the right unitor of `⊗^𝐋_{𝒪_C}`, is `Lf^*` of the right unitor
of `⊗^𝐋_{𝒪_D}`. -/
def DerivedRightUnitorCoherenceAt
    (ν : (derivedPullback f).obj (unitObject ⟨Y.C, Y.J, Y.O⟩) ≅
      unitObject ⟨X.C, X.J, X.O⟩)
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    Prop :=
  (derivedPullbackTensorIso f hmos).hom.app (Z, unitObject ⟨Y.C, Y.J, Y.O⟩) ≫
      (Functor.uncurry.obj (derivedTensorProductFunctor X.O)).map
        ((𝟙 ((derivedPullback f).obj Z) ×ₘ ν.hom) :
          (((derivedPullback f).obj Z,
              (derivedPullback f).obj (unitObject ⟨Y.C, Y.J, Y.O⟩)) : _ × _) ⟶
            ((derivedPullback f).obj Z, unitObject ⟨X.C, X.J, X.O⟩)) ≫
        (((canonicalDerivedTensorProduct X.O).rightUnitorNatIso ⟨X.C, X.J, X.O⟩).app
          ((derivedPullback f).obj Z)).hom =
    (derivedPullback f).map
      (((canonicalDerivedTensorProduct Y.O).rightUnitorNatIso ⟨Y.C, Y.J, Y.O⟩).app Z).hom

/-- **The right-unitor coherence of [Stacks, Tag 07A4] needs checking on flat K-flat models
only.** If the equation holds at `Q P` for every K-flat complex `P` of `𝒪_D`-modules with flat
terms, it holds at every object of `D(𝒪_D)`. -/
theorem derivedRightUnitorCoherence_of_flatKFlat
    (ν : (derivedPullback f).obj (unitObject ⟨Y.C, Y.J, Y.O⟩) ≅
      unitObject ⟨X.C, X.J, X.O⟩)
    (h : ∀ (P : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
      CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i)) →
      DerivedRightUnitorCoherenceAt f hmos ν (DerivedCategory.Q.obj P))
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    DerivedRightUnitorCoherenceAt f hmos ν Z := by
  have hloc := flatKFlatModelsQ_isLocalization Y
  have hes := Localization.essSurj (flatKFlatModelsQ Y) (flatKFlatModelsW Y)
  have hnatY := fun {A B : DerivedModules Y.O} (u : A ⟶ B) =>
    DerivedTensorProduct.rightUnitorNatIso_naturality_uncurry ⟨Y.C, Y.J, Y.O⟩
      (canonicalDerivedTensorProduct Y.O) u
  have hnatX := fun {A B : DerivedModules X.O} (u : A ⟶ B) =>
    DerivedTensorProduct.rightUnitorNatIso_naturality_uncurry ⟨X.C, X.J, X.O⟩
      (canonicalDerivedTensorProduct X.O) u
  exact Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherence_of_essSurj
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
    (derivedPullbackTensorIso f hmos).hom
    (fun W => ((canonicalDerivedTensorProduct Y.O).rightUnitorNatIso ⟨Y.C, Y.J, Y.O⟩).app W)
    (fun W => ((canonicalDerivedTensorProduct X.O).rightUnitorNatIso ⟨X.C, X.J, X.O⟩).app W)
    ν (flatKFlatModelsQ Y)
    hnatY hnatX
    (fun M => Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherence_of_iso _ _ _ _ _ _
      hnatY hnatX
      ((DerivedCategory.quotientCompQhIso _).app M.obj.as)
      (h M.obj.as M.property.1 M.property.2)) Z

end Stacks.Sheaves.DerivedPullback

end
