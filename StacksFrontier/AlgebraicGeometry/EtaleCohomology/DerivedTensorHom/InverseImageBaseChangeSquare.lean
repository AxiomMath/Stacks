module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.TorsionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ProjectionFormula
public import StacksFrontier.CategoryTheory.Adjunction.TransportedBaseChangeSquare
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BraidingIsoEqCanonicalBraiding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorSquareCompatible

/-!
# Base change squares on `D(X_étale, Λ)`

Let `Λ` be a commutative ring and let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. On the unbounded derived categories `D(-_étale, Λ)` this
file provides

* the identification `g⁻¹ ⋙ f'⁻¹ ≅ f⁻¹ ⋙ g'⁻¹` of the two composite inverse images
  (`etaleModuleDerivedInverseImageSquareIso`), read off the one of the constant ringed topoi;
* the base change map `g⁻¹ Rf_* ⟶ Rf'_* g'⁻¹` (`etaleModuleDerivedSquareBaseChange`), the mate of
  that identification for the adjunctions `etaleModuleDerivedInverseImageAdj`; it is invertible
  for `f` proper, the square cartesian and `Λ` torsion (proper base change, [Stacks, Tag 0F0C]);
* [Stacks, Tag 0H9A]: the cup product `Rf_*K ⊗^L Rf_*L ⟶ Rf_*(K ⊗^L L)` of the adjunction
  `f⁻¹ ⊣ Rf_*` and of the comparison of [Stacks, Tag 07A4] is compatible with the base change
  map (`etaleModuleDerivedSquareBaseChange_adjunctionCupProduct`);
* the comparison `g⁻¹(A ⊗^L B) ≅ g⁻¹A ⊗^L g⁻¹B` of [Stacks, Tag 07A4] carries the commutativity
  constraint of [Stacks, Tag 0FPT] on `D(Y_étale, Λ)` to the one on `D(Y'_étale, Λ)`
  (`etaleDerivedInverseImageTensorIso_braiding`).

All are transported from the constant ringed topoi along
`Stacks.EtaleCohomology.etaleDerivedEquivalence` by the abstract lemmas of
`StacksFrontier/CategoryTheory/Adjunction/TransportedBaseChangeSquare.lean`; the statements mention
the étale derived categories only.

## References

* [Stacks Project, Tag 0H9A](https://stacks.math.columbia.edu/tag/0H9A)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0F0C](https://stacks.math.columbia.edu/tag/0F0C)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Prod

attribute [local instance] HasDerivedCategory.standard
attribute [local instance high]
  Stacks.EtaleCohomology.instHasSheafifyCRingedToposEtaleRingedSiteJType
attribute [local instance]
  Stacks.EtaleCohomology.etaleRingedPullbackOnHomotopy_hasLeftDerivedFunctor
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

universe u

namespace Stacks.EtaleCohomology

section Square

variable (Λ : Type) [CommRing Λ] {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
  (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- **The two composite inverse images around a commutative square agree** on the étale derived
categories: `g⁻¹ ⋙ f'⁻¹ ≅ f⁻¹ ⋙ g'⁻¹`, the identification of the two composite derived pullbacks
of the constant ringed topoi (`AlgebraicGeometry.RingedToposHom.TwoIso.derivedPullbackSquareIso`)
read through `Stacks.EtaleCohomology.etaleDerivedEquivalence`. -/
def etaleModuleDerivedInverseImageSquareIso :
    etaleModuleDerivedInverseImage.{u, 0} Λ g ⋙ etaleModuleDerivedInverseImage.{u, 0} Λ f' ≅
      etaleModuleDerivedInverseImage.{u, 0} Λ f ⋙ etaleModuleDerivedInverseImage.{u, 0} Λ g' :=
  let s := etaleRingedToposHomSquareTwoIso.{u, 0} Λ f g f' g' w
  let sq₀ := RingedToposHom.TwoIso.derivedPullbackSquareIso.{u + 1} s
  let θ : etaleRingedDerivedPullback.{u, 0} Λ g ⋙ etaleRingedDerivedPullback.{u, 0} Λ f' ≅
      etaleRingedDerivedPullback.{u, 0} Λ f ⋙ etaleRingedDerivedPullback.{u, 0} Λ g' :=
    Stacks.AffineProjectionFormula.squareCompositeIso sq₀ (Iso.refl _)
  Stacks.CategoryTheory.ProjectionMapTransport.transportSquareIso
    (etaleDerivedEquivalence.{u, 0} Λ Y) (etaleDerivedEquivalence.{u, 0} Λ X)
    (etaleDerivedEquivalence.{u, 0} Λ Y') (etaleDerivedEquivalence.{u, 0} Λ X')
    (etaleRingedDerivedPullbackIso.{u, 0} Λ f) (etaleRingedDerivedPullbackIso.{u, 0} Λ f')
    (etaleRingedDerivedPullbackIso.{u, 0} Λ g) (etaleRingedDerivedPullbackIso.{u, 0} Λ g') θ

/-- **The base change map** `g⁻¹ Rf_* M ⟶ Rf'_* g'⁻¹ M` on the unbounded étale derived
categories of a commutative square: the mate, for the adjunctions `f⁻¹ ⊣ Rf_*` and
`f'⁻¹ ⊣ Rf'_*` of `etaleModuleDerivedInverseImageAdj`, of the identification of the two
composite inverse images. -/
def etaleModuleDerivedSquareBaseChange (M : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedInverseImage.{u, 0} Λ g).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f).obj M) ⟶
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f').obj
        ((etaleModuleDerivedInverseImage.{u, 0} Λ g').obj M) :=
  Stacks.CategoryTheory.BaseChange.map (etaleModuleDerivedInverseImageAdj.{u, 0} Λ f)
    (etaleModuleDerivedInverseImageAdj.{u, 0} Λ f')
    (etaleModuleDerivedInverseImageSquareIso Λ f g f' g' w) (Iso.refl _) M

/-- **Proper base change on `D(X_étale, Λ)`, for the mate base change map.** For `f` proper, the
square cartesian and `Λ` torsion, the base change map `g⁻¹ Rf_* M ⟶ Rf'_* g'⁻¹ M` is invertible
for every unbounded `M`: it is the base change map of the constant ringed topoi read through the
equivalences, which is invertible by
`Stacks.EtaleCohomology.isIso_squareBaseChangeMap_etaleRingedToposHomSquareTwoIso_of_isProper`. -/
theorem isIso_etaleModuleDerivedSquareBaseChange_of_isProper (hΛ : IsAddTorsion Λ)
    [IsProper f] (sq : IsPullback g' f' f g) (M : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    IsIso (etaleModuleDerivedSquareBaseChange Λ f g f' g' sq.w M) :=
  (Stacks.CategoryTheory.ProjectionMapTransport.isIso_baseChangeMap_transportSquareIso_iff
    (etaleDerivedEquivalence.{u, 0} Λ Y) (etaleDerivedEquivalence.{u, 0} Λ X)
    (etaleDerivedEquivalence.{u, 0} Λ Y') (etaleDerivedEquivalence.{u, 0} Λ X')
    (etaleRingedDerivedPullbackIso.{u, 0} Λ f) (etaleRingedDerivedPullbackIso.{u, 0} Λ f')
    (etaleRingedDerivedPullbackIso.{u, 0} Λ g) (etaleRingedDerivedPullbackIso.{u, 0} Λ g')
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction.{u + 1}
      (etaleRingedToposHom.{u, 0} Λ f))
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction.{u + 1}
      (etaleRingedToposHom.{u, 0} Λ f'))
    (etaleDerivedPushforwardIsoConj.{u, 0} Λ f) (etaleDerivedPushforwardIsoConj.{u, 0} Λ f')
    (RingedToposHom.TwoIso.derivedPullbackSquareIso.{u + 1}
      (etaleRingedToposHomSquareTwoIso.{u, 0} Λ f g f' g' sq.w)) (Iso.refl _) M).2
    (isIso_squareBaseChangeMap_etaleRingedToposHomSquareTwoIso_of_isProper Λ hΛ f sq _)

/-- **[Stacks, Tag 0H9A] on `D(X_étale, Λ)`.** For a commutative square of schemes and
arbitrary unbounded `G`, `H` in `D(X_étale, Λ)`, the comparison `g⁻¹(A ⊗^L B) ≅ g⁻¹A ⊗^L g⁻¹B` of
[Stacks, Tag 07A4], followed by the base change map in both factors and by the cup product of
`f'⁻¹ ⊣ Rf'_*`, is `g⁻¹` of the cup product of `f⁻¹ ⊣ Rf_*`, followed by the base change map at
`G ⊗^L H` and by `Rf'_*` of the comparison along `g'`. The cup products are
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct` of the adjunctions
`etaleModuleDerivedInverseImageAdj` and the comparisons `etaleDerivedInverseImageTensorIso`. -/
theorem etaleModuleDerivedSquareBaseChange_adjunctionCupProduct
    (G H : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (etaleDerivedInverseImageTensorIso.{u, 0} Λ g).hom.app
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f).obj G,
            (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f).obj H) ≫
        (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} Λ Y')).map
            (etaleModuleDerivedSquareBaseChange Λ f g f' g' w G ×ₘ
              etaleModuleDerivedSquareBaseChange Λ f g f' g' w H) ≫
          Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct
            (etaleModuleDerivedInverseImageAdj.{u, 0} Λ f')
            (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} Λ Y'))
            (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} Λ X'))
            (etaleDerivedInverseImageTensorIso.{u, 0} Λ f').hom
            ((etaleModuleDerivedInverseImage.{u, 0} Λ g').obj G)
            ((etaleModuleDerivedInverseImage.{u, 0} Λ g').obj H) =
      (etaleModuleDerivedInverseImage.{u, 0} Λ g).map
          (Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct
            (etaleModuleDerivedInverseImageAdj.{u, 0} Λ f)
            (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} Λ Y))
            (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} Λ X))
            (etaleDerivedInverseImageTensorIso.{u, 0} Λ f).hom G H) ≫
        etaleModuleDerivedSquareBaseChange Λ f g f' g' w
            (((etaleDerivedTensor.{u, 0} Λ X).obj G).obj H) ≫
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f').map
            ((etaleDerivedInverseImageTensorIso.{u, 0} Λ g').hom.app (G, H)) :=
  Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_baseChange_square
    (etaleModuleDerivedInverseImageAdj.{u, 0} Λ f) (etaleModuleDerivedInverseImageAdj.{u, 0} Λ f')
    (etaleModuleDerivedInverseImageSquareIso Λ f g f' g' w) (Iso.refl _)
    (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} Λ Y))
    (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} Λ Y'))
    (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} Λ X))
    (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} Λ X'))
    (etaleDerivedInverseImageTensorIso.{u, 0} Λ f).hom
    (etaleDerivedInverseImageTensorIso.{u, 0} Λ f').hom
    (etaleDerivedInverseImageTensorIso.{u, 0} Λ g).hom
    (etaleDerivedInverseImageTensorIso.{u, 0} Λ g').hom G H
    (Stacks.CategoryTheory.ProjectionMapTransport.tensorComparisonCompatible_transportSquareIso
      (etaleDerivedEquivalence.{u, 0} Λ Y) (etaleDerivedEquivalence.{u, 0} Λ X)
      (etaleDerivedEquivalence.{u, 0} Λ Y') (etaleDerivedEquivalence.{u, 0} Λ X')
      (etaleRingedDerivedPullbackIso.{u, 0} Λ f) (etaleRingedDerivedPullbackIso.{u, 0} Λ f')
      (etaleRingedDerivedPullbackIso.{u, 0} Λ g) (etaleRingedDerivedPullbackIso.{u, 0} Λ g')
      (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso
        (etaleRingedToposHom.{u, 0} Λ f))
      (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso
        (etaleRingedToposHom.{u, 0} Λ f'))
      (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso
        (etaleRingedToposHom.{u, 0} Λ g))
      (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso
        (etaleRingedToposHom.{u, 0} Λ g'))
      (RingedToposHom.TwoIso.derivedPullbackSquareIso.{u + 1}
        (etaleRingedToposHomSquareTwoIso.{u, 0} Λ f g f' g' w)) (Iso.refl _) _ _
      (RingedToposHom.TwoIso.tensorComparisonCompatible.{u + 1}
        (etaleRingedToposHomSquareTwoIso.{u, 0} Λ f g f' g' w) _ _))

end Square

section Braiding

variable (Λ : Type) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- **The comparison of [Stacks, Tag 07A4] is braided on `D(-_étale, Λ)`**: `g⁻¹` of the
commutativity constraint `A ⊗^L B ≅ B ⊗^L A` of [Stacks, Tag 0FPT], followed by the comparison
`g⁻¹(B ⊗^L A) ≅ g⁻¹B ⊗^L g⁻¹A`, is the comparison followed by the commutativity constraint of
`D(X_étale, Λ)`. -/
theorem etaleDerivedInverseImageTensorIso_braiding
    (A B : DerivedCategory (EtaleModules.{u, 0} Λ Y)) :
    (etaleModuleDerivedInverseImage.{u, 0} Λ g).map
        (etaleDerivedTensorBraidingIso.{u, 0} Λ Y A B).hom ≫
        (etaleDerivedInverseImageTensorIso.{u, 0} Λ g).hom.app (B, A) =
      (etaleDerivedInverseImageTensorIso.{u, 0} Λ g).hom.app (A, B) ≫
        (etaleDerivedTensorBraidingIso.{u, 0} Λ X
          ((etaleModuleDerivedInverseImage.{u, 0} Λ g).obj A)
          ((etaleModuleDerivedInverseImage.{u, 0} Λ g).obj B)).hom :=
  Stacks.CategoryTheory.ProjectionMapTransport.transportTensorIso_braiding
    (etaleDerivedEquivalence.{u, 0} Λ Y) (etaleDerivedEquivalence.{u, 0} Λ X)
    (etaleRingedDerivedPullbackIso.{u, 0} Λ g)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso
      (etaleRingedToposHom.{u, 0} Λ g))
    (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
      (etaleRingedSite.{u, 0} Λ Y) _).hom
    (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
      (etaleRingedSite.{u, 0} Λ X) _).hom
    (fun a b => by
      rw [Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso_hom_app_app,
        Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso_hom_app_app,
        ← Stacks.DerivedTensor.RingedSite.canonicalBraidingHom_eq_braidingIso,
        ← Stacks.DerivedTensor.RingedSite.canonicalBraidingHom_eq_braidingIso]
      exact Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_braiding
        (etaleRingedToposHom.{u, 0} Λ g) a b) A B

end Braiding

end Stacks.EtaleCohomology

end
