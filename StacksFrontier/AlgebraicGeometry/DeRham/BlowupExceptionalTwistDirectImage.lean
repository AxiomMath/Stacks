module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaUnit
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.FiniteLocallyFree

/-!
# Direct images of exceptional-divisor twists on a blowup

Let `b : L ⟶ X` be the blowing up of a scheme `X` in a quasi-coherent sheaf of ideals, let
`E ⊆ L` be its exceptional divisor and let `i ≥ 0`. Multiplication by the canonical section of
`𝒪_L(iE)` turns the adjunction unit into a canonical map

`ℰ ⟶ b_*(𝒪_L(iE) ⊗_{𝒪_L} b^*ℰ)`

for every `𝒪_X`-module `ℰ`. This file proves that the map for a finite locally free `ℰ` is an
isomorphism as soon as the map for `ℰ = 𝒪_X` is: the comparison factors through the
projection-formula map `b_*𝒪_L(iE) ⊗_{𝒪_X} ℰ ⟶ b_*(𝒪_L(iE) ⊗_{𝒪_L} b^*ℰ)`, which is invertible
at a finite locally free module with no further hypothesis.

## Main definitions

* `Stacks.DeRham.BlowupTwist.twistUnitComparison`: the map `𝒪_X ⟶ b_*T` attached to a global
  section `𝒪_L ⟶ T` of an `𝒪_L`-module `T`, by adjunction.
* `Stacks.DeRham.BlowupTwist.twistComparison`: the map `ℰ ⟶ b_*(T ⊗_{𝒪_L} b^*ℰ)` attached to
  the same section.
* `Stacks.DeRham.BlowupTwist.exceptionalTwistComparison`: the comparison map at
  `T = 𝒪_L(iE)` and the canonical section of that twist.

## Main results

* `Stacks.DeRham.BlowupTwist.twistComparison_eq`: the comparison map at `ℰ` is the left unitor,
  followed by the comparison map at `𝒪_X` tensored with `ℰ`, followed by the
  projection-formula map.
* `Stacks.DeRham.BlowupTwist.isIso_twistComparison`: the comparison map at a finite
  locally free `ℰ` is an isomorphism as soon as the one at `𝒪_X` is.

## Implementation notes

The two tensor factors are written in the order in which the projection-formula map
`Stacks.AffineProjectionFormula.projectionFormulaMap` produces them, `𝒪_L(iE) ⊗_{𝒪_L} b^*ℰ`,
rather than the source's `b^*ℰ ⊗_{𝒪_L} 𝒪_L(iE)`; the two targets differ by the symmetry
isomorphism of the tensor product.

Only the direct image `b_*` appears, not the derived direct image: the projection formula
available here is the `q = 0` clause of [Stacks, Tag 01E8],
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_isFiniteLocallyFree`, and the
higher direct images `R^q b_*` are not treated, so the dévissage carried out here is the one in
`ℰ` and not the passage to `D(𝒪_X)`.

The only hypothesis is the case `ℰ = 𝒪_X`.  The factorization needs the left-unitor coherence
of [Stacks, Tag 01CD] — the structure sheaf sits in the *first* tensor factor of
`b_*𝒪_L(iE) ⊗_{𝒪_X} ℰ` once the first factor is replaced — and that is
`Stacks.RingedSpace.comparison_leftUnitor`.

The hypothesis of finite local freeness on `ℰ` is
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree` written out, in the form taken by
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_isFiniteLocallyFree`.

## References

* [Stacks Project, Tag 0G5H](https://stacks.math.columbia.edu/tag/0G5H)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

open scoped CategoryTheory.Prod TensorProduct

universe u

namespace Stacks.DeRham.BlowupTwist

open _root_.RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.AffineProjectionFormula

variable {L X : Scheme.{u}} (b : L ⟶ X)
  (T : SheafOfModules.{u} (structureRingSheaf L.toRingedSpace))
  (s : SheafOfModules.unit (structureRingSheaf L.toRingedSpace) ⟶ T)

/-- **The comparison map at the structure sheaf**, `𝒪_X ⟶ b_*T`: the adjoint transpose of the
global section `s` of `T`, read through `b^*𝒪_X ≅ 𝒪_L`. -/
def twistUnitComparison :
    SheafOfModules.unit (structureRingSheaf X.toRingedSpace) ⟶
      (pushforwardFunctor b.toLRSHom.toShHom).obj T :=
  (pullbackAdjunction b.toLRSHom.toShHom).homEquiv _ _
    ((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s)

/-- **The comparison map at an `𝒪_X`-module `ℰ`**, `ℰ ⟶ b_*(T ⊗_{𝒪_L} b^*ℰ)`: the adjoint
transpose of multiplication by the global section `s` of `T` on `b^*ℰ`. -/
def twistComparison (E : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :
    E ⟶ (pushforwardFunctor b.toLRSHom.toShHom).obj
      (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf))).obj
        (T, (pullbackFunctor b.toLRSHom.toShHom).obj E)) :=
  (pullbackAdjunction b.toLRSHom.toShHom).homEquiv _ _
    ((tensorSheafUnitLeftIso L.toRingedSpace
        ((pullbackFunctor b.toLRSHom.toShHom).obj E)).inv ≫
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf))).map
        ((s ×ₘ 𝟙 ((pullbackFunctor b.toLRSHom.toShHom).obj E)) :
          ((SheafOfModules.unit (structureRingSheaf L.toRingedSpace),
              (pullbackFunctor b.toLRSHom.toShHom).obj E) : _ × _) ⟶
            (T, (pullbackFunctor b.toLRSHom.toShHom).obj E)))

/-- **The comparison map at `ℰ` factors through the projection-formula map.** It is the inverse
left unitor of `ℰ`, followed by the comparison map at the structure sheaf tensored with `ℰ`,
followed by the projection-formula map `b_*T ⊗_{𝒪_X} ℰ ⟶ b_*(T ⊗_{𝒪_L} b^*ℰ)`. This is the
reduction to `ℰ = 𝒪_X` that the proof of [Stacks, Tag 0G5H] opens with. -/
theorem twistComparison_eq (E : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :
    twistComparison b T s E =
      (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf))).map
            ((twistUnitComparison b T s ×ₘ 𝟙 E) :
              ((SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E) : _ × _) ⟶
                ((pushforwardFunctor b.toLRSHom.toShHom).obj T, E)) ≫
          projectionFormulaMap b.toLRSHom.toShHom T E := by
  have hunitSplit :
      twistUnitComparison b T s =
        (pullbackAdjunction b.toLRSHom.toShHom).unit.app
            (SheafOfModules.unit (structureRingSheaf X.toRingedSpace)) ≫
          (pushforwardFunctor b.toLRSHom.toShHom).map
            ((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s) := by
    simp [twistUnitComparison, Adjunction.homEquiv_unit]
  have key : (pullbackFunctor b.toLRSHom.toShHom).map
        (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
      (comparisonNatTrans b.toLRSHom.toShHom).app
          (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E) ≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf))).map
          ((pullbackObjUnitIso b.toLRSHom.toShHom).hom ×ₘ
            𝟙 ((pullbackFunctor b.toLRSHom.toShHom).obj E)) =
      (tensorSheafUnitLeftIso L.toRingedSpace
        ((pullbackFunctor b.toLRSHom.toShHom).obj E)).inv := by
    have hcomp :
        (comparisonNatTrans b.toLRSHom.toShHom).app
              (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E) ≫
            ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf))).map
              ((pullbackObjUnitIso b.toLRSHom.toShHom).hom ×ₘ
                𝟙 ((pullbackFunctor b.toLRSHom.toShHom).obj E)) =
          (pullbackFunctor b.toLRSHom.toShHom).map
              (tensorSheafUnitLeftIso X.toRingedSpace E).hom ≫
            (tensorSheafUnitLeftIso L.toRingedSpace
              ((pullbackFunctor b.toLRSHom.toShHom).obj E)).inv :=
      (Iso.eq_comp_inv _).mpr
        ((Category.assoc _ _ _).trans (comparison_leftUnitor b.toLRSHom.toShHom E))
    exact (congrArg (fun arrow => (pullbackFunctor b.toLRSHom.toShHom).map
        (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫ arrow) hcomp).trans
      (((pullbackFunctor b.toLRSHom.toShHom).mapIso
        (tensorSheafUnitLeftIso X.toRingedSpace E)).inv_hom_id_assoc _)
  symm
  refine Eq.trans (b := (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
      (pullbackAdjunction b.toLRSHom.toShHom).homEquiv
          ((((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf)))).obj
            (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E))
          ((((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf)))).obj
            (T, (pullbackFunctor b.toLRSHom.toShHom).obj E))
        ((comparisonNatTrans b.toLRSHom.toShHom).app
              (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E) ≫
            (((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                L.toRingedSpace.sheaf)))).map
              (((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s) ×ₘ
                (pullbackFunctor b.toLRSHom.toShHom).map (𝟙 E)))) ?_ ?_
  · calc (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
          ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf))).map
              (twistUnitComparison b T s ×ₘ 𝟙 E) ≫
            projectionFormulaMap b.toLRSHom.toShHom T E
        = (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
            ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf))).map
                (((pullbackAdjunction b.toLRSHom.toShHom).unit.app
                      (SheafOfModules.unit (structureRingSheaf X.toRingedSpace)) ≫
                    (pushforwardFunctor b.toLRSHom.toShHom).map
                      ((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s)) ×ₘ 𝟙 E) ≫
              projectionFormulaMap b.toLRSHom.toShHom T E :=
          congrArg (fun arrow => (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
            ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf))).map
              (arrow ×ₘ 𝟙 E) ≫ projectionFormulaMap b.toLRSHom.toShHom T E) hunitSplit
      _ = (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
            (((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf))).map
                  ((pullbackAdjunction b.toLRSHom.toShHom).unit.app
                    (SheafOfModules.unit (structureRingSheaf X.toRingedSpace)) ×ₘ 𝟙 E) ≫
                ((Functor.uncurry.obj
                  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    X.toRingedSpace.sheaf))).map
                  ((pushforwardFunctor b.toLRSHom.toShHom).map
                    ((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s) ×ₘ 𝟙 E)) ≫
              projectionFormulaMap b.toLRSHom.toShHom T E :=
          congrArg (fun arrow => (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫ arrow ≫
              projectionFormulaMap b.toLRSHom.toShHom T E)
            (bifunctor_map_comp_left
              ((Functor.uncurry.obj
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf)))
              ((pullbackAdjunction b.toLRSHom.toShHom).unit.app
                (SheafOfModules.unit (structureRingSheaf X.toRingedSpace)))
              ((pushforwardFunctor b.toLRSHom.toShHom).map
                ((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s)) (𝟙 E))
      _ = (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
            ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf))).map
                ((pullbackAdjunction b.toLRSHom.toShHom).unit.app
                  (SheafOfModules.unit (structureRingSheaf X.toRingedSpace)) ×ₘ 𝟙 E) ≫
              ((Functor.uncurry.obj
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  X.toRingedSpace.sheaf))).map
                  ((pushforwardFunctor b.toLRSHom.toShHom).map
                    ((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s) ×ₘ 𝟙 E) ≫
                projectionFormulaMap b.toLRSHom.toShHom T E :=
          congrArg (fun arrow => (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫ arrow)
            (Category.assoc _ _ _)
      _ = (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
            ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf))).map
                ((pullbackAdjunction b.toLRSHom.toShHom).unit.app
                  (SheafOfModules.unit (structureRingSheaf X.toRingedSpace)) ×ₘ 𝟙 E) ≫
              projectionFormulaMap b.toLRSHom.toShHom
                  ((pullbackFunctor b.toLRSHom.toShHom).obj
                    (SheafOfModules.unit (structureRingSheaf X.toRingedSpace))) E ≫
                (pushforwardFunctor b.toLRSHom.toShHom).map
                  (((Functor.uncurry.obj
                    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                      L.toRingedSpace.sheaf))).map
                    (((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s) ×ₘ
                      (pullbackFunctor b.toLRSHom.toShHom).map (𝟙 E))) :=
          congrArg (fun arrow => (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
              ((Functor.uncurry.obj
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  X.toRingedSpace.sheaf))).map
                ((pullbackAdjunction b.toLRSHom.toShHom).unit.app
                  (SheafOfModules.unit (structureRingSheaf X.toRingedSpace)) ×ₘ 𝟙 E) ≫ arrow)
            (projectionFormulaMap_natural b.toLRSHom.toShHom
              ((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s) (𝟙 E))
      _ = (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
            (((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf))).map
                  ((pullbackAdjunction b.toLRSHom.toShHom).unit.app
                    (SheafOfModules.unit (structureRingSheaf X.toRingedSpace)) ×ₘ 𝟙 E) ≫
                projectionFormulaMap b.toLRSHom.toShHom
                  ((pullbackFunctor b.toLRSHom.toShHom).obj
                    (SheafOfModules.unit (structureRingSheaf X.toRingedSpace))) E) ≫
              (pushforwardFunctor b.toLRSHom.toShHom).map
                (((Functor.uncurry.obj
                  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    L.toRingedSpace.sheaf))).map
                  (((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s) ×ₘ
                    (pullbackFunctor b.toLRSHom.toShHom).map (𝟙 E))) :=
          congrArg (fun arrow => (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫ arrow)
            (Category.assoc _ _ _).symm
      _ = (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
            (pullbackAdjunction b.toLRSHom.toShHom).homEquiv _ _
                ((comparisonNatTrans b.toLRSHom.toShHom).app
                  (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E)) ≫
              (pushforwardFunctor b.toLRSHom.toShHom).map
                (((Functor.uncurry.obj
                  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    L.toRingedSpace.sheaf))).map
                  (((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s) ×ₘ
                    (pullbackFunctor b.toLRSHom.toShHom).map (𝟙 E))) :=
          congrArg (fun arrow => (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫ arrow ≫
              (pushforwardFunctor b.toLRSHom.toShHom).map
                (((Functor.uncurry.obj
                  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    L.toRingedSpace.sheaf))).map
                  (((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s) ×ₘ
                    (pullbackFunctor b.toLRSHom.toShHom).map (𝟙 E))))
            (projectionFormulaMap_natural_unit b.toLRSHom.toShHom
              (SheafOfModules.unit (structureRingSheaf X.toRingedSpace)) E)
      _ = (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
            (pullbackAdjunction b.toLRSHom.toShHom).homEquiv
              ((((Functor.uncurry.obj
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  X.toRingedSpace.sheaf))).obj
                (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E)))
              ((((Functor.uncurry.obj
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  L.toRingedSpace.sheaf))).obj
                (T, (pullbackFunctor b.toLRSHom.toShHom).obj E)))
              ((comparisonNatTrans b.toLRSHom.toShHom).app
                  (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E) ≫
                ((Functor.uncurry.obj
                  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    L.toRingedSpace.sheaf))).map
                  (((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s) ×ₘ
                    (pullbackFunctor b.toLRSHom.toShHom).map (𝟙 E))) :=
          congrArg (fun arrow => (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫ arrow)
            ((pullbackAdjunction b.toLRSHom.toShHom).homEquiv_naturality_right _ _).symm
  · refine Eq.trans ((pullbackAdjunction b.toLRSHom.toShHom).homEquiv_naturality_left
      _ _).symm ?_
    calc (pullbackAdjunction b.toLRSHom.toShHom).homEquiv E
            ((((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf))).obj
              (T, (pullbackFunctor b.toLRSHom.toShHom).obj E)))
            ((pullbackFunctor b.toLRSHom.toShHom).map
                (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
              (comparisonNatTrans b.toLRSHom.toShHom).app
                  (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E) ≫
                ((Functor.uncurry.obj
                  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    L.toRingedSpace.sheaf))).map
                  (((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s) ×ₘ
                    (pullbackFunctor b.toLRSHom.toShHom).map (𝟙 E)))
      _ = (pullbackAdjunction b.toLRSHom.toShHom).homEquiv E
            ((((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf))).obj
              (T, (pullbackFunctor b.toLRSHom.toShHom).obj E)))
            ((pullbackFunctor b.toLRSHom.toShHom).map
                (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
              (comparisonNatTrans b.toLRSHom.toShHom).app
                  (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E) ≫
                ((Functor.uncurry.obj
                  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    L.toRingedSpace.sheaf))).map
                  (((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s) ×ₘ
                    𝟙 ((pullbackFunctor b.toLRSHom.toShHom).obj E))) :=
          congrArg (fun arrow => (pullbackAdjunction b.toLRSHom.toShHom).homEquiv E
            ((((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf))).obj
              (T, (pullbackFunctor b.toLRSHom.toShHom).obj E)))
              ((pullbackFunctor b.toLRSHom.toShHom).map
                  (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
                (comparisonNatTrans b.toLRSHom.toShHom).app
                    (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E) ≫
                  ((Functor.uncurry.obj
                    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                      L.toRingedSpace.sheaf))).map
                    (((pullbackObjUnitIso b.toLRSHom.toShHom).hom ≫ s) ×ₘ arrow)))
            ((pullbackFunctor b.toLRSHom.toShHom).map_id E)
      _ = (pullbackAdjunction b.toLRSHom.toShHom).homEquiv E
            ((((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf))).obj
              (T, (pullbackFunctor b.toLRSHom.toShHom).obj E)))
            ((pullbackFunctor b.toLRSHom.toShHom).map
                (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
              (comparisonNatTrans b.toLRSHom.toShHom).app
                  (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E) ≫
                (((Functor.uncurry.obj
                  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    L.toRingedSpace.sheaf))).map
                    ((pullbackObjUnitIso b.toLRSHom.toShHom).hom ×ₘ
                      𝟙 ((pullbackFunctor b.toLRSHom.toShHom).obj E)) ≫
                  ((Functor.uncurry.obj
                    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                      L.toRingedSpace.sheaf))).map
                    (s ×ₘ 𝟙 ((pullbackFunctor b.toLRSHom.toShHom).obj E)))) :=
          congrArg (fun arrow => (pullbackAdjunction b.toLRSHom.toShHom).homEquiv E
            ((((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf))).obj
              (T, (pullbackFunctor b.toLRSHom.toShHom).obj E)))
              ((pullbackFunctor b.toLRSHom.toShHom).map
                  (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
                (comparisonNatTrans b.toLRSHom.toShHom).app
                    (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E) ≫ arrow))
            (bifunctor_map_comp_left
              ((Functor.uncurry.obj
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf)))
              (pullbackObjUnitIso b.toLRSHom.toShHom).hom s
              (𝟙 ((pullbackFunctor b.toLRSHom.toShHom).obj E)))
      _ = (pullbackAdjunction b.toLRSHom.toShHom).homEquiv E
            ((((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf))).obj
              (T, (pullbackFunctor b.toLRSHom.toShHom).obj E)))
            (((pullbackFunctor b.toLRSHom.toShHom).map
                    (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫
                  (comparisonNatTrans b.toLRSHom.toShHom).app
                      (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), E) ≫
                    ((Functor.uncurry.obj
                      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                        L.toRingedSpace.sheaf))).map
                      ((pullbackObjUnitIso b.toLRSHom.toShHom).hom ×ₘ
                        𝟙 ((pullbackFunctor b.toLRSHom.toShHom).obj E))) ≫
              ((Functor.uncurry.obj
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  L.toRingedSpace.sheaf))).map
                (s ×ₘ 𝟙 ((pullbackFunctor b.toLRSHom.toShHom).obj E))) :=
          congrArg ((pullbackAdjunction b.toLRSHom.toShHom).homEquiv E
            ((((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf))).obj
              (T, (pullbackFunctor b.toLRSHom.toShHom).obj E))))
            ((congrArg (fun arrow => (pullbackFunctor b.toLRSHom.toShHom).map
                  (tensorSheafUnitLeftIso X.toRingedSpace E).inv ≫ arrow)
                (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)
      _ = (pullbackAdjunction b.toLRSHom.toShHom).homEquiv E
            ((((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf))).obj
              (T, (pullbackFunctor b.toLRSHom.toShHom).obj E)))
            ((tensorSheafUnitLeftIso L.toRingedSpace
                  ((pullbackFunctor b.toLRSHom.toShHom).obj E)).inv ≫
              ((Functor.uncurry.obj
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  L.toRingedSpace.sheaf))).map
                (s ×ₘ 𝟙 ((pullbackFunctor b.toLRSHom.toShHom).obj E))) :=
          congrArg (fun arrow => (pullbackAdjunction b.toLRSHom.toShHom).homEquiv E
            ((((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} L.toRingedSpace.sheaf))).obj
              (T, (pullbackFunctor b.toLRSHom.toShHom).obj E)))
              (arrow ≫
                ((Functor.uncurry.obj
                  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    L.toRingedSpace.sheaf))).map
                  (s ×ₘ 𝟙 ((pullbackFunctor b.toLRSHom.toShHom).obj E)))) key
      _ = twistComparison b T s E := rfl

/-- **The comparison map at a finite locally free `ℰ` is an isomorphism as soon as the one at the
structure sheaf is.** The comparison map factors as the inverse left unitor, the comparison map
at `𝒪_X` tensored with `ℰ`, and the projection-formula map; the first is an isomorphism, the
second is one by `hunit`, and the third is one by the `q = 0` projection formula of
[Stacks, Tag 01E8] at a finite locally free module. -/
theorem isIso_twistComparison (E : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    (hE : ∀ x : X.carrier, ∃ (V : X.Opens) (_ : x ∈ V) (I : Type u) (_ : Finite I),
      Nonempty (openRestrictModule V E ≅ SheafOfModules.free.{u} I))
    (hunit : IsIso (twistUnitComparison b T s)) :
    IsIso (twistComparison b T s E) := by
  rw [twistComparison_eq]
  refine IsIso.comp_isIso' (tensorSheafUnitLeftIso X.toRingedSpace E).isIso_inv
    (IsIso.comp_isIso' ?_ ?_)
  · exact (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf))).mapIso
      (Iso.prod (@asIso _ _ _ _ (twistUnitComparison b T s) hunit) (Iso.refl E))).isIso_hom
  · exact isIso_projectionFormulaMap_of_isFiniteLocallyFree b T E hE

/-! ### The exceptional-divisor twists of a blowup -/

variable {W : Scheme.{u}} (I : W.IdealSheafData) (i : ℕ)

/-- **The comparison map `ℰ ⟶ b_*(𝒪_L(iE) ⊗_{𝒪_L} b^*ℰ)`** for the blowing up `b : L ⟶ X` of a
scheme in a quasi-coherent sheaf of ideals, `E` its exceptional divisor and `i ≥ 0`: the
adjunction unit followed by multiplication by the canonical section of `𝒪_L(iE)`. -/
def exceptionalTwistComparison
    (E : SheafOfModules.{u} (structureRingSheaf W.toRingedSpace)) :
    E ⟶ (pushforwardFunctor (blowUpToBase I).toLRSHom.toShHom).obj
      (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (blowUp I).toRingedSpace.sheaf))).obj
        (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal I ^ i),
          (pullbackFunctor (blowUpToBase I).toLRSHom.toShHom).obj E)) :=
  twistComparison (blowUpToBase I) (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal I ^ i))
    (Stacks.Divisors.canonicalSectionHom (exceptionalIdeal I ^ i)) E

end Stacks.DeRham.BlowupTwist

end
