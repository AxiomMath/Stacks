module

public import StacksFrontier.Deformation.ToposThickening.RelativeBaseSquare
public import StacksFrontier.Deformation.ToposThickening.FlatPushforwardEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.Deformation.ToposThickening.FlatLiftBaseRingComparison
public import StacksFrontier.Deformation.ToposThickening.TrivialExtensionClass

/-!
# Flatness over the relative base square

`Deformation.ToposThickening.relBaseRight f'` is the morphism `f̃' = (id, f'^♯)` from
`(Sh(D), O')` to the base `(Sh(D), f'⁻¹O_{ℬ'})` read on the thickened topos. A module flat over
`f̃'` in the sense of Stacks 08M7 is the same as a module flat over `f'⁻¹O_{ℬ'}`; this is how the
flatness hypothesis of the deformation theory of quotients (Stacks 0CZU, 0CZV) on the relative
square is supplied from flatness over the base.

## Main results

* `Deformation.ToposThickening.relBaseRight_fSharpInverseImage`: the structure map of `f̃'`.
* `Deformation.ToposThickening.isFlat_restrictScalars_relBaseRight_iff`: flatness over `f̃'` is
  flatness over `f'⁻¹O_{ℬ'}`.

## References

* [Stacks Project, Tag 0CZV](https://stacks.math.columbia.edu/tag/0CZV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor inverseImageCommRingFunctor
  commRingImageAdjunction)
open Stacks.Sheaves.ToposPullback (pullbackCommRingSheafFunctorId)

universe v u w v' u' vS' uS'

namespace Deformation.ToposThickening

variable {X' : RingedTopos.{v', u', w}} {S' : RingedTopos.{vS', uS', w}}
  [X'.J.HasSheafCompose (forget RingCat.{w})] [S'.J.HasSheafCompose (forget RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (f' : RingedToposHom X' S')

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- For the identity morphism of topoi, the unit `𝒜 ⟶ id_*id⁻¹𝒜` of the adjunction on sheaves of
commutative rings, followed by the two identifications `id_*id⁻¹𝒜 ≅ id⁻¹𝒜 ≅ 𝒜`, is the identity:
the three maps are identities on underlying sheaves of sets. -/
theorem commRingImageAdjunction_id_unit_comp [X'.J.HasSheafCompose (forget CommRingCat.{w})]
    (A : Sheaf X'.J CommRingCat.{w}) :
    (commRingImageAdjunction (MorphismOfTopoi.id X'.Topos)).unit.app A ≫
      (pushforwardCommRingFunctor (MorphismOfTopoi.id X'.Topos)).map
        ((pullbackCommRingSheafFunctorId X'.J).hom.app A) ≫
      (pullbackCommRingSheafFunctorId X'.J).hom.app A = 𝟙 A := by
  apply (sheafCompose X'.J (forget CommRingCat.{w})).map_injective
  have h1 := Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_unit_app
    (MorphismOfTopoi.id X'.Topos) A
  have h2 := Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap X'.J
    (Φ := 𝟭 (Sheaf X'.J (Type w))) ((pullbackCommRingSheafFunctorId X'.J).hom.app A)
  have h3 := Stacks.Sheaves.ToposPullback.forget_map_pullbackCommRingSheafFunctorId_hom_app X'.J A
  refine ((sheafCompose X'.J (forget CommRingCat.{w})).map_comp _ _).trans ?_
  refine (congrArg₂ (· ≫ ·) h1 (((sheafCompose X'.J (forget CommRingCat.{w})).map_comp _ _).trans
    (congrArg₂ (· ≫ ·) h2 h3))).trans ?_
  refine Eq.trans ?_ ((sheafCompose X'.J (forget CommRingCat.{w})).map_id A).symm
  rw [h3]
  rfl

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The structure map of `f̃' = (id, f'^♯)`, in inverse-image form, is that of `f'`**, read
through the identification `id⁻¹f'⁻¹O_{ℬ'} ≅ f'⁻¹O_{ℬ'}`. -/
theorem relBaseRight_fSharpInverseImage [X'.J.HasSheafCompose (forget CommRingCat.{w})] :
    (relBaseRight f').fSharpInverseImage =
      (pullbackCommRingSheafFunctorId X'.J).hom.app _ ≫ f'.fSharpInverseImage := by
  apply ((commRingImageAdjunction (relBaseRight f').toToposHom).homEquiv _ _).injective
  change _ = ((commRingImageAdjunction (relBaseRight f').toToposHom).homEquiv _ _)
    ((pullbackCommRingSheafFunctorId X'.J).hom.app _ ≫ f'.fSharpInverseImage)
  rw [AlgebraicGeometry.RingedToposHom.fSharpInverseImage, Equiv.apply_symm_apply]
  have hu : (commRingImageAdjunction (MorphismOfTopoi.id X'.Topos)).unit.app
        (inverseImageBaseRing f') ≫
      (pushforwardCommRingFunctor (MorphismOfTopoi.id X'.Topos)).map
        ((pullbackCommRingSheafFunctorId X'.J).hom.app (inverseImageBaseRing f')) =
      (pullbackCommRingSheafFunctorId X'.J).inv.app (inverseImageBaseRing f') :=
    (Iso.comp_hom_eq_id ((pullbackCommRingSheafFunctorId X'.J).app _)).1
      ((Category.assoc _ _ _).trans (commRingImageAdjunction_id_unit_comp _))
  refine Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm
  exact ((pullbackCommRingSheafFunctorId X'.J).inv.naturality f'.fSharpInverseImage).trans
    ((congrArg (· ≫ _) hu.symm).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) ((pushforwardCommRingFunctor (MorphismOfTopoi.id X'.Topos)).map_comp
        _ _).symm)))

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **Flatness over `f̃' = (id, f'^♯)` is flatness over `f'⁻¹O_{ℬ'}`.** -/
theorem isFlat_restrictScalars_relBaseRight_iff [X'.J.HasSheafCompose (forget CommRingCat.{w})]
    [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    AlgebraicGeometry.SheafOfModules.IsFlat
        ((SheafOfModules.restrictScalars
          ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            (relBaseRight f').fSharpInverseImage)).obj F') ↔
      AlgebraicGeometry.SheafOfModules.IsFlat
        ((SheafOfModules.restrictScalars
          ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            f'.fSharpInverseImage)).obj F') := by
  rw [relBaseRight_fSharpInverseImage]
  let e := (pullbackCommRingSheafFunctorId X'.J).app (inverseImageBaseRing f')
  let N := (SheafOfModules.restrictScalars ((sheafCompose X'.J
    (forget₂ CommRingCat.{w} RingCat.{w})).map f'.fSharpInverseImage)).obj F'
  change AlgebraicGeometry.SheafOfModules.IsFlat
    ((SheafOfModules.restrictScalars (Stacks.SheafOfModules.FlatSquareZero.ringMap e.hom)).obj N) ↔
      AlgebraicGeometry.SheafOfModules.IsFlat N
  refine ⟨fun h => ?_, fun h => isFlat_restrictScalars_of_iso e N h⟩
  refine AlgebraicGeometry.SheafOfModules.isFlat_of_iso
    (Stacks.SheafOfModules.restrictScalarsSplitIso
      (Stacks.SheafOfModules.FlatSquareZero.ringMap e.inv)
      (Stacks.SheafOfModules.FlatSquareZero.ringMap e.hom) ?_ N)
    (isFlat_restrictScalars_of_iso e.symm _ h)
  exact ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map_comp e.inv e.hom).symm.trans
    ((congrArg (sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map e.inv_hom_id).trans
      ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map_id _))

end Deformation.ToposThickening

end
