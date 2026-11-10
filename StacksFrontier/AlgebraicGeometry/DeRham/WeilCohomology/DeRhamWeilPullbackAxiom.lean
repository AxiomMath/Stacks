module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilData

/-!
# Axiom (A2) for de Rham cohomology

Axiom (A2) of Weil Cohomology Theories, Section 0FID asks that the first Chern class be compatible
with pullbacks. For de Rham cohomology over a field `k` this is the special case of Lemma 0FMD
for squares over `Spec k`, as in Section 0FWC.

## Main results

* `Stacks.DeRhamWeil.firstChernClassPiece_picardClassOf`: on the class of an invertible module,
  `c₁^{dR}` is `AlgebraicGeometry.SheafOfModules.deRhamCohomologyFirstChernClass`.
* `Stacks.DeRhamWeil.pullbackPiece_firstChernClassPiece`: `f^*c₁^{dR}(ℒ) = c₁^{dR}(f^*ℒ)` on
  Picard classes.
* `Stacks.DeRhamWeil.pullbackAxiom`: **axiom (A2)** for the data
  `Stacks.DeRhamWeil.deRhamFirstChernClassData`.

## References

* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.DeRhamBaseChange
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.DeRhamWeil

variable {k : Type u} [Field k]

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

/-- On the class of an invertible module `ℒ`, `c₁^{dR}` is the first Chern class of `ℒ` in de
Rham cohomology. -/
theorem firstChernClassPiece_picardClass (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L : ((toScheme k).obj X).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
      (Stacks.RingedSpace.structureIsSheaf ((toScheme k).obj X).toRingedSpace) L) :
    firstChernClassPiece X (Stacks.SheafOfModules.picardClass ((toScheme k).obj X).presheaf
        (Stacks.RingedSpace.structureIsSheaf ((toScheme k).obj X).toRingedSpace) L hL) =
      AlgebraicGeometry.SheafOfModules.deRhamCohomologyFirstChernClass
        (X := ((toScheme k).obj X).toRingedSpace) (algebras X) (differential X) L hL := by
  change (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (algebras X) (differential X) 2).hom.hom
    (AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian (algebras X) (differential X)
      (Stacks.GluePicard.picardModelAddEquiv _ _)) = _
  erw [Stacks.GluePicard.picardModelAddEquiv_classOf]
  rfl

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory}

/-- **`f^*c₁^{dR}(ℒ) = c₁^{dR}(f^*ℒ)`** on Picard classes, in `H^2_{dR}(X/k)` (Lemma 0FMD). -/
theorem pullbackPiece_firstChernClassPiece (f : X ⟶ Y)
    (c : ((toScheme k).obj Y).picardGroup) :
    pullbackPiece f 2 (firstChernClassPiece Y c) =
      firstChernClassPiece X (Stacks.Picard.schemePullbackClassHom ((toScheme k).map f) c) := by
  have h := Scheme.Hom.deRhamFirstChernClassAbelian_schemePullbackClassHom ((toScheme k).map f)
    Y.obj.hom X.obj.hom (𝟙 _) (square_w f) c
  let eY := AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
    (algebras Y) (differential Y) 2
  let eX := AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
    (algebras X) (differential X) 2
  let P := Scheme.Hom.deRhamCohomologyPullback ((toScheme k).map f) Y.obj.hom X.obj.hom (𝟙 _)
    (square_w f) 2
  let z := AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian (algebras Y)
    (differential Y) (Stacks.GluePicard.picardModelAddEquiv _ c)
  change eX.hom.hom (P.hom (eY.inv.hom (eY.hom.hom z))) = eX.hom.hom _
  rw [Iso.hom_inv_id_apply]
  exact congrArg eX.hom.hom h.symm

/-- Pullback of Picard classes is pullback of invertible modules. -/
theorem schemePullbackClassHom_picardClassOf (f : X ⟶ Y) (L : ((toScheme k).obj Y).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj Y).presheaf
      ((toScheme k).obj Y).ringCatSheaf.2 L) :
    Stacks.Picard.schemePullbackClassHom ((toScheme k).map f) (picardClassOf _ L hL) =
      picardClassOf _ ((Scheme.Modules.pullback ((toScheme k).map f)).obj L)
        (isInvertible_pullback_obj _ L hL) :=
  Stacks.Picard.pullbackClass_classOf _ L _

/-- **Axiom (A2) for de Rham cohomology**: the de Rham first Chern class is compatible with
pullbacks, `f^*c₁^{dR}(ℒ) = c₁^{dR}(f^*ℒ)` (Lemma 0FMD, as in Section 0FWC). -/
theorem pullbackAxiom : (deRhamFirstChernClassData k).PullbackAxiom := by
  intro X Y f L hL
  change tateTwistMap (pullback f).toLinearMap 1 (firstChernClass Y _) = firstChernClass X _
  apply (untwist (cohomology X) 1).injective
  have e1 : ∀ x, untwist (cohomology X) 1 (tateTwistMap (pullback f).toLinearMap 1 x) =
      pullback f (untwist (cohomology Y) 1 x) := fun x =>
    tateTwistCoordinates_map _ _ _ _
  rw [e1]
  change pullback f (untwist _ 1 ((untwist _ 1).symm (DirectSum.of (piece Y) 2 _))) =
    untwist _ 1 ((untwist _ 1).symm (DirectSum.of (piece X) 2 _))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, pullback_of,
    pullbackPiece_firstChernClassPiece, schemePullbackClassHom_picardClassOf]

end Stacks.DeRhamWeil

end
