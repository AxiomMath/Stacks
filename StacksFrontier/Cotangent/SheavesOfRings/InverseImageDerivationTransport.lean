module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageDerivations
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageStandardResolutionComparison

/-!
# Transport of derivations along an isomorphism of the acting sheaf of rings

Let `C` be a site and `A' ⟶ P ⟶ B'` sheaves of commutative rings on it. An `A'`-derivation of
`P` with values in a sheaf of `B'`-modules is a pointwise datum, so a morphism `ρ : P ⟶ P'` of
sheaves of commutative rings compatible with the maps from `A'` and to `B'` carries an
`A'`-derivation of `P'` to one of `P` by composing with the sections of `ρ`, and an isomorphism
carries the two types of derivations onto each other.

For a morphism of topoi `f` and a homomorphism `a : A ⟶ B` of sheaves of commutative rings on
its target, the comparison of the standard resolution of `a` with that of `f⁻¹a` is such an
isomorphism in every simplicial degree, compatible with the structure map from `f⁻¹A` and with
the augmentation to `f⁻¹B`.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.derivationPrecompRing` is the precomposition of a
  derivation by a morphism of the acting sheaf of commutative rings.
* `Stacks.Sheaves.RingedToposModules.derivationRingEquiv` is the induced bijection of
  derivations for an isomorphism of the acting sheaf of commutative rings.
* `CategoryTheory.Sheaf.inverseImageTargetModules` is the inverse image of sheaves of
  `B`-modules, read as sheaves of `f⁻¹B`-modules.
* `CategoryTheory.Sheaf.resolutionInverseImageIso` is the degreewise comparison of the standard
  resolution of `a` with that of `f⁻¹a`, as an isomorphism of sheaves of commutative rings.

## Main results

* `Stacks.Sheaves.RingedToposModules.derivationSheafHom_derivationPrecompRing` and
  `Stacks.Sheaves.RingedToposModules.derivationSheafHom_derivationRingEquiv`: the morphism of
  underlying sheaves of sets of a transported derivation is that of the derivation preceded by
  the morphism of sheaves of sets of `ρ`.
* `CategoryTheory.Sheaf.resolutionInverseImageIso_base` and
  `CategoryTheory.Sheaf.resolutionInverseImageIso_augmentation`: the degreewise comparison is a
  map of `f⁻¹A`-algebras and is compatible with the two augmentations.

## Implementation notes

`derivationPrecompRing` keeps the two maps `augP : P ⟶ B'` and `augP' : P' ⟶ B'` as independent
data rather than composing one out of the other, so that the two sheaves of modules obtained by
restriction of scalars are the ones the statement names and no transport along an equality of
restriction functors is needed; the morphism of underlying sheaves of sets of the result is then
a composition on sections.

The degreewise comparison is read off the simplicial comparison
`CategoryTheory.Sheaf.standardResolutionInverseImageIso` rather than from
`CategoryTheory.Sheaf.standardResolutionInverseImageTermIso`, so that it is available in every
simplicial degree and not only in the degrees `⦋n⦌`.

The two sites, their morphism universes and the two universes of sections all vary
independently, as in `CategoryTheory.Sheaf.cotangentComplex`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.RingedToposModules

section RingTransport

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {A' P P' B' : Sheaf J CommRingCat.{w}}
  (M : SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf.{u, v, w} B'))

/-- Precomposition of a derivation by a morphism `ρ : P ⟶ P'` of sheaves of commutative rings
which is compatible with given maps from `A'` and to `B'`: an `A'`-derivation of `P'` with
values in `M`, read as a sheaf of `P'`-modules along `augP'`, is an `A'`-derivation of `P` with
values in `M` read along `augP`. -/
noncomputable def derivationPrecompRing (rho : P ⟶ P')
    {baseP : A' ⟶ P} {baseP' : A' ⟶ P'} {augP : P ⟶ B'} {augP' : P' ⟶ B'}
    (hbase : baseP ≫ rho = baseP') (haug : rho ≫ augP' = augP)
    (DD : ((SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v, u, w} J).map augP')).obj M).val.Derivation'
          baseP'.hom) :
    ((SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v, u, w} J).map augP)).obj M).val.Derivation'
          baseP.hom where
  d {U} := (DD.d (X := U)).comp (rho.hom.app U).hom.toAddMonoidHom
  d_mul {U} x y := by
    have h : ∀ z : P.obj.obj U, augP'.hom.app U (rho.hom.app U z) = augP.hom.app U z :=
      fun z ↦ congrArg (fun k : P ⟶ B' ↦ k.hom.app U z) haug
    change DD.d (rho.hom.app U (x * y)) =
      (show (SheafOfModules.Tensor.ringSheaf.{u, v, w} B').obj.obj U from augP.hom.app U x) •
          (show M.val.obj U from DD.d (rho.hom.app U y)) +
        (show (SheafOfModules.Tensor.ringSheaf.{u, v, w} B').obj.obj U from augP.hom.app U y) •
          (show M.val.obj U from DD.d (rho.hom.app U x))
    rw [map_mul (rho.hom.app U).hom, DD.d_mul]
    change (show (SheafOfModules.Tensor.ringSheaf.{u, v, w} B').obj.obj U from
            augP'.hom.app U (rho.hom.app U x)) •
          (show M.val.obj U from DD.d (rho.hom.app U y)) +
        (show (SheafOfModules.Tensor.ringSheaf.{u, v, w} B').obj.obj U from
            augP'.hom.app U (rho.hom.app U y)) •
          (show M.val.obj U from DD.d (rho.hom.app U x)) =
      (show (SheafOfModules.Tensor.ringSheaf.{u, v, w} B').obj.obj U from augP.hom.app U x) •
          (show M.val.obj U from DD.d (rho.hom.app U y)) +
        (show (SheafOfModules.Tensor.ringSheaf.{u, v, w} B').obj.obj U from augP.hom.app U y) •
          (show M.val.obj U from DD.d (rho.hom.app U x))
    rw [h, h]
  d_map {U V} g x := by
    have h := congrArg (fun k ↦ k x) (rho.hom.naturality g)
    dsimp at h
    change DD.d (rho.hom.app V (P.obj.map g x)) = M.val.map g (DD.d (rho.hom.app U x))
    rw [h]
    exact DD.d_map g _
  d_app {U} x := by
    have h : rho.hom.app U (baseP.hom.app U x) = baseP'.hom.app U x :=
      congrArg (fun k : A' ⟶ P' ↦ k.hom.app U x) hbase
    change DD.d (rho.hom.app U (baseP.hom.app U x)) = 0
    rw [h]
    exact DD.d_app x

/-- The morphism of underlying sheaves of sets of a precomposed derivation is that of the
derivation, preceded by the morphism of sheaves of sets of `ρ`. -/
lemma derivationSheafHom_derivationPrecompRing (rho : P ⟶ P')
    {baseP : A' ⟶ P} {baseP' : A' ⟶ P'} {augP : P ⟶ B'} {augP' : P' ⟶ B'}
    (hbase : baseP ≫ rho = baseP') (haug : rho ≫ augP' = augP)
    (DD : ((SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v, u, w} J).map augP')).obj M).val.Derivation'
          baseP'.hom) :
    derivationSheafHom baseP ((SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, w} J).map augP)).obj M)
        (derivationPrecompRing M rho hbase haug DD) =
      commRingSetHom rho ≫ derivationSheafHom baseP' ((SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v, u, w} J).map augP')).obj M) DD :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- An isomorphism `ρ : P ≅ P'` of sheaves of commutative rings compatible with given maps from
`A'` and to `B'` identifies the two types of `A'`-derivations with values in `M`. -/
noncomputable def derivationRingEquiv (rho : P ≅ P')
    {baseP : A' ⟶ P} {baseP' : A' ⟶ P'} {augP : P ⟶ B'} {augP' : P' ⟶ B'}
    (hbase : baseP ≫ rho.hom = baseP') (haug : rho.hom ≫ augP' = augP) :
    ((SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v, u, w} J).map augP)).obj M).val.Derivation'
          baseP.hom ≃
      ((SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v, u, w} J).map augP')).obj M).val.Derivation'
          baseP'.hom where
  toFun := derivationPrecompRing M rho.inv
    (by rw [← hbase, Category.assoc, rho.hom_inv_id, Category.comp_id])
    (by rw [← haug, ← Category.assoc, rho.inv_hom_id, Category.id_comp])
  invFun := derivationPrecompRing M rho.hom hbase haug
  left_inv DD := by
    ext U x
    have h : rho.inv.hom.app U (rho.hom.hom.app U x) = x :=
      congrArg (fun k : P ⟶ P ↦ k.hom.app U x) rho.hom_inv_id
    change DD.d (rho.inv.hom.app U (rho.hom.hom.app U x)) = DD.d x
    rw [h]
  right_inv DD := by
    ext U x
    have h : rho.hom.hom.app U (rho.inv.hom.app U x) = x :=
      congrArg (fun k : P' ⟶ P' ↦ k.hom.app U x) rho.inv_hom_id
    change DD.d (rho.hom.hom.app U (rho.inv.hom.app U x)) = DD.d x
    rw [h]

/-- Transporting a derivation along an isomorphism of the acting sheaf of commutative rings
composes its morphism of underlying sheaves of sets with the inverse isomorphism. -/
lemma derivationSheafHom_derivationRingEquiv (rho : P ≅ P')
    {baseP : A' ⟶ P} {baseP' : A' ⟶ P'} {augP : P ⟶ B'} {augP' : P' ⟶ B'}
    (hbase : baseP ≫ rho.hom = baseP') (haug : rho.hom ≫ augP' = augP)
    (DD : ((SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v, u, w} J).map augP)).obj M).val.Derivation'
          baseP.hom) :
    derivationSheafHom baseP' ((SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, w} J).map augP')).obj M)
        (derivationRingEquiv M rho hbase haug DD) =
      commRingSetHom rho.inv ≫ derivationSheafHom baseP ((SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v, u, w} J).map augP)).obj M) DD :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

end RingTransport



end Stacks.Sheaves.RingedToposModules

namespace CategoryTheory.Sheaf

universe u v w u' v' w'

open Stacks.Sheaves.RingedToposModules

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {A B : Sheaf K CommRingCat.{max u' v' w'}} (a : A ⟶ B)

/-- The inverse image of sheaves of modules along `f`, as a functor from sheaves of
`B`-modules to sheaves of `f⁻¹B`-modules. -/
noncomputable abbrev inverseImageTargetModules :
    targetModules.{u', v', w'} K B ⥤ targetModules.{u, v, w} J (f.inverseImageRing.obj B) :=
  inverseImageModules f ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)

/-- The inverse image of sheaves of modules along `f`, read as a functor from sheaves of
`B`-modules to sheaves of `f⁻¹B`-modules, is additive. -/
instance inverseImageTargetModules_additive :
    (inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).Additive :=
  letI := f.preservesFiniteLimits
  inferInstanceAs (Stacks.Sheaves.ToposPullback.pullbackModuleFunctor J f.inverseImage
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).Additive

/-- The comparison of the standard resolutions of `a` and of `f⁻¹a` in a simplicial degree. -/
noncomputable def resolutionInverseImageIso (n : SimplexCategoryᵒᵖ) :
    f.inverseImageRing.obj (resolutionTerm.{u', v', w'} K a n) ≅
      resolutionTerm.{u, v, w} J (f.inverseImageRing.map a) n :=
  (Under.forget (f.inverseImageRing.obj A)).mapIso
    ((standardResolutionInverseImageIso.{u, v, w, u', v', w'} J K f a).app n)

/-- The degreewise comparison of the standard resolutions is a map of `f⁻¹A`-algebras. -/
lemma resolutionInverseImageIso_base (n : SimplexCategoryᵒᵖ) :
    f.inverseImageRing.map (resolutionBase.{u', v', w'} K a n) ≫
        (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a n).hom =
      resolutionBase.{u, v, w} J (f.inverseImageRing.map a) n :=
  Under.w ((standardResolutionInverseImageIso.{u, v, w, u', v', w'} J K f a).hom.app n)

/-- The degreewise comparison of the standard resolutions is compatible with the
augmentations. -/
lemma resolutionInverseImageIso_augmentation (n : SimplexCategoryᵒᵖ) :
    (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a n).hom ≫
        resolutionAugmentation.{u, v, w} J (f.inverseImageRing.map a) n =
      f.inverseImageRing.map (resolutionAugmentation.{u', v', w'} K a n) :=
  congrArg (fun k ↦ k.right)
    (standardResolutionInverseImageIso_hom_app_comp_augmentation.{u, v, w, u', v', w'}
      J K f a n.unop.len)

end CategoryTheory.Sheaf

end
