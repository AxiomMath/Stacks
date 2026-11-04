module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf
public import StacksFrontier.Homology.ExtendScalars.AlongARingIsomorphism
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback

/-!
# The stalk of a pullback as a base change, at the spelling of the décalage files

Let `f : X ⟶ Y` be a morphism of ringed spaces and `x` a point of `X`.  Stacks tag 0098 says
that the stalk at `x` of a pullback is the base change of the stalk at `f x` along the germ map
of `f`,

`(f^* A)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} A_{f(x)}`,

and `Stacks.RingedSpace.stalkModulePullbackFunctorIso` proves it, naturally in `A`.  That
statement is written over the `RingCat`-valued stalks of `structureSheafRing`, which is where
`SheafOfModules` and the pullback functor live.  The décalage files
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheaf.lean` and everything downstream of it)
read the stalk instead over the *commutative* ring `ringStalk X x = 𝒪_{X,x}`, the
`CommRingCat`-valued stalk, through `Stacks.IdealTorsion.Eta.stalkModuleFunctor`.  This file
transports tag 0098 across that identification, so that the décalage calculus at a stalk can be
compared with the ring-level base change of
`StacksFrontier/Homology/Eta/BaseChange.lean`, whose statements are about `B ⊗[A] -` for a
commutative `A` and `B`.

## Main definitions

* `Stacks.RingedSpace.commStalkGermMap`: the germ map `𝒪_{Y,f(x)} →+* 𝒪_{X,x}` of `f`, read
  between the `CommRingCat`-valued stalks.
* `Stacks.RingedSpace.commStalkBaseChange`: base change along it,
  `N ↦ 𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} N`.

## Main results

* `Stacks.RingedSpace.commStalkGermMap_comp`: the germ map is compatible with the comparison
  `SemilinearStalk.commStalkRingEquiv` of the two spellings of the stalk ring.
* `Stacks.RingedSpace.stalkPullbackBaseChangeIso`: **Stacks tag 0098 at the décalage
  spelling** — `f^* ⋙ (-)_x ≅ (-)_{f(x)} ⋙ (𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} -)` as functors into
  `ModuleCat (ringStalk X x)`.

## Implementation notes

`Stacks.IdealTorsion.Eta.stalkModuleFunctor X x` is the `RingCat`-valued stalk functor followed
by restriction of scalars along `SemilinearStalk.commStalkIso`, which is an isomorphism of
rings; so the transport is purely a change-of-rings computation.  Restriction of scalars along an
isomorphism is extension of scalars along it
(`ModuleCat.extendScalarsIsoRestrictScalarsSymm`), and two successive extensions of scalars
compose (`ModuleCat.extendScalarsComp`), so the whole comparison is five whiskerings of those
two facts around `Stacks.RingedSpace.stalkModulePullbackFunctorIso`.  The one equation that is
not formal is `commStalkGermMap_comp`, which says that the germ map chosen here is the one the
comparison of stalk rings conjugates the `RingCat`-level germ map into; it holds by construction.

The commutative-ring structure on the `RingCat`-valued stalk is seated by hand with `letI`
inside the construction, as `Stacks.RingedSpace.structureStalkCommRing` is deliberately not an
instance; see the implementation notes of
`StacksFrontier/Topology/Sheaves/RingedSpace/StalkModulePullback.lean`.  No `ModuleCat` over that
stalk occurs in the *statement* below, so no consumer has to reproduce the seating.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory

open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

open Stacks.IdealTorsion.Eta (stalkModuleFunctor)

universe u

namespace Stacks.RingedSpace

noncomputable section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y) (x : X)

/-- **The germ map of a morphism of ringed spaces between the commutative stalk rings**,
`𝒪_{Y,f(x)} →+* 𝒪_{X,x}`.  It is `Stacks.RingedSpace.stalkRingMap`, which is written between
the `RingCat`-valued stalks, conjugated by the comparison
`SemilinearStalk.commStalkRingEquiv` of the two spellings of the stalk ring. -/
def commStalkGermMap : ringStalk Y (f.hom.base x) →+* ringStalk X x :=
  (SemilinearStalk.commStalkRingEquiv X.presheaf x).toRingHom.comp
    ((stalkRingMap f x).hom.comp
      (SemilinearStalk.commStalkRingEquiv Y.presheaf (f.hom.base x)).symm.toRingHom)

/-- The germ map between the commutative stalk rings is the `RingCat`-level germ map read
through the comparison of the two spellings of the stalk ring. -/
theorem commStalkGermMap_comp :
    (commStalkGermMap f x).comp
        (SemilinearStalk.commStalkRingEquiv Y.presheaf (f.hom.base x)).toRingHom =
      (SemilinearStalk.commStalkRingEquiv X.presheaf x).toRingHom.comp
        (stalkRingMap f x).hom := by
  refine RingHom.ext fun r => ?_
  show (SemilinearStalk.commStalkRingEquiv X.presheaf x)
      ((stalkRingMap f x).hom ((SemilinearStalk.commStalkRingEquiv Y.presheaf
        (f.hom.base x)).symm ((SemilinearStalk.commStalkRingEquiv Y.presheaf
          (f.hom.base x)) r))) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

/-- **Base change of stalk modules along the germ map**, between the commutative stalk rings:
`N ↦ 𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} N`.  Its carrier is literally the tensor product, and its action
on morphisms is literally `LinearMap.baseChange`. -/
abbrev commStalkBaseChange :
    ModuleCat.{u} (ringStalk Y (f.hom.base x)) ⥤ ModuleCat.{u} (ringStalk X x) :=
  ModuleCat.extendScalars.{u, u, u} (commStalkGermMap f x)

/-- **Stacks tag 0098 at the spelling of the décalage files.**  Taking the pullback along `f` and
then the stalk at `x`, as a functor into modules over the commutative local ring `𝒪_{X,x}`, is
taking the stalk at `f x` and then base changing along the germ map — naturally in the sheaf of
modules.

This is `Stacks.RingedSpace.stalkModulePullbackFunctorIso` transported along the comparison
`SemilinearStalk.commStalkIso` of the `RingCat`-valued with the `CommRingCat`-valued stalk of
the structure sheaf, on both `X` and `Y`. -/
def stalkPullbackBaseChangeIso :
    RingedSpaceModuleAdjunction.modulePullback f ⋙ stalkModuleFunctor X x ≅
      stalkModuleFunctor Y (f.hom.base x) ⋙ commStalkBaseChange f x :=
  letI := structureStalkCommRing Y (f.hom.base x)
  letI := structureStalkCommRing X x
  Functor.isoWhiskerLeft (RingedSpaceModuleAdjunction.modulePullback f ⋙
      AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) x)
      (ModuleCat.extendScalarsIsoRestrictScalarsSymm
        (SemilinearStalk.commStalkRingEquiv X.presheaf x)).symm ≪≫
    Functor.isoWhiskerRight (stalkModulePullbackFunctorIso f x)
      (ModuleCat.extendScalars.{u, u, u}
        (SemilinearStalk.commStalkRingEquiv X.presheaf x).toRingHom) ≪≫
    Functor.isoWhiskerLeft
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) (f.hom.base x))
      ((ModuleCat.extendScalarsComp (stalkRingMap f x).hom
        (SemilinearStalk.commStalkRingEquiv X.presheaf x).toRingHom).symm) ≪≫
    Functor.isoWhiskerLeft
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) (f.hom.base x))
      (eqToIso (congrArg ModuleCat.extendScalars.{u, u, u} (commStalkGermMap_comp f x).symm)) ≪≫
    Functor.isoWhiskerLeft
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) (f.hom.base x))
      (ModuleCat.extendScalarsComp
        (SemilinearStalk.commStalkRingEquiv Y.presheaf (f.hom.base x)).toRingHom
        (commStalkGermMap f x)) ≪≫
    Functor.isoWhiskerLeft
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) (f.hom.base x))
      (Functor.isoWhiskerRight (ModuleCat.extendScalarsIsoRestrictScalarsSymm
        (SemilinearStalk.commStalkRingEquiv Y.presheaf (f.hom.base x)))
        (commStalkBaseChange f x))

/-- The naturality square of `Stacks.RingedSpace.stalkPullbackBaseChangeIso`, written out: the
stalk of the pullback of a map of sheaves of modules is the base change of the stalk of that
map. -/
theorem stalkPullbackBaseChangeIso_naturality
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)} (g : A ⟶ B) :
    (stalkModuleFunctor X x).map
          ((RingedSpaceModuleAdjunction.modulePullback f).map g) ≫
        (stalkPullbackBaseChangeIso f x).hom.app B =
      (stalkPullbackBaseChangeIso f x).hom.app A ≫
        (commStalkBaseChange f x).map ((stalkModuleFunctor Y (f.hom.base x)).map g) :=
  (stalkPullbackBaseChangeIso f x).hom.naturality g

end

end Stacks.RingedSpace

end
