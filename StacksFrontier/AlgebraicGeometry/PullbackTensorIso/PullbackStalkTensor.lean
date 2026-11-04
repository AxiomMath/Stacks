module

public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.StalkRingComparison

/-!
# The stalk of a pullback as a tensor product over the stalks of Stacks 01CB

`Stacks.ModuleSkyscraper.ringedSpacePullbackStalkIso` identifies `(f^*A)_x` with `L (A_{f x})`
for any `L` left adjoint to restriction of scalars along
`Stacks.ModuleSkyscraper.ringedSpaceStalkRingMap`, a map between the stalks of the structure
sheaves **taken in `RingCat`**. The stalk of a tensor product of Stacks 01CB is a tensor
product over `Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk`, the stalk **taken in
  `CommRingCat`**. This file
supplies an `L` whose value is a tensor product over the latter, so that the two halves of
the computation live over the same base rings.

## Main definitions and results

* `Stacks.PullbackTensorIso.commStalkRingMap`: the stalk map of `f` between the stalks taken
  in `CommRingCat`, obtained by conjugating the `RingCat` stalk map with `stalkRingEquiv`.
  `ringedSpaceStalkRingMap_eq` says that conjugating back returns the `RingCat` stalk map,
  which is the only compatibility used below.
* `Stacks.PullbackTensorIso.stalkExtendScalars`: the chosen `L`. It is extension of scalars
  along `commStalkRingMap`, conjugated by restriction of scalars along the two ring
  isomorphisms `stalkRingEquiv`, so that its value on `N` is `𝒪_{X,x} ⊗_{𝒪_{Y,f x}} N` with
  both stalks taken in `CommRingCat`.
* `Stacks.PullbackTensorIso.stalkExtendScalarsAdj`: it is left adjoint to restriction of
  scalars along the `RingCat` stalk map, as `ringedSpacePullbackStalkIso` requires. Built as
  a composite of three adjunctions — the equivalence given by restriction along a ring
  isomorphism in each direction, and `ModuleCat.extendRestrictScalarsAdj` in the middle —
  transported along the comparison of the two right adjoints. There is no equality cast
  anywhere: the comparison is `ModuleCat.restrictScalarsComp'` applied to
  `ringedSpaceStalkRingMap_eq`.
* `Stacks.PullbackTensorIso.pullbackStalkTensorIso`: the resulting identification
  `(f^*A)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} A_{f x}`, natural in `A`, and
  `pullbackStalkTensorIso_inv_app_unit`: **on elements it carries the image of `germ a` under
  the unit of `stalkExtendScalarsAdj` to `germ (η a)`**, the germ of the pullback-unit image
  of `a`. The unit is `n ↦ 1 ⊗ₜ n` for the module structure `commStalkModule`; that reading
  is not stated as a lemma here, because the pure tensor has to be written in the restriction
  of scalars along `stalkRingEquiv` and a type ascription does not reach the elaboration of
  the tensor notation. It is recovered where the tensor product is given as a linear
  equivalence.

## Universes

A single universe `u`, over `AlgebraicGeometry.RingedSpace.{u, u}`.

## Transparency notes

* The functor and the adjunction are stated over `ringCatStalk`, which is
  `TopCat.Presheaf.stalk (Stacks.SheafOfModules.TensorStalkRingedSpace.O _) _`, where
  `Stacks.ModuleSkyscraper.ringedSpacePullbackStalkIso` states them over
  `Stacks.ModuleSkyscraper.Stalk (structureSheafRing _) _`. The two are
  definitionally equal and the application below is accepted on that basis; the first
  spelling is used because it is the one against which the module structures on a stalk
  resolve, instance search being reducible-only.
* The three-fold composite of adjunctions produces its right adjoint associated to the
  right, while `ModuleCat.restrictScalarsComp'` produces it associated to the left. The two
  are definitionally equal, so no associator is inserted.

## What is not done here

This file does not prove Stacks 01CD. It removes the base-ring mismatch that blocked the
stalk route and gives the identification of `(f^*A)_x` on elements over 01CB's rings. What
remains is the base-change identity for a tensor product of two such, and the assembly; see
`StacksFrontier/AlgebraicGeometry/PullbackTensorIso/Basic.lean`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped TensorProduct

universe u

namespace Stacks.PullbackTensorIso

open RingedSpaceModuleAdjunction Stacks.ModuleSkyscraper

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (x : X.carrier)

/-- The stalk map of `f` between the stalks of the structure sheaves taken in `CommRingCat`:
the stalk map taken in `RingCat`, conjugated by `stalkRingEquiv`. -/
def commStalkRingMap :
    Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y (f.hom.base x) →+*
      Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x :=
  (stalkRingEquiv X x).symm.toRingHom.comp
    ((ringedSpaceStalkRingMap f x).hom.comp (stalkRingEquiv Y (f.hom.base x)).toRingHom)

/-- The module structure on the stalk at `x` over the stalk at `f x` given by
`commStalkRingMap`. This is the module structure the tensor product below is taken for; it is
made a local instance so that a pure tensor can be written down at all. -/
abbrev commStalkModule : Module (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y
  (f.hom.base x))
    (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x) :=
  (commStalkRingMap f x).toModule

attribute [local instance] commStalkModule

/-- Conjugating `commStalkRingMap` back returns the stalk map taken in `RingCat`. -/
lemma ringedSpaceStalkRingMap_eq :
    (ringedSpaceStalkRingMap f x).hom =
      ((stalkRingEquiv X x).toRingHom.comp (commStalkRingMap f x)).comp
        (stalkRingEquiv Y (f.hom.base x)).symm.toRingHom :=
  RingHom.ext fun r =>
    (((stalkRingEquiv X x).apply_symm_apply
          ((ringedSpaceStalkRingMap f x).hom (stalkRingEquiv Y (f.hom.base x)
            ((stalkRingEquiv Y (f.hom.base x)).symm r)))).trans
      (congrArg (fun t => (ringedSpaceStalkRingMap f x).hom t)
        ((stalkRingEquiv Y (f.hom.base x)).apply_symm_apply r))).symm

/-- **Extension of scalars along the stalk map, with the tensor product taken over the stalks
of Stacks 01CB.** Its value on `N` is `𝒪_{X,x} ⊗_{𝒪_{Y,f x}} N`, both stalks being taken in
`CommRingCat`. -/
def stalkExtendScalars : ModuleCat.{u} (ringCatStalk Y (f.hom.base x)) ⥤
    ModuleCat.{u} (ringCatStalk X x) :=
  ModuleCat.restrictScalars (stalkRingEquiv Y (f.hom.base x)).toRingHom ⋙
    ModuleCat.extendScalars (commStalkRingMap f x) ⋙
      ModuleCat.restrictScalars (stalkRingEquiv X x).symm.toRingHom

/-- The comparison of the right adjoint of the composite with restriction of scalars along
the stalk map taken in `RingCat`. -/
def restrictStalkIso :
    ModuleCat.restrictScalars.{u} (ringedSpaceStalkRingMap f x).hom ≅
      ModuleCat.restrictScalars.{u} (stalkRingEquiv X x).toRingHom ⋙
        ModuleCat.restrictScalars (commStalkRingMap f x) ⋙
          ModuleCat.restrictScalars (stalkRingEquiv Y (f.hom.base x)).symm.toRingHom :=
  ModuleCat.restrictScalarsComp' _ _ _ (ringedSpaceStalkRingMap_eq f x) ≪≫
    Functor.isoWhiskerRight (ModuleCat.restrictScalarsComp' _ _ _ rfl) _

/-- **`stalkExtendScalars` is left adjoint to restriction of scalars along the stalk map
taken in `RingCat`**, which is the datum
`Stacks.ModuleSkyscraper.ringedSpacePullbackStalkIso` consumes. -/
def stalkExtendScalarsAdj : stalkExtendScalars f x ⊣
    ModuleCat.restrictScalars.{u} (ringedSpaceStalkRingMap f x).hom :=
  Adjunction.ofNatIsoRight
    (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          (stalkRingEquiv Y (f.hom.base x))).toAdjunction.comp
        (ModuleCat.extendRestrictScalarsAdj (commStalkRingMap f x))).comp
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (stalkRingEquiv X x)).symm.toAdjunction)
    (restrictStalkIso f x).symm

/-- **The stalk of a pullback as a tensor product over the stalks of Stacks 01CB**,
`(f^*A)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} A_{f x}`, naturally in `A`. -/
def pullbackStalkTensorIso :
    modulePullback f ⋙ AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) (f.hom.base x) ⋙
        stalkExtendScalars f x :=
  ringedSpacePullbackStalkIso f x (stalkExtendScalarsAdj f x)

/-- **The identification of the stalk of a pullback, on elements**: it carries the image of
`germ a` under the unit — that is, `1 ⊗ germ a` by `stalkExtendScalarsAdj_unit_apply` — to
the germ of the pullback-unit image of `a`. -/
lemma pullbackStalkTensorIso_inv_app_unit
    (A : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y)) (V : Opens Y.carrier)
    (hV : f.hom.base x ∈ V) (a : A.val.obj (op V)) :
    ((pullbackStalkTensorIso f x).inv.app A).hom
        ((stalkExtendScalarsAdj f x).unit.app (stalkMod (structureSheafRing Y) (f.hom.base x) A)
          (modGerm (structureSheafRing Y) (f.hom.base x) A V hV a)) =
      modGerm (structureSheafRing X) x ((Stacks.RingedSpace.pullbackFunctor f).obj A)
        ((opensMap f).obj V) hV (Stacks.RingedSpace.pullbackUnit f A (op V) a) :=
  ringedSpacePullbackStalkIso_inv_app_unit f x (stalkExtendScalarsAdj f x) A V hV a

end Stacks.PullbackTensorIso
