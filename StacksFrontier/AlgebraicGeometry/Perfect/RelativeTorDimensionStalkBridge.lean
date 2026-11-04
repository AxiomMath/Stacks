module

public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalks
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectThickening
public import StacksFrontier.AlgebraicGeometry.SheafifyStalk.StalkMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealTorsionFree
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictScalars

/-!
# The coefficient stalk of `f^{-1}𝒪_S` and the local ring of the base

Let `f : X ⟶ S` be a morphism of schemes. Condition (2) of Stacks 069C reads `𝒪_X` as a sheaf of
modules over `f^{-1}𝒪_S` on the inverse-image ringed space `(X, f^{-1}𝒪_S)`, and the stalkwise
criterion of Stacks 09U9 turns that into a condition at the stalk ring `(f^{-1}𝒪_S)_x`. Condition
(3) reads the same thing over the local ring `𝒪_{S, f x}` along the stalk map of `f`. This file
identifies the two: at a point `x` of `X` the stalk of
`AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction f` of `𝒪_X[0]`, over `(f^{-1}𝒪_S)_x`, is
`𝒪_{X, x}` placed in degree zero over `𝒪_{S, f x}`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.inverseImageStalkRingEquiv`: the comparison
  `(f^{-1}𝒪_S)_x ≃+* 𝒪_{S, f x}`, read at the `RingCat`-valued stalk the module API uses.
* `AlgebraicGeometry.Scheme.Hom.stalkObjRingIso`: a stalk of a sheaf of modules that is free of
  rank one on the stalk ring, as an isomorphism in the category of modules.
* `AlgebraicGeometry.Scheme.Hom.structureModuleStalkIso`: the stalk of the structure sheaf of a
  ringed space, viewed as a module over itself, is the local ring.
* `AlgebraicGeometry.Scheme.Hom.relativeStalkStructureModuleIso` and
  `relativeStalkDerivedIso`: the bridge itself, degreewise and in the derived category.

## Main results

* `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_stalk_relative_iff`: **the
  coefficient-stalk bridge.** The stalk at `x` of the derived restriction of scalars of `𝒪_X[0]`
  has Tor amplitude in `[a, b]` over `(f^{-1}𝒪_S)_x` if and only if `𝒪_{X, x}` has Tor amplitude
  in `[a, b]` over `𝒪_{S, f x}`.
* `AlgebraicGeometry.Scheme.Hom.commStalkRingEquiv_comp_ringStalkMap`: the square behind it — the
  stalk of the structural map `f^{-1}𝒪_S ⟶ 𝒪_X`, read through the two comparisons with the
  `CommRingCat`-valued stalks, is the stalk map of `f`.
* `AlgebraicGeometry.Scheme.Hom.isGenuineRelativeTensorFamily_canonical`: the canonical family of
  certificates is pinned to the genuine tensor product, so condition (2) of Stacks 069C is not
  vacuous; `forall_locallyHasFiniteRelativeTorDimension_iff_exists` is the resulting equivalence
  of its universal and existential readings.
* `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_obj_iff`:
  canonical Tor amplitude is unchanged by restriction of scalars along a ring isomorphism, for an
  arbitrary object of the derived category. This is
  `hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff`, in the namespace
  `AlgebraicGeometry.AffineRelativeTorAmplitude`, transported off the image of
  `DerivedCategory.Q`.

## Implementation notes

**Three stalk rings, and the two comparisons between them.** The module API of a ringed space
takes its modules over the `RingCat`-valued stalk of `𝒪 ⋙ forget₂ CommRingCat RingCat`, whereas
`AlgebraicGeometry.Scheme.Hom.stalkMap` and the local rings of a scheme live at the
`CommRingCat`-valued stalk. `SemilinearStalk.commStalkRingEquiv` compares the two, and
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso` compares `(f^{-1}𝒪_S)_x` with
`𝒪_{S, f x}`. Composing them is `inverseImageStalkRingEquiv`, and the compatibility of that
composite with the structural map is `commStalkRingEquiv_comp_ringStalkMap`, proved on germs:
each of `SemilinearStalk.ringStalkMap_germ`, `SemilinearStalk.commStalkRingEquiv_germ` and
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap` computes one factor
there, and germs are jointly surjective.

**Instance search cannot cross `StrictlyPerfect.structureSheafOfRings`.** That spelling of the
sheaf of rings is a plain `def`, so a `Module` or a `CommRing` instance proved for the stalk of a
variable sheaf of rings is not *found* at it, even though the two are the same structure at
default transparency. The three exactness instances of the stalk functor and the commutativity of
the stalk ring are therefore re-seated here as `local instance`s keyed at the inverse-image ringed
space, and `stalkObjRingIso` — where a `Module` instance on the carrier of a restriction of
scalars is unavoidable — is stated for a *variable* sheaf of rings and instantiated afterwards, so
that every instance in it is synthesised where synthesis succeeds. Writing the same construction
directly at `structureSheafOfRings` fails: the `Semiring` the goal carries comes from
`StacksDraft.StalkTensor.commRing_stalk` while the one the module category carries comes from
`RingCat`, and the two are interchangeable only at default transparency.

**The object is a single complex, which is what keeps the derived-category work small.** The
object condition (2) is about is `𝒪_X` placed in degree zero, so the two functors it is pushed
through are commuted with `DerivedCategory.singleFunctor` by
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` and the whole identification happens in
the category of modules; no comparison of composites of derived functors is needed.

`hasTorAmplitudeCanonical_restrictScalars_ringEquiv_obj_iff` duplicates the `private`
`hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff'` of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectThickening`, derived here from the same
public biconditional on complexes and in the same way; it is a dedup target, and the private copy
should be deleted in favour of this one.

`Stacks.IdealTorsion.unitStalkAddEquiv` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealTorsionFree` is reused rather than rebuilt, and
is the reason that file is imported here; `Stacks.IdealTorsion.Eta.unitStalkAddEquiv` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheaf.lean` is a second copy of it and is a dedup target.

## References

* [Stacks Project, Lemma 36.19.9 (Tag 069C)](https://stacks.math.columbia.edu/tag/069C)
* [Stacks Project, Lemma 20.48.8 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- Canonical Tor amplitude depends only on the isomorphism class of an object of `D(R)`. -/
private theorem hasTorAmplitudeCanonical_iff_of_iso' {R : Type u} [CommRing R]
    {E F : DerivedCategory (ModuleCat.{u} R)} (e : E ≅ F) (a b : ℤ) :
    HasTorAmplitudeCanonical R E a b ↔ HasTorAmplitudeCanonical R F a b :=
  ⟨AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b,
    AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e.symm a b⟩

/-- **Canonical Tor amplitude is unchanged by restriction of scalars along a ring isomorphism**,
for an arbitrary object of the derived category.

`hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff`, in the namespace
`AlgebraicGeometry.AffineRelativeTorAmplitude`, is this statement for an object in the image of
`DerivedCategory.Q`; every object is isomorphic to one, by
`CategoryTheory.Functor.objObjPreimageIso`, and canonical Tor amplitude transports along an
isomorphism. -/
theorem hasTorAmplitudeCanonical_restrictScalars_ringEquiv_obj_iff {R T : Type u} [CommRing R]
    [CommRing T] (e : R ≃+* T) (E : DerivedCategory (ModuleCat.{u} T)) (a b : ℤ) :
    HasTorAmplitudeCanonical R
        ((ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory.obj E) a b ↔
      HasTorAmplitudeCanonical T E a b := by
  set K := DerivedCategory.Q.objPreimage E with hK
  have eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have ei : (ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory.obj E ≅
      DerivedCategory.Q.obj (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
    (ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory.mapIso eK.symm ≪≫
      (ModuleCat.restrictScalars e.toRingHom).mapDerivedCategoryFactors.app K
  rw [hasTorAmplitudeCanonical_iff_of_iso' eK.symm,
    hasTorAmplitudeCanonical_iff_of_iso' ei]
  exact AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff e K a b

/-- The stalk at `x` of `f⁻¹𝒪_S`, read in `RingCat`, is the local ring `𝒪_{S, f x}`. -/
def inverseImageStalkRingEquiv :
    ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafOfRings.{u}
          (RingedSpace.inverseImage S.toRingedSpace f.base)).obj x) ≃+*
      ToType (S.presheaf.stalk (f.base x)) :=
  (SemilinearStalk.commStalkRingEquiv
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf x).trans
    (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).commRingCatIsoToRingEquiv

/-- **The comparison between the `RingCat`- and the `CommRingCat`-valued stalk is natural along
the structural map of `f`.** Applied to an element, this says that the stalk of
`f^{-1}𝒪_S ⟶ 𝒪_X` at `x`, read in `RingCat` and transported to the `CommRingCat`-valued stalks,
is the stalk map of `f` precomposed with the comparison `(f^{-1}𝒪_S)_x ≅ 𝒪_{S, f x}`.

Germs are jointly surjective, and on a germ each of the three maps involved is computed by
`SemilinearStalk.ringStalkMap_germ`, `SemilinearStalk.commStalkRingEquiv_germ` and
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap`. -/
theorem commStalkRingEquiv_ringStalkMap_inverseImageRingToStructure
    (r : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings.{u}
        (RingedSpace.inverseImage S.toRingedSpace f.base)).obj x)) :
    SemilinearStalk.commStalkRingEquiv X.presheaf x
        ((SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom x).hom r)
      = (f.stalkMap x).hom
          ((Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom.hom
            (SemilinearStalk.commStalkRingEquiv
              ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf x r)) := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf ⋙
      forget₂ CommRingCat.{u} RingCat.{u}) r
  refine Eq.trans (congrArg (SemilinearStalk.commStalkRingEquiv X.presheaf x)
    (SemilinearStalk.ringStalkMap_germ (inverseImageRingToStructure f).hom x U hU s)) ?_
  refine Eq.trans (SemilinearStalk.commStalkRingEquiv_germ X.presheaf x U hU _) ?_
  refine Eq.trans ?_ (congrArg (fun z => (f.stalkMap x).hom
      ((Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom.hom z))
    (SemilinearStalk.commStalkRingEquiv_germ
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf x U hU s)).symm
  refine Eq.trans ?_ (ConcreteCategory.congr_hom
    (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap f x)
    (TopCat.Presheaf.germ
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf U x hU s)).symm
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hU
    (AlgebraicGeometry.inverseImageStructureMap f).hom s).symm

/-- **The coefficient-stalk square.** The stalk at `x` of the structural map `f⁻¹𝒪_S ⟶ 𝒪_X`,
read through the two comparisons with the `CommRingCat`-valued stalks, is the stalk map of `f`.
-/
theorem commStalkRingEquiv_comp_ringStalkMap :
    (SemilinearStalk.commStalkRingEquiv X.presheaf x).toRingHom.comp
        (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom x).hom
      = (f.stalkMap x).hom.comp (inverseImageStalkRingEquiv f x).toRingHom :=
  RingHom.ext fun r => commStalkRingEquiv_ringStalkMap_inverseImageRingToStructure f x r

/-- The stalk functor of the inverse-image ringed space is additive, at the point spelling a
point of `X` presents. -/
local instance additive_stalkFunctor_inverseImage :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafOfRings.{u}
        (RingedSpace.inverseImage S.toRingedSpace f.base)) x).Additive :=
  RingedSpace.additive_stalkFunctor _ _

/-- The stalk functor of the inverse-image ringed space is left exact, at the point spelling a
point of `X` presents. -/
local instance preservesFiniteLimits_stalkFunctor_inverseImage :
    PreservesFiniteLimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) x) :=
  RingedSpace.preservesFiniteLimits_stalkFunctor _ _

/-- The stalk functor of the inverse-image ringed space is right exact, at the point spelling a
point of `X` presents. -/
local instance preservesFiniteColimits_stalkFunctor_inverseImage :
    PreservesFiniteColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) x) :=
  RingedSpace.preservesFiniteColimits_stalkFunctor _ _

/-- **A stalk of a sheaf of modules that is free of rank one on the stalk ring**, as an
isomorphism of modules. The datum is an additive equivalence `ψ` of the stalk with a ring `T`, a
ring isomorphism `e` of the stalk ring with `T`, and the semilinearity of `ψ` over `e`.

The sheaf of rings is a variable, which is what makes the `Module` instances on the two carriers
findable; see the implementation notes of this file. -/
def stalkObjRingIso {Z : TopCat.{u}}
    (O : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) (z : Z)
    {T : Type u} [Ring T]
    (e : ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj z) ≃+* T)
    (N : _root_.SheafOfModules.{u} O)
    (ψ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf z) ≃+ T)
    (hψ : ∀ (r : ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj z))
        (m : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf z)),
      ψ (r • m) = e r * ψ m) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor O z).obj N ≅
      (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T) where
  hom := ConcreteCategory.ofHom
    (C := ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj z))
    { toFun := fun m => ψ m
      map_add' := fun a b => map_add ψ a b
      map_smul' := fun r m => hψ r m }
  inv := ConcreteCategory.ofHom
    (C := ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj z))
    { toFun := fun t => ψ.symm t
      map_add' := fun a b => map_add ψ.symm a b
      map_smul' := fun r t => ψ.injective (by
        refine Eq.trans (ψ.apply_symm_apply _) ?_
        refine Eq.trans ?_ (hψ r (ψ.symm t)).symm
        exact (congrArg (fun w => e r * w) (ψ.apply_symm_apply t)).symm) }
  hom_inv_id := by ext m; exact ψ.symm_apply_apply m
  inv_hom_id := by ext t; exact ψ.apply_symm_apply t

/-- **The stalk of the structure sheaf of a ringed space, viewed as a module over itself, is the
local ring at the point.** Both are the same filtered colimit, computed in `AddCommGrpCat` and in
`CommRingCat`; the comparison is `Stacks.IdealTorsion.unitStalkAddEquiv`, and its semilinearity
over `SemilinearStalk.commStalkRingEquiv` is checked on germs, where the scalar action is
multiplication of sections. -/
def structureModuleStalkIso (Y : RingedSpace.{u, u}) (y : Y.carrier) :=
  stalkObjRingIso (structureSheafOfRings.{u} Y) y
    (SemilinearStalk.commStalkRingEquiv Y.presheaf y) (structureModule Y)
    (Stacks.IdealTorsion.unitStalkAddEquiv Y y) (by
      intro r m
      obtain ⟨V, hV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
        (structureModule Y).val.presheaf m
      obtain ⟨W, hW, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := RingCat.{u})
        (structureSheafOfRings.{u} Y).obj r
      have hmem : y ∈ V ⊓ W := ⟨hV, hW⟩
      have hb := TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
        (structureModule Y).val.presheaf (homOfLE (inf_le_left : V ⊓ W ≤ V)) y hmem b
      have ha := TopCat.Presheaf.germ_res_apply (C := RingCat.{u})
        (structureSheafOfRings.{u} Y).obj (homOfLE (inf_le_right : V ⊓ W ≤ W)) y hmem a
      rw [← ha, ← hb]
      have h1 : ∀ c : ToType ((structureSheafOfRings.{u} Y).obj.obj (Opposite.op (V ⊓ W))),
          SemilinearStalk.commStalkRingEquiv Y.presheaf y
              ((ConcreteCategory.hom (TopCat.Presheaf.germ
                (structureSheafOfRings.{u} Y).obj (V ⊓ W) y hmem)) c)
            = (ConcreteCategory.hom (TopCat.Presheaf.germ Y.presheaf (V ⊓ W) y hmem)) c :=
        fun c => SemilinearStalk.commStalkRingEquiv_germ Y.presheaf y (V ⊓ W) hmem c
      have h2 : ∀ c : ToType ((structureModule Y).val.presheaf.obj (Opposite.op (V ⊓ W))),
          Stacks.IdealTorsion.unitStalkAddEquiv Y y
              ((ConcreteCategory.hom (TopCat.Presheaf.germ
                (structureModule Y).val.presheaf (V ⊓ W) y hmem)) c)
            = (ConcreteCategory.hom (TopCat.Presheaf.germ Y.presheaf (V ⊓ W) y hmem)) c :=
        fun c => Stacks.IdealTorsion.unitStalkAddEquiv_germ Y y (V ⊓ W) hmem c
      refine Eq.trans (congrArg (Stacks.IdealTorsion.unitStalkAddEquiv Y y)
        (PresheafOfModules.germ_ringCat_smul (structureModule Y).val y (V ⊓ W) hmem
          ((ConcreteCategory.hom ((structureSheafOfRings.{u} Y).obj.map
            (homOfLE (inf_le_right : V ⊓ W ≤ W)).op)) a)
          ((ConcreteCategory.hom ((structureModule Y).val.presheaf.map
            (homOfLE (inf_le_left : V ⊓ W ≤ V)).op)) b)).symm) ?_
      refine Eq.trans
        (Stacks.IdealTorsion.unitStalkAddEquiv_germ Y y (V ⊓ W) hmem _) ?_
      refine Eq.trans ?_ (congrArg₂ (· * ·) (h1 _) (h2 _)).symm
      exact map_mul (ConcreteCategory.hom (TopCat.Presheaf.germ Y.presheaf (V ⊓ W) y hmem)) _ _)

/-- **The stalk of the derived restriction of scalars of a module placed in degree zero is a
module placed in degree zero.** Both functors are exact, so each commutes with
`DerivedCategory.singleFunctor` by
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`. -/
def stalkDerivedScalarRestrictionSingleIso (E : OXMod.{u, u} X.toRingedSpace) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)) x).mapDerivedCategory.obj
        ((derivedScalarRestriction f).obj
          ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj E)) ≅
      (DerivedCategory.singleFunctor
          (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
            (structureSheafOfRings.{u}
              (RingedSpace.inverseImage S.toRingedSpace f.base)).obj x)) 0).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u}
              (RingedSpace.inverseImage S.toRingedSpace f.base)) x).obj
          ((scalarRestriction f).obj E)) :=
  (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u}
          (RingedSpace.inverseImage S.toRingedSpace f.base)) x).mapDerivedCategory.mapIso
      (((scalarRestriction f).mapDerivedCategorySingleFunctor 0).app E) ≪≫
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafOfRings.{u}
        (RingedSpace.inverseImage S.toRingedSpace f.base)) x).mapDerivedCategorySingleFunctor
        0).app ((scalarRestriction f).obj E)

/-- The algebra structure clause (3) of Stacks 069C reads the local ring `𝒪_{X, x}` over. -/
local instance algebraStalkMap :
    Algebra (ToType (S.presheaf.stalk (f.base x))) (ToType (X.presheaf.stalk x)) :=
  (f.stalkMap x).hom.toAlgebra

/-- **The coefficient-stalk bridge, at the level of modules.** The stalk at `x` of `𝒪_X` read
over `f^{-1}𝒪_S` is `𝒪_{X, x}` read over `𝒪_{S, f x}`.

The stalk does not see the restriction of scalars
(`AlgebraicGeometry.SheafOfModules.stalkFunctorRestrictScalarsFunctorIso`), the stalk of the
structure module is the local ring (`structureModuleStalkIso`), and the two resulting changes of
coefficient ring are composed into one by `ModuleCat.restrictScalarsComp'`, the two composites
agreeing by `commStalkRingEquiv_comp_ringStalkMap`. -/
def relativeStalkStructureModuleIso :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)) x).obj
        ((scalarRestriction f).obj (structureModule X.toRingedSpace)) ≅
      (ModuleCat.restrictScalars (inverseImageStalkRingEquiv f x).toRingHom).obj
        (ModuleCat.of (ToType (S.presheaf.stalk (f.base x)))
          (ToType (X.presheaf.stalk x))) :=
  AlgebraicGeometry.SheafOfModules.stalkFunctorRestrictScalarsIso
      (inverseImageRingToStructure f) x (structureModule X.toRingedSpace) ≪≫
    (ModuleCat.restrictScalars
        (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom x).hom).mapIso
      (structureModuleStalkIso X.toRingedSpace x) ≪≫
    ((ModuleCat.restrictScalarsComp'.{u}
        (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom x).hom
        (SemilinearStalk.commStalkRingEquiv X.presheaf x).toRingHom
        ((f.stalkMap x).hom.comp (inverseImageStalkRingEquiv f x).toRingHom)
        (commStalkRingEquiv_comp_ringStalkMap f x).symm).app
      (ModuleCat.of (ToType (X.presheaf.stalk x)) (ToType (X.presheaf.stalk x)))).symm ≪≫
    (ModuleCat.restrictScalarsComp'.{u} (inverseImageStalkRingEquiv f x).toRingHom
        (f.stalkMap x).hom
        ((f.stalkMap x).hom.comp (inverseImageStalkRingEquiv f x).toRingHom) rfl).app
      (ModuleCat.of (ToType (X.presheaf.stalk x)) (ToType (X.presheaf.stalk x)))

/-- **The coefficient-stalk bridge, in the derived category.** `relativeStalkStructureModuleIso`
placed in degree zero, with the two single-complex comparisons of
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` on either side. -/
def relativeStalkDerivedIso :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)) x).mapDerivedCategory.obj
        ((derivedScalarRestriction f).obj
          ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj
            (structureModule X.toRingedSpace))) ≅
      (ModuleCat.restrictScalars
          (inverseImageStalkRingEquiv f x).toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor
            (ModuleCat.{u} (ToType (S.presheaf.stalk (f.base x)))) 0).obj
          (ModuleCat.of (ToType (S.presheaf.stalk (f.base x)))
            (ToType (X.presheaf.stalk x)))) :=
  stalkDerivedScalarRestrictionSingleIso f x (structureModule X.toRingedSpace) ≪≫
    (DerivedCategory.singleFunctor
        (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)).obj x)) 0).mapIso
      (relativeStalkStructureModuleIso f x) ≪≫
    (((ModuleCat.restrictScalars
        (inverseImageStalkRingEquiv f x).toRingHom).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of (ToType (S.presheaf.stalk (f.base x)))
        (ToType (X.presheaf.stalk x)))).symm

/-- The stalk ring of the inverse-image ringed space is commutative, at the point spelling a
point of `X` presents. -/
local instance commRing_stalk_inverseImage :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings.{u}
        (RingedSpace.inverseImage S.toRingedSpace f.base)).obj x)) :=
  RingedSpace.commRing_stalk_structureSheafOfRings _ _

/-- **The coefficient-stalk bridge.** The stalk at `x` of the derived restriction of scalars of
`𝒪_X[0]` along `f^{-1}𝒪_S ⟶ 𝒪_X` has Tor amplitude in `[a, b]` over the stalk `(f^{-1}𝒪_S)_x`
exactly when the local ring `𝒪_{X, x}` has Tor amplitude in `[a, b]` over `𝒪_{S, f x}`.

This is the step that lets the stalkwise criterion of Stacks 09U9 for condition (2) of
Stacks 069C be read as a statement about the local rings of `f`, which is condition (3). The
object is identified by `relativeStalkDerivedIso` and the change of coefficient ring, being along
a ring isomorphism, does not move canonical Tor amplitude. -/
theorem hasTorAmplitudeCanonical_stalk_relative_iff (a b : ℤ) :
    HasTorAmplitudeCanonical
        (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)).obj x))
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u}
              (RingedSpace.inverseImage S.toRingedSpace f.base)) x).mapDerivedCategory.obj
          ((derivedScalarRestriction f).obj
            ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj
              (structureModule X.toRingedSpace)))) a b ↔
      HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base x)))
        ((DerivedCategory.singleFunctor
            (ModuleCat.{u} (ToType (S.presheaf.stalk (f.base x)))) 0).obj
          (ModuleCat.of (ToType (S.presheaf.stalk (f.base x)))
            (ToType (X.presheaf.stalk x)))) a b := by
  rw [hasTorAmplitudeCanonical_iff_of_iso' (relativeStalkDerivedIso f x)]
  exact hasTorAmplitudeCanonical_restrictScalars_ringEquiv_obj_iff
    (inverseImageStalkRingEquiv f x) _ a b

/-! ### The canonical family of certificates is genuine -/

/-- **A genuine family of certificates exists.** The canonical family of
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily` on the opens of the
inverse-image ringed space is pinned to the tensor product of sheaves of modules of Stacks 06YM
on every open subspace: that is what its `tensor` field is, on the nose. -/
theorem isGenuineRelativeTensorFamily_canonical :
    IsGenuineRelativeTensorFamily f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) :=
  fun _ => rfl

/-- **Condition (2) of Stacks 069C is non-vacuous and unambiguous.** Some pinned family of
certificates witnesses it exactly when every pinned family does, the canonical family being one.
-/
theorem forall_locallyHasFiniteRelativeTorDimension_iff_exists :
    (∀ D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
        RingedSpace.CertifiedDerivedSheafTensoring
          ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding),
      IsGenuineRelativeTensorFamily f D → LocallyHasFiniteRelativeTorDimension f D) ↔
      ∃ D : ∀ U : TopologicalSpace.Opens
          (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
          RingedSpace.CertifiedDerivedSheafTensoring
            ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding),
        IsGenuineRelativeTensorFamily f D ∧ LocallyHasFiniteRelativeTorDimension f D :=
  ⟨fun h => ⟨_, isGenuineRelativeTensorFamily_canonical f,
      h _ (isGenuineRelativeTensorFamily_canonical f)⟩,
    forall_locallyHasFiniteRelativeTorDimension_of_exists f⟩

end AlgebraicGeometry.Scheme.Hom

end

