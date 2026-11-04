module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFreeLeftAdjoint
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RestrictFreeIsoTautological
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport

/-!
# The free comparison of a restriction is the free comparison of the inverse image

An open immersion of schemes `g : T ⟶ S` gives two identifications of the free `𝒪_T`-module on
`I` with a functor applied to the free `𝒪_S`-module on `I`:  `Stacks.Modules.restrictFreeIso`
for the restriction functor, and `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso` for the
inverse image.  Restriction and inverse image are identified by Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and this file proves that the two
free identifications **agree** through it.

Both identifications are used in the descent of a trivialised sheaf of modules along a blow-up:
a chart comparison is produced on inverse images, where the pullback of a free module is free,
and consumed on restrictions, where the sheaf is glued, so every statement mixing them goes
through this agreement.

## The route

The restriction functor and the inverse image are *both* left adjoint to the direct image, and
`restrictFunctorIsoPullback` is the comparison
`CategoryTheory.Adjunction.leftAdjointUniq` of those two adjunctions.  Transposing the
comparison across the restriction adjunction therefore turns it into the unit of the
inverse-image adjunction, and the statement at the structure sheaf becomes an identity between
two morphisms `𝒪_S ⟶ g_* 𝒪_T` of sheaves of modules -- one Mathlib's
`SheafOfModules.unitToPushforwardObjUnit`, built from the morphism of sheaves of
rings underlying `g`, the other the unit of the restriction adjunction followed by the
structure-sheaf comparison `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`.  On sections over
an open `U` of `S` that identity is the statement that restricting a section to `g(g⁻¹U)` and
then applying the inverse-image comparison of `g` is applying `g` on sections over `U`, which is
Mathlib's `AlgebraicGeometry.Scheme.Hom.app_appIso_inv` read on the other side of the
comparison.

The passage from the structure sheaf to a free module is
`Stacks.SheafOfModules.pullbackObjFreeIso_hom_eq_mapFreeIso_inv_of_unit`, stated over a general
site: a free sheaf of modules is a coproduct of copies of the structure sheaf, and both
identifications are built from the structure-sheaf one by that coproduct.

## Implementation notes

**The passage from the unit to a free module is made over a general site.**  A goal mentioning a
free module on a scheme is not type-correct at the transparency `rw` and `simp` build motives at,
because `AlgebraicGeometry.Scheme.ringCatSheaf` unfolds to the sheaf of rings
`SheafOfModules` asks for only at default transparency.  The coproduct argument
is therefore carried out once and for all over a general site, where the two spellings do not
arise, and instantiated here by a single `exact`.

**The coproduct-preservation instance is supplied by hand.**  Instance search does not find
`CategoryTheory.Limits.PreservesColimitsOfShape (Discrete I)` for the restriction functor of a
scheme, so it is supplied as `Stacks.Modules.preservesColimitsOfShape_discrete_restrictFunctor`.

## Main results

* `Stacks.Modules.restrictAdjunction_unit_app_unit_comp_map_restrictUnitIso_hom`: the transpose
  of the structure-sheaf comparison of a restriction is Mathlib's
  `SheafOfModules.unitToPushforwardObjUnit`.
* `Stacks.Modules.restrictFunctorIsoPullback_hom_app_unit_comp_pullbackObjUnitToUnit`: **at the
  structure sheaf, the identification of restriction with the inverse image agrees with the two
  structure-sheaf comparisons.**
* `Stacks.Modules.restrictFreeIso_eq`: **the free comparison of a restriction is the free
  comparison of the inverse image**, read through the identification of the two functors, for an
  arbitrary index type.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules (restrictFunctor)

universe u

namespace Stacks.Modules

variable {T S : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g]

/-- **The transpose of the structure-sheaf comparison of a restriction across the restriction
adjunction is Mathlib's `SheafOfModules.unitToPushforwardObjUnit`.**

Each component of `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` is an
`AlgebraicGeometry.Scheme.Hom.appIso` by `rfl` and each component of the unit of the restriction
adjunction is a restriction map of the presheaf, so on sections this is the statement that
restricting a section of `𝒪_S` over `U` to the image of the inverse image of `U` and then
applying the inverse-image comparison of `g` is applying `g` -- which is Mathlib's
`AlgebraicGeometry.Scheme.Hom.app_appIso_inv` read on the other side of the comparison. -/
theorem restrictAdjunction_unit_app_unit_comp_map_restrictUnitIso_hom :
    (Scheme.Modules.restrictAdjunction g).unit.app (SheafOfModules.unit S.ringCatSheaf) ≫
        (Scheme.Modules.pushforward g).map (Scheme.Modules.restrictUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  ext U x
  exact congr($((Iso.eq_comp_inv _).mp (Scheme.Hom.app_appIso_inv g U).symm) x)

/-- **At the structure sheaf, Mathlib's identification of restriction along an open immersion
with the inverse image agrees with the two structure-sheaf comparisons:** the identification,
followed by the comparison of the inverse image of `𝒪_S` with `𝒪_T`, is the comparison of the
restriction of `𝒪_S` with `𝒪_T`.

`restrictFunctorIsoPullback` is the comparison of the restriction adjunction with the
inverse-image adjunction, so
`Stacks.SheafOfModules.leftAdjointUniq_hom_app_unit_comp_pullbackObjUnitToUnit` turns the left
side into the transpose of `SheafOfModules.unitToPushforwardObjUnit`, and
`Stacks.Modules.restrictAdjunction_unit_app_unit_comp_map_restrictUnitIso_hom` says that
transpose is the right side. -/
theorem restrictFunctorIsoPullback_hom_app_unit_comp_pullbackObjUnitToUnit
    [(SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint] :
    (Scheme.Modules.restrictFunctorIsoPullback g).hom.app
          (SheafOfModules.unit S.ringCatSheaf) ≫
        SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom =
      (Scheme.Modules.restrictUnitIso g).hom :=
  have h3 : (Scheme.Modules.restrictAdjunction g).homEquiv
        (SheafOfModules.unit S.ringCatSheaf) (SheafOfModules.unit T.ringCatSheaf)
        (Scheme.Modules.restrictUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    Eq.trans (Adjunction.homEquiv_unit (Scheme.Modules.restrictAdjunction g) _ _ _)
      (restrictAdjunction_unit_app_unit_comp_map_restrictUnitIso_hom g)
  Eq.trans
    (Stacks.SheafOfModules.leftAdjointUniq_hom_app_unit_comp_pullbackObjUnitToUnit
      g.toRingCatSheafHom (Scheme.Modules.restrictAdjunction g))
    ((Equiv.symm_apply_eq _).mpr h3.symm)

/-- **The free comparison of a restriction is the free comparison of the inverse image.**
Identifying the restriction of the free `𝒪_S`-module on `I` with the free `𝒪_T`-module on `I` is
identifying the restriction with the inverse image and then identifying the inverse image of the
free module with the free module.

This is
`Stacks.SheafOfModules.pullbackObjFreeIso_hom_eq_mapFreeIso_inv_of_unit` at the restriction
functor, whose unit compatibility is
`Stacks.Modules.restrictFunctorIsoPullback_hom_app_unit_comp_pullbackObjUnitToUnit`. -/
theorem restrictFreeIso_eq (I : Type u) :
    restrictFreeIso g I =
      (Scheme.Modules.restrictFunctorIsoPullback g).app
          (SheafOfModules.free (R := S.ringCatSheaf) I) ≪≫
        Scheme.Modules.pullbackFreeIso g I :=
  have : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward g).IsRightAdjoint)
  Iso.ext (Stacks.SheafOfModules.pullbackObjFreeIso_hom_eq_mapFreeIso_inv_of_unit
    (hfin := final_of_representablyFlat (Opens.map g.base))
    (hL := preservesColimitsOfShape_discrete_restrictFunctor g I)
    (φ := g.toRingCatSheafHom) (L := restrictFunctor g) I
    (η := (Scheme.Modules.restrictUnitIso g).symm)
    (τ := (Scheme.Modules.restrictFunctorIsoPullback g).hom)
    (hτ := restrictFunctorIsoPullback_hom_app_unit_comp_pullbackObjUnitToUnit g)).symm

end Stacks.Modules

end
