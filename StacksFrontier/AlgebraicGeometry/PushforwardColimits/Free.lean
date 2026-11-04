module

public import StacksFrontier.AlgebraicGeometry.PushforwardColimits.Basic
public import StacksFrontier.AlgebraicGeometry.QcohOverAlgebra.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.QcohUnitCounit.Basic

/-!
# The direct image over `f_* 𝒪_X` commutes with coproducts, and carries free modules to free
modules

Let `f : X ⟶ S` be an affine morphism of schemes and `A = f_* 𝒪_X`.  The direct image of
`𝒪_X`-modules regarded as a functor to `A`-modules, namely
`Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardModules f.base X.ringCatSheaf`, is the
functor whose restriction to quasi-coherent modules the equivalence assertion of Stacks Tag 01SB
is about.  This file transfers
`Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforward_of_isAffineHom` from
the direct image of `𝒪_X`-modules to it, and records the consequence at free modules: the direct
image of the free `𝒪_X`-module on a type `I` is the free `A`-module on `I`.

## Main definitions

* `Stacks.AlgebraicGeometry.PushforwardColimits.pushforwardModulesFreeIso`: the direct image
  along an affine morphism carries `SheafOfModules.free I` to `SheafOfModules.free I`.

## Main results

* `Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforwardModules`: **the
  direct image over `f_* 𝒪_X` along an affine morphism preserves colimits of quasi-coherent
  modules**; in particular, by
  `Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforwardModules_unit`, the
  coproduct of an arbitrary family of copies of the structure sheaf.

## Implementation notes

Restriction of scalars along `f.toRingCatSheafHom` turns the direct image over `f_* 𝒪_X` into the
direct image of `𝒪_X`-modules, *on the nose*, which is
`Stacks.AlgebraicGeometry.AffineQcohPushforward.restrictScalars_pushforwardModules`.  Restriction
of scalars preserves colimits by
`Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesColimitsOfShape_restrictScalars` and
reflects them by
`Stacks.AlgebraicGeometry.QcohOverAlgebra.reflectsColimitsOfShape_restrictScalars`; so
`CategoryTheory.Limits.preservesColimit_of_reflects_of_preserves` transfers the statement.

The isomorphism at free modules is the construction of `SheafOfModules.mapFreeIso` written out:
that lemma asks for preservation of *all* coproducts indexed by `I`, which is not available here
— the direct image preserves the coproduct of a family of *quasi-coherent* modules — whereas its
proof only uses preservation of the one coproduct of copies of the structure sheaf, which is.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe v₂ u₂ u

noncomputable section

namespace Stacks.AlgebraicGeometry.PushforwardColimits

open Stacks.AlgebraicGeometry.AffineQcohPushforward

/-! ### The direct image over `f_* 𝒪_X` -/

variable {K : Type u₂} [Category.{v₂} K] [HasColimitsOfShape K AddCommGrpCat.{u}]
  [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
  [∀ W : Scheme.{u}, HasColimitsOfShape K W.Modules]

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The direct image over `f_* 𝒪_X` along an affine morphism preserves colimits of
quasi-coherent modules.**  Restriction of scalars along `f.toRingCatSheafHom` turns it into the
direct image of `𝒪_X`-modules, and restriction of scalars reflects colimits. -/
theorem preservesColimit_pushforwardModules [IsAffineHom f]
    [HasColimitsOfShape K (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))]
    {D : K ⥤ SheafOfModules.{u} X.ringCatSheaf} (hD : ∀ k, (D.obj k).IsQuasicoherent) :
    PreservesColimit D (pushforwardModules.{u} f.base X.ringCatSheaf) := by
  have _h1 : PreservesColimit D (pushforwardModules.{u} f.base X.ringCatSheaf ⋙
      SheafOfModules.restrictScalars f.toRingCatSheafHom) :=
    preservesColimit_pushforward_of_isAffineHom f hD
  have _h2 : ReflectsColimit (D ⋙ pushforwardModules.{u} f.base X.ringCatSheaf)
      (SheafOfModules.restrictScalars f.toRingCatSheafHom) :=
    (QcohOverAlgebra.reflectsColimitsOfShape_restrictScalars.{v₂, u₂}
      f.toRingCatSheafHom K).reflectsColimit
  exact preservesColimit_of_reflects_of_preserves (pushforwardModules.{u} f.base X.ringCatSheaf)
    (SheafOfModules.restrictScalars f.toRingCatSheafHom)

/-- **The direct image over `f_* 𝒪_X` along an affine morphism preserves the coproduct of an
arbitrary family of copies of the structure sheaf.**  This is the instance of
`preservesColimit_pushforwardModules` that the equivalence assertion of Stacks Tag 01SB needs:
the structure sheaf is quasi-coherent, and no finiteness is assumed on the index type. -/
theorem preservesColimit_pushforwardModules_unit [IsAffineHom f] (I : Type u) :
    PreservesColimit (Discrete.functor fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf)
      (pushforwardModules.{u} f.base X.ringCatSheaf) :=
  preservesColimit_pushforwardModules f fun _ ↦ isQuasicoherent_unit X

/-- **The direct image along an affine morphism carries the free `𝒪_X`-module on a type to the
free `f_* 𝒪_X`-module on that type.**  This is `SheafOfModules.mapFreeIso` for the direct image,
whose hypothesis of preservation of all coproducts indexed by `I` is replaced by the one
instance of it supplied by `preservesColimit_pushforwardModules_unit`.  The comparison map at
the structure sheaf is the identity, by
`Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardModules_unit`. -/
def pushforwardModulesFreeIso [IsAffineHom f] (I : Type u) :
    SheafOfModules.free.{u} (R := pushforwardRing f.base X.ringCatSheaf) I ≅
      (pushforwardModules.{u} f.base X.ringCatSheaf).obj (SheafOfModules.free.{u} I) :=
  have := preservesColimit_pushforwardModules_unit f I
  (SheafOfModules.isColimitFreeCofan I).coconePointsIsoOfNatIso
    (isColimitOfPreserves (pushforwardModules.{u} f.base X.ringCatSheaf)
      (SheafOfModules.isColimitFreeCofan I))
    (Discrete.natIso fun _ ↦ eqToIso (pushforwardModules_unit f).symm)

end Stacks.AlgebraicGeometry.PushforwardColimits

end

end
