module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.Relocalization

/-!
# Pullback along the relocalization of a ringed site is restriction along `Over.map`

Let `(C, O)` be a ringed site and `f : V ⟶ U` a morphism of `C`. Pulling a sheaf of `O|_U`-modules
back along the relocalization morphism of ringed topoi `j : (Sh(C/V), O|_V) ⟶ (Sh(C/U), O|_U)` of
Stacks 04IY is the same thing as restricting it along `Over.map f`, i.e. Mathlib's
`SheafOfModules.overMap`.

The proof has two halves. The inverse-image half is
`Stacks.Sheaves.ToposPullback.restrictionModuleIso`: the inverse image along the morphism of topoi
induced by a continuous functor *is* restriction along that functor, the two differing only by the
transport of the module structure along a sections functor. The extension-of-scalars half is
`Stacks.Sheaves.RingedToposModules.RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso`:
the structure map of the relocalization is an isomorphism of sheaves of rings, so extension of
scalars along it is restriction of scalars along its inverse.

## Main results

* `AlgebraicGeometry.RingedSite.relocalizationPullbackIsoOverMap`: pullback of sheaves of modules
  along the relocalization morphism at `f : V ⟶ U` is `SheafOfModules.overMap`.

## Implementation notes

The structure map of the relocalization is the comparison of the inverse image of `O|_U` with its
restriction along `Over.map f`, followed by the change-of-slice identification of that restriction
with `O|_V`. Only the first factor is undone by the inverse-image half, so the second survives as a
restriction of scalars along an isomorphism, and that is exactly the structure map carried by
`SheafOfModules.overMap`.

The ring sheaf of the localized ringed site and the restriction of the ring sheaf of `(C, O)` --
`(X.over U).ringSheaf` and `X.ringSheaf.over U` -- are the same sheaf of rings by definition but
not after the reductions `rw` and instance search perform, so the two spellings cannot be mixed
inside a rewrite. Everything below is therefore assembled in term mode out of `Iso.trans`,
whiskering and one `eqToIso`, whose only input is the morphism equality
`inv_fSharpInverseImage_comp_restrictionRingIso_hom`;
`Stacks.Sheaves.RingedToposModules.restrictScalars_comp` is
stated separately so that a composite of two restrictions of scalars is matched syntactically
rather than by an expensive unfolding of `SheafOfModules.restrictScalars`.

## References

* [Stacks Project, Tag 04IY](https://stacks.math.columbia.edu/tag/04IY)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u v u₁ v₁ w₁

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v}) {U V : X.C} (f : V ⟶ U)

/-- The structure map of the relocalization along `f : V ⟶ U`, in inverse-image form, is the
comparison of the inverse image of `O|_U` with its restriction along `Over.map f`, followed by the
change-of-slice identification of that restriction with `O|_V`. -/
public theorem restrictionRingIso_hom_comp_pushforwardOverMapIso_hom :
    (restrictionRingIso (X.J.over V) (X.J.over U) (Over.map f)
          (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).hom ≫
        (Sheaf.pushforwardOverMapIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).hom =
      (X.relocalizationMorphism f).fSharpInverseImage :=
  rfl

/-- The structure map of the relocalization is an isomorphism of sheaves of rings, both of its two
factors being comparison isomorphisms. -/
public instance isIso_fSharpInverseImage_relocalizationMorphism :
    IsIso (X.relocalizationMorphism f).fSharpInverseImage :=
  (X.overMapInverseImageRingIso f).isIso_hom

/-- Undoing the relocalization structure map and then applying the comparison of the inverse image
of `O|_U` with its restriction along `Over.map f` leaves the inverse of the change-of-slice
identification of that restriction with `O|_V`. -/
public theorem inv_fSharpInverseImage_comp_restrictionRingIso_hom :
    (asIso (X.relocalizationMorphism f).fSharpInverseImage).inv ≫
        (restrictionRingIso (X.J.over V) (X.J.over U) (Over.map f)
          (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).hom =
      (Sheaf.pushforwardOverMapIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).inv :=
  (IsIso.inv_comp_eq _).mpr
    ((Iso.eq_comp_inv _).mpr (X.restrictionRingIso_hom_comp_pushforwardOverMapIso_hom f))

/-- Restriction of scalars along the comparison of the inverse image of `O|_U` with its
restriction along `Over.map f`, followed by restriction of scalars along the inverse of the
relocalization structure map, is restriction of scalars along the inverse of the change-of-slice
identification. -/
public theorem restrictScalars_comp_restrictScalars_inv_fSharpInverseImage :
    SheafOfModules.restrictScalars.{max u v}
          (restrictionRingIso (X.J.over V) (X.J.over U) (Over.map f)
            (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).hom ⋙
        SheafOfModules.restrictScalars.{max u v}
          (asIso (X.relocalizationMorphism f).fSharpInverseImage).inv =
      SheafOfModules.restrictScalars.{max u v}
        (Sheaf.pushforwardOverMapIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).inv :=
  (restrictScalars_comp _ _).trans
    (congrArg SheafOfModules.restrictScalars
      (X.inv_fSharpInverseImage_comp_restrictionRingIso_hom f))

variable [HasWeakSheafify (X.J.over V) AddCommGrpCat.{max u v}]
  [(X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Extension of scalars along the relocalization structure map undoes the restriction of scalars
along the comparison of the inverse image of `O|_U` with its restriction along `Over.map f`,
leaving restriction of scalars along the inverse of the change-of-slice identification. -/
public def restrictScalarsCompExtendScalarsFSharpIso :
    SheafOfModules.restrictScalars
          (restrictionRingIso (X.J.over V) (X.J.over U) (Over.map f)
            (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).hom ⋙
        extendScalarsFSharp (X.relocalizationMorphism f) ≅
      SheafOfModules.restrictScalars
        (Sheaf.pushforwardOverMapIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).inv :=
  Functor.isoWhiskerLeft
      (SheafOfModules.restrictScalars
        (restrictionRingIso (X.J.over V) (X.J.over U) (Over.map f)
          (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).hom)
      (X.relocalizationMorphism f).extendScalarsFSharpIsoRestrictScalarsOfIsIso ≪≫
    eqToIso (X.restrictScalars_comp_restrictScalars_inv_fSharpInverseImage f)

/-- Restriction of sheaves of modules along `Over.map f`, followed by restriction of scalars along
the change-of-slice identification of the restriction of `O|_U` with `O|_V`, is
`SheafOfModules.overMap`: the two functors agree by definition. -/
public def restrictionModulesCompRestrictScalarsIsoOverMap :
    restrictionModules (X.J.over V) (X.J.over U) (Over.map f)
          (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) ⋙
        SheafOfModules.restrictScalars
          (Sheaf.pushforwardOverMapIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).inv ≅
      SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f :=
  Iso.refl _

/-- **Stacks 04IY.** Pullback of sheaves of modules along the relocalization morphism of ringed
topoi attached to a morphism `f : V ⟶ U` of a ringed site is restriction along `Over.map f`, that
is, `SheafOfModules.overMap`. -/
public def relocalizationPullbackIsoOverMap :
    (X.relocalizationMorphism f).pullbackModules ≅
      SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f :=
  Functor.isoWhiskerRight
      (restrictionModuleIso (X.J.over V) (X.J.over U) (Over.map f)
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))
      (extendScalarsFSharp (X.relocalizationMorphism f)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (restrictionModules (X.J.over V) (X.J.over U) (Over.map f)
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))
      (X.restrictScalarsCompExtendScalarsFSharpIso f) ≪≫
    X.restrictionModulesCompRestrictScalarsIsoOverMap f

end AlgebraicGeometry.RingedSite

end
