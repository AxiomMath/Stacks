module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomFlat
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackRestrictionSections

/-!
# The canonical map of Stacks 0GMX at a four-field morphism of ringed topoi

`Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap` takes the *two-field* morphism of
ringed topoi of Stacks 01D3 part (2) and reaches the pullback of sheaves of modules through
`AlgebraicGeometry.RingedToposHom.toModulesHom`. Everything it is built from — the pullback of
Stacks 03D6 part (2), the comparison of Stacks 03EL, the evaluation morphism of Stacks 03EO —
needs only the four-field morphism of the modules development that `toModulesHom` produces. This
file exposes the construction at that argument.

A localization at `U` has two presentations as a four-field morphism of ringed topoi: the one
attached to the two-field localization morphism by `toModulesHom`, at which
`Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap` is stated, and
`AlgebraicGeometry.RingedSite.localizationMorphism`, at which the statements about the sections
of the localization are proved. They are equal
(`AlgebraicGeometry.RingedSite.fSharpInverseImage_toModulesHom_localizationRingedToposHom` and
the structure-map identity behind it) but not definitionally equal. Invertibility of the
canonical map is a proposition in the four-field morphism, so it transports along that equality
(`isIso_modulesPullbackInternalHomMap_of_eq`), without identifying the two comparisons of
Stacks 03EL.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.modulesPullbackEvaluation`: the pullback of the evaluation
  morphism, at a four-field morphism of ringed topoi.
* `Stacks.SheafOfModules.InternalHom.modulesPullbackInternalHomMap`: **Stacks 0GMX** at a
  four-field morphism of ringed topoi.

## Main results

* `Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_eq_modulesPullbackInternalHomMap`:
  the canonical map at a two-field morphism is the canonical map at the four-field morphism it
  determines, on the nose.
* `Stacks.SheafOfModules.InternalHom.isIso_modulesPullbackInternalHomMap_of_eq`: invertibility of
  the canonical map transports along an equality of four-field morphisms.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)

namespace Stacks.SheafOfModules.InternalHom

universe u

section FourField

variable {X Y : RingedSite.{u, u, u}}
  (h : Stacks.Sheaves.RingedToposModules.RingedToposHom
    (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))
  (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- The pullback of sheaves of modules of Stacks 03D6 part (2) along a four-field morphism of
ringed topoi between the topoi of two ringed sites.

A plain `def` rather than an `abbrev`: the identity below is `rfl` either way, and a reducible
name for a pullback functor is unfolded by conversion wherever it appears, which is what makes
identities about its image cost the elaborator's whole budget. -/
def modulesPullback :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := RingedSite.ringedTopos X) (Y := RingedSite.ringedTopos Y) h

/-- The pullback of the evaluation morphism of `Hom_{O_Y}(F, G)` along a four-field morphism of
ringed topoi, read as a morphism out of the tensor product of the pullbacks through the
comparison of Stacks 03EL. -/
def modulesPullbackEvaluation :
    ((sheafTensor X.O).obj
          ((modulesPullback h).obj ((internalHomSecondFunctor Y.J Y.O F).obj G))).obj
        ((modulesPullback h).obj F) ⟶
      (modulesPullback h).obj G :=
  (pullbackTensorIso h).inv.app ((internalHomSecondFunctor Y.J Y.O F).obj G, F) ≫
    (modulesPullback h).map (internalHomEvaluation Y.O F G)

/-- **Stacks 0GMX at a four-field morphism of ringed topoi.** The canonical map
`h^* Hom_{O_Y}(F, G) ⟶ Hom_{O_X}(h^*F, h^*G)`: the transpose, under the correspondence of
Stacks 03EO, of the pullback of the evaluation morphism. -/
def modulesPullbackInternalHomMap :
    (modulesPullback h).obj ((internalHomSecondFunctor Y.J Y.O F).obj G) ⟶
      (internalHomSecondFunctor X.J X.O ((modulesPullback h).obj F)).obj
        ((modulesPullback h).obj G) :=
  sheafTensorHomEquiv X.O
    ((modulesPullback h).obj ((internalHomSecondFunctor Y.J Y.O F).obj G))
    ((modulesPullback h).obj F) ((modulesPullback h).obj G) (modulesPullbackEvaluation h F G)

/-- Evaluation of the canonical map recovers its defining pulled-back evaluation. -/
theorem tensorEvaluation_modulesPullbackInternalHomMap :
    tensorEvaluation X.O ((modulesPullback h).obj F) ((modulesPullback h).obj G)
      (modulesPullbackInternalHomMap h F G) = modulesPullbackEvaluation h F G :=
  (tensorEvaluation_eq X.O ((modulesPullback h).obj F) ((modulesPullback h).obj G)
    (modulesPullbackInternalHomMap h F G)).trans
      ((sheafTensorHomEquiv X.O
        ((modulesPullback h).obj ((internalHomSecondFunctor Y.J Y.O F).obj G))
        ((modulesPullback h).obj F) ((modulesPullback h).obj G)).symm_apply_apply
          (modulesPullbackEvaluation h F G))

/-- **Invertibility of the canonical map of Stacks 0GMX transports along an equality of
four-field morphisms of ringed topoi.** For a localization this passes between the
presentation `AlgebraicGeometry.RingedToposHom.toModulesHom` produces and
`AlgebraicGeometry.RingedSite.localizationMorphism`. -/
theorem isIso_modulesPullbackInternalHomMap_of_eq
    {h' : Stacks.Sheaves.RingedToposModules.RingedToposHom
      (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y)}
    (e : h = h') (hiso : IsIso (modulesPullbackInternalHomMap h' F G)) :
    IsIso (modulesPullbackInternalHomMap h F G) :=
  Eq.mpr (congrArg (fun k ↦ IsIso (modulesPullbackInternalHomMap k F G)) e) hiso

end FourField

section TwoField

variable {X Y : RingedSite.{u, u, u}}
  (φ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))
  (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- The pullback of the evaluation morphism along a two-field morphism of ringed topoi is the
one along the four-field morphism it determines. -/
theorem toposPullbackEvaluation_eq_modulesPullbackEvaluation :
    toposPullbackEvaluation φ F G = modulesPullbackEvaluation φ.toModulesHom F G :=
  rfl

/-- **The canonical map of Stacks 0GMX at a two-field morphism of ringed topoi is the canonical
map at the four-field morphism it determines**, on the nose: the two-field construction reaches
the pullback of sheaves of modules through
`AlgebraicGeometry.RingedToposHom.toModulesHom` and through nothing else. -/
theorem toposPullbackInternalHomMap_eq_modulesPullbackInternalHomMap :
    toposPullbackInternalHomMap φ F G = modulesPullbackInternalHomMap φ.toModulesHom F G :=
  rfl

/-- At the morphism of ringed topoi of a morphism of ringed sites, the canonical map at the
four-field morphism is the canonical map of Stacks 0GMX. -/
theorem modulesPullbackInternalHomMap_ringedToposHom (f : RingedSite.Hom X Y) :
    modulesPullbackInternalHomMap f.ringedToposHom.toModulesHom F G =
      pullbackInternalHomMap f F G :=
  rfl

end TwoField

end Stacks.SheafOfModules.InternalHom

end
