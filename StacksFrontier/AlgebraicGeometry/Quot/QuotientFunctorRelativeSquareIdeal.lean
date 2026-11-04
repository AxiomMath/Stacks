module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorRelativeSquare
public import StacksFrontier.Deformation.ToposThickening.RelativeBaseIdeal
public import StacksFrontier.Deformation.ToposThickening.IdealProductTensorIso
public import StacksFrontier.Deformation.ToposThickening.QuotientLiftObstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleFirstOrderThickeningIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorQuasicoherentOnSite

/-!
# The ideal of the test scheme, read through the relative square

In the relative square of `AlgebraicGeometry.Space.QuotientSituation.relativeSquare_comm`, the
first order thickening `T ⊂ T'` with ideal `𝒥` is replaced by the thickening `t̃` of
`(X_{T'}, f'⁻¹O_{T'})`, and the module `f_T^*𝒥` of Remark 0CZU is replaced by
`Deformation.ToposThickening.basePullbackIdeal` of the relative square. This file identifies the
two: the module `f̃^*t̃^*𝒥̃` of the relative square is `p^*t^*𝒥 = f_T^*𝒥`, where `p : X_T ⟶ T` and
`t^*𝒥` is `𝒥` read as an `𝒪_T`-module. In particular it is quasi-coherent, and so is
`𝒬 ⊗_{𝒪_T} 𝒥 = 𝒬 ⊗ f_T^*𝒥` for every quasi-coherent `𝒪_{X_T}`-module `𝒬`.

## Main definitions

* `AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso`: the
  identification `f̃^*t̃^*𝒥̃ ≅ f_T^*𝒥`.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.isQuasicoherentOnSite_basePullbackIdeal`: `f_T^*𝒥`
  is quasi-coherent.
* `AlgebraicGeometry.Space.QuotientSituation.isQuasicoherentOnSite_baseIdealTensor_relativeSquare`:
  `𝒬 ⊗ f_T^*𝒥` is quasi-coherent for quasi-coherent `𝒬`.

## References

* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

universe u

namespace AlgebraicGeometry.Space.QuotientSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotientSituation B S hS) {T T' : SchemesOver D.Y} (h : T ⟶ T')
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

/-- The small étale site of `X_{T'}`, read as the site of the base `(X_{T'}, f'⁻¹t_*𝒪_T)` of the
relative square, has sheaf composition with the forgetful functor of abelian groups. -/
instance (priority := 10000) relBaseBottom_hasSheafCompose_forget :
    (relBaseBottom (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
      (smallEtaleRingedToposHom B S hS (D.projection T'))).J.HasSheafCompose
        (forget AddCommGrpCat.{u}) :=
  inferInstanceAs ((SmallEtale.topology B S hS (D.space T').1).HasSheafCompose
    (forget AddCommGrpCat.{u}))

/-- Sheafification of abelian presheaves on the small étale site of `X_{T'}`, read as the site of
the base of the relative square. -/
instance (priority := 10000) relBaseBottom_hasWeakSheafify :
    HasWeakSheafify (relBaseBottom
      (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
      (smallEtaleRingedToposHom B S hS (D.projection T'))).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS (D.space T').1) AddCommGrpCat.{u})

/-- Local bijectivity of the weak equivalences of abelian presheaves on the small étale site of
`X_{T'}`, read as the site of the base of the relative square. -/
instance (priority := 10000) relBaseBottom_wEqualsLocallyBijective :
    (relBaseBottom (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
      (smallEtaleRingedToposHom B S hS (D.projection T'))).J.WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
  inferInstanceAs ((SmallEtale.topology B S hS (D.space T').1).WEqualsLocallyBijective
    AddCommGrpCat.{u})

/-- **`f_T^*𝒥` read through the relative square**: the module
`Deformation.ToposThickening.basePullbackIdeal` of the relative square, `f̃^*t̃^*𝒥̃`. -/
abbrev relativeSquareBasePullbackIdeal :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.space T)).O) :=
  basePullbackIdeal.{u, u + 1, u, u, u + 1, u, u, u + 1, u} (D.relativeSquareThickening h)
    (D.relativeSquareLeft h) (D.relativeSquareThickeningFirstOrderThickening h hh)

/-- **`f_T^*𝒥`**: the ideal `𝒥` of `T ⊂ T'`, read as an `𝒪_T`-module `t^*𝒥`, pulled back along
`X_T ⟶ T` (`Deformation.ToposThickening.basePullbackIdeal` of the square of test schemes). -/
abbrev testSchemeBasePullbackIdeal :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.space T)).O) :=
  basePullbackIdeal.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
    (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
    (smallEtaleRingedToposHom B S hS (D.projection T)) (D.testSchemeFirstOrderThickening h hh)

/-- **`f̃^*t̃^*𝒥̃ ≅ f_T^*𝒥`.** The pulled-back ideal of the relative square is the pullback
`p^*t^*𝒥` of the ideal `𝒥` of `T ⊂ T'` along `X_T ⟶ T`: around the strictly commuting relative
square it is `i^*f̃'^*𝒥̃` (`Deformation.ToposThickening.basePullbackIdealIsoPullback`), then
`f̃'^*𝒥̃ ≅ f'^*𝒥` (`Deformation.ToposThickening.relBasePullbackIdealIso`), and the comparison of
Stacks 03LU for the square `X_T ⟶ X_{T'} ⟶ T'`, `X_T ⟶ T ⟶ T'` identifies `i^*f'^*𝒥` with
`p^*t^*𝒥`. -/
def relativeSquareBasePullbackIdealIso :
    D.relativeSquareBasePullbackIdeal h hh ≅ D.testSchemeBasePullbackIdeal h hh :=
  haveI := D.relBaseBottom_hasSheafCompose_forget h
  basePullbackIdealIsoPullback.{u, u + 1, u, u, u + 1, u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS (D.relativeMap h))
      (D.relativeSquareThickening h) (D.relativeSquareLeft h)
      (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
      (D.relativeMapFirstOrderThickening h hh) (D.relativeSquareThickeningFirstOrderThickening h hh)
      (D.relativeSquare_comm h) ≪≫
    (pullbackModules
        (smallEtaleRingedToposHom B S hS (D.relativeMap h)).toRingedToposModulesHom).mapIso
      (eqToIso (congrArg (fun φ : Stacks.Sheaves.RingedToposModules.RingedToposHom
          (smallEtaleRingedTopos B S hS (D.space T'))
          (relBaseTop (smallEtaleRingedToposHom B S hS (D.projection T'))) =>
        (pullbackModules φ).obj
          (D.relativeSquareThickeningFirstOrderThickening h hh).idealOfThickening.I)
        (relBaseRight (smallEtaleRingedToposHom B S hS
          (D.projection T'))).toModulesHom_eq_toRingedToposModulesHom)) ≪≫
    (pullbackModules
        (smallEtaleRingedToposHom B S hS (D.relativeMap h)).toRingedToposModulesHom).mapIso
      (relBasePullbackIdealIso
        (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
        (smallEtaleRingedToposHom B S hS (D.projection T'))
        (D.testSchemeFirstOrderThickening h hh)) ≪≫
    (modulePullbackSquare B S hS (D.relativeMap_comp_projection h) rfl).app
      (D.testSchemeFirstOrderThickening h hh).idealOfThickening.I

include hh in
/-- **`f_T^*𝒥` is quasi-coherent**: `𝒥` is the defining ideal sheaf of `T` in `T'`, which is
quasi-coherent (Stacks 03MB), and pullbacks of quasi-coherent modules are quasi-coherent
(Stacks 03GA). -/
theorem isQuasicoherentOnSite_basePullbackIdeal :
    (D.testSchemeBasePullbackIdeal h hh).IsQuasicoherentOnSite := by
  have : Mono ((schemeSpaceFunctor B S hS).map h.left).hom :=
    mono_yoneda_map_of_isClosedImmersion h.left hh.1
  exact isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (D.projection T) _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      ((schemeSpaceFunctor B S hS).map h.left) _
      (isQuasicoherentOnSite_smallEtaleThickeningIdeal B S hS
        ((schemeSpaceFunctor B S hS).map h.left) inferInstance
        (isFirstOrderThickening_range_yoneda_map B S hS h.left hh)))

include hh in
/-- **`f̃^*t̃^*𝒥̃` is quasi-coherent**, being isomorphic to `f_T^*𝒥`. -/
theorem isQuasicoherentOnSite_relativeSquareBasePullbackIdeal :
    (D.relativeSquareBasePullbackIdeal h hh).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (D.relativeSquareBasePullbackIdealIso h hh).symm
    (D.isQuasicoherentOnSite_basePullbackIdeal h hh)

include hh in
/-- **`𝒬 ⊗_{𝒪_T} 𝒥 = 𝒬 ⊗ f_T^*𝒥` is quasi-coherent** for a quasi-coherent `𝒪_{X_T}`-module `𝒬`,
in the presentation of the relative square: the tensor product of two quasi-coherent modules
is quasi-coherent (Stacks 03L6). -/
theorem isQuasicoherentOnSite_baseIdealTensor_relativeSquare
    (Q : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) [Q.IsQuasicoherentOnSite] :
    haveI := D.relBaseBottom_hasSheafCompose_forget h
    haveI := D.relBaseBottom_hasWeakSheafify h
    haveI := D.relBaseBottom_wEqualsLocallyBijective h
    ((baseIdealTensor.{u, u + 1, u, u, u + 1, u, u, u + 1, u} (D.relativeSquareThickening h)
      (D.relativeSquareLeft h)
        (D.relativeSquareThickeningFirstOrderThickening h hh)).obj Q).IsQuasicoherentOnSite :=
  @Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite _ _
    (smallEtaleRingedTopos B S hS (D.space T)).J _ _ _ (smallEtaleRingedTopos B S hS (D.space T)).O
    Q (D.relativeSquareBasePullbackIdeal h hh) ‹Q.IsQuasicoherentOnSite›
    (D.isQuasicoherentOnSite_relativeSquareBasePullbackIdeal h hh)

end AlgebraicGeometry.Space.QuotientSituation

end
