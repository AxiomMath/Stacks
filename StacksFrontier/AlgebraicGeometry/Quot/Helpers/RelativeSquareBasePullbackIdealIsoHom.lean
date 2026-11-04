module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealSquare

/-!
# The components of `f̃^*t̃^*𝒥̃ ≅ f_T^*𝒥`

`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso_eq_trans` writes
`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso` as the composite of
its four pieces: `Deformation.ToposThickening.basePullbackIdealIsoPullback`, the identification of
the two spellings of `f̃'^*𝒥̃`
(`AlgebraicGeometry.Space.QuotientSituation.relBaseRight_pullbackIdeal_eq`), the pullback of
`Deformation.ToposThickening.relBasePullbackIdealIso`, and the comparison
`AlgebraicGeometry.Space.modulePullbackSquare` of Stacks 03LU. The first and third pieces are named
(`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIsoPullback`,
`AlgebraicGeometry.Space.QuotientSituation.relativeSquareRelBasePullbackIdealIso`), so that their
instance arguments are found once and not at each use. It is an equation of isomorphisms,
proved once in the instance context of the definition, so that its uses rewrite with it instead of
unfolding the definition; `CategoryTheory.Iso.trans_mapIso_trans_mapIso_trans_hom` reads off the
maps over arbitrary categories. Used in the functoriality of the obstruction classes of
`Coh_{X/B}` (second proof of Stacks 08WA).

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

universe u

namespace CategoryTheory

/-- The map of `a ≪≫ P(e) ≪≫ P(ρ) ≪≫ s` is `a ≫ P(e) ≫ P(ρ) ≫ s`, with the intermediate objects
those of `a`, `e`, `ρ` and `s`. -/
theorem Iso.trans_mapIso_trans_mapIso_trans_hom {C D : Type*} [Category* C] [Category* D]
    (P : C ⥤ D) {Q W : D} {X Y Z : C} (a : Q ≅ P.obj X) (e : X ≅ Y) (ρ : Y ≅ Z)
    (s : P.obj Z ≅ W) :
    (a ≪≫ P.mapIso e ≪≫ P.mapIso ρ ≪≫ s).hom = a.hom ≫ P.map e.hom ≫ P.map ρ.hom ≫ s.hom :=
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Space.QuotientSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotientSituation B S hS) {T T' : SchemesOver D.Y} (h : T ⟶ T')
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

/-- `f̃'^*𝒥̃ ≅ f'^*𝒥` for the relative square of `h : T ⟶ T'`:
`Deformation.ToposThickening.relBasePullbackIdealIso` at `X_{T'} ⟶ T'` and the ideal of `T ⊂ T'`,
the third isomorphism of `relativeSquareBasePullbackIdealIso`.
Named so that its instance arguments are found once. -/
def relativeSquareRelBasePullbackIdealIso :=
  relBasePullbackIdealIso
    (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
    (smallEtaleRingedToposHom B S hS (D.projection T')) (D.testSchemeFirstOrderThickening h hh)

/-- `f̃^*t̃^*𝒥̃ ≅ i^*f̃'^*𝒥̃` for the relative square of `h : T ⟶ T'`:
`Deformation.ToposThickening.basePullbackIdealIsoPullback` at the relative square, the first
isomorphism of `relativeSquareBasePullbackIdealIso`.
Named so that its instance arguments are found once. -/
def relativeSquareBasePullbackIdealIsoPullback :=
  basePullbackIdealIsoPullback (smallEtaleRingedToposHom B S hS (D.relativeMap h))
    (D.relativeSquareThickening h) (D.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
    (D.relativeMapFirstOrderThickening h hh) (D.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquare_comm h)

/-- **`f̃^*t̃^*𝒥̃ ≅ f_T^*𝒥` as a composite of four isomorphisms**: the inverse image along the
relative square (`relativeSquareBasePullbackIdealIsoPullback`), the identification of the two
spellings of `f̃'^*𝒥̃` (`relBaseRight_pullbackIdeal_eq`), the pullback of `f̃'^*𝒥̃ ≅ f'^*𝒥`
(`relativeSquareRelBasePullbackIdealIso`) and the comparison of Stacks 03LU for the square
`X_T ⟶ X_{T'} ⟶ T'`, `X_T ⟶ T ⟶ T'`. Stated as an equation of isomorphisms: the corresponding
equation of the maps, with the composite written with `≫`, makes the kernel compare two spellings
of the intermediate objects under reducible heads. -/
theorem relativeSquareBasePullbackIdealIso_eq_trans :
    D.relativeSquareBasePullbackIdealIso h hh =
      D.relativeSquareBasePullbackIdealIsoPullback h hh ≪≫
        (pullbackModules
          (smallEtaleRingedToposHom B S hS (D.relativeMap h)).toRingedToposModulesHom).mapIso
          (eqToIso (D.relBaseRight_pullbackIdeal_eq h hh)) ≪≫
        (pullbackModules
          (smallEtaleRingedToposHom B S hS (D.relativeMap h)).toRingedToposModulesHom).mapIso
          (D.relativeSquareRelBasePullbackIdealIso h hh) ≪≫
        (modulePullbackSquare B S hS (D.relativeMap_comp_projection h) rfl).app
          (D.testSchemeFirstOrderThickening h hh).idealOfThickening.I :=
  rfl

end AlgebraicGeometry.Space.QuotientSituation

end
