module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.DerivedProperDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.UnboundedTorsionBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Proper direct images commute with the comparison of big and small étale sites (Stacks 0DDJ)

Let `B` be a big étale site and `f : T ⟶ S` a proper morphism of it. Write `π_S⁻¹` for the
extension of sheaves from the small étale site of `S` to the big étale site over `S`. This file
proves Stacks 0DDJ:

1. `π_S⁻¹ ∘ f_{small,*} = f_{big,*} ∘ π_T⁻¹` on sheaves of sets;
2. `π_S⁻¹ Rf_{small,*} K = Rf_{big,*} π_T⁻¹ K` for `K` in `D^+(T_étale)` with torsion cohomology
   sheaves;
3. `π_S⁻¹ Rf_{small,*} K = Rf_{big,*} π_T⁻¹ K` for `K` in `D(T_étale, ℤ/nℤ)`;
4. `π_S⁻¹ Rf_{small,*} K = Rf_{big,*} π_T⁻¹ K` for all `K` in `D(T_étale)` if `f` is finite.

In each case the identification is the canonical base change map:
`AlgebraicGeometry.bigSmallEtaleBaseChange` for (1) and its derived map
`AlgebraicGeometry.bigSmallEtaleDerivedBaseChange` for (2)–(4). The derived functors
`Rf_{small,*}` and `Rf_{big,*}` are any right derived functors of the direct images on the
unbounded derived categories, in the standard model of the derived categories, and in part (3)
the integer `n` is positive.

## Main results

* `AlgebraicGeometry.isIso_bigSmallEtaleBaseChange_of_isProper` — **Stacks 0DDJ (1)**.
* `AlgebraicGeometry.isIso_bigSmallEtaleDerivedBaseChange_app_of_isProper` — **Stacks 0DDJ (2)**.
* `AlgebraicGeometry.isIso_bigSmallEtaleDerivedBaseChange_app_toSheaf_of_isProper_zmod` —
  **Stacks 0DDJ (3)**.
* `AlgebraicGeometry.isIso_bigSmallEtaleDerivedBaseChange_of_isFinite` — **Stacks 0DDJ (4)**.

## References

* [Stacks Project, Tag 0DDJ](https://stacks.math.columbia.edu/tag/0DDJ)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 0F0C](https://stacks.math.columbia.edu/tag/0F0C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Stacks.Cohomology.ZModSheaf (zmodRingSheaf)

universe u

namespace AlgebraicGeometry

-- The site-modules `Abelian` instance is stated in a `max` universe; on the `ℤ/nℤ`-module sheaves
-- of the small étale site it leaves a universe metavariable unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigEtaleSite.{u}) {T S : B.Scheme} (f : T ⟶ S)

/-- **Stacks 0DDJ (1).** Let `f : T ⟶ S` be a proper morphism of a big étale site. Then
`π_S⁻¹ ∘ f_{small,*} = f_{big,*} ∘ π_T⁻¹` as functors from sheaves of sets on `T_étale` to sheaves
of sets on `(Sch/S)_étale`: the canonical base change map
`AlgebraicGeometry.bigSmallEtaleBaseChange` is an isomorphism. -/
@[stacks 0DDJ "(1)"]
public theorem isIso_bigSmallEtaleBaseChange_of_isProper [IsProper (B.inclusion.map f)] :
    IsIso (bigSmallEtaleBaseChange B (Type (u + 1)) f (bigEtaleProjectionAdjunction B T)
      (bigEtaleProjectionAdjunction B S)) :=
  isIso_bigSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange B f
    fun _ _ g g' f' sq ↦
      Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper _ g g' f' sq

add_to_stacks 0DDJ "(4)" AlgebraicGeometry.isIso_bigSmallEtaleDerivedBaseChange_of_isFinite

section Derived

attribute [local instance] HasDerivedCategory.standard smallEtaleSheaf_isGrothendieckAbelian
  bigEtaleSheaf_isGrothendieckAbelian

variable
  (RfSmall : DerivedCategory (Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1})
    ⥤ DerivedCategory (Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}))
  (RfBig :
    DerivedCategory (Sheaf (BigEtaleOver.topology B T.obj T.property) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (BigEtaleOver.topology B S.obj S.property) AddCommGrpCat.{u + 1}))
  (αSmall : (B.smallPushforward f AddCommGrpCat.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RfSmall)
  (αBig : ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigEtaleOver.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RfBig)
  [RfSmall.IsRightDerivedFunctor αSmall (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
  [RfBig.IsRightDerivedFunctor αBig (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]

/-- **Stacks 0DDJ (2).** Let `f : T ⟶ S` be a proper morphism of a big étale site. Then
`π_S⁻¹ Rf_{small,*} K = Rf_{big,*} π_T⁻¹ K` for every `K` in `D^+(T_étale)` whose cohomology
sheaves are torsion: the canonical base change map
`AlgebraicGeometry.bigSmallEtaleDerivedBaseChange` is invertible at `K`. Here `Rf_{small,*}` and
`Rf_{big,*}` are any right derived functors of the direct images of abelian sheaves along `f`. -/
@[stacks 0DDJ "(2)"]
public theorem isIso_bigSmallEtaleDerivedBaseChange_app_of_isProper
    [IsProper (B.inclusion.map f)]
    (K : DerivedCategory (Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1}))
    (n : ℤ) (hK : K.IsGE n)
    (hT : Stacks.Torsion.torsionCohomologyProperty.{u + 1}
      (SmallEtale.topology B T.obj T.property) K) :
    IsIso ((bigSmallEtaleDerivedBaseChange B f RfSmall RfBig αSmall αBig).app K) :=
  isIso_bigSmallEtaleDerivedBaseChange_app_of_cohomologyCommutesWithBaseChange B f RfSmall RfBig
    αSmall αBig (Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper _) K n hK hT

/-- **Stacks 0DDJ (3).** Let `f : T ⟶ S` be a proper morphism of a big étale site and `n ≥ 1`.
Then `π_S⁻¹ Rf_{small,*} K = Rf_{big,*} π_T⁻¹ K` for every `K` in `D(T_étale, ℤ/nℤ)`, the
unbounded derived category of sheaves of modules over the constant sheaf of rings `ℤ/nℤ`: the
canonical base change map `AlgebraicGeometry.bigSmallEtaleDerivedBaseChange` is invertible at
the underlying abelian complex of `K`. -/
@[stacks 0DDJ "(3)"]
public theorem isIso_bigSmallEtaleDerivedBaseChange_app_toSheaf_of_isProper_zmod
    [IsProper (B.inclusion.map f)] {n : ℕ} (hn : 0 < n)
    (E : DerivedCategory (SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1}
      (SmallEtale.topology B T.obj T.property) n))) :
    IsIso ((bigSmallEtaleDerivedBaseChange B f RfSmall RfBig αSmall αBig).app
      ((SheafOfModules.toSheaf _).mapDerivedCategory.obj E)) :=
  isIso_bigSmallEtaleDerivedBaseChange_app_toSheaf_of_zmod B f RfSmall RfBig αSmall αBig
    (fun _ _ _ _ _ sq E' ↦ open Stacks.EtaleCohomology in
      isIso_etaleAbelianDerivedBaseChange_zmod_of_cohomologyCommutesWithBaseChange
        (cohomologyCommutesWithBaseChange_of_isProper _)
        (fun _ _ p _ N hN F hF q hq ↦
          isZero_rightDerived_etaleAbelianDirectImage_of_isProper p N hN F hF q hq)
        sq hn E')
    E

end Derived

end AlgebraicGeometry

end
