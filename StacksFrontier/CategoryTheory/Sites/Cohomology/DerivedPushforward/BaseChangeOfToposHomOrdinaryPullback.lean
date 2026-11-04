module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHomTwoIso

/-!
# The base change map of a 2-commutative square into the pushforward of an ordinary pullback

For a square of morphisms of ringed topoi commuting up to a 2-isomorphism
`s : g ∘ f' ≅ f ∘ g'`, the base change map of Cohomology on Sites, Remark 07A7,
`Lg^* Rf_* K ⟶ Rf'_* L(g')^* K`, is
`Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedBaseChangeMapOfTwoIso`.  Composing it with
`Rf'_*` of the canonical comparison `L(g')^* ⟶ (g')^*` of Stacks 06YY gives, at a module `ℱ'` in
degree zero, the map

`Lg^* Rf_* ℱ' ⟶ Rf'_* (g')^* ℱ'`

whose target is the derived pushforward of the *ordinary* pullback of `ℱ'`.  This is the shape of
the base change map of Stacks 07MS, whose hint reads: compose the very general base change map of
Remark 07A7 with the canonical map `Lf_cris^* ℱ' ⟶ f_cris^* ℱ' = ℱ`.

This is the ringed-topos counterpart, for 2-commutative squares, of
`Stacks.Cohomology.DerivedBaseChangeOnTopoi.derivedBaseChangeMapOfModule`, which is stated for
morphisms presented by continuous functors of sites and strictly commuting squares.

## Main definitions

* `homotopyPullbackModulesSingleIso` — degreewise pullback of a module in degree zero is the
  pullback of the module in degree zero.
* `derivedBaseChangeMapOfTwoIsoOfModule` — the map `Lg^* Rf_* ℱ' ⟶ Rf'_* (g')^* ℱ'`.

## References

* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom

namespace Stacks.Cohomology.DerivedBaseChangeOfToposHom

universe vC' uC' wC' vC uC wC vD' uD' wD' vD uD wD

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

noncomputable section

section Single

variable {X' : RingedTopos.{vC', uC', wC'}} {X : RingedTopos.{vC, uC, wC}}
  [X'.J.HasSheafCompose (forget RingCat.{wC'})] [X.J.HasSheafCompose (forget RingCat.{wC})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [HasSheafify X'.J AddCommGrpCat.{wC'}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{wC'}]
  [HasSheafify X.J AddCommGrpCat.{wC}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
  [HasSheafify X'.J (Type wC')] [HasSheafify X.J (Type wC)]
  (g' : RingedToposHom X' X)

/-- **Degreewise pullback of a module in degree zero.**  Degreewise pullback along `g'` carries
the complex with `ℱ'` in degree zero to the complex with the ordinary pullback `(g')^* ℱ'` in
degree zero, as objects of the homotopy category. -/
def homotopyPullbackModulesSingleIso
    (F' : SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    (g'.toModulesHom.pullbackModules.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.singleFunctor
          (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
          (0 : ℤ)).obj F') ≅
      (HomotopyCategory.singleFunctor
          (SheafOfModules.{wC'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J)) X'.O))
          (0 : ℤ)).obj (g'.toModulesHom.pullbackModules.obj F') :=
  (g'.toModulesHom.pullbackModules.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
      ((HomologicalComplex.single
        (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
        (ComplexShape.up ℤ) (0 : ℤ)).obj F') ≪≫
    (HomotopyCategory.quotient
        (SheafOfModules.{wC'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J)) X'.O))
        (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex g'.toModulesHom.pullbackModules
        (ComplexShape.up ℤ) (0 : ℤ)).app F')

/-- **The canonical comparison `L(g')^* ℱ' ⟶ (g')^* ℱ'` at a module in degree zero**, the
comparison of Stacks 06YY read between the two single complexes. -/
def derivedPullbackSingleComparison
    (F' : SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    (derivedPullback g').obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
          (0 : ℤ)).obj F') ⟶
      (DerivedCategory.singleFunctor
          (SheafOfModules.{wC'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J)) X'.O))
          (0 : ℤ)).obj (g'.toModulesHom.pullbackModules.obj F') :=
  (derivedPullback g').map
      ((DerivedCategory.singleFunctorIsoCompQh
        (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
        (0 : ℤ)).hom.app F') ≫
    (derivedPullbackComparison g').app
      ((HomotopyCategory.singleFunctor
        (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
        (0 : ℤ)).obj F') ≫
    DerivedCategory.Qh.map (homotopyPullbackModulesSingleIso g' F').hom ≫
    (DerivedCategory.singleFunctorIsoCompQh
        (SheafOfModules.{wC'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J)) X'.O))
        (0 : ℤ)).inv.app (g'.toModulesHom.pullbackModules.obj F')

end Single

section Square

variable {X' : RingedTopos.{vC', uC', wC'}} {X : RingedTopos.{vC, uC, wC}}
  {Y' : RingedTopos.{vD', uD', wD'}} {Y : RingedTopos.{vD, uD, wD}}
  [X'.J.HasSheafCompose (forget RingCat.{wC'})] [X.J.HasSheafCompose (forget RingCat.{wC})]
  [Y'.J.HasSheafCompose (forget RingCat.{wD'})] [Y.J.HasSheafCompose (forget RingCat.{wD})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{wD'} RingCat.{wD'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{wD'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{wD})]
  [HasSheafify X'.J AddCommGrpCat.{wC'}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{wC'}]
  [HasSheafify X.J AddCommGrpCat.{wC}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
  [HasSheafify Y'.J AddCommGrpCat.{wD'}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{wD'}]
  [HasSheafify Y.J AddCommGrpCat.{wD}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{wD}]
  [HasSheafify X'.J (Type wC')] [HasSheafify X.J (Type wC)]
  [HasSheafify Y'.J (Type wD')] [HasSheafify Y.J (Type wD)]
  [IsGrothendieckAbelian.{wC}
    (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))]
  [IsGrothendieckAbelian.{wC'}
    (SheafOfModules.{wC'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J)) X'.O))]
  (f : RingedToposHom X Y) (g' : RingedToposHom X' X)
  (f' : RingedToposHom X' Y') (g : RingedToposHom Y' Y)

/-- **The base change map into the pushforward of the ordinary pullback, at a module.**  For a
square of morphisms of ringed topoi 2-commuting by `s : g ∘ f' ≅ f ∘ g'` and an `𝒪_C`-module
`ℱ'`, the composite

`Lg^* Rf_* ℱ' ⟶ Rf'_* L(g')^* ℱ' ⟶ Rf'_* (g')^* ℱ'`

of the base change map of Stacks 07A7 with `Rf'_*` of the comparison `L(g')^* ℱ' ⟶ (g')^* ℱ'` of
Stacks 06YY, both modules read in degree zero. -/
def derivedBaseChangeMapOfTwoIsoOfModule (s : RingedToposHom.TwoIso (g.comp f') (f.comp g'))
    (F' : SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    (derivedPullback g).obj ((derivedPushforward f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
          (0 : ℤ)).obj F')) ⟶
      (derivedPushforward f').obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{wC'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J)) X'.O))
          (0 : ℤ)).obj (g'.toModulesHom.pullbackModules.obj F')) :=
  derivedBaseChangeMapOfTwoIso f g' f' g s _ ≫
    (derivedPushforward f').map (derivedPullbackSingleComparison g' F')

/-- The defining factorization: the base change map of Stacks 07A7 followed by the derived
pushforward of the comparison of Stacks 06YY. -/
theorem derivedBaseChangeMapOfTwoIsoOfModule_eq
    (s : RingedToposHom.TwoIso (g.comp f') (f.comp g'))
    (F' : SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    derivedBaseChangeMapOfTwoIsoOfModule f g' f' g s F' =
      derivedBaseChangeMapOfTwoIso f g' f' g s _ ≫
        (derivedPushforward f').map (derivedPullbackSingleComparison g' F') :=
  rfl

end Square

end

end Stacks.Cohomology.DerivedBaseChangeOfToposHom

end
