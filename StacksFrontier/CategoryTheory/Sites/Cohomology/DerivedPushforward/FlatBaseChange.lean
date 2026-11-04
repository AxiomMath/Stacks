module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.ExactnessOfPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap
import StacksCore.Tactic.StacksAttribute

/-!
# The base change map for a square of ringed topoi with flat horizontal morphisms

Let

```
(Sh(C'), O_{C'}) --g'--> (Sh(C), O_C)
      |                       |
      f'                      f
      v                       v
(Sh(D'), O_{D'}) --g-->  (Sh(D), O_D)
```

be a commutative square of ringed topoi with `g` and `g'` flat. This file constructs the
canonical base change map

`g^* Rf_* F^• ⟶ R(f')_* (g')^* F^•`

on bounded below derived categories of sheaves of modules, and characterizes it by its
compatibility with the derived-functor unit of `Rf_*`.

The pullback of sheaves of modules along a flat morphism of ringed topoi is exact, so its right
derived functor on `D⁺` is computed degreewise and is the inverse image `g^*`.

## Main definitions

* `Stacks.Cohomology.ToposBaseChange.flatPullback`: inverse image along a flat morphism of
  ringed topoi, on bounded below derived categories.
* `Stacks.Cohomology.ToposBaseChange.flatPullbackComparison`: the identification of that
  functor with degreewise inverse image.
* `Stacks.Cohomology.ToposBaseChange.moduleBaseChange`: the underived base change map
  `g^* f_* ⟶ f'_* (g')^*`.
* `Stacks.Cohomology.ToposBaseChange.baseChangeOnHomotopyCategory`: the comparison before
  localization.
* `Stacks.Cohomology.ToposBaseChange.baseChangeMap`: **the base change map.**

## Main results

* `Stacks.Cohomology.ToposBaseChange.baseChangeMap_fac`: composed with the derived-functor unit
  of `Rf_*`, the base change map is the comparison on the bounded below homotopy category.

## References

* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.Sheaves.RingedToposModules

namespace Stacks.Cohomology.ToposBaseChange

attribute [local instance] HasDerivedCategory.standard

universe v u v' u' v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ w

/-! ### Inverse image along a flat morphism on bounded below derived categories -/

section Pullback

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]

/-- Inverse image of sheaves of modules along a flat morphism of ringed topoi, on bounded below
derived categories: the right derived functor of the inverse image of Stacks 03D6 part (2). -/
abbrev flatPullback (g : AlgebraicGeometry.RingedToposHom X Y) (_hg : g.IsFlat) :
    DerivedCategory.Plus (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory.Plus (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (g.toRingedToposModulesHom.pullbackModules).rightDerivedFunctorPlus

/-- Along a flat morphism of ringed topoi the derived inverse image is the degreewise one: the
derived-functor unit of the inverse image is an isomorphism. -/
def flatPullbackComparison (g : AlgebraicGeometry.RingedToposHom X Y) (hg : g.IsFlat) :
    (g.toRingedToposModulesHom.pullbackModules).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ flatPullback g hg :=
  have hex := (exactFunctor_iff _).mp (pullbackModules_exact_of_isFlatMap g hg)
  have := hex.1
  have := hex.2
  have := Stacks.Cohomology.BaseChange.exactUnit_isIso
    (g.toRingedToposModulesHom.pullbackModules)
  asIso (g.toRingedToposModulesHom.pullbackModules).rightDerivedFunctorPlusUnit

end Pullback

/-! ### The base change map of a commutative square -/

section Square

variable {C : RingedTopos.{v₁, u₁, w}} {C' : RingedTopos.{v₂, u₂, w}}
  {D : RingedTopos.{v₃, u₃, w}} {D' : RingedTopos.{v₄, u₄, w}}
  [C.J.HasSheafCompose (forget RingCat.{w})] [C'.J.HasSheafCompose (forget RingCat.{w})]
  [D.J.HasSheafCompose (forget RingCat.{w})] [D'.J.HasSheafCompose (forget RingCat.{w})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [D'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [C.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [C'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [D.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [D'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify C.J AddCommGrpCat.{w}] [HasSheafify C'.J AddCommGrpCat.{w}]
  [HasSheafify D.J AddCommGrpCat.{w}] [HasSheafify D'.J AddCommGrpCat.{w}]
  [C.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [C'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [D.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [D'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf C.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf C'.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf D.O))]
  (f : AlgebraicGeometry.RingedToposHom C D)
  (f' : AlgebraicGeometry.RingedToposHom C' D')
  (g : AlgebraicGeometry.RingedToposHom D' D)
  (g' : AlgebraicGeometry.RingedToposHom C' C)
  (comm : pushforwardModules g'.toRingedToposModulesHom ⋙
      pushforwardModules f.toRingedToposModulesHom ≅
    pushforwardModules f'.toRingedToposModulesHom ⋙
      pushforwardModules g.toRingedToposModulesHom)

/-- The underived base change map `g^* f_* ⟶ f'_* (g')^*` of a commutative square of ringed
topoi: the mate of the isomorphism between the two composite direct images, under the two
adjunctions of Stacks 03D7. -/
def moduleBaseChange :
    pushforwardModules f.toRingedToposModulesHom ⋙
        g.toRingedToposModulesHom.pullbackModules ⟶
      g'.toRingedToposModulesHom.pullbackModules ⋙
        pushforwardModules f'.toRingedToposModulesHom :=
  Stacks.Cohomology.BaseChange.mate
    (pullbackAdjPushforwardModules g.toRingedToposModulesHom)
    (pullbackAdjPushforwardModules g'.toRingedToposModulesHom)
    (pushforwardModules f.toRingedToposModulesHom)
    (pushforwardModules f'.toRingedToposModulesHom) comm

variable (hg : g.IsFlat) (hg' : g'.IsFlat)

/-- The base change comparison before localization: the underived base change map applied
degreewise on the bounded below homotopy category of `Mod(O_C)`, followed by the
derived-functor units of `R(g')^*` and `R(f')_*`. -/
def baseChangeOnHomotopyCategory :
    ((pushforwardModules f.toRingedToposModulesHom).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh) ⋙ flatPullback g hg ⟶
      DerivedCategory.Plus.Qh ⋙ (flatPullback g' hg' ⋙
        (pushforwardModules f'.toRingedToposModulesHom).rightDerivedFunctorPlus) :=
  Stacks.Cohomology.BaseChange.onHomotopy
    (pushforwardModules f.toRingedToposModulesHom)
    (pushforwardModules f'.toRingedToposModulesHom)
    (g.toRingedToposModulesHom.pullbackModules)
    (g'.toRingedToposModulesHom.pullbackModules)
    (moduleBaseChange f f' g g' comm) (flatPullbackComparison g hg)

/-- **The base change map** `g^* Rf_* ⟶ R(f')_* (g')^*` of a commutative square of ringed topoi
whose horizontal morphisms `g` and `g'` are flat, on bounded below derived categories of sheaves
of modules: the descent of the underived base change map `moduleBaseChange` to bounded below
derived categories. -/
@[stacks 0736 "base-change morphism"]
def baseChangeMap :
    (pushforwardModules f.toRingedToposModulesHom).rightDerivedFunctorPlus ⋙
        flatPullback g hg ⟶
      flatPullback g' hg' ⋙
        (pushforwardModules f'.toRingedToposModulesHom).rightDerivedFunctorPlus :=
  Stacks.Cohomology.BaseChange.derived
    (pushforwardModules f.toRingedToposModulesHom)
    (pushforwardModules f'.toRingedToposModulesHom)
    (g.toRingedToposModulesHom.pullbackModules)
    (g'.toRingedToposModulesHom.pullbackModules)
    (moduleBaseChange f f' g g' comm) (flatPullbackComparison g hg)

/-- Composed with the derived-functor unit of `Rf_*`, the base change map `baseChangeMap` is the
comparison `baseChangeOnHomotopyCategory` on the bounded below homotopy category. -/
@[stacks 0736 "canonical characterization"]
theorem baseChangeMap_fac :
    Functor.whiskerRight
        (pushforwardModules f.toRingedToposModulesHom).rightDerivedFunctorPlusUnit
        (flatPullback g hg) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh (baseChangeMap f f' g g' comm hg hg') =
        baseChangeOnHomotopyCategory f f' g g' comm hg hg' :=
  Stacks.Cohomology.BaseChange.derived_fac
    (pushforwardModules f.toRingedToposModulesHom)
    (pushforwardModules f'.toRingedToposModulesHom)
    (g.toRingedToposModulesHom.pullbackModules)
    (g'.toRingedToposModulesHom.pullbackModules)
    (moduleBaseChange f f' g g' comm) (flatPullbackComparison g hg)

end Square

end Stacks.Cohomology.ToposBaseChange

end
