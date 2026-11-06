module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap
public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
import StacksCore.Tactic.StacksAttribute

/-!
# The base change map for a square of ringed spaces with flat horizontal morphisms

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g-->  S
```

be a commutative diagram of ringed spaces with `g` and `g'` flat. This file constructs the
canonical base change map

`g^* Rf_* F^• ⟶ R(f')_* (g')^* F^•`

on bounded below derived categories of sheaves of modules, and characterizes it by its
compatibility with the derived-functor unit of `Rf_*`.

Flatness enters in exactly one place: pullback of sheaves of modules along a flat morphism of
ringed spaces is exact (Stacks 02N4), so its right derived functor on `D⁺` is computed
degreewise and is the honest pullback `g^*`. That is what makes the mate of the square, which
lives between the underived functors, descend to the derived level.

## Main definitions

* `Stacks.Cohomology.FlatBaseChange.flatPullback`: pullback along a flat morphism of ringed
  spaces, on bounded below derived categories.
* `Stacks.Cohomology.FlatBaseChange.flatPullbackComparison`: the identification of that functor
  with degreewise pullback.
* `Stacks.Cohomology.FlatBaseChange.squarePushforwardIso`: the isomorphism between the two
  composite direct images that commutativity of the square provides.
* `Stacks.Cohomology.FlatBaseChange.moduleBaseChange`: the underived base change map
  `g^* f_* ⟶ f'_* (g')^*`.
* `Stacks.Cohomology.FlatBaseChange.baseChangeOnHomotopyCategory`: the comparison before
  localization.
* `Stacks.Cohomology.FlatBaseChange.baseChangeMap`: **the base change map of Stacks 02N7.**

## Main results

* `Stacks.Cohomology.FlatBaseChange.baseChangeMap_fac`: composed with the derived-functor unit
  of `Rf_*`, the base change map is the comparison on the bounded below homotopy category.
  Since `Rf_* ⋙ g^*` is a right derived functor of `f_* ⋙ g^*` with that unit, this equation
  determines the map, so the map is canonical and not merely some morphism. This is what the
  source means by "there exists a canonical base change map".

## Implementation notes

*What is reused.* The descent of a commuting square of underived functors to bounded below right
derived functors is available in full generality as `Stacks.Cohomology.BaseChange.mate`,
`.onHomotopy`, `.derived` and `.derived_fac`, with `Stacks.Cohomology.BaseChange.exactUnit_isIso`
for the invertibility of the derived-functor unit of an exact functor. Those are stated for
arbitrary abelian categories, and none of that recipe is repeated here; this file only
instantiates it at pullback and pushforward of sheaves of modules on ringed spaces. Exactness of
pullback along a flat morphism is Stacks 02N4,
`RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat` together with
the unconditional right exactness
`RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback`.

*How the square enters.* Only through `squarePushforwardIso`, the isomorphism
`(g')_* f_* ≅ f'_* g_*` of the two composite direct images. Pushforward of sheaves of modules
is multiplicative in the morphism on the nose
(`RingedSpaceModuleAdjunction.modulePushforwardComp` has identity components), so the
equality `g' ≫ f = f' ≫ g` of the source yields that isomorphism with a single transport, and
it is exactly what the mate construction consumes.

*Why `flatPullback` records a flatness hypothesis it does not use.* The right derived functor of
the pullback exists for any morphism, but it is the `g^*` of the source statement only when the
morphism is flat — otherwise it is not computed degreewise. Carrying the hypothesis in the
interface keeps the two flatness assumptions of the source visible in the type of
`baseChangeMap`; `flatPullbackComparison` is where the hypothesis does its work.

*Relation to Stacks 08HY.* The file
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/BaseChangeMap.lean` builds the base
change map `Lg^* Rf_* ⟶ Rf'_* L(g')^*` on the *unbounded* derived category, for an arbitrary
square, with the *derived* pullbacks. That is a different statement: here the horizontal functors
are the underived pullbacks, which is what flatness buys, and the categories are the bounded
below ones. Neither map is obtained from the other by specialization.

*Universes.* A morphism of ringed spaces as Mathlib defines it, and the pullback-pushforward
adjunction of Stacks 0096 built on it, identify the universe of the underlying space, of the
structure sheaf and of the sheaves of modules; so the four ringed spaces of the square all live
in `RingedSpace.{u, u}` and the modules in `SheafOfModules.{u}`. The derived categories are
seated by `HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.FlatBaseChange

attribute [local instance] HasDerivedCategory.standard

universe u

/-- **The injectivity hypotheses below are always satisfied.** For every ringed space `X` the
category of sheaves of `𝒪_X`-modules has enough injectives, by
`SheafOfModules.enoughInjectives_opens`. So the `EnoughInjectives` arguments carried by
`flatPullback`, `baseChangeMap` and `baseChangeMap_fac` are not restrictions on the square: they
are stated as instance hypotheses only because the repository keeps this a theorem rather than a
global instance, and a consumer discharges them with this lemma. -/
@[sga "4½ Etat_0 6.2" "special case"]
theorem enoughInjectives_ringSheaf (X : RingedSpace.{u, u}) :
    EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
  _root_.SheafOfModules.enoughInjectives_opens.{u, u, u} X.carrier (structureSheafRing X)

/-! ### Pullback along a flat morphism on bounded below derived categories -/

section Pullback

variable {X Y : RingedSpace.{u, u}}
  [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing Y))]

/-- Pullback of sheaves of modules along a flat morphism of ringed spaces, on bounded below
derived categories: the right derived functor of the pullback of Stacks 0096. Flatness is
recorded in the interface because it is what makes this functor the `g^*` of the source
statement, namely computed degreewise; see `flatPullbackComparison`. -/
abbrev flatPullback (g : X ⟶ Y) (_hg : AlgebraicGeometry.IsFlat g) :
    DerivedCategory.Plus (_root_.SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory.Plus (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
  (modulePullback g).rightDerivedFunctorPlus

/-- Along a flat morphism of ringed spaces the derived pullback is the degreewise one: the
pullback is exact by Stacks 02N4, so its derived-functor unit is invertible. -/
def flatPullbackComparison (g : X ⟶ Y) (hg : AlgebraicGeometry.IsFlat g) :
    (modulePullback g).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ flatPullback g hg :=
  have := preservesFiniteLimits_modulePullback_of_isFlat g hg
  have := preservesFiniteColimits_modulePullback g
  have := Stacks.Cohomology.BaseChange.exactUnit_isIso (modulePullback g)
  asIso (modulePullback g).rightDerivedFunctorPlusUnith

end Pullback

/-! ### The base change map of a commutative square -/

section Square

variable {X X' S S' : RingedSpace.{u, u}}
  [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X))]
  [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X'))]
  [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing S))]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g)

/-- The isomorphism `(g')_* f_* ≅ f'_* g_*` between the two composite direct images of a
commutative square of ringed spaces. Pushforward of sheaves of modules is multiplicative in the
morphism on the nose, so this is the equality `g' ≫ f = f' ≫ g` of the source transported along
`RingedSpaceModuleAdjunction.modulePushforwardComp`. -/
def squarePushforwardIso :
    modulePushforward g' ⋙ modulePushforward f ≅
      modulePushforward f' ⋙ modulePushforward g :=
  RingedSpaceModuleAdjunction.modulePushforwardComp g' f ≪≫
    eqToIso (congrArg (modulePushforward (X := X') (Y := S)) comm) ≪≫
    (RingedSpaceModuleAdjunction.modulePushforwardComp f' g).symm

/-- The underived base change map `g^* f_* ⟶ f'_* (g')^*` of a commutative square of ringed
spaces: the mate of `squarePushforwardIso` under the two pullback-pushforward adjunctions of
Stacks 0096. -/
def moduleBaseChange :
    modulePushforward f ⋙ modulePullback g ⟶
      modulePullback g' ⋙ modulePushforward f' :=
  Stacks.Cohomology.BaseChange.mate
    (modulePullbackPushforwardAdjunction g) (modulePullbackPushforwardAdjunction g')
    (modulePushforward f) (modulePushforward f') (squarePushforwardIso f f' g g' comm)

variable (hg : AlgebraicGeometry.IsFlat g) (hg' : AlgebraicGeometry.IsFlat g')

/-- The base change comparison before localization: the underived base change map applied
degreewise on the bounded below homotopy category of `Mod(𝒪_X)`, followed by the derived-functor
units of `R(g')^*` and `R(f')_*`. -/
def baseChangeOnHomotopyCategory :
    ((modulePushforward f).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        flatPullback g hg ⟶
      DerivedCategory.Plus.Qh ⋙
        (flatPullback g' hg' ⋙ (modulePushforward f').rightDerivedFunctorPlus) :=
  Stacks.Cohomology.BaseChange.onHomotopy (modulePushforward f) (modulePushforward f')
    (modulePullback g) (modulePullback g') (moduleBaseChange f f' g g' comm)
    (flatPullbackComparison g hg)

/-- **Stacks 02N7, the base change map.** For a commutative diagram of ringed spaces whose
horizontal morphisms `g` and `g'` are flat, the canonical map

`g^* Rf_* ⟶ R(f')_* (g')^*`

of functors on bounded below derived categories of sheaves of modules, so in particular
`g^* Rf_* ℱ^• ⟶ R(f')_* (g')^* ℱ^•` in `D⁺(S')` for every bounded below complex `ℱ^•` of
`𝒪_X`-modules. It is the descent of the underived base change map along the derived-functor unit
of `Rf_*`, and `baseChangeMap_fac` says that this determines it. -/
@[stacks 02N7 "base-change morphism"]
def baseChangeMap :
    (modulePushforward f).rightDerivedFunctorPlus ⋙ flatPullback g hg ⟶
      flatPullback g' hg' ⋙ (modulePushforward f').rightDerivedFunctorPlus :=
  Stacks.Cohomology.BaseChange.derived (modulePushforward f) (modulePushforward f')
    (modulePullback g) (modulePullback g') (moduleBaseChange f f' g g' comm)
    (flatPullbackComparison g hg)

/-- **Stacks 02N7, canonicity of the base change map.** Composed with the derived-functor unit
of `Rf_*`, the base change map is the comparison `baseChangeOnHomotopyCategory` on the bounded
below homotopy category. Since `Rf_* ⋙ g^*` is a right derived functor of `f_* ⋙ g^*` with that
unit, this equation determines the base change map; it is the sense in which the map of the
source is canonical rather than merely existing. -/
@[stacks 02N7 "canonical characterization"]
theorem baseChangeMap_fac :
    Functor.whiskerRight (modulePushforward f).rightDerivedFunctorPlusUnith
        (flatPullback g hg) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh (baseChangeMap f f' g g' comm hg hg') =
        baseChangeOnHomotopyCategory f f' g g' comm hg hg' :=
  Stacks.Cohomology.BaseChange.derived_fac (modulePushforward f) (modulePushforward f')
    (modulePullback g) (modulePullback g') (moduleBaseChange f f' g g' comm)
    (flatPullbackComparison g hg)

end Square

end Stacks.Cohomology.FlatBaseChange

end
