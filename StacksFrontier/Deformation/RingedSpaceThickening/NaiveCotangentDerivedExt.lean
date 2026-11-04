module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.RingedSpace.NaiveCotangentComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two `Ext¹` groups of Stacks 0GQ3 and the maps between them

For a first order thickening `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` with ideal `𝒥`, a morphism
`f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`, an `𝒪_X`-module `𝒢` and a map `c : f^*𝒥 ⟶ 𝒢`, **Stacks 0GQ3**
compares the two groups

`Ext¹_{𝒪_X}(NL_{X/S'}, 𝒢)`  and  `Ext¹_{𝒪_X}(Lf^*NL_{S/S'}, 𝒢)`

and asks for the fibre of the map between them over the image of a class
`ξ ∈ Ext¹_{𝒪_S}(NL_{S/S'}, 𝒥)`.  This file builds both groups and both maps: `NL` is the naive
cotangent complex of **Stacks 08TN**, `Lf^*` the derived pullback of **Stacks 06YJ**, and the
map that `ξ` travels along is `Lf^*` applied to a class, commuted past the shift, and pushed
along `c`.

No `@[stacks]` attribute is carried.  These are the two groups and two maps appearing in the
statement of **Stacks 0GQ3**, not that tag's assertion; the tag's content is the bijection, and
why it is not claimed is explained in
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionExtensionFibre.lean`.  The map
`pullbackExtClass` is the first of the two maps the proof of 0GQ3 constructs, and the one
**Stacks 0GQ1** of
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionClassComparison.lean` explicitly leaves
out.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.relativeNaiveCotangentObj`: `NL_{X/S}` in `D(𝒪_X)`.
* `AlgebraicGeometry.RingedSpaceThickening.extOneNaiveCotangent` and
  `extOnePulledNaiveCotangent`: the two `Ext¹` groups.
* `AlgebraicGeometry.RingedSpaceThickening.derivedPullbackNaiveCotangent`: `Lf^*NL_{S/S'}`.
* `AlgebraicGeometry.RingedSpaceThickening.restrictDerivedExtClass`: precomposition with a
  comparison `Lf^*NL_{S/S'} ⟶ NL_{X/S'}`.
* `AlgebraicGeometry.RingedSpaceThickening.derivedPullbackSingleObj`: the comparison
  `Lf^*(ℱ[0]) ⟶ (f^*ℱ)[0]`, and `coefficientExtMap`, the coefficient map attached to `c`.
* `AlgebraicGeometry.RingedSpaceThickening.pullbackExtClass`: the image of `ξ`.

## Implementation notes

`Ext¹` is `DerivedCategory.Ext _ _ 1`, i.e. a morphism into the shift, so the map induced by a
comparison of the sources is literally composition; `restrictDerivedExtClass` is that
composition.  `HasDerivedCategory.standard` is a local instance, as in the other modules of the
library that work in `D(𝒪_X)`.

`relativeNaiveCotangentObj` ascribes the complex of **Stacks 08TN** to
`CochainComplex (SheafOfModules (structureSheafRing X)) ℤ` before applying `DerivedCategory.Q`.
Without the ascription the zero-morphisms instance of the complex comes from
`SheafOfModules.instPreadditive` while `DerivedCategory.Q` asks for the one induced by the abelian
structure, and the two do not unify while the category instance is still a metavariable.

The comparison `Lf^*NL_{S/S'} ⟶ NL_{X/S'}` is an argument of `restrictDerivedExtClass` rather
than a construction.  What the library has is the degreewise comparison
`f^*NL_{S/S'} ⟶ NL_{X/S'}`, built from **Stacks 08TM** and the base-change map of
**Stacks 0E1Y** in
`StacksFrontier/Topology/Sheaves/Modules/NaiveCotangentExactSequence.lean`; composing it with the
comparison `Lf^*K ⟶ f^*K` of **Stacks 06YJ** would need the degreewise pullback of `NL` in the
spelling `Lf^*`'s comparison uses — `(modulePullback f).mapHomologicalComplex` of the complex
of **Stacks 08TN** — identified with the spelling the base-change map uses, which is the
inverse image followed by extension of scalars, applied to a complex over an iterated inverse
image of the structure sheaf.  The library does not identify the two.

## References

* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 08TN](https://stacks.math.columbia.edu/tag/08TN)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y)
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}}

/-! ### The two `Ext¹` groups and the two maps between them -/

/-- `NL_{X/S}`, the naive cotangent complex of **Stacks 08TN**, as an object of `D(𝒪_X)`. -/
@[sga "6 0 4.4"]
abbrev relativeNaiveCotangentObj (f : X ⟶ S) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  DerivedCategory.Q.obj
    (show CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ from
      AlgebraicGeometry.RingedSpace.naiveCotangentComplex f)

/-- `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)`. -/
abbrev extOneNaiveCotangent (f : X ⟶ S) (G : SheafOfModules.{u} (structureSheafRing X)) :=
  DerivedCategory.Ext (relativeNaiveCotangentObj f)
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj G) 1

/-- `Lf^*NL_{S/S'}`, the derived pullback of **Stacks 06YJ** of the naive cotangent complex of
the base thickening, as an object of `D(𝒪_X)`. -/
abbrev derivedPullbackNaiveCotangent (f : X ⟶ S) (t : S ⟶ S') :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  (derivedPullback f).obj (relativeNaiveCotangentObj t)

/-- `Ext¹_{𝒪_X}(Lf^*NL_{S/S'}, 𝒢)`, the group the two classes of **Stacks 0GQ3** are compared
in. -/
abbrev extOnePulledNaiveCotangent (f : X ⟶ S) (t : S ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing X)) :=
  DerivedCategory.Ext (derivedPullbackNaiveCotangent f t)
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj G) 1

/-- The map `Ext¹_{𝒪_X}(NL_{X/S'}, 𝒢) ⟶ Ext¹_{𝒪_X}(Lf^*NL_{S/S'}, 𝒢)` of **Stacks 0GQ3**:
precomposition with a comparison `q : Lf^*NL_{S/S'} ⟶ NL_{X/S'}`.  See the implementation notes
for why `q` is an argument. -/
def restrictDerivedExtClass {f : X ⟶ S} {t : S ⟶ S'} {G : SheafOfModules.{u} (structureSheafRing X)}
    (q : derivedPullbackNaiveCotangent f t ⟶ relativeNaiveCotangentObj (f ≫ t))
    (z : extOneNaiveCotangent (f ≫ t) G) : extOnePulledNaiveCotangent f t G :=
  q ≫ z

/-- The comparison `Lf^*(ℱ[0]) ⟶ (f^*ℱ)[0]` of the derived with the degreewise pullback on a
module placed in degree `0`. -/
def derivedPullbackSingleObj (f : X ⟶ S) (F : SheafOfModules.{u} (structureSheafRing S)) :
    (derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (DerivedCategory.singleFunctor _ 0).obj ((modulePullback f).obj F) :=
  let K := (CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0).obj F
  (derivedPullback f).map ((DerivedCategory.singleFunctorIsoCompQh _ 0).hom.app F) ≫
    (derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (modulePullback f)
        (ComplexShape.up ℤ) 0).hom.app F)

/-- The coefficient map `Lf^*(𝒥[0]) ⟶ 𝒢[0]` attached to `c : f^*𝒥 ⟶ 𝒢`. -/
def coefficientExtMap (f : X ⟶ S) {J : SheafOfModules.{u} (structureSheafRing S)}
    {G : SheafOfModules.{u} (structureSheafRing X)} (c : (modulePullback f).obj J ⟶ G) :
    (derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj J) ⟶
      (DerivedCategory.singleFunctor _ 0).obj G :=
  derivedPullbackSingleObj f J ≫ (DerivedCategory.singleFunctor _ 0).map c

/-- The image of `ξ ∈ Ext¹_{𝒪_S}(NL_{S/S'}, 𝒥)` in `Ext¹_{𝒪_X}(Lf^*NL_{S/S'}, 𝒢)`: apply
`Lf^*`, commute it past the shift, and push the coefficients along `c`.  This is the first of
the two maps the proof of **Stacks 0GQ3** constructs. -/
def pullbackExtClass (f : X ⟶ S) (t : S ⟶ S') {J : SheafOfModules.{u} (structureSheafRing S)}
    {G : SheafOfModules.{u} (structureSheafRing X)} (c : (modulePullback f).obj J ⟶ G)
    (xi : extOneNaiveCotangent t J) : extOnePulledNaiveCotangent f t G :=
  (derivedPullback f).map xi ≫
    ((derivedPullback f).commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj J) ≫
    (coefficientExtMap f c)⟦(1 : ℤ)⟧'

end AlgebraicGeometry.RingedSpaceThickening

end
