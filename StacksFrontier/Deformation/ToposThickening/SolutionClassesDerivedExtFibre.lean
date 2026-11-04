module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentLiftingObstruction
public import StacksFrontier.Deformation.ToposThickening.SolutionClassesFibre
import StacksCore.Tactic.StacksAttribute

/-!
# The fibre of Stacks 0GQ9, for the derived pullback

Fix the data (91.13.0.1) of **Stacks 08UF**: a first order thickening
`t : (Sh(ℬ), 𝒪_ℬ) ⟶ (Sh(ℬ'), 𝒪_{ℬ'})` with ideal `𝒥 = Ker(t^♯)`, a morphism
`f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)`, an `𝒪`-module `𝒢` and a map `c : f^*𝒥 ⟶ 𝒢`. Writing `ξ` for
the class in `Ext¹_{𝒪_ℬ}(NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒥)` of the extension `𝒪_{ℬ'}` of `𝒪_ℬ` by `𝒥`,
**Stacks 0GQ9** says the isomorphism classes of solutions are canonically bijective to the fibre
over the image of `ξ` of

`Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢) ⟶ Ext¹_𝒪(Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒢)`.

This file builds both groups and both maps and then the bijection. `NL` is the naive cotangent
complex of **Stacks 08TW**, `Lf^*` the derived pullback of **Stacks 06YY** along a morphism of
ringed topoi, and the map `ξ` travels along is `Lf^*` applied to a class, commuted past the
shift, and pushed along `c`. It is the topos counterpart of
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentDerivedExt.lean` together with
`StacksFrontier/Deformation/RingedSpaceThickening/DerivedExtensionClassCriterion.lean`, where the
same two constructions and the same assembly deliver the ringed-space twin **Stacks 0GQ3**.

The companion file `StacksFrontier/Deformation/ToposThickening/SolutionClassesFibre.lean` proves
the two unconditional halves this one consumes: that a solution of (91.13.0.1) is exactly a
square-zero extension of `f⁻¹𝒪_{ℬ'}`-algebras inducing `c` on the base ideal
(`solutionEquivSquareZero`), and that this descends to isomorphism classes
(`classesEquivCompatible`). What that file states for the *sectionwise* obstruction and a fibre
over `0` — an analogue of 0GQ9 with a different map, as its own notes record — is here replaced
by the source's map and the source's class.

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.relativeNaiveCotangentObj` and
  `.baseNaiveCotangentObj`: `NL_{𝒪/𝒪_{ℬ'}}` in `D(𝒪)` and `NL_{𝒪_ℬ/𝒪_{ℬ'}}` in `D(𝒪_ℬ)`.
* `.derivedPullbackNaiveCotangent`: `Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}`, and
  `.extOneRelativeNaiveCotangent`, `.extOnePulledNaiveCotangent`: the two `Ext¹` groups.
* `.restrictDerivedExtClass`: precomposition with a comparison
  `q : Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}} ⟶ NL_{𝒪/𝒪_{ℬ'}}`.
* `.derivedPullbackSingleObj`: the comparison `Lf^*(ℱ[0]) ⟶ (f^*ℱ)[0]`, and
  `.coefficientExtMap`, the coefficient map attached to `c`.
* `.pullbackExtClass`: the image of `ξ`.
* `.CompatibleSolutionInClass`: the solutions lying in a prescribed isomorphism class of
  square-zero extensions of `f⁻¹𝒪_{ℬ'}`-algebras.

## Main results

* `Deformation.ToposThickening.RingedToposExtensionProblem.nonempty_lift_iff_eq_pullbackExtClass`:
  **Stacks 0GQ7** for the derived pullback — a compatible lift exists exactly when the
  constructed image of `ξ` equals the restriction of the class of the extension.
* `.isCompatibleWithIdealClass_iff_eq_pullbackExtClass`: the same criterion read on isomorphism
  classes. This is 0GQ9's cutting-out condition, discharged.
* `.classesEquivDerivedExtFibre`: **Stacks 0GQ9**, the canonical bijection with the fibre, and
  `.classesEquivDerivedExtFibre_apply`, that it is the map `[𝒪'] ↦ E [𝒪']`.

## Implementation notes

**What is constructed and what is carried.** The two groups, the comparison
`Lf^*(ℱ[0]) ⟶ (f^*ℱ)[0]`, the coefficient map and the image `pullbackExtClass` of `ξ` are all
built outright; so is the restriction map, once a comparison `q` is given. The criterion is
proved, not assumed. What remains hypotheses are exactly the carriers of the ringed-space
twin **Stacks 0GQ3**, and no more.

* `q : Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}} ⟶ NL_{𝒪/𝒪_{ℬ'}}` is an argument. The library has the degreewise
  comparison in the one-site spelling of
  `StacksFrontier/CategoryTheory/Sites/Modules/NaiveCotangentTowerConeMap.lean`, and **Stacks 08TZ**
  in the two terms separately (`Stacks.Sheaves.RingedToposModules.inverseImageConormalIso` and
  `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroIso`); composing either with the
  comparison `Lf^*𝒦 ⟶ f^*𝒦` of **Stacks 06YY** would need the degreewise pullback of `NL` in the
  spelling that comparison uses — `(pullbackModules f).mapHomologicalComplex` of the complex of
  **Stacks 08TW** — identified with the inverse image followed by extension of scalars. The
  complex-level identification
  `Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso` exists but is conditional on a
  commuting square that is nowhere proved, so the composite is not available.
* `E`, the bijection of **Stacks 0GQ5**, is an argument because the library's form of that tag,
  `Deformation.ToposThickening.RingedToposExtensionProblem.classesEquivExt`, classifies by the
  `Ext¹` of a *fixed presentation* `α` rather than by `Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢)`; identifying
  the two is **Stacks 08TY** and **Stacks 08TL**, which on a general site the library has only
  in degree `0`, as the notes of
  `StacksFrontier/Deformation/ToposThickening/ExtensionPresentation.lean` record at length.
* `P` with `hP`, `δ` and `e` — the two-term structure of `Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}`, the Step 1
  difference homomorphism and Steps 1 to 3 of the proof of **Stacks 08UG** — and `hcompat`, the
  compatibility between the constructions in the proofs of **Stacks 0GQ5** and **Stacks 08UG**
  whose statement and proof **the source itself omits**, deferring to **Stacks 0GQ8**. These are
  the carriers of the degreewise form of **Stacks 0GQ7** already proved in
  `StacksFrontier/Deformation/ToposThickening/LiftingMorphismExtensionClasses.lean`, inherited
  unchanged.

**The base-side data `𝒥`, `c` and `ξ` are arguments, and what that costs.** `𝒥` is a sheaf of
`𝒪_ℬ`-modules on the site of the base, `c : f^*𝒥 ⟶ 𝒢` and `ξ ∈ Ext¹_{𝒪_ℬ}(NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒥)`,
and none of the three is tied to `S` by a hypothesis of its own: `S` records the base ideal only
through its *inverse image* `S.I` on the site of the source, together with the requirement that
`S.idealInclusion` be the kernel of `f⁻¹(t^♯)` section by section, so the topos encoding of
(91.13.0.1) has no base-site ideal to construct `𝒥` as. (The ringed-space twin does, as
`baseIdealOnReduction t`; `Stacks.Sites.Conormal.idealSheaf` gives `Ker(t^♯)` only as a module
over the *thickened* base ring `𝒪_{ℬ'}`, and factoring its scalars through `𝒪_ℬ` from the
square-zero hypothesis is not in the library.) What ties the three to the problem is `hcompat`,
in which the difference between the restriction of the class of an extension and the image of
`ξ` is the obstruction class of **Stacks 08UG** for that extension — so instantiating this
theorem at the source's `𝒥 = Ker(t^♯)`, the source's `c` and the source's `ξ` is what makes the
conclusion the source's statement, and `hcompat` is then precisely the compatibility the source
omits. Left free, the three generalize the statement rather than restricting it: the source's
case is an instance.

The instance argument `(pullbackOnHomotopy S.f).HasLeftDerivedFunctor` is the existence assertion
of **Stacks 06YY** for this morphism. It is `Prop`-valued, so `Lf^*` is the same functor
whichever witness supplies it, and it is what
`Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy_hasLeftDerivedFunctor` produces
from a resolving datum; the resolution of **Stacks 06YS** asks for a site small on the nose, so
the datum is carried here rather than discharged, exactly as in the module that builds `Lf^*`.

**The left-hand side is the honest quotient.** It is
`CompatibleFirstOrderThickening.IsomorphismClasses S` — solutions of (91.13.0.1) modulo
isomorphism of solutions — reached through the unconditional `classesEquivCompatible`, and not
an auxiliary quotient. And the bijection is pinned, not merely asserted to exist:
`classesEquivDerivedExtFibre_apply` says it is `[𝒪'] ↦ E [𝒪']`.

**Universes.** The source ringed topos is `AlgebraicGeometry.RingedTopos.{u, u, u}`, inherited
from the companion file. The base ringed topos is `RingedTopos.{v', u', max v' u' w'}`: the naive
cotangent complex of the base thickening is a complex of sheaves of modules with sections in the
universe of the base structure sheaf, which asks for the sections of that sheaf to be at least as
large as the base site.

## References

* [Stacks Project, Tag 0GQ9](https://stacks.math.columbia.edu/tag/0GQ9)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 0GQ7](https://stacks.math.columbia.edu/tag/0GQ7)
* [Stacks Project, Tag 0GQ8](https://stacks.math.columbia.edu/tag/0GQ8), the remark the source
  of **Stacks 0GQ7** defers its omitted compatibility to.
* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3), the ringed-space twin.
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY), the derived pullback.
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open AlgebraicGeometry.RingedSpaceThickening (NaiveCotangentTwoTerm liftingObstruction
  liftingObstruction_eq_zero_iff)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Cohomology.DerivedPullbackOfToposHom

universe u v' u' w'

attribute [local instance 10000] HasDerivedCategory.standard

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', max v' u' w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{max v' u' w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{max v' u' w'} RingCat.{max v' u' w'})]
  [HasWeakSheafify X.J CommRingCat.{u}]
  [HasWeakSheafify B.J CommRingCat.{max v' u' w'}]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify B.J AddCommGrpCat.{max v' u' w'}]
  [B.J.WEqualsLocallyBijective AddCommGrpCat.{max v' u' w'}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  (S : RingedToposExtensionProblem X B)

/-! ### The two naive cotangent complexes -/

/-- `NL_{𝒪/𝒪_{ℬ'}}` as an object of `D(𝒪)`: the naive cotangent complex of `𝒪` over the
inverse image `f⁻¹𝒪_{ℬ'}` of the thickened base structure sheaf. -/
abbrev relativeNaiveCotangentObj :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  DerivedCategory.Q.obj
    (show CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ from
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) X.O
        S.toThickenedBase.fSharpInverseImage)

/-- `NL_{𝒪_ℬ/𝒪_{ℬ'}}` as an object of `D(𝒪_ℬ)`: the naive cotangent complex of the base first
order thickening, on the site of the base. -/
abbrev baseNaiveCotangentObj :
    DerivedCategory (SheafOfModules.{max v' u' w'} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)) :=
  DerivedCategory.Q.obj
    (show CochainComplex
        (SheafOfModules.{max v' u' w'} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)) ℤ from
      Stacks.SheafOfModules.naiveCotangentComplex.{v', u', max v' u' w', max v' u' w'} B.J
        S.baseExtension B.O S.baseReduction)

/-! ### The two `Ext¹` groups and the maps between them -/

section Derived

variable [(pullbackOnHomotopy S.f).HasLeftDerivedFunctor (quasiIsoTarget (Y := B))]

/-- `Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢)`, the group the classes of the square-zero extensions of
`f⁻¹𝒪_{ℬ'}`-algebras live in. -/
abbrev extOneRelativeNaiveCotangent :=
  DerivedCategory.Ext S.relativeNaiveCotangentObj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj S.G) 1

/-- `Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}`, the derived pullback of **Stacks 06YY** of the naive cotangent
complex of the base thickening, as an object of `D(𝒪)`. -/
abbrev derivedPullbackNaiveCotangent :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (derivedPullback S.f).obj S.baseNaiveCotangentObj

/-- `Ext¹_𝒪(Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒢)`, the group the two classes of **Stacks 0GQ9** are
compared in. -/
abbrev extOnePulledNaiveCotangent :=
  DerivedCategory.Ext S.derivedPullbackNaiveCotangent
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj S.G) 1

/-- The map `Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢) ⟶ Ext¹_𝒪(Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒢)` of **Stacks 0GQ9**:
precomposition with a comparison `q : Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}} ⟶ NL_{𝒪/𝒪_{ℬ'}}`. -/
def restrictDerivedExtClass
    (q : S.derivedPullbackNaiveCotangent ⟶ S.relativeNaiveCotangentObj)
    (z : S.extOneRelativeNaiveCotangent) : S.extOnePulledNaiveCotangent :=
  q ≫ z

/-- The comparison `Lf^*(ℱ[0]) ⟶ (f^*ℱ)[0]` of the derived with the degreewise pullback on a
module placed in degree `0`. -/
def derivedPullbackSingleObj
    (F : SheafOfModules.{max v' u' w'} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)) :
    (derivedPullback S.f).obj ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (S.f.toModulesHom.pullbackModules.obj F) :=
  let K := (CochainComplex.singleFunctor
    (SheafOfModules.{max v' u' w'} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)) 0).obj F
  (derivedPullback S.f).map ((DerivedCategory.singleFunctorIsoCompQh _ 0).hom.app F) ≫
    (derivedPullbackComparison S.f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      ((S.f.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex S.f.toModulesHom.pullbackModules
        (ComplexShape.up ℤ) 0).hom.app F)

/-- The coefficient map `Lf^*(𝒥[0]) ⟶ 𝒢[0]` attached to `c : f^*𝒥 ⟶ 𝒢`. -/
def coefficientExtMap
    {J : SheafOfModules.{max v' u' w'} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)}
    (c : S.f.toModulesHom.pullbackModules.obj J ⟶ S.G) :
    (derivedPullback S.f).obj ((DerivedCategory.singleFunctor _ 0).obj J) ⟶
      (DerivedCategory.singleFunctor _ 0).obj S.G :=
  S.derivedPullbackSingleObj J ≫ (DerivedCategory.singleFunctor _ 0).map c

/-- The image of `ξ ∈ Ext¹_{𝒪_ℬ}(NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒥)` in `Ext¹_𝒪(Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒢)`:
apply `Lf^*`, commute it past the shift, and push the coefficients along `c`.  This is the
first of the two maps the proof of **Stacks 0GQ9** constructs. -/
def pullbackExtClass
    {J : SheafOfModules.{max v' u' w'} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)}
    (c : S.f.toModulesHom.pullbackModules.obj J ⟶ S.G)
    (xi : DerivedCategory.Ext S.baseNaiveCotangentObj
      ((DerivedCategory.singleFunctor _ 0).obj J) 1) :
    S.extOnePulledNaiveCotangent :=
  (derivedPullback S.f).map xi ≫
    ((derivedPullback S.f).commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj J) ≫
    (S.coefficientExtMap c)⟦(1 : ℤ)⟧'

/-! ### Stacks 0GQ7 for the derived pullback -/

/-- **Stacks Project, Tag 0GQ7** for the derived pullback of **Stacks 06YY**.  A lift compatible
with `f` and the prescribed map `c` exists if and only if the class of the extension `𝒪'`,
restricted along a comparison `q : Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}} ⟶ NL_{𝒪/𝒪_{ℬ'}}`, agrees with the image
of `ξ ∈ Ext¹_{𝒪_ℬ}(NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒥)` in `Ext¹_𝒪(Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒢)`.

Unlike the degreewise form
`Deformation.ToposThickening.LiftDiagram.nonempty_lift_iff_eq_restrictExtClass`, the comparison
group here is the `Ext¹` of the *derived* pullback and the image of `ξ` is the constructed map
`pullbackExtClass`, not a hypothesis.  The compatible lifts are identified by `e` with the
factorizations of the difference homomorphism `δ` through the degree `0` term — Steps 1 to 3 of
the proof of **Stacks 08UG** — and `hcompat` is the compatibility between the constructions in
the proofs of **Stacks 0GQ5** and **Stacks 08UG** which the source omits, deferring to
**Stacks 0GQ8**: the difference of the two classes is the obstruction class. -/
@[stacks 0GQ7 "the criterion for the DERIVED pullback Lf^*NL_{O_B/O_B'} of the source's \
statement, with the image of ξ the constructed map pullbackExtClass. Carried, exactly as in the \
degreewise form of this tag: the two-term structure P with hP, the bijection e of Steps 1 to 3 \
of 08UG, and hcompat, the 0GQ5/08UG compatibility whose statement and proof the source itself \
omits, deferring to Tag 0GQ8"]
theorem nonempty_lift_iff_eq_pullbackExtClass
    {J : SheafOfModules.{max v' u' w'} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)}
    (c : S.f.toModulesHom.pullbackModules.obj J ⟶ S.G)
    (q : S.derivedPullbackNaiveCotangent ⟶ S.relativeNaiveCotangentObj)
    (P : NaiveCotangentTwoTerm (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0))
    (hP : P.obj = S.derivedPullbackNaiveCotangent)
    (δ : P.conormal ⟶ S.G) {Lift : Type*}
    (e : Lift ≃ {θ : P.base ⟶ S.G // P.d ≫ θ = δ})
    (xi : DerivedCategory.Ext S.baseNaiveCotangentObj
      ((DerivedCategory.singleFunctor _ 0).obj J) 1)
    (ζ : S.extOneRelativeNaiveCotangent)
    (hcompat : eqToHom hP ≫ (S.pullbackExtClass c xi - S.restrictDerivedExtClass q ζ) =
      P.conormalExtClass S.G δ) :
    Nonempty Lift ↔ S.pullbackExtClass c xi = S.restrictDerivedExtClass q ζ := by
  refine Iff.trans (liftingObstruction_eq_zero_iff P S.G δ e).symm ?_
  rw [show liftingObstruction P S.G δ =
      eqToHom hP ≫ (S.pullbackExtClass c xi - S.restrictDerivedExtClass q ζ) from hcompat.symm]
  constructor
  · intro h
    refine sub_eq_zero.1 ((cancel_epi (eqToHom hP)).1 ?_)
    rw [h, Limits.comp_zero]
  · intro h
    exact (congrArg (eqToHom hP ≫ ·) (sub_eq_zero.2 h)).trans Limits.comp_zero

/-! ### The criterion on isomorphism classes, and Stacks 0GQ9 -/

/-- The solutions of **Stacks 08UF** whose underlying square-zero extension of
`f⁻¹𝒪_{ℬ'}`-algebras lies in the class `p`.  A solution of the original problem is exactly such
an extension inducing the prescribed `c` on the base ideal, by `solutionEquivSquareZero`, so
this is the source's set of lifts of the extension compatible with `f` and `c`, read on the
class `p`. -/
abbrev CompatibleSolutionInClass
    (p : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem) : Type _ :=
  {Q : S.squareZeroProblem.CompatibleFirstOrderThickening //
    Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid S.squareZeroProblem) Q = p ∧
      S.IsCompatibleWithIdeal Q}

omit [HasWeakSheafify X.J CommRingCat] [HasWeakSheafify B.J CommRingCat]
  [X.J.HasSheafCompose (forget AddCommGrpCat)] [HasSheafify X.J AddCommGrpCat]
  [X.J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify B.J AddCommGrpCat]
  [B.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify X.J AddCommGrpCat]
  [(pullbackOnHomotopy S.f).HasLeftDerivedFunctor quasiIsoTarget] in
/-- A class of extensions of `f⁻¹𝒪_{ℬ'}`-algebras induces the prescribed map on the base ideal
exactly when it contains a solution, i.e. when `CompatibleSolutionInClass` is nonempty.  Both
sides say the same thing about the same extension, the condition being an invariant of the
isomorphism class by `isCompatibleWithIdeal_of_iso`. -/
theorem nonempty_compatibleSolutionInClass_iff
    (p : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem) :
    Nonempty (S.CompatibleSolutionInClass p) ↔ S.IsCompatibleWithIdealClass p := by
  induction p using Quotient.ind with
  | _ Q =>
    constructor
    · rintro ⟨Q', hmk, hc⟩
      exact S.isCompatibleWithIdeal_of_iso (Quotient.exact hmk).some hc
    · exact fun hc => ⟨Q, rfl, hc⟩

/-- **Stacks Project, Tag 0GQ7**, read on isomorphism classes: a class of square-zero extensions
of `f⁻¹𝒪_{ℬ'}`-algebras induces the prescribed map `c` on the base ideal — equivalently, is a
class of solutions of **Stacks 08UF** — exactly when its image under `E` restricts, along a
comparison `q : Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}} ⟶ NL_{𝒪/𝒪_{ℬ'}}`, to the image of `ξ`.

This is the cutting-out condition of **Stacks 0GQ9**, proved rather than assumed.  `E` is the
bijection of **Stacks 0GQ5**, and `P`, `hP`, `δ`, `e` and `hcompat` are the inputs of the
criterion for the derived pullback. -/
@[stacks 0GQ7 "the criterion for the DERIVED pullback, read on isomorphism classes of \
extensions: this is the cutting-out condition of 0GQ9, proved rather than assumed. Carried are \
the two-term structure P with hP, the per-class bijections e of Steps 1 to 3 of 08UG, the \
per-class 0GQ5/08UG compatibilities that the source defers to 0GQ8, and the 0GQ5 bijection E"]
theorem isCompatibleWithIdealClass_iff_eq_pullbackExtClass
    {J : SheafOfModules.{max v' u' w'} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)}
    (c : S.f.toModulesHom.pullbackModules.obj J ⟶ S.G)
    (E : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem ≃
      S.extOneRelativeNaiveCotangent)
    (q : S.derivedPullbackNaiveCotangent ⟶ S.relativeNaiveCotangentObj)
    (xi : DerivedCategory.Ext S.baseNaiveCotangentObj
      ((DerivedCategory.singleFunctor _ 0).obj J) 1)
    (P : NaiveCotangentTwoTerm (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0))
    (hP : P.obj = S.derivedPullbackNaiveCotangent)
    (δ : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem →
      (P.conormal ⟶ S.G))
    (e : ∀ p : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem,
      S.CompatibleSolutionInClass p ≃ {θ : P.base ⟶ S.G // P.d ≫ θ = δ p})
    (hcompat : ∀ p : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem,
      eqToHom hP ≫ (S.pullbackExtClass c xi - S.restrictDerivedExtClass q (E p)) =
        P.conormalExtClass S.G (δ p))
    (p : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem) :
    S.IsCompatibleWithIdealClass p ↔
      S.restrictDerivedExtClass q (E p) = S.pullbackExtClass c xi :=
  (S.nonempty_compatibleSolutionInClass_iff p).symm.trans
    ((S.nonempty_lift_iff_eq_pullbackExtClass c q P hP (δ p) (e p) xi (E p)
      (hcompat p)).trans eq_comm)

/-- **Stacks Project, Tag 0GQ9.**  In the situation of (91.13.0.1), with `ξ` the class of the
extension `𝒪_{ℬ'}` of `𝒪_ℬ` by `𝒥`, the isomorphism classes of solutions are canonically
bijective to the fibre of

`Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢) ⟶ Ext¹_𝒪(Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒢)`

over the image of `ξ`.  The bijection is the constructed map `[𝒪'] ↦ E [𝒪']`, as
`classesEquivDerivedExtFibre_apply` records; the fibre is the subtype of classes restricting to
that image.  The criterion telling which classes are classes of solutions is proved, in
`isCompatibleWithIdealClass_iff_eq_pullbackExtClass`; `E` is the bijection of **Stacks 0GQ5**,
`q` the comparison of naive cotangent complexes, and `P`, `hP`, `δ`, `e`, `hcompat` the inputs
of that criterion.

**The companion form.** The form that does not take the bijection `E` as an input is
`Deformation.ToposThickening.RingedToposExtensionProblem.classesEquivFibre` of
`StacksFrontier/Deformation/ToposThickening/SolutionClassesFibre.lean`, which exhibits
the isomorphism classes of solutions as the fibre over `0` of the compatibility obstruction on
the `Ext¹` of a fixed presentation. This declaration is the general
form: it takes the bijection `E` of [Stacks 0GQ5] at the real `NL_{𝒪/𝒪_{ℬ'}}` as an input, the
library's form of that tag classifying by the `Ext¹` of a fixed presentation instead, along with the
comparison `q` — [Stacks 08TZ] not being available in the spelling `Lf^*`'s comparison uses —
and the inputs `P`, `hP`, `δ`, `e`, `hcompat` of the [Stacks 0GQ7] criterion, which is proved
here rather than assumed. These are exactly the inputs of the ringed-space twin
[Stacks 0GQ3]. -/
def classesEquivDerivedExtFibre
    {J : SheafOfModules.{max v' u' w'} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)}
    (c : S.f.toModulesHom.pullbackModules.obj J ⟶ S.G)
    (E : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem ≃
      S.extOneRelativeNaiveCotangent)
    (q : S.derivedPullbackNaiveCotangent ⟶ S.relativeNaiveCotangentObj)
    (xi : DerivedCategory.Ext S.baseNaiveCotangentObj
      ((DerivedCategory.singleFunctor _ 0).obj J) 1)
    (P : NaiveCotangentTwoTerm (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0))
    (hP : P.obj = S.derivedPullbackNaiveCotangent)
    (δ : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem →
      (P.conormal ⟶ S.G))
    (e : ∀ p : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem,
      S.CompatibleSolutionInClass p ≃ {θ : P.base ⟶ S.G // P.d ≫ θ = δ p})
    (hcompat : ∀ p : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem,
      eqToHom hP ≫ (S.pullbackExtClass c xi - S.restrictDerivedExtClass q (E p)) =
        P.conormalExtClass S.G (δ p)) :
    CompatibleFirstOrderThickening.IsomorphismClasses S ≃
      {z : S.extOneRelativeNaiveCotangent //
        S.restrictDerivedExtClass q z = S.pullbackExtClass c xi} :=
  S.classesEquivCompatible.trans
    (E.subtypeEquiv
      (S.isCompatibleWithIdealClass_iff_eq_pullbackExtClass c E q xi P hP δ e hcompat))

/-- The bijection of **Stacks 0GQ9** is the constructed map `[𝒪'] ↦ E [𝒪']`, not an arbitrary
one: it sends the class of a solution to the class of its underlying square-zero extension of
`f⁻¹𝒪_{ℬ'}`-algebras, read through the bijection of **Stacks 0GQ5**.  This is the "canonically"
of the source's "canonically bijective".

This records the canonicity of `classesEquivDerivedExtFibre` and takes the same inputs, among
them the bijection `E` of [Stacks 0GQ5]; the form that does not take `E` as an input is
`Deformation.ToposThickening.RingedToposExtensionProblem.classesEquivFibre` of
`StacksFrontier/Deformation/ToposThickening/SolutionClassesFibre.lean`. -/
theorem classesEquivDerivedExtFibre_apply
    {J : SheafOfModules.{max v' u' w'} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)}
    (c : S.f.toModulesHom.pullbackModules.obj J ⟶ S.G)
    (E : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem ≃
      S.extOneRelativeNaiveCotangent)
    (q : S.derivedPullbackNaiveCotangent ⟶ S.relativeNaiveCotangentObj)
    (xi : DerivedCategory.Ext S.baseNaiveCotangentObj
      ((DerivedCategory.singleFunctor _ 0).obj J) 1)
    (P : NaiveCotangentTwoTerm (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0))
    (hP : P.obj = S.derivedPullbackNaiveCotangent)
    (δ : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem →
      (P.conormal ⟶ S.G))
    (e : ∀ p : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem,
      S.CompatibleSolutionInClass p ≃ {θ : P.base ⟶ S.G // P.d ≫ θ = δ p})
    (hcompat : ∀ p : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem,
      eqToHom hP ≫ (S.pullbackExtClass c xi - S.restrictDerivedExtClass q (E p)) =
        P.conormalExtClass S.G (δ p))
    (s : CompatibleFirstOrderThickening.IsomorphismClasses S) :
    (S.classesEquivDerivedExtFibre c E q xi P hP δ e hcompat s).1 =
      E (S.classesEquivCompatible s).1 :=
  rfl

end Derived

end Deformation.ToposThickening.RingedToposExtensionProblem

end
