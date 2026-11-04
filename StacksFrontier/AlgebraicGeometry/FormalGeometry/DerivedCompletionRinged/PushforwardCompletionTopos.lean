module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.FiniteTypeReflector
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardTopoi
public import StacksFrontier.CategoryTheory.Adjunction.ReflectiveRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
import StacksCore.Tactic.StacksAttribute

/-!
# Derived completion and the derived direct image of a morphism of ringed topoi

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed topoi, given as the two-field
`AlgebraicGeometry.RingedToposHom`, and let `ℐ ⊆ 𝒪`, `ℐ' ⊆ 𝒪'` be sheaves of ideals.
[Stacks, Tag 099K] says that when `f^♯(f^{-1}ℐ) ⊆ ℐ'` and both ideals are of finite type, `Rf_*`
sends `D_comp(𝒪', ℐ')` into `D_comp(𝒪, ℐ)`, and the resulting functor has a left adjoint
`Lf^*_comp`, namely `Lf^*` followed by derived completion.

This file proves the tag. The functors and the adjunction are first built from their two
inputs, each stated as exactly what is consumed:

* that `Rf_*` carries `D_comp(𝒪', ℐ')` into `D_comp(𝒪, ℐ)` — the content of
  [Stacks, Tag 099J];
* that `D_comp(𝒪', ℐ') ⊆ D(𝒪')` is reflective — the content of [Stacks, Tag 099F];

and then both inputs are supplied: Tag 099J by
`AlgebraicGeometry.RingedToposHom.derivedPushforward_isDerivedComplete`, for an arbitrary `ℐ`
and `ℐ'`, and Tag 099F by the instance
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete`, for `ℐ'` of finite type.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.derivedCompletePushforward`: `Rf_*` as a functor
  `D_comp(𝒪', ℐ') ⥤ D_comp(𝒪, ℐ)`.
* `AlgebraicGeometry.RingedToposHom.derivedCompletePullback`: `Lf^*_comp`, `Lf^*` followed by
  derived completion along `ℐ'`.
* `AlgebraicGeometry.RingedToposHom.derivedCompletePullbackPushforwardAdjunction`:
  **Tag 099K, second statement**, the adjunction `Lf^*_comp ⊣ Rf_*` on the derived-complete
  objects, for `ℐ'` of finite type.

## Main results

* `AlgebraicGeometry.RingedToposHom.isDerivedComplete_derivedPushforward`: **Tag 099K, first
  statement**, `Rf_*` sends `D_comp(𝒪', ℐ')` into `D_comp(𝒪, ℐ)`.
* `AlgebraicGeometry.RingedToposHom.derivedCompletePullback_comp_ι`: `Lf^*_comp` read in `D(𝒪')`
  is `Lf^*` followed by the derived completion functor.

## Implementation notes

The adjunction is `CategoryTheory.Adjunction.restrictReflective` applied to the adjunction
`Lf^* ⊣ Rf_*` of [Stacks, Tag 07A6] for a morphism of ringed topoi,
`Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunctionOfToposHom`: this is
the source's chain `Hom(K, Rf_*M) = Hom(Lf^*K, M) = Hom(Lf^*_comp K, M)`.

The derived-complete objects are those of the ringed site `RingedTopos.toRingedSite` presenting
each ringed topos; its sheaf of rings is the one `Rf_*` and `Lf^*` are built over, by definition.

The source asks both ideals to be of finite type. Only `ℐ'` is: Tag 099J, which is all that is
used about `ℐ`, holds for an arbitrary sheaf of ideals. The ringed topoi are
`AlgebraicGeometry.RingedTopos.{u, u, u}`, presented by sites small in the universe of the
sections of their structure sheaves, which is the generality of [Stacks, Tag 03CR] through which
Tag 099J is proved for a morphism of ringed topoi.

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 099K](https://stacks.math.columbia.edu/tag/099K)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Cohomology

universe u

namespace AlgebraicGeometry.RingedToposHom

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))))
  (I' : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))))

section Pushforward

variable (hRf : ∀ M : ObjectProperty.FullSubcategory
      (RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I'),
    RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I
      ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj M.1))

/-- `Rf_*` as a functor `D_comp(𝒪', ℐ') ⥤ D_comp(𝒪, ℐ)`, given that it carries derived-complete
objects to derived-complete objects. -/
def derivedCompletePushforwardOfPreserves :
    ObjectProperty.FullSubcategory (RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I') ⥤
      ObjectProperty.FullSubcategory
        (RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I) :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ DerivedPushforward.derivedPushforward (X := X) (Y := Y) f)
    hRf

variable
  [(ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I')).IsRightAdjoint]

/-- `Lf^*_comp : D_comp(𝒪, ℐ) ⥤ D_comp(𝒪', ℐ')`, the derived pullback `Lf^*` of
[Stacks, Tag 06YY] followed by the derived completion along `ℐ'`, for an `ℐ'` whose
derived-complete objects are reflective in `D(𝒪')`. -/
def derivedCompletePullback :
    ObjectProperty.FullSubcategory (RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I) ⥤
      ObjectProperty.FullSubcategory
        (RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I') :=
  ObjectProperty.ι _ ⋙ DerivedPullbackOfToposHom.derivedPullback (X := X) (Y := Y) f ⋙
    (ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I')).leftAdjoint

/-- `Lf^*_comp` read in `D(𝒪')` is `Lf^*` followed by the derived completion functor
`K ↦ K^∧` of `ReflectorCompletion.lean`, on the nose. -/
theorem derivedCompletePullback_comp_ι :
    derivedCompletePullback f I I' ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ DerivedPullbackOfToposHom.derivedPullback (X := X) (Y := Y) f ⋙
        RingedSite.derivedCompletion X.toRingedSite I' :=
  rfl

/-- `Lf^*_comp ⊣ Rf_*` on the derived-complete objects, for an `ℐ'` whose derived-complete
objects are reflective and given that `Rf_*` preserves derived completeness: the restriction of
`Lf^* ⊣ Rf_*` ([Stacks, Tag 07A6]) along the reflection onto `D_comp(𝒪', ℐ')`. -/
def derivedCompletePullbackAdjunctionOfPreserves :
    derivedCompletePullback f I I' ⊣ derivedCompletePushforwardOfPreserves f I I' hRf :=
  (DerivedPushforward.derivedPullbackPushforwardAdjunctionOfToposHom
    f).restrictReflective _ _ hRf

end Pushforward

section FiniteType

open Stacks.Sheaves.ToposPullback in
/-- The hypothesis of [Stacks, Tag 099J] and [Stacks, Tag 099K] on the two sheaves of ideals:
`f^♯ : f^{-1}𝒪 ⟶ 𝒪'` sends `f^{-1}ℐ` into `ℐ'`. On underlying sheaves of sets, the inverse image
of the inclusion `ℐ ↪ 𝒪` followed by `f^♯` factors through `ℐ' ↪ 𝒪'`; this is the hypothesis of
`AlgebraicGeometry.RingedToposHom.derivedPushforward_isDerivedComplete`. -/
abbrev IdealCompatible : Prop :=
  ∃ φ : f.toToposHom.inverseImage.obj
        ((Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).obj I.toSheafOfModules) ⟶
        (Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))).obj I'.toSheafOfModules,
      f.toToposHom.inverseImage.map
          ((Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).map I.ι) ≫
        X.forgetRing.map f.fSharpInverseImage =
          φ ≫ (Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))).map I'.ι


/-- [Stacks, Tag 099F] for the ringed site presenting a ringed topos: for `ℐ'` of finite type the
inclusion `D_comp(𝒪', ℐ') ⥤ D(𝒪')` has a left adjoint. This is
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete` at `X.toRingedSite`, restated
because instance search does not find that instance at a ringed site of this form. -/
instance isRightAdjoint_ι_isDerivedComplete_toRingedSite [I'.toSheafOfModules.IsFiniteType] :
    (ObjectProperty.ι
      (RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I')).IsRightAdjoint :=
  RingedSite.isRightAdjoint_ι_isDerivedComplete X.toRingedSite I'

/-- **[Stacks, Tag 099K], first statement.** Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism
of ringed topoi and let `ℐ ⊆ 𝒪`, `ℐ' ⊆ 𝒪'` be sheaves of ideals such that `f^♯` sends `f^{-1}ℐ`
into `ℐ'`. Then `Rf_*` sends `D_comp(𝒪', ℐ')` into `D_comp(𝒪, ℐ)`: if `K` is derived complete
along `ℐ'`, then `Rf_*K` is derived complete along `ℐ`.

The source asks `ℐ` and `ℐ'` to be of finite type; neither hypothesis is needed. This is
[Stacks, Tag 099J], `AlgebraicGeometry.RingedToposHom.derivedPushforward_isDerivedComplete`,
read in the variables of Tag 099K, as the source's proof says. -/
@[stacks 099K "first statement: `Rf_*` sends `D_comp(𝒪', ℐ')` into `D_comp(𝒪, ℐ)`; the
  finite-type hypotheses on `ℐ` and `ℐ'` are not needed"]
theorem isDerivedComplete_derivedPushforward (hI : IdealCompatible f I I')
    (K : DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))))
    (hK : RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I' K) :
    RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I
      ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj K) :=
  derivedPushforward_isDerivedComplete f I I' hI K hK

/-- `Rf_*` as a functor `D_comp(𝒪', ℐ') ⥤ D_comp(𝒪, ℐ)`, for `f^♯(f^{-1}ℐ) ⊆ ℐ'`: the first
statement of [Stacks, Tag 099K], `isDerivedComplete_derivedPushforward`, read as a functor. It is
the right adjoint of `derivedCompletePullbackPushforwardAdjunction`. -/
def derivedCompletePushforward
    (hI : IdealCompatible f I I') :
    ObjectProperty.FullSubcategory (RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I') ⥤
      ObjectProperty.FullSubcategory
        (RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I) :=
  derivedCompletePushforwardOfPreserves f I I'
    (fun M ↦ isDerivedComplete_derivedPushforward f I I' hI M.1 M.2)

/-- **[Stacks, Tag 099K], second statement.** Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a
morphism of ringed topoi and let `ℐ ⊆ 𝒪`, `ℐ' ⊆ 𝒪'` be sheaves of ideals such that `f^♯` sends
`f^{-1}ℐ` into `ℐ'`, with `ℐ'` of finite type. Then `Rf_*` sends `D_comp(𝒪', ℐ')` into
`D_comp(𝒪, ℐ)` (`isDerivedComplete_derivedPushforward`, read as the functor
`derivedCompletePushforward`), and this functor has a left adjoint `Lf^*_comp`, which is `Lf^*`
followed by derived completion along `ℐ'` (`derivedCompletePullback`, and
`derivedCompletePullback_comp_ι`).

The derived completion functor is the left adjoint of the inclusion `D_comp(𝒪', ℐ') ⥤ D(𝒪')`
that [Stacks, Tag 099F] provides for `ℐ'` of finite type, the instance
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete`. The source also asks `ℐ` to be
of finite type; that is not needed, since [Stacks, Tag 099J] holds for an arbitrary `ℐ`. The two
ringed topoi are presented by sites small in the universe of the sections of their structure
sheaves, as in [Stacks, Tag 03CR], through which Tag 099J is proved. -/
@[stacks 099K "second statement: the left adjoint `Lf^*_comp` of `Rf_*` on the derived-complete
  objects, `Lf^*` followed by derived completion; the finite-type hypothesis on `ℐ` is not
  needed"]
def derivedCompletePullbackPushforwardAdjunction [I'.toSheafOfModules.IsFiniteType]
    (hI : IdealCompatible f I I') :
    derivedCompletePullback f I I' ⊣ derivedCompletePushforward f I I' hI :=
  derivedCompletePullbackAdjunctionOfPreserves f I I' _

end FiniteType

end AlgebraicGeometry.RingedToposHom

end
