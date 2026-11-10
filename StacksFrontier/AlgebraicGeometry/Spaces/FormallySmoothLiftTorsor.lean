module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UndeformedLiftDerivationAction
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The lifts of an infinitesimal lifting problem are a torsor under the local derivations

Let `f : F ⟶ G` be a morphism of algebraic spaces over a scheme `S`, let `i : T ⟶ T'` be a
square-zero closed immersion of objects of the big fppf site, and let `x` be a section of `F`
over `T` and `y` a section of `G` over `T'` agreeing under `f`.  The *lifts* of that
infinitesimal lifting problem are the sections `z` of `F` over `T'` with `z|_T = x` and
`f(z) = y`; formal smoothness of `f` asks that there be one.

This file identifies those lifts with the lifts of a morphism along a thickening into an
**undeformed** target, and so equips them with the simply transitive action of the
`𝒪_T`-linear maps `x^*Ω_{F/G} ⟶ 𝒞_{T/T'}`: once one lift is given, the lifts are in bijection
with those maps.  This is [Stacks Project, Tag 061C] at the lifting problem which step (II) of
[Stacks Project, Tag 04AM] is about, and it is unconditional.

The dictionary is the one the source uses in Remark [Stacks Project, Tag 061D]: the thickening
of the *source* is `T ⊂ T'`, read as the algebraic spaces the two schemes represent, and the
target is not thickened, so the conormal condition (3) of [Stacks Project, Tag 061A] is vacuous
by `AlgebraicGeometry.Space.isZero_conormalModule_top` and the lifts are a single torsor rather
than a union of torsors.

## Main definitions

* `AlgebraicGeometry.Space.liftingProblemAmbient` is the algebraic space `T'` represents.
* `AlgebraicGeometry.Space.squareZeroRangeIso` identifies the representable presheaf of `T`
  with the image of `yoneda.map i`, which is the subspace presenting `T` as a thickening of
  `T'`.
* `AlgebraicGeometry.Space.liftingProblemThickening`, `…liftingProblemRestriction`,
  `…liftingProblemMap` and `…liftingProblemBase` are the thickening `T ⊂ T'`, the morphism `x`
  out of it, the morphism `f` and the structure morphism `y`, as data of algebraic spaces.
* `AlgebraicGeometry.Space.InfinitesimalLifts` is the set of lifts of the lifting problem.
* `AlgebraicGeometry.Space.infinitesimalLiftsEquiv` identifies it with the lifts into an
  undeformed target along the thickening `T ⊂ T'`.
* `AlgebraicGeometry.Space.infinitesimalLiftsDiff` is the difference of two lifts, the `θ` of
  Equation [Stacks Project, Tag 0619].

## Main results

* `AlgebraicGeometry.Space.isUndeformedLift_iff_isLift`: a section of `F` over `T'` is a lift of
  the infinitesimal lifting problem exactly when the morphism of algebraic spaces it names is a
  lift of `x` over `G` along the thickening `T ⊂ T'`.
* `AlgebraicGeometry.Space.infinitesimalLiftsDiff_bijective`: **the lifts are a torsor.**  The
  difference from a given lift is a bijection from the lifts onto the `𝒪_T`-linear maps
  `x^*Ω_{F/G} ⟶ 𝒞_{T/T'}`.
* `AlgebraicGeometry.Space.infinitesimalLiftsDiffEquiv`: that bijection, bundled.
* `AlgebraicGeometry.Space.infinitesimalLiftsDiff_self` and
  `AlgebraicGeometry.Space.infinitesimalLiftsDiff_add_infinitesimalLiftsDiff`: a lift does not
  differ from itself and the differences along a chain of three lifts add up.
* `AlgebraicGeometry.Space.existsUnique_infinitesimalLiftsDiff_eq`: exactly one lift has a
  prescribed difference from a given lift.

## Implementation notes

**Where the affineness of `T` and `T'` went.**  Nowhere: it is not used.  The definition of
`AlgebraicGeometry.Space.FormallySmooth` tests only affine objects of the site, but the torsor
statement below holds for every square-zero closed immersion, so no affineness hypothesis is
carried.

**Why the image of `yoneda.map i` and not `T` itself.**  The thickening datum
`AlgebraicGeometry.Space.IsFirstOrderThickening` is a property of a *subfunctor* of the ambient
space, and the subfunctor presenting `T` inside `T'` is the image of `yoneda.map i`, which is
what `AlgebraicGeometry.Space.isFirstOrderThickening_range_yoneda_map` proves to be a
first-order thickening.  That subfunctor is isomorphic to `yoneda.obj T` — the Yoneda image of a
square-zero closed immersion is a monomorphism, so `CategoryTheory.Subfunctor.toRange` is an
isomorphism — and `AlgebraicGeometry.Space.squareZeroRangeIso` is that isomorphism; it is what
turns the section `x` into a morphism out of the subspace.

**What this does not do.**  The statements below are about the lifts over `T'` itself, which is
one object of the small étale site of `T'`.  They are the torsor property of
[Stacks Project, Tag 061C] over that one object, not the pseudo-torsor *sheaf* of
[Stacks Project, Tag 061A]: making the action compatible with étale restriction needs the
functoriality in the étale source of
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso`, which the "What is not proved"
section of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean` records as
open, and the compatibility of `AlgebraicGeometry.Space.undeformedLiftDiff` with étale
restriction, which nothing in this development carries.  Those two are what separate these
statements from step (II) of [Stacks Project, Tag 04AM], which also needs them in order to feed
the triviality of a torsor with vanishing first cohomology.

## References

* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The thickening presented by a square-zero closed immersion of the site -/

variable {T T' : BigFppfOver B S hS}

/-- The algebraic space represented by an object of the site, with its presheaf written out as
the representable presheaf.  This is `AlgebraicGeometry.schemeSpace`, spelled so that the
inclusion of a subfunctor into it has `yoneda.obj T'` as its literal codomain; otherwise every
reassociation of a composite out of the thickening leaves the rewriter with two spellings of
that presheaf which are equal only after unfolding two semireducible definitions. -/
abbrev liftingProblemAmbient (T' : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩

/-- **The thickening `T ⊂ T'` presented by a square-zero closed immersion of the site**, as a
closed subspace of the algebraic space `T'` represents.  This is
`AlgebraicGeometry.Space.isFirstOrderThickening_range_yoneda_map`. -/
abbrev liftingProblemThickening (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i) :
    ClosedSubspaces B S hS (liftingProblemAmbient B S hS T').1 :=
  ⟨Subfunctor.range (yoneda.map i), (isFirstOrderThickening_range_yoneda_map B S hS i hi).1.1⟩

/-- **The image of the Yoneda map of a square-zero closed immersion is the representable
presheaf of its source.**  A closed immersion of schemes is a monomorphism, the functor to
schemes is faithful and the Yoneda embedding preserves monomorphisms, so
`CategoryTheory.Subfunctor.toRange` is an isomorphism. -/
def squareZeroRangeIso (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i) :
    yoneda.obj T ≅ (liftingProblemThickening B S hS i hi).1.toFunctor :=
  haveI : _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map i) := hi.1
  haveI : Mono i := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  haveI : Mono (yoneda.map i) := inferInstance
  asIso (Subfunctor.toRange (yoneda.map i))

/-- The isomorphism of `AlgebraicGeometry.Space.squareZeroRangeIso` followed by the inclusion of
the image is the Yoneda map itself. -/
theorem squareZeroRangeIso_hom_ι (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i) :
    (squareZeroRangeIso B S hS i hi).hom ≫ (liftingProblemThickening B S hS i hi).1.ι =
      yoneda.map i :=
  Subfunctor.toRange_ι _

/-- The thickening of `AlgebraicGeometry.Space.liftingProblemThickening` is of first order. -/
theorem isFirstOrderThickening_liftingProblemThickening (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) :
    IsFirstOrderThickening B S hS (liftingProblemAmbient B S hS T')
      (liftingProblemThickening B S hS i hi).1 :=
  isFirstOrderThickening_range_yoneda_map B S hS i hi

/-! ### The lifting problem as a lifting problem into an undeformed target -/

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
  (hG : IsAlgebraicSpace B S hS G)

/-- The morphism `f : F ⟶ G` of the lifting problem, as a morphism of algebraic spaces. -/
abbrev liftingProblemMap (f : F ⟶ G) :
    (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk f

/-- The section `y` of `G` over `T'` of the lifting problem, as the structure morphism of the
ambient space of the thickening over the target. -/
abbrev liftingProblemBase (y : G.obj (op T')) :
    liftingProblemAmbient B S hS T' ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (yonedaEquiv.symm y)

/-- The section `x` of `F` over `T` of the lifting problem, as a morphism out of the thickening:
the inverse of `AlgebraicGeometry.Space.squareZeroRangeIso` followed by `x`. -/
abbrev liftingProblemRestriction (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i)
    (x : F.obj (op T)) :
    (⟨(liftingProblemThickening B S hS i hi).1.toFunctor,
        (liftingProblemThickening B S hS i hi).2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk ((squareZeroRangeIso B S hS i hi).inv ≫ yonedaEquiv.symm x)

/-- The group of `𝒪_T`-linear maps `x^*Ω_{F/G} ⟶ 𝒞_{T/T'}` acting on the lifts of the
infinitesimal lifting problem. -/
abbrev LiftingProblemDerivations (f : F ⟶ G) (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) :=
  UndeformedLiftDerivations B S hS (liftingProblemThickening B S hS i hi)
    (liftingProblemRestriction B S hS hF i hi x) (liftingProblemMap B S hS hF hG f)

/-- Sections of `F` over `T'` are the same thing as morphisms of algebraic spaces from the space
`T'` represents into `F`. -/
def liftingProblemHomEquiv :
    (liftingProblemAmbient B S hS T' ⟶ (⟨F, hF⟩ : AlgebraicSpaces B S hS)) ≃
      F.obj (op T') where
  toFun c := yonedaEquiv c.hom
  invFun z := ObjectProperty.homMk (yonedaEquiv.symm z)
  left_inv c := ObjectProperty.hom_ext _ (yonedaEquiv.symm_apply_apply c.hom)
  right_inv z := yonedaEquiv.apply_symm_apply z

/-- The morphism of algebraic spaces named by a section of `F` over `T'`. -/
theorem liftingProblemHomEquiv_symm_hom (z : F.obj (op T')) :
    ((liftingProblemHomEquiv B S hS hF).symm z).hom = yonedaEquiv.symm z := rfl

/-- **The first clause of the lifting condition is the restriction clause.**  A morphism out of
the ambient space of the thickening restricts to `x` on the thickening exactly when the section
it names restricts to `x` along `i`. -/
theorem subspaceInclusion_comp_eq_iff (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) (z : F.obj (op T')) :
    subspaceInclusion B S hS (liftingProblemAmbient B S hS T')
          (liftingProblemThickening B S hS i hi) ≫
        (ObjectProperty.homMk (yonedaEquiv.symm z) :
          liftingProblemAmbient B S hS T' ⟶ (⟨F, hF⟩ : AlgebraicSpaces B S hS)) =
      liftingProblemRestriction B S hS hF i hi x ↔ F.map i.op z = x := by
  have hι := squareZeroRangeIso_hom_ι B S hS i hi
  rw [ObjectProperty.hom_ext_iff]
  change (liftingProblemThickening B S hS i hi).1.ι ≫ yonedaEquiv.symm z =
      (squareZeroRangeIso B S hS i hi).inv ≫ yonedaEquiv.symm x ↔ _
  refine ⟨fun hh => yonedaEquiv.symm.injective ?_, fun hh => ?_⟩
  · rw [← yonedaEquiv_symm_naturality_left, ← hι, Category.assoc, hh, Iso.hom_inv_id_assoc]
  · have key : yoneda.map i ≫ yonedaEquiv.symm z = yonedaEquiv.symm x := by
      rw [yonedaEquiv_symm_naturality_left, hh]
    rw [← Iso.inv_hom_id_assoc (squareZeroRangeIso B S hS i hi)
      ((liftingProblemThickening B S hS i hi).1.ι ≫ yonedaEquiv.symm z),
      ← Category.assoc (squareZeroRangeIso B S hS i hi).hom, hι, key]

/-- **The second clause of the lifting condition is the clause over the target.**  A morphism out
of the ambient space of the thickening lies over `G` with structure morphism `y` exactly when the
section it names maps to `y` under `f`. -/
theorem comp_liftingProblemMap_eq_iff (f : F ⟶ G) (y : G.obj (op T')) (z : F.obj (op T')) :
    (ObjectProperty.homMk (yonedaEquiv.symm z) :
          liftingProblemAmbient B S hS T' ⟶ (⟨F, hF⟩ : AlgebraicSpaces B S hS)) ≫
        liftingProblemMap B S hS hF hG f =
      liftingProblemBase B S hS hG y ↔ f.app (op T') z = y := by
  rw [ObjectProperty.hom_ext_iff]
  change yonedaEquiv.symm z ≫ f = yonedaEquiv.symm y ↔ _
  rw [yonedaEquiv_symm_naturality_right]
  exact yonedaEquiv.symm.apply_eq_iff_eq

/-- **A section of `F` over `T'` is a lift of the infinitesimal lifting problem exactly when the
morphism of algebraic spaces it names is a lift of `x` over `G` along the thickening
`T ⊂ T'`.**  The two clauses match up one by one: restricting to the thickening is restricting
along `i`, and lying over `G` with structure morphism `y` is mapping to `y` under `f`. -/
theorem isUndeformedLift_iff_isLift (f : F ⟶ G) (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) (y : G.obj (op T'))
    (z : F.obj (op T')) :
    IsUndeformedLift B S hS (liftingProblemThickening B S hS i hi)
        (liftingProblemRestriction B S hS hF i hi x) (liftingProblemMap B S hS hF hG f)
        (liftingProblemBase B S hS hG y)
        ((liftingProblemHomEquiv B S hS hF).symm z) ↔
      IsLift f i x y z :=
  and_congr (subspaceInclusion_comp_eq_iff B S hS hF i hi x z)
    (comp_liftingProblemMap_eq_iff B S hS hF hG f y z)

/-! ### The torsor -/

/-- The lifts of the infinitesimal lifting problem: the sections `z` of `F` over `T'` with
`z|_T = x` and `f(z) = y`. -/
abbrev InfinitesimalLifts (f : F ⟶ G) (i : T ⟶ T') (x : F.obj (op T)) (y : G.obj (op T')) :=
  {z : F.obj (op T') // IsLift f i x y z}

/-- The lifts of the infinitesimal lifting problem are the lifts of `x` over `G` along the
thickening `T ⊂ T'` into the undeformed target `F`. -/
def infinitesimalLiftsEquiv (f : F ⟶ G) (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) (y : G.obj (op T')) :
    InfinitesimalLifts B S hS f i x y ≃
      UndeformedLifts B S hS (liftingProblemThickening B S hS i hi)
        (liftingProblemRestriction B S hS hF i hi x) (liftingProblemMap B S hS hF hG f)
        (liftingProblemBase B S hS hG y) :=
  Equiv.subtypeEquiv (liftingProblemHomEquiv B S hS hF).symm
    fun z => (isUndeformedLift_iff_isLift B S hS hF hG f i hi x y z).symm

/-- **The difference of two lifts of the infinitesimal lifting problem**, the `𝒪_T`-linear map
`x^*Ω_{F/G} ⟶ 𝒞_{T/T'}` of [Stacks Project, Tag 0618] with Equation
[Stacks Project, Tag 0619]. -/
def infinitesimalLiftsDiff (f : F ⟶ G) (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) (y : G.obj (op T'))
    (z z' : InfinitesimalLifts B S hS f i x y) :
    LiftingProblemDerivations B S hS hF hG f i hi x :=
  undeformedLiftsDiff B S hS (liftingProblemThickening B S hS i hi)
    (isFirstOrderThickening_liftingProblemThickening B S hS i hi)
    (liftingProblemRestriction B S hS hF i hi x) (liftingProblemMap B S hS hF hG f)
    (liftingProblemBase B S hS hG y)
    (infinitesimalLiftsEquiv B S hS hF hG f i hi x y z)
    (infinitesimalLiftsEquiv B S hS hF hG f i hi x y z')

/-- **The lifts of an infinitesimal lifting problem for a morphism of algebraic spaces are a
torsor under the local derivations.**  Once one lift `z` is given, the difference from `z` is a
bijection from the lifts onto the `𝒪_T`-linear maps `x^*Ω_{F/G} ⟶ 𝒞_{T/T'}`.

This is [Stacks Project, Tag 061C] at the lifting problem of step (II) of
[Stacks Project, Tag 04AM], over the ambient space `T'` of the thickening.  It is
unconditional: the content is [Stacks Project, Tag 04D0] for an undeformed target,
`AlgebraicGeometry.Space.undeformedLiftsDiff_bijective`. -/
@[ega "IV 16.5.14" "more general"]
theorem infinitesimalLiftsDiff_bijective (f : F ⟶ G) (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) (y : G.obj (op T'))
    (z : InfinitesimalLifts B S hS f i x y) :
    Function.Bijective (infinitesimalLiftsDiff B S hS hF hG f i hi x y z) :=
  (undeformedLiftsDiff_bijective B S hS (liftingProblemThickening B S hS i hi)
    (isFirstOrderThickening_liftingProblemThickening B S hS i hi)
    (liftingProblemRestriction B S hS hF i hi x) (liftingProblemMap B S hS hF hG f)
    (liftingProblemBase B S hS hG y)
    (infinitesimalLiftsEquiv B S hS hF hG f i hi x y z)).comp
      (infinitesimalLiftsEquiv B S hS hF hG f i hi x y).bijective

/-- **The lifts of an infinitesimal lifting problem, in bijection with the local derivations**,
once one lift is given.  This is the bijection of [Stacks Project, Tag 061C] at the lifting
problem of step (II) of [Stacks Project, Tag 04AM]. -/
@[ega "IV 16.5.14" "more general"]
def infinitesimalLiftsDiffEquiv (f : F ⟶ G) (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) (y : G.obj (op T'))
    (z : InfinitesimalLifts B S hS f i x y) :
    InfinitesimalLifts B S hS f i x y ≃ LiftingProblemDerivations B S hS hF hG f i hi x :=
  Equiv.ofBijective _ (infinitesimalLiftsDiff_bijective B S hS hF hG f i hi x y z)

/-- **A lift does not differ from itself.** -/
theorem infinitesimalLiftsDiff_self (f : F ⟶ G) (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) (y : G.obj (op T'))
    (z : InfinitesimalLifts B S hS f i x y) :
    infinitesimalLiftsDiff B S hS hF hG f i hi x y z z = 0 :=
  undeformedLiftsDiff_self B S hS (liftingProblemThickening B S hS i hi)
    (isFirstOrderThickening_liftingProblemThickening B S hS i hi)
    (liftingProblemRestriction B S hS hF i hi x) (liftingProblemMap B S hS hF hG f)
    (liftingProblemBase B S hS hG y)
    (infinitesimalLiftsEquiv B S hS hF hG f i hi x y z)

/-- **The differences along a chain of three lifts add up**, the cocycle identity. -/
theorem infinitesimalLiftsDiff_add_infinitesimalLiftsDiff (f : F ⟶ G) (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) (y : G.obj (op T'))
    (z z' z'' : InfinitesimalLifts B S hS f i x y) :
    infinitesimalLiftsDiff B S hS hF hG f i hi x y z z' +
        infinitesimalLiftsDiff B S hS hF hG f i hi x y z' z'' =
      infinitesimalLiftsDiff B S hS hF hG f i hi x y z z'' :=
  undeformedLiftsDiff_add_undeformedLiftsDiff B S hS (liftingProblemThickening B S hS i hi)
    (isFirstOrderThickening_liftingProblemThickening B S hS i hi)
    (liftingProblemRestriction B S hS hF i hi x) (liftingProblemMap B S hS hF hG f)
    (liftingProblemBase B S hS hG y)
    (infinitesimalLiftsEquiv B S hS hF hG f i hi x y z)
    (infinitesimalLiftsEquiv B S hS hF hG f i hi x y z')
    (infinitesimalLiftsEquiv B S hS hF hG f i hi x y z'')

/-- **Exactly one lift of the infinitesimal lifting problem has a prescribed difference from a
given lift.**  This is [Stacks Project, Tag 04D0] at the lifting problem of step (II) of
[Stacks Project, Tag 04AM]. -/
theorem existsUnique_infinitesimalLiftsDiff_eq (f : F ⟶ G) (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) (y : G.obj (op T'))
    (z : InfinitesimalLifts B S hS f i x y)
    (θ : LiftingProblemDerivations B S hS hF hG f i hi x) :
    ∃! z' : InfinitesimalLifts B S hS f i x y,
      infinitesimalLiftsDiff B S hS hF hG f i hi x y z z' = θ :=
  (infinitesimalLiftsDiff_bijective B S hS hF hG f i hi x y z).existsUnique θ

end AlgebraicGeometry.Space

end
