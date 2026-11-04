module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.AffineComparison
public import
  StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestrictionConjugate
public import
  StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestrictionSupport
public import StacksFrontier.AlgebraicGeometry.RingedSpace.DerivedPushforward

/-!
# Tag 0A9K over an open of the base

Let `f : X ⟶ Y` be a morphism of schemes, let `j : V ⟶ Y` be an open immersion and let

```
U --j'--> X
|         |
f'        f
v         v
V --j---> Y
```

be the base change of `j` along `f`.  Writing `a` and `a'` for the twisted inverse images of
[Stacks, Tag 0A9E] along `f` and `f'`, this file proves that the transformation

`ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*`

of [Stacks, Tag 0A9K] is invertible.  An open immersion is flat, so the square is Tor independent
and this is [Stacks, Tag 0A9K] for every square of its Situation [Stacks, Tag 0A9J] in which the
base change morphism is an open immersion.  **Nothing is assumed**: the only arguments are the
quasi-coherence of the cohomology of the four derived direct images and the existence of the two
twisted inverse images, which is what makes `ξ` exist at all.

## The proof

`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/BaseChangeConjugate.lean` reduces
`IsIso ξ` for a general square to [Stacks, Tag 08IB], which this repository does not have, and
`StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/TwistedInverseImageRestrictionConjugate.lean`
reduces it, along an open immersion, to invertibility of the comparison

`β : Rf_* ⋙ j^* ⟶ (j')^* ⋙ Rf'_*`

of [Stacks, Tag 08FE] —
`Stacks.Duality.OpenImmersion.quasiCoherentDerivedRestrictBaseChangeSquare`, the mate of
`Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso` read backwards across the two restriction
adjunctions.  That is the slot this file fills, and it fills it without identifying `β` with any
other map:

* `β` is the mate, across the two adjunctions `Lf^* ⊣ Rf_*` and `L(f')^* ⊣ Rf'_*`, of the
  transformation `α = (mateEquiv ..).symm β` of *left* adjoints.  The iterated mate of `α` is its
  conjugate (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`), and that iterated mate is, by
  construction of `β`, the comparison of derived direct image around the square, which is
  invertible with no hypothesis at all.  Conjugation reflects invertibility
  (`CategoryTheory.conjugateEquiv_of_iso`), so `α` is invertible.
* `Stacks.Cohomology.DerivedBaseChange.isIso_mateEquiv_app_of_isIso_counit` then gives that the
  mate of an invertible two-square is invertible, provided the two restriction adjunctions have
  invertible counit — they do, `j` and `j'` being open immersions — and provided the square of
  right adjoints commutes up to *some* isomorphism.  That isomorphism is [Stacks, Tag 08FE], and
  the point is that only its existence is used, not any identification of it with `β`.

Supplying [Stacks, Tag 08FE] at the quasi-coherent derived categories of this development is the
remaining work, and it is `quasiCoherentDerivedPushforwardRestrictSquareIso` below.
`Stacks.Cohomology.derivedPushforwardRestrictIso` proves Tag 08FE for ringed spaces at an
arbitrary model of the derived category and for arbitrary choices of right derived functors, so
nothing has to be transported between models; what has to be provided is the presentation of
`Stacks.Duality.OpenImmersion.derivedRestrict` — which is `Functor.mapDerivedCategory` of the exact
restriction, not a derived pullback — as a right derived functor of the ringed-space module
pullback.  That is `derivedRestrict_isRightDerivedFunctor`, got from
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

## Main definitions

All in the namespace `Stacks.Duality.OpenImmersion`.

* `derivedRestrictFactorsQh` — the comparison exhibiting `j^*` as a right derived functor of
  degreewise module pullback.
* `derivedPushforwardRestrictSquareIso` and `quasiCoherentDerivedPushforwardRestrictSquareIso` —
  **[Stacks, Tag 08FE]** for a cartesian square of schemes, on the unbounded and on the
  quasi-coherent derived categories.

## Main results

* `isIso_quasiCoherentDerivedRestrictBaseChangeSquare` — the comparison of [Stacks, Tag 08FE] is
  invertible.
* `isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion` — **[Stacks, Tag 0A9K] for a
  cartesian square whose base change morphism is an open immersion.**
* `isIso_quasiCoherentDerivedBaseChangeSquare_of_isOpenImmersion` — its companion
  **[Stacks, Tag 08IB] for base change along an open immersion**, which is the localization step
  of [Stacks, Tag 0DJ9] at the locally small model.

## Implementation notes

*Why `Stacks.Cohomology.derivedPushforwardRestrictIso` is applied with `@`.*  Its four
`IsRightDerivedFunctor` arguments are instance arguments whose morphism property is spelled
`HomotopyCategory.quasiIso (SheafOfModules (structureSheafRing Z))` for the ringed space of the
scheme, whereas the instances available here are spelled with `Z.Modules`;
`AlgebraicGeometry.Scheme.Modules` is a plain `def`, so instance search does not bridge the two
even though they are definitionally equal.  Passing the four instances explicitly spends the
identification once, on a defeq check, and leaves the `HasDerivedCategory` arguments to be
determined by unification against the four functors, so that the model stays the locally small one
of the rest of `Duality/`.

*The model of the derived categories* is therefore the locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, as in the two files this one sits between.
No declaration here mentions `CategoryTheory.HasDerivedCategory.standard`, and nothing is
transported across models:
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/DerivedBaseChangeGlobal.lean` is
imported only for its model-free `isIso_mateEquiv_app_of_isIso_counit` and
`isPullback_toShHom_of_isOpenImmersion`, neither of which mentions a derived category.

*What this does not give.*  [Stacks, Tag 0A9K] for a general Tor-independent square.  That is
equivalent to [Stacks, Tag 08IB] by
`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_iff`, and Tag 08IB is not invoked
here, nor is its route [Stacks, Tag 0DJ9]
(`AlgebraicGeometry.isIso_derivedBaseChangeComp_of_pointwiseBaseChange`).  Along an open
immersion none of that is needed, which is the point of the reduction in
`TwistedInverseImageRestrictionConjugate.lean`.

## References

* [Stacks Project, Tag 0A9J](https://stacks.math.columbia.edu/tag/0A9J)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.Duality.OpenImmersion

/-! ### Restriction along an open immersion as a right derived functor -/

section RightDerived

variable {V Y : Scheme.{u}} (j : V ⟶ Y) [IsOpenImmersion j]

/-- Restriction along an open immersion and module pullback agree on homotopy categories:
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` read through
`CategoryTheory.NatTrans.mapHomotopyCategory`. -/
def restrictPullbackMapHomotopyIso :
    (Scheme.Modules.pullback j).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (restrictFunctor j).mapHomotopyCategory (ComplexShape.up ℤ) where
  hom := (restrictFunctorIsoPullback j).inv.mapHomotopyCategory (ComplexShape.up ℤ)
  inv := (restrictFunctorIsoPullback j).hom.mapHomotopyCategory (ComplexShape.up ℤ)
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp]
    simp
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp]
    simp

/-- The comparison exhibiting `j^* : D(𝒪_Y) ⥤ D(𝒪_V)` as a right derived functor of degreewise
module pullback.  Restriction is exact, so the functor it induces on derived categories is both
its left and its right derived functor; the comparison is the exactness comparison
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` read through
`restrictPullbackMapHomotopyIso`. -/
def derivedRestrictFactorsQh :
    DerivedCategory.Qh ⋙ derivedRestrict j ≅
      (Scheme.Modules.pullback j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (restrictFunctor j).mapDerivedCategoryFactorsh ≪≫
    (Functor.isoWhiskerRight (restrictPullbackMapHomotopyIso j) DerivedCategory.Qh).symm

/-- **Restriction along an open immersion is a right derived functor of degreewise module
pullback**, with comparison `derivedRestrictFactorsQh`.  This is the shape in which
[Stacks, Tag 08FE] consumes a restriction functor. -/
instance derivedRestrict_isRightDerivedFunctor :
    (derivedRestrict j).IsRightDerivedFunctor (derivedRestrictFactorsQh j).inv
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ (derivedRestrictFactorsQh j)

end RightDerived

/-! ### Tag 08FE for a cartesian square of schemes -/

section Square

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j'] [IsOpenImmersion j]

/-- **[Stacks, Tag 08FE] for a cartesian square of schemes**, at the locally small model and for
the canonical derived direct images and the exact restrictions: restricting `Rf_*` along `j` is
`Rf'_*` of the restriction along `j'`.

This is `Stacks.Cohomology.derivedPushforwardRestrictIso` — Tag 08FE for ringed spaces, at an
arbitrary model and for arbitrary right derived functors — instantiated at
`Stacks.Duality.derivedPushforward` with its total-right-derived comparison and at
`Stacks.Duality.OpenImmersion.derivedRestrict` with `derivedRestrictFactorsQh`. -/
def derivedPushforwardRestrictSquareIso (sq : IsPullback j' f' f j) :
    Stacks.Duality.derivedPushforward f ⋙ derivedRestrict j ≅
      derivedRestrict j' ⋙ Stacks.Duality.derivedPushforward f' :=
  @Stacks.Cohomology.derivedPushforwardRestrictIso.{u} _ _ _ _
    f.toLRSHom.toShHom j'.toLRSHom.toShHom j.toLRSHom.toShHom f'.toLRSHom.toShHom
    inferInstance inferInstance
    (Stacks.Cohomology.DerivedBaseChange.isPullback_toShHom_of_isOpenImmersion j' f' f j sq)
    _ _ _ _
    (Stacks.Duality.derivedPushforward f) (Stacks.Duality.derivedPushforward f')
    (derivedRestrict j') (derivedRestrict j)
    (AlgebraicGeometry.RingedSpace.derivedPushforwardUnit f.toLRSHom.toShHom)
    (AlgebraicGeometry.RingedSpace.derivedPushforwardUnit f'.toLRSHom.toShHom)
    (derivedRestrictFactorsQh j').inv (derivedRestrictFactorsQh j).inv
    (AlgebraicGeometry.RingedSpace.derivedPushforward_isRightDerivedFunctor f.toLRSHom.toShHom)
    (AlgebraicGeometry.RingedSpace.derivedPushforward_isRightDerivedFunctor f'.toLRSHom.toShHom)
    (derivedRestrict_isRightDerivedFunctor j') (derivedRestrict_isRightDerivedFunctor j)

variable
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor V.Modules i).obj
      ((Stacks.Duality.derivedPushforward f').obj K.obj)).IsQuasicoherent)

/-- **[Stacks, Tag 08FE] on the quasi-coherent derived categories**:
`derivedPushforwardRestrictSquareIso` read on the full subcategories `D_QCoh`, restriction along
an open immersion preserving quasi-coherence of cohomology by
`Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict`. -/
def quasiCoherentDerivedPushforwardRestrictSquareIso (sq : IsPullback j' f' f j) :
    Stacks.Duality.quasiCoherentDerivedPushforward f hpushf ⋙
        quasiCoherentDerivedRestrict j
          (fun K i => derivedCategoryB_derivedRestrict j K.obj K.property i) ≅
      quasiCoherentDerivedRestrict j'
          (fun K i => derivedCategoryB_derivedRestrict j' K.obj K.property i) ⋙
        Stacks.Duality.quasiCoherentDerivedPushforward f' hpushf' :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _
      ((derivedPushforwardRestrictSquareIso j' f' f j sq).app K.obj))
    (fun e => ObjectProperty.hom_ext _
      ((derivedPushforwardRestrictSquareIso j' f' f j sq).hom.naturality e.hom))

end Square

/-! ### The mate of an invertible square of left adjoints -/

section Abstract

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
  {H : C ⥤ C'} {I : C' ⥤ C} {J : D ⥤ D'} {W : D' ⥤ D}

/-- **A two-square of right adjoints is invertible when its mate across the vertical adjunctions
is**, provided the two horizontal adjunctions have invertible counit and the square of right
adjoints commutes up to some isomorphism.

Given `a : L ⊣ R`, `b : L' ⊣ R'`, `h : H ⊣ I` and `jj : J ⊣ W`, a two-square
`β : R ⋙ H ⟶ J ⋙ R'` is the mate across `a` and `b` of a two-square `α` of left adjoints, and the
mate of `β` across `jj` and `h` is the conjugate of `α`; so if that mate is invertible then so is
`α`, and then
`Stacks.Cohomology.DerivedBaseChange.isIso_mateEquiv_app_of_isIso_counit` applies to `α`. -/
private theorem isIso_twoSquare_of_isIso_mateEquiv (a : L ⊣ R) (b : L' ⊣ R') (h : H ⊣ I)
    (jj : J ⊣ W) [IsIso h.counit] [IsIso jj.counit] (e : R ⋙ H ≅ J ⋙ R')
    (β : TwoSquare R J H R') [IsIso (mateEquiv jj h β).natTrans] :
    IsIso β.natTrans := by
  have hβ : mateEquiv a b ((mateEquiv a b).symm β) = β := Equiv.apply_symm_apply _ _
  have hiter := iterated_mateEquiv_conjugateEquiv a b h jj ((mateEquiv a b).symm β)
  rw [hβ] at hiter
  have : IsIso (conjugateEquiv (a.comp jj) (h.comp b) ((mateEquiv a b).symm β)) := by
    rw [← hiter]
    infer_instance
  have : IsIso ((mateEquiv a b).symm β).natTrans :=
    conjugateEquiv_of_iso (a.comp jj) (h.comp b) _
  have happ : ∀ A, IsIso ((mateEquiv a b ((mateEquiv a b).symm β)).natTrans.app A) := fun A =>
    Stacks.Cohomology.DerivedBaseChange.isIso_mateEquiv_app_of_isIso_counit a b h jj _ e A
  rw [hβ] at happ
  have : ∀ A, IsIso (β.natTrans.app A) := happ
  exact NatIso.isIso_of_isIso_app _

end Abstract

/-! ### Tag 0A9K over an open of the base -/

section BaseChange

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j'] [IsOpenImmersion j]
  (hpushj' : ∀ (K : quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((Stacks.Duality.derivedPushforward j').obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor V.Modules i).obj
      ((Stacks.Duality.derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushj : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Stacks.Duality.derivedPushforward j).obj K.obj)).IsQuasicoherent)

/-- The counit of `j^* ⊣ Rj_*` on the quasi-coherent derived categories is invertible, as a
natural transformation. -/
private theorem isIso_counit_quasiCoherentDerivedRestrictAdjunction {V Y : Scheme.{u}}
    (j : V ⟶ Y) [IsOpenImmersion j]
    (hpushj : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((Stacks.Duality.derivedPushforward j).obj K.obj)).IsQuasicoherent) :
    IsIso (quasiCoherentDerivedRestrictAdjunction j
      (fun K i => derivedCategoryB_derivedRestrict j K.obj K.property i) hpushj).counit :=
  NatIso.isIso_of_isIso_app _

/-- **The comparison `(Rf_*K)|_V ⟶ Rf'_*(K|_U)` of [Stacks, Tag 08FE] is invertible on the
quasi-coherent derived categories.**  This is the slot that
`StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/TwistedInverseImageRestrictionConjugate.lean`
leaves open; see the module documentation for the argument. -/
@[stacks 08FE "invertibility of \
  Stacks.Duality.OpenImmersion.quasiCoherentDerivedRestrictBaseChangeSquare, the mate of \
  Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso across the two restriction adjunctions, \
  on the quasi-coherent derived categories of a cartesian square of schemes whose vertical \
  arrows are open immersions, at the locally small model. The isomorphism of functors itself is \
  Stacks.Cohomology.derivedPushforwardRestrictIso, for ringed spaces; what is added here is that \
  this particular canonical map is the invertible one"]
theorem isIso_quasiCoherentDerivedRestrictBaseChangeSquare (sq : IsPullback j' f' f j) :
    IsIso (quasiCoherentDerivedRestrictBaseChangeSquare j' f' f j hpushj' hpushf hpushf' hpushj
      (fun K i => derivedCategoryB_derivedRestrict j K.obj K.property i)
      (fun K i => derivedCategoryB_derivedRestrict j' K.obj K.property i) sq.w) := by
  have := isIso_counit_quasiCoherentDerivedRestrictAdjunction j hpushj
  have := isIso_counit_quasiCoherentDerivedRestrictAdjunction j' hpushj'
  have : IsIso (mateEquiv
      (quasiCoherentDerivedRestrictAdjunction j'
        (fun K i => derivedCategoryB_derivedRestrict j' K.obj K.property i) hpushj')
      (quasiCoherentDerivedRestrictAdjunction j
        (fun K i => derivedCategoryB_derivedRestrict j K.obj K.property i) hpushj)
      (TwoSquare.mk _ _ _ _ (quasiCoherentDerivedRestrictBaseChangeSquare j' f' f j hpushj'
        hpushf hpushf' hpushj
        (fun K i => derivedCategoryB_derivedRestrict j K.obj K.property i)
        (fun K i => derivedCategoryB_derivedRestrict j' K.obj K.property i) sq.w))).natTrans := by
    rw [mateEquiv_quasiCoherentDerivedRestrictBaseChangeSquare]
    infer_instance
  exact isIso_twoSquare_of_isIso_mateEquiv
    (Stacks.Duality.quasiCoherentDerivedAdjunction f
      (Stacks.Duality.isQuasicoherent_homology_derivedPullback' f) hpushf)
    (Stacks.Duality.quasiCoherentDerivedAdjunction f'
      (Stacks.Duality.isQuasicoherent_homology_derivedPullback' f') hpushf')
    (quasiCoherentDerivedRestrictAdjunction j
      (fun K i => derivedCategoryB_derivedRestrict j K.obj K.property i) hpushj)
    (quasiCoherentDerivedRestrictAdjunction j'
      (fun K i => derivedCategoryB_derivedRestrict j' K.obj K.property i) hpushj')
    (quasiCoherentDerivedPushforwardRestrictSquareIso j' f' f j hpushf hpushf' sq) _

/-- **[Stacks, Tag 0A9K] for a cartesian square whose base change morphism is an open
immersion.**  In the Situation of [Stacks, Tag 0A9J], if `j : V ⟶ Y` is an open immersion — so
flat, and the square is Tor independent — then the transformation
`ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*` is an isomorphism.

The arguments are the four quasi-coherence conditions of [Stacks, Tag 08D5] and the two
adjointness instances of [Stacks, Tag 0A9E], without which `ξ` does not exist; no further
hypothesis is carried. -/
@[stacks 0A9K "for a cartesian square of schemes whose base change morphism g is an OPEN \
  IMMERSION, hence flat, hence Tor independent of f: the transformation xi = \
  Stacks.Duality.twistedInverseImagePushforwardBaseChange of the Situation of Stacks 0A9J is \
  invertible, with nothing assumed beyond the quasi-coherence of the cohomology of the four \
  derived direct images (Stacks 08D5) and the existence of the two twisted inverse images \
  (Stacks 0A9E), which is what makes xi exist. The general Tor-independent case is NOT proved: \
  by Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_iff it is equivalent to \
  Stacks 08IB, whose route Stacks 0DJ9 is carried in this repository over three unproved \
  hypotheses (AlgebraicGeometry.BaseChangeAffineOpenCase, \
  AlgebraicGeometry.BaseChangeMayerVietorisStep, and the localization step) at \
  AlgebraicGeometry.isIso_derivedBaseChangeComp_of_affineCase. Along an open immersion none of \
  that is needed, Stacks 08IB being replaced by Stacks 08FE"]
theorem isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion
    [(Stacks.Duality.quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
    [(Stacks.Duality.quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]
    (sq : IsPullback j' f' f j) :
    IsIso (Stacks.Duality.twistedInverseImagePushforwardBaseChange j' f' f j hpushj' hpushf
      hpushf' hpushj sq) :=
  have := isIso_quasiCoherentDerivedRestrictBaseChangeSquare j' f' f j hpushj' hpushf hpushf'
    hpushj sq
  isIso_twistedInverseImagePushforwardBaseChange_of_isIso_restrictBaseChangeSquare j' f' f j
    hpushj' hpushf hpushf' hpushj
    (fun K i => derivedCategoryB_derivedRestrict j K.obj K.property i)
    (fun K i => derivedCategoryB_derivedRestrict j' K.obj K.property i) sq

/-- **[Stacks, Tag 08IB] for base change along an open immersion of the base**, on the
quasi-coherent derived categories at the locally small model: the derived base change map
`β : Rf_* ⋙ Lj^* ⟶ L(j')^* ⋙ Rf'_*` of [Stacks, Tag 08HY] is invertible.

This is the companion of
`isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion` under
`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_iff`, and it is the localization
step of [Stacks, Tag 0DJ9] at this model — `β` here is the mate of
`Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso`, not the comparison of
`Stacks.Duality.OpenImmersion.quasiCoherentDerivedRestrictBaseChangeSquare`, so nothing identifies
derived pullback with the exact restriction along the way. -/
@[stacks 08IB "for base change along an OPEN IMMERSION of the base, hence flat, hence Tor \
  independent of f: invertibility of Stacks.Duality.quasiCoherentDerivedBaseChangeSquare, the \
  derived base change map of Stacks 08HY on the quasi-coherent derived categories at the locally \
  small model. The general Tor-independent case is not proved in this repository; see \
  Stacks.Duality.OpenImmersion.isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion"]
theorem isIso_quasiCoherentDerivedBaseChangeSquare_of_isOpenImmersion
    [(Stacks.Duality.quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
    [(Stacks.Duality.quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]
    (sq : IsPullback j' f' f j) :
    IsIso (Stacks.Duality.quasiCoherentDerivedBaseChangeSquare j' f' f j hpushj' hpushf hpushf'
      hpushj (Stacks.Duality.isQuasicoherent_homology_derivedPullback' j)
      (Stacks.Duality.isQuasicoherent_homology_derivedPullback' j') sq.w) :=
  (Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_iff j' f' f j hpushj' hpushf
    hpushf' hpushj _ _ sq).1
    (isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion j' f' f j hpushj' hpushf
      hpushf' hpushj sq)

end BaseChange

end Stacks.Duality.OpenImmersion

end
