module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# Base change of étale charts is right adjoint to postcomposition

Let `f : X ⟶ Y` be an étale *representable* morphism of algebraic spaces over a scheme `S`
contained in a big fppf site `B`.  Stacks 03LP attaches to `f` the postcomposition functor

`j : X_étale ⥤ Y_étale`, `(φ : U ⟶ X) ↦ (φ ≫ f : U ⟶ Y)`,

which is `AlgebraicGeometry.Space.smallEtalePostcomp`, and Stacks 03G2, part (4) attaches to a
representable `f` the base-change functor `V ↦ V ×_Y X` on étale scheme charts, which is
`AlgebraicGeometry.Space.smallBaseChange`.  This file proves that the two are adjoint,

`j ⊣ (- ×_Y X)`,

which is nothing but the universal property of the fibre product read on charts: a morphism of
charts `jU ⟶ V` over `Y` is the same thing as a morphism `U ⟶ V ×_Y X` over `X`.

The point of the adjunction is what it gives for modules.  Restriction of modules along `f` is
`AlgebraicGeometry.Space.etaleModulePullback`, which is `SheafOfModules.pushforward` along `j`
for the identity structure map; the adjunction therefore transports, by
`SheafOfModules.pushforwardPushforwardAdj`, to an adjunction between it and
`SheafOfModules.pushforward` along base change, that is,
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`.  By uniqueness of right adjoints
that functor is then the direct image `f_*` of Stacks 03LU
(`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso`), so

**the direct image of modules along a representable étale morphism is restriction of sections
along base change of charts:** `(f_*ℱ)(V) = ℱ(V ×_Y X)`, and the unit `ℱ ⟶ f_*f^*ℱ` is, over a
chart `V`, restriction along the cartesian projection `V ×_Y X ⟶ V`
(`AlgebraicGeometry.Space.etaleModulePullbackSmallBaseChangeAdjunction_unit_app_val_app`).

That is a description of `AlgebraicGeometry.Space.modulePushforward` on sections which does not
require unwinding the comparison equivalence of Stacks 03G1, through which that functor is
built and whose quasi-inverse is a `Classical.choose`; see the implementation notes.

Nothing here produces an *extension by zero* `f_!`, a left adjoint of restriction.
`SheafOfModules.isLeftAdjoint_pushforward_of_isIso` goes the other way: from a right adjoint of
`j` it produces a right adjoint of restriction, which is the direct image again.

## Main definitions

* `AlgebraicGeometry.Space.postcompToBaseChange` and
  `AlgebraicGeometry.Space.baseChangeToPostcomp` are the two directions of the bijection on
  morphisms of charts.
* `AlgebraicGeometry.Space.smallEtalePostcompBaseChangeAdjunction` is the adjunction
  `j ⊣ (- ×_Y X)`.
* `AlgebraicGeometry.Space.etaleRestrictionSharp` is the identity structure map through which
  `AlgebraicGeometry.Space.etaleModulePullback` is a `SheafOfModules.pushforward`, written over
  `AlgebraicGeometry.Space.SmallEtale.topology`.
* `AlgebraicGeometry.Space.bigFppfGammaMap` is the ring map on global regular functions induced
  by a morphism of the big fppf site.

## Main results

* `AlgebraicGeometry.Space.etaleModulePullbackSmallBaseChangeAdjunction`: restriction of modules
  along a representable étale morphism is left adjoint to restriction of sections along base
  change of charts.
* `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso`: that right adjoint is
  `AlgebraicGeometry.Space.modulePushforward`, the direct image of Stacks 03LU.  Together with
  `AlgebraicGeometry.Space.smallBaseChangeModulePushforward_obj_val_obj` this computes the
  sections of the direct image over an étale chart.
* `AlgebraicGeometry.Space.etaleModulePullbackSmallBaseChangeAdjunction_unit_app_val_app`: the
  unit of that adjunction is restriction of sections along the cartesian projection.

## Implementation notes

The underlying maps of the morphisms of charts in play are retyped by the definitions
`AlgebraicGeometry.Space.postcompLeft`, `AlgebraicGeometry.Space.baseChangeLeft` and
`AlgebraicGeometry.Space.baseChangeMapLeft` rather than used as the projections
`k.hom.left`.  That is not cosmetic.  The source of `k.hom.left` for
`k : j U ⟶ V` is recorded as `(j U).1.left`, which is `U.1.left` only after unfolding
`AlgebraicGeometry.Space.smallEtalePostcomp`, and `rw` type-checks its motive at `instances`
transparency, where that unfolding does not happen; every rewrite on a composite that mixes the
two spellings fails with a "did not find an occurrence" error whose real cause is the type
mismatch.  Retyping each underlying map once, at the point where the defeq is still available
to the elaborator, removes the problem from all later proofs.  The same applies to
`hrep.pullback V.1.hom` versus `((- ×_Y X) V).1.left`.

The sheaf of rings is `AlgebraicGeometry.Space.smallEtaleRingSheaf`, written over
`AlgebraicGeometry.Space.SmallEtale.topology`, for the reason recorded in the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeRestriction.lean`: instance
search does not unfold the projection `.J` of a `AlgebraicGeometry.RingedSite` instance, so a
continuity instance stated for the small étale topology does not apply to a sheaf of modules
indexed through that projection.

That is also why `AlgebraicGeometry.Space.etaleRestrictionSharp` is stated here rather than
reusing `AlgebraicGeometry.Space.etaleRestrictionRingMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompIsoEtaleRestriction.lean`.
The two are the same morphism — both are `𝟙 _`, and their types agree by `rfl`, which is
`AlgebraicGeometry.Space.ringedSite_ringSheaf_eq` — but that one is stated over the projection
`(AlgebraicGeometry.Space.smallEtaleRingedSite …).J` and over
`AlgebraicGeometry.RingedSite.ringSheaf`.  Used in its place it leaves both continuity instances
of the adjunction below unsynthesizable, sends the identification of the double restriction into
an `isDefEq` timeout, and breaks
`AlgebraicGeometry.Space.etaleModulePullbackSmallBaseChangeAdjunction_unit_app_val_app`, whose
proof is `rfl`.  The two spellings are therefore not interchangeable and must not be merged.

The identification of the right adjoint with `AlgebraicGeometry.Space.modulePushforward` is by
`CategoryTheory.Adjunction.rightAdjointUniq` against the adjunction of Stacks 03LU, and so it
avoids both of the comparisons that
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeRestriction.lean` records as missing:
neither the transported ring structure of
`Stacks.Sheaves.ToposPullback.pullbackRingSheaf` nor the structure map
`AlgebraicGeometry.Space.structureSharp` is touched.  What is compared is not the two functors
term by term but the two adjunctions, and a right adjoint is unique up to a unique compatible
isomorphism.  For the same reason this file does not carry the tag of Stacks 04CF: the identity
of 04CF is about the restriction of the direct image to a chart, which is
`AlgebraicGeometry.Space.overFunctor_comp_smallBaseChangeModulePushforward`, and what is added
here is the identification of the functor being restricted.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public section

open CategoryTheory

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-! ### The underlying maps of the morphisms of charts in play -/

/-- The underlying morphism of the big fppf site of a morphism of étale charts out of a
postcomposed chart, with its source retyped as the underlying object of the original chart.

Postcomposition leaves the underlying object unchanged, so this is `k.hom.left`; see the
implementation notes for why the retyping matters. -/
def postcompLeft (c : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (k : (smallEtalePostcomp B S hS f hf).obj c ⟶ V) : c.1.left ⟶ V.1.left := k.hom.left

/-- The underlying map of a composite is the composite of the underlying maps. -/
theorem postcompLeft_comp (c : SmallEtale B S hS X.1) {V V' : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS f hf).obj c ⟶ V) (l : V ⟶ V') :
    postcompLeft B S hS f hf c V' (k ≫ l) =
      postcompLeft B S hS f hf c V k ≫ l.hom.left := rfl

/-- The triangle over `Y` commuted by a morphism of charts out of a postcomposed chart. -/
theorem yoneda_postcompLeft (c : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (k : (smallEtalePostcomp B S hS f hf).obj c ⟶ V) :
    yoneda.map (postcompLeft B S hS f hf c V k) ≫ V.1.hom = c.1.hom ≫ f.hom :=
  CostructuredArrow.w k.hom

/-- A morphism of étale charts is determined by its underlying morphism of the big fppf site. -/
theorem postcompLeft_injective (c : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    {k k' : (smallEtalePostcomp B S hS f hf).obj c ⟶ V}
    (h : postcompLeft B S hS f hf c V k = postcompLeft B S hS f hf c V k') : k = k' :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ h)

variable (hrep : yoneda.relativelyRepresentable f.hom)

/-- The underlying morphism of the big fppf site of a morphism of étale charts into a
base-changed chart, with its target retyped as the chosen representing object of the fibre
product. -/
def baseChangeLeft (c : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (m : c ⟶ (smallBaseChange B S hS f hrep).obj V) :
    c.1.left ⟶ hrep.pullback V.1.hom := m.hom.left

/-- The triangle over `X` commuted by a morphism of charts into a base-changed chart. -/
theorem yoneda_baseChangeLeft (c : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (m : c ⟶ (smallBaseChange B S hS f hrep).obj V) :
    yoneda.map (baseChangeLeft B S hS f hrep c V m) ≫ hrep.fst V.1.hom = c.1.hom :=
  CostructuredArrow.w m.hom

/-- A morphism of étale charts into a base-changed chart is determined by its underlying
morphism of the big fppf site. -/
theorem baseChangeLeft_injective (c : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    {m m' : c ⟶ (smallBaseChange B S hS f hrep).obj V}
    (h : baseChangeLeft B S hS f hrep c V m = baseChangeLeft B S hS f hrep c V m') : m = m' :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ h)

/-- The underlying morphism of the big fppf site of the base change of a morphism of étale
charts, with its source and target retyped as the chosen representing objects of the fibre
products. -/
noncomputable def baseChangeMapLeft {V V' : SmallEtale B S hS Y.1} (l : V ⟶ V') :
    hrep.pullback V.1.hom ⟶ hrep.pullback V'.1.hom :=
  ((smallBaseChange B S hS f hrep).map l).hom.left

/-- The base change of a morphism of charts is a morphism over `X`. -/
theorem yoneda_baseChangeMapLeft_comp_fst {V V' : SmallEtale B S hS Y.1} (l : V ⟶ V') :
    yoneda.map (baseChangeMapLeft B S hS f hrep l) ≫ hrep.fst V'.1.hom = hrep.fst V.1.hom :=
  hrep.lift_fst _ _ _

/-- The base change of a morphism of charts is compatible with the cartesian projections. -/
theorem baseChangeMapLeft_comp_snd {V V' : SmallEtale B S hS Y.1} (l : V ⟶ V') :
    baseChangeMapLeft B S hS f hrep l ≫ hrep.snd V'.1.hom =
      hrep.snd V.1.hom ≫ l.hom.left :=
  hrep.lift_snd _ _ _

/-- The underlying map of a composite with a base-changed morphism. -/
theorem baseChangeLeft_comp (c : SmallEtale B S hS X.1) {V V' : SmallEtale B S hS Y.1}
    (m : c ⟶ (smallBaseChange B S hS f hrep).obj V) (l : V ⟶ V') :
    baseChangeLeft B S hS f hrep c V' (m ≫ (smallBaseChange B S hS f hrep).map l) =
      baseChangeLeft B S hS f hrep c V m ≫ baseChangeMapLeft B S hS f hrep l := rfl

/-! ### The bijection on morphisms of charts -/

/-- **The universal property of the fibre product, on charts, forwards.**  A morphism of étale
charts `jU ⟶ V` over `Y` gives a morphism `U ⟶ V ×_Y X` over `X`. -/
noncomputable def postcompToBaseChange (c : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (k : (smallEtalePostcomp B S hS f hf).obj c ⟶ V) :
    c ⟶ (smallBaseChange B S hS f hrep).obj V :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (hrep.lift c.1.hom (postcompLeft B S hS f hf c V k)
      (yoneda_postcompLeft B S hS f hf c V k).symm)
    (hrep.lift_fst _ _ _))

/-- The underlying map of `AlgebraicGeometry.Space.postcompToBaseChange` is the lift given by
the universal property. -/
theorem baseChangeLeft_postcompToBaseChange (c : SmallEtale B S hS X.1)
    (V : SmallEtale B S hS Y.1) (k : (smallEtalePostcomp B S hS f hf).obj c ⟶ V) :
    baseChangeLeft B S hS f hrep c V (postcompToBaseChange B S hS f hf hrep c V k) =
      hrep.lift c.1.hom (postcompLeft B S hS f hf c V k)
        (yoneda_postcompLeft B S hS f hf c V k).symm := rfl

/-- **The universal property of the fibre product, on charts, backwards.**  A morphism of étale
charts `U ⟶ V ×_Y X` over `X` gives a morphism `jU ⟶ V` over `Y`, by following the cartesian
projection. -/
noncomputable def baseChangeToPostcomp (c : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (m : c ⟶ (smallBaseChange B S hS f hrep).obj V) :
    (smallEtalePostcomp B S hS f hf).obj c ⟶ V :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (baseChangeLeft B S hS f hrep c V m ≫ hrep.snd V.1.hom)
    (by
      change yoneda.map (baseChangeLeft B S hS f hrep c V m ≫ hrep.snd V.1.hom) ≫ V.1.hom
        = c.1.hom ≫ f.hom
      rw [Functor.map_comp, Category.assoc, ← hrep.w, ← Category.assoc,
        yoneda_baseChangeLeft]))

/-- The underlying map of `AlgebraicGeometry.Space.baseChangeToPostcomp` is the composite with
the cartesian projection. -/
theorem postcompLeft_baseChangeToPostcomp (c : SmallEtale B S hS X.1)
    (V : SmallEtale B S hS Y.1) (m : c ⟶ (smallBaseChange B S hS f hrep).obj V) :
    postcompLeft B S hS f hf c V (baseChangeToPostcomp B S hS f hf hrep c V m) =
      baseChangeLeft B S hS f hrep c V m ≫ hrep.snd V.1.hom := rfl

/-- The two directions of the bijection are mutually inverse, one way. -/
theorem baseChangeToPostcomp_postcompToBaseChange (c : SmallEtale B S hS X.1)
    (V : SmallEtale B S hS Y.1) (k : (smallEtalePostcomp B S hS f hf).obj c ⟶ V) :
    baseChangeToPostcomp B S hS f hf hrep c V
        (postcompToBaseChange B S hS f hf hrep c V k) = k := by
  refine postcompLeft_injective B S hS f hf c V ?_
  rw [postcompLeft_baseChangeToPostcomp, baseChangeLeft_postcompToBaseChange, hrep.lift_snd]

/-- The two directions of the bijection are mutually inverse, the other way. -/
theorem postcompToBaseChange_baseChangeToPostcomp (c : SmallEtale B S hS X.1)
    (V : SmallEtale B S hS Y.1) (m : c ⟶ (smallBaseChange B S hS f hrep).obj V) :
    postcompToBaseChange B S hS f hf hrep c V
        (baseChangeToPostcomp B S hS f hf hrep c V m) = m := by
  refine baseChangeLeft_injective B S hS f hrep c V ?_
  rw [baseChangeLeft_postcompToBaseChange]
  refine hrep.hom_ext ?_ ?_
  · rw [hrep.lift_fst, yoneda_baseChangeLeft]
  · rw [hrep.lift_snd, postcompLeft_baseChangeToPostcomp]

/-- **Postcomposition along an étale representable morphism of algebraic spaces is left adjoint
to base change of étale charts.**  For `f : X ⟶ Y` étale and representable, the functor `j` of
Stacks 03LP is left adjoint to the functor `V ↦ V ×_Y X` of Stacks 03G2, part (4).

The bijection is the universal property of the fibre product: a morphism `jU ⟶ V` over `Y` is a
morphism `U ⟶ V` of the big fppf site whose triangle over `Y` commutes, which is exactly the
datum of a morphism `U ⟶ V ×_Y X` over `X`. -/
noncomputable def smallEtalePostcompBaseChangeAdjunction :
    smallEtalePostcomp B S hS f hf ⊣ smallBaseChange B S hS f hrep :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun c V =>
        { toFun := postcompToBaseChange B S hS f hf hrep c V
          invFun := baseChangeToPostcomp B S hS f hf hrep c V
          left_inv := baseChangeToPostcomp_postcompToBaseChange B S hS f hf hrep c V
          right_inv := postcompToBaseChange_baseChangeToPostcomp B S hS f hf hrep c V }
      homEquiv_naturality_left_symm := by
        intro c' c V g m
        refine postcompLeft_injective B S hS f hf c' V ?_
        change baseChangeLeft B S hS f hrep c' V (g ≫ m) ≫ hrep.snd V.1.hom
          = g.hom.left ≫ baseChangeLeft B S hS f hrep c V m ≫ hrep.snd V.1.hom
        exact Category.assoc _ _ _
      homEquiv_naturality_right := by
        intro c V V' k l
        refine baseChangeLeft_injective B S hS f hrep c V' ?_
        change baseChangeLeft B S hS f hrep c V'
            (postcompToBaseChange B S hS f hf hrep c V' (k ≫ l))
          = baseChangeLeft B S hS f hrep c V'
              (postcompToBaseChange B S hS f hf hrep c V k ≫
                (smallBaseChange B S hS f hrep).map l)
        rw [baseChangeLeft_postcompToBaseChange, baseChangeLeft_comp,
          baseChangeLeft_postcompToBaseChange]
        refine hrep.hom_ext ?_ ?_
        · rw [hrep.lift_fst, Functor.map_comp, Category.assoc,
            yoneda_baseChangeMapLeft_comp_fst, hrep.lift_fst]
        · rw [hrep.lift_snd, Category.assoc, baseChangeMapLeft_comp_snd, ← Category.assoc,
            hrep.lift_snd, postcompLeft_comp] }

/-- The counit of the adjunction is the cartesian projection `(V ×_Y X) ⟶ V`. -/
theorem smallEtalePostcompBaseChangeAdjunction_counit_left (V : SmallEtale B S hS Y.1) :
    ((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).counit.app V).hom.left
      = hrep.snd V.1.hom :=
  Category.id_comp _

/-- The unit of the adjunction is a section of the cartesian projection. -/
theorem smallEtalePostcompBaseChangeAdjunction_unit_left_comp_snd
    (c : SmallEtale B S hS X.1) :
    ((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).unit.app c).hom.left ≫
        hrep.snd ((smallEtalePostcomp B S hS f hf).obj c).1.hom = 𝟙 c.1.left :=
  hrep.lift_snd _ _ _

include hrep in
/-- Postcomposition along an étale representable morphism has a right adjoint. -/
theorem isLeftAdjoint_smallEtalePostcomp :
    (smallEtalePostcomp B S hS f hf).IsLeftAdjoint :=
  (smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).isLeftAdjoint

/-! ### Global regular functions -/

/-- The ring map on global regular functions of the underlying schemes induced by a morphism of
the big fppf site, as a morphism of the (not necessarily commutative) rings in which the
sheaves of modules of the small étale site are indexed. -/
noncomputable def bigFppfGammaMap {A A' : BigFppfOver B S hS} (g : A ⟶ A') :
    (forget₂ CommRingCat.{u} RingCat.{u}).obj
        (Scheme.Γ.obj (Opposite.op ((BigFppfOver.toScheme B S hS).obj A'))) ⟶
      (forget₂ CommRingCat.{u} RingCat.{u}).obj
        (Scheme.Γ.obj (Opposite.op ((BigFppfOver.toScheme B S hS).obj A))) :=
  (forget₂ CommRingCat.{u} RingCat.{u}).map
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op)

/-- Global regular functions are contravariantly functorial. -/
theorem bigFppfGammaMap_comp {A A' A'' : BigFppfOver B S hS} (g : A ⟶ A') (g' : A' ⟶ A'') :
    bigFppfGammaMap B S hS (g ≫ g') = bigFppfGammaMap B S hS g' ≫ bigFppfGammaMap B S hS g := by
  simp [bigFppfGammaMap, ← Functor.map_comp]

/-- Global regular functions take the identity to the identity. -/
theorem bigFppfGammaMap_id (A : BigFppfOver B S hS) :
    bigFppfGammaMap B S hS (𝟙 A) = 𝟙 _ := by
  simp [bigFppfGammaMap]

/-! ### The direct image of modules along a representable étale morphism -/

/-- The structure map through which `AlgebraicGeometry.Space.etaleModulePullback` is a
`SheafOfModules.pushforward`: the identity, because postcomposition leaves the underlying scheme
of a chart unchanged and therefore restricts the structure sheaf of `Y` to that of `X` on the
nose.

This is the morphism `AlgebraicGeometry.Space.etaleRestrictionRingMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompIsoEtaleRestriction.lean`, but
written over `AlgebraicGeometry.Space.SmallEtale.topology` and
`AlgebraicGeometry.Space.smallEtaleRingSheaf` rather than over the projections `.J` and
`AlgebraicGeometry.RingedSite.ringSheaf` of
`AlgebraicGeometry.Space.smallEtaleRingedSite`; see the implementation notes for why the two
spellings are not interchangeable here. -/
noncomputable abbrev etaleRestrictionSharp :
    smallEtaleRingSheaf B S hS X.1 X.2 ⟶
      ((smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS X.1)
        (SmallEtale.topology B S hS Y.1)).obj (smallEtaleRingSheaf B S hS Y.1 Y.2) :=
  𝟙 (smallEtaleRingSheaf B S hS X.1 X.2)

/-- Étale restriction of modules is the pushforward of sheaves of modules along postcomposition
for the identity structure map. -/
theorem etaleModulePullback_eq_pushforward :
    SheafOfModules.pushforward.{u} (etaleRestrictionSharp B S hS f hf) =
      etaleModulePullback.{u, u} B S hS f hf := rfl

/-- The structure map of base change is adjunct to the identity, on the counit side. -/
theorem smallBaseChangeSharp_counit :
    Functor.whiskerRight
        (NatTrans.op (smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).counit)
        (smallEtaleRingSheaf B S hS Y.1 Y.2).obj =
      (smallBaseChangeSharp B S hS f hrep).hom ≫
        (smallBaseChange B S hS f hrep).op.whiskerLeft
          (etaleRestrictionSharp B S hS f hf).hom := by
  ext U : 2
  exact congrArg (bigFppfGammaMap B S hS)
    (smallEtalePostcompBaseChangeAdjunction_counit_left B S hS f hf hrep U.unop)

/-- The structure map of base change is adjunct to the identity, on the unit side. -/
theorem smallBaseChangeSharp_unit :
    (etaleRestrictionSharp B S hS f hf).hom ≫
        (smallEtalePostcomp B S hS f hf).op.whiskerLeft
          (smallBaseChangeSharp B S hS f hrep).hom ≫
        Functor.whiskerRight
          (NatTrans.op (smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).unit)
          (smallEtaleRingSheaf B S hS X.1 X.2).obj =
      𝟙 (smallEtaleRingSheaf B S hS X.1 X.2).obj := by
  ext U : 2
  refine (Category.id_comp _).trans ?_
  refine Eq.trans ?_ (bigFppfGammaMap_id B S hS _)
  refine Eq.trans (bigFppfGammaMap_comp B S hS
    (((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).unit.app U.unop).hom.left)
    (hrep.snd ((smallEtalePostcomp B S hS f hf).obj U.unop).1.hom)).symm ?_
  exact congrArg (bigFppfGammaMap B S hS)
    (smallEtalePostcompBaseChangeAdjunction_unit_left_comp_snd B S hS f hf hrep U.unop)

/-- **Restriction of modules along an étale representable morphism of algebraic spaces is left
adjoint to restriction of sections along base change of étale charts.**

This is `SheafOfModules.pushforwardPushforwardAdj` applied to
`AlgebraicGeometry.Space.smallEtalePostcompBaseChangeAdjunction`, with the identity structure map
on the restriction side and the structure map of Stacks 03G2, part (4) on the base-change
side. -/
noncomputable def etaleModulePullbackSmallBaseChangeAdjunction :
    etaleModulePullback.{u, u} B S hS f hf ⊣
      smallBaseChangeModulePushforward.{u, u} B S hS f hrep :=
  SheafOfModules.pushforwardPushforwardAdj
    (smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep)
    (etaleRestrictionSharp B S hS f hf) (smallBaseChangeSharp B S hS f hrep)
    (smallBaseChangeSharp_counit B S hS f hf hrep)
    (smallBaseChangeSharp_unit B S hS f hf hrep)

/-- **The direct image of modules along an étale representable morphism of algebraic spaces is
restriction of sections along base change of étale charts.**

Both functors are right adjoint to restriction of modules along `f` — the first by the
adjunction of Stacks 03LU read through the identification of Stacks 03LW, the second by
`AlgebraicGeometry.Space.etaleModulePullbackSmallBaseChangeAdjunction` — so they agree by
uniqueness of right adjoints.  No comparison of the two constructions term by term is involved;
see the implementation notes. -/
noncomputable def smallBaseChangeModulePushforwardIso :
    smallBaseChangeModulePushforward.{u, u} B S hS f hrep ≅ modulePushforward B S hS f :=
  (etaleModulePullbackSmallBaseChangeAdjunction B S hS f hf hrep).rightAdjointUniq
    ((modulePullbackAdjunction B S hS f).ofNatIsoLeft
      (modulePullbackIsoEtaleModulePullback B S hS f hf))

/-- The unit of the adjunction is restriction of sections along the cartesian projection
`V ×_Y X ⟶ V`: over an étale chart `V` of `Y` the map `ℱ(V) ⟶ (f_*f^*ℱ)(V) = ℱ(V ×_Y X)` is the
restriction map of `ℱ` along that projection.  This holds by definition of
`SheafOfModules.pushforwardPushforwardAdj`; the projection is
`AlgebraicGeometry.Space.smallEtalePostcompBaseChangeAdjunction_counit_left`. -/
theorem etaleModulePullbackSmallBaseChangeAdjunction_unit_app_val_app
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : ((M.val.obj V : ModuleCat _) : Type u)) :
    ((etaleModulePullbackSmallBaseChangeAdjunction B S hS f hf hrep).unit.app M).val.app V x =
      M.val.map
        ((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).counit.app V.unop).op x :=
  rfl

/-- The sections of the direct image of a module over an étale chart `V` of `Y` are its sections
over the base-changed chart `V ×_Y X`, as a type: by definition of the base-change pushforward
the two agree, the scalars of the first being those of the second restricted along the
structure map of Stacks 03G2, part (4). -/
theorem smallBaseChangeModulePushforward_obj_val_obj
    (M : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1) :
    (((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).obj M).val.obj
        (Opposite.op V) : Type u) =
      (M.val.obj (Opposite.op ((smallBaseChange B S hS f hrep).obj V)) : Type u) := rfl

end AlgebraicGeometry.Space

end
