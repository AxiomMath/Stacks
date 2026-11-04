module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraQcqs

/-!
# Stacks 081X against a given bounded anti-equivalence

Stacks 081X asserts that a quasi-compact, quasi-separated morphism `f : Y ⟶ X` of algebraic
spaces factors canonically as

`Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X`,

which makes sense because `f_* 𝒪_Y` is quasi-coherent (Stacks 03M9).  Quasi-coherence is proved
unconditionally, as `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra_of_qcqs` of
`StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraQcqs`.  This file states the
factorization against a given anti-equivalence of Stacks 081V and does not carry the tag: Stacks
081X is delivered unconditionally, quasi-coherence, factorization and canonicity together, by
`AlgebraicGeometry.Space.directImageSpec_factorization` of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSpecFactorization`, whose relative spectrum is
`AlgebraicGeometry.Space.boundedRelativeSpec` (Stacks 081W) and whose size condition is
`AlgebraicGeometry.Space.sectionsBelowCutoff_pushforwardAlgebra`.

The factorization in that file is stated against
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence`, and that structure is **uninhabited**:
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`
empties it from a single affine chart with `1 ≠ 0`, because its target carries no bound on the
sections of an algebra while its source carries one by construction.  Every statement under that
hypothesis is therefore vacuous.  This file restates the factorization against
`AlgebraicGeometry.Space.BoundedAffineAlgebraAntiEquivalence`, whose target is cut down to the
algebras satisfying exactly the bound the source side satisfies, and which that argument does not
refute.  That the exchange is a *strengthening* is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalenceRestriction`, as
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.toBounded`: an unrestricted
anti-equivalence restricts to a bounded one, so the bounded structure is the weaker hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardAlgebraIdAlgebraIso` identifies `(𝟙_Y)_* 𝒪_Y` with `𝒪_Y`
  as `𝒪_Y`-algebras, with **no** anti-equivalence: this is the identity clause of Stacks 03G8,
  `AlgebraicGeometry.Space.isIso_fSharp_id`, read through
  `AlgebraicGeometry.Space.AlgebraSheaf.ofHomMap`.
* `AlgebraicGeometry.Space.affineOverBaseChange` is the base change `Y ×_X Z` of an algebraic
  space affine over `X`, as an algebraic space affine over `Y`, with
  `AlgebraicGeometry.Space.affineOverBaseChangeProjection` its projection to `Z` and
  `AlgebraicGeometry.Space.affineOverBaseChange_isPullback` the cartesian square.  Also with no
  anti-equivalence: fibre products of algebraic spaces exist
  (`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`, Stacks 02X2) and affine morphisms
  are stable under base change (`AlgebraicGeometry.Space.isAffineHom_hom_of_isPullback`,
  Stacks 03WI).
* `AlgebraicGeometry.Space.algebraPullbackPushforwardCounit` is the canonical algebra map
  `f^* f_* 𝒪_Y ⟶ 𝒪_Y`, and
  `AlgebraicGeometry.Space.algebraPullbackPushforwardCounitAlgebraHom` the same as a morphism of
  algebra sheaves.  Again with no anti-equivalence, from the pushout description of algebra
  pullback `AlgebraicGeometry.Space.algebraPullback_isPushout`.
* `AlgebraicGeometry.Space.boundedAlgebraHomSection` is the section `Y ⟶ W` over `Y` which a
  bounded anti-equivalence matches with an algebra map `w_* 𝒪_W ⟶ 𝒪_Y`.
* `AlgebraicGeometry.Space.boundedRelativeSpecDirectImage` is the relative spectrum
  `\underline{Spec}_X(f_* 𝒪_Y)` taken with a bounded anti-equivalence, and
  `AlgebraicGeometry.Space.boundedDirectImageFactorizationMap`,
  `AlgebraicGeometry.Space.boundedQcqsDirectImageFactorizationMap` are the canonical morphisms
  `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` over `X`.

## Main results

* `AlgebraicGeometry.Space.boundedDirectImageFactorizationMap_factorization` and
  `AlgebraicGeometry.Space.boundedQcqsDirectImageFactorizationMap_factorization`: **the
  factorization of Stacks 081X against a given bounded anti-equivalence.**  The canonical morphism
  composed with the structure morphism of the relative spectrum is `f`.  These do not carry the
  tag; `AlgebraicGeometry.Space.directImageSpec_factorization` does.
* `AlgebraicGeometry.Space.boundedAlgebraHomSection_unique`: the section is the only morphism
  over `Y` which the anti-equivalence matches with that algebra map, so "canonical" is not an
  empty word here.
* The size side-condition the theorems carry is not a vacuous hypothesis: it is discharged for
  an *arbitrary* morphism, by `AlgebraicGeometry.Space.sectionsBelowCutoff_pushforwardAlgebra` of
  `StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraSectionsCutoff`; see the
  implementation notes.

## Implementation notes

**What is carried and what is discharged.**  Of the inputs the factorization of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage` carries — an unrestricted
anti-equivalence `E`, a base-change compatibility `C`, quasi-coherence `hqc` and the identity
clause `hid` of Stacks 03G8 — this file carries only the first, and in its bounded form.  `hid`
is discharged by `AlgebraicGeometry.Space.pushforwardAlgebraIdAlgebraIso`.  Of the twelve
fields of `AlgebraicGeometry.Space.BaseChangeCompatibility`, the six this construction uses are
discharged here or in `StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback`:
`algebraPullback`, `algebraPullbackMap` and `algebraPullback_isPushout` there, and
`affineBaseChange`, `affineBaseChange_projection` and `affineBaseChange_isPullback` here — the
last three at an object, `affineBaseChange` being a functor in the structure and only its value
on objects being built here, which is all this construction needs.  Two hypotheses are still
carried as binders below, but only one of them is something the development does not have:

* `hb`, the size condition `AlgebraicGeometry.Space.AlgebraSheaf.SectionsBelowCutoff` on
  `f_* 𝒪_Y`, **is dischargeable outright**, with no hypothesis on the morphism at all — not
  affineness, not quasi-compactness, not quasi-separatedness, not representability.  It is
  `AlgebraicGeometry.Space.sectionsBelowCutoff_pushforwardAlgebra` of
  `StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraSectionsCutoff`.  It survives as a
  binder on the declarations below only because removing it is a change of statement rather than
  of prose, and is not made here; this file does not import the discharging one.

  What this note said before was that bounding `f_* 𝒪_Y (V)` for a non-affine `f` would need a
  surjective étale chart of the algebraic space `Y ×_X V` *together with* a sections formula for
  the direct image of a sheaf of commutative rings along a non-representable morphism.  That was
  wrong on both halves.  The chart is Tag 03H7, which the tree has as
  `AlgebraicGeometry.Space.exists_smallEtaleDirectImageChartEqualizerEquiv`, and it is the only
  ingredient the bound needs; the sections formula is indeed still absent, but a cardinality
  *upper* bound never wanted it, because a bound asks for the sections injected into something
  small and not identified.  Tag 03H7 presents `(f_* 𝒪_Y)(V)` as an equalizer, hence a subtype
  of the regular functions on an étale scheme chart of `Y`, and a subtype is no larger than its
  ambient type.

  The same bound, chart by chart, is
  `AlgebraicGeometry.Space.mk_sections_pushforwardAlgebra_lt_cutoff` of
  `StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSectionsBounded`, by the same
  equalizer presentation.
* `bc`, the identification `w_* 𝒪_{Y ×_X \underline{Spec}_X(f_* 𝒪_Y)} ≅ f^* f_* 𝒪_Y`.  This is
  the `baseChangeIso` field of `AlgebraicGeometry.Space.BaseChangeCompatibility` read at one
  algebra, and it is one of the **two** fields of that structure which mention the
  anti-equivalence at all, the other being `baseChangeIso_canonical`.  It is carried as a bare
  isomorphism rather than through a bounded copy of the structure on purpose: cloning the
  structure's ten anti-equivalence-free fields would duplicate six fields the tree proves and
  four it does not, and the right change is to split the ten off into a structure independent of
  the anti-equivalence.  That is a refactor of
  `StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence` and is **not** done here;
  it is the change this file would consume.

  Note that both of the anti-equivalence-mentioning fields mention it essentially — they are
  stated in terms of `E.equivalence` — so the base-change clause of Stacks 081V cannot be
  completed without an inhabitant of the anti-equivalence.  Discharging `hb` does not touch that.

**Relation to the delivered form.**  Every factorization statement below takes the bounded
anti-equivalence `E : AlgebraicGeometry.Space.BoundedAffineAlgebraAntiEquivalence B S hS` and the
isomorphism `bc` as arguments, so none of them is registered for Stacks 081X.  The tag is
delivered by `AlgebraicGeometry.Space.directImageSpec_factorization` of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSpecFactorization`, which needs neither: its
relative spectrum `AlgebraicGeometry.Space.directImageSpec` is
`AlgebraicGeometry.Space.boundedRelativeSpec` of `f_* 𝒪_Y`, built from its functor of points, and
its canonical morphism `AlgebraicGeometry.Space.toDirectImageSpec` comes from the universal
property of the relative spectrum rather than from a base-change identification.  The three
inputs of 081V's anti-equivalence clause are also proved —
`AlgebraicGeometry.Space.faithful_affinePushforwardAlgebraFunctor`,
`AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor` and
`AlgebraicGeometry.Space.essSurj_boundedPushforwardAlgebraFunctor` — so
`AlgebraicGeometry.Space.boundedAffineAlgebraAntiEquivalenceOfIsEquivalence` yields an `E`.

**Why the construction is the source's.**  Stacks 081X says the algebra map `f^* f_* 𝒪_Y ⟶ 𝒪_Y`
"corresponds to" a morphism `Y ⟶ Y ×_X \underline{Spec}_X(f_* 𝒪_Y)` over `Y`, and that composing
that section with the projection gives the factorization.  The correspondence used here is the
bounded anti-equivalence over `Y` applied to `AlgebraicGeometry.Space.idAffineOver`: the identity
of `Y` is affine, so `Y` over itself is an object of the source category, and a morphism over `Y`
out of it into an algebraic space affine over `Y` is a morphism of bounded quasi-coherent
algebras in the other direction.  That is a *bijection*, which is what makes
`AlgebraicGeometry.Space.boundedAlgebraHomSection_unique` available and the morphism canonical.
The one place the anti-equivalence has to be applied to an algebra that is not visibly a direct
image is the relative spectrum itself, and that is where the bounded form asks for `hb`; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence`.

**The restriction of an unrestricted anti-equivalence.**  That an unrestricted anti-equivalence
restricts to a bounded one is `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.toBounded`,
in `StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalenceRestriction`, and it
is not reproved here.  One consequence of how it is built matters to a reader of this file: its
equivalence is obtained by `CategoryTheory.Functor.asEquivalence` from full faithfulness and
essential surjectivity of the restricted functor, so its *inverse* is not the inverse of the
given equivalence, and the relative spectrum computed from the restricted structure is
isomorphic to `AlgebraicGeometry.Space.relativeSpec` of the original rather than equal to it.
Nothing in this file depends on which inverse is taken.

**Related results.**

* The identity clause of Stacks 03G8, which
  `StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage` carries as the hypothesis `hid`,
  is `AlgebraicGeometry.Space.isIso_fSharp_id`, and the algebra-level isomorphism `hid` asks for
  is `AlgebraicGeometry.Space.pushforwardAlgebraIdAlgebraIso` of this file, proved from it with no
  hypothesis at all.  Stacks 03M9 is
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`, which is what
  `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra_of_qcqs` uses.
* The structure `AlgebraicGeometry.Space.BaseChangeCompatibility` has **twelve** fields, and
  **ten** of them do not mention the anti-equivalence: the two that do are `baseChangeIso` and
  `baseChangeIso_canonical`.  Six of the ten are *provable*, not merely independent of it:
  `algebraPullback`, `algebraPullbackMap` and `algebraPullback_isPushout` are constructed in
  `StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback`, and `affineBaseChange`,
  `affineBaseChange_projection` and `affineBaseChange_isPullback` are constructed in this file at
  an object.  The remaining four — `algebraPullback_isQuasicoherent`,
  `affineBaseChange_projection_naturality`, `pushforwardBaseChangeMap` and
  `pushforwardBaseChangeMap_canonical` — are not.
* Stacks 03M3 is proved as a full equivalence at
  `AlgebraicGeometry.Space.isEquivalence_quasicoherentFromSpaceBase` and
  `AlgebraicGeometry.Space.equivalenceQuasicoherentFromSpaceBase` in
  `StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseEquivalence`, as
  `StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence` also records.

## References

* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The identity clause of Stacks 03G8 at the level of algebras -/

namespace AlgebraSheaf

/-- An isomorphism of the underlying sheaves of rings which carries one structure map to the
other is an isomorphism of the algebra sheaves those structure maps present.  This is
`AlgebraicGeometry.Space.AlgebraSheaf.ofHomMap` in both directions; the two round trips are
equalities of the underlying morphisms of sheaves of rings, because a morphism of algebra sheaves
is determined by that morphism. -/
def ofHomIso {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    {R R' : Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u}}
    {a : structureSheaf B S hS F hF ⟶ R} {a' : structureSheaf B S hS F hF ⟶ R'}
    (ρ : R ≅ R') (h : a ≫ ρ.hom = a') :
    AlgebraSheaf.ofHom a ≅ AlgebraSheaf.ofHom a' where
  hom := ofHomMap ρ.hom h
  inv := ofHomMap ρ.inv (by rw [← h, Category.assoc, ρ.hom_inv_id, Category.comp_id])
  hom_inv_id := Hom.ext (by simp)
  inv_hom_id := Hom.ext (by simp)

end AlgebraSheaf

/-- **The direct image of `𝒪_Y` along the identity of `Y` is `𝒪_Y`, as an `𝒪_Y`-algebra**, with
no anti-equivalence and no hypothesis.

`AlgebraicGeometry.Space.pushforwardAlgebra` of a morphism is its structure map read as an
algebra structure, so this is the identity clause of Stacks 03G8 — the structure map of an
identity is an isomorphism, `AlgebraicGeometry.Space.isIso_fSharp_id` — read through
`AlgebraicGeometry.Space.AlgebraSheaf.ofHomIso`: the inverse of that structure map carries it to
the identity of `𝒪_Y`, which is the structure map of `AlgebraicGeometry.Space.unitAlgebra`.

This is the isomorphism that `AlgebraicGeometry.Space.pushforwardAlgebraIdIso` of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization` obtains from an assumed
anti-equivalence and that
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage` carries as the hypothesis
`hid`. -/
@[stacks 03G8 "the identity clause at the level of algebras: (𝟙_Y)_* 𝒪_Y is 𝒪_Y"]
def pushforwardAlgebraIdAlgebraIso (Y : AlgebraicSpaces B S hS) :
    pushforwardAlgebra B S hS (Over.mk (𝟙 Y)) ≅ unitAlgebra B S hS Y := by
  haveI : IsIso (smallEtaleRingedToposHom B S hS (Over.mk (𝟙 Y)).hom).fSharp :=
    isIso_fSharp_id B S hS Y
  exact AlgebraSheaf.ofHomIso B S hS
    (asIso (smallEtaleRingedToposHom B S hS (Over.mk (𝟙 Y)).hom).fSharp).symm
    (IsIso.hom_inv_id _)

/-! ### The base change of an algebraic space affine over the base -/

variable {X Y : AlgebraicSpaces B S hS}

/-- **The base change `Y ×_X Z` of an algebraic space `Z` affine over `X`**, as an algebraic
space affine over `Y`.  Fibre products of algebraic spaces exist, by Stacks 02X2
(`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`), and an affine morphism stays
affine under base change, by Stacks 03WI
(`AlgebraicGeometry.Space.isAffineHom_hom_of_isPullback`).

This has the type of the `affineBaseChange` field of
`AlgebraicGeometry.Space.BaseChangeCompatibility` at one object, and needs no anti-equivalence
and no base-change compatibility. -/
def affineOverBaseChange (f : Y ⟶ X) (Z : AffineOver B S hS X) : AffineOver B S hS Y :=
  ⟨Over.mk (ObjectProperty.homMk (pullback.snd Z.obj.hom.hom f.hom) :
      AlgebraicSpaces.fiberProduct B S hS Z.obj.hom f ⟶ Y),
    isAffineHom_hom_of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS Z.obj.hom f) Z.property⟩

/-- The projection `Y ×_X Z ⟶ Z` of the base change. -/
def affineOverBaseChangeProjection (f : Y ⟶ X) (Z : AffineOver B S hS X) :
    (affineOverBaseChange B S hS f Z).obj.left ⟶ Z.obj.left :=
  ObjectProperty.homMk (pullback.fst Z.obj.hom.hom f.hom)

/-- The base change of an algebraic space affine over `X` is a cartesian square. -/
theorem affineOverBaseChange_isPullback (f : Y ⟶ X) (Z : AffineOver B S hS X) :
    IsPullback (affineOverBaseChangeProjection B S hS f Z)
      (affineOverBaseChange B S hS f Z).obj.hom Z.obj.hom f :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS Z.obj.hom f

/-! ### The canonical algebra map `f^* f_* 𝒪_Y ⟶ 𝒪_Y` -/

/-- **The canonical map `f^* f_* 𝒪_Y ⟶ 𝒪_Y` of sheaves of commutative rings**, with no
base-change compatibility carried.  Algebra pullback is extension of scalars
(`AlgebraicGeometry.Space.algebraPullback_isPushout`), so `f^* f_* 𝒪_Y` is the pushout of `𝒪_Y`
and `f⁻¹ f_* 𝒪_Y` over `f⁻¹ 𝒪_X`; the map out of it is the counit of the
inverse-image/direct-image adjunction on one side and the identity of `𝒪_Y` on the other, and
those agree on `f⁻¹ 𝒪_X` because `AlgebraicGeometry.RingedToposHom.fSharpInverseImage` is by
definition the adjunct of `f^♯`.

This is `AlgebraicGeometry.Space.pullbackPushforwardCounit` of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage` with the pushout taken from the
construction of `StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback` instead of from the
`algebraPullback_isPushout` field of
`AlgebraicGeometry.Space.BaseChangeCompatibility`. -/
def algebraPullbackPushforwardCounit (f : Y ⟶ X) :
    ((algebraPullback B S hS f).obj (pushforwardAlgebra B S hS (Over.mk f))).right ⟶
      (smallEtaleRingedTopos B S hS Y).O :=
  (algebraPullback_isPushout B S hS f (pushforwardAlgebra B S hS (Over.mk f))).desc
    ((commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS f).toToposHom).counit.app
      (smallEtaleRingedTopos B S hS Y).O)
    (𝟙 (smallEtaleRingedTopos B S hS Y).O)
    ((Adjunction.homEquiv_counit
        (commRingImageAdjunction (smallEtaleRingedToposHom B S hS f).toToposHom)
        (smallEtaleRingedTopos B S hS X).O (smallEtaleRingedTopos B S hS Y).O
        (smallEtaleRingedToposHom B S hS f).fSharp).symm.trans
      (Category.comp_id _).symm)

/-- The canonical map `f^* f_* 𝒪_Y ⟶ 𝒪_Y` is a map of `𝒪_Y`-algebras: precomposing it with the
algebra structure map of `f^* f_* 𝒪_Y` gives the identity of `𝒪_Y`. -/
theorem algebraPullbackPushforwardCounit_structure (f : Y ⟶ X) :
    ((algebraPullback B S hS f).obj (pushforwardAlgebra B S hS (Over.mk f))).hom ≫
        algebraPullbackPushforwardCounit B S hS f =
      𝟙 (structureSheaf B S hS Y.1 Y.2) := by
  dsimp only [algebraPullbackPushforwardCounit]
  exact IsPushout.inr_desc _ _ _ _

/-- The canonical map `f^* f_* 𝒪_Y ⟶ 𝒪_Y` as a morphism of algebra sheaves into
`AlgebraicGeometry.Space.unitAlgebra`. -/
def algebraPullbackPushforwardCounitAlgebraHom (f : Y ⟶ X) :
    (algebraPullback B S hS f).obj (pushforwardAlgebra B S hS (Over.mk f)) ⟶
      unitAlgebra B S hS Y where
  right := algebraPullbackPushforwardCounit B S hS f
  comm U r := by
    have h : ((((algebraPullback B S hS f).obj (pushforwardAlgebra B S hS (Over.mk f))).hom ≫
        algebraPullbackPushforwardCounit B S hS f).hom.app U).hom r = r := by
      rw [algebraPullbackPushforwardCounit_structure]; rfl
    rw [ObjectProperty.FullSubcategory.comp_hom] at h
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    exact h

/-! ### Sections over `Y` from algebra maps, for a bounded anti-equivalence -/

variable (E : BoundedAffineAlgebraAntiEquivalence B S hS)

/-- An algebra map `w_* 𝒪_W ⟶ 𝒪_Y`, read as a morphism of the bounded quasi-coherent algebras
that the anti-equivalence assigns to `W` and to `Y` over itself.  The two identifications are
`pushforwardIso` and `pushforward_obj` of the anti-equivalence, and
`AlgebraicGeometry.Space.pushforwardAlgebraIdAlgebraIso` for the second object, whose
direct-image algebra is `(𝟙_Y)_* 𝒪_Y` and not `𝒪_Y` on the nose. -/
def boundedPushforwardAlgebraHom (W : AffineOver B S hS Y)
    (ι : pushforwardAlgebra B S hS W.obj ⟶ unitAlgebra B S hS Y) :
    (E.equivalence Y).functor.obj (op W) ⟶
      (E.equivalence Y).functor.obj (op (idAffineOver B S hS Y)) :=
  ((E.pushforwardIso Y).app (op W)).hom ≫
    (boundedAlgebraSheafInclusion B S hS Y).preimage
      ((E.pushforward_obj Y W).hom ≫ ι ≫
        (pushforwardAlgebraIdAlgebraIso B S hS Y).inv ≫
        (E.pushforward_obj Y (idAffineOver B S hS Y)).inv) ≫
    ((E.pushforwardIso Y).app (op (idAffineOver B S hS Y))).inv

/-- **The section `Y ⟶ W` over `Y` which the bounded anti-equivalence matches with an algebra
map `w_* 𝒪_W ⟶ 𝒪_Y`.**  The identity of `Y` is affine, so `Y` over itself is an object of the
source category of the anti-equivalence over `Y`, and the anti-equivalence turns a morphism of
algebras in one direction into a morphism over `Y` in the other. -/
def boundedAlgebraHomSection (W : AffineOver B S hS Y)
    (ι : pushforwardAlgebra B S hS W.obj ⟶ unitAlgebra B S hS Y) :
    idAffineOver B S hS Y ⟶ W :=
  ((E.equivalence Y).functor.preimage (boundedPushforwardAlgebraHom B S hS E W ι)).unop

/-- The morphism of `AlgebraicGeometry.Space.boundedAlgebraHomSection` is a section of the
structure morphism of `W`. -/
theorem boundedAlgebraHomSection_section (W : AffineOver B S hS Y)
    (ι : pushforwardAlgebra B S hS W.obj ⟶ unitAlgebra B S hS Y) :
    (boundedAlgebraHomSection B S hS E W ι).hom.left ≫ W.obj.hom = 𝟙 Y :=
  Over.w _

/-- The anti-equivalence sends the section back to the algebra map it was built from. -/
theorem functor_map_boundedAlgebraHomSection (W : AffineOver B S hS Y)
    (ι : pushforwardAlgebra B S hS W.obj ⟶ unitAlgebra B S hS Y) :
    (E.equivalence Y).functor.map (op (boundedAlgebraHomSection B S hS E W ι)) =
      boundedPushforwardAlgebraHom B S hS E W ι :=
  (E.equivalence Y).functor.map_preimage _

/-- **The section is the only morphism over `Y` which the anti-equivalence matches with the
given algebra map**, because the anti-equivalence is faithful.  This is what makes the morphism
of `AlgebraicGeometry.Space.boundedDirectImageFactorizationMap` canonical. -/
theorem boundedAlgebraHomSection_unique (W : AffineOver B S hS Y)
    (ι : pushforwardAlgebra B S hS W.obj ⟶ unitAlgebra B S hS Y)
    (s : idAffineOver B S hS Y ⟶ W)
    (hs : (E.equivalence Y).functor.map (op s) = boundedPushforwardAlgebraHom B S hS E W ι) :
    s = boundedAlgebraHomSection B S hS E W ι :=
  Quiver.Hom.op_inj
    ((E.equivalence Y).functor.map_injective
      (hs.trans (functor_map_boundedAlgebraHomSection B S hS E W ι).symm))

/-! ### The relative spectrum of the direct-image algebra -/

/-- **The relative spectrum `\underline{Spec}_X(f_* 𝒪_Y)`** for a bounded anti-equivalence, as an
algebraic space affine over `X`.  Quasi-coherence of `f_* 𝒪_Y` is `hqc`, which Stacks 03M9
supplies for a quasi-compact quasi-separated `f`; `hb` is the size condition the bounded target
imposes. -/
def boundedRelativeSpecDirectImage (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hb : AlgebraSheaf.SectionsBelowCutoff B S hS (pushforwardAlgebra B S hS (Over.mk f))) :
    AffineOver B S hS X :=
  E.relativeSpec (directImageAlgebra B S hS f hqc) hb

/-- The direct image of the structure sheaf of `\underline{Spec}_X(f_* 𝒪_Y)` is `f_* 𝒪_Y`: the
counit of the bounded anti-equivalence, read through its identification with direct image.  This
is what makes the middle term of the factorization the relative spectrum of `f_* 𝒪_Y` and not
merely some algebraic space affine over `X`. -/
def boundedRelativeSpecDirectImagePushforwardIso (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hb : AlgebraSheaf.SectionsBelowCutoff B S hS (pushforwardAlgebra B S hS (Over.mk f))) :
    pushforwardAlgebra B S hS (boundedRelativeSpecDirectImage B S hS E f hqc hb).obj ≅
      pushforwardAlgebra B S hS (Over.mk f) :=
  E.relativeSpecPushforwardIso (directImageAlgebra B S hS f hqc) hb

/-- The structure morphism `\underline{Spec}_X(f_* 𝒪_Y) ⟶ X` of the middle term of the
factorization is affine. -/
theorem isAffineHom_boundedRelativeSpecDirectImage (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hb : AlgebraSheaf.SectionsBelowCutoff B S hS (pushforwardAlgebra B S hS (Over.mk f))) :
    IsAffineHom B S hS (boundedRelativeSpecDirectImage B S hS E f hqc hb).obj.hom.hom :=
  (boundedRelativeSpecDirectImage B S hS E f hqc hb).property

/-! ### The canonical factorization -/

/-- The canonical section `Y ⟶ Y ×_X \underline{Spec}_X(f_* 𝒪_Y)` over `Y`: the morphism which
the bounded anti-equivalence over `Y` matches with the canonical algebra map `f^* f_* 𝒪_Y ⟶ 𝒪_Y`,
read through the base-change identification `bc`. -/
def boundedDirectImageSection (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hb : AlgebraSheaf.SectionsBelowCutoff B S hS (pushforwardAlgebra B S hS (Over.mk f)))
    (bc : pushforwardAlgebra B S hS
        (affineOverBaseChange B S hS f
          (boundedRelativeSpecDirectImage B S hS E f hqc hb)).obj ≅
      (algebraPullback B S hS f).obj (pushforwardAlgebra B S hS (Over.mk f))) :
    idAffineOver B S hS Y ⟶
      affineOverBaseChange B S hS f (boundedRelativeSpecDirectImage B S hS E f hqc hb) :=
  boundedAlgebraHomSection B S hS E
    (affineOverBaseChange B S hS f (boundedRelativeSpecDirectImage B S hS E f hqc hb))
    (bc.hom ≫ algebraPullbackPushforwardCounitAlgebraHom B S hS f)

/-- **The canonical morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` over `X`** attached to a morphism
`f : Y ⟶ X` whose direct-image algebra is quasi-coherent and satisfies the size condition of the
bounded form of Stacks 081V: the canonical section over `Y`, composed with the projection of the
base change. -/
def boundedDirectImageFactorizationMap (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hb : AlgebraSheaf.SectionsBelowCutoff B S hS (pushforwardAlgebra B S hS (Over.mk f)))
    (bc : pushforwardAlgebra B S hS
        (affineOverBaseChange B S hS f
          (boundedRelativeSpecDirectImage B S hS E f hqc hb)).obj ≅
      (algebraPullback B S hS f).obj (pushforwardAlgebra B S hS (Over.mk f))) :
    Over.mk f ⟶ (boundedRelativeSpecDirectImage B S hS E f hqc hb).obj :=
  Over.homMk
    ((boundedDirectImageSection B S hS E f hqc hb bc).hom.left ≫
      affineOverBaseChangeProjection B S hS f
        (boundedRelativeSpecDirectImage B S hS E f hqc hb))
    (((Category.assoc _ _ _).trans
        (congrArg
          (fun k => (boundedDirectImageSection B S hS E f hqc hb bc).hom.left ≫ k)
          (affineOverBaseChange_isPullback B S hS f
            (boundedRelativeSpecDirectImage B S hS E f hqc hb)).w)).trans
      (((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ f)
            (Over.w (boundedDirectImageSection B S hS E f hqc hb bc).hom))).trans
        (Category.id_comp f)))

/-- **The canonical factorization `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X` of Stacks 081X**, for an
anti-equivalence of Stacks 081V whose target is cut down to the algebras below the site's cutoff.
The canonical morphism composed with the structure morphism of the relative spectrum of
`f_* 𝒪_Y` is `f`.

Unlike `AlgebraicGeometry.Space.directImageFactorizationMap_factorization`, which presupposes
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` and is therefore vacuous, the
anti-equivalence here is the bounded one, which the size obstruction does not refute; an
unrestricted anti-equivalence restricts to a bounded one by
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.toBounded`, so this hypothesis is the
weaker of the two.

This statement does not carry Stacks 081X: it takes `E` and `bc` as arguments.  The tag is
delivered unconditionally by `AlgebraicGeometry.Space.directImageSpec_factorization` of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSpecFactorization`. -/
theorem boundedDirectImageFactorizationMap_factorization (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hb : AlgebraSheaf.SectionsBelowCutoff B S hS (pushforwardAlgebra B S hS (Over.mk f)))
    (bc : pushforwardAlgebra B S hS
        (affineOverBaseChange B S hS f
          (boundedRelativeSpecDirectImage B S hS E f hqc hb)).obj ≅
      (algebraPullback B S hS f).obj (pushforwardAlgebra B S hS (Over.mk f))) :
    (boundedDirectImageFactorizationMap B S hS E f hqc hb bc).left ≫
        (boundedRelativeSpecDirectImage B S hS E f hqc hb).obj.hom = f :=
  Over.w _

/-! ### The factorization of a quasi-compact, quasi-separated morphism -/

variable (f : Y ⟶ X) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (hb : AlgebraSheaf.SectionsBelowCutoff B S hS (pushforwardAlgebra B S hS (Over.mk f)))

/-- The relative spectrum `\underline{Spec}_X(f_* 𝒪_Y)` of the direct-image algebra of a
quasi-compact, quasi-separated morphism, whose quasi-coherence is Stacks 03M9. -/
def boundedQcqsRelativeSpecDirectImage : AffineOver B S hS X :=
  boundedRelativeSpecDirectImage B S hS E f
    (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS f hfqc hfqs) hb

/-- **The canonical morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` over `X`** attached to a
quasi-compact, quasi-separated morphism `f : Y ⟶ X` of algebraic spaces. -/
def boundedQcqsDirectImageFactorizationMap
    (bc : pushforwardAlgebra B S hS
        (affineOverBaseChange B S hS f
          (boundedQcqsRelativeSpecDirectImage B S hS E f hfqc hfqs hb)).obj ≅
      (algebraPullback B S hS f).obj (pushforwardAlgebra B S hS (Over.mk f))) :
    Over.mk f ⟶ (boundedQcqsRelativeSpecDirectImage B S hS E f hfqc hfqs hb).obj :=
  boundedDirectImageFactorizationMap B S hS E f
    (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS f hfqc hfqs) hb bc

/-- **The factorization of Stacks 081X, against a given bounded anti-equivalence.**  A
quasi-compact, quasi-separated morphism `f : Y ⟶ X` of algebraic spaces factors canonically as
`Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X`, the middle term being the relative spectrum of the
quasi-coherent algebra `f_* 𝒪_Y` taken with an anti-equivalence of Stacks 081V against the
algebras below the site's cutoff.

This is `AlgebraicGeometry.Space.qcqsDirectImageFactorizationMap_factorization` with its
anti-equivalence replaced by one the size obstruction does not refute; see the implementation
notes for the arguments it takes.  It does not carry Stacks 081X: the tag is delivered, with
neither `E`, `hb` nor `bc`, by `AlgebraicGeometry.Space.directImageSpec_factorization` of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSpecFactorization`. -/
theorem boundedQcqsDirectImageFactorizationMap_factorization
    (bc : pushforwardAlgebra B S hS
        (affineOverBaseChange B S hS f
          (boundedQcqsRelativeSpecDirectImage B S hS E f hfqc hfqs hb)).obj ≅
      (algebraPullback B S hS f).obj (pushforwardAlgebra B S hS (Over.mk f))) :
    (boundedQcqsDirectImageFactorizationMap B S hS E f hfqc hfqs hb bc).left ≫
        (boundedQcqsRelativeSpecDirectImage B S hS E f hfqc hfqs hb).obj.hom = f :=
  Over.w _

end AlgebraicGeometry.Space

end
