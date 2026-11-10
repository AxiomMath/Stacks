module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.LocalStructure.Cotangent
public import StacksFrontier.AlgebraicGeometry.Groupoids.OpenArrowSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Etale.UniversallyInjectiveUnramified.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.OverPullbackLeft
public import StacksFrontier.AlgebraicGeometry.Scheme.UniversallyInjectiveSection

/-!
# The open and closed piece of the arrow scheme through the identity

Let `(U, R, s, t, c)` be a groupoid scheme whose object scheme `U` has exactly one point and
whose arrow scheme `R` is zero-dimensional, so that every point of `R` is open and closed.  The
point `e(u)` of `R` then cuts out an open and closed subscheme `P ⊆ R` which is a subgroupoid of
`R` on the same object scheme, with `s|_P` and `t|_P` finite.

This is the piece `P` of the proof of **Stacks 06N0**: there `U = Spec k`, `R = U ×_𝒵 U` for a
flat, locally finitely presented, surjective field-valued point of a DM stack with a one-point
space, and `R` is zero-dimensional because the stabilizer of the groupoid is unramified over
`U`.  The division of `(U, R, s, t, c)` by `P`, which **Stacks 04S4** performs, is what produces
the field `k₀` of invariants.

## What makes the piece a subgroupoid

Of the three conditions of `Stacks.Groupoids.GroupoidScheme.IsArrowSubgroupoid`, the first is the
choice of `P`; the other two are statements about points of `P` and about points of the scheme of
composable pairs of `P`, and both schemes turn out to have at most one point.

For `P` itself that is the hypothesis, and stability under the inverse is then the groupoid law
`i ∘ e = e`.

For the composable pairs it is not a hypothesis: `P ×_{s|_P, U, t|_P} P` is the base change of
`s|_P` along `t|_P`, and `s|_P` is *universally injective* because its source has one point and
the identity section of the groupoid is a section of it — this is
`AlgebraicGeometry.universallyInjective_of_subsingleton_of_section`, condition (3) of
**Stacks 01S4**.  A base change of a universally injective morphism is injective on points, so
the composable pairs of `P` have at most one point as well, and stability under the composition
is the groupoid law `c(e, e) = e`.  (This is the same mechanism as the computation
`A ⊗_{k ⊗ k} k = k` of the source, which is what makes `P ⟶ U × U` universally injective; here
only the weaker statement about `s|_P` is needed, and it comes from the identity section.)

Finiteness of `s|_P` and of `t|_P` is **Stacks 02NG** in the form
`AlgebraicGeometry.IsFinite.of_locallyQuasiFinite`: the morphism is locally of finite type with
a one-point source, hence locally quasi-finite and quasi-compact, and the object scheme is
zero-dimensional.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.openArrowIdentity`: the identity section of the groupoid,
  lifted to an open subscheme of the arrow scheme containing every identity arrow.
* `Stacks.Groupoids.GroupoidScheme.openArrowIdentityPair`: the pair of identities, as a section
  of the scheme of composable pairs of such an open.
* `Stacks.Groupoids.GroupoidScheme.identityArrowOpens`: the open subscheme of a zero-dimensional
  arrow scheme whose only point is the identity arrow `e(u)`.
* `Stacks.Groupoids.GroupoidScheme.identityOpenFiniteSubgroupoid`: that open, as an open finite
  subgroupoid in the sense of **Stacks 04RK**.

## Main results

* `Stacks.Groupoids.GroupoidScheme.subsingleton_openArrowComposables`: the composable pairs of a
  one-point open containing the identity arrows have at most one point.
* `Stacks.Groupoids.GroupoidScheme.isArrowSubgroupoid_of_subsingleton`: a one-point open of the
  arrow scheme containing the identity arrows is a subgroupoid.
* `Stacks.Groupoids.GroupoidScheme.isFinite_openArrowSource` and `isFinite_openArrowTarget`: the
  restricted source and target of such an open are finite.
* `Stacks.Groupoids.GroupoidScheme.isArrowSubgroupoid_identityArrowOpens`: for a groupoid scheme
  with a one-point object scheme and a zero-dimensional arrow scheme, the identity arrow cuts out
  an open and closed subgroupoid.
* `exists_openFiniteSubgroupoid_singleton_identity_of_isoSpecField`: for an object scheme
  isomorphic to the spectrum of a field, there is an open finite subgroupoid whose scheme of
  arrows has the identity arrow as its range.
* `Stacks.Groupoids.GroupoidScheme.isQuasiSplitAt_of_isLocallyArtinian_arrows`: such a groupoid
  scheme is quasi-split at every point of its object scheme.

## Implementation notes

Zero-dimensionality of the arrow scheme is `AlgebraicGeometry.IsLocallyArtinian`, which for a
locally Noetherian scheme is exactly `topologicalKrullDim ≤ 0` and which supplies the discrete
topology making the one-point subset open and closed.  The object scheme is asked to be locally
Artinian too, which is what `AlgebraicGeometry.IsFinite.of_locallyQuasiFinite` consumes; for an
object scheme isomorphic to the spectrum of a field both hypotheses on it — that it is a
subsingleton and that it is locally Artinian — are automatic, and that is the form
`exists_openFiniteSubgroupoid_singleton_identity_of_isoSpecField` is stated in.

The hypothesis that the open is a subsingleton is stated on `openOver G.arrows W`, the open read
as an object of `Over S`, since that is the scheme whose points the conditions of
`IsArrowSubgroupoid` quantify over.

## References

* [Stacks Project, Tag 01S4](https://stacks.math.columbia.edu/tag/01S4)
* [Stacks Project, Tag 02NG](https://stacks.math.columbia.edu/tag/02NG)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} {G : GroupoidScheme S} (W : G.arrows.left.Opens)

/-! ### The identity section of an open of the arrow scheme -/

/-- The identity section of a groupoid scheme, lifted to an open subscheme of the arrow scheme
which contains every identity arrow. -/
def openArrowIdentity (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W) :
    G.objects ⟶ openOver G.arrows W :=
  openOverLift G.identity W hid

/-- The lifted identity section followed by the inclusion of the open is the identity section. -/
@[simp]
theorem openArrowIdentity_comp_openOverι
    (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W) :
    openArrowIdentity W hid ≫ openOverι G.arrows W = G.identity :=
  openOverLift_comp_openOverι _ _ _

/-- The lifted identity section is a section of the restricted source map. -/
theorem openArrowIdentity_comp_source
    (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W) :
    openArrowIdentity W hid ≫ openArrowSource W = 𝟙 G.objects := by
  have h : openArrowIdentity W hid ≫ openArrowSource W =
      (openArrowIdentity W hid ≫ openOverι G.arrows W) ≫ G.source :=
    (Category.assoc _ _ _).symm
  rw [h, openArrowIdentity_comp_openOverι, G.source_identity]

/-- The lifted identity section is a section of the restricted target map. -/
theorem openArrowIdentity_comp_target
    (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W) :
    openArrowIdentity W hid ≫ openArrowTarget W = 𝟙 G.objects := by
  have h : openArrowIdentity W hid ≫ openArrowTarget W =
      (openArrowIdentity W hid ≫ openOverι G.arrows W) ≫ G.target :=
    (Category.assoc _ _ _).symm
  rw [h, openArrowIdentity_comp_openOverι, G.target_identity]

/-- The pair of identities, as a section of the scheme of composable pairs of arrows of an open
subscheme of the arrow scheme which contains every identity arrow. -/
def openArrowIdentityPair (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W) :
    G.objects ⟶ pullback (openArrowSource W) (openArrowTarget W) :=
  pullback.lift (openArrowIdentity W hid) (openArrowIdentity W hid)
    (by rw [openArrowIdentity_comp_source, openArrowIdentity_comp_target])

/-- The pair of identities of an open, mapped into the composable pairs of the arrow scheme, is
the pair of identities of the groupoid. -/
theorem openArrowIdentityPair_comp_openArrowComposables
    (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W) :
    openArrowIdentityPair W hid ≫ openArrowComposables W = G.identityPair := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, show openArrowComposables W ≫ pullback.fst G.source G.target =
        pullback.fst (openArrowSource W) (openArrowTarget W) ≫ openOverι G.arrows W from
      pullback.lift_fst _ _ _, ← Category.assoc, openArrowIdentityPair, pullback.lift_fst,
      openArrowIdentity_comp_openOverι, G.identityPair_fst]
  · rw [Category.assoc, show openArrowComposables W ≫ pullback.snd G.source G.target =
        pullback.snd (openArrowSource W) (openArrowTarget W) ≫ openOverι G.arrows W from
      pullback.lift_snd _ _ _, ← Category.assoc, openArrowIdentityPair, pullback.lift_snd,
      openArrowIdentity_comp_openOverι, G.identityPair_snd]

/-- The composite of the pair of identities of an open is the identity section. -/
theorem openArrowIdentityPair_comp_comp
    (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W) :
    openArrowIdentityPair W hid ≫ openArrowComposables W ≫ G.comp = G.identity := by
  rw [← Category.assoc, openArrowIdentityPair_comp_openArrowComposables, G.identityPair_comp]

/-! ### The three conditions at a one-point open -/

/-- Every point of a one-point open of the arrow scheme containing the identity arrows *is* an
identity arrow. -/
theorem openOverι_apply_eq_identity [Subsingleton (openOver G.arrows W).left]
    (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W)
    (x : (openOver G.arrows W).left) (u : G.objects.left) :
    (openOverι G.arrows W).left.base x = G.identity.left.base u := by
  have hx : x = (openArrowIdentity W hid).left.base u := Subsingleton.elim _ _
  subst hx
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, openArrowIdentity_comp_openOverι]

/-- **Stability under the inverse at a one-point open.**  The inverse of an arrow of a one-point
open of the arrow scheme containing the identity arrows is again an arrow of it, because that
arrow is an identity arrow and the inverse fixes identity arrows. -/
theorem mem_inverse_of_subsingleton [Nonempty G.objects.left]
    [Subsingleton (openOver G.arrows W).left]
    (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W)
    (x : (openOver G.arrows W).left) :
    (openOverι G.arrows W ≫ G.inverse).left.base x ∈ W := by
  obtain ⟨u⟩ := ‹Nonempty G.objects.left›
  rw [Over.comp_left, Scheme.Hom.comp_apply, openOverι_apply_eq_identity W hid x u,
    G.inverse_apply_identity]
  exact hid u

/-- **Stability under the composition at a one-point open.**  If the scheme of composable pairs
of a one-point open of the arrow scheme containing the identity arrows has at most one point,
then the composite of a composable pair of its arrows lies in it, because that pair is the pair
of identities and the composite of the pair of identities is an identity arrow. -/
theorem mem_comp_of_subsingleton [Nonempty G.objects.left]
    (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W)
    (hQ : Subsingleton (pullback (openArrowSource W) (openArrowTarget W)).left)
    (z : (pullback (openArrowSource W) (openArrowTarget W)).left) :
    (openArrowComposables W ≫ G.comp).left.base z ∈ W := by
  obtain ⟨u⟩ := ‹Nonempty G.objects.left›
  have hz : z = (openArrowIdentityPair W hid).left.base u := Subsingleton.elim _ _
  subst hz
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, openArrowIdentityPair_comp_comp]
  exact hid u

/-! ### The composable pairs of a one-point open -/

/-- **The source map restricted to a one-point open of the arrow scheme containing the identity
arrows is universally injective.**  Its source has at most one point and the identity section of
the groupoid is a section of it, so this is
`AlgebraicGeometry.universallyInjective_of_subsingleton_of_section`, condition (3) of
**Stacks 01S4**. -/
theorem universallyInjective_openArrowSource [Subsingleton (openOver G.arrows W).left]
    (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W) :
    UniversallyInjective (openArrowSource W).left := by
  refine universallyInjective_of_subsingleton_of_section (openArrowSource W).left
    (openArrowIdentity W hid).left ?_
  have h := congrArg Over.Hom.left (openArrowIdentity_comp_source W hid)
  rwa [Over.comp_left, Over.id_left] at h

/-- **The scheme of composable pairs of a one-point open of the arrow scheme containing the
identity arrows has at most one point.**  The restricted source map has a section, namely the
identity section of the groupoid, and a one-point source, so it is universally injective by
condition (3) of **Stacks 01S4**; the second projection of the scheme of composable pairs is a
base change of it, hence injective on points, and its target has at most one point. -/
theorem subsingleton_openArrowComposables [Subsingleton (openOver G.arrows W).left]
    (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W) :
    Subsingleton (pullback (openArrowSource W) (openArrowTarget W)).left := by
  have hui : UniversallyInjective (openArrowSource W).left :=
    universallyInjective_openArrowSource W hid
  have : UniversallyInjective
      (pullback.snd (openArrowSource W).left (openArrowTarget W).left) :=
    MorphismProperty.of_isPullback (P := @UniversallyInjective)
      (IsPullback.of_hasPullback _ _) hui
  have hsub : Subsingleton
      (pullback (openArrowSource W).left (openArrowTarget W).left : Scheme.{u}) :=
    ⟨fun a b => (pullback.snd (openArrowSource W).left
      (openArrowTarget W).left).injective (Subsingleton.elim _ _)⟩
  refine ⟨fun a b => ?_⟩
  exact (overPullbackLeftIso (openArrowSource W) (openArrowTarget W)).hom.homeomorph.injective
    (Subsingleton.elim _ _)

/-- **A one-point open of the arrow scheme containing the identity arrows is a subgroupoid.** -/
theorem isArrowSubgroupoid_of_subsingleton [Nonempty G.objects.left]
    [Subsingleton (openOver G.arrows W).left]
    (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W) :
    IsArrowSubgroupoid W where
  mem_identity := hid
  mem_inverse := mem_inverse_of_subsingleton W hid
  mem_comp := mem_comp_of_subsingleton W hid (subsingleton_openArrowComposables W hid)

/-! ### Finiteness of the restricted source and target -/

/-- A morphism locally of finite type from a one-point scheme to a locally Artinian scheme is
finite. -/
private theorem isFinite_of_subsingleton_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Subsingleton X] [LocallyOfFiniteType f] [IsLocallyArtinian Y] : IsFinite f := by
  have : Finite X := Finite.of_subsingleton
  have : LocallyQuasiFinite f :=
    locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr fun _ =>
      _root_.isDiscrete_iff_discreteTopology.mpr inferInstance
  have : QuasiCompact f := ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
  exact IsFinite.of_locallyQuasiFinite _

/-- **The source map restricted to a one-point open of the arrow scheme is finite**, as soon as
the source map is locally of finite type and the object scheme is zero-dimensional. -/
theorem isFinite_openArrowSource [Subsingleton (openOver G.arrows W).left]
    [LocallyOfFiniteType G.source.left] [IsLocallyArtinian G.objects.left] :
    IsFinite (openArrowSource W).left := by
  have : LocallyOfFiniteType (openArrowSource W).left :=
    inferInstanceAs (LocallyOfFiniteType ((openOverι G.arrows W).left ≫ G.source.left))
  exact isFinite_of_subsingleton_of_locallyOfFiniteType _

/-- **The target map restricted to a one-point open of the arrow scheme is finite**, as soon as
the target map is locally of finite type and the object scheme is zero-dimensional. -/
theorem isFinite_openArrowTarget [Subsingleton (openOver G.arrows W).left]
    [LocallyOfFiniteType G.target.left] [IsLocallyArtinian G.objects.left] :
    IsFinite (openArrowTarget W).left := by
  have : LocallyOfFiniteType (openArrowTarget W).left :=
    inferInstanceAs (LocallyOfFiniteType ((openOverι G.arrows W).left ≫ G.target.left))
  exact isFinite_of_subsingleton_of_locallyOfFiniteType _

/-! ### The pre-relation of a one-point open -/

/-- The pre-relation of the subgroupoid cut out by an open subscheme of the arrow scheme is the
ambient pre-relation restricted to that open. -/
theorem prodLift_openArrowTarget_openArrowSource :
    prod.lift (openArrowTarget W) (openArrowSource W) =
      openOverι G.arrows W ≫ prod.lift G.target G.source := by
  refine prod.hom_ext ?_ ?_
  · rw [prod.lift_fst, Category.assoc, prod.lift_fst]
  · rw [prod.lift_snd, Category.assoc, prod.lift_snd]

/-- **The pre-relation of a one-point open of the arrow scheme containing the identity arrows is
universally injective.**  It is the first factor of the restricted source map, which is
universally injective, and universal injectivity is cancellable on the right. -/
theorem universallyInjective_prodLift [Subsingleton (openOver G.arrows W).left]
    (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W) :
    UniversallyInjective (prod.lift (openArrowTarget W) (openArrowSource W)).left := by
  refine universallyInjective_of_comp _
    (prod.snd : G.objects ⨯ G.objects ⟶ G.objects).left ?_
  have h : (prod.lift (openArrowTarget W) (openArrowSource W)).left ≫
      (prod.snd : G.objects ⨯ G.objects ⟶ G.objects).left = (openArrowSource W).left := by
    rw [← Over.comp_left, prod.lift_snd]
  rw [h]
  exact universallyInjective_openArrowSource W hid

/-- **The pre-relation of a one-point open of the arrow scheme containing the identity arrows is
a monomorphism**, as soon as the ambient pre-relation is unramified.

This is the role of the computation `A ⊗_{k ⊗ k} k = k` in the proof of **Stacks 06N0**: it is
what makes `P ⟶ U × U` universally injective there, and universal injectivity together with
unramifiedness is a monomorphism by **Stacks 05VH**, part (2) implies part (1).  Here universal
injectivity comes instead from the identity section, which is what makes the statement
unconditional, and unramifiedness of the ambient pre-relation is in the setting of Stacks 06N0
the DM hypothesis read through **Stacks 050H**, part (4). -/
theorem mono_prodLift_of_unramified [Subsingleton (openOver G.arrows W).left]
    [Unramified (prod.lift G.target G.source).left]
    (hid : ∀ y : G.objects.left, G.identity.left.base y ∈ W) :
    Mono (prod.lift (openArrowTarget W) (openArrowSource W)) := by
  have : Unramified (prod.lift (openArrowTarget W) (openArrowSource W)).left := by
    rw [show (prod.lift (openArrowTarget W) (openArrowSource W)).left =
        (openOverι G.arrows W).left ≫ (prod.lift G.target G.source).left from by
      rw [← Over.comp_left, prodLift_openArrowTarget_openArrowSource]]
    exact MorphismProperty.comp_mem (@Unramified) _ _ inferInstance inferInstance
  have hpair : Unramified (prod.lift (openArrowTarget W) (openArrowSource W)).left ∧
      UniversallyInjective (prod.lift (openArrowTarget W) (openArrowSource W)).left :=
    ⟨inferInstance, universallyInjective_prodLift W hid⟩
  have hmono : Unramified (prod.lift (openArrowTarget W) (openArrowSource W)).left ∧
      Mono (prod.lift (openArrowTarget W) (openArrowSource W)).left :=
    ((universallyInjective_unramified_tfae
      (prod.lift (openArrowTarget W) (openArrowSource W)).left).out 2 1).mp hpair
  have : Mono (prod.lift (openArrowTarget W) (openArrowSource W)).left := hmono.2
  exact Over.mono_of_mono_left _

/-! ### The piece through the identity -/

section Identity

variable (G) [IsLocallyArtinian G.arrows.left]

/-- **The open subscheme of the arrow scheme cut out by an identity arrow.**  For a groupoid
scheme whose arrow scheme is zero-dimensional, the single point `e(u)` of the arrow scheme is
open, every point of a locally Artinian scheme being isolated. -/
def identityArrowOpens (u : G.objects.left) : G.arrows.left.Opens :=
  ⟨{G.identity.left.base u}, isOpen_discrete _⟩

/-- The underlying set of the open cut out by the identity arrow at `u` is `{e(u)}`. -/
@[simp]
theorem coe_identityArrowOpens (u : G.objects.left) :
    (identityArrowOpens G u : Set G.arrows.left) = {G.identity.left.base u} := rfl

/-- The piece of the arrow scheme through an identity arrow is closed as well as open. -/
theorem isClopen_identityArrowOpens (u : G.objects.left) :
    IsClopen (identityArrowOpens G u : Set G.arrows.left) := isClopen_discrete _

/-- The open subscheme cut out by an identity arrow has at most one point. -/
instance subsingleton_openOver_identityArrowOpens (u : G.objects.left) :
    Subsingleton (openOver G.arrows (identityArrowOpens G u)).left :=
  ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩

/-- Every identity arrow lies in the piece through an identity arrow, the object scheme having
only one point. -/
theorem mem_identityArrowOpens [Subsingleton G.objects.left] (u : G.objects.left)
    (y : G.objects.left) : G.identity.left.base y ∈ identityArrowOpens G u :=
  congrArg G.identity.left.base (Subsingleton.elim y u)

/-- **The open and closed piece of the arrow scheme through the identity is a subgroupoid.**  For
a groupoid scheme whose object scheme has exactly one point and whose arrow scheme is
zero-dimensional, the identity arrow at a point of the object scheme cuts out an open and closed
subscheme of the arrow scheme which contains every identity arrow and is stable under the
inverse and under the composition of its own composable pairs. -/
theorem isArrowSubgroupoid_identityArrowOpens [Subsingleton G.objects.left]
    [Nonempty G.objects.left] (u : G.objects.left) :
    IsArrowSubgroupoid (identityArrowOpens G u) :=
  isArrowSubgroupoid_of_subsingleton _ (mem_identityArrowOpens G u)

/-- The source map restricted to the piece through the identity is finite. -/
theorem isFinite_openArrowSource_identityArrowOpens [IsLocallyArtinian G.objects.left]
    [LocallyOfFiniteType G.source.left] (u : G.objects.left) :
    IsFinite (openArrowSource (identityArrowOpens G u)).left :=
  isFinite_openArrowSource _

/-- The target map restricted to the piece through the identity is finite. -/
theorem isFinite_openArrowTarget_identityArrowOpens [IsLocallyArtinian G.objects.left]
    [LocallyOfFiniteType G.target.left] (u : G.objects.left) :
    IsFinite (openArrowTarget (identityArrowOpens G u)).left :=
  isFinite_openArrowTarget _

variable [Subsingleton G.objects.left] [Nonempty G.objects.left]
  [IsLocallyArtinian G.objects.left] [LocallyOfFiniteType G.source.left]
  [LocallyOfFiniteType G.target.left]

/-- **The open and closed piece of the arrow scheme through the identity, as an open finite
subgroupoid.**  This is conditions (a) and (b) of **Stacks 04RK** for the piece through the
identity. -/
def identityOpenFiniteSubgroupoid (u : G.objects.left) : OpenFiniteSubgroupoid G :=
  openFiniteSubgroupoidOfOpens (identityArrowOpens G u)
    (isArrowSubgroupoid_identityArrowOpens G u)
    (isFinite_openArrowSource_identityArrowOpens G u)
    (isFinite_openArrowTarget_identityArrowOpens G u)

/-- The arrows of the piece through the identity are exactly the identity arrow. -/
theorem range_identityOpenFiniteSubgroupoid_inclusion (u : G.objects.left) :
    Set.range (identityOpenFiniteSubgroupoid G u).inclusion.mapArrows.left.base =
      {G.identity.left.base u} := by
  change Set.range (openOverι G.arrows (identityArrowOpens G u)).left.base =
    {G.identity.left.base u}
  exact congrArg (fun V : G.arrows.left.Opens => (V : Set G.arrows.left))
    (opensRange_openOverι_left G.arrows (identityArrowOpens G u))

/-- **A groupoid scheme with a one-point object scheme and a zero-dimensional arrow scheme is
quasi-split at every point of its object scheme**, in the sense of part (3) of
**Stacks 04RK**. -/
@[stacks 04RK "part (3): a groupoid scheme with a one-point object scheme and a zero-dimensional \
arrow scheme is quasi-split at every point of its object scheme, the quasi-splitting being the \
open and closed piece of the arrow scheme through the identity"]
theorem isQuasiSplitAt_of_isLocallyArtinian_arrows (u : G.objects.left) : IsQuasiSplitAt G u :=
  ⟨(identityOpenFiniteSubgroupoid G u).toQuasiSplitting u⟩

end Identity

/-- **The open and closed piece of the arrow scheme through the identity, at an object scheme
which is the spectrum of a field.**  Both hypotheses on the object scheme are automatic there:
the spectrum of a field has exactly one point and is Artinian. -/
theorem exists_openFiniteSubgroupoid_singleton_identity_of_isoSpecField
    (G : GroupoidScheme S)
    [IsLocallyArtinian G.arrows.left] [LocallyOfFiniteType G.source.left]
    [LocallyOfFiniteType G.target.left] (k : Type u) [Field k]
    (iso : G.objects.left ≅ Spec (.of k)) (u : G.objects.left) :
    ∃ P : OpenFiniteSubgroupoid G,
      Set.range P.inclusion.mapArrows.left.base = {G.identity.left.base u} := by
  have : Subsingleton G.objects.left :=
    ⟨fun a b => iso.hom.homeomorph.injective (Subsingleton.elim _ _)⟩
  have : Nonempty G.objects.left := ⟨u⟩
  have : IsLocallyArtinian G.objects.left := IsLocallyArtinian.of_isImmersion iso.hom
  exact ⟨identityOpenFiniteSubgroupoid G u, range_identityOpenFiniteSubgroupoid_inclusion G u⟩

end Stacks.Groupoids.GroupoidScheme

end

end
