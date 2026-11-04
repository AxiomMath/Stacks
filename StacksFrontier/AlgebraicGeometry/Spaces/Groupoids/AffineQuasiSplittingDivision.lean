module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.RestrictionAffineQuotient
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.SubgroupoidDivision
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasiSplittingAffineLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureQuasiSplitting

/-!
# Quasi-splitting and division of an affine groupoid scheme at a point

`Stacks.Groupoids.GroupoidScheme.exists_isAffine_isQuasiSplitAt_of_quasiSplittingSituation` is
**Stacks 04S0**: in the quasi-splitting situation of Stacks 04RV, with `U` affine and with `s`
and `t` flat and locally of finite presentation, the chosen point has an affine étale
neighbourhood over which the restricted groupoid scheme is quasi-split.  It is unconditional,
but it is stated for an `AlgebraicGeometry.Space.QuasiSplittingSituation`, and nothing produced
one: Situation 04RV is a list of hypotheses, so a consumer that has a groupoid scheme and a
point rather than a bundled situation could not reach the tag.

This file supplies the situation and then runs the consequences of Stacks 04S0 as far as this
library's other pieces reach.

The situation is produced from hypotheses that are about the groupoid scheme alone: an affine
object scheme, a monomorphic relation map `j = (t, s) : R ⟶ U ×_S U`, source and target locally
of finite presentation, and a locally quasi-finite source.  Separatedness of `s` and `t`, which
Situation 04RV asks for, is *derived* from the first two — an affine scheme is separated, so
`U ⟶ S` is separated, so each projection `U ×_S U ⟶ U` is separated, so `U ×_S U` is a separated
scheme; a monomorphism into it makes `R` a separated scheme, and every morphism out of a
separated scheme is separated.  Quasi-finiteness of `s` at the identity arrow is read off from
local finite presentation and local quasi-finiteness through
`AlgebraicGeometry.forall_quasiFiniteAt_iff`.

Three consequences are then recorded, each an unconditional theorem about such a groupoid
scheme and a point of its object scheme.  The first is Stacks 04S0 itself with the situation
discharged.  The second composes it with **Stacks 0DU3**, clause (3)
(`Stacks.Groupoids.GroupoidScheme.exists_quasiSplitting_isAffine_isFinite_flat`): the
quasi-splitting obtained on the affine étale neighbourhood is, as a groupoid scheme in its own
right, one with both structure schemes affine and with source and target finite, flat and
locally of finite presentation.  The third composes that with the first three conclusions of
**Stacks 04S4**
(`AlgebraicGeometry.affineFiniteFlatQuotient`, as in
`AlgebraicGeometry.exists_finiteFlatQuotient_isAffine_of_mono_groupoidPreRelation`): such a
groupoid scheme can be divided out, giving an affine quotient `Ū` of the neighbourhood, a
finite locally free surjection onto it, and the quasi-splitting as the kernel pair.

## Main definitions

* `AlgebraicGeometry.Space.quasiSplittingSituation`: the quasi-splitting situation of
  Stacks 04RV attached to a groupoid scheme with affine object scheme, monomorphic relation
  map, source and target locally of finite presentation and locally quasi-finite source, at a
  point of its object scheme.

## Main results

* `Stacks.Groupoids.GroupoidScheme.isSeparated_arrows_of_isAffine_objects`: the arrow scheme of
  a groupoid scheme with affine object scheme and monomorphic relation map is a separated
  scheme.
* `Stacks.Groupoids.GroupoidScheme.exists_isAffine_isQuasiSplitAt_of_isAffine_objects`:
  Stacks 04S0 for such a groupoid scheme, with no situation supplied.
* `Stacks.Groupoids.GroupoidScheme.exists_isAffine_isFinite_flat_subgroupoid_of_isAffine_objects`:
  the same, with the quasi-splitting delivered as a groupoid scheme with affine structure
  schemes and finite, flat, locally finitely presented source and target.
* `Stacks.Groupoids.GroupoidScheme.exists_isAffine_finiteFlatQuotient_of_isAffine_objects`: the
  same, with the division of that groupoid scheme by Stacks 04S4.

## Implementation notes

None of the four theorems is tagged.  Each is an implication between statements the library
already has: the hypotheses are not those of any one tag, and the conclusions chain two or
three tags together.  Stacks 04S0 itself is tagged where it is proved, on
`Stacks.Groupoids.GroupoidScheme.exists_isAffine_isQuasiSplitAt_of_quasiSplittingSituation`.

The five containment hypotheses `hS`, `hU`, `hR`, `hP` and `hK` — that the big fppf site
contains the base scheme, the object scheme, the arrow scheme, the scheme of composable pairs
and the spectrum of the residue field at the point — are carried, exactly as Stacks 04S0 and the
rest of the étale-localization chain carry them.  They are this library's standing ambient
requirement and are not a conditionality of the mathematics.

The quasi-splitting is produced for *every* groupoid scheme realizing the restriction to the
neighbourhood, which is how Stacks 04S0 states it and what
`AlgebraicGeometry.GroupoidScheme.Restriction.hom_ext` makes possible; the three theorems below
keep that form.

The fourth conclusion of Stacks 04S4 — that the ambient groupoid `R` is the restriction of a
groupoid scheme on `Ū` — is **not** reached, and
`StacksFrontier/AlgebraicGeometry/Groupoids/FiniteFlatQuotient/SubgroupoidDivision.lean` records
why: it needs effective descent along the finite locally free `U ⟶ Ū` for separated locally
quasi-finite schemes at the level of `AlgebraicGeometry.DescentDatum`, and the library has
Stacks 02W8 only for morphisms of sheaves.  That is the single remaining obstruction on this
branch of the proof of Stacks 04S6.

The two categorical lemmas about binary products in a slice category are `private`: the
statement that the two projections of `X ⨯ Y` in `Over B` underlie a pullback square in the
ambient category is not recorded anywhere in this library and is needed only here.

## References

* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 04S0](https://stacks.math.columbia.edu/tag/04S0)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 0DU3](https://stacks.math.columbia.edu/tag/0DU3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

/-- Two morphisms into the underlying object of a binary product of a slice category agree as
soon as they agree after both projections.  The lift they are compared through is formed in the
slice category over the structure morphism of the first of them. -/
private theorem over_prod_left_hom_ext {C : Type*} [Category C] {B : C}
    [HasBinaryProducts (Over B)] {X Y : Over B} {Z : C}
    {a b : Z ⟶ (X ⨯ Y : Over B).left}
    (h₁ : a ≫ (prod.fst : (X ⨯ Y : Over B) ⟶ X).left =
      b ≫ (prod.fst : (X ⨯ Y : Over B) ⟶ X).left)
    (h₂ : a ≫ (prod.snd : (X ⨯ Y : Over B) ⟶ Y).left =
      b ≫ (prod.snd : (X ⨯ Y : Over B) ⟶ Y).left) : a = b := by
  have hw : b ≫ (X ⨯ Y : Over B).hom = a ≫ (X ⨯ Y : Over B).hom := by
    rw [← Over.w (prod.fst : (X ⨯ Y : Over B) ⟶ X), reassoc_of% h₁]
  have h : (Over.homMk a : Over.mk (a ≫ (X ⨯ Y : Over B).hom) ⟶ (X ⨯ Y : Over B)) =
      Over.homMk b hw :=
    prod.hom_ext (Over.OverMorphism.ext h₁) (Over.OverMorphism.ext h₂)
  exact congrArg Over.Hom.left h

/-- The two projections of a binary product in a slice category underlie a pullback square in
the ambient category: `X ⨯ Y` in `Over B` is the fibre product of `X` and `Y` over `B`. -/
private theorem isPullback_over_prod {C : Type*} [Category C] {B : C}
    [HasBinaryProducts (Over B)] (X Y : Over B) :
    IsPullback (prod.fst : (X ⨯ Y : Over B) ⟶ X).left
      (prod.snd : (X ⨯ Y : Over B) ⟶ Y).left X.hom Y.hom := by
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [Over.w, Over.w]
  · intro T a b h₁ h₂
    exact over_prod_left_hom_ext h₁ h₂
  · intro T a b h
    exact ⟨(prod.lift (Over.homMk a : Over.mk (a ≫ X.hom) ⟶ X)
      (Over.homMk b h.symm : Over.mk (a ≫ X.hom) ⟶ Y)).left,
      congrArg Over.Hom.left (prod.lift_fst _ _), congrArg Over.Hom.left (prod.lift_snd _ _)⟩

namespace Stacks.Groupoids.GroupoidScheme

/-- **The arrow scheme of a groupoid scheme with affine object scheme and monomorphic relation
map is a separated scheme.**

An affine scheme is separated, so the structure morphism `U ⟶ S` is separated; the second
projection `U ×_S U ⟶ U` is its base change along itself, hence separated, so `U ×_S U` is a
separated scheme; and `j = (t, s) : R ⟶ U ×_S U` is a monomorphism, hence separated, so `R` is a
separated scheme too.

This is what supplies the separatedness hypotheses of Situation 04RV to
`AlgebraicGeometry.Space.quasiSplittingSituation`: every morphism out of a separated scheme is
separated, so `s` and `t` are. -/
theorem isSeparated_arrows_of_isAffine_objects {S : Scheme.{u}} {G : GroupoidScheme S}
    [IsAffine G.objects.left] [Mono (AlgebraicGeometry.groupoidPreRelation G)] :
    Scheme.IsSeparated G.arrows.left := by
  have hsnd : IsSeparated
      (prod.snd : (G.objects ⨯ G.objects : Over S) ⟶ G.objects).left :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (isPullback_over_prod G.objects G.objects) inferInstance
  have hprod : Scheme.IsSeparated (G.objects ⨯ G.objects : Over S).left := by
    constructor
    rw [show terminal.from ((G.objects ⨯ G.objects : Over S).left) =
      (prod.snd : (G.objects ⨯ G.objects : Over S) ⟶ G.objects).left ≫
        terminal.from G.objects.left from terminal.hom_ext _ _]
    infer_instance
  constructor
  rw [show terminal.from G.arrows.left = (AlgebraicGeometry.groupoidPreRelation G).left ≫
    terminal.from ((G.objects ⨯ G.objects : Over S).left) from terminal.hom_ext _ _]
  infer_instance

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry.Space

/-- **The quasi-splitting situation of Stacks 04RV attached to an affine groupoid scheme.**

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `U` affine, with
`j = (t, s) : R ⟶ U ×_S U` a monomorphism, with `s` and `t` locally of finite presentation and
with `s` locally quasi-finite, and let `u` be a point of `U`.  Then the standing hypotheses of
Situation 04RV hold: `s` and `t` are separated by
`Stacks.Groupoids.GroupoidScheme.isSeparated_arrows_of_isAffine_objects`, they are locally of
finite type because they are locally of finite presentation, and `s` is quasi-finite at the
identity arrow `e(u)` because it is locally of finite type and locally quasi-finite everywhere,
by `AlgebraicGeometry.forall_quasiFiniteAt_iff`.

The hypotheses on `U` and on `j` are the ones a groupoid `R = X ×_F X` arising from a chart of
a sheaf comes with — `j` is a monomorphism exactly when `(t, s)` is an equivalence relation,
by `AlgebraicGeometry.isEquivalenceRelation_of_mono_groupoidPreRelation` — so this is the form
in which the étale-localization chain is applied downstream. -/
def quasiSplittingSituation {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [Mono (AlgebraicGeometry.groupoidPreRelation G)]
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left]
    [LocallyQuasiFinite G.source.left] (u : G.objects.left) :
    QuasiSplittingSituation.{u} :=
  have := Stacks.Groupoids.GroupoidScheme.isSeparated_arrows_of_isAffine_objects (G := G)
  { S := S
    groupoid := G
    u := u
    sourceSeparated := inferInstance
    targetSeparated := inferInstance
    sourceQuasiFiniteAtIdentity :=
      (forall_quasiFiniteAt_iff G.source.left).mpr ⟨inferInstance, inferInstance⟩
        (G.identity.left.base u) }

/-- The base scheme of `quasiSplittingSituation G u` is `S`. -/
@[simp]
theorem quasiSplittingSituation_S {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [Mono (AlgebraicGeometry.groupoidPreRelation G)]
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left]
    [LocallyQuasiFinite G.source.left] (u : G.objects.left) :
    (quasiSplittingSituation G u).S = S := rfl

/-- The groupoid scheme of `quasiSplittingSituation G u` is `G`. -/
@[simp]
theorem quasiSplittingSituation_groupoid {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [Mono (AlgebraicGeometry.groupoidPreRelation G)]
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left]
    [LocallyQuasiFinite G.source.left] (u : G.objects.left) :
    (quasiSplittingSituation G u).groupoid = G := rfl

/-- The point of `quasiSplittingSituation G u` is `u`. -/
@[simp]
theorem quasiSplittingSituation_u {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [Mono (AlgebraicGeometry.groupoidPreRelation G)]
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left]
    [LocallyQuasiFinite G.source.left] (u : G.objects.left) :
    (quasiSplittingSituation G u).u = u := rfl

end AlgebraicGeometry.Space

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

/-- **Stacks 04S0 for an affine groupoid scheme**, with the quasi-splitting situation of
Stacks 04RV discharged rather than assumed.

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `U` affine, with
`j = (t, s) : R ⟶ U ×_S U` a monomorphism, with `s` and `t` flat and locally of finite
presentation and with `s` locally quasi-finite, and let `u` be a point of `U`.  Then there are a
separated étale neighbourhood `U' ⟶ U`, a groupoid scheme `R'` realizing `R|_{U'}`, an affine
open `U'' ⊆ U'` and a point `u''` of `U''` over `u` with `κ(u) = κ(u'')` such that `U'' ⟶ U` is
étale and `R|_{U''}` is quasi-split over `u''`, in both readings of `R|_{U''}`.

This is
`Stacks.Groupoids.GroupoidScheme.exists_isAffine_isQuasiSplitAt_of_quasiSplittingSituation`
applied to `AlgebraicGeometry.Space.quasiSplittingSituation`; the only work is supplying the
situation, and the conclusion is verbatim that of the tag. -/
theorem exists_isAffine_isQuasiSplitAt_of_isAffine_objects {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.objects.left)
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains S)
    (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left)
    (hK : C.Contains (Spec (G.objects.left.residueField u)))
    [IsAffine G.objects.left] [Mono (AlgebraicGeometry.groupoidPreRelation G)]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    [LocallyQuasiFinite G.source.left] :
    ∃ (U' : Over S) (gp : U' ⟶ G.objects)
      (R' : AlgebraicGeometry.GroupoidScheme.Restriction G gp)
      (U'' : Over S) (j : U'' ⟶ R'.groupoid.objects) (u'' : U''.left),
      AlgebraicGeometry.IsSeparated gp.left ∧ Etale gp.left ∧
      IsAffine U''.left ∧ IsOpenImmersion j.left ∧
      Etale (j ≫ R'.hom.mapObjects).left ∧
      (j ≫ R'.hom.mapObjects).left.base u'' = u ∧
      IsIso ((j ≫ R'.hom.mapObjects).left.residueFieldMap u'') ∧
      (∀ R'' : AlgebraicGeometry.GroupoidScheme.Restriction R'.groupoid j,
        IsQuasiSplitAt R''.groupoid ((eqToHom R''.objects_eq.symm).left.base u'')) ∧
      ∀ R''' : AlgebraicGeometry.GroupoidScheme.Restriction G (j ≫ R'.hom.mapObjects),
        IsQuasiSplitAt R'''.groupoid ((eqToHom R'''.objects_eq.symm).left.base u'') := by
  have : IsAffine (quasiSplittingSituation G u).groupoid.objects.left :=
    inferInstanceAs (IsAffine G.objects.left)
  have : Flat (quasiSplittingSituation G u).groupoid.source.left :=
    inferInstanceAs (Flat G.source.left)
  have : LocallyOfFinitePresentation (quasiSplittingSituation G u).groupoid.source.left :=
    inferInstanceAs (LocallyOfFinitePresentation G.source.left)
  have : Flat (quasiSplittingSituation G u).groupoid.target.left :=
    inferInstanceAs (Flat G.target.left)
  have : LocallyOfFinitePresentation (quasiSplittingSituation G u).groupoid.target.left :=
    inferInstanceAs (LocallyOfFinitePresentation G.target.left)
  exact exists_isAffine_isQuasiSplitAt_of_quasiSplittingSituation
    (quasiSplittingSituation G u) C hS hU hR hP hK

/-- The source and target maps of a groupoid scheme realizing a restriction have every property of
morphisms of schemes which is stable under base change and composition and holds for the source
map of the groupoid and for the restricting morphism: by Stacks 04MV, the source map of the
restriction is a base change of the restricting morphism followed by the source map. -/
private theorem restriction_source_target_property {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (R : AlgebraicGeometry.GroupoidScheme.Restriction G g)
    (hs : P G.source.left) (hg : P g.left) :
    P R.groupoid.source.left ∧ P R.groupoid.target.left :=
  have h := AlgebraicGeometry.overFibreProduct_comp (pullback.snd g G.target) G.source
    (AlgebraicGeometry.overFibreProduct_snd g G.target hg) hs
  ⟨AlgebraicGeometry.restriction_source_mem G g R P h,
    AlgebraicGeometry.restriction_target_mem G g R P h⟩

/-- **The quasi-splitting of Stacks 04S0 delivered as a groupoid scheme of the shape clause (3)
of Stacks 0DU3 demands.**

Under the hypotheses of
`Stacks.Groupoids.GroupoidScheme.exists_isAffine_isQuasiSplitAt_of_isAffine_objects` there are an
affine scheme `U''`, an étale morphism `g : U'' ⟶ U` and a point `u''` of `U''` over `u` with
`κ(u) = κ(u'')` such that every groupoid scheme `R''` realizing `R|_{U''}` contains a groupoid
scheme `P` on the same object scheme, by an open immersion on arrow schemes through the identity
arrow at `u''`, whose two structure schemes are affine and whose source and target are finite,
flat and locally of finite presentation.

The affine étale neighbourhood is the one Stacks 04S0 produces, read along the composite
`U'' ⟶ U' ⟶ U`, and `P` is the quasi-splitting, whose properties are those
`Stacks.Groupoids.GroupoidScheme.exists_quasiSplitting_isAffine_isFinite_flat` derives from it.
The flatness and local finite presentation of the source and target of `R''`, which that
theorem needs, come from Stacks 04MV: they are base changes of the étale `g` followed by `s`. -/
theorem exists_isAffine_isFinite_flat_subgroupoid_of_isAffine_objects {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.objects.left)
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains S)
    (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left)
    (hK : C.Contains (Spec (G.objects.left.residueField u)))
    [IsAffine G.objects.left] [Mono (AlgebraicGeometry.groupoidPreRelation G)]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    [LocallyQuasiFinite G.source.left] :
    ∃ (U'' : Over S) (g : U'' ⟶ G.objects) (u'' : U''.left),
      IsAffine U''.left ∧ Etale g.left ∧ g.left.base u'' = u ∧
      IsIso (g.left.residueFieldMap u'') ∧
      ∀ R : AlgebraicGeometry.GroupoidScheme.Restriction G g,
        ∃ (H : GroupoidScheme S) (φ : Hom H R.groupoid),
          H.objects = R.groupoid.objects ∧
          IsOpenImmersion φ.mapArrows.left ∧
          (∃ p : H.arrows.left, φ.mapArrows.left.base p =
            R.groupoid.identity.left.base ((eqToHom R.objects_eq.symm).left.base u'')) ∧
          IsAffine H.objects.left ∧ IsAffine H.arrows.left ∧
          IsFinite H.source.left ∧ Flat H.source.left ∧
          LocallyOfFinitePresentation H.source.left ∧
          IsFinite H.target.left ∧ Flat H.target.left ∧
          LocallyOfFinitePresentation H.target.left := by
  obtain ⟨U', gp, R', U'', j, u'', -, -, haff, -, het, hbase, hres, -, hqs⟩ :=
    exists_isAffine_isQuasiSplitAt_of_isAffine_objects G u C hS hU hR hP hK
  refine ⟨U'', j ≫ R'.hom.mapObjects, u'', haff, het, hbase, hres, fun R => ?_⟩
  have : IsAffine R.groupoid.objects.left := by rwa [R.objects_eq]
  obtain ⟨_, _⟩ := restriction_source_target_property (P := @Flat) G _ R inferInstance inferInstance
  obtain ⟨_, _⟩ := restriction_source_target_property (P := @LocallyOfFinitePresentation) G _ R
    inferInstance inferInstance
  exact exists_quasiSplitting_isAffine_isFinite_flat (hqs R)

/-- If the arrow map of a morphism of groupoid schemes is a monomorphism and the relation map of
the target groupoid is a monomorphism, then so is the relation map of the source groupoid: the
inclusion carries the one relation map into the other, up to the product of the maps of object
schemes. -/
private theorem mono_groupoidPreRelation_of_mono_mapArrows {S : Scheme.{u}}
    {G H : GroupoidScheme S} (φ : Hom H G) [Mono φ.mapArrows]
    [Mono (AlgebraicGeometry.groupoidPreRelation G)] :
    Mono (AlgebraicGeometry.groupoidPreRelation H) := by
  have key : φ.mapArrows ≫ AlgebraicGeometry.groupoidPreRelation G =
      AlgebraicGeometry.groupoidPreRelation H ≫ prod.map φ.mapObjects φ.mapObjects := by
    simp only [AlgebraicGeometry.groupoidPreRelation, prod.comp_lift, φ.map_target, φ.map_source,
      prod.lift_map]
  refine ⟨fun a b hab => ?_⟩
  apply (cancel_mono φ.mapArrows).mp
  apply (cancel_mono (AlgebraicGeometry.groupoidPreRelation G)).mp
  simp only [Category.assoc, key, reassoc_of% hab]

/-- **The quasi-splitting of Stacks 04S0 divided out, by the first three conclusions of
Stacks 04S4.**

Under the hypotheses of
`Stacks.Groupoids.GroupoidScheme.exists_isAffine_isQuasiSplitAt_of_isAffine_objects` there are an
affine scheme `U''`, an étale morphism `g : U'' ⟶ U` and a point `u''` of `U''` over `u` with
`κ(u) = κ(u'')` such that every groupoid scheme `R''` realizing `R|_{U''}` contains a groupoid
scheme `P` on the same object scheme, by an open immersion on arrow schemes through the identity
arrow at `u''`, whose two structure schemes are affine, whose source and target are finite
locally free, and which can be divided out: `U''/P` is representable by an affine scheme `Ū`,
the quotient morphism `U'' ⟶ Ū` is finite locally free and surjective, and `P = U'' ×_Ū U''`.

Finite locally freeness of `s|_P` and `t|_P` is finiteness, flatness and local finite
presentation together, by
`Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation`; the
monomorphism condition of Stacks 04S4 on the relation map of `P` comes from the one on the
relation map of `R` — it passes to the restriction `R''` by
`AlgebraicGeometry.GroupoidScheme.mono_groupoidPreRelation_restriction` and from there to `P`
along the open immersion of arrow schemes.

The fourth conclusion of Stacks 04S4, that `R''` is the restriction of a groupoid scheme on `Ū`,
is not asserted; see the implementation notes. -/
theorem exists_isAffine_finiteFlatQuotient_of_isAffine_objects {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.objects.left)
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains S)
    (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left)
    (hK : C.Contains (Spec (G.objects.left.residueField u)))
    [IsAffine G.objects.left] [Mono (AlgebraicGeometry.groupoidPreRelation G)]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    [LocallyQuasiFinite G.source.left] :
    ∃ (U'' : Over S) (g : U'' ⟶ G.objects) (u'' : U''.left),
      IsAffine U''.left ∧ Etale g.left ∧ g.left.base u'' = u ∧
      IsIso (g.left.residueFieldMap u'') ∧
      ∀ R : AlgebraicGeometry.GroupoidScheme.Restriction G g,
        ∃ (H : GroupoidScheme S) (φ : Hom H R.groupoid),
          H.objects = R.groupoid.objects ∧
          IsOpenImmersion φ.mapArrows.left ∧
          (∃ p : H.arrows.left, φ.mapArrows.left.base p =
            R.groupoid.identity.left.base ((eqToHom R.objects_eq.symm).left.base u'')) ∧
          IsAffine H.objects.left ∧ IsAffine H.arrows.left ∧
          Stacks.Morphisms.IsFiniteLocallyFree H.source.left ∧
          Stacks.Morphisms.IsFiniteLocallyFree H.target.left ∧
          ∃ Q : FiniteFlatQuotient H, IsAffine Q.space.left := by
  obtain ⟨U'', g, u'', haff, het, hbase, hres, hsub⟩ :=
    exists_isAffine_isFinite_flat_subgroupoid_of_isAffine_objects G u C hS hU hR hP hK
  refine ⟨U'', g, u'', haff, het, hbase, hres, fun R => ?_⟩
  obtain ⟨H, φ, hobj, hoi, hid, hHoaff, hHaaff, hsfin, hsflat, hslfp, htfin, htflat, htlfp⟩ :=
    hsub R
  have : Stacks.Morphisms.IsFiniteLocallyFree H.source.left :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
      ⟨hsfin, hsflat, hslfp⟩
  have : Stacks.Morphisms.IsFiniteLocallyFree H.target.left :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
      ⟨htfin, htflat, htlfp⟩
  have : IsEquivalenceRelation G.target G.source :=
    AlgebraicGeometry.isEquivalenceRelation_of_mono_groupoidPreRelation G
  have : Mono (AlgebraicGeometry.groupoidPreRelation R.groupoid) :=
    AlgebraicGeometry.GroupoidScheme.mono_groupoidPreRelation_restriction G g R
  have : Mono φ.mapArrows := Over.mono_of_mono_left φ.mapArrows
  have : Mono (AlgebraicGeometry.groupoidPreRelation H) :=
    mono_groupoidPreRelation_of_mono_mapArrows φ
  have : IsEquivalenceRelation H.target H.source :=
    AlgebraicGeometry.isEquivalenceRelation_of_mono_groupoidPreRelation H
  have hq : IsAffine (AlgebraicGeometry.quotientOver H).left := by
    rw [AlgebraicGeometry.quotientOver_left]
    infer_instance
  exact ⟨H, φ, hobj, hoi, hid, hHoaff, hHaaff, inferInstance, inferInstance,
    AlgebraicGeometry.affineFiniteFlatQuotient H, hq⟩

end Stacks.Groupoids.GroupoidScheme

end
