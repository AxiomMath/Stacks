module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresOpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFinite

/-!
# The affine criterion for finite and integral morphisms of algebraic spaces

`AlgebraicGeometry.Space.IsFinite` and `AlgebraicGeometry.Space.IsIntegralHom` test a morphism
of algebraic spaces over `S` on the objects of the big fppf site with *affine* underlying
scheme. A relatively representable morphism whose represented base changes are finite,
respectively integral, is tested on *every* object of the site: it satisfies
`CategoryTheory.MorphismProperty.presheaf` for the inverse image along
`AlgebraicGeometry.BigFppfOver.toScheme` of Mathlib's `AlgebraicGeometry.IsFinite`, respectively
`AlgebraicGeometry.IsIntegralHom`. This file identifies the two conditions, for a morphism which
is already known to be relatively representable.

## Main definitions

* `AlgebraicGeometry.Space.openObjHom` is the morphism of the big fppf site over `S` carried by
  an open subscheme of the scheme underlying an object of the site.  The object itself is
  `AlgebraicGeometry.Space.openObj` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresOpenCover`.

## Main results

* `AlgebraicGeometry.Space.property_snd_of_affineOpens`: for a property of morphisms of schemes
  which is Zariski-local at the target, the canonical represented base change of a relatively
  representable morphism along *one* test has the property as soon as its base changes along
  the restrictions of that test to the affine opens of the test object do.
* `AlgebraicGeometry.Space.presheaf_inverseImage_of_isAffine_test`: for a property of morphisms
  of schemes which is Zariski-local at the target, a relatively representable morphism of
  presheaves whose represented base changes along maps from *affine* objects of the site have
  the property has it after base change along a map from *any* object of the site.  This is the
  previous item applied at every test.
* `AlgebraicGeometry.Space.isAffine_test_of_presheaf_inverseImage` is the converse for a
  property contained in `AlgebraicGeometry.IsAffineHom`, which also supplies the affineness of
  the representing object demanded by the two predicates.
* `AlgebraicGeometry.Space.isFinite_of_presheaf_isFinite` and
  `AlgebraicGeometry.Space.isIntegralHom_of_presheaf_isIntegralHom`: a relatively representable
  morphism with finite, respectively integral, represented base changes is finite, respectively
  integral, as a morphism of algebraic spaces. These need no hypothesis.
* `AlgebraicGeometry.Space.presheaf_isFinite_of_isFinite` and
  `AlgebraicGeometry.Space.presheaf_isIntegralHom_of_isIntegralHom` are the converses for a
  morphism assumed relatively representable.
* `AlgebraicGeometry.Space.isFinite_iff_representable_of_relativelyRepresentable` and
  `AlgebraicGeometry.Space.isIntegralHom_iff_representable_of_relativelyRepresentable` are the
  two equivalences, for a morphism assumed relatively representable.  The unqualified
  `AlgebraicGeometry.Space.isFinite_iff_representable` and
  `AlgebraicGeometry.Space.isIntegralHom_iff_representable` of
  `StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae` are the same equivalences from the
  hypothesis that the source and the target are algebraic spaces instead, which is a hypothesis
  on different data and implies neither way.
* `AlgebraicGeometry.Space.isFinite_iff_representable_iff` and
  `AlgebraicGeometry.Space.isIntegralHom_iff_representable_iff` locate exactly what the
  hypothesis costs: each equivalence, stated with no hypothesis at all, is *equivalent* to the
  single implication that a finite, respectively integral, morphism of algebraic spaces is
  relatively representable.

## Implementation notes

Nothing here carries an unqualified `@[stacks 03ZQ]`. The tag's conditions (1) and (2) are
exactly the two sides of
`AlgebraicGeometry.Space.isFinite_iff_representable_of_relativelyRepresentable`, and that
equivalence is proved here only for a morphism already known to be relatively representable.
The residue is named and isolated rather than assumed: by
`AlgebraicGeometry.Space.isFinite_iff_representable_iff` the hypothesis-free equivalence is
*equivalent* to `AlgebraicGeometry.Space.IsFinite B S hS f → yoneda.relativelyRepresentable f`,
so the hypothesis is implied by the right-hand side of the very equivalence it is used to prove
and the whole of the remaining content is that one implication. Its proof needs a glueing
theorem which is not available: the base change of `f` along a map from a *general* object `U`
of the site is covered by the affine pieces obtained from the affine opens of `U`, and
`AlgebraicGeometry.Space.isRepresentable_of_openCover` glues such a family only when its index
type is smaller than `B.cutoff.ord.cof`, whereas the affine opens of `U` are bounded only by
`U.size`, hence by `B.cutoff`. The glued scheme *is* an object of the site here — it is finite
over `U`, so `AlgebraicGeometry.Scheme.size_lt_of_openCover` bounds its size by `U.size ^ ℵ₀`
and the cutoff is a strong prelimit — but that bound cannot be fed to the existing glueing
theorem, whose hypothesis is on the index type. No counterexample is possible, since the
implication is true; what is excluded is a glueing step of a different shape.

The locality argument is run on a bare morphism property of schemes, not on the two predicates
separately, and the affine test is passed in as a hypothesis rather than as the predicate
itself: this is what makes one proof serve both the finite and the integral case, whose
existential statements list their three conjuncts in different orders.

Only `CategoryTheory.MorphismProperty.relative_of_snd` is used to produce the relativized
property, so only the canonical represented base change is examined; the variance in the
pullback square is handled once, by `CategoryTheory.MorphismProperty.RespectsIso`, inside that
lemma. For the canonical square, the comparison with the affine datum is a single application
of `CategoryTheory.IsPullback.of_right'`, and the resulting square of presheaves is transported
to the site by `CategoryTheory.IsPullback.of_map`: `CategoryTheory.yoneda` is fully faithful,
hence reflects the fibre product, so no pointwise description of a presheaf pullback is needed.
The square is then pushed to schemes along `AlgebraicGeometry.BigFppfOver.toScheme`, which
preserves fibre products, and compared with
`AlgebraicGeometry.isPullback_morphismRestrict` through
`CategoryTheory.IsPullback.isoIsPullback`.

`AlgebraicGeometry.Space.isZariskiLocalAtTarget_isIntegralHom`, of
`StacksFrontier/AlgebraicGeometry/Spaces/IntegralFinite.lean`, and
`AlgebraicGeometry.Space.isZariskiLocalAtTarget_locallyOfFiniteType`, named here, name instances
which Mathlib already has but which instance search does not find: Mathlib declares the
underlying `AlgebraicGeometry.HasAffineProperty` and
`AlgebraicGeometry.HasRingHomProperty` instances under
`set_option backward.isDefEq.respectTransparency.types false`, and every use site inside Mathlib
repeats that option, so without it even `HasAffineProperty @AlgebraicGeometry.IsFinite _` is
unsolvable. Naming the two instances keeps the option out of this file.

For the same reason the finite case does not instantiate the locality argument at
`AlgebraicGeometry.IsFinite`: Mathlib's `HasAffineProperty` instance for it is anonymous, and
its generated name is longer than a source line may be. The argument is instead run twice, at
`AlgebraicGeometry.IsIntegralHom` and at `AlgebraicGeometry.LocallyOfFiniteType`, and the two
conclusions are recombined by
`AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`. That the relativized
property splits along that decomposition needs no lemma: the two conjuncts of
`CategoryTheory.MorphismProperty.relative` are a representability clause, shared, and a clause
quantified over pullback squares, which is checked square by square.

## References

* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Open subobjects of the site -/

/-- The morphism of the big fppf site over `S` underlying the inclusion of an open subscheme of
an object of the site.  This is `AlgebraicGeometry.Space.openIncl`, named as the morphism
carried by `AlgebraicGeometry.Space.openObj`. -/
noncomputable def openObjHom (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : openObj B S hS U V ⟶ U :=
  openIncl B S hS U V

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.openObjHom` is the inclusion of
the open subscheme. -/
theorem toScheme_map_openObjHom (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (BigFppfOver.toScheme B S hS).map (openObjHom B S hS U V) = V.ι :=
  toScheme_map_openIncl B S hS U V

/-! ### One instance of Mathlib's, named -/

/-- Being locally of finite type is Zariski-local at the target. This is Mathlib's instance,
named because instance search does not find it without
`set_option backward.isDefEq.respectTransparency.types false`. -/
theorem isZariskiLocalAtTarget_locallyOfFiniteType :
    IsZariskiLocalAtTarget
      (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    (@HasRingHomProperty.HasAffineProperty _ _
      instHasRingHomPropertyLocallyOfFiniteTypeFiniteType)

/-! ### The affine criterion -/

section Criterion

variable {B S hS}

/-- **One test descends to the affine opens of the test object.** Let `P` be a property of
morphisms of schemes which is Zariski-local at the target, and let `f` be relatively
representable. If the base change of `f` along the restriction of a single test
`g : yoneda.obj a ⟶ Y` to each affine open of the scheme underlying `a` is represented by a
morphism with `P`, then the canonical represented base change of `f` along `g` itself has `P`.

Only the target of the represented base change is cut up, so no hypothesis on `a` is needed:
the affine opens of its scheme cover it, and `P` is Zariski-local at the target. -/
theorem property_snd_of_affineOpens
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable f) {a : BigFppfOver B S hS}
    (g : yoneda.obj a ⟶ Y)
    (haff : ∀ V : ((BigFppfOver.toScheme B S hS).obj a).affineOpens,
      ∃ (W : BigFppfOver B S hS) (p : W ⟶ openObj B S hS a V.1) (i : yoneda.obj W ⟶ X),
        P ((BigFppfOver.toScheme B S hS).map p) ∧
          IsPullback i (yoneda.map p) f (yoneda.map (openObjHom B S hS a V.1) ≫ g)) :
    P ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun V : ((BigFppfOver.toScheme B S hS).obj a).affineOpens => V.1)
    (iSup_affineOpens_eq_top _) fun V => ?_
  obtain ⟨W, p, i, hP, hpb⟩ := haff V
  have hsq := hrep.isPullback g
  -- the affine datum over `V` is the base change of the canonical square along `V`
  obtain ⟨m, hm⟩ : ∃ m, yoneda.map m =
      hsq.lift i (yoneda.map p ≫ yoneda.map (openObjHom B S hS a V.1)) (by simp [hpb.w]) :=
    ⟨_, yoneda.map_preimage _⟩
  have key : IsPullback (yoneda.map m) (yoneda.map p) (yoneda.map (hrep.snd g))
      (yoneda.map (openObjHom B S hS a V.1)) := by
    rw [hm]
    exact hpb.of_right' hsq
  have hw : m ≫ hrep.snd g = p ≫ openObjHom B S hS a V.1 :=
    yoneda.map_injective (by simp [hm])
  -- `yoneda` reflects it, `toScheme` preserves it, and `V` is where it lands
  have hsch := (IsPullback.of_map yoneda hw key).map (BigFppfOver.toScheme B S hS)
  rw [toScheme_map_openObjHom] at hsch
  have hres := isPullback_morphismRestrict
    ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) V.1
  refine (P.arrow_mk_iso_iff (Arrow.isoMk (hsch.flip.isoIsPullback _ _ hres)
    (Iso.refl _) ?_)).mp hP
  exact (hsch.flip.isoIsPullback_hom_fst _ _ hres).trans (Category.comp_id _).symm

/-- **The affine test suffices.** Let `P` be a property of morphisms of schemes which is
Zariski-local at the target. A relatively representable morphism `f` of presheaves on the big
fppf site over `S` whose base change along every morphism from an *affine* object of the site is
represented by a morphism with `P` satisfies `(P.inverseImage _).presheaf`, that is, the same
holds for every object of the site.

The affine test is a hypothesis rather than the predicate itself, so that the one proof serves
both `AlgebraicGeometry.Space.IsFinite` and `AlgebraicGeometry.Space.IsIntegralHom`. -/
theorem presheaf_inverseImage_of_isAffine_test
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable f)
    (haff : ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ (ξ : yoneda.obj U ⟶ Y), ∃ (V : BigFppfOver B S hS) (p : V ⟶ U) (i : yoneda.obj V ⟶ X),
        P ((BigFppfOver.toScheme B S hS).map p) ∧ IsPullback i (yoneda.map p) f ξ) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f :=
  MorphismProperty.relative_of_snd hrep fun {a} g =>
    property_snd_of_affineOpens P hrep g fun V =>
      haff (openObj B S hS a V.1) V.2 (yoneda.map (openObjHom B S hS a V.1) ≫ g)

/-- **The relative property gives the affine test.** If `P` is contained in
`AlgebraicGeometry.IsAffineHom` and `f` satisfies `(P.inverseImage _).presheaf`, then the base
change of `f` along a morphism from an affine object of the site is represented by an object
of the site which is again affine, by a morphism with `P`.

Affineness of the representing object is not an extra hypothesis: it follows from `P`, since
a scheme affine over an affine scheme is affine. -/
theorem isAffine_test_of_presheaf_inverseImage
    (P : MorphismProperty Scheme.{u})
    (hPaff : ∀ {A C : Scheme.{u}} (q : A ⟶ C), P q → IsAffineHom q)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (ξ : yoneda.obj U ⟶ Y) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ U) (i : yoneda.obj V ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        P ((BigFppfOver.toScheme B S hS).map p) ∧ IsPullback i (yoneda.map p) f ξ := by
  obtain ⟨V, p, i, hpb⟩ := hf.rep ξ
  have hP : P ((BigFppfOver.toScheme B S hS).map p) := hf.property ξ i p hpb
  have _ := hPaff _ hP
  have _ := hU
  exact ⟨V, p, i, isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map p), hP, hpb⟩

end Criterion

/-! ### Finite and integral morphisms of algebraic spaces -/

section Conditions

variable {B S hS} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)

/-- **Stacks 03ZQ, condition (1) implies condition (2), finite case.** A morphism of presheaves
on the big fppf site over `S` which is relatively representable and whose represented base
changes are finite morphisms of schemes is a finite morphism of algebraic spaces. -/
theorem isFinite_of_presheaf_isFinite
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsFinite B S hS f :=
  fun U hU ξ => isAffine_test_of_presheaf_inverseImage _
    (fun _ h => h.toIsAffineHom) hf U hU ξ

/-- **Stacks 03ZQ, condition (2) implies condition (1), finite case, for a relatively
representable morphism.** A relatively representable finite morphism of algebraic spaces has
finite represented base changes along morphisms from *every* object of the site, not only from
the affine ones. -/
theorem presheaf_isFinite_of_isFinite
    (hrep : yoneda.relativelyRepresentable f) (h : IsFinite B S hS f) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  have _ := isZariskiLocalAtTarget_isIntegralHom.{u}
  have _ := isZariskiLocalAtTarget_locallyOfFiniteType.{u}
  have aux : ∀ (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P],
      (∀ {A C : Scheme.{u}} (q : A ⟶ C), AlgebraicGeometry.IsFinite q → P q) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f := by
    intro P _ hP
    refine presheaf_inverseImage_of_isAffine_test _ hrep fun U hU ξ => ?_
    obtain ⟨V, p, i, _, hfin, hpb⟩ := h U hU ξ
    exact ⟨V, p, i, hP _ hfin, hpb⟩
  have hint := aux (@_root_.AlgebraicGeometry.IsIntegralHom.{u}) fun _ hfin =>
    ((_root_.AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).1 hfin).1
  have hft := aux (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u}) fun _ hfin =>
    ((_root_.AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).1 hfin).2
  exact ⟨hrep, fun {_ _} g fst snd hsq =>
    (_root_.AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).2
      ⟨hint.property g fst snd hsq, hft.property g fst snd hsq⟩⟩

/-- **Stacks 03ZQ, conditions (1) and (2), finite case, for a relatively representable
morphism.** A relatively representable morphism of algebraic spaces over `S` is finite exactly
when it is relatively representable with finite represented base changes. The representability
conjunct on the right is kept, as in the source; it is implied by the rest of that side. -/
theorem isFinite_iff_representable_of_relativelyRepresentable
    (hrep : yoneda.relativelyRepresentable f) :
    IsFinite B S hS f ↔
      (yoneda.relativelyRepresentable f ∧
        (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f) :=
  ⟨fun h => ⟨hrep, presheaf_isFinite_of_isFinite f hrep h⟩,
    fun h => isFinite_of_presheaf_isFinite f h.2⟩

/-- **What the representability hypothesis costs, finite case.** The equivalence of conditions
(1) and (2) of Stacks 03ZQ, asserted with no hypothesis, is *equivalent* to the single
implication that a finite morphism of algebraic spaces is relatively representable. So that
implication is the whole of the content which
`AlgebraicGeometry.Space.isFinite_iff_representable_of_relativelyRepresentable` leaves out, and
it is implied by the
right-hand side of the equivalence it would prove. -/
theorem isFinite_iff_representable_iff :
    (IsFinite B S hS f ↔
        (yoneda.relativelyRepresentable f ∧
          (MorphismProperty.inverseImage
            (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf f)) ↔
      (IsFinite B S hS f → yoneda.relativelyRepresentable f) :=
  ⟨fun hiff hfin => (hiff.1 hfin).1,
    fun h => ⟨fun hfin => ⟨h hfin, presheaf_isFinite_of_isFinite f (h hfin) hfin⟩,
      fun hr => isFinite_of_presheaf_isFinite f hr.2⟩⟩

/-- **Stacks 03ZQ, condition (1) implies condition (2), integral case.** A morphism of
presheaves on the big fppf site over `S` which is relatively representable and whose
represented base changes are integral morphisms of schemes is an integral morphism of
algebraic spaces. -/
theorem isIntegralHom_of_presheaf_isIntegralHom
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsIntegralHom B S hS f := by
  intro Z hZ g
  obtain ⟨W, p, q, hW, hint, hpb⟩ := isAffine_test_of_presheaf_inverseImage _
    (fun _ h => h.toIsAffineHom) hf Z hZ g
  exact ⟨W, p, q, hpb, hW, hint⟩

/-- **Stacks 03ZQ, condition (2) implies condition (1), integral case, for a relatively
representable morphism.** A relatively representable integral morphism of algebraic spaces has
integral represented base changes along morphisms from *every* object of the site, not only from
the affine ones. -/
theorem presheaf_isIntegralHom_of_isIntegralHom
    (hrep : yoneda.relativelyRepresentable f) (h : IsIntegralHom B S hS f) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  have _ := isZariskiLocalAtTarget_isIntegralHom.{u}
  refine presheaf_inverseImage_of_isAffine_test _ hrep fun U hU ξ => ?_
  obtain ⟨V, p, i, hpb, _, hint⟩ := h U hU ξ
  exact ⟨V, p, i, hint, hpb⟩

/-- **Stacks 03ZQ, conditions (1) and (2), integral case, for a relatively representable
morphism.** A relatively representable morphism of algebraic spaces over `S` is integral exactly
when it is relatively representable with integral represented base changes. -/
theorem isIntegralHom_iff_representable_of_relativelyRepresentable
    (hrep : yoneda.relativelyRepresentable f) :
    IsIntegralHom B S hS f ↔
      (yoneda.relativelyRepresentable f ∧
        (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f) :=
  ⟨fun h => ⟨hrep, presheaf_isIntegralHom_of_isIntegralHom f hrep h⟩,
    fun h => isIntegralHom_of_presheaf_isIntegralHom f h.2⟩

/-- **What the representability hypothesis costs, integral case.** The equivalence of conditions
(1) and (2) of Stacks 03ZQ, asserted with no hypothesis, is *equivalent* to the single
implication that an integral morphism of algebraic spaces is relatively representable. -/
theorem isIntegralHom_iff_representable_iff :
    (IsIntegralHom B S hS f ↔
        (yoneda.relativelyRepresentable f ∧
          (MorphismProperty.inverseImage
            (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf f)) ↔
      (IsIntegralHom B S hS f → yoneda.relativelyRepresentable f) :=
  ⟨fun hiff hint => (hiff.1 hint).1,
    fun h => ⟨fun hint => ⟨h hint, presheaf_isIntegralHom_of_isIntegralHom f (h hint) hint⟩,
      fun hr => isIntegralHom_of_presheaf_isIntegralHom f hr.2⟩⟩

end Conditions

end AlgebraicGeometry.Space

end
