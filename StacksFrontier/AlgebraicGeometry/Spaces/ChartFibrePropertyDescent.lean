module

public import StacksFrontier.AlgebraicGeometry.Descent.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen

/-!
# The fibre locus of a chart descends to the space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`f : h_V ⟶ X` be a morphism from a representable presheaf, and let `a : h_A ⟶ X` be a chart.
For a morphism property `P` of schemes, consider the condition "the represented fibre of `f`
over a field-valued point of `X` satisfies `P`". This file proves that the condition depends
only on the *class* of that field-valued point, that is, only on the corresponding point of
`X` in the sense of Tag 03BU, and draws the consequence for the chart: the set of points of
`h_A` at which the fibre satisfies `P` is the preimage along the chart of a set of points of
`X`, and when it is closed and the chart is surjective étale, that set of points of `X` is
closed.

This is the step of the proof of Stacks 07S8 which turns a stratification of the chart into a
stratification of the space: in the source it reads "the formation of these closed subsets
commutes with base change … in other words the closed subsets `Y_r ⊂ U` are `R`-invariant …
this means that `|Y_r|` is the inverse image of a closed subset `Z_r ⊂ |X|`". Nothing here is
a Stacks tag of its own.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.property_representedFibre_iff_of_dominates` and
  `AlgebraicGeometry.Space.property_representedFibre_iff_of_class_eq`: the property `P` of the
  represented fibre of `f` over a field-valued point of `X` is unchanged when that point is
  replaced by one it dominates, and therefore depends only on its class. These are the general
  forms, for an arbitrary morphism property local at the target for the fpqc topology, of the
  invariance which the proof of Tag 086T establishes for the degree-at-least condition.
* `AlgebraicGeometry.Space.mem_representedFibreLocus_iff`: the locus of points of a chart at
  which the fibre satisfies `P` is tested at any field-valued representative. This is the
  inhabitation of the hypothesis `hY` carried by the two results below.
* `AlgebraicGeometry.Space.preimage_image_pointsMap_eq_of_representedFibreLocus`: such a locus
  is the preimage along the chart of its own image, i.e. it is saturated for the chart. This is
  `R`-invariance in point-set form.
* `AlgebraicGeometry.Space.isClosed_image_pointsMap_of_representedFibreLocus`: a closed such
  locus has closed image in the points of `X`, for a chart surjective on points.
* `AlgebraicGeometry.Space.isClosed_image_pointsMap_isFiniteLocallyFreeOfRank_locus`: the case
  `P = `being finite locally free of rank `r`, where the fpqc locality hypothesis is discharged
  by Tag 02VO and nothing is carried.

## Implementation notes

The invariance under domination is the argument of the source read for a single property. A
morphism of field spectra is by itself an fpqc covering
(`AlgebraicGeometry.Space.fpqc_singleton_of_fieldSpecHom`), so a property local at the target
for the fpqc topology may be tested after base change along it
(`AlgebraicGeometry.Space.property_iff_fpqc_singleton_pullback`); the two represented fibres
differ by exactly that base change, up to the two reassociations
`AlgebraicGeometry.Space.property_representedPullback_assoc` and
`AlgebraicGeometry.Space.property_map_pullback_snd_iff_pullback_fst`, which only need `P` to
respect isomorphisms.

`AlgebraicGeometry.Space.FibreDegreeGe` and the three private lemmas
`fibreDegreeGe_iff_sourceIso`, `fibreDegreeGe_iff_sitePullback` and
`fibreDegreeGe_iff_representedPullback_assoc` of
`StacksFrontier/AlgebraicGeometry/Spaces/FibreDegreeStratification.lean` are the special case of
the lemmas of this file for the disjunction of two properties; they are private there, so they
cannot be reused, and they are subsumed by the general forms proved here.

The descent of the locus is the quotient-map property of a surjective étale chart on points,
`AlgebraicGeometry.Space.isQuotientMap_pointsMap_of_presheafEtale`, which is clause (3) of
Tag 03BX together with clause (2): a set of points of `X` is closed exactly when its preimage
in the chart is closed, and the preimage of the image of a saturated set is the set itself.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 02VO](https://stacks.math.columbia.edu/tag/02VO)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reassociating a represented fibre -/

/-- A morphism property respecting isomorphisms holds of one projection of a pullback exactly
when it holds of the other projection of the swapped pullback. -/
private theorem property_pullback_snd_iff_fst
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) : P (pullback.snd f g) ↔ P (pullback.fst g f) := by
  rw [← pullbackSymmetry_hom_comp_fst f g]
  exact P.cancel_left_of_respectsIso _ _

/-- A morphism property respecting isomorphisms holds of the underlying morphism of schemes of
a fibre product formed in the site exactly when it holds of the corresponding projection of the
fibre product of the underlying schemes: the forgetful functor to schemes preserves pullbacks,
so the two differ by an isomorphism of the source.

This is the general form of the private lemma `fibreDegreeGe_iff_sitePullback` of
`StacksFrontier/AlgebraicGeometry/Spaces/FibreDegreeStratification.lean`. -/
theorem property_map_pullback_snd_iff_pullback_fst
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {A C T : BigFppfOver B S hS} (a : A ⟶ T) (c : C ⟶ T) :
    P ((BigFppfOver.toScheme B S hS).map (pullback.snd a c)) ↔
      P (pullback.fst ((BigFppfOver.toScheme B S hS).map c)
        ((BigFppfOver.toScheme B S hS).map a)) := by
  let T' := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan T' := by
    apply comp_preservesLimitsOfShape
  let e := ((IsPullback.of_hasPullback a c).map T').isoIsPullback _ _
    (IsPullback.of_hasPullback (T'.map a) (T'.map c))
  have he : e.hom ≫ pullback.snd (T'.map a) (T'.map c) = T'.map (pullback.snd a c) :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  rw [← he, P.cancel_left_of_respectsIso]
  exact property_pullback_snd_iff_fst P _ _

/-- Representing the fibre product of `f` with a chart precomposed by a morphism of the site is
the same as restricting the already represented fibre product along that morphism, for any
morphism property respecting isomorphisms.

This is the general form of the private lemma `fibreDegreeGe_iff_representedPullback_assoc` of
`StacksFrontier/AlgebraicGeometry/Spaces/FibreDegreeStratification.lean`. -/
theorem property_representedPullback_assoc
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V A T : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (a : yoneda.obj A ⟶ X) (c : T ⟶ A) :
    P ((BigFppfOver.toScheme B S hS).map (hf.snd (yoneda.map c ≫ a))) ↔
      P ((BigFppfOver.toScheme B S hS).map (pullback.snd (hf.snd a) c)) := by
  let T' := BigFppfOver.toScheme B S hS
  have hcomp := ((IsPullback.of_hasPullback (hf.snd a) c).map yoneda).paste_horiz
    (hf.isPullback a)
  let htarget := hf.isPullback (yoneda.map c ≫ a)
  let e := yoneda.preimageIso (hcomp.isoIsPullback _ _ htarget)
  have he : e.hom ≫ hf.snd (yoneda.map c ≫ a) = pullback.snd (hf.snd a) c := by
    apply yoneda.map_injective
    simp [e]
  have he' : (T'.mapIso e).hom ≫ T'.map (hf.snd (yoneda.map c ≫ a)) =
      T'.map (pullback.snd (hf.snd a) c) := by
    change T'.map e.hom ≫ _ = _
    rw [← Functor.map_comp, he]
  rw [← he']
  exact (MorphismProperty.cancel_left_of_respectsIso P (T'.mapIso e).hom
    (T'.map (hf.snd (yoneda.map c ≫ a)))).symm

/-! ### Invariance of the fibre property under the point class -/

/-- **The property `P` of the represented fibre of `f` is unchanged when a field-valued point
of the target is replaced by one it dominates.** The two represented fibres differ by a base
change along a morphism of spectra of fields, which is an fpqc covering, so a property local at
the target for the fpqc topology cannot distinguish them.

This is the general form of the private lemma `fibreDegreeGe_iff_fieldPoint_dominates` of
`StacksFrontier/AlgebraicGeometry/Spaces/FibreDegreeStratification.lean`. -/
theorem property_representedFibre_iff_of_dominates
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hloc : MorphismProperty.IsLocalAtTarget P Scheme.fpqcPrecoverage)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (p q : FieldValuedPoint B S hS X)
    (hpq : FieldValuedPoint.Dominates B S hS X q p) :
    P ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm p.value))) ↔
      P ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm q.value))) := by
  have := hloc
  let T' := BigFppfOver.toScheme B S hS
  let αp := yonedaEquiv.symm p.value
  obtain ⟨c, hc⟩ := hpq
  have hα : yoneda.map c ≫ αp = yonedaEquiv.symm q.value := by
    apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality αp c]
    simpa [αp] using hc
  have hrepr : P (T'.map (hf.snd (yonedaEquiv.symm q.value))) ↔
      P (T'.map (pullback.snd (hf.snd αp) c)) := by
    rw [← hα]
    exact property_representedPullback_assoc B S hS P f hf αp c
  have hext : P (T'.map (hf.snd αp)) ↔ P (pullback.snd (T'.map (hf.snd αp)) (T'.map c)) :=
    property_iff_fpqc_singleton_pullback P _ _ (fpqc_singleton_of_fieldSpecHom (T'.map c))
  exact (hext.trans ((property_pullback_snd_iff_fst P _ _).trans
    (property_map_pullback_snd_iff_pullback_fst B S hS P (hf.snd αp) c).symm)).trans hrepr.symm

/-- **The property `P` of the represented fibre of `f` over a field-valued point of the target
depends only on the class of that point**, that is, only on the corresponding point of `X` in
the sense of Tag 03BU. Two field-valued points have the same class exactly when they have a
common extension, and the fibre property is invariant under domination.

This is the general form of the private lemma `fibreDegreeGe_iff_fieldPoint_class_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/FibreDegreeStratification.lean`. -/
theorem property_representedFibre_iff_of_class_eq
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hloc : MorphismProperty.IsLocalAtTarget P Scheme.fpqcPrecoverage)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (p q : FieldValuedPoint B S hS X)
    (hclass : p.class B S hS X = q.class B S hS X) :
    P ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm p.value))) ↔
      P ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm q.value))) := by
  obtain ⟨r, hp, hq⟩ := (FieldValuedPoint.class_eq_class_iff B S hS X p q).mp hclass
  exact (property_representedFibre_iff_of_dominates B S hS P hloc f hf p r hp).trans
    (property_representedFibre_iff_of_dominates B S hS P hloc f hf q r hq).symm

/-! ### The fibre locus of a chart -/

/-- **The locus of points of a chart at which the fibre of `f` satisfies `P` may be tested at
any field-valued representative.** This is the inhabitation of the hypothesis `hY` of
`AlgebraicGeometry.Space.preimage_image_pointsMap_eq_of_representedFibreLocus` and of
`AlgebraicGeometry.Space.isClosed_image_pointsMap_of_representedFibreLocus`: the set displayed
here satisfies it, so that hypothesis is neither vacuous nor stronger than the description it
gives. -/
theorem mem_representedFibreLocus_iff
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hloc : MorphismProperty.IsLocalAtTarget P Scheme.fpqcPrecoverage)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V A : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (a : yoneda.obj A ⟶ X) (p : FieldValuedPoint B S hS (yoneda.obj A)) :
    p.class B S hS (yoneda.obj A) ∈
        {y : points B S hS (yoneda.obj A) |
          ∃ q : FieldValuedPoint B S hS (yoneda.obj A),
            q.class B S hS (yoneda.obj A) = y ∧
              P ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm
                (FieldValuedPoint.map B S hS (yoneda.obj A) a q).value)))} ↔
      P ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm
        (FieldValuedPoint.map B S hS (yoneda.obj A) a p).value))) :=
  ⟨fun ⟨q, hq, hqP⟩ => (property_representedFibre_iff_of_class_eq B S hS P hloc f hf
      (FieldValuedPoint.map B S hS (yoneda.obj A) a q)
      (FieldValuedPoint.map B S hS (yoneda.obj A) a p)
      (congrArg (pointsMap B S hS (yoneda.obj A) a) hq)).mp hqP,
    fun hp => ⟨p, rfl, hp⟩⟩

/-- **A fibre locus of a chart is saturated for the chart**: it is the preimage along the chart
of its own image. This is the `R`-invariance of the source's closed subsets `Y_r`, in the
point-set form in which the next lemma consumes it.

The hypothesis `hY` says that `Y` is the locus of points of the chart at which the represented
fibre of `f` satisfies `P`, tested at an arbitrary field-valued representative; it is satisfied
by `AlgebraicGeometry.Space.mem_representedFibreLocus_iff`. -/
theorem preimage_image_pointsMap_eq_of_representedFibreLocus
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hloc : MorphismProperty.IsLocalAtTarget P Scheme.fpqcPrecoverage)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V A : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (a : yoneda.obj A ⟶ X) (Y : Set (points B S hS (yoneda.obj A)))
    (hY : ∀ p : FieldValuedPoint B S hS (yoneda.obj A),
      p.class B S hS (yoneda.obj A) ∈ Y ↔
        P ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm
          (FieldValuedPoint.map B S hS (yoneda.obj A) a p).value)))) :
    pointsMap B S hS (yoneda.obj A) a ⁻¹' (pointsMap B S hS (yoneda.obj A) a '' Y) = Y := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro x ⟨y, hyY, hxy⟩
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  obtain ⟨q, rfl⟩ := Quot.exists_rep y
  exact (hY p).mpr ((property_representedFibre_iff_of_class_eq B S hS P hloc f hf
    (FieldValuedPoint.map B S hS (yoneda.obj A) a q)
    (FieldValuedPoint.map B S hS (yoneda.obj A) a p) hxy).mp ((hY q).mp hyY))

/-- **A closed fibre locus of a surjective étale chart has closed image in the points of the
space.** This is the conclusion "`|Y_r|` is the inverse image of a closed subset `Z_r ⊂ |X|`"
of the proof of Stacks 07S8: a surjective étale chart is a quotient map on points, by clauses
(2) and (3) of Tag 03BX, so a set of points of `X` is closed as soon as its preimage in the
chart is, and the preimage of the image of a saturated set is the set itself. -/
theorem isClosed_image_pointsMap_of_representedFibreLocus
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hloc : MorphismProperty.IsLocalAtTarget P Scheme.fpqcPrecoverage)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V A : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (a : yoneda.obj A ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hasurj : Function.Surjective (pointsMap B S hS (yoneda.obj A) a))
    (Y : Set (points B S hS (yoneda.obj A)))
    (hY : ∀ p : FieldValuedPoint B S hS (yoneda.obj A),
      p.class B S hS (yoneda.obj A) ∈ Y ↔
        P ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm
          (FieldValuedPoint.map B S hS (yoneda.obj A) a p).value))))
    (hYc : IsClosed Y) :
    IsClosed (pointsMap B S hS (yoneda.obj A) a '' Y) := by
  have hq := isQuotientMap_pointsMap_of_presheafEtale B S hS a ha hasurj
  rw [← hq.isCoinducing.isClosed_preimage,
    preimage_image_pointsMap_eq_of_representedFibreLocus B S hS P hloc f hf a Y hY]
  exact hYc

/-! ### The case of a fixed rank -/

/-- **The locus of a chart where the fibre is finite locally free of rank `r` is saturated, and
its image is closed as soon as it is.** This is the case
`P = Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property r` of the two lemmas above, for which
the fpqc locality hypothesis is the second assertion of Tag 02VO,
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc`, so nothing is carried.

This is the property in which Stacks 07S8 describes its strata. -/
theorem isClosed_image_pointsMap_isFiniteLocallyFreeOfRank_locus
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V A : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (a : yoneda.obj A ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hasurj : Function.Surjective (pointsMap B S hS (yoneda.obj A) a))
    (r : ℕ) (Y : Set (points B S hS (yoneda.obj A)))
    (hY : ∀ p : FieldValuedPoint B S hS (yoneda.obj A),
      p.class B S hS (yoneda.obj A) ∈ Y ↔
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank
          ((BigFppfOver.toScheme B S hS).map (hf.snd (yonedaEquiv.symm
            (FieldValuedPoint.map B S hS (yoneda.obj A) a p).value))) r)
    (hYc : IsClosed Y) :
    pointsMap B S hS (yoneda.obj A) a ⁻¹'
        (pointsMap B S hS (yoneda.obj A) a '' Y) = Y ∧
      IsClosed (pointsMap B S hS (yoneda.obj A) a '' Y) :=
  ⟨preimage_image_pointsMap_eq_of_representedFibreLocus B S hS
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc.{u} r) f hf a Y hY,
    isClosed_image_pointsMap_of_representedFibreLocus B S hS
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc.{u} r) f hf a ha hasurj
      Y hY hYc⟩

end AlgebraicGeometry.Space

end
