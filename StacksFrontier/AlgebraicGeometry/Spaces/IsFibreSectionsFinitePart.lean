module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.AlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SectionOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalars

/-!
# A pair for the restriction of scalars as a pair of Stacks 04PC

Let `x : X ⟶ Z` and `z : Z ⟶ Q` be morphisms of algebraic spaces over `S` and let
`p = (a, b)` be a pair of Stacks 05Y9 for them at a scheme `T` of the site, that is a morphism
`a : T ⟶ Q` together with a morphism `b : T ×_{a, Q} Z ⟶ X` over `Z`
(`AlgebraicGeometry.Space.RestrictionPair`). This file attaches to `p` a pair of Stacks 04PC for
the composite `x ≫ z : X ⟶ Q`, namely `a` together with the image of `b` inside `T ×_{a, Q} X`,
and shows that the construction is natural and injective.

This is the relative form, over an arbitrary base `Q`, of `AlgebraicGeometry.Space.sectionPair`
and its two companion results `AlgebraicGeometry.Space.isBaseChange_sectionPair` and
`AlgebraicGeometry.Space.sectionPair_injective`, which treat the absolute case: there `Q` is the
final algebraic space of the site and `Z` is an object of the site, so a pair is just a section
and the ambient fibre product is a product.

## Main definitions

* `AlgebraicGeometry.Space.pairAmbientProjection`: the base change `T ×_Q X ⟶ T ×_Q Z` of `x`.
* `AlgebraicGeometry.Space.ambientBaseChangeMap`: the comparison `T' ×_Q Z ⟶ T ×_Q Z` of two
  ambient fibre products whose base morphisms are related by a composite.
* `AlgebraicGeometry.Space.pairLift`: the second component of a pair, read as a section of that
  base change.
* `AlgebraicGeometry.Space.restrictionPairFinitePart`: **the pair of Stacks 04PC attached to a
  pair for the restriction of scalars.**

## Main results

* `AlgebraicGeometry.Space.isPullback_pairAmbientProjection`: `T ×_Q X ⟶ T ×_Q Z` is a base
  change of `x`.
* `AlgebraicGeometry.Space.isOpenImmersion_pairLift`: the second component of a pair is an open
  immersion into `T ×_Q X` when `x` is étale.
* `AlgebraicGeometry.Space.isBaseChange_restrictionPairFinitePart`: the pair of Stacks 04PC of a
  base-changed pair is the base change of the pair of Stacks 04PC.
* `AlgebraicGeometry.Space.restrictionPairFinitePart_injective`: a pair is determined by the pair
  of Stacks 04PC it defines.

## Implementation notes

The relative and the absolute constructions have the same shape and neither is an instance of
the other: the absolute one is phrased with the product `T × Z` and the terminal presheaf, which
do not occur here, and the relative one is phrased with a bound first component `a`, which does
not occur there.

`AlgebraicGeometry.Space.ambientBaseChangeMap` takes the target morphism `b` as data, with the
relation `b = k ≫ a` as a hypothesis, rather than spelling it as the composite: the first
component of a base-changed pair is only definitionally that composite, so spelling it out makes
rewriting along it fail its motive check.

## References

* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05Y9](https://stacks.math.columbia.edu/tag/05Y9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Z Q : AlgebraicSpaces B S hS}

/-- Pullbacks in presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_IsFibreSectionsFinitePart
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_IsFibreSectionsFinitePart :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-! ### The ambient base change of `x` -/

section Ambient

variable (x : X ⟶ Z) (z : Z ⟶ Q)

/-- **The base change `T ×_Q X ⟶ T ×_Q Z` of `x : X ⟶ Z`** along the projection
`T ×_Q Z ⟶ Z`, written as the comparison of two fibre products over `Q`. -/
noncomputable def pairAmbientProjection {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ Q.obj) :
    pullback a (x ≫ z).hom ⟶ pullback a z.hom :=
  pullback.map a (x ≫ z).hom a z.hom (𝟙 T) x.hom (𝟙 Q.obj) (by simp)
    (by simp [show (x ≫ z).hom = x.hom ≫ z.hom from rfl])

/-- The first component of `AlgebraicGeometry.Space.pairAmbientProjection` is the projection
to `T`. -/
@[simp] theorem pairAmbientProjection_comp_fst {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : T ⟶ Q.obj) :
    pairAmbientProjection x z a ≫ pullback.fst a z.hom = pullback.fst a (x ≫ z).hom := by
  rw [pairAmbientProjection, pullback.map_fst, Category.comp_id]

/-- The second component of `AlgebraicGeometry.Space.pairAmbientProjection` is the projection
to `X` followed by `x`. -/
@[simp] theorem pairAmbientProjection_comp_snd {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : T ⟶ Q.obj) :
    pairAmbientProjection x z a ≫ pullback.snd a z.hom =
      pullback.snd a (x ≫ z).hom ≫ x.hom := by
  rw [pairAmbientProjection, pullback.map_snd]

/-- **`T ×_Q X ⟶ T ×_Q Z` is a base change of `x`.** -/
theorem isPullback_pairAmbientProjection {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ Q.obj) :
    IsPullback (pairAmbientProjection x z a) (pullback.snd a (x ≫ z).hom)
      (pullback.snd a z.hom) x.hom := by
  refine IsPullback.of_right (h₁₂ := pullback.fst a z.hom) (h₂₂ := z.hom) ?_
    (pairAmbientProjection_comp_snd x z a) (.of_hasPullback a z.hom)
  rw [pairAmbientProjection_comp_fst]
  exact .of_hasPullback a (x ≫ z).hom

/-- The ambient fibre product `T ×_Q Z` of a pair is an algebraic space. -/
theorem isAlgebraicSpace_pullback_base {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Q.obj) :
    IsAlgebraicSpace B S hS (pullback a z.hom) :=
  isAlgebraicSpace_pullback B S hS a z.hom (isAlgebraicSpace_yoneda B S hS T) Z.property
    Q.property

/-- The ambient fibre product `T ×_Q X` of a pair is an algebraic space. -/
theorem isAlgebraicSpace_pullback_total {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Q.obj) :
    IsAlgebraicSpace B S hS (pullback a (x ≫ z).hom) :=
  isAlgebraicSpace_pullback B S hS a (x ≫ z).hom (isAlgebraicSpace_yoneda B S hS T) X.property
    Q.property

/-- **The base change of an étale `x` along the projection `T ×_Q Z ⟶ Z` is étale.** -/
theorem isEtale_pairAmbientProjection (hx : IsEtale B S hS x.hom) {T : BigFppfOver B S hS}
    (a : yoneda.obj T ⟶ Q.obj) : IsEtale B S hS (pairAmbientProjection x z a) :=
  isEtale_of_isPullback_of_isAlgebraicSpace B S hS (isPullback_pairAmbientProjection x z a)
    (isAlgebraicSpace_pullback_total x z a) (isAlgebraicSpace_pullback_base z a) X.property
    Z.property hx

/-- The projection `T ×_Q Z ⟶ T` is finite as soon as `z` is. -/
theorem isFinite_pullback_fst_base (hz : IsFinite B S hS z.hom)
    {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Q.obj) :
    IsFinite B S hS (pullback.fst a z.hom) :=
  isFinite_of_isPullback B S hS (IsPullback.of_hasPullback a z.hom).flip hz

end Ambient

/-! ### A pair, read as a section of the ambient base change -/

section PairLift

variable {x : X ⟶ Z} {z : Z ⟶ Q} {T : BigFppfOver B S hS}

/-- **The second component of a pair, read as a morphism `T ×_Q Z ⟶ T ×_Q X`**: the projection
to `T` on the first component and the second component of the pair on the second. -/
noncomputable def pairLift (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    pullback p.base z.hom ⟶ pullback p.base (x ≫ z).hom :=
  pullback.lift (pullback.fst p.base z.hom) p.lift (by
    have hover : p.lift ≫ x.hom ≫ z.hom = pullback.snd p.base z.hom ≫ z.hom := by
      rw [← Category.assoc, p.over]
    rw [show (x ≫ z).hom = x.hom ≫ z.hom from rfl, hover, pullback.condition])

/-- The first component of `AlgebraicGeometry.Space.pairLift` is the projection to `T`. -/
@[simp] theorem pairLift_comp_fst (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    pairLift p ≫ pullback.fst p.base (x ≫ z).hom = pullback.fst p.base z.hom :=
  pullback.lift_fst _ _ _

/-- The second component of `AlgebraicGeometry.Space.pairLift` is the second component of the
pair. -/
@[simp] theorem pairLift_comp_snd (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    pairLift p ≫ pullback.snd p.base (x ≫ z).hom = p.lift :=
  pullback.lift_snd _ _ _

/-- **`pairLift p` is a section of the base change of `x`.** -/
theorem pairLift_comp_pairAmbientProjection (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    pairLift p ≫ pairAmbientProjection x z p.base = 𝟙 (pullback p.base z.hom) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pairAmbientProjection_comp_fst, pairLift_comp_fst, Category.id_comp]
  · rw [Category.assoc, pairAmbientProjection_comp_snd, ← Category.assoc, pairLift_comp_snd,
      p.over, Category.id_comp]

/-- `pairLift p` is a monomorphism. -/
theorem mono_pairLift (p : RestrictionPair B S hS x z (yoneda.obj T)) : Mono (pairLift p) :=
  mono_of_section B S hS (pairAmbientProjection x z p.base) (pairLift p)
    (pairLift_comp_pairAmbientProjection p)

/-- **`pairLift p` is an open immersion** when `x` is étale. -/
theorem isOpenImmersion_pairLift (hx : IsEtale B S hS x.hom)
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    IsOpenImmersion B S hS (pairLift p) :=
  isOpenImmersion_of_isEtale_of_section B S hS (isAlgebraicSpace_pullback_total x z p.base)
    (isAlgebraicSpace_pullback_base z p.base) (pairAmbientProjection x z p.base)
    (isEtale_pairAmbientProjection x z hx p.base) (pairLift p)
    (pairLift_comp_pairAmbientProjection p)

/-- **`T ×_Q Z` is isomorphic to the image of `pairLift p` in `T ×_Q X`.** -/
noncomputable def pairLiftRangeIso (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    pullback p.base z.hom ≅ (Subfunctor.range (pairLift p)).toFunctor :=
  haveI := mono_pairLift p
  asIso (Subfunctor.toRange (pairLift p))

/-- The comparison of `T ×_Q Z` with the image of `pairLift p`, followed by the inclusion of
the image, is `pairLift p`. -/
@[simp] theorem pairLiftRangeIso_hom_comp_ι (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    (pairLiftRangeIso p).hom ≫ (Subfunctor.range (pairLift p)).ι = pairLift p :=
  Subfunctor.toRange_ι _

/-- The image of `pairLift p` is an algebraic space. -/
theorem isAlgebraicSpace_range_pairLift (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    IsAlgebraicSpace B S hS (Subfunctor.range (pairLift p)).toFunctor :=
  (isAlgebraicSpace_pullback_base z p.base).of_iso (pairLiftRangeIso p)

/-- The image of `pairLift p` is an open subspace of `T ×_Q X`. -/
theorem isOpenImmersion_range_pairLift (hx : IsEtale B S hS x.hom)
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    IsOpenImmersion B S hS (Subfunctor.range (pairLift p)).ι := by
  show (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf (Subfunctor.range (pairLift p)).ι
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (P := (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf) (pairLiftRangeIso p).hom]
  simpa using isOpenImmersion_pairLift hx p

/-- The inclusion of the image of `pairLift p` followed by the base change of `x` is the inverse
of the comparison of `T ×_Q Z` with that image. -/
theorem range_pairLift_ι_comp_pairAmbientProjection
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    (Subfunctor.range (pairLift p)).ι ≫ pairAmbientProjection x z p.base =
      (pairLiftRangeIso p).inv := by
  apply (Iso.cancel_iso_hom_left (pairLiftRangeIso p) _ _).1
  rw [← Category.assoc, pairLiftRangeIso_hom_comp_ι, pairLift_comp_pairAmbientProjection,
    Iso.hom_inv_id]

/-- The comparison of `T ×_Q Z` with the image of `pairLift p`, followed by the projection of
that image to `T`, is the projection `T ×_Q Z ⟶ T`. -/
theorem pairLiftRangeIso_hom_comp_ι_comp_fst (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    (pairLiftRangeIso p).hom ≫ (Subfunctor.range (pairLift p)).ι ≫
        pullback.fst p.base (x ≫ z).hom = pullback.fst p.base z.hom := by
  rw [← Category.assoc, pairLiftRangeIso_hom_comp_ι, pairLift_comp_fst]

/-- The comparison of `T ×_Q Z` with the image of `pairLift p`, followed by the projection of
that image to `X`, is the second component of `p`. -/
theorem pairLiftRangeIso_hom_comp_ι_comp_snd (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    (pairLiftRangeIso p).hom ≫ (Subfunctor.range (pairLift p)).ι ≫
        pullback.snd p.base (x ≫ z).hom = p.lift := by
  rw [← Category.assoc, pairLiftRangeIso_hom_comp_ι, pairLift_comp_snd]

/-- **The projection of the image of `pairLift p` to `T` is finite** as soon as `z` is. -/
theorem isFinite_range_pairLift_projection (hz : IsFinite B S hS z.hom)
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    IsFinite B S hS ((Subfunctor.range (pairLift p)).ι ≫
      pullback.fst p.base (x ≫ z).hom) := by
  have halg := isAlgebraicSpace_range_pairLift p
  have hbase := (isFinite_iff_representable B S hS (pullback.fst p.base z.hom)
    (isAlgebraicSpace_pullback_base z p.base) (isAlgebraicSpace_yoneda B S hS T)).1
    (isFinite_pullback_fst_base z hz p.base)
  have heq : (pairLiftRangeIso p).inv ≫ pullback.fst p.base z.hom =
      (Subfunctor.range (pairLift p)).ι ≫ pullback.fst p.base (x ≫ z).hom := by
    rw [← pairLiftRangeIso_hom_comp_ι_comp_fst p, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  have hpre := MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
    (pairLiftRangeIso p).inv (pullback.fst p.base z.hom) hbase.2
  rw [heq] at hpre
  exact (isFinite_iff_representable B S hS _ halg (isAlgebraicSpace_yoneda B S hS T)).2
    ⟨hpre.1, hpre⟩

end PairLift

/-! ### The pair of Stacks 04PC attached to a pair -/

section FinitePart

variable {x : X ⟶ Z} {z : Z ⟶ Q}

/-- **The pair of Stacks 04PC attached to a pair for the restriction of scalars**: its first
component together with the image of its second component inside `T ×_Q X`, which is an open
subspace finite over `T`. -/
noncomputable def restrictionPairFinitePart (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) {T : BigFppfOver B S hS}
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    FiniteOpenSubspace B S hS (x ≫ z) (schemeSpace T) where
  toBase := ObjectProperty.homMk p.base
  subspace := Subfunctor.range (pairLift p)
  isOpen := ⟨isAlgebraicSpace_range_pairLift p, isOpenImmersion_range_pairLift hx p⟩
  finite_projection := isFinite_range_pairLift_projection hz p

/-- The base morphism of the pair of Stacks 04PC attached to a pair is the pair's first
component. -/
theorem restrictionPairFinitePart_toBase (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) {T : BigFppfOver B S hS}
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    (restrictionPairFinitePart hx hz p).toBase.hom = p.base :=
  rfl

/-- The open subspace of the pair of Stacks 04PC attached to a pair is the image of
`AlgebraicGeometry.Space.pairLift`. -/
theorem restrictionPairFinitePart_subspace (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) {T : BigFppfOver B S hS}
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    (restrictionPairFinitePart hx hz p).subspace = Subfunctor.range (pairLift p) :=
  rfl

/-- **The comparison `T' ×_Q Z ⟶ T ×_Q Z`** of two ambient fibre products of pairs whose first
components are related by `hba : b = k ≫ a`. -/
noncomputable def ambientBaseChangeMap (z : Z ⟶ Q)
    {T₁ T₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : T₁ ⟶ T₂) (a : T₂ ⟶ Q.obj) (b : T₁ ⟶ Q.obj)
    (hba : b = k ≫ a) : pullback b z.hom ⟶ pullback a z.hom :=
  pullback.map b z.hom a z.hom k (𝟙 Z.obj) (𝟙 Q.obj) (by rw [hba]; simp) (by simp)

/-- The first component of `AlgebraicGeometry.Space.ambientBaseChangeMap` is the projection to
`T₁` followed by `k`. -/
@[simp] theorem ambientBaseChangeMap_comp_fst (z : Z ⟶ Q)
    {T₁ T₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : T₁ ⟶ T₂) (a : T₂ ⟶ Q.obj) (b : T₁ ⟶ Q.obj)
    (hba : b = k ≫ a) :
    ambientBaseChangeMap z k a b hba ≫ pullback.fst a z.hom = pullback.fst b z.hom ≫ k := by
  rw [ambientBaseChangeMap, pullback.map_fst]

/-- The second component of `AlgebraicGeometry.Space.ambientBaseChangeMap` is the projection to
`Z`. -/
@[simp] theorem ambientBaseChangeMap_comp_snd (z : Z ⟶ Q)
    {T₁ T₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : T₁ ⟶ T₂) (a : T₂ ⟶ Q.obj) (b : T₁ ⟶ Q.obj)
    (hba : b = k ≫ a) :
    ambientBaseChangeMap z k a b hba ≫ pullback.snd a z.hom = pullback.snd b z.hom := by
  rw [ambientBaseChangeMap, pullback.map_snd, Category.comp_id]

/-- **The ambient fibre product of a base-changed pair is a base change of the ambient fibre
product.** -/
theorem isPullback_ambientBaseChangeMap (z : Z ⟶ Q)
    {T₁ T₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : T₁ ⟶ T₂) (a : T₂ ⟶ Q.obj) (b : T₁ ⟶ Q.obj)
    (hba : b = k ≫ a) :
    IsPullback (pullback.fst b z.hom) (ambientBaseChangeMap z k a b hba) k
      (pullback.fst a z.hom) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd a z.hom) (v₂₂ := a) ?_
    (ambientBaseChangeMap_comp_fst z k a b hba).symm (.of_hasPullback a z.hom)
  rw [ambientBaseChangeMap_comp_snd, ← hba]
  exact .of_hasPullback b z.hom

/-- **The comparison of the ambient fibre products of a pair and of its base change along
`h`.** -/
noncomputable def pairRestrictAmbient {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    pullback (RestrictionPair.restrict (yoneda.map h) p).base z.hom ⟶ pullback p.base z.hom :=
  ambientBaseChangeMap z (yoneda.map h) p.base
    (RestrictionPair.restrict (yoneda.map h) p).base rfl

/-- The first component of `AlgebraicGeometry.Space.pairRestrictAmbient` is the projection to
`T'` followed by `h`. -/
@[simp] theorem pairRestrictAmbient_comp_fst {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    pairRestrictAmbient h p ≫ pullback.fst p.base z.hom =
      pullback.fst (RestrictionPair.restrict (yoneda.map h) p).base z.hom ≫ yoneda.map h :=
  ambientBaseChangeMap_comp_fst z (yoneda.map h) p.base _ rfl

/-- The second component of `AlgebraicGeometry.Space.pairRestrictAmbient` is the projection to
`Z`. -/
@[simp] theorem pairRestrictAmbient_comp_snd {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    pairRestrictAmbient h p ≫ pullback.snd p.base z.hom =
      pullback.snd (RestrictionPair.restrict (yoneda.map h) p).base z.hom :=
  ambientBaseChangeMap_comp_snd z (yoneda.map h) p.base _ rfl

/-- **The ambient fibre product of a base-changed pair is a base change of the ambient fibre
product.** -/
theorem isPullback_pairRestrictAmbient {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    IsPullback (pullback.fst (RestrictionPair.restrict (yoneda.map h) p).base z.hom)
      (pairRestrictAmbient h p) (yoneda.map h) (pullback.fst p.base z.hom) :=
  isPullback_ambientBaseChangeMap z (yoneda.map h) p.base _ rfl

/-- The second component of a base-changed pair is the second component of the pair, precomposed
with the comparison of the ambient fibre products. -/
theorem restrict_lift_eq_pairRestrictAmbient_comp {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    (RestrictionPair.restrict (yoneda.map h) p).lift = pairRestrictAmbient h p ≫ p.lift :=
  rfl

/-- The comparison of the images of the two `AlgebraicGeometry.Space.pairLift`s of a pair and of
its base change along `h`. -/
noncomputable def rangePairLiftRestrictMap {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    (Subfunctor.range (pairLift (RestrictionPair.restrict (yoneda.map h) p))).toFunctor ⟶
      (Subfunctor.range (pairLift p)).toFunctor :=
  (pairLiftRangeIso (RestrictionPair.restrict (yoneda.map h) p)).inv ≫
    pairRestrictAmbient h p ≫ (pairLiftRangeIso p).hom

/-- **The square of images is cartesian over `h`.** -/
theorem isPullback_rangePairLiftRestrictMap {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    IsPullback
      ((Subfunctor.range (pairLift (RestrictionPair.restrict (yoneda.map h) p))).ι ≫
        pullback.fst (RestrictionPair.restrict (yoneda.map h) p).base (x ≫ z).hom)
      (rangePairLiftRestrictMap h p) (yoneda.map h)
      ((Subfunctor.range (pairLift p)).ι ≫ pullback.fst p.base (x ≫ z).hom) := by
  refine (isPullback_pairRestrictAmbient h p).of_iso
    (pairLiftRangeIso (RestrictionPair.restrict (yoneda.map h) p)) (Iso.refl _)
    (pairLiftRangeIso p) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (pairLiftRangeIso_hom_comp_ι_comp_fst (RestrictionPair.restrict (yoneda.map h) p)).symm
  · rw [rangePairLiftRestrictMap, Iso.hom_inv_id_assoc]
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (pairLiftRangeIso_hom_comp_ι_comp_fst p).symm

/-- **The comparison of images is compatible with the two projections to `X`.** -/
theorem rangePairLiftRestrictMap_comp_snd {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    rangePairLiftRestrictMap h p ≫ (Subfunctor.range (pairLift p)).ι ≫
        pullback.snd p.base (x ≫ z).hom =
      (Subfunctor.range (pairLift (RestrictionPair.restrict (yoneda.map h) p))).ι ≫
        pullback.snd (RestrictionPair.restrict (yoneda.map h) p).base (x ≫ z).hom := by
  apply (Iso.cancel_iso_hom_left
    (pairLiftRangeIso (RestrictionPair.restrict (yoneda.map h) p)) _ _).1
  rw [rangePairLiftRestrictMap, Category.assoc, Iso.hom_inv_id_assoc, Category.assoc,
    pairLiftRangeIso_hom_comp_ι_comp_snd p,
    pairLiftRangeIso_hom_comp_ι_comp_snd (RestrictionPair.restrict (yoneda.map h) p),
    restrict_lift_eq_pairRestrictAmbient_comp h p]

/-- **The pair of Stacks 04PC of a base-changed pair is the base change of the pair of Stacks
04PC.** -/
theorem isBaseChange_restrictionPairFinitePart (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    FiniteOpenSubspace.IsBaseChange B S hS (x ≫ z) h (restrictionPairFinitePart hx hz p)
      (restrictionPairFinitePart hx hz (RestrictionPair.restrict (yoneda.map h) p)) :=
  ⟨rfl, rangePairLiftRestrictMap h p, isPullback_rangePairLiftRestrictMap h p,
    rangePairLiftRestrictMap_comp_snd h p⟩

/-- **A pair is determined by the pair of Stacks 04PC it defines.** -/
theorem restrictionPairFinitePart_injective (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) {T : BigFppfOver B S hS}
    {p q : RestrictionPair B S hS x z (yoneda.obj T)}
    (hpq : restrictionPairFinitePart hx hz p = restrictionPairFinitePart hx hz q) : p = q := by
  obtain ⟨pb, pl, po⟩ := p
  obtain ⟨qb, ql, qo⟩ := q
  have hbase : pb = qb :=
    congrArg (fun r : FiniteOpenSubspace B S hS (x ≫ z) (schemeSpace T) => r.toBase.hom) hpq
  cases hbase
  have hR : Subfunctor.range (pairLift (⟨pb, pl, po⟩ : RestrictionPair B S hS x z _)) =
      Subfunctor.range (pairLift (⟨pb, ql, qo⟩ : RestrictionPair B S hS x z _)) := by
    have hfields : ∀ (r r' : FiniteOpenSubspace B S hS (x ≫ z) (schemeSpace T)), r = r' →
        HEq r.subspace r'.subspace := by
      intro r r' hrr'
      subst hrr'
      exact HEq.rfl
    exact eq_of_heq (hfields _ _ hpq)
  have hlι : ((pairLiftRangeIso (⟨pb, ql, qo⟩ : RestrictionPair B S hS x z _)).hom ≫
        Subfunctor.homOfLe hR.ge) ≫
      (Subfunctor.range (pairLift (⟨pb, pl, po⟩ : RestrictionPair B S hS x z _))).ι =
      pairLift (⟨pb, ql, qo⟩ : RestrictionPair B S hS x z _) := by
    rw [Category.assoc, Subfunctor.homOfLe_ι, pairLiftRangeIso_hom_comp_ι]
  have h1 : ((pairLiftRangeIso (⟨pb, ql, qo⟩ : RestrictionPair B S hS x z _)).hom ≫
        Subfunctor.homOfLe hR.ge) ≫
      (pairLiftRangeIso (⟨pb, pl, po⟩ : RestrictionPair B S hS x z _)).inv =
      𝟙 (pullback pb z.hom) := by
    rw [← range_pairLift_ι_comp_pairAmbientProjection
      (⟨pb, pl, po⟩ : RestrictionPair B S hS x z _), ← Category.assoc, hlι,
      pairLift_comp_pairAmbientProjection]
  have hlinv : ((pairLiftRangeIso (⟨pb, ql, qo⟩ : RestrictionPair B S hS x z _)).hom ≫
        Subfunctor.homOfLe hR.ge) =
      (pairLiftRangeIso (⟨pb, pl, po⟩ : RestrictionPair B S hS x z _)).hom := by
    have hc := congrArg
      (fun t => t ≫ (pairLiftRangeIso (⟨pb, pl, po⟩ : RestrictionPair B S hS x z _)).hom) h1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp] using hc
  have key : pairLift (⟨pb, pl, po⟩ : RestrictionPair B S hS x z _) =
      pairLift (⟨pb, ql, qo⟩ : RestrictionPair B S hS x z _) := by
    rw [← hlι, hlinv, pairLiftRangeIso_hom_comp_ι]
  have hl : pl = ql := by
    have hk := congrArg (fun t => t ≫ pullback.snd pb (x ≫ z).hom) key
    exact (pairLift_comp_snd (⟨pb, pl, po⟩ : RestrictionPair B S hS x z _)).symm.trans
      (hk.trans (pairLift_comp_snd (⟨pb, ql, qo⟩ : RestrictionPair B S hS x z _)))
  cases hl
  rfl

end FinitePart

end AlgebraicGeometry.Space

end
