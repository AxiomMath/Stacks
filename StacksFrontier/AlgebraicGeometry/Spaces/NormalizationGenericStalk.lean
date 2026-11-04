module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The normalization of an algebraic space at its generic points

The normalization morphism `ν : X^ν ⟶ X` of an algebraic space over a scheme `S` is studied
here at the points of codimension zero. Over a decent base with finitely many irreducible
components the normalization is again such a space, the morphism `ν` carries the generic
points of `X^ν` bijectively onto those of `X`, and on a pair of compatible charts at a
generic point the induced map of local rings is *surjective*: the local ring of `X^ν` at a
generic point is a field, being a zero-dimensional normal domain, and a field-valued point of
`X` of codimension zero lifts uniquely to `X^ν` by the universal property of the
normalization.

## Main results

* `AlgebraicGeometry.Space.NormalizationData.isDecentSpace` and
  `AlgebraicGeometry.Space.NormalizationData.finite_irreducibleComponents`: the normalization
  of a decent algebraic space with finitely many irreducible components is again one.
* `AlgebraicGeometry.Space.NormalizationData.bijOn_genericPoints_hom`: the normalization
  morphism bijects generic points.
* `AlgebraicGeometry.Space.NormalizationData.localRingDimension_eq_zero_of_hom`: a point of
  the normalization lying over a point of codimension zero has codimension zero.
* `AlgebraicGeometry.Space.isField_genericChart_localRing_of_isNormal`: on a normal algebraic
  space the local ring of any chart at a point of codimension zero is a field.
* `AlgebraicGeometry.Space.NormalizationData.surjective_stalkMap_of_genericChart`: on
  compatible charts at a point of codimension zero the normalization morphism induces a
  surjection of local rings.

## Implementation notes

The normalization of an algebraic space is `AlgebraicGeometry.Space.NormalizationData`, a
morphism from an algebraic space whose base change along every surjective étale scheme chart
of the target is the normalization of that chart; everything below is universally quantified
over such data, as are the four parts of Stacks 0BB4.

Decency of the normalization is Stacks 0ABT applied to the normalization morphism, which is
integral and therefore representable. Finiteness of the irreducible components is read off
the bijection on codimension-zero points of Stacks 0BB4, part (3), through the identification
of the codimension-zero points of a decent algebraic space with the generic points of its
irreducible components, which is Stacks 0ABV.

The surjectivity statement is the engine of the birationality clause of Stacks 0BBG. The point
is that the normalization morphism, although not birational — it kills nilpotents — is *onto*
the local rings at codimension zero: the canonical field-valued representative of the image
point factors through the normalization by its universal property, and that factorization
splits the chart map up to the spectrum of a residue field, whose stalk maps are surjective.

## References

* [Stacks Project, Tag 0ABT](https://stacks.math.columbia.edu/tag/0ABT)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reducedness of a normal algebraic space -/

/-- **A normal algebraic space over `S` is reduced.** The chart witnessing normality is a
reduced scheme, because a normal scheme is, and it witnesses reducedness. -/
theorem hasEtaleLocalProperty_isReduced_of_isNormal
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsNormal B S hS F) :
    HasEtaleLocalProperty B S hS F
      (fun Z : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced Z) := by
  obtain ⟨U, f, hsurjective, hetale, hnormal⟩ := hF
  let : _root_.AlgebraicGeometry.IsNormal ((BigFppfOver.toScheme B S hS).obj U) := hnormal
  exact ⟨U, f, hsurjective, hetale, inferInstance⟩

/-! ### Field-valued points along a morphism -/

/-- A field-valued point of a presheaf, moved to another presheaf along a morphism out of the
presheaf it represents: the same field spectrum over the base, carrying the section that
classifies the given morphism. -/
noncomputable def FieldValuedPoint.ofHom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint B S hS F)
    (a : yoneda.obj (p.siteObject B S hS F) ⟶ G) : FieldValuedPoint B S hS G where
  carrier := p.carrier
  contained := p.contained
  toBase := p.toBase
  value := yonedaEquiv a

/-- Moving a field-valued point along a morphism and then pushing the resulting point forward
is moving it along the composite. -/
theorem FieldValuedPoint.pointsMap_class_ofHom
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS F)
    (a : yoneda.obj (p.siteObject B S hS F) ⟶ G) (b : G ⟶ H) :
    pointsMap B S hS G b ((FieldValuedPoint.ofHom B S hS p a).class B S hS G) =
      (FieldValuedPoint.ofHom B S hS p (a ≫ b)).class B S hS H := rfl

/-- Moving a field-valued point along the morphism it itself classifies returns it. -/
theorem FieldValuedPoint.ofHom_value {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint B S hS F) :
    FieldValuedPoint.ofHom B S hS p (yonedaEquiv.symm p.value) = p := by
  cases p
  simp [FieldValuedPoint.ofHom]

/-- If a morphism out of the field spectrum of a field-valued point composes with a morphism
of presheaves to the morphism that point classifies, then the point it defines upstairs lies
over the original point. -/
theorem FieldValuedPoint.pointsMap_class_ofHom_eq
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS F)
    (a : yoneda.obj (p.siteObject B S hS F) ⟶ G) (b : G ⟶ F)
    (h : a ≫ b = yonedaEquiv.symm p.value) :
    pointsMap B S hS G b ((FieldValuedPoint.ofHom B S hS p a).class B S hS G) =
      p.class B S hS F := by
  rw [FieldValuedPoint.pointsMap_class_ofHom, h, FieldValuedPoint.ofHom_value]

/-- The morphism classified by a field-valued point is constant on points: the spectrum of a
field has a single point, which it sends to the point the field-valued point represents. -/
theorem pointsMap_eq_class_of_fieldSpectrum
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS F)
    (z : points B S hS (yoneda.obj (p.siteObject B S hS F))) :
    pointsMap B S hS _ (yonedaEquiv.symm p.value) z = p.class B S hS F := by
  induction z using Quot.inductionOn with
  | _ q =>
    apply Quot.sound
    exact ⟨FieldValuedPoint.map B S hS _ (yonedaEquiv.symm p.value) q,
      FieldValuedPoint.dominates_refl B S hS F _, q.value, rfl⟩

/-- **The field spectrum of a field-valued point is a normal algebraic space over `S`.** The
spectrum of a field is a normal scheme, having a single local ring, which is that field. -/
theorem isNormal_yoneda_siteObject {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint B S hS F) :
    IsNormal B S hS (yoneda.obj (p.siteObject B S hS F)) := by
  refine (isNormal_iff_of_representable B S hS _ (p.siteObject B S hS F) (Iso.refl _)).2 ?_
  show _root_.AlgebraicGeometry.IsNormal (Spec (.of p.carrier))
  constructor
  · intro x
    obtain rfl : x = IsLocalRing.closedPoint p.carrier := Subsingleton.elim _ _
    exact (stalkClosedPointIso (.of p.carrier)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  · intro x
    obtain rfl : x = IsLocalRing.closedPoint p.carrier := Subsingleton.elim _ _
    exact IsIntegrallyClosed.of_equiv
      (stalkClosedPointIso (.of p.carrier)).commRingCatIsoToRingEquiv.symm

/-- Composing the pullback of a point of `N` along `a` with `ν` gives the point of `F` it maps
to. -/
theorem yoneda_map_comp_yonedaEquiv_symm_comp {N F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (ν : N ⟶ F) {X Y : BigFppfOver B S hS} (a : X ⟶ Y) (x : N.obj (Opposite.op Y))
    (y : F.obj (Opposite.op X)) (h : F.map a.op (ν.app _ x) = y) :
    (yoneda.map a ≫ yonedaEquiv.symm x) ≫ ν = yonedaEquiv.symm y := by
  apply (yonedaEquiv (X := X) (F := F)).injective
  simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply]
  exact (ν.naturality_apply a.op x).trans h

/-- **A morphism with unique liftings of field-valued points is injective on points there.**
If every field-valued point of the target satisfying `P` admits at most one lift along `ν`,
then `ν` separates the points of the source lying over points satisfying `P`. -/
theorem pointsMap_injective_of_unique_lift
    {N F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (ν : N ⟶ F) (P : points B S hS F → Prop)
    (hunique : ∀ r : FieldValuedPoint B S hS F, P (r.class B S hS F) →
      ∀ gp gq : yoneda.obj (r.siteObject B S hS F) ⟶ N,
        gp ≫ ν = yonedaEquiv.symm r.value →
        gq ≫ ν = yonedaEquiv.symm r.value → gp = gq)
    (z w : points B S hS N) (hz : P (pointsMap B S hS N ν z))
    (hzw : pointsMap B S hS N ν z = pointsMap B S hS N ν w) : z = w := by
  induction z using Quot.inductionOn with
  | _ p =>
    induction w using Quot.inductionOn with
    | _ q =>
      obtain ⟨r, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
        (FieldValuedPoint.class_eq_class_iff B S hS F _ _).mp hzw
      have hr : r.class B S hS F =
          (FieldValuedPoint.map B S hS N ν p).class B S hS F :=
        Quot.sound ⟨r, FieldValuedPoint.dominates_refl B S hS F r, a, ha⟩
      have heq := hunique r (hr.symm ▸ hz) _ _
        (yoneda_map_comp_yonedaEquiv_symm_comp B S hS ν a p.value r.value ha)
        (yoneda_map_comp_yonedaEquiv_symm_comp B S hS ν b q.value r.value hb)
      let t : FieldValuedPoint B S hS N :=
        { carrier := r.carrier, contained := r.contained, toBase := r.toBase,
          value := N.map a.op p.value }
      refine Quot.sound ⟨t, ⟨a, rfl⟩, b, ?_⟩
      exact (congrArg (fun k : yoneda.obj (r.siteObject B S hS F) ⟶ N =>
        k.app (Opposite.op (r.siteObject B S hS F)) (𝟙 _)) heq).symm

/-- **A field-valued point of the target of an open immersion lifts through it as soon as its
class does.** The base change of the open immersion along the morphism the point classifies is
an open immersion out of a scheme surjecting onto the spectrum of a field, hence an
isomorphism, and its inverse is the lift. -/
theorem exists_lift_fieldPoint_of_isOpenImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (i : G ⟶ F) (hi : IsOpenImmersion B S hS i)
    (p : FieldValuedPoint B S hS F) (q : FieldValuedPoint B S hS G)
    (hpq : pointsMap B S hS G i (q.class B S hS G) = p.class B S hS F) :
    ∃ a : yoneda.obj (p.siteObject B S hS F) ⟶ G, a ≫ i = yonedaEquiv.symm p.value := by
  obtain ⟨W, j, k, hpb⟩ := hi.1 (yonedaEquiv.symm p.value)
  obtain ⟨r, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS F _ _).mp hpq
  have h₁ := yoneda_map_comp_yonedaEquiv_symm_comp B S hS i a q.value r.value ha
  have h₂ : yoneda.map b ≫ yonedaEquiv.symm p.value = yonedaEquiv.symm r.value := by
    simpa using yoneda_map_comp_yonedaEquiv_symm_comp B S hS (𝟙 F) b p.value r.value hb
  let ℓ := hpb.lift (yoneda.map a ≫ yonedaEquiv.symm q.value) (yoneda.map b) (h₁.trans h₂.symm)
  let t : r.siteObject B S hS F ⟶ W := yoneda.preimage ℓ
  let T := BigFppfOver.toScheme B S hS
  have hj : _root_.AlgebraicGeometry.IsOpenImmersion (T.map j) := hi.2 _ _ _ hpb
  have hjSurj : Surjective (T.map j) := by
    let : Field p.carrier := p.field
    let : Field r.carrier := r.field
    refine ⟨fun x => ⟨T.map t (IsLocalRing.closedPoint r.carrier), ?_⟩⟩
    show (_ : Spec (.of p.carrier)) = x
    exact Subsingleton.elim _ _
  have : IsIso (T.map j) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hj, hjSurj⟩
  have : IsIso j := isIso_of_reflects_iso j T
  refine ⟨inv (yoneda.map j) ≫ k, ?_⟩
  rw [Category.assoc, hpb.w, IsIso.inv_hom_id_assoc]

/-- The canonical field-valued representative of the image of a scheme point under a morphism
of the site has the class of the pushed-forward point. -/
theorem schemePointRepresentative_class_map {U V : BigFppfOver B S hS} (j : U ⟶ V)
    (x : FieldValuedPoint B S hS (yoneda.obj U)) :
    (schemePointRepresentative B S hS V
        ((BigFppfOver.toScheme B S hS).map j (schemePoint B S hS U x))).class B S hS
          (yoneda.obj V) =
      pointsMap B S hS _ (yoneda.map j) (x.class B S hS (yoneda.obj U)) := by
  have h := schemePointRepresentative_class B S hS V
    (FieldValuedPoint.map B S hS _ (yoneda.map j) x)
  rw [show (BigFppfOver.toScheme B S hS).map
      (FieldValuedPoint.map B S hS _ (yoneda.map j) x).value
      (IsLocalRing.closedPoint (FieldValuedPoint.map B S hS _ (yoneda.map j) x).carrier) =
      (BigFppfOver.toScheme B S hS).map j (schemePoint B S hS U x) from
    schemePoint_map_yoneda B S hS j x] at h
  exact h

/-- If the stalk of `X` at `k q` is a field and the stalk map of `k ≫ f` at `q` is surjective,
then so is the stalk map of `f` at `k q`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.surjective_stalkMap_of_comp {X Y Z : Scheme.{u}}
    (k : Z ⟶ X) (f : X ⟶ Y) (q : Z) (hfield : IsField (X.presheaf.stalk (k q)))
    (h : Function.Surjective ((k ≫ f).stalkMap q).hom) :
    Function.Surjective (f.stalkMap (k q)).hom := by
  let : Field (X.presheaf.stalk (k q)) := hfield.toField
  rw [Scheme.Hom.stalkMap_comp] at h
  intro v
  obtain ⟨w, hw⟩ := h ((k.stalkMap q).hom v)
  exact ⟨w, (k.stalkMap q).hom.injective hw⟩

/-! ### The local ring of a normal algebraic space at a codimension-zero point -/

/-- **On a normal algebraic space over `S` the local ring of any chart at a point of
codimension zero is a field.** The chart is an open immersion, hence étale, so by Stacks 0BAM
its local ring at the chosen point has Krull dimension zero; and it is a domain because the
chart is a normal scheme. A zero-dimensional local domain is a field. -/
theorem isField_genericChart_localRing_of_isNormal
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hnormal : IsNormal B S hS F) (x : points B S hS F)
    (hx : localRingDimension B S hS x = 0) (c : GenericChart B S hS x) :
    IsField (c.localRing B S hS) := by
  let T := BigFppfOver.toScheme B S hS
  let t := schemePoint B S hS c.U c.point
  have heta := presheaf_etale_of_isOpenImmersion B S hS c.isOpen
  have hnormalU : _root_.AlgebraicGeometry.IsNormal (T.obj c.U) :=
    (isNormal_iff_forall_etale B S hS F hF).mp hnormal c.U c.immersion heta
  let : _root_.AlgebraicGeometry.IsNormal (T.obj c.U) := hnormalU
  have hchart : ChartPoint B S hS c.U c.immersion t x := ⟨c.point, rfl, c.mapsTo⟩
  have hdim : ringKrullDim (c.localRing B S hS) = 0 :=
    (hasChartLocalRingDimension_iff_allChartsLocalRingDimension B S hS hF x 0).mp
      ((localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hF x 0).mp hx)
      c.U c.immersion t heta hchart
  let : IsDomain (c.localRing B S hS) := hnormalU.stalk_isDomain t
  let : Ring.KrullDimLE 0 (c.localRing B S hS) :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
  exact Ring.KrullDimLE.isField_of_isDomain

/-- On a decent algebraic space the generic points are exactly the points of codimension
zero. -/
theorem genericPoints_eq_setOf_localRingDimension_eq_zero
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hdec : IsDecentSpace B S hS F) :
    genericPoints (points B S hS F) = {x | localRingDimension B S hS x = 0} :=
  Set.ext (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hF hdec)

/-! ### The normalization of a decent space with finitely many components -/

namespace NormalizationData

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The normalization of a decent algebraic space over `S` is decent.** The normalization
morphism is integral by Stacks 0BB4, part (2), hence representable by Stacks 03ZQ, and
decency passes to the source of a representable morphism by Stacks 0ABT. -/
theorem isDecentSpace (D : NormalizationData B S hS F) (hF : IsAlgebraicSpace B S hS F)
    (hdec : IsDecentSpace B S hS F) : IsDecentSpace B S hS D.space :=
  isDecentSpace_of_relativelyRepresentable B S hS D.isAlgebraicSpace D.hom
    ((isIntegralHom_iff_representable B S hS D.hom D.isAlgebraicSpace hF).1
      (D.isIntegralHom_hom hF)).1 hdec

/-- **The normalization of a decent algebraic space over `S` with finitely many irreducible
components has finitely many irreducible components.** On a decent algebraic space the
codimension-zero points are exactly the generic points of the irreducible components, by
Stacks 0ABV, and there are finitely many of those; the normalization morphism bijects
codimension-zero points by Stacks 0BB4, part (3), so the normalization has finitely many
generic points, and its point space is sober, so finitely many irreducible components. -/
theorem finite_irreducibleComponents (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (hdec : IsDecentSpace B S hS F)
    (hfinite : (irreducibleComponents (points B S hS F)).Finite) :
    (irreducibleComponents (points B S hS D.space)).Finite := by
  have hNdec : IsDecentSpace B S hS D.space := D.isDecentSpace hF hdec
  have hsoberF := stacksSober_points_of_isDecentSpace B S hS hF hdec
  let : T0Space (points B S hS F) := (stacksSober_iff_t0_and_quasiSober.mp hsoberF).1
  have hFcodim : {x : points B S hS F | localRingDimension B S hS x = 0}.Finite := by
    rw [← genericPoints_eq_setOf_localRingDimension_eq_zero B S hS hF hdec]
    exact genericPoints.finite hfinite
  have hsoberN := stacksSober_points_of_isDecentSpace B S hS D.isAlgebraicSpace hNdec
  let : T0Space (points B S hS D.space) := (stacksSober_iff_t0_and_quasiSober.mp hsoberN).1
  let : QuasiSober (points B S hS D.space) :=
    (stacksSober_iff_t0_and_quasiSober.mp hsoberN).2
  have hNgeneric : (genericPoints (points B S hS D.space)).Finite := by
    rw [genericPoints_eq_setOf_localRingDimension_eq_zero B S hS D.isAlgebraicSpace hNdec]
    exact (D.bijOn_codimensionZeroPoints_hom hF).finite_iff_finite.mpr hFcodim
  let : Finite (genericPoints (points B S hS D.space)) := hNgeneric.to_subtype
  exact Finite.of_equiv _ (genericPoints.equiv (α := points B S hS D.space))

/-- **The normalization morphism bijects generic points.** This is the bijection on
codimension-zero points of Stacks 0BB4, part (3), read through the identification of
codimension zero with genericity on a decent algebraic space, which is Stacks 0ABV. -/
theorem bijOn_genericPoints_hom (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (hdec : IsDecentSpace B S hS F) :
    Set.BijOn (pointsMap B S hS D.space D.hom)
      (genericPoints (points B S hS D.space)) (genericPoints (points B S hS F)) := by
  rw [genericPoints_eq_setOf_localRingDimension_eq_zero B S hS hF hdec,
    genericPoints_eq_setOf_localRingDimension_eq_zero B S hS D.isAlgebraicSpace
      (D.isDecentSpace hF hdec)]
  exact D.bijOn_codimensionZeroPoints_hom hF

/-! #### Codimension zero on the normalization -/

/-- A field-valued point of codimension zero of the base lifts uniquely to the normalization, by
the universal property of Stacks 0BB4, part (4), applied to the normal spectrum of its field. -/
private theorem existsUnique_lift_fieldPoint (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (r : FieldValuedPoint B S hS F)
    (hr : localRingDimension B S hS (r.class B S hS F) = 0) :
    ∃! a : yoneda.obj (r.siteObject B S hS F) ⟶ D.space, a ≫ D.hom = yonedaEquiv.symm r.value :=
  D.existsUnique_lift_hom hF (isAlgebraicSpace_yoneda B S hS _)
    (isNormal_yoneda_siteObject B S hS r) _ fun w _ =>
    (congrArg (localRingDimension B S hS) (pointsMap_eq_class_of_fieldSpectrum B S hS r w)).trans hr

/-- **The normalization morphism is injective over the points of codimension zero.** A
field-valued point of codimension zero of the base has at most one lift to the normalization,
by the uniqueness half of the universal property of Stacks 0BB4, part (4), applied to the
spectrum of its field: that spectrum is normal, and it carries codimension zero to the point
in question. -/
theorem pointsMap_hom_injective_of_localRingDimension_eq_zero
    (D : NormalizationData B S hS F) (hF : IsAlgebraicSpace B S hS F)
    (z w : points B S hS D.space)
    (hz : localRingDimension B S hS (pointsMap B S hS D.space D.hom z) = 0)
    (hzw : pointsMap B S hS D.space D.hom z = pointsMap B S hS D.space D.hom w) : z = w := by
  refine pointsMap_injective_of_unique_lift B S hS D.hom
    (fun x => localRingDimension B S hS x = 0) ?_ z w hz hzw
  intro r hr gp gq hgp hgq
  exact ExistsUnique.unique (D.existsUnique_lift_fieldPoint hF r hr) hgp hgq

/-- **A point of the normalization lying over a point of codimension zero has codimension
zero.** The bijection of Stacks 0BB4, part (3), produces such a point over the image, and the
normalization morphism does not separate it from the given one. -/
theorem localRingDimension_eq_zero_of_hom (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (z : points B S hS D.space)
    (hz : localRingDimension B S hS (pointsMap B S hS D.space D.hom z) = 0) :
    localRingDimension B S hS z = 0 := by
  obtain ⟨w, hw, heq⟩ := (D.bijOn_codimensionZeroPoints_hom hF).surjOn hz
  exact D.pointsMap_hom_injective_of_localRingDimension_eq_zero hF z w hz heq.symm ▸ hw

/-- **A field-valued point over a point of codimension zero of the normalization lifts
through any chart at that point.** It lifts to the normalization by the universal property of
Stacks 0BB4, part (4), and then through the open immersion of the chart. -/
theorem exists_lift_genericChart (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) {z : points B S hS D.space}
    (hz : localRingDimension B S hS z = 0) (c : GenericChart B S hS z)
    (p : FieldValuedPoint B S hS F) (hp : p.class B S hS F = pointsMap B S hS D.space D.hom z) :
    ∃ b : yoneda.obj (p.siteObject B S hS F) ⟶ yoneda.obj c.U,
      b ≫ c.immersion ≫ D.hom = yonedaEquiv.symm p.value ∧
        (FieldValuedPoint.ofHom B S hS p b).class B S hS (yoneda.obj c.U) =
          c.point.class B S hS (yoneda.obj c.U) := by
  have hpzero : localRingDimension B S hS (p.class B S hS F) = 0 :=
    hp ▸ (D.bijOn_codimensionZeroPoints_hom hF).mapsTo hz
  obtain ⟨a, ha, -⟩ := D.existsUnique_lift_fieldPoint hF p hpzero
  let pn := FieldValuedPoint.ofHom B S hS p a
  have hpnν : pointsMap B S hS D.space D.hom (pn.class B S hS D.space) = p.class B S hS F :=
    FieldValuedPoint.pointsMap_class_ofHom_eq B S hS p a D.hom ha
  have hpn : pn.class B S hS D.space = z :=
    D.pointsMap_hom_injective_of_localRingDimension_eq_zero hF _ z (hpnν ▸ hpzero)
      (hpnν.trans hp)
  obtain ⟨b, hb⟩ : ∃ b : yoneda.obj (p.siteObject B S hS F) ⟶ yoneda.obj c.U,
      b ≫ c.immersion = yonedaEquiv.symm pn.value :=
    exists_lift_fieldPoint_of_isOpenImmersion B S hS c.immersion c.isOpen
      pn c.point (c.mapsTo.trans hpn.symm)
  have : Mono c.immersion := mono_of_presheaf_isOpenImmersion c.isOpen
  refine ⟨b, ?_, pointsMap_injective_of_mono B S hS c.immersion ?_⟩
  · rw [← Category.assoc, hb]
    show (yonedaEquiv.symm (yonedaEquiv a)) ≫ D.hom = _
    rw [Equiv.symm_apply_apply, ha]
  · exact (FieldValuedPoint.pointsMap_class_ofHom_eq B S hS pn b c.immersion hb).trans
      (hpn.trans c.mapsTo.symm)

/-- **The normalization morphism is surjective on local rings at codimension zero.** Let `z`
be a point of codimension zero of the normalization and let `c ⟶ e` be charts at `z` and at
its image compatible with the normalization morphism. The canonical field-valued
representative of the image point lifts to the normalization by the universal property of
Stacks 0BB4, part (4), and then through the open immersion `c`; the resulting morphism from
the spectrum of a residue field splits the chart map, and its own stalk maps are surjective,
whence so is that of the chart map. -/
theorem surjective_stalkMap_of_genericChart (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (z : points B S hS D.space)
    (hz : localRingDimension B S hS z = 0) (c : GenericChart B S hS z)
    (e : GenericChart B S hS (pointsMap B S hS D.space D.hom z)) (j : c.U ⟶ e.U)
    (hcomm : c.immersion ≫ D.hom = yoneda.map j ≫ e.immersion) :
    Function.Surjective
      (((BigFppfOver.toScheme B S hS).map j).stalkMap
        (schemePoint B S hS c.U c.point)).hom := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let t := schemePoint B S hS c.U c.point
  let y := T.map j t
  let r := schemePointRepresentative B S hS e.U y
  let p := FieldValuedPoint.map B S hS _ e.immersion r
  have hr : r.class B S hS (yoneda.obj e.U) =
      pointsMap B S hS _ (yoneda.map j) (c.point.class B S hS (yoneda.obj c.U)) :=
    schemePointRepresentative_class_map B S hS j c.point
  have hp : p.class B S hS F = pointsMap B S hS D.space D.hom z := by
    show pointsMap B S hS _ e.immersion (r.class B S hS (yoneda.obj e.U)) = _
    rw [hr]
    have h := congrArg (fun k => pointsMap B S hS _ k (c.point.class B S hS (yoneda.obj c.U)))
      hcomm
    rw [pointsMap_comp, pointsMap_comp, Function.comp_apply, Function.comp_apply,
      c.mapsTo] at h
    exact h.symm
  obtain ⟨b, hb, hcp⟩ := D.exists_lift_genericChart hF hz c p hp
  have hbp : b ≫ yoneda.map j = yonedaEquiv.symm r.value := by
    have : Mono e.immersion := mono_of_presheaf_isOpenImmersion e.isOpen
    apply (cancel_mono e.immersion).mp
    rw [Category.assoc, ← hcomm, hb]
    exact (yonedaEquiv_symm_naturality_right _ e.immersion r.value).symm
  let k₀ : p.siteObject B S hS F ⟶ c.U := yonedaEquiv b
  let k := T.map k₀
  have hk : k ≫ T.map j = (T.obj e.U).fromSpecResidueField y := by
    have hk₀ : k₀ ≫ j = r.value := by
      have h := congrArg
        (yonedaEquiv (X := p.siteObject B S hS F) (F := yoneda.obj e.U)) hbp
      rw [yonedaEquiv_comp] at h
      exact h.trans ((yonedaEquiv (X := r.siteObject B S hS (yoneda.obj e.U))
        (F := yoneda.obj e.U)).apply_symm_apply r.value)
    show T.map k₀ ≫ T.map j = _
    rw [← Functor.map_comp, hk₀]
    exact B.inclusion.map_preimage _
  let q : T.obj (p.siteObject B S hS F) := IsLocalRing.closedPoint p.carrier
  have hkt : k q = t :=
    schemePoint_eq_of_class_eq B S hS c.U (FieldValuedPoint.ofHom B S hS p b) c.point hcp
  show Function.Surjective ((T.map j).stalkMap t).hom
  rw [← hkt]
  refine Scheme.Hom.surjective_stalkMap_of_comp k (T.map j) q (hkt ▸
    isField_genericChart_localRing_of_isNormal B S hS D.isAlgebraicSpace (D.isNormal hF) z hz c) ?_
  rw [hk]
  exact ((T.obj e.U).fromSpecResidueField y).stalkMap_surjective q

end NormalizationData

end AlgebraicGeometry.Space

end
