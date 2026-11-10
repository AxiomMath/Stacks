module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralBirationalOverNormal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationGenericStalk

/-!
# Normalizations of a birational morphism of algebraic spaces

A decent algebraic space over a scheme `S` whose space of points has finitely many irreducible
components has a normalization. So a birational morphism `f : X ⟶ Y` of such spaces lifts to
the normalizations: the normalization morphism of `X` followed by `f` factors uniquely through
the normalization of `Y`, and the induced morphism `X^ν ⟶ Y^ν` is again birational. This is
**Stacks 0BBG**.

When `f` is in addition integral that induced morphism is an isomorphism, so the normalization
morphism of `Y` factors as `Y^ν ⟶ X ⟶ Y` with first leg the normalization of `X`. This is
**Stacks 0BBH**.

## Main results

* `AlgebraicGeometry.Space.localRingDimension_eq_zero_of_isBirational`: a birational morphism
  of decent algebraic spaces carries points of codimension `0` to points of codimension `0`.
* `AlgebraicGeometry.Space.existsUnique_lift_normalization_of_isBirational`: the commutative
  square of **Stacks 0BBG**, in the form of a unique factorization, for given normalizations.
* `AlgebraicGeometry.Space.isBirational_lift_normalization_of_isBirational`: the morphism
  closing that square is birational, which is the final clause of **Stacks 0BBG**, and
  `AlgebraicGeometry.Space.exists_isBirational_lift_normalization_of_isBirational` asserts
  the square and that clause together, again for given normalizations.
* `AlgebraicGeometry.Space.exists_factorization_normalization_of_isIntegralHom_of_isBirational`
  is **Stacks 0BBH**.

The existence of the normalizations, and with it the whole of **Stacks 0BBG**, is in
`StacksFrontier.AlgebraicGeometry.Spaces.BirationalNormalizationExistence`:
`AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_of_isDecentSpace` shows that a
decent algebraic space with finitely many irreducible components satisfies the equivalent
conditions of Stacks 0BB1, `AlgebraicGeometry.Space.nonempty_normalizationData_of_isDecentSpace`
is then the first clause of **Stacks 0BBG**, that its normalization exists, and
`AlgebraicGeometry.Space.exists_normalizationData_isBirational_lift_of_isBirational` is
**Stacks 0BBG**: the normalizations exist, the square commutes and the induced morphism is
birational, with no normalization assumed.

## Implementation notes

The normalization of an algebraic space is `AlgebraicGeometry.Space.NormalizationData`, a
morphism from an algebraic space whose base change along every surjective étale scheme chart of
the target is the normalization of that chart. Existence of such data is the existence half of
Stacks 07U4, `AlgebraicGeometry.Space.nonempty_normalizationData`, whose hypothesis is
condition (2) of Stacks 0BB1. A decent algebraic space with finitely many irreducible
components meets that condition — this is the route the source takes, through Stacks 0BB9 —
and `AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_of_isDecentSpace`, in
`StacksFrontier.AlgebraicGeometry.Spaces.BirationalNormalizationExistence`, records it: Stacks 0BB9
gives the first clause of its condition (2), that every quasi-compact scheme étale over the space
has finitely many irreducible components, and that is condition (2) of Stacks 0BB1 by the
equivalence with its condition (4). So the first clause of Stacks 0BBG is available, and
`AlgebraicGeometry.Space.exists_normalizationData_isBirational_lift_of_isBirational`, in the
same module, states the lemma with the two normalizations existentially quantified rather than
assumed.

The square, its uniqueness and the birationality are nevertheless proved for an *arbitrary*
choice of the two normalizations, as are the four parts of Stacks 0BB4 in
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization`; that is strictly stronger than
the statement for the constructed ones, and it is what the rest of the development consumes.
Those universally quantified forms keep the `@[stacks 0BBG]` registrations they carry on the base,
each naming the part of the lemma it proves for given normalizations; the whole lemma, with the
existence the source asserts, is registered on
`AlgebraicGeometry.Space.exists_normalizationData_isBirational_lift_of_isBirational`.
Stacks 0BBH is in the same universally quantified form, and identifies its factor `Y^ν ⟶ X`
with the normalization of `X` by exhibiting an isomorphism `Y^ν ≅ X^ν` over `X`, which is what
being a normalization means once the data is quantified over: normalizations are unique up to
unique isomorphism over the space.

The factorization is part (4) of Stacks 0BB4,
`AlgebraicGeometry.Space.NormalizationData.existsUnique_lift_hom`, applied to the composite
`X^ν ⟶ X ⟶ Y`. It asks for two things about that composite. Normality of its source is part (1)
of Stacks 0BB4. Preservation of codimension-zero points splits along the composite: the
normalization morphism of `X` bijects codimension-zero points by part (3) of Stacks 0BB4, and
`f` preserves them because on a decent algebraic space a point has codimension `0` exactly when
it is a generic point of an irreducible component, which is Stacks 0ABV, and birationality
bijects those generic points.

The birationality of the induced morphism `X^ν ⟶ Y^ν` is proved at the generic points. The
bijection there is the bijection on codimension-zero points of part (3) of Stacks 0BB4 on
both normalizations, composed with the bijection supplied by `f`, together with the fact
that a point of a normalization over a point of codimension zero has codimension zero. On
local rings the normalization morphism of `X` is *surjective* at a generic point — it need
not be injective, since it kills nilpotents — while `f` is an isomorphism there; so the
composite `X^ν ⟶ X ⟶ Y` is surjective on local rings at a generic point, hence so is
`X^ν ⟶ Y^ν` followed by the normalization morphism of `Y`, hence so is `X^ν ⟶ Y^ν`. That
last map is injective because its source is the local ring of the normal algebraic space
`Y^ν` at a point of codimension zero, which is a field. These inputs are
`AlgebraicGeometry.Space.NormalizationData.surjective_stalkMap_of_genericChart` and
`AlgebraicGeometry.Space.isField_genericChart_localRing_of_isNormal`.

For Stacks 0BBH the induced morphism `X^ν ⟶ Y^ν` is integral by part (2) of Stacks 081Z,
since its composite with the normalization morphism of `Y` is integral and that morphism,
being integral, is separated; it is then an isomorphism by Stacks 0B4E.

Birationality is `AlgebraicGeometry.Space.IsBirational`, which is parameterised by decency of
the source and the target, as the source statement is; the same decency is what Stacks 0ABV
needs to identify the codimension-zero points with the generic points of the irreducible
components.

## References

* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 081Z](https://stacks.math.columbia.edu/tag/081Z)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 0ACV](https://stacks.math.columbia.edu/tag/0ACV)
* [Stacks Project, Tag 0B4E](https://stacks.math.columbia.edu/tag/0B4E)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
* [Stacks Project, Tag 0BB9](https://stacks.math.columbia.edu/tag/0BB9)
* [Stacks Project, Tag 0BBG](https://stacks.math.columbia.edu/tag/0BBG)
* [Stacks Project, Tag 0BBH](https://stacks.math.columbia.edu/tag/0BBH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A birational morphism of decent algebraic spaces preserves codimension zero.** On a decent
algebraic space a point has codimension `0` exactly when it is a generic point of an irreducible
component of the point space, which is Stacks 0ABV, and a birational morphism bijects those
generic points. -/
theorem localRingDimension_eq_zero_of_isBirational (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsBirational B S hS hX hY hXdec hYdec hfiniteX hfiniteY f)
    (x : points B S hS X) (hx : localRingDimension B S hS x = 0) :
    localRingDimension B S hS (pointsMap B S hS X f x) = 0 :=
  (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hY hYdec _).1
    ((hf.bijOn B S hS hX hY hXdec hYdec hfiniteX hfiniteY).mapsTo
      ((mem_genericPoints_iff_localRingDimension_eq_zero B S hS hX hXdec x).2 hx))

/-- **The commutative square of Stacks 0BBG, for given normalizations.** Let `f : X ⟶ Y` be a
birational morphism of decent algebraic spaces over `S` with finitely many irreducible
components, and let `X^ν ⟶ X` and `Y^ν ⟶ Y` be normalizations. Then `X^ν ⟶ X ⟶ Y` factors
through `Y^ν ⟶ Y` by a unique morphism `X^ν ⟶ Y^ν`, so that the square it closes commutes.

The factorization is the universal property of the normalization of `Y`, part (4) of
Stacks 0BB4. Its two hypotheses on the composite `X^ν ⟶ X ⟶ Y` are normality of `X^ν`, part (1)
of Stacks 0BB4, and preservation of codimension-zero points, which holds for `X^ν ⟶ X` by
part (3) of Stacks 0BB4 and for `f` by
`AlgebraicGeometry.Space.localRingDimension_eq_zero_of_isBirational`.

The normalizations are hypotheses here, whereas the source asserts their existence; that
existence is `AlgebraicGeometry.Space.nonempty_normalizationData_of_isDecentSpace`, and the
whole lemma, which quantifies over no normalization data at all, is
`AlgebraicGeometry.Space.exists_normalizationData_isBirational_lift_of_isBirational`. The
statement here is the stronger one for the
square — it holds for *every* choice of the two normalizations, not just the ones the
existence theorem produces — and it is what the rest of the development consumes. -/
@[stacks 0BBG "the commutative square, as a unique factorization through the target normalization"]
theorem existsUnique_lift_normalization_of_isBirational (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    (DX : NormalizationData B S hS X) (DY : NormalizationData B S hS Y) {f : X ⟶ Y}
    (hf : IsBirational B S hS hX hY hXdec hYdec hfiniteX hfiniteY f) :
    ∃! g : DX.space ⟶ DY.space, g ≫ DY.hom = DX.hom ≫ f :=
  DY.existsUnique_lift_hom hY DX.isAlgebraicSpace (DX.hasEtaleLocalProperty_isNormal hX)
    (DX.hom ≫ f) fun z hz => by
      rw [pointsMap_comp_apply]
      exact localRingDimension_eq_zero_of_isBirational B S hS hX hY
        hfiniteX hfiniteY hXdec hYdec hf _
        ((DX.bijOn_codimensionZeroPoints_hom hX).mapsTo hz)

/-! ### Refining a chart at a point to one compatible with a chart at its image -/

/-- Open immersions of schemes pulled back to the site are stable under base change, because
open immersions of schemes are. -/
private local instance inverseImage_isOpenImmersion_isStableUnderBaseChange :
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange where
  of_isPullback h hf := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u})
    (h.map (BigFppfOver.toScheme B S hS)) hf

/-- **A chart at a point refines to one compatible with a prescribed chart at the image
point.** Pulling the given chart at the source point back along the open immersion of the
given chart at the image point produces an open subspace of it through which the composite
factors, and the chosen field-valued point lifts to that subspace because its image already
lies in the target chart. -/
private theorem exists_refine_genericChart_compatible
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (x : points B S hS F)
    (c : GenericChart B S hS x) {y : points B S hS G} (d : GenericChart B S hS y)
    (hfx : pointsMap B S hS F f x = y) :
    ∃ (c' : GenericChart B S hS x) (a : c'.U ⟶ c.U) (b : c'.U ⟶ d.U),
      c'.immersion = yoneda.map a ≫ c.immersion ∧
      c'.immersion ≫ f = yoneda.map b ≫ d.immersion ∧
      (BigFppfOver.toScheme B S hS).map a (schemePoint B S hS c'.U c'.point) =
        schemePoint B S hS c.U c.point ∧
      (BigFppfOver.toScheme B S hS).map b (schemePoint B S hS c'.U c'.point) =
        schemePoint B S hS d.U d.point := by
  let p := FieldValuedPoint.map B S hS _ (c.immersion ≫ f) c.point
  have heq : (FieldValuedPoint.map B S hS _ d.immersion d.point).class B S hS G =
      p.class B S hS G := by
    change pointsMap B S hS _ d.immersion (d.point.class B S hS (yoneda.obj d.U)) =
      pointsMap B S hS _ (c.immersion ≫ f) (c.point.class B S hS (yoneda.obj c.U))
    rw [pointsMap_comp_apply, c.mapsTo, d.mapsTo, hfx]
  obtain ⟨s, hs⟩ := exists_lift_fieldPoint_of_isOpenImmersion B S hS d.immersion d.isOpen
    p d.point heq
  obtain ⟨W, a, b', hpb⟩ := d.isOpen.1 (c.immersion ≫ f)
  let b : W ⟶ d.U := yoneda.preimage b'
  have hb : yoneda.map b = b' := yoneda.map_preimage b'
  let ℓ := hpb.lift s (yonedaEquiv.symm c.point.value) (by
    rw [hs]
    exact (yonedaEquiv_symm_naturality_right _ (c.immersion ≫ f) c.point.value).symm)
  let cp := FieldValuedPoint.ofHom B S hS c.point ℓ
  have hca : pointsMap B S hS _ (yoneda.map a) (cp.class B S hS (yoneda.obj W)) =
      c.point.class B S hS (yoneda.obj c.U) :=
    FieldValuedPoint.pointsMap_class_ofHom_eq B S hS c.point ℓ (yoneda.map a)
      (hpb.lift_snd _ _ _)
  have hcb : pointsMap B S hS _ b' (cp.class B S hS (yoneda.obj W)) =
      d.point.class B S hS (yoneda.obj d.U) := by
    have : Mono d.immersion := mono_of_presheaf_isOpenImmersion d.isOpen
    apply pointsMap_injective_of_mono B S hS d.immersion
    have h := congrArg (fun k => pointsMap B S hS _ k (cp.class B S hS (yoneda.obj W))) hpb.w
    rw [pointsMap_comp_apply, pointsMap_comp_apply, hca] at h
    exact h.trans heq.symm
  have ha : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map a) := d.isOpen.2 _ _ _ hpb
  have ha' : IsOpenImmersion B S hS (yoneda.map a) :=
    (MorphismProperty.relative_map_iff (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS))).2 ha
  have hc' : IsOpenImmersion B S hS (yoneda.map a ≫ c.immersion) :=
    MorphismProperty.comp_mem _ _ _ ha' c.isOpen
  let c' : GenericChart B S hS x :=
    ⟨W, yoneda.map a ≫ c.immersion, hc', cp, by
      rw [pointsMap_comp_apply, hca, c.mapsTo]⟩
  refine ⟨c', a, b, rfl, ?_, ?_, ?_⟩
  · change (yoneda.map a ≫ c.immersion) ≫ f = yoneda.map b ≫ d.immersion
    rw [Category.assoc, hb, hpb.w]
  · exact (schemePoint_map_yoneda B S hS a cp).symm.trans
      (schemePoint_eq_of_class_eq B S hS _ _ _ hca)
  · exact (schemePoint_map_yoneda B S hS b cp).symm.trans
      (schemePoint_eq_of_class_eq B S hS _ _ _ (hb ▸ hcb))

/-! ### Birationality of the induced morphism of normalizations -/

private theorem pointsMap_lift_normalization {DX : NormalizationData B S hS X}
    {DY : NormalizationData B S hS Y} {f : X ⟶ Y} {g : DX.space ⟶ DY.space}
    (hg : g ≫ DY.hom = DX.hom ≫ f) (z : points B S hS DX.space) :
    pointsMap B S hS DY.space DY.hom (pointsMap B S hS DX.space g z) =
      pointsMap B S hS X f (pointsMap B S hS DX.space DX.hom z) := by
  simpa only [pointsMap_comp, Function.comp_apply] using
    congrArg (fun k => pointsMap B S hS DX.space k z) hg

/-- A point of a normalization is a generic point exactly when it has codimension `0`. -/
private theorem mem_genericPoints_normalization_iff (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (D : NormalizationData B S hS X) (z : points B S hS D.space) :
    z ∈ genericPoints (points B S hS D.space) ↔ localRingDimension B S hS z = 0 :=
  mem_genericPoints_iff_localRingDimension_eq_zero B S hS D.isAlgebraicSpace
    (D.isDecentSpace hX hXdec) z

/-- The distinguished chart at a generic point of a decent algebraic space. -/
private noncomputable def decentGenericChart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hdec : IsDecentSpace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    (x : points B S hS F) (hx : x ∈ genericPoints (points B S hS F)) : GenericChart B S hS x :=
  schematicGenericChart B S hS hF
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hF hdec) hfinite x hx

/-- The morphism of normalizations closing the square over a birational morphism maps generic
points to generic points. -/
theorem mapsTo_genericPoints_lift_normalization (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (DX : NormalizationData B S hS X) (DY : NormalizationData B S hS Y) {f : X ⟶ Y}
    (hf : IsBirational B S hS hX hY hXdec hYdec hfiniteX hfiniteY f)
    (g : DX.space ⟶ DY.space) (hg : g ≫ DY.hom = DX.hom ≫ f) :
    Set.MapsTo (pointsMap B S hS DX.space g) (genericPoints (points B S hS DX.space))
      (genericPoints (points B S hS DY.space)) := by
  intro z hz
  refine (mem_genericPoints_normalization_iff B S hS hY hYdec DY _).2
    (DY.localRingDimension_eq_zero_of_hom hY _ ?_)
  rw [pointsMap_lift_normalization B S hS hg]
  exact (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hY hYdec _).1
    ((hf.bijOn B S hS hX hY _ _ hfiniteX hfiniteY).mapsTo
      ((DX.bijOn_genericPoints_hom hX hXdec).mapsTo hz))

/-- The morphism of normalizations closing the square over a birational morphism bijects
generic points. -/
theorem bijOn_genericPoints_lift_normalization (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (DX : NormalizationData B S hS X) (DY : NormalizationData B S hS Y) {f : X ⟶ Y}
    (hf : IsBirational B S hS hX hY hXdec hYdec hfiniteX hfiniteY f)
    (g : DX.space ⟶ DY.space) (hg : g ≫ DY.hom = DX.hom ≫ f) :
    Set.BijOn (pointsMap B S hS DX.space g) (genericPoints (points B S hS DX.space))
      (genericPoints (points B S hS DY.space)) := by
  have hνX := DX.bijOn_genericPoints_hom hX hXdec
  have hνY := DY.bijOn_genericPoints_hom hY hYdec
  have hfb := hf.bijOn B S hS hX hY _ _ hfiniteX hfiniteY
  have hcomm := pointsMap_lift_normalization B S hS hg
  have hmap := mapsTo_genericPoints_lift_normalization B S hS hX hY hXdec hYdec hfiniteX
    hfiniteY DX DY hf g hg
  refine ⟨hmap, ?_, ?_⟩
  · intro z hz w hw heq
    refine hνX.injOn hz hw (hfb.injOn (hνX.mapsTo hz) (hνX.mapsTo hw) ?_)
    rw [← hcomm, ← hcomm, heq]
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hfb.surjOn (hνY.mapsTo hy)
    obtain ⟨z, hz, hzx⟩ := hνX.surjOn hx
    refine ⟨z, hz, hνY.injOn (hmap hz) hy ?_⟩
    rw [hcomm, hzx, hxy]

/-- A morphism of schemes `κ : P ⟶ M` induces an isomorphism on the stalks at `t` when the stalk
of `M` at `κ t` is a field and `κ` fits in a square `φ ≫ ψ = κ ≫ μ` with `φ` surjective on the
stalks at `t` and `ψ` an isomorphism on the stalks at `φ t`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_of_comp_eq_of_isField
    {P Q R M : Scheme.{u}} (φ : P ⟶ Q) (ψ : Q ⟶ R) (κ : P ⟶ M) (μ : M ⟶ R)
    (hsq : φ ≫ ψ = κ ≫ μ) {t : P} (hφ : Function.Surjective (φ.stalkMap t).hom)
    (hψ : IsIso (ψ.stalkMap (φ t))) (hfield : IsField (M.presheaf.stalk (κ t))) :
    IsIso (κ.stalkMap t) := by
  have h : Function.Surjective ((φ ≫ ψ).stalkMap t).hom := by
    rw [Scheme.Hom.stalkMap_comp]
    exact hφ.comp (ConcreteCategory.bijective_of_isIso (ψ.stalkMap (φ t))).2
  rw [hsq, Scheme.Hom.stalkMap_comp] at h
  let := hfield.toField
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(κ.stalkMap t).hom.injective, Function.Surjective.of_comp h⟩

/-- For any pair of generic charts compatible with a morphism through a chart morphism `k`, the
map of generic local rings induced by the morphism is an isomorphism exactly when the stalk map
of `k` at the chart point is. -/
theorem isIso_genericLocalRingMap_iff_isIso_stalkMap
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hdenseF : HasDenseRepresentableOpenSubspace B S hS F)
    (hdenseG : HasDenseRepresentableOpenSubspace B S hS G)
    (hfiniteF : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    (hfiniteG : (letI := pointTopology B S hS G
      (irreducibleComponents (points B S hS G)).Finite))
    (f : F ⟶ G) (x : points B S hS F) (hx : x ∈ genericPoints (points B S hS F))
    (hy : pointsMap B S hS F f x ∈ genericPoints (points B S hS G))
    (c : GenericChart B S hS x) (d : GenericChart B S hS (pointsMap B S hS F f x))
    (k : c.U ⟶ d.U) (hcomm : c.immersion ≫ f = yoneda.map k ≫ d.immersion)
    (hpoint : (BigFppfOver.toScheme B S hS).map k (schemePoint B S hS c.U c.point) =
      schemePoint B S hS d.U d.point) :
    IsIso (genericLocalRingMap B S hS hF hG hdenseF hdenseG hfiniteF hfiniteG f x hx hy) ↔
      IsIso (((BigFppfOver.toScheme B S hS).map k).stalkMap
        (schemePoint B S hS c.U c.point)) := by
  rw [show genericLocalRingMap B S hS hF hG hdenseF hdenseG hfiniteF hfiniteG f x hx hy = _ from
    (exists_genericLocalRingMap B S hS hF hG hdenseF hdenseG hfiniteF hfiniteG f x hx
      hy).choose_spec c d k hcomm hpoint]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]

/-- At a generic point of `X^ν`, the morphism of normalizations closing the square over a
birational morphism induces an isomorphism of generic local rings. -/
theorem isIso_genericLocalRingMap_lift_normalization (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (DX : NormalizationData B S hS X) (DY : NormalizationData B S hS Y) {f : X ⟶ Y}
    (hf : IsBirational B S hS hX hY hXdec hYdec hfiniteX hfiniteY f)
    (g : DX.space ⟶ DY.space) (hg : g ≫ DY.hom = DX.hom ≫ f)
    (z : points B S hS DX.space) (hz : z ∈ genericPoints (points B S hS DX.space))
    (hw : pointsMap B S hS DX.space g z ∈ genericPoints (points B S hS DY.space)) :
    IsIso (genericLocalRingMap B S hS DX.isAlgebraicSpace DY.isAlgebraicSpace
      (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS DX.isAlgebraicSpace
        (DX.isDecentSpace hX hXdec))
      (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS DY.isAlgebraicSpace
        (DY.isDecentSpace hY hYdec))
      (DX.finite_irreducibleComponents hX hXdec hfiniteX)
      (DY.finite_irreducibleComponents hY hYdec hfiniteY) g z hz hw) := by
  let T := BigFppfOver.toScheme B S hS
  let x := pointsMap B S hS DX.space DX.hom z
  have hx : x ∈ genericPoints (points B S hS X) := (DX.bijOn_genericPoints_hom hX hXdec).mapsTo hz
  have hy : pointsMap B S hS X f x ∈ genericPoints (points B S hS Y) :=
    (hf.bijOn B S hS hX hY _ _ hfiniteX hfiniteY).mapsTo hx
  let cY := decentGenericChart B S hS hY hYdec hfiniteY _ hy
  obtain ⟨cX, -, gf, -, hgf, -, hgfp⟩ := exists_refine_genericChart_compatible B S hS f x
    (decentGenericChart B S hS hX hXdec hfiniteX x hx) cY rfl
  obtain ⟨cNY, -, nY, -, hnY, -, hnYp⟩ := exists_refine_genericChart_compatible B S hS DY.hom _
    (decentGenericChart B S hS DY.isAlgebraicSpace (DY.isDecentSpace hY hYdec)
      (DY.finite_irreducibleComponents hY hYdec hfiniteY) _ hw) cY
    (pointsMap_lift_normalization B S hS hg z)
  obtain ⟨cNX₁, -, nX₁, -, hnX₁, -, hnX₁p⟩ := exists_refine_genericChart_compatible B S hS
    DX.hom z (decentGenericChart B S hS DX.isAlgebraicSpace (DX.isDecentSpace hX hXdec)
      (DX.finite_irreducibleComponents hX hXdec hfiniteX) z hz) cX rfl
  obtain ⟨cNX, a, k, ha, hk, hap, hkp⟩ :=
    exists_refine_genericChart_compatible B S hS g z cNX₁ cNY rfl
  let nX := a ≫ nX₁
  have hnX : cNX.immersion ≫ DX.hom = yoneda.map nX ≫ cX.immersion := by
    rw [ha, Category.assoc, hnX₁, ← Category.assoc, ← Functor.map_comp]
  have hnXp : T.map nX (schemePoint B S hS cNX.U cNX.point) =
      schemePoint B S hS cX.U cX.point := by
    change T.map (a ≫ nX₁) _ = _
    rw [Functor.map_comp]
    change T.map nX₁ (T.map a _) = _
    rw [hap, hnX₁p]
  have hsq : nX ≫ gf = k ≫ nY := by
    have : Mono cY.immersion := mono_of_presheaf_isOpenImmersion cY.isOpen
    refine yoneda.map_injective ((cancel_mono cY.immersion).mp ?_)
    simp only [Functor.map_comp, Category.assoc]
    rw [← hgf, ← Category.assoc, ← hnX, Category.assoc, ← hg, ← Category.assoc, hk,
      Category.assoc, hnY]
  refine (isIso_genericLocalRingMap_iff_isIso_stalkMap B S hS _ _ _ _ _ _ g z hz hw cNX cNY k
    hk hkp).2 (Scheme.Hom.isIso_stalkMap_of_comp_eq_of_isField (T.map nX) (T.map gf) (T.map k)
      (T.map nY) (by simpa only [Functor.map_comp] using congrArg T.map hsq)
      (DX.surjective_stalkMap_of_genericChart hX z ?_ cNX cX nX hnX) ?_ ?_)
  · exact (mem_genericPoints_normalization_iff B S hS hX hXdec DX z).1 hz
  · rw [hnXp]
    exact (isIso_genericLocalRingMap_iff_isIso_stalkMap B S hS hX hY _ _ hfiniteX hfiniteY f x
      hx hy cX cY gf hgf hgfp).1
        (hf.isIso_genericLocalRingMap B S hS hX hY _ _ hfiniteX hfiniteY x hx)
  · rw [hkp]
    exact isField_genericChart_localRing_of_isNormal B S hS DY.isAlgebraicSpace
      (DY.isNormal hY) _ ((mem_genericPoints_normalization_iff B S hS hY hYdec DY _).1 hw) cNY

/-- **Birationality of the induced morphism, for given normalizations.** Let `f : X ⟶ Y` be a
birational morphism of decent algebraic spaces over `S` with finitely many irreducible
components, and
let `X^ν ⟶ X` and `Y^ν ⟶ Y` be normalizations. Then any morphism `X^ν ⟶ Y^ν` closing the
square over `f` is birational.

The two normalizations are again decent with finitely many irreducible components, and their
normalization morphisms biject generic points, so the induced morphism does too. At a generic
point `z` of `X^ν` the local-ring map is computed on charts: the chart map of `X^ν ⟶ X` is
surjective on local rings at `z` by
`AlgebraicGeometry.Space.NormalizationData.surjective_stalkMap_of_genericChart`, and the
chart map of `f` is an isomorphism there by birationality, so the chart map of `X^ν ⟶ Y^ν`
followed by that of `Y^ν ⟶ Y` is surjective, whence the chart map of `X^ν ⟶ Y^ν` is
surjective. It is injective because its source — the local ring of the normal space `Y^ν` at
a point of codimension zero — is a field.

The normalizations are hypotheses here, as at
`AlgebraicGeometry.Space.existsUnique_lift_normalization_of_isBirational`. -/
@[stacks 0BBG "birationality of the induced morphism of normalizations"]
theorem isBirational_lift_normalization_of_isBirational (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (DX : NormalizationData B S hS X) (DY : NormalizationData B S hS Y) {f : X ⟶ Y}
    (hf : IsBirational B S hS hX hY hXdec hYdec hfiniteX hfiniteY f)
    (g : DX.space ⟶ DY.space) (hg : g ≫ DY.hom = DX.hom ≫ f) :
    IsBirational B S hS DX.isAlgebraicSpace DY.isAlgebraicSpace
      (DX.isDecentSpace hX hXdec) (DY.isDecentSpace hY hYdec)
      (DX.finite_irreducibleComponents hX hXdec hfiniteX)
      (DY.finite_irreducibleComponents hY hYdec hfiniteY) g :=
  ⟨bijOn_genericPoints_lift_normalization B S hS hX hY hXdec hYdec hfiniteX hfiniteY DX DY hf g
    hg, fun z hz => isIso_genericLocalRingMap_lift_normalization B S hS hX hY hXdec hYdec
      hfiniteX hfiniteY DX DY hf g hg z hz _⟩

/-- **The square and the birationality together, for given normalizations.** Let `f : X ⟶ Y`
be a birational morphism of decent algebraic spaces over `S` with finitely many irreducible
components, and let `X^ν ⟶ X` and `Y^ν ⟶ Y` be normalizations. Then `X^ν ⟶ X ⟶ Y` factors
through `Y^ν ⟶ Y`, and the factoring morphism `X^ν ⟶ Y^ν` is birational.

The factorization is
`AlgebraicGeometry.Space.existsUnique_lift_normalization_of_isBirational` and its
birationality is
`AlgebraicGeometry.Space.isBirational_lift_normalization_of_isBirational`.

The normalizations are hypotheses here; the whole lemma, with their existence, is
`AlgebraicGeometry.Space.exists_normalizationData_isBirational_lift_of_isBirational`. -/
@[stacks 0BBG "the commutative square together with the birationality of the induced \
morphism of normalizations"]
theorem exists_isBirational_lift_normalization_of_isBirational
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (DX : NormalizationData B S hS X) (DY : NormalizationData B S hS Y) {f : X ⟶ Y}
    (hf : IsBirational B S hS hX hY hXdec hYdec hfiniteX hfiniteY f) :
    ∃ g : DX.space ⟶ DY.space, g ≫ DY.hom = DX.hom ≫ f ∧
      IsBirational B S hS DX.isAlgebraicSpace DY.isAlgebraicSpace
        (DX.isDecentSpace hX hXdec) (DY.isDecentSpace hY hYdec)
        (DX.finite_irreducibleComponents hX hXdec hfiniteX)
        (DY.finite_irreducibleComponents hY hYdec hfiniteY) g :=
  (existsUnique_lift_normalization_of_isBirational B S hS hX hY hfiniteX hfiniteY hXdec hYdec
    DX DY hf).exists.imp fun g hg => ⟨hg, isBirational_lift_normalization_of_isBirational B S hS
      hX hY hXdec hYdec hfiniteX hfiniteY DX DY hf g hg⟩

/-! ### Integral birational morphisms -/

/-- **Stacks 0BBH.** Let `f : X ⟶ Y` be an integral birational morphism of decent algebraic
spaces over `S` with finitely many irreducible components, and let `X^ν ⟶ X` and `Y^ν ⟶ Y` be
normalizations. Then the normalization morphism of `Y` factors as `Y^ν ⟶ X ⟶ Y`, and the
first leg `Y^ν ⟶ X` is the normalization of `X`: it is the normalization morphism `X^ν ⟶ X`
precomposed with an isomorphism `Y^ν ≅ X^ν` over `X`.

The induced morphism `X^ν ⟶ Y^ν` of Stacks 0BBG is integral by Stacks 081Z, part (2): its
composite with the normalization morphism of `Y` is the composite of the normalization
morphism of `X` with `f`, both integral, and the normalization morphism of `Y` is integral
hence separated. It is birational by Stacks 0BBG, its source is reduced — being normal — and
its target is normal, both normalizations are decent with finitely many irreducible
components, so Stacks 0B4E makes it an isomorphism. Its inverse is the asserted
factorization. -/
@[stacks 0BBH]
theorem exists_factorization_normalization_of_isIntegralHom_of_isBirational
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (DX : NormalizationData B S hS X) (DY : NormalizationData B S hS Y) {f : X ⟶ Y}
    (hfint : IsIntegralHom B S hS f)
    (hf : IsBirational B S hS hX hY hXdec hYdec hfiniteX hfiniteY f) :
    ∃ (h : DY.space ⟶ X) (e : DY.space ≅ DX.space),
      h ≫ f = DY.hom ∧ h = e.hom ≫ DX.hom := by
  obtain ⟨g, hg, hgbir⟩ := exists_isBirational_lift_normalization_of_isBirational
    B S hS hX hY hXdec hYdec hfiniteX hfiniteY DX DY hf
  have hgint : IsIntegralHom B S hS g := by
    refine isIntegralHom_of_comp_of_isSeparated B S hS g DY.hom ?_
      (isSeparated_of_isIntegralHom B S hS DY.hom DY.isAlgebraicSpace hY
        (DY.isIntegralHom_hom hY))
    rw [hg]
    exact isIntegralHom_comp B S hS (DX.isIntegralHom_hom hX) hfint
  have hiso : IsIso g :=
    isIso_of_isIntegralHom_of_isBirational_of_isNormal_of_isReduced B S hS
      DX.isAlgebraicSpace DY.isAlgebraicSpace (DX.isDecentSpace hX hXdec)
      (DY.isDecentSpace hY hYdec) (DX.finite_irreducibleComponents hX hXdec hfiniteX)
      (DY.finite_irreducibleComponents hY hYdec hfiniteY) g hgint hgbir (DY.isNormal hY)
      (hasEtaleLocalProperty_isReduced_of_isNormal B S hS DX.space (DX.isNormal hX))
  refine ⟨inv g ≫ DX.hom, (asIso g).symm, ?_, rfl⟩
  rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc]

end AlgebraicGeometry.Space

end
