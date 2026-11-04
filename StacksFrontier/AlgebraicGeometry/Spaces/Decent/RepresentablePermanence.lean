module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphicFieldRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Monomorphic field-valued representatives pass to the source of a representable morphism

Stacks 0ABT says that decency and reasonableness pass from the target of a representable
morphism of algebraic spaces to its source. This file proves the part of that statement which
concerns monomorphic field-valued representatives: if every point of `Y` satisfies condition
(4) of Stacks 03JU — it is the class of a field-valued point whose presenting morphism is a
monomorphism — then so does every point of `X`, for any representable `f : X ⟶ Y`.

The argument is the one Stacks gives for property `(β)` of Stacks 03JX. Let `x` be a point of
`X` and let `Spec k ⟶ Y` be a monomorphic representative of its image. Representability of
`f` makes the fibre product `X ×_Y Spec k` an object of the site, the projection to `X` is a
monomorphism because monomorphisms are stable under base change, and `x` lifts to a point of
that fibre product by Stacks 03H4. The residue field at that lifted point presents it by a
monomorphism of schemes, so the composite is a monomorphic representative of `x`.

## Main results

* `AlgebraicGeometry.Space.hasMonomorphicFieldRepresentative_yoneda`: every point of a
  presheaf represented by an object of the site satisfies condition (4) of Stacks 03JU.
* `AlgebraicGeometry.Space.hasMonomorphicFieldRepresentative_of_relativelyRepresentable`:
  condition (4) of Stacks 03JU at every point passes to the source of a representable
  morphism.
* `AlgebraicGeometry.Space.hasMonomorphicFieldRepresentative_of_isDecentSpace` is the form
  the previous statement takes when the target is decent.
* `AlgebraicGeometry.Space.hasFiniteRelationFibersAtEveryPoint_of_relativelyRepresentable`
  reads the same conclusion as property `(β)` of Stacks 03JX.
* `AlgebraicGeometry.Space.hasFiniteRelationFibersAtEveryPoint_of_relativelyRepresentable_of_target`
  is the case `(β)` of Stacks 03KF: the same statement with property `(β)` of the target as
  hypothesis in place of condition (4) of Stacks 03JU.

## Implementation notes

The conclusion is condition (4) of Stacks 03JU — equivalently, through Stacks 03JU,
property `(β)` of Stacks 03JX — and not decency. Decency is
`AlgebraicGeometry.Space.IsDecentSpace`, which spells Stacks 03I8 with condition (4) of
Stacks 03JV — a monomorphism from a field spectrum which is moreover *quasi-compact* in the
sense of Stacks 03HE — and the only consequence of it available here is
`AlgebraicGeometry.Space.IsDecentSpace.hasMonomorphicFieldRepresentative`, which forgets the
quasi-compactness. Recovering it for the composite built below needs quasi-compactness of the
morphism `Spec κ(z) ⟶ Z` of Stacks 03HE from quasi-compactness of the underlying morphism of
schemes, which is the comparison of Stacks 03HG; that comparison is
`AlgebraicGeometry.Space.quasiCompact_schemeMap_isQuasiCompact`, and with it decency itself is
`AlgebraicGeometry.Space.isDecentSpace_of_relativelyRepresentable` in
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PropertyGammaPermanence.lean`, which carries both
Stacks 0ABT for the decent case and Stacks 03KF for property `(γ)`. The statements below are
therefore the weaker, condition-(4)-of-03JU forms, kept because they need no quasi-compactness
and so apply where it is not known. What remains unavailable is the equivalence of conditions
(1) and (4) of Stacks 03JV, which would let decency be read off condition `(γ)` instead.

Neither presheaf is assumed to be an algebraic space: only representability of the morphism
is used, together with the identification of the points of a represented presheaf with the
points of the representing scheme.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KF](https://stacks.math.columbia.edu/tag/03KF)
* [Stacks Project, Tag 0ABT](https://stacks.math.columbia.edu/tag/0ABT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03JU, condition (4), for a scheme.** Every point of the presheaf represented by
an object of the big fppf site over `S` is the class of a field-valued point whose presenting
morphism is a monomorphism: the residue field at the corresponding point of the representing
scheme does it. -/
theorem hasMonomorphicFieldRepresentative_yoneda (T : BigFppfOver B S hS)
    (z : points B S hS (yoneda.obj T)) :
    HasMonomorphicFieldRepresentative B S hS (yoneda.obj T) z :=
  ⟨schemePointRepresentative B S hS T (pointsToScheme B S hS T z),
    class_schemePointRepresentative_pointsToScheme B S hS T z,
    mono_fieldMorphism_schemePointRepresentative B S hS T _⟩

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0ABT, the decent case in the form of condition (4) of Stacks 03JU.** Let
`f : X ⟶ Y` be a representable morphism of presheaves on the big fppf site over `S`. If every
point of `Y` is the class of a field-valued point presenting it by a monomorphism, then so is
every point of `X`. -/
@[stacks 0ABT "decent, as condition (4) of Stacks 03JU at every point"]
theorem hasMonomorphicFieldRepresentative_of_relativelyRepresentable (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f)
    (hY : ∀ y : points B S hS Y, HasMonomorphicFieldRepresentative B S hS Y y)
    (x : points B S hS X) :
    HasMonomorphicFieldRepresentative B S hS X x := by
  obtain ⟨p, hpy, hpmono⟩ := hY (pointsMap B S hS X f x)
  -- A monomorphic representative `Spec k ⟶ Y` of the image of `x`.
  have hcomm : pointsMap B S hS X f x =
      pointsMap B S hS (yoneda.obj (FieldValuedPoint.siteObject B S hS Y p))
        (fieldMorphism B S hS Y p)
        ((FieldValuedPoint.tautologicalPoint B S hS Y p).class B S hS
          (yoneda.obj (FieldValuedPoint.siteObject B S hS Y p))) := by
    rw [pointsMap_fieldMorphism_tautologicalPoint, hpy]
  -- The fibre product `X ×_Y Spec k` is an object of the site and `x` lifts to a point of it.
  obtain ⟨z, hz, -⟩ :=
    exists_points_of_isPullback B S hS (hf.isPullback (fieldMorphism B S hS Y p)) x _ hcomm
  -- Its projection to `X` is a monomorphism, being a base change of a monomorphism.
  have hqmono : Mono (hf.fst (fieldMorphism B S hS Y p)) :=
    (hf.isPullback (fieldMorphism B S hS Y p)).mono_fst_of_mono hpmono
  -- The residue field at the lifted point presents it by a monomorphism.
  obtain ⟨r, hrz, hrmono⟩ :=
    hasMonomorphicFieldRepresentative_yoneda B S hS (hf.pullback (fieldMorphism B S hS Y p)) z
  refine ⟨FieldValuedPoint.map B S hS _ (hf.fst (fieldMorphism B S hS Y p)) r, ?_, ?_⟩
  · rw [← pointsMap_class, hrz]
    exact hz
  · rw [fieldMorphism_map]
    exact mono_comp' hrmono hqmono

/-- The form that
`AlgebraicGeometry.Space.hasMonomorphicFieldRepresentative_of_relativelyRepresentable` takes
when the target is decent: every point of the source of a representable morphism into a
decent algebraic space satisfies condition (4) of Stacks 03JU. -/
theorem hasMonomorphicFieldRepresentative_of_isDecentSpace (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) (hY : IsDecentSpace B S hS Y)
    (x : points B S hS X) :
    HasMonomorphicFieldRepresentative B S hS X x :=
  hasMonomorphicFieldRepresentative_of_relativelyRepresentable B S hS f hf
    (fun y => IsDecentSpace.hasMonomorphicFieldRepresentative B S hS Y hY y) x

/-- **Stacks 0ABT, the decent case as property `(β)` of Stacks 03JX.** The source of a
representable morphism into a presheaf all of whose points have a monomorphic field-valued
representative has property `(β)`: every point of it has a finite relation fibre in some
étale chart.

This is the reading of
`AlgebraicGeometry.Space.hasMonomorphicFieldRepresentative_of_relativelyRepresentable`
through the equivalences of Stacks 03JU, which need the source to be an algebraic space. -/
@[stacks 0ABT "decent, as property (β) of Stacks 03JX"]
theorem hasFiniteRelationFibersAtEveryPoint_of_relativelyRepresentable
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f)
    (hY : ∀ y : points B S hS Y, HasMonomorphicFieldRepresentative B S hS Y y) :
    HasFiniteRelationFibersAtEveryPoint B S hS X := fun x =>
  (hasFiniteRelationFiberAt_iff_everyEtaleChart B S hS X hX x).2
    (hasFiniteRelationFiberAtEveryEtaleChart_of_hasMonomorphicFieldRepresentative B S hS X hX x
      (hasMonomorphicFieldRepresentative_of_relativelyRepresentable B S hS f hf hY x))

/-- The form that
`AlgebraicGeometry.Space.hasFiniteRelationFibersAtEveryPoint_of_relativelyRepresentable` takes
when the target is decent: the source of a representable morphism into a decent algebraic
space has property `(β)` of Stacks 03JX. -/
theorem hasFiniteRelationFibersAtEveryPoint_of_isDecentSpace
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) (hY : IsDecentSpace B S hS Y) :
    HasFiniteRelationFibersAtEveryPoint B S hS X :=
  hasFiniteRelationFibersAtEveryPoint_of_relativelyRepresentable B S hS hX f hf
    (fun y => IsDecentSpace.hasMonomorphicFieldRepresentative B S hS Y hY y)

/-- **Stacks 03KF, the case `(β)`.** Property `(β)` of Stacks 03JX passes from the target of
a representable morphism of algebraic spaces over `S` to its source.

Property `(β)` is condition (1) of Stacks 03JU at every point, which is how
`AlgebraicGeometry.Space.HasFiniteRelationFibersAtEveryPoint` spells it. The source's
argument runs on condition (4) instead, a monomorphic field-valued representative, so the
hypothesis on `Y` is carried across the equivalences of Stacks 03JU before
`AlgebraicGeometry.Space.hasFiniteRelationFibersAtEveryPoint_of_relativelyRepresentable`
transports it to `X`; that is what makes `Y` an algebraic space a hypothesis here. -/
@[stacks 03KF "property_beta"]
theorem hasFiniteRelationFibersAtEveryPoint_of_relativelyRepresentable_of_target
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f)
    (hYβ : HasFiniteRelationFibersAtEveryPoint B S hS Y) :
    HasFiniteRelationFibersAtEveryPoint B S hS X :=
  hasFiniteRelationFibersAtEveryPoint_of_relativelyRepresentable B S hS hX f hf fun y =>
    (hasEtaleQuasiCompactFieldRepresentative_iff_hasMonomorphicFieldRepresentative B S hS hY
        y).1
      ((hasFiniteRelationFiberAtEveryEtaleChart_iff_hasEtaleQuasiCompactFieldRepresentative
          B S hS Y hY y).1
        ((hasFiniteRelationFiberAt_iff_everyEtaleChart B S hS Y hY y).1 (hYβ y)))

/-- **Stacks 03KF, property `(θ)`.** Property `(θ)` of an algebraic space over `S` is
representability of its functor of points, so this is the case `𝒫 = (θ)`: for a representable
morphism `f : X ⟶ Y`, representability of `Y` gives representability of `X`.

Neither the sheaf condition nor an atlas is used, so the implication holds for presheaves on
any category; that general form is Stacks 03KC. -/
@[stacks 03KF "property_theta"]
theorem isRepresentable_of_relativelyRepresentable_of_target
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f) (hYθ : Y.IsRepresentable) :
    X.IsRepresentable :=
  letI := hYθ
  CategoryTheory.Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable f hf

end AlgebraicGeometry.Space

end
