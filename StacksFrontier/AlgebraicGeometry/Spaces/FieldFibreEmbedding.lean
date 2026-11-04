module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fold5.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# The field fibre maps bijectively onto the set-theoretic fibre

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `y ∈ |Y|` be
represented by a field-valued point `p` whose presenting morphism `Spec(k) ⟶ Y` is a
monomorphism. Stacks 0AC8 asserts that, when that morphism is in addition quasi-compact,
`|X_k| → |X|` is a **homeomorphism** onto `f^{-1}({y}) ⊂ |X|` with the induced topology.

That statement has three parts: the map is injective, its image is the set-theoretic fibre,
and it is topologically inducing. This file proves the first, and combines it with the second
— `AlgebraicGeometry.Space.range_pointsMap_fst_fieldFibre`, proved for arbitrary presheaves —
into the bijection `|X_k| ≃ f^{-1}({y})`. The third part is **not** proved; see the
implementation notes.

## Main definitions

* `AlgebraicGeometry.Space.pointsEquivSetFibre` is the bijection from the points of the field
  fibre onto the set-theoretic fibre.

## Main results

* `AlgebraicGeometry.Space.injective_pointsMap_fst_fieldFibre` is Stacks 0AC8, injectivity.
* `AlgebraicGeometry.Space.bijOn_pointsMap_fst_fieldFibre` is Stacks 0AC8, the bijection onto
  the set-theoretic fibre.
* `AlgebraicGeometry.Space.isEmbedding_pointsMap_fst_fieldFibre_of_isInducing` records what the
  remaining part of Stacks 0AC8 would add: with injectivity in hand the homeomorphism onto the
  fibre is exactly the inducing property.
* `AlgebraicGeometry.Space.finite_univ_points_fieldFibre_of_finite_setFibre` is the converse of
  the implication "condition (4) implies condition (1)" of Stacks 0ACK, available here
  because the comparison map is a bijection.

## Implementation notes

Injectivity needs only the monomorphism hypothesis, and uses none of the algebraic-space
axioms: the field fibre is `X ×_Y Spec(k)` and a pullback of a monomorphism is a monomorphism
(`CategoryTheory.Limits.pullback.fst_of_mono`), so the projection `X_k ⟶ X` is a monomorphism
of presheaves, and a monomorphism is injective on the points of Tag 03BU by Tag 06RV
(`AlgebraicGeometry.Space.pointsMap_injective_of_mono`).

The quasi-compactness hypothesis of the source is therefore **absent** from everything proved
here. It is what the unproved third part needs: without it the conclusion is false, as the
disjoint union of the spectra of all the prime fields mapping to `Spec(ℤ)` shows — that is a
monomorphism, injective with image the set of closed points, which carries the cofinite and not
the discrete topology.

The source proves the third part by choosing an affine étale chart `V ⟶ Y` with a point `v`
above `y`, shrinking `V` so that `v` is the only point of `V` above `y` — which is where
quasi-compactness of `Spec(k) ⟶ Y` enters, through the finiteness of that set of points
(Tag 03JV) — and then comparing `|X_v| → |X_V| → |X|` with the scheme fibre `U_v ⊂ U_V` of an
étale atlas `U ⟶ X` (Tag 01K1). Both Tag 03JU and Tag 03JV ARE now proved in this
repository -- 03JV at
`Spaces/QuasiCompactPointsFiniteFibres.lean:161,241,277` and 03JU at
`Spaces/RelationFibreTransfer.lean:371,404` -- so the shrinking step is available. The third
part of Tag 0AC8 is likewise no longer open: it is proved at
`Spaces/FieldFibreInducing.lean:402,451`, using 03JV. The structure of the
remaining argument would follow
`AlgebraicGeometry.Space.isInducing_pointsMap_of_isImmersion`, which performs the same transfer
along an étale atlas for an immersion.

## References

* [Stacks Project, Tag 01K1](https://stacks.math.columbia.edu/tag/01K1)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 06RV](https://stacks.math.columbia.edu/tag/06RV)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Injectivity -/

/-- **Stacks 0AC8, injectivity.** If the morphism `Spec(k) ⟶ Y` presented by a field-valued
point `p` of `Y` is a monomorphism, then the comparison map `|X_k| → |X|` from the points of
the field fibre is injective.

The projection `X_k = X ×_Y Spec(k) ⟶ X` is a pullback of that monomorphism, hence itself a
monomorphism, and a monomorphism is injective on points by Tag 06RV. -/
@[stacks 0AC8 "injectivity on points"]
theorem injective_pointsMap_fst_fieldFibre (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (hp : Mono (fieldMorphism B S hS Y p)) :
    Function.Injective (pointsMap B S hS (fieldFibre B S hS f p)
      (pullback.fst f (yonedaEquiv.symm p.value))) :=
  have := hp
  pointsMap_injective_of_mono B S hS _

/-! ### The bijection onto the set-theoretic fibre -/

/-- **Stacks 0AC8, the bijection.** Under the monomorphism hypothesis the comparison map
`|X_k| → |X|` is a bijection from the points of the field fibre onto the set-theoretic fibre
`f^{-1}({y}) ⊂ |X|`.

Injectivity is `AlgebraicGeometry.Space.injective_pointsMap_fst_fieldFibre` and the image is
`AlgebraicGeometry.Space.range_pointsMap_fst_fieldFibre`, which is Tag 03H4. -/
@[stacks 0AC8 "bijection onto the set-theoretic fibre"]
theorem bijOn_pointsMap_fst_fieldFibre (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (hp : Mono (fieldMorphism B S hS Y p)) :
    Set.BijOn (pointsMap B S hS (fieldFibre B S hS f p)
        (pullback.fst f (yonedaEquiv.symm p.value)))
      Set.univ (setFibre B S hS f p) := by
  have hr := range_pointsMap_fst_fieldFibre B S hS f p
  refine ⟨fun w _ ↦ ?_, (injective_pointsMap_fst_fieldFibre B S hS f p hp).injOn,
    fun x hx ↦ ?_⟩
  · rw [← hr]
    exact Set.mem_range_self w
  · rw [Set.image_univ, hr]
    exact hx

/-- The bijection of `AlgebraicGeometry.Space.bijOn_pointsMap_fst_fieldFibre` as an
equivalence: the points of the field fibre `X_k` are in bijection with the set-theoretic fibre
`f^{-1}({y}) ⊂ |X|`. -/
noncomputable def pointsEquivSetFibre (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (hp : Mono (fieldMorphism B S hS Y p)) :
    points B S hS (fieldFibre B S hS f p) ≃ setFibre B S hS f p :=
  (Equiv.ofInjective _ (injective_pointsMap_fst_fieldFibre B S hS f p hp)).trans
    (Set.equivOfEq (range_pointsMap_fst_fieldFibre B S hS f p))

/-- **Stacks 0ACK, condition (1) implies condition (4)** for a point represented by a
monomorphism. This is the converse of
`AlgebraicGeometry.Space.finite_setFibre_of_finite_fieldFibre`, and it is available because the
comparison map is then a bijection and not merely a surjection onto the fibre. -/
@[stacks 0ACK "condition (1) implies condition (4), monomorphic representative"]
theorem finite_univ_points_fieldFibre_of_finite_setFibre (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (hp : Mono (fieldMorphism B S hS Y p))
    (hfin : (setFibre B S hS f p).Finite) :
    (Set.univ : Set (points B S hS (fieldFibre B S hS f p))).Finite :=
  have : Finite (setFibre B S hS f p) := hfin
  have := Finite.of_equiv _ (pointsEquivSetFibre B S hS f p hp).symm
  Set.finite_univ

/-! ### What the remaining part of the tag would add -/

/-- With injectivity available, the outstanding part of Stacks 0AC8 — that `|X_k| → |X|` is a
homeomorphism onto `f^{-1}({y})` with the induced topology — is exactly the statement that the
comparison map is topologically inducing. -/
theorem isEmbedding_pointsMap_fst_fieldFibre_of_isInducing (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (hp : Mono (fieldMorphism B S hS Y p))
    (hind : Topology.IsInducing (pointsMap B S hS (fieldFibre B S hS f p)
      (pullback.fst f (yonedaEquiv.symm p.value)))) :
    Topology.IsEmbedding (pointsMap B S hS (fieldFibre B S hS f p)
      (pullback.fst f (yonedaEquiv.symm p.value))) :=
  ⟨hind, injective_pointsMap_fst_fieldFibre B S hS f p hp⟩

end AlgebraicGeometry.Space

end
