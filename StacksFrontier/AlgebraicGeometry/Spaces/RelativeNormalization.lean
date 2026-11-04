module

public import Mathlib.AlgebraicGeometry.Normalization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Normalization of an algebraic space

Let `F` be an algebraic space over `S` each of whose étale scheme charts has finitely many
irreducible components over every quasi-compact open. Then `F` has a normalization: an
algebraic space `F^ν` over `S` together with a morphism `F^ν ⟶ F` whose base change along
every surjective étale scheme chart `U ⟶ F` is the normalization `U^ν ⟶ U` of that chart.

This module introduces the normalization as *data*. The source proof constructs it from one
surjective étale presentation `F = U/R` by normalizing both `U` and `R`, and then proves the
construction independent of the presentation; the chart condition recorded here is the
conclusion of that independence, so it holds for every surjective étale chart at once and in
particular for the identity chart when `F` is representable.

## Main definitions

* `AlgebraicGeometry.Space.HasLocallyFiniteIrreducibleComponents` is the finiteness condition
  on the quasi-compact opens of every étale scheme chart of an algebraic space.
* `AlgebraicGeometry.Space.NormalizationData` packages a normalization morphism of an
  algebraic space with its identification over every surjective étale scheme chart.

## Main results

* `AlgebraicGeometry.Space.NormalizationData.finite_irreducibleComponents_of_chart`: a
  surjective étale chart of a normalized algebraic space has finitely many irreducible
  components over each of its quasi-compact opens.
* `AlgebraicGeometry.Space.NormalizationData.chart_self`: for a representable algebraic space
  the identity is such a chart, so the normalization of the representing scheme is the base
  change of the normalization morphism along the identity.
* `AlgebraicGeometry.Space.isSurjective_id` and `AlgebraicGeometry.Space.isEtale_id`: the
  identity of a presheaf on the big fppf site of `S` is surjective and étale. Together with
  `AlgebraicGeometry.Space.isSmooth_id` these are the three relative properties an identity
  presentation has to have; like that lemma they are untagged, since Stacks 041D is their
  home.

## Implementation notes

The chart condition is an existential statement about a scheme `Uν` *of the site*: the
normalized chart has to be small enough to be an object of the chosen big fppf site. This is
a genuine constraint and not a bookkeeping detail, since `BigFppfSite.Contains` is a bound on
`AlgebraicGeometry.Scheme.size`.

The finiteness hypothesis `hU` needed to form the normalization of a chart is existentially
bound inside the chart condition rather than imposed as a field. This makes the condition
self-contained — the hypothesis is part of what a normalization asserts about each of its
charts — and `finite_irreducibleComponents_of_chart` recovers it.

No declaration here carries the tag of the source lemma: the lemma asserts that such data
*exists*, and only the construction is entitled to the tag.

`AlgebraicGeometry.Space.isSurjective_id` and `AlgebraicGeometry.Space.isEtale_id` are stated
for an arbitrary presheaf, not just for a representable one: the proofs are the identity on
points and the unit law for composition of charts, neither of which uses representability. They
sit here, next to their first consumer `AlgebraicGeometry.Space.NormalizationData.chart_self`.

`HasLocallyFiniteIrreducibleComponents` is likewise untagged. It is condition (2) of Tag 0BB1,
whose content is the equivalence of that condition with three others; a definition of one of
the conditions is not that equivalence, so the tag belongs to the equivalences and not here.

## References

* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every quasi-compact open of every étale scheme chart of an algebraic space
has finitely many irreducible components. -/
abbrev HasLocallyFiniteIrreducibleComponents (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F),
    IsEtale B S hS f →
      ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
        IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
          (irreducibleComponents V).Finite

/-- An algebraic space over `S` together with a morphism to `F` whose base change along every
surjective étale scheme chart of `F` is the normalization of that chart. -/
structure NormalizationData (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The normalization, as a presheaf on the big fppf site. -/
  space : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The normalization is an algebraic space over `S`. -/
  isAlgebraicSpace : IsAlgebraicSpace B S hS space
  /-- The normalization morphism. -/
  hom : space ⟶ F
  /-- Along every surjective étale scheme chart of `F` the normalization morphism base changes
  to the normalization of the chart. -/
  chart :
    ∀ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F),
      IsSurjective B S hS f →
      IsEtale B S hS f →
      ∃ (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
          IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
            (irreducibleComponents V).Finite)
        (Uν : BigFppfOver B S hS) (p : Uν ⟶ U)
        (g : yoneda.obj Uν ⟶ space)
        (e : ((BigFppfOver.toScheme B S hS).obj Uν) ≅
          Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U) hU),
          (BigFppfOver.toScheme B S hS).map p =
            e.hom ≫ Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU ∧
          IsPullback g (yoneda.map p) hom f

namespace NormalizationData

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Every quasi-compact open of a surjective étale scheme chart of a normalized algebraic
space has finitely many irreducible components. -/
theorem finite_irreducibleComponents_of_chart (D : NormalizationData B S hS F)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F) (hf : IsSurjective B S hS f)
    (hfe : IsEtale B S hS f) (V : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (hV : IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U))) :
    (irreducibleComponents V).Finite :=
  (D.chart U f hf hfe).elim fun hU _ ↦ hU V hV

end NormalizationData

/-- **The identity of a presheaf on the big fppf site of `S` is surjective on points**, because
the map it induces on points is the identity. -/
theorem isSurjective_id (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsSurjective B S hS (𝟙 X) :=
  fun x ↦ ⟨x, congrFun (pointsMap_id B S hS X) x⟩

/-- **The identity of a presheaf on the big fppf site of `S` is étale**, immediately from
Stacks 03FR: the composite of an étale morphism from a representable presheaf with the identity
is that morphism. -/
theorem isEtale_id (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsEtale B S hS (𝟙 X) := fun _ _ hφ ↦ by simpa using hφ

namespace NormalizationData

variable {B S hS}

/-- For a representable algebraic space the identity is a surjective étale chart, so the
normalization of the representing scheme is cut out of the normalization morphism by a
cartesian square. -/
theorem chart_self {U : BigFppfOver B S hS}
    (D : NormalizationData B S hS (yoneda.obj U)) :
    ∃ (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
        IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
          (irreducibleComponents V).Finite)
      (Uν : BigFppfOver B S hS) (p : Uν ⟶ U)
      (g : yoneda.obj Uν ⟶ D.space)
      (e : ((BigFppfOver.toScheme B S hS).obj Uν) ≅
        Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U) hU),
        (BigFppfOver.toScheme B S hS).map p =
          e.hom ≫ Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU ∧
        IsPullback g (yoneda.map p) D.hom (𝟙 (yoneda.obj U)) :=
  D.chart U (𝟙 _) (isSurjective_id B S hS (yoneda.obj U)) (isEtale_id B S hS (yoneda.obj U))

end NormalizationData

end AlgebraicGeometry.Space

end
