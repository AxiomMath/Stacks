module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyBoundedFibers

/-!
# Reasonable and very reasonable algebraic spaces, absolutely and relatively

An algebraic space over a scheme `S` is *reasonable* when it satisfies the equivalent
conditions of Stacks 03JT; equivalently, when it has property `(δ)` of Stacks 03JX. It is
*very reasonable* when it satisfies the equivalent conditions of Stacks 03IH; equivalently,
when it has property `(ε)` of Stacks 03JX. A *morphism* of algebraic spaces has either
property when every base change of it along a scheme-valued point of its target has the
corresponding absolute property.

## Main definitions

* `AlgebraicGeometry.Space.IsReasonableSpace` and
  `AlgebraicGeometry.Space.IsVeryReasonableSpace` are the two conditions on an algebraic
  space.
* `AlgebraicGeometry.Space.IsReasonable` and `AlgebraicGeometry.Space.IsVeryReasonable` are
  the two corresponding conditions on a morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.IsReasonableSpace.hasUniversallyBoundedFibers` and
  `AlgebraicGeometry.Space.IsReasonable.hasUniversallyBoundedFibers` read off the condition
  of Stacks 03JL at an affine étale chart, in the absolute and the relative case.
* `AlgebraicGeometry.Space.isVeryReasonableSpace_of_atlas` builds very reasonableness from
  one explicit family of charts, and
  `AlgebraicGeometry.Space.IsVeryReasonableSpace.exists_etaleAtlas`,
  `AlgebraicGeometry.Space.IsVeryReasonable.exists_etaleAtlas` extract from it the jointly
  surjective étale atlas, forgetting the quasi-compactness of the self-intersection
  projections.

## Implementation notes

The two renames. Stacks 03I8 and 03KZ both call their conditions "reasonable" and "very
reasonable", one for a space and one for a morphism, so the *object*-level predicates carry
the suffix `Space`: `IsReasonableSpace` and `IsVeryReasonableSpace` for 03I8 against
`IsReasonable` and `IsVeryReasonable` for 03KZ. This is the convention F4 fixed for
`AlgebraicGeometry.Space.IsQuasiCompactSpace` (03E3, a space) against
`AlgebraicGeometry.Space.IsQuasiCompact` (03HE, a morphism), and it is the same rename
`AlgebraicGeometry.Space.IsDecentSpace` already carries against
`AlgebraicGeometry.Space.IsDecent`.

What the two absolute conditions are spelled as. Stacks 03I8 defines reasonableness by "the
equivalent conditions of Lemma 03JT" and very reasonableness by "the equivalent conditions
of Lemma 03IH", so each formalization must pick one of those conditions.
`IsReasonableSpace` uses condition (2) of 03JT, that every étale chart by an affine scheme
has universally bounded fibres in the sense of Stacks 03JL
(`AlgebraicGeometry.Space.HasUniversallyBoundedFibers`), and `IsVeryReasonableSpace` uses
condition (2) of 03IH, the property-`(ε)` form: a jointly surjective family of étale charts
by schemes whose two self-intersection projections are quasi-compact. Those are the choices
made in the library's statements of 03JT and 03IH. Each definition therefore agrees with the other formulation of its
source definition by an equivalence, and both equivalences are available:
`AlgebraicGeometry.Space.isReasonableSpace_iff_exists_boundedEtaleCover` is 03JT and
`AlgebraicGeometry.Space.isVeryReasonableSpace_iff_exists_isZariskiCover_quasiCompact_chart`
is 03IH. The comparison 03JX of properties `(β)`, `(γ)`, `(δ)` and `(ε)` is not proved here,
so the implications between these conditions and decency — very reasonable implies reasonable
implies decent — are still unavailable: each of them is a part of 03JX, and none of them is
definitional on the chosen formulations.

Étaleness occurs here in its two different senses, as it does in the source. The charts of
`IsReasonableSpace` are *representable* morphisms whose represented base changes are étale
morphisms of schemes, which is the hypothesis Stacks 03JT puts on `U → X` and which is what
`CategoryTheory.MorphismProperty.presheaf` of the inverse image of
`AlgebraicGeometry.Etale` says; the charts of `IsVeryReasonableSpace` are étale in the sense
of Stacks 03FR, `AlgebraicGeometry.Space.IsEtale`. Joint surjectivity of the family is local
surjectivity of the induced morphism out of the coproduct for the localized fppf topology
`AlgebraicGeometry.BigFppfOver.topology`, and the self-intersections are pullbacks in the
presheaf category. Nothing here assumes that the presheaf is an algebraic space; as in the
source definitions that hypothesis is imposed by clients, and it is what makes the two
conditions equivalent to the other formulations.

The relative conditions quantify over *all* morphisms from a representable presheaf into
the target, as the source does — not over a chosen cover of it. All four predicates are kept
as `abbrev`s, as in the statements of the source definitions, so their quantifiers and the absolute predicates
underneath are directly available to base-change and composition statements.

Inside the namespace `AlgebraicGeometry.Space` a bare `IsEtale`, `IsQuasiCompact` or
`HasUniversallyBoundedFibers` resolves to the space-level notion, not to the identically
named property of a morphism of schemes; write `_root_.AlgebraicGeometry.Etale` and
`_root_.AlgebraicGeometry.HasUniversallyBoundedFibers` for those.

## References

* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03IH](https://stacks.math.columbia.edu/tag/03IH)
* [Stacks Project, Tag 03JT](https://stacks.math.columbia.edu/tag/03JT)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KZ](https://stacks.math.columbia.edu/tag/03KZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The absolute conditions -/

section Absolute

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 03I8, reasonable.** An algebraic space over `S` is *reasonable* when it
satisfies the equivalent conditions of Stacks 03JT, taken here in the form of condition (2):
every étale chart of it by an affine scheme has universally bounded fibres. -/
@[stacks 03I8 "reasonable"]
abbrev IsReasonableSpace : Prop :=
  ∀ U : BigFppfOver B S hS,
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    ∀ φ : yoneda.obj U ⟶ X,
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ →
      HasUniversallyBoundedFibers B S hS U φ

/-- **Stacks 03I8, very reasonable.** An algebraic space over `S` is *very reasonable* when
it satisfies the equivalent conditions of Stacks 03IH, taken here in the form of condition
(2), which is property `(ε)` of Stacks 03JX: there is a jointly surjective family of étale
charts by schemes whose two self-intersection projections are quasi-compact. -/
@[stacks 03I8 "very_reasonable"]
abbrev IsVeryReasonableSpace : Prop :=
  ∃ (I : Type u) (U : I → BigFppfOver B S hS) (φ : ∀ i, yoneda.obj (U i) ⟶ X),
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc φ) ∧
    ∀ i, IsEtale B S hS (φ i) ∧
      IsQuasiCompact B S hS (pullback.fst (φ i) (φ i)) ∧
      IsQuasiCompact B S hS (pullback.snd (φ i) (φ i))

/-- A reasonable algebraic space has universally bounded fibres, in the sense of
Stacks 03JL, along each of its étale charts by an affine scheme. -/
theorem IsReasonableSpace.hasUniversallyBoundedFibers (h : IsReasonableSpace B S hS X)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ) :
    HasUniversallyBoundedFibers B S hS U φ := h U hU φ hφ

/-- One explicit jointly surjective family of étale charts with quasi-compact
self-intersection projections makes an algebraic space very reasonable. -/
theorem isVeryReasonableSpace_of_atlas {I : Type u} (U : I → BigFppfOver B S hS)
    (φ : ∀ i, yoneda.obj (U i) ⟶ X)
    (hφ : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc φ))
    (hU : ∀ i, IsEtale B S hS (φ i) ∧
      IsQuasiCompact B S hS (pullback.fst (φ i) (φ i)) ∧
      IsQuasiCompact B S hS (pullback.snd (φ i) (φ i))) :
    IsVeryReasonableSpace B S hS X :=
  ⟨I, U, φ, hφ, hU⟩

/-- A very reasonable algebraic space has a jointly surjective family of étale charts by
schemes; the quasi-compactness of the self-intersection projections is forgotten. -/
theorem IsVeryReasonableSpace.exists_etaleAtlas (h : IsVeryReasonableSpace B S hS X) :
    ∃ (I : Type u) (U : I → BigFppfOver B S hS) (φ : ∀ i, yoneda.obj (U i) ⟶ X),
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc φ) ∧
      ∀ i, IsEtale B S hS (φ i) := by
  obtain ⟨I, U, φ, hφ, hU⟩ := h
  exact ⟨I, U, φ, hφ, fun i ↦ (hU i).1⟩

end Absolute

/-! ### The relative conditions -/

section Relative

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03KZ, reasonable morphism.** A morphism of algebraic spaces over `S` is
*reasonable* when every base change of it along a morphism from a representable presheaf
into its target is a reasonable algebraic space. -/
@[stacks 03KZ "reasonable morphism"]
abbrev IsReasonable (f : X ⟶ Y) : Prop :=
  ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
    IsReasonableSpace B S hS (pullback g f)

/-- **Stacks 03KZ, very reasonable morphism.** A morphism of algebraic spaces over `S` is
*very reasonable* when every base change of it along a morphism from a representable
presheaf into its target is a very reasonable algebraic space. -/
@[stacks 03KZ "very reasonable morphism"]
abbrev IsVeryReasonable (f : X ⟶ Y) : Prop :=
  ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
    IsVeryReasonableSpace B S hS (pullback g f)

/-- A reasonable morphism has universally bounded fibres, in the sense of Stacks 03JL,
along each affine étale chart of each of its represented base changes. -/
theorem IsReasonable.hasUniversallyBoundedFibers {f : X ⟶ Y} (h : IsReasonable B S hS f)
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y) (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (φ : yoneda.obj U ⟶ pullback g f)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ) :
    HasUniversallyBoundedFibers B S hS U φ :=
  (h T g).hasUniversallyBoundedFibers B S hS _ U hU φ hφ

/-- A very reasonable morphism has a jointly surjective family of étale charts by schemes
over each of its represented base changes. -/
theorem IsVeryReasonable.exists_etaleAtlas {f : X ⟶ Y} (h : IsVeryReasonable B S hS f)
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y) :
    ∃ (I : Type u) (U : I → BigFppfOver B S hS)
      (φ : ∀ i, yoneda.obj (U i) ⟶ pullback g f),
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc φ) ∧
      ∀ i, IsEtale B S hS (φ i) :=
  (h T g).exists_etaleAtlas B S hS _

end Relative

end AlgebraicGeometry.Space

end
