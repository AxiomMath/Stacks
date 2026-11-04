module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionCofinalColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeColimit
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver

/-!
# The quotient stages of a relative completion are identified with `Spec (A ⧸ JA)` naturally

Let `B` be a topological ring, let `f : B →+* A` be a ring map and let
`A^∧ = CompletionOver f` be the completion of `A` along the extensions of the weak ideals of
definition of `B`. For a weak ideal of definition `J ⊆ B` the stage of the cofinal subdiagram
`AlgebraicGeometry.FormalSpace.kerProjectionDiagram` at `J` is identified with
`Spec (A ⧸ JA)` by `AlgebraicGeometry.FormalSpace.kerProjectionStageIso`. This file proves that
identification is *natural* in `J`: the transition morphism of the subdiagram over an inclusion
`K ⊆ J` of weak ideals of definition of `B` is carried to `Spec` of the quotient transition map
`A ⧸ KA → A ⧸ JA`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.extendedQuotientDiagram`: the diagram `J ↦ Spec (A ⧸ JA)` of
  schemes, indexed by the weak ideals of definition of `B` ordered by reverse inclusion, with
  the quotient transition maps as transitions.
* `AlgebraicGeometry.FormalSpace.kerProjectionStageNatIso`: the stagewise identifications
  assembled into an isomorphism of diagrams of schemes.
* `AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageNatIso`: a sheaf over `Spf B` whose
  stagewise base changes are naturally the quotient stages of `A^∧` is `Spf A^∧`.

## Main results

* `TopologicalRing.transitionMap_le_refl` and `TopologicalRing.transitionMap_comp`: the
  quotient transition maps of a relative completion are a functor on the weak ideals of
  definition.
* `AlgebraicGeometry.FormalSpace.transitionMap_quotientKerProjectionRingEquiv`: the
  ring-theoretic naturality, which is the compatibility condition defining the completion.
* `AlgebraicGeometry.FormalSpace.kerProjectionStageIso_naturality`: the naturality square.

## Implementation notes

The whole content is the compatibility condition in the definition of
`TopologicalRing.CompletionOver`: an element of the completion is a family of classes
`a_J ∈ A ⧸ JA` with `TopologicalRing.transitionMap f h (a_K) = a_J` whenever `K ⊆ J`. Since
`AlgebraicGeometry.FormalSpace.quotientKerProjectionRingEquiv` sends the class of `a` modulo
`ker (A^∧ → A ⧸ JA)` to `a_J`, that condition *is* the naturality of the identification, and
the rest is transport through `Spec` and the quotient-factorization lemmas
`Ideal.Quotient.factor_mk`, `Ideal.Quotient.factor_eq` and `Ideal.Quotient.factor_comp`.

The target diagram `AlgebraicGeometry.FormalSpace.extendedQuotientDiagram` is a diagram of
bare schemes, not of schemes *over* `S`. That is deliberate, and is the limit of what can be
stated with what the library has: a diagram over `S` would need structure morphisms
`Spec (A ⧸ JA) ⟶ S` indexed by the weak ideals of definition of `B`, and the two structures
carrying such data, `AlgebraicGeometry.FormalSpace.QuotientSystem` and
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation`, both index them by the weak
ideals of definition of the ring being quotiented — here `A^∧`, not `B`. The naturality square
`AlgebraicGeometry.FormalSpace.kerProjectionStageIso_naturality` is stated at the same place as
the corresponding field
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.quotientIso_natural` of a
weak-ideal presentation, namely after the structure morphisms have been forgotten by
`AlgebraicGeometry.BigAffineFppf.toScheme`, so it is exactly as strong as that field is.

This file is untagged substrate: Stacks 0AN6 supplies the completion and Stacks 0AIF the formal
spectrum, while the statements here are the naturality of the stage identification that the
essential surjectivity half of Stacks 0AN8 runs on, together with the colimit assembly that
consumes it. Stacks 0AN8 itself is not claimed anywhere here: the identification of the
stagewise base changes `Spec (B ⧸ J) ×_{Spf B} X` with the quotient stages `Spec (A ⧸ JA)` —
the family `φ_J` of the source's proof — is a step of that proof and is carried as a hypothesis
by `AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageNatIso` rather than proved. Producing
it needs a *choice* of affine model for each `Spec (B ⧸ J) ×_{Spf B} X`, which the available
form of Stacks 0AKN
(`AlgebraicGeometry.FormalSpace.exists_isAffineHom_isPullback_of_isRepresentable`) gives only
as an existence statement.

## References

* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A] (f : B →+* A)

/-- The quotient transition map attached to the reflexive inclusion is the identity. -/
theorem transitionMap_le_refl (J : WeakIdealOfDefinitionIndex B)
    (h : (J.1 : Ideal B) ≤ J.1) :
    transitionMap f h = RingHom.id (A ⧸ extendedIdeal f J) :=
  Ideal.Quotient.factor_eq

/-- The quotient transition maps attached to a chain of inclusions of weak ideals of definition
compose. -/
theorem transitionMap_comp {J K L : WeakIdealOfDefinitionIndex B}
    (h₁ : (J.1 : Ideal B) ≤ K.1) (h₂ : (K.1 : Ideal B) ≤ L.1) :
    (transitionMap f h₂).comp (transitionMap f h₁) = transitionMap f (h₁.trans h₂) :=
  Ideal.Quotient.factor_comp _ _

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

section Diagram

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A] (f : B →+* A)

/-- The diagram `J ↦ Spec (A ⧸ JA)` of schemes, indexed by the weak ideals of definition of `B`
ordered by reverse inclusion, whose transition morphisms are `Spec` of the quotient transition
maps `TopologicalRing.transitionMap`. -/
noncomputable def extendedQuotientDiagram : WeakIdeals B ⥤ Scheme.{u} where
  obj J := Spec (.of (A ⧸ TopologicalRing.extendedIdeal f (OrderDual.ofDual J)))
  map {_J _K} g := Spec.map (CommRingCat.ofHom (TopologicalRing.transitionMap f (leOfHom g)))
  map_id _ := by
    rw [TopologicalRing.transitionMap_le_refl, CommRingCat.ofHom_id, Spec.map_id]
  map_comp _ _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, TopologicalRing.transitionMap_comp]

/-- The object of `extendedQuotientDiagram f` at `J` is `Spec (A ⧸ JA)`. -/
@[simp]
theorem extendedQuotientDiagram_obj (J : WeakIdeals B) :
    (extendedQuotientDiagram f).obj J =
      Spec (.of (A ⧸ TopologicalRing.extendedIdeal f (OrderDual.ofDual J))) := rfl

/-- The morphism of `extendedQuotientDiagram f` over `J ⟶ K` is `Spec` of the quotient
transition map `A ⧸ KA → A ⧸ JA`. -/
@[simp]
theorem extendedQuotientDiagram_map {J K : WeakIdeals B} (g : J ⟶ K) :
    (extendedQuotientDiagram f).map g =
      Spec.map (CommRingCat.ofHom (TopologicalRing.transitionMap f
        (show ((OrderDual.ofDual K).1 : Ideal B) ≤ (OrderDual.ofDual J).1 from
          leOfHom g))) := rfl

end Diagram

section Naturality

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [CommRing A] (f : B →+* A)

/-- **The identification of the quotient stages of a relative completion with the quotients of
`A` is natural.** Writing `A^∧ ⧸ ker (A^∧ → A ⧸ KA) ≅ A ⧸ KA` for the identification at `K`,
the square over an inclusion `K ⊆ J` of weak ideals of definition of `B` commutes. This is the
compatibility condition in the definition of `TopologicalRing.CompletionOver`. -/
theorem transitionMap_quotientKerProjectionRingEquiv
    {J K : TopologicalRing.WeakIdealOfDefinitionIndex B} (h : (K.1 : Ideal B) ≤ J.1)
    (x : TopologicalRing.CompletionOver f ⧸ (kerProjectionIdeal f K).1) :
    TopologicalRing.transitionMap f h (quotientKerProjectionRingEquiv f K x) =
      quotientKerProjectionRingEquiv f J
        (Ideal.Quotient.factor (kerProjectionIdeal_mono f h) x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk, quotientKerProjectionRingEquiv_mk,
    quotientKerProjectionRingEquiv_mk]
  exact a.2 K J h

/-- The inverse form of
`AlgebraicGeometry.FormalSpace.transitionMap_quotientKerProjectionRingEquiv`: the quotient
transition map of `A` is carried to the quotient transition map of the completion. -/
theorem factor_comp_quotientKerProjectionRingEquiv_symm
    {J K : TopologicalRing.WeakIdealOfDefinitionIndex B} (h : (K.1 : Ideal B) ≤ J.1) :
    (Ideal.Quotient.factor (kerProjectionIdeal_mono f h)).comp
        (quotientKerProjectionRingEquiv f K).symm.toRingHom =
      (quotientKerProjectionRingEquiv f J).symm.toRingHom.comp
        (TopologicalRing.transitionMap f h) := by
  refine RingHom.ext fun y ↦ ?_
  have hy := transitionMap_quotientKerProjectionRingEquiv f h
    ((quotientKerProjectionRingEquiv f K).symm y)
  rw [RingEquiv.apply_symm_apply] at hy
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [hy, RingEquiv.symm_apply_apply]

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}

/-- The stage identification of `AlgebraicGeometry.FormalSpace.kerProjectionStageIso` is `Spec`
of the inverse of the ring identification. -/
theorem kerProjectionStageIso_hom
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f)) (J : WeakIdeals B) :
    (kerProjectionStageIso f E J).hom =
      Spec.map (CommRingCat.ofHom
        (quotientKerProjectionRingEquiv f (OrderDual.ofDual J)).symm.toRingHom) := rfl

/-- **The identification of the stages of the cofinal subdiagram with `Spec (A ⧸ JA)` is
natural in the weak ideal of definition `J ⊆ B`.** The transition morphism of the subdiagram is
carried to `Spec` of the quotient transition map `A ⧸ KA → A ⧸ JA`; this is the naturality in
`J` that `AlgebraicGeometry.FormalSpace.kerProjectionStageIso` does not record. -/
theorem kerProjectionStageIso_naturality
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f))
    {J K : WeakIdeals B} (g : J ⟶ K) :
    (BigAffineFppf.toScheme 𝔅 S hS).map ((kerProjectionDiagram f ⋙ E.diagram).map g) ≫
        (kerProjectionStageIso f E K).hom =
      (kerProjectionStageIso f E J).hom ≫ (extendedQuotientDiagram f).map g := by
  have hle : ((OrderDual.ofDual K).1 : Ideal B) ≤ (OrderDual.ofDual J).1 := leOfHom g
  show Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (kerProjectionIdeal_mono f hle))) ≫
        Spec.map (CommRingCat.ofHom
          (quotientKerProjectionRingEquiv f (OrderDual.ofDual K)).symm.toRingHom) =
      Spec.map (CommRingCat.ofHom
          (quotientKerProjectionRingEquiv f (OrderDual.ofDual J)).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (TopologicalRing.transitionMap f hle))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    Spec.map_inj]
  exact congrArg CommRingCat.ofHom (factor_comp_quotientKerProjectionRingEquiv_symm f hle)

/-- **The stages of the cofinal subdiagram of a relative completion form the diagram
`J ↦ Spec (A ⧸ JA)`.** The stagewise identifications of
`AlgebraicGeometry.FormalSpace.kerProjectionStageIso`, assembled into an isomorphism of
diagrams of schemes by `AlgebraicGeometry.FormalSpace.kerProjectionStageIso_naturality`. -/
noncomputable def kerProjectionStageNatIso
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f)) :
    (kerProjectionDiagram f ⋙ E.diagram) ⋙ BigAffineFppf.toScheme 𝔅 S hS ≅
      extendedQuotientDiagram f :=
  NatIso.ofComponents (kerProjectionStageIso f E) fun g ↦
    kerProjectionStageIso_naturality f E g

section Assembly

attribute [local instance] sheaf_hasColimits

/-- **A sheaf over `Spf B` whose stagewise base changes are naturally the quotient stages of
`A^∧` is the formal spectrum of `A^∧`.** The three isomorphisms are: the sheaf is the colimit
of its base changes to the stages of `Spf B`
(`AlgebraicGeometry.FormalSpace.isoColimitStageBaseChange`), the given identification of
diagrams, and the cofinality transport
(`AlgebraicGeometry.FormalSpace.colimitIsoFormalSpectrumOfCompletion`).

This is the final assembly of the essential surjectivity half of Stacks 0AN8, with the
stagewise identification `α` — which the source obtains from the uniqueness clause of Stacks
0ALI applied to the two étale `B ⧸ J`-algebras lifting `A ⧸ J₀A` — carried as a hypothesis. It
is therefore *not* tagged: `α` is a step of the proof of Stacks 0AN8, not a separate result the
source defers to. -/
noncomputable def isoFormalSpectrumOfStageNatIso
    (hB : TopologicalRing.IsWeaklyPreAdmissible B) (D : QuotientSystem 𝔅 S hS B)
    {V : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))} (v : V ⟶ formalSpectrum D)
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f))
    (α : stageBaseChangeDiagram D v ≅ kerProjectionDiagram f ⋙ formalSpectrumDiagram E) :
    V ≅ formalSpectrum E :=
  (isoColimitStageBaseChange D v hB).trans
    ((HasColimit.isoOfNatIso α).trans (colimitIsoFormalSpectrumOfCompletion f hB E))

end Assembly

end Naturality

end AlgebraicGeometry.FormalSpace

end
