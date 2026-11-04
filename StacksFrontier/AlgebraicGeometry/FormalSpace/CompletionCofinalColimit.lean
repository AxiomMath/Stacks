module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeColimit
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverCofinality

/-!
# The quotient stages of a relative completion form a cofinal subdiagram

Let `B` be a weakly pre-admissible topological ring, let `f : B →+* A` be a ring map and let
`A^∧ = CompletionOver f` be the completion of `A` along the extensions of the weak ideals of
definition of `B`. Sending a weak ideal of definition `J ⊆ B` to the kernel of the projection
`A^∧ → A ⧸ JA` is a functor from the weak ideals of definition of `B`, ordered by reverse
inclusion, to those of `A^∧`, and that functor is *final*: every weak ideal of definition of
`A^∧` contains one of the kernels. Consequently the diagram of quotient stages indexed by the
weak ideals of definition of `B` computes the same colimit as the canonical diagram of all
quotient stages of `A^∧`, which is `Spf A^∧`; and the stage at `J` is `Spec (A ⧸ JA)`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.kerProjectionDiagram`: the functor
  `J ↦ ker (A^∧ → A ⧸ JA)` on weak ideals of definition ordered by reverse inclusion.
* `AlgebraicGeometry.FormalSpace.colimitIsoFormalSpectrumOfCompletion`:
  `colim_J Spec (A^∧ ⧸ ker (A^∧ → A ⧸ JA)) ≅ Spf A^∧`.
* `AlgebraicGeometry.FormalSpace.kerProjectionStageIso`: the stage at `J` of that cofinal
  subdiagram is `Spec (A ⧸ JA)`.

## Main results

* `AlgebraicGeometry.FormalSpace.final_kerProjectionDiagram`: the functor is final.

## Implementation notes

The ring-theoretic content is
`TopologicalRing.CompletionOver.exists_ker_projection_le_of_isWeakIdealOfDefinition`: the
kernels of the projections are cofinal among the weak ideals of definition of `A^∧`. All that
is added here is the categorical packaging — a functor between the two preorder categories and
`CategoryTheory.Functor.final_of_exists_of_isFiltered`, whose second hypothesis is vacuous
because the morphisms of a preorder category form a subsingleton — together with the transport
of the colimit along it by `CategoryTheory.Functor.Final.colimitIso`.

The source category is filtered because the weak ideals of definition of `B` are directed under
reverse inclusion, the intersection of two of them being one again.

This file is untagged substrate: Stacks 0AN6 supplies the inputs and Stacks 0AIF the formal
spectrum, while the statements here are the colimit-cofinality step that the essential
surjectivity half of Stacks 0AN8 runs on. They are stated exactly at the generality that step
needs, namely for the canonical quotient system of the completion.

## References

* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 04E7](https://stacks.math.columbia.edu/tag/04E7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [CommRing A] (f : B →+* A)

/-- The kernels of the projections of the relative completion increase with the weak ideal of
definition of the base. -/
theorem kerProjectionIdeal_mono {J K : TopologicalRing.WeakIdealOfDefinitionIndex B}
    (h : J.1 ≤ K.1) : (kerProjectionIdeal f J).1 ≤ (kerProjectionIdeal f K).1 := by
  intro x hx
  change x.1 J = 0 at hx
  show x.1 K = 0
  rw [← x.2 J K h, hx]
  simp

/-- The diagram `J ↦ ker (A^∧ → A ⧸ JA)` of weak ideals of definition of the relative
completion, indexed by the weak ideals of definition of the base ordered by reverse
inclusion. -/
def kerProjectionDiagram :
    WeakIdeals B ⥤ WeakIdeals (TopologicalRing.CompletionOver f) where
  obj J := OrderDual.toDual (kerProjectionIdeal f (OrderDual.ofDual J))
  map {_J _K} g := homOfLE (kerProjectionIdeal_mono f (leOfHom g))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The ideal of `AlgebraicGeometry.FormalSpace.kerProjectionDiagram` at `J` is the kernel of the
projection of the relative completion to `A ⧸ JA`. -/
@[simp]
theorem kerProjectionDiagram_obj_coe (J : WeakIdeals B) :
    ((kerProjectionDiagram f).obj J).1 =
      RingHom.ker (TopologicalRing.CompletionOver.projection f (OrderDual.ofDual J)) := rfl

/-- **The quotient stages of the relative completion indexed by the weak ideals of definition
of the base form a cofinal subdiagram of the canonical diagram of all quotient stages.** Every
weak ideal of definition of `A^∧` contains the kernel of one of the projections
`A^∧ → A ⧸ JA`, which is the cofinality statement
`TopologicalRing.CompletionOver.exists_ker_projection_le_of_isWeakIdealOfDefinition`. -/
theorem final_kerProjectionDiagram (hB : TopologicalRing.IsWeaklyPreAdmissible B) :
    (kerProjectionDiagram f).Final := by
  let _ : IsDirectedOrder (WeakIdeals B) := isDirectedOrder_weakIdeals B
  refine Functor.final_of_exists_of_isFiltered _ (fun K ↦ ?_)
    (fun _ _ ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
  obtain ⟨J, hJ⟩ :=
    TopologicalRing.CompletionOver.exists_ker_projection_le_of_isWeakIdealOfDefinition f hB
      (OrderDual.ofDual K).2
  exact ⟨OrderDual.toDual J, ⟨homOfLE hJ⟩⟩

section Colimit

attribute [local instance] sheaf_hasColimits

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}

/-- **`Spf A^∧` is the colimit of the quotient stages indexed by the weak ideals of definition
of the base.** The cofinal subdiagram of
`AlgebraicGeometry.FormalSpace.final_kerProjectionDiagram` computes the colimit of the
canonical diagram, which is the formal spectrum of `A^∧`. -/
noncomputable def colimitIsoFormalSpectrumOfCompletion
    (hB : TopologicalRing.IsWeaklyPreAdmissible B)
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f)) :
    colimit (kerProjectionDiagram f ⋙ formalSpectrumDiagram E) ≅ formalSpectrum E :=
  have := final_kerProjectionDiagram f hB
  Functor.Final.colimitIso (kerProjectionDiagram f) (formalSpectrumDiagram E)

/-- The isomorphism `AlgebraicGeometry.FormalSpace.colimitIsoFormalSpectrumOfCompletion` restricts
on the stage at `J` to the inclusion of that quotient stage into the formal spectrum. -/
@[reassoc (attr := simp)]
theorem ι_colimitIsoFormalSpectrumOfCompletion_hom
    (hB : TopologicalRing.IsWeaklyPreAdmissible B)
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f)) (J : WeakIdeals B) :
    colimit.ι (kerProjectionDiagram f ⋙ formalSpectrumDiagram E) J ≫
        (colimitIsoFormalSpectrumOfCompletion f hB E).hom =
      formalSpectrumInclusion E ((kerProjectionDiagram f).obj J) :=
  have := final_kerProjectionDiagram f hB
  Functor.Final.ι_colimitIso_hom (kerProjectionDiagram f) (formalSpectrumDiagram E) J

/-- The quotient of the relative completion by the kernel of its projection to `A ⧸ JA` is
`A ⧸ JA`, by the unique isomorphism compatible with that projection
(`AlgebraicGeometry.FormalSpace.existsUnique_quotientCompletionEquiv`). -/
noncomputable def quotientKerProjectionRingEquiv
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    (TopologicalRing.CompletionOver f ⧸ (kerProjectionIdeal f J).1) ≃+*
      (A ⧸ TopologicalRing.extendedIdeal f J) :=
  RingHom.quotientKerEquivOfSurjective
    (TopologicalRing.CompletionOver.projection_surjective f J)

/-- `AlgebraicGeometry.FormalSpace.quotientKerProjectionRingEquiv` sends the class of `x` to its
image under the projection of the relative completion to `A ⧸ JA`. -/
@[simp]
theorem quotientKerProjectionRingEquiv_mk
    (J : TopologicalRing.WeakIdealOfDefinitionIndex B)
    (x : TopologicalRing.CompletionOver f) :
    quotientKerProjectionRingEquiv f J (Ideal.Quotient.mk _ x) =
      TopologicalRing.CompletionOver.projection f J x := rfl

/-- **The stage of the cofinal subdiagram at `J` is `Spec (A ⧸ JA)`.** Together with
`AlgebraicGeometry.FormalSpace.colimitIsoFormalSpectrumOfCompletion` this identifies
`Spf A^∧` with `colim_J Spec (A ⧸ JA)` over the weak ideals of definition `J` of the base. -/
noncomputable def kerProjectionStageIso
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f)) (J : WeakIdeals B) :
    (BigAffineFppf.toScheme 𝔅 S hS).obj ((kerProjectionDiagram f ⋙ E.diagram).obj J) ≅
      Spec (.of (A ⧸ TopologicalRing.extendedIdeal f (OrderDual.ofDual J))) :=
  (Scheme.Spec.mapIso
    (quotientKerProjectionRingEquiv f (OrderDual.ofDual J)).toCommRingCatIso.op).symm

end Colimit

end AlgebraicGeometry.FormalSpace

end
