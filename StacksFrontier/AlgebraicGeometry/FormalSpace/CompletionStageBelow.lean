module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionStageNaturality

/-!
# The weak ideals of definition contained in a fixed one are cofinal

Let `R` be a topological ring and let `J₀ ⊆ R` be a weak ideal of definition. The weak ideals
of definition `J ⊆ J₀`, ordered by reverse inclusion, are *cofinal* among all weak ideals of
definition of `R`: for any weak ideal of definition `J` the intersection `J ⊓ J₀` is one again
and is contained in both. Consequently every colimit over the weak ideals of definition of `R`
is computed by the subdiagram indexed by those contained in `J₀`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.WeakIdealsBelow`: the weak ideals of definition contained in a
  fixed one, ordered by reverse inclusion.
* `AlgebraicGeometry.FormalSpace.weakIdealsBelowInclusion`: the inclusion into all weak ideals
  of definition.
* `AlgebraicGeometry.FormalSpace.isoColimitStageBaseChangeBelow`:
  `V ≅ colim_{J ⊆ J₀} (Spec (R ⧸ J) ×_{Spf R} V)`.
* `AlgebraicGeometry.FormalSpace.colimitIsoFormalSpectrumOfCompletionBelow`:
  `colim_{J ⊆ J₀} Spec (A ⧸ JA) ≅ Spf A^∧`.
* `AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageNatIsoBelow`: a sheaf over `Spf B`
  whose stagewise base changes *at the stages below `J₀`* are naturally the quotient stages of
  `A^∧` is `Spf A^∧`.

## Main results

* `AlgebraicGeometry.FormalSpace.final_weakIdealsBelowInclusion`: the inclusion is final.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
* [Stacks Project, Tag 04E7](https://stacks.math.columbia.edu/tag/04E7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

section Index

variable (R : Type u) [CommRing R] [TopologicalSpace R]
  (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex R)

/-- The weak ideals of definition of `R` contained in a fixed one `J₀`, ordered by reverse
inclusion. -/
abbrev WeakIdealsBelow : Type u :=
  { J : WeakIdeals R // (OrderDual.ofDual J).1 ≤ J₀.1 }

/-- `J₀` itself is a weak ideal of definition contained in `J₀`. -/
theorem nonempty_weakIdealsBelow : Nonempty (WeakIdealsBelow R J₀) :=
  ⟨⟨OrderDual.toDual J₀, le_rfl⟩⟩

/-- The weak ideals of definition contained in `J₀` are directed under reverse inclusion. -/
theorem isDirectedOrder_weakIdealsBelow : IsDirectedOrder (WeakIdealsBelow R J₀) := by
  refine ⟨fun i j ↦ ⟨⟨OrderDual.toDual
      ⟨(OrderDual.ofDual i.1).1 ⊓ (OrderDual.ofDual j.1).1,
        TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right
          (OrderDual.ofDual i.1).2 (OrderDual.ofDual j.1).2.1⟩, ?_⟩, ?_, ?_⟩⟩
  · exact inf_le_left.trans i.2
  · exact (inf_le_left :
      (OrderDual.ofDual i.1).1 ⊓ (OrderDual.ofDual j.1).1 ≤ (OrderDual.ofDual i.1).1)
  · exact (inf_le_right :
      (OrderDual.ofDual i.1).1 ⊓ (OrderDual.ofDual j.1).1 ≤ (OrderDual.ofDual j.1).1)

/-- Passing from a weak ideal of definition contained in `J₀` to the underlying weak ideal of
definition is monotone. -/
theorem monotone_weakIdealsBelow_val :
    Monotone (fun J : WeakIdealsBelow R J₀ ↦ J.1) := fun _ _ h ↦ h

/-- The inclusion of the weak ideals of definition contained in `J₀` into all weak ideals of
definition, as a functor of preorder categories. -/
def weakIdealsBelowInclusion : WeakIdealsBelow R J₀ ⥤ WeakIdeals R :=
  (monotone_weakIdealsBelow_val R J₀).functor

/-- The inclusion `AlgebraicGeometry.FormalSpace.weakIdealsBelowInclusion` sends `J ⊆ J₀` to
`J`. -/
@[simp]
theorem weakIdealsBelowInclusion_obj (J : WeakIdealsBelow R J₀) :
    (weakIdealsBelowInclusion R J₀).obj J = J.1 := rfl

/-- **The weak ideals of definition contained in a fixed one are cofinal among all weak ideals
of definition.** -/
instance final_weakIdealsBelowInclusion : (weakIdealsBelowInclusion R J₀).Final := by
  let _ : IsDirectedOrder (WeakIdealsBelow R J₀) := isDirectedOrder_weakIdealsBelow R J₀
  refine (Monotone.final_functor_iff (monotone_weakIdealsBelow_val R J₀)).mpr fun J ↦ ?_
  refine ⟨⟨OrderDual.toDual ⟨(OrderDual.ofDual J).1 ⊓ J₀.1,
    TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right
      (OrderDual.ofDual J).2 J₀.2.1⟩, inf_le_right⟩, ?_⟩
  exact (inf_le_left : (OrderDual.ofDual J).1 ⊓ J₀.1 ≤ (OrderDual.ofDual J).1)

end Index

section Colimit

attribute [local instance] sheaf_hasColimits

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}

section StageBaseChange

variable {R : Type u} [CommRing R] [TopologicalSpace R] (D : QuotientSystem 𝔅 S hS R)
  {V : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))} (v : V ⟶ formalSpectrum D)

/-- **A sheaf over a formal spectrum is the colimit of its base changes to the quotient stages
below a fixed weak ideal of definition `J₀`**:
`V ≅ colim_{J ⊆ J₀} (Spec (R ⧸ J) ×_{Spf R} V)`. -/
noncomputable def isoColimitStageBaseChangeBelow
    (hR : TopologicalRing.IsWeaklyPreAdmissible R)
    (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex R) :
    V ≅ colimit (weakIdealsBelowInclusion R J₀ ⋙ stageBaseChangeDiagram D v) :=
  (isoColimitStageBaseChange D v hR).trans
    (Functor.Final.colimitIso (weakIdealsBelowInclusion R J₀)
      (stageBaseChangeDiagram D v)).symm

/-- The leg of the colimit cocone of
`AlgebraicGeometry.FormalSpace.isoColimitStageBaseChangeBelow` at `J ⊆ J₀` is the projection
`Spec (R ⧸ J) ×_{Spf R} V ⟶ V`. -/
theorem ι_isoColimitStageBaseChangeBelow_inv
    (hR : TopologicalRing.IsWeaklyPreAdmissible R)
    (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex R) (J : WeakIdealsBelow R J₀) :
    colimit.ι (weakIdealsBelowInclusion R J₀ ⋙ stageBaseChangeDiagram D v) J ≫
        (isoColimitStageBaseChangeBelow D v hR J₀).inv =
      pullback.snd (formalSpectrumInclusion D J.1) v := by
  rw [isoColimitStageBaseChangeBelow, Iso.trans_inv, Iso.symm_inv, ← Category.assoc,
    Functor.Final.ι_colimitIso_hom, ι_isoColimitStageBaseChange_inv]
  rfl

end StageBaseChange

section Completion

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [CommRing A] (f : B →+* A)

/-- **`Spf A^∧` is the colimit of the quotient stages indexed by the weak ideals of definition
of the base contained in a fixed one `J₀`.** -/
noncomputable def colimitIsoFormalSpectrumOfCompletionBelow
    (hB : TopologicalRing.IsWeaklyPreAdmissible B)
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f))
    (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    colimit (weakIdealsBelowInclusion B J₀ ⋙
        (kerProjectionDiagram f ⋙ formalSpectrumDiagram E)) ≅ formalSpectrum E :=
  (Functor.Final.colimitIso (weakIdealsBelowInclusion B J₀)
      (kerProjectionDiagram f ⋙ formalSpectrumDiagram E)).trans
    (colimitIsoFormalSpectrumOfCompletion f hB E)

/-- The leg of `AlgebraicGeometry.FormalSpace.colimitIsoFormalSpectrumOfCompletionBelow` at
`J ⊆ J₀` is the inclusion of the quotient stage `Spec (A ⧸ JA)` into `Spf A^∧`. -/
@[reassoc (attr := simp)]
theorem ι_colimitIsoFormalSpectrumOfCompletionBelow_hom
    (hB : TopologicalRing.IsWeaklyPreAdmissible B)
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f))
    (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex B) (J : WeakIdealsBelow B J₀) :
    colimit.ι (weakIdealsBelowInclusion B J₀ ⋙
          (kerProjectionDiagram f ⋙ formalSpectrumDiagram E)) J ≫
        (colimitIsoFormalSpectrumOfCompletionBelow f hB E J₀).hom =
      formalSpectrumInclusion E ((kerProjectionDiagram f).obj J.1) := by
  rw [colimitIsoFormalSpectrumOfCompletionBelow, Iso.trans_hom, ← Category.assoc,
    Functor.Final.ι_colimitIso_hom, ι_colimitIsoFormalSpectrumOfCompletion_hom]
  rfl

/-- **A sheaf over `Spf B` whose stagewise base changes at the stages below `J₀` are naturally
the quotient stages of `A^∧` is the formal spectrum of `A^∧`.** -/
noncomputable def isoFormalSpectrumOfStageNatIsoBelow
    (hB : TopologicalRing.IsWeaklyPreAdmissible B) (D : QuotientSystem 𝔅 S hS B)
    {V : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))} (v : V ⟶ formalSpectrum D)
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f))
    (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex B)
    (α : weakIdealsBelowInclusion B J₀ ⋙ stageBaseChangeDiagram D v ≅
      weakIdealsBelowInclusion B J₀ ⋙ (kerProjectionDiagram f ⋙ formalSpectrumDiagram E)) :
    V ≅ formalSpectrum E :=
  (isoColimitStageBaseChangeBelow D v hB J₀).trans
    ((HasColimit.isoOfNatIso α).trans (colimitIsoFormalSpectrumOfCompletionBelow f hB E J₀))

end Completion

end Colimit

end AlgebraicGeometry.FormalSpace

end
