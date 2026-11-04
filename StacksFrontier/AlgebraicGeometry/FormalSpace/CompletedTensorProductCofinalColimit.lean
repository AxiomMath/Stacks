module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeColimit
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.QuotientLimit
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.QuotientLimitKernels

/-!
# The quotient stages of a completed tensor product indexed by pairs of weak ideals

Let `A` and `C` be weakly admissible topological algebras over a ring `R`. Sending a pair
`(I, J)` of weak ideals of definition of `A` and of `C` to the kernel of the projection
`A ⊗̂[R] C → A ⧸ I ⊗[R] C ⧸ J` is a functor from the product of the two systems of weak ideals,
each ordered by reverse inclusion, to the weak ideals of definition of `A ⊗̂[R] C`, and that
functor is *final*: every weak ideal of definition of `A ⊗̂[R] C`, being open, contains one of
the projection kernels. Consequently

`Spf (A ⊗̂[R] C) = colim_{I, J} Spec (A ⧸ I ⊗[R] C ⧸ J)`,

the stage at `(I, J)` being `Spec (A ⧸ I ⊗[R] C ⧸ J)` because the projection is surjective with
exactly that kernel.

## Main definitions

* `AlgebraicGeometry.FormalSpace.projectionKernelIndex`: the weak ideal of definition of
  `A ⊗̂[R] C` cut out by a pair of weak ideals of definition of the factors.
* `AlgebraicGeometry.FormalSpace.projectionKernelDiagram`: that assignment as a functor.
* `AlgebraicGeometry.FormalSpace.colimitIsoFormalSpectrumCompletedTensorProduct`:
  `colim_{I, J} Spec ((A ⊗̂[R] C) ⧸ ker) ≅ Spf (A ⊗̂[R] C)`.
* `AlgebraicGeometry.FormalSpace.projectionKernelStageIso`: the stage at `(I, J)` of that
  cofinal subdiagram is `Spec (A ⧸ I ⊗[R] C ⧸ J)`.

## Main results

* `AlgebraicGeometry.FormalSpace.final_projectionKernelDiagram`: the functor is final.

## Implementation notes

The ring-theoretic content is in
`StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.QuotientLimit`:
`TopologicalRing.isWeakIdealOfDefinition_projectionKernel` makes a projection kernel an object
of the target index, `TopologicalRing.projectionKernel_mono` makes the assignment monotone, and
`TopologicalRing.exists_projectionKernel_le` is the cofinality. All that is added here is the
categorical packaging — `CategoryTheory.Functor.final_of_exists_of_isFiltered`, whose second
hypothesis is vacuous because the morphisms of a preorder category form a subsingleton —
together with the transport of the colimit along the functor by
`CategoryTheory.Functor.Final.colimitIso`. This file is the exact analogue, for the completed
tensor product, of
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionCofinalColimit` for a relative completion.

The index is filtered because each factor's weak ideals of definition are directed under
reverse inclusion, the intersection of two of them being one again, and a product of filtered
categories is filtered.

This file is untagged substrate. It is the left-hand side of clause (3) of Stacks 0AN3: the
source's proof of that clause computes `X ×_Z Y` as `colim_{λ, μ} Spec (A/I_λ ⊗_C B/J_μ)` and
then reads off the completed tensor product, and the identification of that colimit with
`Spf (A ⊗̂_C B)` is what is proved here.

## References

* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

variable {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
  [TopologicalSpace A] [TopologicalSpace C] [IsTopologicalRing A] [IsTopologicalRing C]
  [IsLinearTopology A A] [IsLinearTopology C C] [Algebra R A] [Algebra R C]

/-- The weak ideals of definition of a weakly admissible topological ring form a
neighbourhood basis of zero, indexed by the subtype of all of them. This is
`TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition` in the shape the inverse-limit
description of the completed tensor product takes its systems of ideals. -/
theorem hasBasis_weakIdealOfDefinitionIndex {Q : Type u} [CommRing Q] [TopologicalSpace Q]
    [IsTopologicalRing Q] [IsLinearTopology Q Q] (hQ : TopologicalRing.IsWeaklyAdmissible Q) :
    (nhds (0 : Q)).HasBasis
      (fun _ : TopologicalRing.WeakIdealOfDefinitionIndex Q => True)
      (fun i => (i.1 : Set Q)) :=
  (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hQ).to_hasBasis
    (fun _ hI => ⟨⟨_, hI⟩, trivial, subset_rfl⟩) (fun i _ => ⟨i.1, i.2, subset_rfl⟩)

variable (hA : TopologicalRing.IsWeaklyAdmissible A)
  (hC : TopologicalRing.IsWeaklyAdmissible C)

/-- The weak ideal of definition of `A ⊗̂[R] C` cut out by a pair of weak ideals of definition
of the two factors: the kernel of the projection to `A ⧸ I ⊗[R] C ⧸ J`. -/
noncomputable def projectionKernelIndex
    (p : TopologicalRing.WeakIdealOfDefinitionIndex A ×
      TopologicalRing.WeakIdealOfDefinitionIndex C) :
    TopologicalRing.WeakIdealOfDefinitionIndex
      (TopologicalRing.CompletedTensorProduct (R := R) (M := A) (N := C)) :=
  ⟨TopologicalRing.projectionKernel (B := R)
      (fun i : TopologicalRing.WeakIdealOfDefinitionIndex A => i.1)
      (fun j : TopologicalRing.WeakIdealOfDefinitionIndex C => j.1)
      (hasBasis_weakIdealOfDefinitionIndex hA) (hasBasis_weakIdealOfDefinitionIndex hC)
      p.1 p.2,
    TopologicalRing.isWeakIdealOfDefinition_projectionKernel (B := R)
      (fun i : TopologicalRing.WeakIdealOfDefinitionIndex A => i.1)
      (fun j : TopologicalRing.WeakIdealOfDefinitionIndex C => j.1)
      (hasBasis_weakIdealOfDefinitionIndex hA) (hasBasis_weakIdealOfDefinitionIndex hC)
      p.1 p.2 p.1.2 p.2.2⟩

/-- The projection kernels increase with the pair of weak ideals of definition of the
factors. -/
theorem projectionKernelIndex_mono
    {p q : TopologicalRing.WeakIdealOfDefinitionIndex A ×
      TopologicalRing.WeakIdealOfDefinitionIndex C}
    (h₁ : p.1.1 ≤ q.1.1) (h₂ : p.2.1 ≤ q.2.1) :
    (projectionKernelIndex (R := R) hA hC p).1 ≤ (projectionKernelIndex (R := R) hA hC q).1 :=
  TopologicalRing.projectionKernel_mono (B := R)
    (fun i : TopologicalRing.WeakIdealOfDefinitionIndex A => i.1)
    (fun j : TopologicalRing.WeakIdealOfDefinitionIndex C => j.1)
    (hasBasis_weakIdealOfDefinitionIndex hA) (hasBasis_weakIdealOfDefinitionIndex hC) h₁ h₂

/-- The diagram of projection kernels of `A ⊗̂[R] C`, indexed by pairs of weak ideals of
definition of the two factors ordered by reverse inclusion. -/
noncomputable def projectionKernelDiagram :
    (WeakIdeals A × WeakIdeals C) ⥤
      WeakIdeals (TopologicalRing.CompletedTensorProduct (R := R) (M := A) (N := C)) where
  obj p := OrderDual.toDual (projectionKernelIndex hA hC
    (OrderDual.ofDual p.1, OrderDual.ofDual p.2))
  map {_p _q} g := homOfLE (projectionKernelIndex_mono hA hC (leOfHom g.1) (leOfHom g.2))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The ideal underlying the object of `projectionKernelDiagram` at `(I, J)` is the projection
kernel `TopologicalRing.projectionKernel` of `I` and `J`. -/
@[simp]
theorem projectionKernelDiagram_obj_coe (p : WeakIdeals A × WeakIdeals C) :
    ((projectionKernelDiagram hA hC).obj p).1 =
      TopologicalRing.projectionKernel (B := R)
        (fun i : TopologicalRing.WeakIdealOfDefinitionIndex A => i.1)
        (fun j : TopologicalRing.WeakIdealOfDefinitionIndex C => j.1)
        (hasBasis_weakIdealOfDefinitionIndex hA) (hasBasis_weakIdealOfDefinitionIndex hC)
        (OrderDual.ofDual p.1) (OrderDual.ofDual p.2) := rfl

/-- **The projection kernels form a cofinal subdiagram of the canonical diagram of all weak
ideals of definition of `A ⊗̂[R] C`.** Every weak ideal of definition of `A ⊗̂[R] C` is open and
therefore contains one of the projection kernels, which is the cofinality statement
`TopologicalRing.exists_projectionKernel_le`. -/
theorem final_projectionKernelDiagram :
    (projectionKernelDiagram (R := R) hA hC).Final := by
  let _ : IsDirectedOrder (WeakIdeals A) := isDirectedOrder_weakIdeals A
  let _ : IsDirectedOrder (WeakIdeals C) := isDirectedOrder_weakIdeals C
  let _ : Nonempty (WeakIdeals A) := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1
  let _ : Nonempty (WeakIdeals C) := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hC.1
  refine Functor.final_of_exists_of_isFiltered _ (fun K ↦ ?_)
    (fun _ _ ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
  obtain ⟨i, j, hij⟩ := TopologicalRing.exists_projectionKernel_le (B := R)
    (fun i : TopologicalRing.WeakIdealOfDefinitionIndex A => i.1)
    (fun j : TopologicalRing.WeakIdealOfDefinitionIndex C => j.1)
    (hasBasis_weakIdealOfDefinitionIndex hA) (hasBasis_weakIdealOfDefinitionIndex hC)
    (OrderDual.ofDual K).2.1
  exact ⟨(OrderDual.toDual i, OrderDual.toDual j), ⟨homOfLE hij⟩⟩

section Colimit

attribute [local instance] sheaf_hasColimits

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}

/-- **`Spf (A ⊗̂[R] C)` is the colimit of the quotient stages indexed by pairs of weak ideals of
definition of the two factors.** The cofinal subdiagram of
`AlgebraicGeometry.FormalSpace.final_projectionKernelDiagram` computes the colimit of the
canonical diagram, which is the formal spectrum of `A ⊗̂[R] C`. -/
noncomputable def colimitIsoFormalSpectrumCompletedTensorProduct
    (E : QuotientSystem 𝔅 S hS
      (TopologicalRing.CompletedTensorProduct (R := R) (M := A) (N := C))) :
    colimit (projectionKernelDiagram hA hC ⋙ formalSpectrumDiagram E) ≅ formalSpectrum E :=
  have := final_projectionKernelDiagram (R := R) hA hC
  Functor.Final.colimitIso (projectionKernelDiagram hA hC) (formalSpectrumDiagram E)

/-- The colimit inclusion at `p` followed by `colimitIsoFormalSpectrumCompletedTensorProduct`
is the inclusion `formalSpectrumInclusion` of the stage at `p` into the formal spectrum. -/
@[reassoc (attr := simp)]
theorem ι_colimitIsoFormalSpectrumCompletedTensorProduct_hom
    (E : QuotientSystem 𝔅 S hS
      (TopologicalRing.CompletedTensorProduct (R := R) (M := A) (N := C)))
    (p : WeakIdeals A × WeakIdeals C) :
    colimit.ι (projectionKernelDiagram hA hC ⋙ formalSpectrumDiagram E) p ≫
        (colimitIsoFormalSpectrumCompletedTensorProduct hA hC E).hom =
      formalSpectrumInclusion E ((projectionKernelDiagram hA hC).obj p) :=
  have := final_projectionKernelDiagram (R := R) hA hC
  Functor.Final.ι_colimitIso_hom (projectionKernelDiagram hA hC) (formalSpectrumDiagram E) p

/-- **The stage of the cofinal subdiagram at `(I, J)` is `Spec (A ⧸ I ⊗[R] C ⧸ J)`.** Together
with `AlgebraicGeometry.FormalSpace.colimitIsoFormalSpectrumCompletedTensorProduct` this
identifies `Spf (A ⊗̂[R] C)` with `colim_{I, J} Spec (A ⧸ I ⊗[R] C ⧸ J)`. -/
noncomputable def projectionKernelStageIso
    (E : QuotientSystem 𝔅 S hS
      (TopologicalRing.CompletedTensorProduct (R := R) (M := A) (N := C)))
    (p : WeakIdeals A × WeakIdeals C) :
    (BigAffineFppf.toScheme 𝔅 S hS).obj
        ((projectionKernelDiagram hA hC ⋙ E.diagram).obj p) ≅
      Spec (.of ((A ⧸ (OrderDual.ofDual p.1).1) ⊗[R] (C ⧸ (OrderDual.ofDual p.2).1))) :=
  (Scheme.Spec.mapIso (TopologicalRing.projectionKernelQuotientRingEquiv (B := R)
    (fun i : TopologicalRing.WeakIdealOfDefinitionIndex A => i.1)
    (fun j : TopologicalRing.WeakIdealOfDefinitionIndex C => j.1)
    (hasBasis_weakIdealOfDefinitionIndex hA) (hasBasis_weakIdealOfDefinitionIndex hC)
    (OrderDual.ofDual p.1) (OrderDual.ofDual p.2)).toCommRingCatIso.op).symm

end Colimit

end AlgebraicGeometry.FormalSpace

end
