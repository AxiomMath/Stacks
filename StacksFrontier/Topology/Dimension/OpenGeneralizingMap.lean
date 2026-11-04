module

public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Krull dimension along an open generalizing map

Let `f : X → Y` be a continuous map of topological spaces which collapses no specialization:
whenever `a ⤳ b` and `f a = f b`, already `a = b`. Such a map does not raise the Krull
dimension. If moreover `f` is open and generalizations lift along it, then `f` matches the
Krull dimension of every open subset of `X` with that of its image, and hence the local Krull
dimension at every point of `X` with that at its image.

The hypothesis of collapsing no specialization is what makes these statements true; without it
they fail, a constant map of a space of positive dimension to a point being the simplest
counterexample. It is strictly weaker than injectivity, and it is the form in which the
hypothesis arises in practice, where `f` is a chart and the points it identifies are known to
be incomparable.

## Main results

* `Topology.topologicalKrullDim_le_of_injOn_specializes`: a continuous map of a quasi-sober
  space to a Kolmogorov space which collapses no specialization does not raise the Krull
  dimension.
* `Topology.topologicalKrullDim_image_eq_of_isOpen`: an open generalizing map which collapses
  no specialization matches the Krull dimension of an open set with that of its image.
* `Topology.topologicalKrullDimAt_eq_of_isOpenMap_of_generalizingMap`: the same at the level of
  the local Krull dimension at a point.

## Implementation notes

The first result is the direction that needs the hypothesis on specializations: a strict chain
of irreducible closed subsets of the source is replaced by its chain of generic points, which
maps to a chain of points of the target, and the closures of the images still form a *strict*
chain — were two equal, the two generic points would be specializations of one another, hence
equal by the hypothesis, contradicting strictness upstairs.

The reverse inequality needs no such hypothesis and is
`Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap`, applied
to the restriction of `f` to an open set, which is surjective onto its image and still
generalizing because an open set is stable under the generalizations it receives.

The statement at a point is the infimum over open neighbourhoods of the two statements about
open sets. Each family is cofinal in the other: a neighbourhood `V` of `f a` contributes
`f ⁻¹' V`, and a neighbourhood `W` of `a` contributes `f '' W`, which is open because `f` is.

The invariant here is the *local* dimension, and it should not be confused with the coheight of
a point in the specialization order, for which `Order.coheight_eq_of_strictMono` and
`Topology.IsOpenEmbedding.coheight_eq` are available and these results are not needed. The two
differ: at a closed point of `Spec ℤ` the coheight is `0`, nothing specializing it strictly,
while the local dimension is `1`, every open neighbourhood of it containing the generic point.
The hypotheses below are the same two that the coheight statement consumes — no collapsing of
specializations, and lifting of generizations — but the conclusions are about different
quantities, and neither statement follows from the other.
-/

@[expose] public section

open TopologicalSpace

namespace Topology

/-- A continuous map of a quasi-sober space to a Kolmogorov space which identifies no two
distinct points one of which specializes the other does not raise the Krull dimension: the
generic points of a strict chain of irreducible closed subsets of the source map to a chain of
points whose closures still form a strict chain. -/
theorem topologicalKrullDim_le_of_injOn_specializes
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober X] [T0Space Y]
    (f : X → Y) (hf : Continuous f)
    (hnc : ∀ ⦃a b : X⦄, a ⤳ b → f a = f b → a = b) :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  unfold topologicalKrullDim
  simp only [Order.krullDim]
  refine iSup_le fun p ↦ ?_
  let y : Fin (p.length + 1) → X := fun i ↦ (p.toFun i).isIrreducible'.genericPoint
  have hy : ∀ i, IsGenericPoint (y i) (p.toFun i).carrier := fun i ↦
    (p.toFun i).isIrreducible'.isGenericPoint_genericPoint (p.toFun i).isClosed'
  let z : Fin (p.length + 1) → Y := fun i ↦ f (y i)
  have hz : ∀ i : Fin p.length, z i.succ ⤳ z i.castSucc := fun i ↦
    (specializes_succ_castSucc_of_isGenericPoint p y hy i).map hf
  have hstrict (i : Fin p.length) :
      IrreducibleCloseds.closureSingleton (z i.castSucc) <
        IrreducibleCloseds.closureSingleton (z i.succ) := by
    refine lt_of_le_of_ne ?_ ?_
    · rw [← SetLike.coe_subset_coe, IrreducibleCloseds.coe_closureSingleton,
        IrreducibleCloseds.coe_closureSingleton]
      exact closure_minimal
        (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp (hz i))) isClosed_closure
    · intro heq
      have heq' : closure ({z i.castSucc} : Set Y) = closure {z i.succ} :=
        congrArg (fun Z : IrreducibleCloseds Y ↦ (Z : Set Y)) heq
      have hback : z i.castSucc ⤳ z i.succ := by
        rw [specializes_iff_mem_closure, heq']
        exact subset_closure rfl
      have hyEq : y i.succ = y i.castSucc :=
        hnc (specializes_succ_castSucc_of_isGenericPoint p y hy i)
          (hback.antisymm (hz i)).eq.symm
      have hcar : (p.toFun i.castSucc).carrier = (p.toFun i.succ).carrier := by
        rw [← hy i.castSucc, ← hy i.succ, hyEq.symm]
      exact (ne_of_lt (p.step i)) (IrreducibleCloseds.ext hcar)
  exact le_iSup (fun r : LTSeries (IrreducibleCloseds Y) ↦ (r.length : WithBot ℕ∞))
    { length := p.length
      toFun := fun i ↦ IrreducibleCloseds.closureSingleton (z i)
      step := hstrict }

/-- An open generalizing map between quasi-sober spaces which identifies no two distinct points
one of which specializes the other, the target being Kolmogorov, matches the Krull dimension of
every open subset of the source with that of its image. -/
theorem topologicalKrullDim_image_eq_of_isOpen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] [QuasiSober Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) (hop : IsOpenMap f) (hlift : GeneralizingMap f)
    (hnc : ∀ ⦃a b : X⦄, a ⤳ b → f a = f b → a = b)
    {W : Set X} (hW : IsOpen W) :
    topologicalKrullDim (↥W) = topologicalKrullDim (↥(f '' W)) := by
  have : QuasiSober (↥W) := hW.isOpenEmbedding_subtypeVal.quasiSober
  have : QuasiSober (↥(f '' W)) := (hop W hW).isOpenEmbedding_subtypeVal.quasiSober
  let g : ↥W → ↥(f '' W) := fun a ↦ ⟨f a.1, ⟨a.1, a.2, rfl⟩⟩
  have hgcont : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, ⟨a, ha, rfl⟩⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hglift : GeneralizingMap g := by
    intro a y hspec
    obtain ⟨a', ha', hfa'⟩ := hlift ((subtype_specializes_iff y (g a)).mp hspec)
    exact ⟨⟨a', ha'.mem_open hW a.2⟩,
      (subtype_specializes_iff _ a).mpr ha', Subtype.ext hfa'⟩
  have hgnc : ∀ ⦃a b : ↥W⦄, a ⤳ b → g a = g b → a = b := fun a b hab heq ↦
    Subtype.ext (hnc ((subtype_specializes_iff a b).mp hab) (congrArg Subtype.val heq))
  exact le_antisymm (topologicalKrullDim_le_of_injOn_specializes g hgcont hgnc)
    (topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap
      g hgcont hgsurj (Or.inr hglift))

/-- An open generalizing map between quasi-sober spaces which identifies no two distinct points
one of which specializes the other, the target being Kolmogorov, preserves the local Krull
dimension at every point. -/
theorem topologicalKrullDimAt_eq_of_isOpenMap_of_generalizingMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] [QuasiSober Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) (hop : IsOpenMap f) (hlift : GeneralizingMap f)
    (hnc : ∀ ⦃a b : X⦄, a ⤳ b → f a = f b → a = b) (a : X) :
    topologicalKrullDimAt X a = topologicalKrullDimAt Y (f a) := by
  unfold topologicalKrullDimAt
  refine le_antisymm (le_iInf fun V ↦ ?_) (le_iInf fun W ↦ ?_)
  · calc (⨅ W : {W : Set X // a ∈ W ∧ IsOpen W}, topologicalKrullDim (↥W.val))
        ≤ topologicalKrullDim (↥(f ⁻¹' V.1)) :=
          iInf_le _ (⟨f ⁻¹' V.1, V.2.1, V.2.2.preimage hf⟩ :
            {W : Set X // a ∈ W ∧ IsOpen W})
      _ = topologicalKrullDim (↥(f '' (f ⁻¹' V.1))) :=
          topologicalKrullDim_image_eq_of_isOpen f hf hop hlift hnc (V.2.2.preimage hf)
      _ ≤ topologicalKrullDim (↥V.1) :=
          (IsEmbedding.inclusion
            (Set.image_preimage_subset f V.1)).isInducing.topologicalKrullDim_le
  · calc (⨅ V : {V : Set Y // f a ∈ V ∧ IsOpen V}, topologicalKrullDim (↥V.val))
        ≤ topologicalKrullDim (↥(f '' W.1)) :=
          iInf_le _ (⟨f '' W.1, ⟨a, W.2.1, rfl⟩, hop W.1 W.2.2⟩ :
            {V : Set Y // f a ∈ V ∧ IsOpen V})
      _ = topologicalKrullDim (↥W.1) :=
          (topologicalKrullDim_image_eq_of_isOpen f hf hop hlift hnc W.2.2).symm

end Topology

end
