module

public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionLimit
public import StacksFrontier.AlgebraicGeometry.Limits.SeparatedStage
public import StacksCore.Tactic.StacksAttribute

/-!
# Closed embedding into a separated scheme of finite presentation

A separated morphism of finite type onto a quasi-compact, quasi-separated scheme factors as a
closed immersion followed by a morphism that is separated and of finite presentation.

## Main results

* `AlgebraicGeometry.exists_isClosedImmersion_into_isSeparated_finitePresentation`: the
  factorisation.

## Implementation notes

Finite type is expressed by `LocallyOfFiniteType` together with `QuasiCompact`, and finite
presentation by `AlgebraicGeometry.FinitePresentation`.

Without separatedness the factorisation is
`AlgebraicGeometry.exists_finitePresentation_closedImmersion`, and the content here is that the
ambient scheme can be chosen separated over the base as well. The closed immersion into that
ambient scheme is, by `AlgebraicGeometry.exists_isLimit_closedImmersion_finitePresentation`, the
limit of a directed inverse system of closed immersions of finite presentation with affine
transition morphisms; the composite system maps to the base, the limit of that system is the
original separated morphism, and so
`AlgebraicGeometry.eventually_isSeparated_of_isLimit` makes some stage of the system separated
over the base. That stage is the required ambient scheme, and the projection of the limit onto
it is a closed immersion because its composite with the stage's own closed immersion is one.

## References

* [Stacks Project, Tag 01ZJ](https://stacks.math.columbia.edu/tag/01ZJ)
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- A separated morphism of finite type onto a quasi-compact, quasi-separated scheme factors as
a closed immersion followed by a separated morphism of finite presentation. -/
@[stacks 01ZJ]
theorem exists_isClosedImmersion_into_isSeparated_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (X' : Scheme.{u}) (f' : X' ⟶ S) (i : X ⟶ X'),
      IsSeparated f' ∧ FinitePresentation f' ∧ IsClosedImmersion i ∧ i ≫ f' = f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨Y, q, i, hq, hi, hcomp⟩ := exists_finitePresentation_closedImmersion f
  have : LocallyOfFinitePresentation q := hq.locallyOfFinitePresentation
  have : QuasiCompact q := hq.quasiCompact
  have : QuasiSeparated q := hq.quasiSeparated
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated q
  have : IsClosedImmersion i := hi
  obtain ⟨I, _, _, _, D, tY, p, hc, hbaseY, hstage⟩ :=
    exists_isLimit_closedImmersion_finitePresentation i
  let t : D ⟶ (Functor.const Iᵒᵖ).obj S := tY ≫ (Functor.const Iᵒᵖ).map q
  have hcl (j : Iᵒᵖ) : IsClosedImmersion (tY.app j) := (hstage j).1
  have hfpj (j : Iᵒᵖ) : LocallyOfFinitePresentation (tY.app j) :=
    (hstage j).2.locallyOfFinitePresentation
  have : ∀ j, CompactSpace (D.obj j) := fun j ↦
    @QuasiCompact.compactSpace_of_compactSpace _ Y (tY.app j) inferInstance inferInstance
  have : ∀ j, QuasiSeparatedSpace (D.obj j) := fun j ↦
    @quasiSeparatedSpace_of_quasiSeparated _ Y (tY.app j) inferInstance inferInstance
  have : ∀ {j k : Iᵒᵖ} (g : j ⟶ k), IsAffineHom (D.map g) := fun {j k} g ↦ by
    have hmap : D.map g ≫ tY.app k = tY.app j := by simp [tY.naturality g]
    have : IsClosedImmersion (D.map g ≫ tY.app k) := by rw [hmap]; infer_instance
    have : IsClosedImmersion (D.map g) := IsClosedImmersion.of_comp (D.map g) (tY.app k)
    infer_instance
  have hproj (j : Iᵒᵖ) : p.app j ≫ tY.app j = i := by
    simpa using congrArg (fun α ↦ α.app j) hbaseY
  have hbase : p ≫ t = (Functor.const Iᵒᵖ).map f := by
    ext j
    change p.app j ≫ tY.app j ≫ q = f
    rw [← Category.assoc, hproj, hcomp]
  obtain ⟨i₀, hi₀⟩ := eventually_isSeparated_of_isLimit D t (Cone.mk X p) hc f hbase
  have hfp : FinitePresentation (t.app (Opposite.op i₀)) := by
    change FinitePresentation (tY.app (Opposite.op i₀) ≫ q)
    exact FinitePresentation.mk
      (locallyOfFinitePresentation_comp (tY.app (Opposite.op i₀)) q) inferInstance inferInstance
  have : IsClosedImmersion (p.app (Opposite.op i₀) ≫ tY.app (Opposite.op i₀)) := by
    rw [hproj]; infer_instance
  refine ⟨D.obj (Opposite.op i₀), t.app (Opposite.op i₀), p.app (Opposite.op i₀), hi₀ i₀ le_rfl,
    hfp, IsClosedImmersion.of_comp _ (tY.app (Opposite.op i₀)), ?_⟩
  simpa using congrArg (fun α ↦ α.app (Opposite.op i₀)) hbase

end AlgebraicGeometry

end
