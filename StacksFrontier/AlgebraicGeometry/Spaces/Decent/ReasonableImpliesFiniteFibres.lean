module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.BoundedPointFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Conditions

/-!
# Reasonable algebraic spaces have finite chart and relation fibres

Let `X` be an algebraic space over a scheme `S`. If `X` is reasonable — condition `(δ)` of
Stacks 03JX, that every étale chart of `X` by an affine scheme has universally bounded
fibres — then above every point of `|X|` both such a chart and its self-intersection have
finite fibres. This is condition `(γ)` of Stacks 03JX, so the file supplies the implication
`(δ) ⇒ (γ)` of that tag.

## Main results

* `AlgebraicGeometry.Space.hasFiniteChartAndRelationFibersAtEveryPoint_of_isReasonableSpace`
  is the implication `(δ) ⇒ (γ)` of Stacks 03JX.

## Implementation notes

For an affine étale chart `φ : h_U ⟶ X` the relation `R = h_U ×_X h_U` is the pullback of
`φ` along itself, so Stacks 03JN presents `R` by an object of the site and shows that its
projection to `h_U` again has universally bounded fibres. Stacks 03JQ then makes every fibre
of `|R| → |U|` and every fibre of `|U| → |X|` finite, and the fibre of `|R| → |X|` above a
point is the preimage under `|R| → |U|` of the fibre of `|U| → |X|` there; a preimage of a
finite set under a map with finite fibres is finite.

The source argument instead bounds the fibres of `R → X` universally, by Stacks 03JM, and
only then passes to point sets. Composing the two finiteness statements on point sets avoids
that step, and the conclusion is the same.

Condition `(γ)` is taken, as in `AlgebraicGeometry.Space.HasFiniteChartAndRelationFibersAt`,
in the form of condition (1) of Stacks 03JV. It is therefore not literally
`AlgebraicGeometry.Space.IsDecentSpace`, which spells the definition of a decent space with
condition (4) of that tag; the two agree once the equivalences of Stacks 03JV are available,
and nothing here uses that identification.

## References

* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03JN](https://stacks.math.columbia.edu/tag/03JN)
* [Stacks Project, Tag 03JQ](https://stacks.math.columbia.edu/tag/03JQ)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The map on points induced by the inverse of an isomorphism of presheaves is injective. -/
private theorem injective_pointsMap_inv {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    Function.Injective (pointsMap B S hS G e.inv) := by
  intro a b h
  have h' : pointsMap B S hS G (e.inv ≫ e.hom) a = pointsMap B S hS G (e.inv ≫ e.hom) b := by
    rw [pointsMap_comp_apply, pointsMap_comp_apply, h]
  rwa [e.inv_hom_id, pointsMap_id, id_eq] at h'

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 03JX, `(δ) ⇒ (γ)`.** A reasonable algebraic space satisfies condition `(γ)`:
above every point of it, every étale chart by an affine scheme has a finite fibre, and so
does the self-intersection of that chart. -/
@[stacks 03JX "(delta) implies (gamma)"]
theorem hasFiniteChartAndRelationFibersAtEveryPoint_of_isReasonableSpace
    (hX : IsAlgebraicSpace B S hS X) (hr : IsReasonableSpace B S hS X) :
    HasFiniteChartAndRelationFibersAtEveryPoint B S hS X := by
  intro x U hU φ hφ
  have hbound : HasUniversallyBoundedFibers B S hS U φ := hr U hU φ hφ
  have hchart : (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x}).Finite :=
    finite_pointFiber_of_hasUniversallyBoundedFibers B S hS U φ hbound x
  refine ⟨hchart, ?_⟩
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hrepr : yoneda.relativelyRepresentable φ :=
    Functor.relativelyRepresentable.diag_iff.1 hX.diagonal_representable φ
  obtain ⟨V, i, p, hpb, hVbound⟩ :=
    hasUniversallyBoundedFibers_baseChange B S hS φ hrepr U φ hbound
  set e := hpb.flip.isoPullback
  have he : e.hom ≫ pullback.fst φ φ = p := hpb.flip.isoPullback_hom_fst
  have hinv : e.inv ≫ p = pullback.fst φ φ := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hfibre : ∀ y : points B S hS (yoneda.obj U),
      (pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) ⁻¹' {y}).Finite := by
    intro y
    have hV : (pointsMap B S hS (yoneda.obj V) p ⁻¹' {y}).Finite :=
      finite_pointFiber_of_hasUniversallyBoundedFibers B S hS V p hVbound y
    refine Set.Finite.subset
      (hV.preimage ((injective_pointsMap_inv B S hS e).injOn)) fun z hz ↦ ?_
    have hzy : pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) z = y :=
      Set.mem_singleton_iff.mp (Set.mem_preimage.mp hz)
    refine Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr ?_)
    rw [← pointsMap_comp_apply, hinv, hzy]
  rw [show pointsMap B S hS (pullback φ φ) (pullback.fst φ φ ≫ φ) =
      pointsMap B S hS (yoneda.obj U) φ ∘
        pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) from
    pointsMap_comp B S hS _ _ _, Set.preimage_comp]
  exact hchart.preimage' fun y _ ↦ hfibre y

end AlgebraicGeometry.Space

end
