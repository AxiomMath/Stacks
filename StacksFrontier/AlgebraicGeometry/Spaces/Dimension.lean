module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.GermPropertyAtPoint

/-!
# Dimension of an algebraic space, at a point and globally

The dimension of an algebraic space at a point is the local dimension of an étale scheme
chart at any point lying over it, and the dimension of the algebraic space is the supremum of
its dimensions at points.

## Main definitions

* `AlgebraicGeometry.Space.dimensionAtPoint` is the dimension of an algebraic space at one of
  its points.
* `AlgebraicGeometry.Space.dimension` is the dimension of an algebraic space.

## Main results

* `AlgebraicGeometry.Space.exists_etale_chart_at_point` supplies an étale scheme chart above
  each point, so that the set whose infimum defines the dimension at a point is nonempty.
* `AlgebraicGeometry.Space.dimensionAtPoint_eq_of_etale_chart` is the characterization the
  source states: the dimension at a point equals the local dimension of *every* étale scheme
  chart at a point above it, so the choice of chart is immaterial.

## Implementation notes

Points of the algebraic space are classes of field-valued points (Tag 03BU), and a point of
a chart `U` above `x` is a field-valued point of `yoneda.obj U` whose class maps to `x`. The
scheme point it selects is `AlgebraicGeometry.Space.schemePoint`.

The source defines the dimension at a point as *the* value shared by all the étale charts at
that point. That is realized here by taking the infimum of the local dimensions over all such
charts, and then proving in `dimensionAtPoint_eq_of_etale_chart` that each one of them equals
the infimum; the two together are the content of the definition. The proof applies the chart
equivalence of Tag 04N2 to the property of germs "the local dimension is `d`", which is étale
local because an étale morphism of schemes preserves the local dimension (Tag 04N4): a
representative of an étale morphism of germs is étale on an open neighbourhood of the point,
and the inclusion of that neighbourhood is étale as well.

Both values lie in `WithBot ℕ∞`, which is the codomain of the project's local dimension of a
topological space, `topologicalKrullDimAt` of Tag 0055 (4). In particular an algebraic space
with no points has dimension `⊥`.

The algebraic-space hypothesis is an argument of both definitions. It is not used in either
body — the infimum and the supremum are meaningful for an arbitrary presheaf — but without it
the characterization has no content, since a presheaf with no étale chart above `x` would get
the empty infimum. Carrying it in the definition is what lets a client write
`dimension B S hS F hF = 0` directly.

`dimension` is an abbreviation so that clients reach the supremum, and the order API on
`WithBot ℕ∞`, without an unfolding lemma.

## References

* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 04N5.** The dimension of an algebraic space at one of its points: the infimum of
the local dimensions of the étale scheme charts at a point above it. By
`AlgebraicGeometry.Space.dimensionAtPoint_eq_of_etale_chart` every one of those local
dimensions equals this infimum. -/
@[stacks 04N5 "dimension at a point"]
noncomputable def dimensionAtPoint (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) : WithBot ℕ∞ :=
  sInf {d : WithBot ℕ∞ | ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a ∧
    ∃ p : FieldValuedPoint B S hS (yoneda.obj U),
      pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x ∧
      topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U)
        (schemePoint B S hS U p) = d}

/-- **Stacks 04N5.** Every point of an algebraic space has an étale scheme chart above it. -/
@[stacks 04N5 "existence of a chart at the point"]
theorem exists_etale_chart_at_point (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) :
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      ∃ p : FieldValuedPoint B S hS (yoneda.obj U),
        pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x := by
  obtain ⟨U, a, hsurj, ha⟩ := hF.exists_atlas
  obtain ⟨q, hq⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U a).mp hsurj x
  obtain ⟨p, rfl⟩ := Quot.exists_rep q
  exact ⟨U, a, ha, p, hq⟩

/-- **Stacks 04N5.** The dimension of an algebraic space at a point equals the local
dimension of every étale scheme chart at a point above it; this is the property the source
uses to define the dimension at a point. -/
@[stacks 04N5 "independence of the étale chart"]
theorem dimensionAtPoint_eq_of_etale_chart (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ F)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (hp : pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x) :
    dimensionAtPoint B S hS F hF x =
      topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U)
        (schemePoint B S hS U p) := by
  let d := topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U)
    (schemePoint B S hS U p)
  let P : GermOfScheme.{u} → Prop := fun Z ↦ topologicalKrullDimAt Z.scheme Z.point = d
  have hP : GermOfScheme.IsEtaleLocal P := by
    rintro X Y f ⟨r, -, her⟩
    have : Etale r.hom := her
    let xU : r.source.toScheme := ⟨X.point, r.mem_source⟩
    have hUX := topologicalKrullDimAt_eq_of_etale (Scheme.Opens.ι r.source) xU
    have hUS := topologicalKrullDimAt_eq_of_etale r.hom xU
    rw [show (Scheme.Opens.ι r.source) xU = X.point by simp [xU, Scheme.Opens.ι_apply]] at hUX
    rw [r.map_point] at hUS
    show (topologicalKrullDimAt Y.scheme Y.point = d) ↔
      (topologicalKrullDimAt X.scheme X.point = d)
    rw [← hUS, ← hUX]
  have hall := (forall_etale_chart_iff_exists_etale_chart B S hS F hF x P hP).2
    ⟨U, a, ha, p, hp, rfl⟩
  unfold dimensionAtPoint
  refine le_antisymm (sInf_le ⟨U, a, ha, p, hp, rfl⟩) (le_sInf ?_)
  rintro e ⟨V, b, hb, q, hq, rfl⟩
  exact (hall V b hb q hq).ge

/-- **Stacks 04N6.** The dimension of an algebraic space: the supremum of its dimensions at
its points. -/
@[stacks 04N6]
noncomputable abbrev dimension (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) : WithBot ℕ∞ :=
  ⨆ x : points B S hS F, dimensionAtPoint B S hS F hF x

end AlgebraicGeometry.Space

end
