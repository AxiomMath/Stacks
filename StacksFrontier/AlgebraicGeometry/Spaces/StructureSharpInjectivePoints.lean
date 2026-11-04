module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# A base change whose direct image of functions is nonzero has a point

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and `V` an étale scheme chart
of `Y`.  If the structure map `𝒪_Y(V) ⟶ (f_*𝒪_X)(V)` is injective and `𝒪_Y(V)` is a nonzero
ring, then the algebraic space `X ×_Y V` has a point: the sections of `f_*𝒪_X` over `V` embed in
the regular functions on any surjective étale atlas `U` of `X ×_Y V`
(`AlgebraicGeometry.Space.injective_directImageChartProjection_of_singleton_covering`), and an
empty `U` has only the zero ring of functions.

This is the step of the proof of Stacks 0D2C showing that `𝒪_T ≅ f_{T, *}𝒪_{X_T}` for every
scheme `T` over the base forces `f` to be surjective; it carries no `@[stacks]` attribute.

## Main results

* `AlgebraicGeometry.Space.nonempty_points_chartBaseChangeSpace`.

## References

* [Stacks Project, Tag 0D2C](https://stacks.math.columbia.edu/tag/0D2C)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **If `𝒪_Y(V) ⟶ (f_*𝒪_X)(V)` is injective and `𝒪_Y(V)` is nonzero, then `X ×_Y V` has a
point.** -/
theorem nonempty_points_chartBaseChangeSpace (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (hV : Nontrivial ((structureRingSheaf B S hS Y).obj.obj (op V)))
    (hf : Function.Injective ((structureSharp B S hS f).hom.app (op V))) :
    Nonempty (points B S hS (chartBaseChangeSpace B S hS f V).obj) := by
  obtain ⟨T, a, hsurj, hetale⟩ := (chartBaseChangeSpace B S hS f V).property.exists_atlas
  let c₀ : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj :=
    ⟨CostructuredArrow.mk a, hetale⟩
  have hc₀ : IsSurjective B S hS c₀.obj.hom :=
    (surjective_iff_surjective_pointsMap B S hS (chartBaseChangeSpace B S hS f V).obj
      (chartBaseChangeSpace B S hS f V).property T a).1 hsurj
  have hinj := injective_directImageChartProjection_of_singleton_covering B S hS f V
    (baseChangeSpaceChartIndex B S hS f V c₀)
    (singleton_baseChangeSpaceChartHom_mem_topology B S hS f V c₀ hc₀)
  by_contra hne
  rw [not_nonempty_iff] at hne
  have hT : IsEmpty ((BigFppfOver.toScheme B S hS).obj T) :=
    ⟨fun t ↦ hne.elim (pointsMap B S hS _ a ((pointsEquivScheme B S hS T).symm t))⟩
  have hsub : Subsingleton ((structureSetSheaf B S hS X).obj.obj
      (baseChangeSpaceChartIndex B S hS f V c₀).right) :=
    inferInstanceAs (Subsingleton Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
  have hinj' : Function.Injective
      ((directImageChartProjectionRingHom B S hS f V
          (baseChangeSpaceChartIndex B S hS f V c₀)).hom ∘
        (structureSharp B S hS f).hom.app (op V)) :=
    hinj.comp hf
  obtain ⟨x, y, hxy⟩ := hV
  exact hxy (hinj' (hsub.elim _ _))

end AlgebraicGeometry.Space

end
