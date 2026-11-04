module

public import StacksFrontier.AlgebraicGeometry.ProductFamilyRatio.Basic

/-!
# A linear projection out of one standard chart of projective space

Let `M` be an invertible `𝒪_X`-module, let `P₀, …, P_N` be global sections of `M` generating it
and let `q : X ⟶ ℙᴺ_S` be the morphism of [Stacks, Tag 01NE] they pin. Fix one index `i`. On the
`i`-th standard chart `D₊(Tᵢ)` of `ℙᴺ_S` any family of regular functions spanning the unit ideal
defines a morphism to projective space over `S`
(`Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse` followed by
`Stacks.AmpleProjectiveImmersion.liftOver`), and composing the chart restriction of `q` with it
gives a morphism `X_{Pᵢ} ⟶ ℙᵐ_S`. This file records when that composite is the chart restriction
of a second pinned morphism, and the immersion property it then transports.

## Main definitions

* `Stacks.LinearChartProjection.chartProjOf`: a morphism `D₊(Tᵢ) ⟶ ℙᵐ_S` over `S` from a family
  of regular functions on the chart spanning the unit ideal.

## Main results

* `Stacks.LinearChartProjection.resLE_comp_chartProjOf`: the chart restriction of `q` followed by
  the projection is the restriction of `j`, as soon as the chart's ring map carries the projection
  family to the coordinate ratios of the family pinning `j`.
* `Stacks.LinearChartProjection.isImmersion_ι_comp_of_chart`: if the restriction of `j` to
  `X_{Pᵢ}` is an immersion, so is the restriction of `q`.
* `Stacks.LinearChartProjection.isImmersion_of_comp_forall`: a morphism is an immersion if, locally
  on its target, its composite with some morphism is an immersion.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 02V0](https://stacks.math.columbia.edu/tag/02V0)
* [Stacks Project, Tag 07RK](https://stacks.math.columbia.edu/tag/07RK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.AmpleProjectiveImmersion
open Stacks.SectionsToProjectiveSpace

universe u

namespace Stacks.LinearChartProjection

variable {X S : Scheme.{u}} {N m : ℕ}

/-- The morphism over `S` from the `i`-th standard chart `D₊(Tᵢ)` of `ℙᴺ_S` to `ℙᵐ_S` attached to
a family of regular functions on that chart spanning the unit ideal. For a family of linear forms
divided by `Tᵢ` this is a linear projection. -/
def chartProjOf (i : Fin (N + 1))
    (h : Fin (m + 1) → Γ((projectiveSpaceOver.standardChart N S i).toScheme, ⊤))
    (hh : Ideal.span (Set.range h) = ⊤) :
    (projectiveSpaceOver.standardChart N S i).toScheme ⟶ projectiveSpaceOver m S :=
  liftOver ((projectiveSpaceOver.standardChart N S i).ι ≫
      pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} N)))
    (toProjectiveSpaceAtUniverse h hh)

variable {M : X.Modules} [IsInvertibleModule X M] {M' : X.Modules} [IsInvertibleModule X M']

/-- Let `q : X ⟶ ℙᴺ_S` be pinned over `f` by a family `P` and let `j : X ⟶ ℙᵐ_S` be pinned over
`f` by a family `s`. If the ring map of the `i`-th chart of `q` carries a family `h` of regular
functions on `D₊(Tᵢ)` to the coordinate ratios `s_{α'}/s_α` of the second family, then on `X_{Pᵢ}`
the chart restriction of `q` followed by `Stacks.LinearChartProjection.chartProjOf` is the
restriction of `j`. -/
theorem resLE_comp_chartProjOf
    (P : Fin (N + 1) → Γ(M, ⊤)) (s : Fin (m + 1) → Γ(M', ⊤)) {f : X ⟶ S}
    (q : X ⟶ projectiveSpaceOver N S)
    (hqf : q ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} N)) = f)
    (j : X ⟶ projectiveSpaceOver m S)
    (hjf : j ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} m)) = f)
    (i : Fin (N + 1)) (α : Fin (m + 1))
    (hjchart : (nvCover s α).ι ≫ j ≫ projectiveSpaceOver.toIntegralAtUniverse m S =
      toProjectiveSpaceAtUniverse (chartRatio s α) (span_range_chartRatio s α))
    (hle : nvCover P i ≤ nvCover s α)
    (e : nvCover P i ≤ q ⁻¹ᵁ projectiveSpaceOver.standardChart N S i)
    (h : Fin (m + 1) → Γ((projectiveSpaceOver.standardChart N S i).toScheme, ⊤))
    (hh : Ideal.span (Set.range h) = ⊤)
    (hpull : ∀ α' : Fin (m + 1),
      (q.resLE (projectiveSpaceOver.standardChart N S i) (nvCover P i) e).appTop (h α') =
        (X.homOfLE hle).appTop (chartRatio s α α')) :
    q.resLE (projectiveSpaceOver.standardChart N S i) (nvCover P i) e ≫ chartProjOf i h hh =
      (nvCover P i).ι ≫ j := by
  have hspan1 : Ideal.span (Set.range fun α' =>
      (q.resLE (projectiveSpaceOver.standardChart N S i) (nvCover P i) e).appTop (h α')) = ⊤ :=
    Stacks.SectionsToProjectiveSpace.span_range_comp _ _ hh
  have hspan2 : Ideal.span
      (Set.range fun α' => (X.homOfLE hle).appTop (chartRatio s α α')) = ⊤ :=
    Stacks.SectionsToProjectiveSpace.span_range_comp _ _ (span_range_chartRatio s α)
  refine pullback.hom_ext ?_ ?_ <;> simp only [Category.assoc]
  · rw [show chartProjOf i h hh ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} m)) =
        (projectiveSpaceOver.standardChart N S i).ι ≫
          pullback.fst (terminal.from S)
            (terminal.from (projectiveSpaceAtUniverse.{u} N)) from liftOver_fst _ _,
      hjf, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hqf]
  · rw [show chartProjOf i h hh ≫ projectiveSpaceOver.toIntegralAtUniverse m S =
        toProjectiveSpaceAtUniverse h hh from liftOver_snd _ _,
      Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _ hspan1,
      toProjectiveSpaceAtUniverse_congr (funext hpull) hspan1 hspan2,
      ← Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _
        (span_range_chartRatio s α) hspan2, ← hjchart, ← Category.assoc, Scheme.homOfLE_ι]

/-- In the situation of `Stacks.LinearChartProjection.resLE_comp_chartProjOf`, if the restriction
of `j` to `X_{Pᵢ}` is an immersion then so is the restriction of `q`. -/
theorem isImmersion_ι_comp_of_chart
    (P : Fin (N + 1) → Γ(M, ⊤)) (s : Fin (m + 1) → Γ(M', ⊤)) {f : X ⟶ S}
    (q : X ⟶ projectiveSpaceOver N S)
    (hqf : q ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} N)) = f)
    (j : X ⟶ projectiveSpaceOver m S)
    (hjf : j ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} m)) = f)
    (i : Fin (N + 1)) (α : Fin (m + 1))
    (hjchart : (nvCover s α).ι ≫ j ≫ projectiveSpaceOver.toIntegralAtUniverse m S =
      toProjectiveSpaceAtUniverse (chartRatio s α) (span_range_chartRatio s α))
    (hle : nvCover P i ≤ nvCover s α)
    (e : nvCover P i ≤ q ⁻¹ᵁ projectiveSpaceOver.standardChart N S i)
    (h : Fin (m + 1) → Γ((projectiveSpaceOver.standardChart N S i).toScheme, ⊤))
    (hh : Ideal.span (Set.range h) = ⊤)
    (hpull : ∀ α' : Fin (m + 1),
      (q.resLE (projectiveSpaceOver.standardChart N S i) (nvCover P i) e).appTop (h α') =
        (X.homOfLE hle).appTop (chartRatio s α α'))
    (himm : IsImmersion ((nvCover P i).ι ≫ j)) :
    IsImmersion ((nvCover P i).ι ≫ q) := by
  have : IsImmersion
      (q.resLE (projectiveSpaceOver.standardChart N S i) (nvCover P i) e ≫
        chartProjOf i h hh) := by
    rwa [resLE_comp_chartProjOf P s q hqf j hjf i α hjchart hle e h hh hpull]
  have := IsImmersion.of_comp
    (q.resLE (projectiveSpaceOver.standardChart N S i) (nvCover P i) e) (chartProjOf i h hh)
  rw [← q.resLE_comp_ι e]
  infer_instance

/-- If every point of `X` has an open `V` of `Y` around its image under `q` and a morphism
`Θ : Y ⟶ Y'` such that the restriction of `q ≫ Θ` to `q⁻¹(V)` is an immersion, then `q` is an
immersion. -/
theorem isImmersion_of_comp_forall {Y : Scheme.{u}} (q : X ⟶ Y)
    (H : ∀ x : X, ∃ (Y' : Scheme.{u}) (Θ : Y ⟶ Y') (V : Y.Opens), q.base x ∈ V ∧
      IsImmersion ((q ⁻¹ᵁ V).ι ≫ q ≫ Θ)) :
    IsImmersion q := by
  have hrr : MorphismProperty.RespectsRight (@IsImmersion) (@IsOpenImmersion) :=
    ⟨fun i hi g hg => by
      have : IsOpenImmersion i := hi
      have : IsImmersion g := hg
      infer_instance⟩
  have hop : MorphismProperty.HasOfPostcompProperty (@IsImmersion) (@IsOpenImmersion) :=
    ⟨fun g i _ hgi => MorphismProperty.HasOfPostcompProperty.of_postcomp
      (W := @IsImmersion) (W' := (⊤ : MorphismProperty Scheme)) g i trivial hgi⟩
  apply IsZariskiLocalAtTarget.of_forall_source_exists_preimage (P := @IsImmersion) q
  intro x
  obtain ⟨Y', Θ, V, hx, himm⟩ := H x
  refine ⟨V, hx, ?_⟩
  have : IsImmersion (((q ⁻¹ᵁ V).ι ≫ q) ≫ Θ) := by rwa [Category.assoc]
  exact IsImmersion.of_comp _ Θ

end Stacks.LinearChartProjection

end
