module

public import StacksFrontier.AlgebraicGeometry.Modules.AffineSpanOfGeneratingSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparisonIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalChartFunctoriality

/-!
# Global sections of a chart restriction come from sections over the chart, compatibly with
restriction to the Zariski opens

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `𝓕` be an
`𝒪_X`-module on the small étale site and let `A` be an étale scheme chart of `X`.  The Zariski
restriction `𝓕|_A = AlgebraicGeometry.Space.restrictToChartScheme` of `𝓕` to the scheme of `A`
has two kinds of sections in play in the proof of Stacks 0GUT:

* its **global** sections `Γ(𝓕|_A, ⊤)`, which is where a generating family produced on the chart
  scheme by Stacks 01Q3 (7) lives; and
* its sections over a Zariski open `O` of `chartScheme A`, which
  `AlgebraicGeometry.Space.chartSectionsToRestrict` identifies with the sections of `𝓕` over the
  étale chart `AlgebraicGeometry.Space.openChart` that `O` cuts out.

The hypothesis `hgen` of
`AlgebraicGeometry.Space.spanSieve_moduleFMapSpanningSet_mem_of_span_chartSectionsToRestrict`
asks for a family of sections of `𝓕` **over the chart `A`** whose readings in the second sense
span, over every affine open of `chartScheme A`.  A generating family produced on the chart
scheme arrives in the first sense.  This file is the passage between the two: it reads a section
over the chart as a global section of the chart restriction, shows that every global section
arises this way, and — this is the point — identifies the restriction of that global section to
a Zariski open `O` with the reading over `O` of the restriction of the section to the chart that
`O` cuts out.

## Main definitions

* `AlgebraicGeometry.Space.chartTopRead`: the global section of `𝓕|_A` attached to a section of
  `𝓕` over the chart `A`, through `AlgebraicGeometry.Space.chartSectionsToRestrict` at the open
  `⊤`.

## Main results

* `AlgebraicGeometry.Space.chartTopRead_restrict`: **the restriction to a Zariski open `O` of
  the global section attached to `s` is the reading over `O` of the restriction of `s` to the
  étale chart `O` cuts out.**
* `AlgebraicGeometry.Space.surjective_chartTopRead`: **every global section of the chart
  restriction is attached to a section of `𝓕` over the chart.**
* `AlgebraicGeometry.Space.mem_span_chartSectionsToRestrict_of_mem_span_chartTopRead` and
  `AlgebraicGeometry.Space.exists_chartSections_mem_span_chartSectionsToRestrict`: **the
  hypothesis `hgen` of
  `AlgebraicGeometry.Space.spanSieve_moduleFMapSpanningSet_mem_of_span_chartSectionsToRestrict`,
  from a spanning statement about global sections of the chart restriction.**
* `AlgebraicGeometry.Space.exists_chartSections_hgen_of_generatingSections`: **that hypothesis
  from a family of global sections generating the chart restriction**, which is the shape
  Stacks 01Q3 (7) produces on the chart's scheme.

## Hypotheses carried, and why

None beyond the data: no quasi-coherence, no finiteness, no affineness.  Both
`AlgebraicGeometry.Space.chartSectionsToRestrict` and its naturality and bijectivity hold for an
arbitrary `𝒪_X`-module, and the chart cut out by the open `⊤` is the chart itself for purely
formal reasons.  The hypothesis `IsAffineOpen O` appears in the two `hgen`-shaped statements only
because it appears in the statement they are built to feed; it is not used.

## Implementation notes

Everything rests on three facts about the second reading and on nothing about
sheafification:

* `AlgebraicGeometry.Space.chartSectionsToRestrict_naturality`, which moves the reading along an
  inclusion of Zariski opens at the cost of restricting the section along the induced morphism of
  étale charts `AlgebraicGeometry.Space.openChartHomOfLE`;
* `AlgebraicGeometry.Space.openChartHomOfLE_comp_openChartInclusion`, which says that morphism is
  a morphism over the ambient chart, so that the two restrictions of a section of `𝓕` over `A`
  agree;
* `AlgebraicGeometry.Space.isIso_openChartInclusion_top`, which makes the chart cut out by `⊤`
  the chart itself and so makes the reading at `⊤` surjective, the reading itself being bijective
  by `AlgebraicGeometry.Space.bijective_chartSectionsToRestrict`.

The reading at `⊤` is *not* `AlgebraicGeometry.Space.chartRestrictionTopSection`: that one is
built from `AlgebraicGeometry.Space.chartOpens` and `AlgebraicGeometry.Space.chartOpensTopHom`
and lands in `AlgebraicGeometry.Space.restrictToChart`, which is the parallel restriction of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionReadingsIso.lean`, equal to
`restrictToChartScheme` as a module but on the far side of the definitional obstruction those
notes record.  Staying inside the `openChart` reading is what makes the restriction identity
`AlgebraicGeometry.Space.chartTopRead_restrict` a two-line consequence of naturality rather than
a comparison of two index functors.

No declaration here carries a `stacks` tag: these are chart transports consumed by the proofs of
Stacks 0GUT and Stacks 0GUU, not assertions of either tag.

## References

* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS X.1 X.2)

/-- **The global section of the chart restriction `𝓕|_A` attached to a section of `𝓕` over the
étale chart `A`**: restrict the section to the chart cut out by the open `⊤` of `chartScheme A`
and read it there through `AlgebraicGeometry.Space.chartSectionsToRestrict`. -/
def chartTopRead (A : SmallEtale B S hS X.1) (s : M.val.obj (op A)) :
    (restrictToChartScheme B S hS X.1 X.2 M A).val.obj (op (⊤ : (chartScheme A).Opens)) :=
  chartSectionsToRestrict X M A ⊤ (M.val.map (openChartInclusion B S hS X.1 A ⊤).op s)

/-- Two successive restrictions of a section of a presheaf of modules are the restriction along
any morphism equal to the composite. -/
private theorem map_map_apply_of_comp_eq {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    (N : PresheafOfModules R) {U V W : Cᵒᵖ} {i : U ⟶ V} {j : V ⟶ W} {k : U ⟶ W}
    (e : i ≫ j = k) (x : N.obj U) : N.map j (N.map i x) = N.map k x := by
  rw [← PresheafOfModules.map_comp_apply, e]

/-- **The restriction to a Zariski open of the global section attached to a section over the
chart is the reading of that section over the chart the open cuts out.**

The reading is natural in the Zariski open
(`AlgebraicGeometry.Space.chartSectionsToRestrict_naturality`), at the cost of restricting the
section along `AlgebraicGeometry.Space.openChartHomOfLE`; and that morphism of charts composed
with the inclusion of the chart cut out by `⊤` is the inclusion of the chart cut out by the open
(`AlgebraicGeometry.Space.openChartHomOfLE_comp_openChartInclusion`), so the two restrictions of
the section agree. -/
theorem chartTopRead_restrict (A : SmallEtale B S hS X.1) (O : (chartScheme A).Opens)
    (s : M.val.obj (op A)) :
    (restrictToChartScheme B S hS X.1 X.2 M A).val.map
        (homOfLE (le_top : O ≤ ⊤)).op (chartTopRead X M A s) =
      chartSectionsToRestrict X M A O
        (M.val.map (openChartInclusion B S hS X.1 A O).op s) := by
  refine Eq.trans (chartSectionsToRestrict_naturality X M A (homOfLE (le_top : O ≤ ⊤))
    (M.val.map (openChartInclusion B S hS X.1 A ⊤).op s))
    (congrArg (chartSectionsToRestrict X M A O) ?_)
  have e : (openChartInclusion B S hS X.1 A ⊤).op ≫
      ((openChartFunctor B S hS X.1 A).map (homOfLE (le_top : O ≤ ⊤))).op =
      (openChartInclusion B S hS X.1 A O).op :=
    congrArg Quiver.Hom.op
      (openChartHomOfLE_comp_openChartInclusion B S hS X.1 A (le_top : O ≤ ⊤))
  exact map_map_apply_of_comp_eq M.val e s

/-- **Every global section of the chart restriction comes from a section of `𝓕` over the
chart.**  The reading over a Zariski open is bijective
(`AlgebraicGeometry.Space.bijective_chartSectionsToRestrict`) and the chart cut out by `⊤` is the
chart itself (`AlgebraicGeometry.Space.isIso_openChartInclusion_top`). -/
theorem surjective_chartTopRead (A : SmallEtale B S hS X.1) :
    Function.Surjective (chartTopRead X M A) := by
  have := isIso_openChartInclusion_top B S hS X.1 A
  intro t
  obtain ⟨x, hx⟩ := (bijective_chartSectionsToRestrict X M A ⊤).2 t
  refine ⟨M.val.map (inv (openChartInclusion B S hS X.1 A ⊤)).op x, ?_⟩
  have hh : (inv (openChartInclusion B S hS X.1 A ⊤)).op ≫
      (openChartInclusion B S hS X.1 A ⊤).op = 𝟙 _ := by
    rw [← op_comp, IsIso.hom_inv_id, op_id]
  have e : M.val.map (openChartInclusion B S hS X.1 A ⊤).op
      (M.val.map (inv (openChartInclusion B S hS X.1 A ⊤)).op x) = x :=
    (map_map_apply_of_comp_eq M.val hh x).trans
      (ConcreteCategory.congr_hom (M.val.presheaf.map_id _) x)
  exact (congrArg (chartSectionsToRestrict X M A ⊤) e).trans hx

/-- **The span of the readings over a Zariski open, from the span of the restrictions of the
attached global sections.**  The two spanning families are equal, member by member, by
`AlgebraicGeometry.Space.chartTopRead_restrict`. -/
theorem mem_span_chartSectionsToRestrict_of_mem_span_chartTopRead
    (A : SmallEtale B S hS X.1) {I : Type*} (a : I → M.val.obj (op A))
    (O : (chartScheme A).Opens)
    {y : (restrictToChartScheme B S hS X.1 X.2 M A).val.obj (op O)}
    (hy : y ∈ Submodule.span ((chartScheme A).ringCatSheaf.obj.obj (op O))
      (Set.range fun i => (restrictToChartScheme B S hS X.1 X.2 M A).val.map
        (homOfLE (le_top : O ≤ ⊤)).op (chartTopRead X M A (a i)))) :
    y ∈ Submodule.span ((chartScheme A).ringCatSheaf.obj.obj (op O))
      (Set.range fun i => chartSectionsToRestrict X M A O
        (M.val.map (openChartInclusion B S hS X.1 A O).op (a i))) :=
  funext (fun i => chartTopRead_restrict X M A O (a i)) ▸ hy

/-- **The hypothesis `hgen` of
`AlgebraicGeometry.Space.spanSieve_moduleFMapSpanningSet_mem_of_span_chartSectionsToRestrict`,
from a spanning statement about global sections of the chart restriction.**

If finitely or infinitely many *global* sections of `𝓕|_A` have the property that their
restrictions span the sections of `𝓕|_A` over every affine open of `chartScheme A`, then there is
a family of sections of `𝓕` over the étale chart `A`, indexed by the same type, whose readings
over every affine open of `chartScheme A` span there.  That is exactly the shape the epimorphism
criterion consumes, with the index type and its cardinality unchanged.

The sections over the chart are produced by
`AlgebraicGeometry.Space.surjective_chartTopRead` and the spanning statement is transported by
`AlgebraicGeometry.Space.mem_span_chartSectionsToRestrict_of_mem_span_chartTopRead`. -/
theorem exists_chartSections_mem_span_chartSectionsToRestrict (A : SmallEtale B S hS X.1)
    {I : Type*} (t : I → (restrictToChartScheme B S hS X.1 X.2 M A).val.obj
      (op (⊤ : (chartScheme A).Opens)))
    (hgen : ∀ O : (chartScheme A).Opens, IsAffineOpen O →
      ∀ y : (restrictToChartScheme B S hS X.1 X.2 M A).val.obj (op O),
        y ∈ Submodule.span ((chartScheme A).ringCatSheaf.obj.obj (op O))
          (Set.range fun i => (restrictToChartScheme B S hS X.1 X.2 M A).val.map
            (homOfLE (le_top : O ≤ ⊤)).op (t i))) :
    ∃ a : I → M.val.obj (op A), ∀ O : (chartScheme A).Opens, IsAffineOpen O →
      ∀ y : (restrictToChartScheme B S hS X.1 X.2 M A).val.obj (op O),
        y ∈ Submodule.span ((chartScheme A).ringCatSheaf.obj.obj (op O))
          (Set.range fun i => chartSectionsToRestrict X M A O
            (M.val.map (openChartInclusion B S hS X.1 A O).op (a i))) := by
  refine ⟨fun i => (surjective_chartTopRead X M A (t i)).choose, fun O hO y => ?_⟩
  refine mem_span_chartSectionsToRestrict_of_mem_span_chartTopRead X M A _ O ?_
  refine funext (fun i => congrArg
    ((restrictToChartScheme B S hS X.1 X.2 M A).val.map (homOfLE (le_top : O ≤ ⊤)).op)
    ((surjective_chartTopRead X M A (t i)).choose_spec)) ▸ hgen O hO y

/-- **The hypothesis `hgen` of
`AlgebraicGeometry.Space.spanSieve_moduleFMapSpanningSet_mem_of_span_chartSectionsToRestrict`,
from a family of global sections generating the chart restriction.**

Let `𝓕` be a quasi-coherent `𝒪_X`-module and let the Zariski restriction `𝓕|_A` of `𝓕` to the
scheme of an étale chart `A` be generated by a family of global sections — the shape in which
Stacks 01Q3 (7) hands over its output on the chart's scheme.  Then there is a family of sections
of `𝓕` over the étale chart `A`, indexed by the same type, whose readings over every affine open
of `chartScheme A` span the sections of `𝓕|_A` there.

The two inputs are global generation spanning the sections over an affine open, which is the
`H¹`-vanishing half of Stacks 01XB
(`Stacks.AffineSpanOfGeneratingSections.mem_span_restrict_top_of_generatingSections`), and
`AlgebraicGeometry.Space.exists_chartSections_mem_span_chartSectionsToRestrict`.
Quasi-coherence of `𝓕` is what makes `𝓕|_A` quasi-coherent, which the first input needs. -/
theorem exists_chartSections_hgen_of_generatingSections (A : SmallEtale B S hS X.1)
    (hM : M.IsQuasicoherentOnSite)
    (σ : (restrictToChartScheme B S hS X.1 X.2 M A).GeneratingSections) :
    ∃ a : σ.I → M.val.obj (op A), ∀ O : (chartScheme A).Opens, IsAffineOpen O →
      ∀ y : (restrictToChartScheme B S hS X.1 X.2 M A).val.obj (op O),
        y ∈ Submodule.span ((chartScheme A).ringCatSheaf.obj.obj (op O))
          (Set.range fun i => chartSectionsToRestrict X M A O
            (M.val.map (openChartInclusion B S hS X.1 A O).op (a i))) := by
  have : SheafOfModules.IsQuasicoherent (restrictToChartScheme B S hS X.1 X.2 M A) :=
    restrictToChart_eq_restrictToChartScheme B S hS X.2 M A ▸
      isQuasicoherent_restrictToChart B S hS X M hM A
  exact exists_chartSections_mem_span_chartSectionsToRestrict X M A
    (fun i => (σ.s i).eval (op ⊤))
    (fun O hO y =>
      Stacks.AffineSpanOfGeneratingSections.mem_span_restrict_top_of_generatingSections
        (restrictToChartScheme B S hS X.1 X.2 M A) σ O hO y)

end AlgebraicGeometry.Space

end
