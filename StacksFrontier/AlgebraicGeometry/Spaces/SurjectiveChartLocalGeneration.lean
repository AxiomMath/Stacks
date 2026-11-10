module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartTerminalSectionsSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart

/-!
# Local generation of a quasi-coherent module is detected on one surjective étale chart

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `N` be a
quasi-coherent `𝒪_X`-module on the small étale site and let `T` be a family of local sections of
`N`.  Say that a section *is locally spanned by `T`* if it restricts, along the members of a
covering sieve of the small étale site, into the `𝒪_X`-span of the restrictions of members of
`T` — that is, if the sieve `Stacks.SheafOfModules.spanSieve N T` of that section is a covering
sieve.  This file proves that this condition, which is a condition on *every* étale chart of
`X`, follows from its restriction to the Zariski opens of a *single* étale chart `U` whose
structure morphism is surjective:

**if every section of `N` over an affine open of `chartScheme U` is locally spanned by `T`, then
so is every section of `N` over every étale chart of `X`.**

That is the step the epimorphism criterion
`AlgebraicGeometry.Space.epi_of_spanSieve_moduleFMapSpanningSet_mem` is missing: the criterion
demands the span sieve to be covering over *every* chart, whereas generation is produced over one
surjective chart only.

## Main results

* `AlgebraicGeometry.Space.mem_submodule_of_forall_mem_of_isAffine_hom`: **a presheaf submodule
  of a quasi-coherent module which contains every section over an affine étale chart contains
  every section over any affine étale chart mapping to it.**  This is the forward half of Stacks
  03DX (2) read on submodules.
* `AlgebraicGeometry.Space.spanSieve_mem_of_affineOpens_of_isSurjective`: **local generation is
  detected on the affine opens of one surjective étale chart.**
* `AlgebraicGeometry.Space.spanSieve_mem_of_mem_spanSubmodule_affineOpens_of_isSurjective`: the
  same with the hypothesis in the sharper form "lies in the span", not "lies locally in the
  span".
* `AlgebraicGeometry.Space.spanSieve_mem_of_span_chartSectionsToRestrict_of_isSurjective`:
  **sections over a surjective étale chart whose readings generate the Zariski chart restriction
  locally span every section of `N`.**  This is the hypothesis in the form a generation statement
  on the chart *scheme* produces.
* `AlgebraicGeometry.Space.spanSieve_moduleFMapSpanningSet_mem_of_span_chartSectionsToRestrict`:
  the same conclusion in the shape
  `AlgebraicGeometry.Space.epi_of_spanSieve_moduleFMapSpanningSet_mem` consumes, for the values
  of the chartwise transpose of a morphism out of a module pullback.

## Implementation notes

The two reductions are both applications of the sheaf condition of
`Stacks.SheafOfModules.localSpan N T`, the subsheaf of sections lying locally in the span, whose
membership is by `Stacks.SheafOfModules.mem_localSpan_iff` exactly the covering of the span
sieve.

The first reduction is `AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`: a chart
with surjective structure morphism covers the final object of the small étale site, so every
chart is covered by charts admitting a morphism to `U`.

The second replaces such a chart `Z` by the affine opens of `chartScheme Z` lying over an affine
open of `chartScheme U`, which cover `chartScheme Z` because the affine opens of a scheme form a
basis; `AlgebraicGeometry.Space.ofArrows_openChartInclusion_mem_topology` turns that Zariski
cover into a covering sieve of `Z`, and
`AlgebraicGeometry.Space.openChartHomOfLE_comp_openChartRestrict_comp_openChartInclusion` is the
factorisation of the resulting chart over the affine open of `chartScheme U`.

What makes the passage from one affine chart to another work is the forward half of Stacks
03DX (2), `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isQuasicoherentOnSite`: over a
morphism of affine étale charts the sections of a quasi-coherent module base change, so by
`AlgebraicGeometry.Space.chartBaseChange_surjective_iff_span_eq_top` the restrictions of the
sections over the larger chart span the sections over the smaller one.  No comparison with the
Zariski chart restriction is needed for that; the comparison enters only in the last two results,
where the generation hypothesis is read through
`AlgebraicGeometry.Space.chartSectionsToRestrict`.

Affineness of both charts is an input of Stacks 03DX (2) and not a restriction that could be
dropped: for `U = Spec k[x, y]`, `V = U ∖ {(x, y)}` and `G` the module of sections of
`𝒪_U/(x, y)` one has `G(V) = 0` while `𝒪(V) ⊗_{𝒪(U)} G(U) = k`.  That is why the covering of a
chart `Z` by *affine* opens over *affine* opens of `chartScheme U` is taken, rather than `Z`
itself being compared with `U`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX), the chart criterion for
  quasi-coherence.
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0), a surjective étale chart
  covers the final object of the small étale site.
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH), epimorphisms of sheaves
  of modules are the locally surjective morphisms.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Transport of a submodule between affine charts -/

section Affine

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **A presheaf submodule of a quasi-coherent module which contains every section over an affine
étale chart contains every section over any affine étale chart mapping to it.**

By the forward half of Stacks 03DX (2) the sections over the smaller chart are the base change of
the sections over the larger one, so they are spanned by the restrictions of the latter
(`AlgebraicGeometry.Space.chartBaseChange_surjective_iff_span_eq_top`); those restrictions lie in
the submodule because it is stable under restriction. -/
theorem mem_submodule_of_forall_mem_of_isAffine_hom (N : Modules.{u, u} B S hS F hF)
    (hN : N.IsQuasicoherentOnSite) (K : N.val.Submodule)
    {A A' : SmallEtale B S hS F} (m : A' ⟶ A)
    (hA : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj A))
    (hA' : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj A'))
    (hfull : ∀ w : N.val.obj (op A), w ∈ K.obj (op A)) (z : N.val.obj (op A')) :
    z ∈ K.obj (op A') := by
  let _ := chartAlgebra (hF := hF) m
  have hspan := (chartBaseChange_surjective_iff_span_eq_top N m).1
    (bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS F hF N hN hA hA' m).2
  have hle : Submodule.span (chartRing B S hS F hF A')
      (Set.range fun w : N.val.obj (op A) => chartRestrictLinear N m w) ≤ K.obj (op A') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    exact K.map_mem m.op (hfull w)
  exact hle (hspan.ge Submodule.mem_top)

end Affine

/-! ### Local generation from one surjective chart -/

section Site

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    (N : Modules.{u, u} B S hS F hF) (T : ∀ W : (SmallEtale B S hS F)ᵒᵖ, Set (N.val.obj W))

/-- The affine opens of `chartScheme Z` lying inside the preimage of an affine open of
`chartScheme U` cover `chartScheme Z`: the affine opens of a scheme form a basis of its
topology, so a point of `chartScheme Z` lies in one inside the preimage of an affine open
neighbourhood of its image. -/
theorem iSup_affineOpens_le_preimage_affineOpens_eq_top {Z U : SmallEtale B S hS F}
    (c : Z ⟶ U) :
    ⨆ p : {p : (chartScheme Z).affineOpens × (chartScheme U).affineOpens //
        p.1.1 ≤ chartSchemeMap c ⁻¹ᵁ p.2.1}, (p.1.1.1 : (chartScheme Z).Opens) = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨O, hO, hzO, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
    (chartScheme U).isBasis_affineOpens (TopologicalSpace.Opens.mem_top (chartSchemeMap c z))
  obtain ⟨O', hO', hzO', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
    (chartScheme Z).isBasis_affineOpens (U := chartSchemeMap c ⁻¹ᵁ O) hzO
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨O', hO'⟩, ⟨O, hO⟩), hle⟩, hzO'⟩

/-- Every section of `N` over an étale chart admitting a morphism to `U` lies locally in the span
of `T`, as soon as every section over an affine open of `chartScheme U` does.

The chart is covered by the affine opens of its chart scheme which lie over an affine open of
`chartScheme U`, and over each of those
`AlgebraicGeometry.Space.mem_submodule_of_forall_mem_of_isAffine_hom` carries the hypothesis across
the factorisation of the chart over the affine open of `chartScheme U`. -/
theorem mem_localSpan_of_hom_of_affineOpens (hN : N.IsQuasicoherentOnSite)
    {U : SmallEtale B S hS F}
    (hgen : ∀ O : (chartScheme U).Opens, IsAffineOpen O →
      ∀ w : N.val.obj (op (openChart B S hS F U O)),
        Stacks.SheafOfModules.spanSieve N T w ∈
          SmallEtale.topology B S hS F (openChart B S hS F U O))
    {Z : SmallEtale B S hS F} (c : Z ⟶ U) (y : N.val.obj (op Z)) :
    y ∈ (Stacks.SheafOfModules.localSpan N T).obj (op Z) := by
  refine (Stacks.SheafOfModules.localSpan N T).isSheaf y ?_
  refine (SmallEtale.topology B S hS F).superset_covering ?_
    (ofArrows_openChartInclusion_mem_topology B S hS F Z
      (fun p : {p : (chartScheme Z).affineOpens × (chartScheme U).affineOpens //
          p.1.1 ≤ chartSchemeMap c ⁻¹ᵁ p.2.1} => (p.1.1.1 : (chartScheme Z).Opens))
      (iSup_affineOpens_le_preimage_affineOpens_eq_top c))
  intro V h hh
  obtain ⟨p, k, rfl⟩ := Sieve.ofArrows.exists hh
  have hA : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj
      (openChart B S hS F U p.1.2.1)) := p.1.2.2
  have hA' : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj
      (openChart B S hS F Z p.1.1.1)) := p.1.1.2
  have hmem : ∀ z : N.val.obj (op (openChart B S hS F Z p.1.1.1)),
      z ∈ (Stacks.SheafOfModules.localSpan N T).obj (op (openChart B S hS F Z p.1.1.1)) :=
    mem_submodule_of_forall_mem_of_isAffine_hom N hN
      (Stacks.SheafOfModules.localSpan N T).toSubmodule
      (openChartHomOfLE B S hS F Z p.2 ≫ openChartRestrict B S hS F c p.1.2.1) hA hA'
      (fun w => (Stacks.SheafOfModules.mem_localSpan_iff w).2 (hgen p.1.2.1 p.1.2.2 w))
  change N.val.map ((openChartInclusion B S hS F Z p.1.1.1).op ≫ k.op) y ∈
    (Stacks.SheafOfModules.localSpan N T).obj (op V)
  exact Eq.mpr
    (congrArg (· ∈ (Stacks.SheafOfModules.localSpan N T).obj (op V))
      (PresheafOfModules.map_comp_apply N.val
        (openChartInclusion B S hS F Z p.1.1.1).op k.op y))
    ((Stacks.SheafOfModules.localSpan N T).map_mem k.op (hmem _))

/-- **Local generation of a quasi-coherent module is detected on the affine opens of one
surjective étale chart.**  Let `N` be a quasi-coherent `𝒪_X`-module, `T` a family of local
sections of `N` and `U` an étale chart whose structure morphism is surjective.  If every section
of `N` over an affine open of `chartScheme U` restricts into the `𝒪_X`-span of the restrictions
of members of `T` along a covering sieve, then so does every section of `N` over every étale
chart.

The chart `U` covers the final object of the small étale site by Stacks 03M0
(`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`), so every chart is covered by
charts admitting a morphism to `U`, over which
`AlgebraicGeometry.Space.mem_localSpan_of_hom_of_affineOpens` applies. -/
theorem spanSieve_mem_of_affineOpens_of_isSurjective (hN : N.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS F) (hU : IsSurjective B S hS U.1.hom)
    (hgen : ∀ O : (chartScheme U).Opens, IsAffineOpen O →
      ∀ w : N.val.obj (op (openChart B S hS F U O)),
        Stacks.SheafOfModules.spanSieve N T w ∈
          SmallEtale.topology B S hS F (openChart B S hS F U O))
    (W : SmallEtale B S hS F) (x : N.val.obj (op W)) :
    Stacks.SheafOfModules.spanSieve N T x ∈ SmallEtale.topology B S hS F W := by
  refine (Stacks.SheafOfModules.mem_localSpan_iff x).1
    ((Stacks.SheafOfModules.localSpan N T).isSheaf x ?_)
  refine (SmallEtale.topology B S hS F).superset_covering ?_
    (SmallEtale.coversTop_of_isSurjective B S hS F hF U hU W)
  rintro Z f ⟨_, ⟨c⟩⟩
  exact mem_localSpan_of_hom_of_affineOpens N T hN hgen c _

/-- **Local generation of a quasi-coherent module is detected on the affine opens of one
surjective étale chart**, with the hypothesis in the sharper form: it is enough that every
section of `N` over an affine open of `chartScheme U` lie in the span of the restrictions of
members of `T` *over that chart*, with no further covering. -/
theorem spanSieve_mem_of_mem_spanSubmodule_affineOpens_of_isSurjective
    (hN : N.IsQuasicoherentOnSite) (U : SmallEtale B S hS F)
    (hU : IsSurjective B S hS U.1.hom)
    (hgen : ∀ O : (chartScheme U).Opens, IsAffineOpen O →
      ∀ w : N.val.obj (op (openChart B S hS F U O)),
        w ∈ (Stacks.SheafOfModules.spanSubmodule N T).obj (op (openChart B S hS F U O)))
    (W : SmallEtale B S hS F) (x : N.val.obj (op W)) :
    Stacks.SheafOfModules.spanSieve N T x ∈ SmallEtale.topology B S hS F W :=
  spanSieve_mem_of_affineOpens_of_isSurjective N T hN U hU
    (fun O hO w => (SmallEtale.topology B S hS F).superset_covering
      (fun _ i _ => (Stacks.SheafOfModules.spanSubmodule N T).map_mem i.op (hgen O hO w))
      ((SmallEtale.topology B S hS F).top_mem _)) W x

end Site

/-! ### Generation read on the chart scheme -/

section Zariski

variable {X : AlgebraicSpaces B S hS} (N : Modules.{u, u} B S hS X.1 X.2)
    (T : ∀ W : (SmallEtale B S hS X.1)ᵒᵖ, Set (N.val.obj W))

/-- **A section of `N` over the étale chart cut out by a Zariski open `O` of a chart scheme lies
in the span of a family of local sections as soon as its reading does.**  Precisely: if the
readings over `O` of the restrictions of sections `a i` of `N` over the chart `U` span the
sections of the Zariski chart restriction `N|_U` over `O`, and each `a i` belongs to the family
`T`, then every section of `N` over `openChart U O` lies in the span of `T`.

The readings of the span of `T` form a submodule of the sections of `N|_U` over `O`
(`AlgebraicGeometry.Space.chartSectionsToRestrict_smul` makes it stable under multiplication by
functions, every function on `O` being a function on the étale chart by
`AlgebraicGeometry.Space.surjective_chartSchemeRestrictionRingHom_app`) which contains the
spanning family, hence the whole span; and the reading of sections is injective
(`AlgebraicGeometry.Space.bijective_chartSectionsToRestrict`). -/
theorem mem_spanSubmodule_of_span_chartSectionsToRestrict (U : SmallEtale B S hS X.1)
    (O : (chartScheme U).Opens) {I : Type*} (a : I → N.val.obj (op U))
    (ha : ∀ i, a i ∈ T (op U))
    (hgen : ∀ y : (restrictToChartScheme B S hS X.1 X.2 N U).val.obj (op O),
      y ∈ Submodule.span ((chartScheme U).ringCatSheaf.obj.obj (op O))
        (Set.range fun i => chartSectionsToRestrict X N U O
          (N.val.map (openChartInclusion B S hS X.1 U O).op (a i))))
    (w : N.val.obj (op (openChart B S hS X.1 U O))) :
    w ∈ (Stacks.SheafOfModules.spanSubmodule N T).obj (op (openChart B S hS X.1 U O)) := by
  set cs := chartSectionsToRestrict X N U O
  set Q := (Stacks.SheafOfModules.spanSubmodule N T).obj (op (openChart B S hS X.1 U O))
  let P : Submodule ((chartScheme U).ringCatSheaf.obj.obj (op O))
      ((restrictToChartScheme B S hS X.1 X.2 N U).val.obj (op O)) :=
    { carrier := {y | ∃ z ∈ Q, cs z = y}
      zero_mem' := ⟨0, Submodule.zero_mem _, map_zero cs⟩
      add_mem' := fun {_ _} ⟨z, hz, e⟩ ⟨z', hz', e'⟩ =>
        ⟨z + z', Submodule.add_mem _ hz hz', by rw [map_add, e, e']⟩
      smul_mem' := fun r _ ⟨z, hz, e⟩ =>
        ⟨(show chartRing B S hS X.1 X.2 (openChart B S hS X.1 U O) from
            ((chartSchemeRestrictionRingHom B S hS X.1 U).app (op O)).hom r) • z,
          Submodule.smul_mem _ _ hz, by
            rw [← e]
            exact chartSectionsToRestrict_smul X N U O r z⟩ }
  have hle : Submodule.span ((chartScheme U).ringCatSheaf.obj.obj (op O))
      (Set.range fun i => cs (N.val.map (openChartInclusion B S hS X.1 U O).op (a i))) ≤ P :=
    Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact ⟨_, Stacks.SheafOfModules.map_mem_spanSubmodule (T := T)
        (openChartInclusion B S hS X.1 U O).op (ha i), rfl⟩)
  obtain ⟨z, hz, e⟩ := hle (hgen (cs w))
  exact (bijective_chartSectionsToRestrict X N U O).1 e ▸ hz

/-- **Sections over a surjective étale chart whose readings generate the Zariski chart
restriction locally span every section of `N`.**  Let `N` be a quasi-coherent `𝒪_X`-module, `T` a
family of local sections of `N`, and `U` an étale chart whose structure morphism is surjective.
Suppose given sections `a i` of `N` over `U`, members of `T`, whose readings over every affine
open `O` of `chartScheme U` span the sections of the Zariski chart restriction `N|_U` over `O`.
Then every section of `N` over every étale chart of `X` restricts, along a covering sieve, into
the `𝒪_X`-span of the restrictions of members of `T`.

The index type of the generating family is arbitrary: finiteness is not used. -/
theorem spanSieve_mem_of_span_chartSectionsToRestrict_of_isSurjective
    (hN : N.IsQuasicoherentOnSite) (U : SmallEtale B S hS X.1)
    (hU : IsSurjective B S hS U.1.hom) {I : Type*} (a : I → N.val.obj (op U))
    (ha : ∀ i, a i ∈ T (op U))
    (hgen : ∀ O : (chartScheme U).Opens, IsAffineOpen O →
      ∀ y : (restrictToChartScheme B S hS X.1 X.2 N U).val.obj (op O),
        y ∈ Submodule.span ((chartScheme U).ringCatSheaf.obj.obj (op O))
          (Set.range fun i => chartSectionsToRestrict X N U O
            (N.val.map (openChartInclusion B S hS X.1 U O).op (a i))))
    (W : SmallEtale B S hS X.1) (x : N.val.obj (op W)) :
    Stacks.SheafOfModules.spanSieve N T x ∈ SmallEtale.topology B S hS X.1 W :=
  spanSieve_mem_of_mem_spanSubmodule_affineOpens_of_isSurjective N T hN U hU
    (fun O hO => mem_spanSubmodule_of_span_chartSectionsToRestrict N T U O a ha (hgen O hO)) W x

end Zariski

/-! ### The hypothesis of the epimorphism criterion -/

section Pullback

variable {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')
    (M : Modules.{u, u} B S hS X'.1 X'.2) (N : Modules.{u, u} B S hS X.1 X.2)

/-- **The hypothesis of `AlgebraicGeometry.Space.epi_of_spanSieve_moduleFMapSpanningSet_mem`,
from generation over one surjective étale chart.**

Let `g : X ⟶ X'` be a morphism of algebraic spaces, `M` an `𝒪_{X'}`-module, `N` a quasi-coherent
`𝒪_X`-module and `u : g^*M ⟶ N` a morphism, with chartwise transpose
`ξ = AlgebraicGeometry.Space.modulePullbackHomFMap`.  Let `d` be a commuting diagram of étale
scheme charts whose chart `d.U` of `X` has surjective structure morphism, and let `s i` be
sections of `M` over `d.V` such that the readings of the values `ξ.app d (s i)` generate the
Zariski chart restriction `N|_{d.U}` over every affine open of `chartScheme d.U`.  Then the span
sieve of the values of `ξ` is a covering sieve over *every* étale chart of `X` and every section
of `N` there — which is exactly what the epimorphism criterion asks for.

The index type of the generating family is arbitrary: finiteness is not used. -/
theorem spanSieve_moduleFMapSpanningSet_mem_of_span_chartSectionsToRestrict
    (hN : N.IsQuasicoherentOnSite) (u : (modulePullback B S hS g).obj M ⟶ N)
    (d : ChartDiagram B S hS X.1 X'.1 g.hom) (hd : IsSurjective B S hS d.U.1.hom)
    {I : Type*} (s : I → M.val.obj (op d.V))
    (hgen : ∀ O : (chartScheme d.U).Opens, IsAffineOpen O →
      ∀ y : (restrictToChartScheme B S hS X.1 X.2 N d.U).val.obj (op O),
        y ∈ Submodule.span ((chartScheme d.U).ringCatSheaf.obj.obj (op O))
          (Set.range fun i => chartSectionsToRestrict X N d.U O
            (N.val.map (openChartInclusion B S hS X.1 d.U O).op
              ((modulePullbackHomFMap B S hS g M N u).app d (s i)))))
    (W : SmallEtale B S hS X.1) (x : N.val.obj (op W)) :
    Stacks.SheafOfModules.spanSieve N
        (moduleFMapSpanningSet B S hS g M N (modulePullbackHomFMap B S hS g M N u)) x ∈
      SmallEtale.topology B S hS X.1 W :=
  spanSieve_mem_of_span_chartSectionsToRestrict_of_isSurjective N
    (moduleFMapSpanningSet B S hS g M N (modulePullbackHomFMap B S hS g M N u)) hN d.U hd
    (fun i => (modulePullbackHomFMap B S hS g M N u).app d (s i))
    (fun i => ⟨d, 𝟙 d.U, s i, CategoryTheory.congr_fun (N.val.presheaf.map_id (op d.U))
      ((modulePullbackHomFMap B S hS g M N u).app d (s i))⟩) hgen W x

end Pullback

end AlgebraicGeometry.Space

end
