module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections

/-!
# Spanning the sections over the affine charts is finite type on the site

Let `F` be an algebraic space and `G` an `𝒪_F`-module which is cartesian on affine charts, that
is, one for which the base change comparison of Stacks 03DX(2) is bijective between any two
affine étale charts.  `StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeChartSections.lean` proves
that finitely many sections over an affine étale chart which generate `G` only locally already
span the sections over that chart, and hence that the sections of a module of finite type over an
affine chart form a finite module.  This file proves the converse of both: spanning gives local
generation, and finiteness of the sections over *every* affine chart gives finite type on the
small étale site.

The converse is the direction in which cartesianness is used as a surjection rather than as an
injection, and it needs no faithfully flat descent.  Over an affine chart `Y` lying over the
chart `V` at which a section `t` is given, the comparison for the composite `Y ⟶ V ⟶ U` is
surjective, so `t|_Y` is an `𝒪_F(Y)`-combination of restrictions of sections over `U`; each of
those is an `𝒪_F(U)`-combination of the spanning family, and restriction carries that combination
to an `𝒪_F(Y)`-combination of the restricted family.  The affine charts over `V` cover it
(`AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows`), which is the covering sieve
`PresheafOfModules.Generates` asks for; an arbitrary arrow of that sieve factors through one of
the affine members, and membership in the span is carried along the factoring arrow because
restriction is semilinear.

Finite type on the site is then immediate: the affine charts over an object cover it, and on each
of them local generation is the categorical condition, by
`Stacks.SheafOfModules.hasFiniteGlobalGenerators_of_generates`.

## Main results

* `AlgebraicGeometry.Space.chartRestrictLinear_mem_span_of_span_eq_top`: the restriction of any
  section lies in the span of the restrictions of a spanning family.
* `AlgebraicGeometry.Space.generates_of_span_eq_top`: **finitely many sections spanning the
  sections over an affine étale chart generate the module locally**, the converse of
  `AlgebraicGeometry.Space.span_eq_top_of_generates`.
* `AlgebraicGeometry.Space.generates_of_module_finite_sections`: the same from finiteness of the
  sections over the chart.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_of_module_finite_sections`: **a module cartesian on
  affine charts whose sections over every affine étale chart form a finite module is of finite
  type on the small étale site**, the converse of
  `Space.module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite`.

## Implementation notes

The spanning hypothesis is stated for the `𝒪_F(U)`-module structure on the sections over `U`,
which is the one `AlgebraicGeometry.Space.span_eq_top_of_generates` concludes in, so the two
statements compose to an equivalence without any transport.

Restriction of sections along `f : V ⟶ U` is `𝒪_F(U)`-linear for the `𝒪_F(U)`-module structure
`AlgebraicGeometry.Space.chartSectionsModule` on the sections over `V`, in which the action is
the `𝒪_F(V)`-action along `AlgebraicGeometry.Space.chartRestrict`
(`AlgebraicGeometry.Space.chartSectionsModule_smul`, which holds by `rfl`).  That is what turns
an `𝒪_F(U)`-combination over `U` into an `𝒪_F(Y)`-combination over `Y`, and it is why no
scalar-restriction lemma is needed.

No declaration here carries a `stacks` attribute.  One direction of a clause of Stacks 03DL is
not the clause, and the equivalence these assemble into is consumed as an input by the chartwise
readings rather than asserted as a tag of its own.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

variable {B S hS F hF}

/-- **The restrictions of a spanning family span the restriction of every section.**  If `s`
spans the sections over `U` as an `𝒪_F(U)`-module, then for any chart morphism `f : V ⟶ U` the
restriction of an arbitrary section over `U` lies in the `𝒪_F(V)`-span of the restrictions
of `s`. -/
theorem chartRestrictLinear_mem_span_of_span_eq_top (G : Modules.{u, u} B S hS F hF)
    {U V : SmallEtale B S hS F} (f : V ⟶ U) {k : ℕ} (s : Fin k → G.val.obj (op U))
    (hspan : Submodule.span (chartRing B S hS F hF U) (Set.range s) = ⊤)
    (x : G.val.obj (op U)) :
    chartRestrictLinear G f x ∈
      Submodule.span (chartRing B S hS F hF V)
        (Set.range fun i => chartRestrictLinear G f (s i)) := by
  classical
  have hx : x ∈ Submodule.span (chartRing B S hS F hF U) (Set.range s) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun
    (chartRing B S hS F hF U)).1 hx
  rw [← hb, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [chartRestrictLinear_smul G f (b i) (s i)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Finitely many sections spanning the sections over an affine étale chart generate the module
locally.**  This is the converse of `AlgebraicGeometry.Space.span_eq_top_of_generates`.

The covering sieve is the family of affine étale charts over the chart at which a section is
given.  On an affine member the base change comparison for the composite into `U` is surjective
by cartesianness, so the section restricts into the span of the restrictions of all sections over
`U`, and `AlgebraicGeometry.Space.chartRestrictLinear_mem_span_of_span_eq_top` replaces those by
the spanning family.  An arbitrary arrow of the sieve factors through an affine member, and the
combination is carried along the factoring arrow by semilinearity of restriction. -/
theorem generates_of_span_eq_top (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    {k : ℕ} (s : Fin k → G.val.obj (op U))
    (hspan : Submodule.span (chartRing B S hS F hF U) (Set.range s) = ⊤) :
    PresheafOfModules.Generates (SmallEtale.topology B S hS F) G.val s := by
  classical
  intro V f t
  obtain ⟨I, Y, a, hYaff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F V
  refine ⟨Sieve.ofArrows Y a, hcov, ?_⟩
  intro W g hg
  rw [Sieve.mem_ofArrows_iff] at hg
  obtain ⟨j, h, rfl⟩ := hg
  -- On the affine member `Y j` the comparison for `a j ≫ f : Y j ⟶ U` is surjective, so the
  -- restrictions of all sections over `U` span, hence so do the restrictions of `s`.
  have htop : Submodule.span (chartRing B S hS F hF (Y j))
      (Set.range fun x : G.val.obj (op U) => chartRestrictLinear G (a j ≫ f) x) = ⊤ :=
    (chartBaseChange_surjective_iff_span_eq_top G (a j ≫ f)).1
      (hG U (Y j) hU (hYaff j) (a j ≫ f)).surjective
  have hmemY : chartRestrictLinear G (a j) t ∈
      Submodule.span (chartRing B S hS F hF (Y j))
        (Set.range fun i => chartRestrictLinear G (a j ≫ f) (s i)) := by
    have hle : Submodule.span (chartRing B S hS F hF (Y j))
        (Set.range fun x : G.val.obj (op U) => chartRestrictLinear G (a j ≫ f) x) ≤
          Submodule.span (chartRing B S hS F hF (Y j))
            (Set.range fun i => chartRestrictLinear G (a j ≫ f) (s i)) := by
      refine Submodule.span_le.2 ?_
      rintro y ⟨x, rfl⟩
      exact chartRestrictLinear_mem_span_of_span_eq_top G (a j ≫ f) s hspan x
    exact hle (htop ▸ Submodule.mem_top)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun
    (chartRing B S hS F hF (Y j))).1 hmemY
  -- Restrict the combination along the factoring arrow `h : W ⟶ Y j`.
  refine ⟨fun i => chartRestrict (hF := hF) h (c i), ?_⟩
  have hres := congrArg (chartRestrictLinear G h) hc
  rw [map_sum] at hres
  have hsmul : ∀ i, chartRestrictLinear G h
      (c i • chartRestrictLinear G (a j ≫ f) (s i))
      = chartRestrict (hF := hF) h (c i) •
          chartRestrictLinear G (h ≫ a j ≫ f) (s i) := by
    intro i
    rw [chartRestrictLinear_smul G h (c i) (chartRestrictLinear G (a j ≫ f) (s i)),
      ← chartRestrictLinear_comp G (a j ≫ f) h (s i)]
  simp only [hsmul] at hres
  rw [← chartRestrictLinear_comp G (a j) h t] at hres
  exact hres

/-- **Finiteness of the sections over an affine étale chart gives local generation.**  The
spanning family is a finite generating family of the sections as a module over the chart ring,
and `AlgebraicGeometry.Space.generates_of_span_eq_top` applies. -/
theorem generates_of_module_finite_sections (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hfin : Module.Finite (chartRing B S hS F hF U) (G.val.obj (op U))) :
    ∃ (k : ℕ) (s : Fin k → G.val.obj (op U)),
      PresheafOfModules.Generates (SmallEtale.topology B S hS F) G.val s := by
  classical
  obtain ⟨k, s, hs⟩ := @Module.Finite.exists_fin (chartRing B S hS F hF U)
    (G.val.obj (op U)) _ _ _ hfin
  exact ⟨k, s, generates_of_span_eq_top G hG hU s hs⟩

/-- **Finite type on the small étale site from one covering family of affine charts.**  A module
cartesian on affine charts is of finite type as soon as the sections are finite over the members
of *some* family of affine étale charts covering the final object — not necessarily over every
affine chart.

This is the form a surjective chart's affine opens are consumed in: they cover the site by
`Stacks.Sites.coversTop_bind` applied to
`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`, while they are far from being all
of the affine charts.  Local generation on each member is
`AlgebraicGeometry.Space.generates_of_module_finite_sections`, and a covering family carrying
local generators is the sectionwise form of Stacks 03DL(5), which
`Stacks.SheafOfModules.isFiniteTypeOnSite_of_presheaf_isFiniteType` turns into the categorical
one. -/
theorem isFiniteTypeOnSite_of_coversTop_module_finite_sections (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {I : Type (u + 1)} {Y : I → SmallEtale B S hS F}
    (hcov : (SmallEtale.topology B S hS F).CoversTop Y)
    (hYaff : ∀ j, IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y j)))
    (hfin : ∀ j, Module.Finite (chartRing B S hS F hF (Y j)) (G.val.obj (op (Y j)))) :
    SheafOfModules.IsFiniteTypeOnSite G :=
  Stacks.SheafOfModules.isFiniteTypeOnSite_of_presheaf_isFiniteType G
    ⟨I, Y, hcov, fun j => generates_of_module_finite_sections G hG (hYaff j) (hfin j)⟩

/-- **A module cartesian on affine charts whose sections over every affine étale chart form a
finite module is of finite type on the small étale site.**  This is the converse of
`Space.module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite`.

Every étale chart is covered by the affine étale charts over it
(`AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows`), and on each of those local
generation holds by `AlgebraicGeometry.Space.generates_of_module_finite_sections`, which is the
categorical condition by `Stacks.SheafOfModules.hasFiniteGlobalGenerators_of_generates`. -/
theorem isFiniteTypeOnSite_of_module_finite_sections (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W))) :
    SheafOfModules.IsFiniteTypeOnSite G := by
  refine ⟨fun Z => ?_⟩
  obtain ⟨I, Y, a, hYaff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F Z
  refine ⟨I, Y, a, hcov, fun j => ?_⟩
  obtain ⟨k, s, hs⟩ := generates_of_module_finite_sections G hG (hYaff j) (hfin (Y j) (hYaff j))
  exact Stacks.SheafOfModules.hasFiniteGlobalGenerators_of_generates G s hs

/-- **Clause (5) of Stacks 03DL, read on the affine étale charts.**  For a module cartesian on
affine charts, finite type on the small étale site is exactly finiteness of the sections over
every affine étale chart as a module over the chart ring.

The forward implication is
`Space.module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite`,
where the content is the faithfully flat descent of a local generating family; the converse is
`AlgebraicGeometry.Space.isFiniteTypeOnSite_of_module_finite_sections`, where the content is
surjectivity of the base change comparison on the affine charts of a covering. -/
theorem isFiniteTypeOnSite_iff_module_finite_sections (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) :
    SheafOfModules.IsFiniteTypeOnSite G ↔
      ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)) :=
  ⟨fun hft W hW =>
    module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite G hG hft W hW,
   isFiniteTypeOnSite_of_module_finite_sections G hG⟩

end AlgebraicGeometry.Space

end
