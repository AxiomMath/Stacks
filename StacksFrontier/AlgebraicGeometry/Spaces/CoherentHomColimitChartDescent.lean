module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartProdExponentRise
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitChartTransport

/-!
# The descent from the chart: surjectivity of the canonical map of Stacks 07UM

Let `X` be a Noetherian algebraic space over a scheme `S` of a big fppf site `B`, let `ℐ ⊆ 𝒪_X` be
a quasi-coherent sheaf of ideals, let `U = X ∖ V(ℐ)`, let `𝒢` be coherent and `ℱ` quasi-coherent
and let `θ : 𝒢|_U ⟶ ℱ|_U`.  This file produces an exponent `n` and a morphism `ψ : ℐⁿ𝒢 ⟶ ℱ`
restricting to `θ` on `U`, which is the surjectivity clause of [Stacks, Tag 07UM].

The route is Steps 1–4 of the tag.  A surjective Noetherian affine chart `W` whose kernel pair has
Noetherian scheme carries the first display of [Stacks, Tag 01YB]
(`AlgebraicGeometry.Space.exists_homRestrict_eq_chartThetaOver`), which produces a morphism on the
chart's scheme restricting to the transport of `θ`; its chart transport
`AlgebraicGeometry.Space.chartAlphaSheaf` is a morphism `(ℐᵏ𝒢)|_W ⟶ ℱ|_W` of the restrictions to
the slice of the small étale site at `W`.  Raising the exponent makes the two relocalizations of
that morphism to the kernel pair agree
(`AlgebraicGeometry.Space.exists_homRestr_prod_eq`), so the one-chart gluing
`AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod` extends it to a morphism
`ℐⁿ𝒢 ⟶ ℱ` on all of `X`.

That the extension restricts to `θ` is the last step, and it is *not* formal: the extension is
pinned only over the charts of `X` admitting a morphism to `W`, and the component determination
`AlgebraicGeometry.Space.chartAlphaSheaf_val_app_eq_homOnChart_of_homRestrict` identifies it with
the transport of `θ` only there.  Those charts, however, generate a covering sieve of every chart
of `U`, because `W` is surjective; and `ℱ|_U` is separated.

## Main results

* `Stacks.SheafOfModules.val_app_eq_of_isSeparated`: two morphisms of sheaves of modules take the
  same value on a section as soon as they do after restriction along a covering sieve.
* `AlgebraicGeometry.Space.coversTop_singleton_of_isSurjective`: a surjective étale chart covers
  the final object of the small étale site, with the one-element family indexed by `Unit` — which
  is the shape `AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod` asks for, whereas
  `AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective` produces it indexed by `PUnit` in
  a larger universe.
* `AlgebraicGeometry.Space.overChartSieve_mem_topology`: **the charts of `U = X ∖ V(ℐ)` lying over
  a surjective chart `W` of `X` cover every chart of `U`.**  A point of the chart's scheme is hit
  by a chart of `X` over `W`, that chart lies over `U` because the chart it maps to does
  (`AlgebraicGeometry.Space.exists_pc_eq_of_over`), and the morphism of charts of `X` lifts to the
  charts of `U` (`AlgebraicGeometry.Space.exists_pcMap_eq`).
* `AlgebraicGeometry.Space.val_app_eq_homOnChart_of_restrFun_map_eq`: a morphism `ℐⁿ𝒢 ⟶ ℱ` whose
  restriction to the slice at `W` is the chart transport of `θ` **is** the transport of `θ` on the
  sections over every chart of `U` admitting a morphism to `W`.
* `AlgebraicGeometry.Space.exists_homRestrict_eq_of_chart`: **surjectivity in existence form**, on
  a chart with the required finiteness properties.
* `AlgebraicGeometry.Space.exists_homRestrict_eq`: **surjectivity in existence form**, with the
  chart produced from the Noetherian hypothesis.
* `AlgebraicGeometry.Space.canonicalMapToHomRestrict_surjective`: **the surjectivity clause of
  [Stacks, Tag 07UM]**, and only that clause.

## Implementation notes

**The restriction to `U` is compared at the level of morphisms, not of `homRestrict`.**  The
space-level `AlgebraicGeometry.Space.homRestrict` is the inverse of `(ℐⁿ𝒢)|_U ≅ 𝒢|_U` followed by
the restriction of the morphism, and the components of that inverse are not available.  What is
proved below is therefore the equivalent statement that the restriction of the morphism is the
*forward* map of that isomorphism followed by `θ`, whose components are the components of the
morphism itself; the inverse is then cancelled at the level of morphisms by
`CategoryTheory.Iso.inv_hom_id_assoc`.  This is the same device the injectivity clause uses in
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentHomColimitInjective.lean`.

**No `@[stacks 07UM]` attribute is placed here.**  Tag 07UM asserts that the canonical map is
bijective; the injectivity clause lives in
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentHomColimitInjective.lean`, and the attribute belongs
on the covering set of both clauses, which is
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentHomColimitBijective.lean`.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

universe w m v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : CategoryTheory.Sheaf J RingCat.{w}}

/-- **Two morphisms of sheaves of modules take the same value on a section as soon as they do
after restriction along a covering sieve.**  The target is a sheaf, hence separated, and both
morphisms commute with restriction. -/
theorem val_app_eq_of_isSeparated {M N : _root_.SheafOfModules.{m} R} (a b : M ⟶ N) {W : Cᵒᵖ}
    (z : M.val.obj W) {T : Sieve W.unop} (hT : T ∈ J W.unop)
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ W.unop), T f →
      (a.val.app (op Y)).hom (M.val.map f.op z) =
        (b.val.app (op Y)).hom (M.val.map f.op z)) :
    (a.val.app W).hom z = (b.val.app W).hom z :=
  N.isSheaf.isSeparated _ _ hT _ _ fun _ f hf =>
    (_root_.PresheafOfModules.naturality_apply a.val f.op z).symm.trans
      ((h f hf).trans (_root_.PresheafOfModules.naturality_apply b.val f.op z))

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### A surjective chart covers the final object, indexed by `Unit` -/

/-- **A surjective étale chart covers the final object of the small étale site**, with the
one-element family indexed by `Unit`.

`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective` produces the same statement for the
family indexed by `PUnit.{u + 2}`, and the sieve a constant family with nonempty index generates
does not depend on that index; the one-chart gluing
`AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod` asks for `Unit`. -/
theorem coversTop_singleton_of_isSurjective (W : SmallEtale B S hS X.1)
    (hW : IsSurjective B S hS W.1.hom) :
    (SmallEtale.topology B S hS X.1).CoversTop (fun _ : Unit => W) := by
  intro Z
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    (SmallEtale.coversTop_of_isSurjective B S hS X.1 X.2 W hW Z)
  intro Y f hf
  obtain ⟨i, hi⟩ := hf
  exact ⟨(), hi⟩

/-! ### The charts of the open complement lying over a chart of `X` -/

variable (I : IdealSheaves B S hS X.1 X.2)

/-- **The sieve on a chart of `U = X ∖ V(ℐ)` of the arrows whose source lies over a given chart
`W` of `X`.**  Membership does not depend on the arrow, only on its source; it is downward closed
because a morphism of charts of `U` postcomposes to one of charts of `X`. -/
def overChartSieve (W : SmallEtale B S hS X.1)
    (P : SmallEtale B S hS (idealComplement B S hS X I).1) : Sieve P where
  arrows Q _ := Nonempty (pc B S hS X I Q ⟶ W)
  downward_closed := fun hf g => hf.elim fun t => ⟨pcMap B S hS X I g ≫ t⟩

/-- **The charts of `U = X ∖ V(ℐ)` lying over a surjective chart `W` of `X` cover every chart of
`U`.**

By the pointwise criterion `AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range`
it is enough that every point of the scheme of the chart is hit by one of them.  On the side of
`X` the chart `W` covers the final object, so that point is hit by a chart of `X` admitting a
morphism to `W`; that chart lies over `U` because the chart it maps to does
(`AlgebraicGeometry.Space.exists_pc_eq_of_over`), and the morphism of charts of `X` is the
postcomposition of a morphism of charts of `U` (`AlgebraicGeometry.Space.exists_pcMap_eq`), whose
underlying scheme morphism is the same. -/
theorem overChartSieve_mem_topology (W : SmallEtale B S hS X.1)
    (hW : IsSurjective B S hS W.1.hom)
    (P : SmallEtale B S hS (idealComplement B S hS X I).1) :
    overChartSieve B S hS X I W P ∈
      SmallEtale.topology B S hS (idealComplement B S hS X I).1 P := by
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro x
  obtain ⟨T, g, hg, hx⟩ := (SmallEtale.mem_topology_iff_exists_mem_range B S hS X.1
      (Sieve.ofObjects (fun _ : PUnit.{u + 2} => W) (pc B S hS X I P))).1
    (SmallEtale.coversTop_of_isSurjective B S hS X.1 X.2 W hW (pc B S hS X I P)) x
  obtain ⟨Q, rfl⟩ := exists_pc_eq_of_over B S hS X I g
  obtain ⟨l, hl⟩ := exists_pcMap_eq B S hS X I g
  refine ⟨Q, l, hg.elim fun _ ht => ht, ?_⟩
  exact (congrArg (fun m : pc B S hS X I Q ⟶ pc B S hS X I P =>
    Set.range ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map m))) hl).ge hx

/-! ### The extension is the transport of `θ` over the charts lying over `W` -/

variable (hIc : IsCartesianOnAffineCharts I.toSheafOfModules)
    (G F : Modules.{u, u} B S hS X.1 X.2)
    (θ : (restrictToIdealComplement B S hS X I).obj G ⟶
      (restrictToIdealComplement B S hS X I).obj F)
    (hZt : B.Contains (⊤_ Scheme.{u})) (hNo : IsNoetherian B S hS hZt X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (hG : IsCoherent B S hS X.1 X.2 G)

include hIc hZt hNo hIq hFq hG

/-- **A morphism `ℐⁿ𝒢 ⟶ ℱ` whose restriction to the slice at `W` is the chart transport of `θ`
is the transport of `θ` on the sections over every chart of `U = X ∖ V(ℐ)` admitting a morphism to
`W`.**

The restriction to the slice at `W` has, over the object `Over.mk h`, the component of the
morphism over the source of `h`; the hypothesis replaces it by the component of the chart
transport there, and the component determination
`AlgebraicGeometry.Space.chartAlphaSheaf_val_app_eq_homOnChart_of_homRestrict` evaluates that to
the transport of `θ`. -/
theorem val_app_eq_homOnChart_of_restrFun_map_eq (W : SmallEtale B S hS X.1) (n : ℕ)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc W) n (chartPush B S hS X G W) ⟶
      chartPush B S hS X F W)
    (hφ : Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc W)
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc W)) φ =
      chartThetaOver B S hS X I hIc G F θ W)
    (Ψ : idealPowModule I n G ⟶ F)
    (hΨ : (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) W).map Ψ.val =
      (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG W n φ).val)
    {P : SmallEtale B S hS (idealComplement B S hS X I).1} (h : pc B S hS X I P ⟶ W)
    (z : (idealPowModule I n G).val.obj (op (pc B S hS X I P))) :
    (Ψ.val.app (op (pc B S hS X I P))).hom z =
      (homOnChart B S hS X I G F θ (rfl : pc B S hS X I P = pc B S hS X I P)).hom
        (((idealPowModuleι I n G).val.app (op (pc B S hS X I P))).hom z) :=
  (congrArg
        (fun m : (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) W).obj
              (idealPowModule I n G).val ⟶
            (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) W).obj F.val =>
          (m.app (op (Over.mk h))).hom z) hΨ).trans
    (chartAlphaSheaf_val_app_eq_homOnChart_of_homRestrict B S hS X I hIc G F θ hZt hNo hIq hFq
      hG W n φ hφ rfl h z)

/-- **The restriction to `U = X ∖ V(ℐ)` of a morphism `ℐⁿ𝒢 ⟶ ℱ` whose restriction to the slice at
a surjective chart `W` is the chart transport of `θ` is `θ`**, read as the statement that it
agrees with the forward map of `(ℐⁿ𝒢)|_U ≅ 𝒢|_U` followed by `θ`.

Over a chart of `U` admitting a morphism to `W` this is
`AlgebraicGeometry.Space.val_app_eq_homOnChart_of_restrFun_map_eq`, and such charts cover every
chart of `U` because `W` is surjective; `ℱ|_U` is separated. -/
theorem map_eq_idealPowRestrictIso_hom_comp (W : SmallEtale B S hS X.1)
    (hW : IsSurjective B S hS W.1.hom) (n : ℕ)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc W) n (chartPush B S hS X G W) ⟶
      chartPush B S hS X F W)
    (hφ : Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc W)
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc W)) φ =
      chartThetaOver B S hS X I hIc G F θ W)
    (Ψ : idealPowModule I n G ⟶ F)
    (hΨ : (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) W).map Ψ.val =
      (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG W n φ).val) :
    (restrictToIdealComplement B S hS X I).map Ψ =
      (idealPowRestrictIso B S hS X I n G).hom ≫ θ := by
  refine Stacks.SheafOfModules.hom_ext_val_app_apply fun Z z => ?_
  refine Stacks.SheafOfModules.val_app_eq_of_isSeparated _ _ z
    (overChartSieve_mem_topology B S hS X I W hW Z.unop) fun Y f hf => ?_
  obtain ⟨t⟩ := hf
  refine Eq.trans (val_app_eq_homOnChart_of_restrFun_map_eq B S hS X I hIc G F θ hZt hNo hIq hFq
    hG W n φ hφ Ψ hΨ t _) ?_
  refine Eq.trans (congrArg
    (fun m : G.val.obj (op (pc B S hS X I Y)) ⟶ F.val.obj (op (pc B S hS X I Y)) =>
      m.hom (((idealPowModuleι I n G).val.app (op (pc B S hS X I Y))).hom
        (((restrictToIdealComplement B S hS X I).obj
          (idealPowModule I n G)).val.map f.op z)))
    (homOnChart_rfl B S hS X I G F θ Y)) ?_
  exact (Stacks.SheafOfModules.comp_val_app_hom_apply
    (idealPowRestrictIso B S hS X I n G).hom θ (op Y) _).symm

/-! ### Surjectivity -/

/-- **Surjectivity of the canonical map of [Stacks, Tag 07UM], in existence form, on a chart with
the required finiteness properties.**

The chart carries the first display of [Stacks, Tag 01YB], the exponent is raised until the two
relocalizations of the chart transport to the kernel pair agree, the one-chart gluing extends the
chart transport to a morphism `ℐⁿ𝒢 ⟶ ℱ`, and that morphism restricts to `θ` by
`AlgebraicGeometry.Space.map_eq_idealPowRestrictIso_hom_comp`. -/
theorem exists_homRestrict_eq_of_chart (W : SmallEtale B S hS X.1)
    (hW : IsSurjective B S hS W.1.hom)
    (hWno : _root_.AlgebraicGeometry.IsNoetherian (chartScheme W))
    (hWPno : _root_.AlgebraicGeometry.IsNoetherian
      (chartScheme (W ⨯ W : SmallEtale B S hS X.1))) :
    ∃ (n : ℕ) (Ψ : idealPowModule I n G ⟶ F), homRestrict B S hS X I Ψ = θ := by
  obtain ⟨k, φ, hφ⟩ := exists_homRestrict_eq_chartThetaOver B S hS X I hIc G F θ hFq hG W hWno
  obtain ⟨n, φ', hφ', hpq⟩ := exists_homRestr_prod_eq B S hS X I hIc G F hZt hNo hIq hFq hG W θ
    hWPno k φ hφ
  obtain ⟨Φ, hΦ, -⟩ := existsUnique_hom_of_single_chart_prod B S hS X.1 X.2
    (idealPowModule I n G).val F.val F.isSheaf W
    (coversTop_singleton_of_isSurjective B S hS X W hW)
    (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG W n φ').val hpq
  obtain ⟨Ψ, hΨval⟩ : ∃ Ψ : idealPowModule I n G ⟶ F, Ψ.val = Φ := ⟨⟨Φ⟩, rfl⟩
  have hΨ : (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) W).map Ψ.val =
      (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG W n φ').val :=
    (congrArg (fun m : (idealPowModule I n G).val ⟶ F.val =>
      (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) W).map m) hΨval).trans hΦ
  refine ⟨n, Ψ, ?_⟩
  refine Eq.trans (congrArg
    (fun m : (restrictToIdealComplement B S hS X I).obj (idealPowModule I n G) ⟶
        (restrictToIdealComplement B S hS X I).obj F =>
      (idealPowRestrictIso B S hS X I n G).inv ≫ m)
    (map_eq_idealPowRestrictIso_hom_comp B S hS X I hIc G F θ hZt hNo hIq hFq hG W hW n φ' hφ'
      Ψ hΨ)) ?_
  exact Iso.inv_hom_id_assoc (idealPowRestrictIso B S hS X I n G) θ

/-- **Surjectivity of the canonical map of [Stacks, Tag 07UM], in existence form.**  Every
morphism `𝒢|_U ⟶ ℱ|_U` is the restriction to `U = X ∖ V(ℐ)` of a morphism `ℐⁿ𝒢 ⟶ ℱ` for some `n`.

The chart is the surjective Noetherian affine chart whose kernel pair has Noetherian scheme,
produced by the chart existence statement of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentChartSchemeNonAffine.lean`. -/
theorem exists_homRestrict_eq :
    ∃ (n : ℕ) (Ψ : idealPowModule I n G ⟶ F), homRestrict B S hS X I Ψ = θ := by
  obtain ⟨W, hWaff, hWsurj, -, hWPno, -⟩ :=
    exists_surjective_isNoetherianAffineChart_isNoetherian_prod_isCoherent_chartSchemeModule
      B S hS X G hZt hNo hG
  exact exists_homRestrict_eq_of_chart B S hS X I hIc G F θ hZt hNo hIq hFq hG W hWsurj
    (isNoetherian_chartScheme_of_isNoetherianAffineChart B S hS X W hWaff) hWPno

/-- **The surjectivity clause of [Stacks, Tag 07UM], and only that clause.**  For a Noetherian
algebraic space `X`, a quasi-coherent sheaf of ideals `ℐ` with complement `U = X ∖ V(ℐ)`, a
coherent `𝒪_X`-module `𝒢` and a quasi-coherent `𝒪_X`-module `ℱ`, the canonical map

`colim_n Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ) ⟶ Hom_{𝒪_U}(𝒢|_U, ℱ|_U)`

is surjective. -/
theorem canonicalMapToHomRestrict_surjective :
    Function.Surjective (canonicalMapToHomRestrict B S hS X I G F) := fun θ' => by
  obtain ⟨n, Ψ, hΨ⟩ := exists_homRestrict_eq B S hS X I hIc G F θ' hZt hNo hIq hFq hG
  exact ⟨Limits.colimit.ι (homSystem B S hS X I G F) n Ψ,
    (canonicalMapToHomRestrict_ι B S hS X I G F n Ψ).trans hΨ⟩

end AlgebraicGeometry.Space

end
