module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapIdealBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapIdealMainClause
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapIdealOverSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapChartwiseVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecQuotientOverAffineBase

/-!
# The main clause of Stacks 083K for an affine test object

Let `S = \Spec(R)` be an affine scheme of a big fppf site, let `X` be an algebraic space over
`S` and let `u : ℱ ⟶ 𝒢` be a map of quasi-coherent `𝒪_X`-modules with `𝒢` flat over `S` — the
standing data of Stacks 0CWA.  Let `T` be an **affine** object of the big fppf category over
`S`, read as a test scheme, at which the base change `u_T` vanishes.  This file produces the
closed subscheme the main clause of Stacks 083K asks for: `Z = \Spec(R/I)` for
`I = \ker(R ⟶ \Gamma(T, ⊤))`, through which `T ⟶ S` factors and at which `u_Z = 0`.

No finiteness of `ℱ` is used, and no scheme-theoretic support.  The ideal is the largest one
available, hence cuts out the smallest closed subscheme through which `T ⟶ S` factors, and it
kills the image of `u` over *every* affine chart at once; that is what makes the covering
argument the unconditional one.

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `exists_ofArrows_hasAffineChartDiagram`: the cover-density statement of
  `mem_topology_of_hasAffineChartDiagram` presented by a generating family, which is the form
  the locality of vanishing consumes.
* `ModuleMapSituation.isZeroAt_of_forall_mem_smul_top`: **`u_T = 0`** for an ideal of the
  functions on an *object* `Y₀` of the big fppf category which dies in the functions on the
  test object and kills the image of `u` over every affine chart of `X`.
* `ModuleMapFlatTargetSituation.isZeroAt_specQuotient_of_forall_mem_smul_top`:
  **`u_Z = 0`** for an ideal killing the image of `u` over every affine chart of `X`.  This is
  the previous statement at `Y₀ = baseTerminal`, where the functions on `Y₀` are the
  functions on `S`.
* `ModuleMapFlatTargetSituation.exists_closedSubscheme_isZeroAt_of_isZeroAt`:
  **the main clause of Stacks 083K for an affine test object.**

## Implementation notes

**The covering argument.**  Vanishing of a map of `𝒪`-modules is étale local
(`AlgebraicGeometry.Space.Modules.eq_zero_of_ofArrows`), and the charts of `X ×_S Z` carrying a
diagram of affine étale charts over the projection `X ×_S Z ⟶ X` are cover-dense
(`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`).  Over such a chart the
vanishing is
`AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_chart`: the
ideal kills the image of `u` over the chart of `X`, which is affine, and acts by zero on the
functions of the chart of `X ×_S Z` by
`AlgebraicGeometry.Space.smul_chartRing_baseChangeSpace_eq_zero`.

This is the *unconditional* cover-density of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartDiagramCover.lean`, not the refinement with a
condition on the chart of `X` that the finite-presentation clause needs.  There the ideal is
finitely generated, so it is computed at one chart and has to be transported, and the charts it
reaches are only those over that one or those carrying no sections; here the ideal already works
at every affine chart, and affineness is part of `AlgebraicGeometry.Space.HasAffineChartDiagram`.

**Why the test object is asked to be affine.**  The hypothesis `u_T = 0` is consumed through
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.val_app_mem_ker_smul_top_of_isZeroAt`,
whose proof identifies the ring of functions of the base change of a chart with a tensor
product, and that identification needs the base change of the chart to be affine.  The source
reduces a quasi-compact test scheme to an affine one by replacing it with the coproduct of a
finite affine open covering; `Stacks.Flattening.tmul_one_eq_zero_of_forall_tmul_one_eq_zero`
performs that reduction at the level of the module, and
`StacksFrontier/AlgebraicGeometry/Scheme/FiniteAffineCoverOfQuasiCompact.lean` supplies the
covering.  That reduction is carried out in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartMapQuasiCompactTest.lean`, which consumes the clause
below; the clause itself is therefore stated for an affine test object.

**No `stacks` attribute.**  Stacks 083K states its main clause for a *quasi-compact* test
scheme.  What is proved here is that clause for an affine test object, which is a special case,
and a registration of the tag on it would be a weakening.  The attribute sits on the statement
for a quasi-compact test object,
`ModuleMapFlatTargetSituation.exists_closedSubscheme_isZeroAt_of_isZeroAt_of_quasiCompact`
(in the namespace `AlgebraicGeometry.Space`).

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 0CWA](https://stacks.math.columbia.edu/tag/0CWA)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The charts of `X` carrying an affine chart diagram over `g` are cover-dense, presented by
a generating family.**

This is `AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram` with the covering sieve
exhibited as the sieve generated by a family: the family indexed by all pairs of a good chart and
a morphism of it to `U`.  That is the form
`AlgebraicGeometry.Space.Modules.eq_zero_of_ofArrows` consumes, and it is the form that is
needed, because a statement proved on the good charts does not pass to arbitrary charts over
them. -/
theorem exists_ofArrows_hasAffineChartDiagram {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')
    (U : SmallEtale B S hS X.1) :
    ∃ (I : Type (u + 1)) (Y : I → SmallEtale B S hS X.1) (π : ∀ j, Y j ⟶ U),
      Sieve.ofArrows Y π ∈ SmallEtale.topology B S hS X.1 U ∧
      ∀ j, HasAffineChartDiagram B S hS g (Y j) := by
  refine ⟨Σ W : SmallEtale B S hS X.1, {a : W ⟶ U // HasAffineChartDiagram B S hS g W},
    fun j => j.1, fun j => j.2.1, ?_, fun j => j.2.2⟩
  refine mem_topology_of_hasAffineChartDiagram B S hS g U _ ?_
  intro W a hW
  exact Sieve.ofArrows_mk (fun j : Σ W : SmallEtale B S hS X.1,
      {a : W ⟶ U // HasAffineChartDiagram B S hS g W} => j.1)
    (fun j => j.2.1) ⟨W, a, hW⟩

namespace ModuleMapSituation

/-- **`u_T = 0` for a test object killing an ideal which kills the image of `u` over every affine
chart.**

Let `X` be an algebraic space over an object `Y₀` of the big fppf category over `S`, let `T` be a
test scheme over `Y₀` whose structure morphism is the Yoneda image of a morphism `k : T ⟶ Y₀` of
the category, and let `J` be an ideal of `Γ(Y₀, ⊤)` such that

* `J` dies in `Γ(T, ⊤)`, and
* `J` kills the image of `u` over every affine étale chart of `X`,

the scalars acting on the sections over a chart through the chart's own morphism `α` to `Y₀`.
Then the base change of `u` to `X ×_{Y₀} T` is zero.

Vanishing of a map of `𝒪`-modules is étale local
(`AlgebraicGeometry.Space.Modules.eq_zero_of_ofArrows`), the charts of `X ×_{Y₀} T` carrying a
diagram of affine étale charts over the projection are cover-dense
(`AlgebraicGeometry.Space.exists_ofArrows_hasAffineChartDiagram`), and over such a chart the base
change vanishes by
`AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_site_chart`,
whose second hypothesis is
`AlgebraicGeometry.Space.ModuleMapSituation.smul_chartRing_baseChangeSpace_site_eq_zero`.

**The ideal lives in `Γ(Y₀, ⊤)` and not in `Γ(S, ⊤)`.**  The vanishing over a chart is tested on
the ring of functions of the base change of that chart, which is an algebra over `Γ(Y₀, ⊤)`
through the chart's morphism to `Y₀`; an ideal of the functions on the site's own base acts on it
only through `Γ(Y₀, ⊤)`, so stating the hypotheses there would constrain a different ring of
scalars than the one `X ×_{Y₀} T` is built over.  The terminal-base case
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.isZeroAt_specQuotient_of_forall_mem_smul_top`
is the instance `Y₀ = AlgebraicGeometry.Space.baseTerminal`, where `Γ(Y₀, ⊤)` *is* `Γ(S, ⊤)`.

The two hypotheses are independent of the conclusion: `hJT` is a condition on `T` and `J` alone,
in which neither `u` nor any chart of `X` occurs, and `hJ` is a condition on `u` and `J` alone,
in which `T` does not occur.  Each is satisfied by `J = ⊥`, where the conclusion is the assertion
that `u_T` vanishes and is in general false. -/
theorem isZeroAt_of_forall_mem_smul_top (D : ModuleMapSituation.{u, u} B S hS)
    {Y₀ : BigFppfOver B S hS} (hDY : D.Y = schemeSpace Y₀) (T : D.SchemesOver)
    (k : T.left ⟶ Y₀) (hk : T.hom.hom ≫ (eqToHom hDY).hom = yoneda.map k)
    (α : ∀ A : SmallEtale B S hS D.X.1, chartFppfObject B S hS D.X A ⟶ Y₀)
    (hα : ∀ A : SmallEtale B S hS D.X.1,
      (A.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map (α A))
    (J : Ideal (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u))
    (hJT : J ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map k).appTop.hom)
    (hJ : ∀ A : SmallEtale B S hS D.X.1,
      IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
      letI : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          (D.G.val.obj (op A) : Type u) :=
        Module.compHom _ (chartToSiteRingHom B S hS D.X A (α A))
      ∀ m : D.F.val.obj (op A), D.u.val.app (op A) m ∈
        J • (⊤ : Submodule (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          (D.G.val.obj (op A) : Type u))) :
    D.IsZeroAt (modulePullbackSystem B S hS) T := by
  refine Modules.eq_zero_of_ofArrows B S hS
    (D.baseChangeHom (modulePullbackSystem B S hS) T) fun U => ?_
  obtain ⟨I, Z, π, hcov, hgood⟩ := exists_ofArrows_hasAffineChartDiagram B S hS
    (D.baseChangeProjection T) U
  refine ⟨I, Z, π, hcov, fun j => ?_⟩
  obtain ⟨hWaff, V, q, hcomm, hVaff⟩ := hgood j
  exact modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_site_chart B S hS
    (D.baseChangeProjection T) D.quasicoherent_F D.quasicoherent_G D.u
    { U := Z j, V := V, g := q, comm := hcomm.symm } hWaff hVaff (α V) J (hJ V hVaff)
    (smul_chartRing_baseChangeSpace_site_eq_zero B S hS D hDY T k hk
      { U := Z j, V := V, g := q, comm := hcomm.symm } (α V) (hα V) J hJT)

end ModuleMapSituation

namespace ModuleMapFlatTargetSituation

variable [IsAffine S] (D : ModuleMapFlatTargetSituation B S hS)

/-- **`u_Z = 0`.**  Let `J` be an ideal of the functions on the affine base which kills the image
of `u` over every affine étale chart of `X`.  Then the base change of `u` to `X ×_S Z`, for
`Z = \Spec(\Gamma(S, ⊤)/J)`, is zero.

Vanishing of a map of `𝒪`-modules is étale local, the charts of `X ×_S Z` carrying a diagram of
affine étale charts over the projection are cover-dense, and over such a chart the base change
vanishes by
`AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_chart`.

This is `AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_of_forall_mem_smul_top` at
`Y₀ = AlgebraicGeometry.Space.baseTerminal`, where the target of the situation *is* the algebraic
space of the final object of the category by
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.toModuleMapSituation_Y`, the test object is
`Z = \Spec(\Gamma(S, ⊤)/J)` with its unique morphism to the base, each chart is given the
vertical morphism of `AlgebraicGeometry.Space.baseChartDiagram` — along which the relative
pullback of functions is pullback of functions to the base by definition — and the hypothesis
that `J` dies in `\Gamma(Z, ⊤)` is `AlgebraicGeometry.ker_appTop_specQuotientToBase`. -/
theorem isZeroAt_specQuotient_of_forall_mem_smul_top (J : Ideal Γ(S, ⊤))
    (hJ : ∀ V : SmallEtale B S hS D.X.1,
      IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj V) →
      letI : Module Γ(S, ⊤) (D.G.val.obj (op V) : Type u) :=
        Module.compHom _ (chartToBaseRingHom B S hS D.X V)
      ∀ m : D.F.val.obj (op V), D.u.val.app (op V) m ∈
        J • (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op V) : Type u))) :
    (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.specQuotientTest B S hS J) :=
  ModuleMapSituation.isZeroAt_of_forall_mem_smul_top B S hS (D.toModuleMapSituation B S hS)
    (D.toModuleMapSituation_Y B S hS) (D.baseTest B S hS (specQuotientOver B S hS J))
    (toBaseTerminal B S hS (specQuotientOver B S hS J))
    (D.baseTest_hom_comp_eqToHom B S hS (specQuotientOver B S hS J))
    (fun A => (baseChartDiagram B S hS (D.toModuleMapSituation B S hS).X A).g)
    (fun A => D.chartToBase_comp_eqToHom B S hS A) J
    (ker_appTop_specQuotientToBase S J).ge hJ

/-- **The main clause of Stacks 083K for an affine test object.**

In the situation of Stacks 0CWA over an affine base `S`, let `T` be an affine object of the big
fppf category over `S` at which the base change of `u` vanishes.  Then there is a closed
subscheme `Z ⊆ S` through which `T ⟶ S` factors and at which the base change of `u` vanishes.

The subscheme is `Z = \Spec(\Gamma(S, ⊤)/I)` for `I = \ker(\Gamma(S, ⊤) ⟶ \Gamma(T, ⊤))` — the
smallest closed subscheme of `S` through which `T ⟶ S` factors.  That `I` kills the image of `u`
over every affine chart is
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.val_app_mem_ker_smul_top_of_isZeroAt`, and
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.isZeroAt_specQuotient_of_forall_mem_smul_top`
turns that into `u_Z = 0`.  The factorisation is
`AlgebraicGeometry.Space.exists_hom_specQuotientOver`, for which the inclusion of ideals is an
equality here.

See the implementation notes of this file for why the test object is asked to be affine and why
no `stacks` attribute is claimed. -/
theorem exists_closedSubscheme_isZeroAt_of_isZeroAt (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hzero : (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.baseTest B S hS T)) :
    ∃ Z : BigFppfOver B S hS,
      _root_.AlgebraicGeometry.IsClosedImmersion (B.inclusion.map Z.hom) ∧ Nonempty (T ⟶ Z) ∧
        (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
          (D.baseTest B S hS Z) := by
  refine ⟨specQuotientOver B S hS
      (RingHom.ker (show Γ(S, ⊤) →+*
          (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) from
        (B.inclusion.map T.hom).appTop.hom)),
    ?_, exists_hom_specQuotientOver B S hS _ T le_rfl, ?_⟩
  · exact isClosedImmersion_specQuotientToBase S _
  · exact isZeroAt_specQuotient_of_forall_mem_smul_top B S hS D _
      fun V hV => val_app_mem_ker_smul_top_of_isZeroAt B S hS D T V hzero hT hV

end ModuleMapFlatTargetSituation

end AlgebraicGeometry.Space

end
