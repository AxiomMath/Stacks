module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramSieveRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionTrivialChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackCompIsoChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeAssertionsInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeProperties
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# The inverse image of a section vanishes exactly over its zero scheme

Let `X` be an algebraic space over a scheme `S`, let `L` be an invertible `𝒪_X`-module and let
`s ∈ Γ(X, L)`.  Stacks 0846 (2) says that a morphism `f : Y ⟶ X` of algebraic spaces satisfies
`f^*s = 0` in `Γ(Y, f^*L)` exactly when `f` factors through the zero scheme `Z(s)` of
Stacks 0845.  Applied on `Y` to `f^*s` and on `X` to `s`, it identifies `Z(f^*s)` with the
inverse image `f^{-1}(Z(s)) = Y ×_X Z(s)`, which is the identification `D' = X' ×_X D = Z(s')`
of Stacks 0ER3.

The proof is chartwise.  By the factorization criterion of Stacks 03MB on affine chart diagrams
(`AlgebraicGeometry.Space.exists_comp_eq_iff_forall_chartDiagram_definingIdealAt_le`), and since
the zero scheme of a section of an invertible module is cut out on affine charts by the
evaluation ideal of the section, `f` factors through `Z(s)` exactly when pullback of regular
functions along every affine chart diagram over `f` kills that evaluation ideal.  Over an affine
chart diagram the sections of `f^*L` are the base change of those of `L`
(`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`), and
the value of `f^*s` is `1 ⊗ s`; so `f^*s` vanishing there kills the evaluation ideal.
Conversely, over a chart where `L` is free with generator `t`, `s = c • t` with `c` in the
evaluation ideal and `f^*s = ψ^*(c) • f^*t`, and such charts cover.

## Main results

* `AlgebraicGeometry.Space.modulePullbackSections_eq_zero_iff_exists_comp_eq_zeroScheme`:
  **Stacks 0846 (2).**
* `AlgebraicGeometry.Space.sectionsMap_modulePullbackCompIso_modulePullbackSections`: the
  comparison `a^*(b^*M) ≅ (a ≫ b)^*M` carries `a^*(b^*σ)` to `(a ≫ b)^*σ`.
* `AlgebraicGeometry.Space.zeroScheme_modulePullbackSections`: `Z(f^*s) = f^{-1}(Z(s))`.

## References

* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two global sections that agree on `V` agree on every `Z ⟶ V`. -/
private theorem sections_val_eq_of_restrict_eq {X : AlgebraicSpaces B S hS}
    {N : Modules.{u, u} B S hS X.1 X.2} (ρ τ : N.sections) {Z V : SmallEtale B S hS X.1}
    (h : Z ⟶ V) (hV : ρ.val (op V) = τ.val (op V)) : ρ.val (op Z) = τ.val (op Z) := by
  exact (PresheafOfModules.sections_property (M := N.val) ρ h.op).symm.trans
    ((congrArg _ hV).trans (PresheafOfModules.sections_property (M := N.val) τ h.op))

/-- Two global sections that agree on `V` have equal restrictions to `Z ⟶ V ⟶ U` of their values
on `U`. -/
private theorem map_comp_val_eq_of_val_eq {X : AlgebraicSpaces B S hS}
    {N : Modules.{u, u} B S hS X.1 X.2} (ρ τ : N.sections) {Z V U : SmallEtale B S hS X.1}
    (h : Z ⟶ V) (g : V ⟶ U) (hV : ρ.val (op V) = τ.val (op V)) :
    N.val.map (h ≫ g).op (ρ.val (op U)) = N.val.map (h ≫ g).op (τ.val (op U)) := by
  exact (PresheafOfModules.sections_property (M := N.val) ρ (h ≫ g).op).trans
    ((sections_val_eq_of_restrict_eq B S hS ρ τ h hV).trans
      (PresheafOfModules.sections_property (M := N.val) τ (h ≫ g).op).symm)

/-- If the inverse image of a section vanishes over the chart of an affine chart diagram, then
pullback of regular functions along the diagram kills the evaluation ideal of the section. -/
theorem sectionEvaluationIdealAt_le_ker_of_modulePullbackSections_val_eq_zero
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : L.IsQuasicoherentOnSite) (s : L.sections) (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (haU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (h0 : (modulePullbackSections B S hS f L s).val (op d.U) = 0) :
    sectionEvaluationIdealAt B S hS X L s d.V ≤ RingHom.ker (chartDiagramRestrict B S hS f d) := by
  let := chartDiagramAlgebra B S hS f d
  rw [modulePullbackSections_val] at h0
  have hinj := (bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS f L hL d
    haU haV).1
  have h1 : TensorProduct.tmul (chartRing B S hS X.1 X.2 d.V) (1 : chartRing B S hS Y.1 Y.2 d.U)
      (s.eval (op d.V)) = 0 := by
    refine hinj ?_
    rw [map_zero, modulePullbackChartBaseChange_tmul, one_smul]
    exact h0
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨l, rfl⟩
  have h2 := congrArg (fun z => TensorProduct.AlgebraTensorModule.rid
    (chartRing B S hS X.1 X.2 d.V) (chartRing B S hS Y.1 Y.2 d.U)
      (chartRing B S hS Y.1 Y.2 d.U) (LinearMap.baseChange (chartRing B S hS Y.1 Y.2 d.U) l z)) h1
  simp only [LinearMap.baseChange_tmul, map_zero, TensorProduct.AlgebraTensorModule.rid_tmul]
    at h2
  show chartDiagramRestrict B S hS f d (l (s.eval (op d.V))) = 0
  rw [← chartDiagramAlgebra_algebraMap B S hS f d, Algebra.algebraMap_eq_smul_one]
  exact h2

/-- Over a chart diagram whose chart of `X` carries a free generator `t` of `L`, the inverse image
of a section vanishes on the chart of `Y` as soon as pullback of regular functions along the
diagram kills the evaluation ideal of the section: the section is `c • t` with `c` in that ideal,
and the inverse image is `ψ^*(c) • f^*t`. -/
theorem modulePullbackSections_val_eq_zero_of_le_ker {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (L : Modules.{u, u} B S hS X.1 X.2) (s : L.sections)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom) (t : L.val.obj (op d.V))
    (ht : Function.Bijective fun r : chartRing B S hS X.1 X.2 d.V ↦ r • t)
    (hle : sectionEvaluationIdealAt B S hS X L s d.V ≤
      RingHom.ker (chartDiagramRestrict B S hS f d)) :
    (modulePullbackSections B S hS f L s).val (op d.U) = 0 := by
  let e : chartRing B S hS X.1 X.2 d.V ≃ₗ[chartRing B S hS X.1 X.2 d.V] L.val.obj (op d.V) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ t) ht
  have hc : e.symm (s.eval (op d.V)) • t = s.eval (op d.V) :=
    e.apply_symm_apply (s.eval (op d.V))
  have hker : chartDiagramRestrict B S hS f d (e.symm (s.eval (op d.V))) = 0 :=
    hle (Ideal.subset_span ⟨e.symm.toLinearMap, rfl⟩)
  rw [modulePullbackSections_val]
  show modulePullbackChartSection B S hS f L d (s.eval (op d.V)) = 0
  rw [← hc, modulePullbackChartSection_smul, hker, zero_smul]

/-- Over every affine chart diagram the inverse image of a section of an invertible module
vanishes on the chart of `Y`, as soon as pullback along every affine chart diagram kills the
evaluation ideal: the chart diagram is refined to ones whose chart of `X` carries a free generator
of `L` (Stacks 0B8Q), on which
`AlgebraicGeometry.Space.modulePullbackSections_val_eq_zero_of_le_ker` applies. -/
theorem modulePullbackSections_val_eq_zero_of_forall_le_ker {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (L : Modules.{u, u} B S hS X.1 X.2)
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L) (s : L.sections)
    (hle : ∀ d : ChartDiagram B S hS Y.1 X.1 f.hom,
      IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
        sectionEvaluationIdealAt B S hS X L s d.V ≤
          RingHom.ker (chartDiagramRestrict B S hS f d))
    (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (haU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    (modulePullbackSections B S hS f L s).val (op d.U) = 0 := by
  obtain ⟨I, V, a, hcov, hfree⟩ := exists_generator_cover_smul_of_isInvertible B S hS X L hinv d.V
  obtain ⟨n, d', a', k, hU', hV', hT, -, hcov'⟩ :=
    exists_affine_chartDiagram_cover_of_sieve B S hS f d haU haV hcov
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _ hcov' ?_
  rintro W g ⟨Z, h, g', ⟨i⟩, rfl⟩
  obtain ⟨Z', h', g'', ⟨j⟩, hk⟩ := hT i
  obtain ⟨e, -, he⟩ := hfree j
  have hi : (modulePullbackSections B S hS f L s).val (op (d' i).U) = 0 :=
    modulePullbackSections_val_eq_zero_of_le_ker B S hS f L s (d' i) (e (d' i).V h')
      (he (d' i).V h') (hle (d' i) (hU' i) (hV' i))
  exact (map_comp_val_eq_of_val_eq B S hS _ 0 h (a' i) hi).trans (map_zero _)

/-- If pullback along every affine chart diagram kills the evaluation ideal of a section of an
invertible module, then the inverse image of the section is zero: it vanishes over the affine
chart diagrams, which cover every étale chart of `Y` by Stacks 03G2. -/
theorem modulePullbackSections_eq_zero_of_forall_le_ker {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (L : Modules.{u, u} B S hS X.1 X.2)
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L) (s : L.sections)
    (hle : ∀ d : ChartDiagram B S hS Y.1 X.1 f.hom,
      IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
        sectionEvaluationIdealAt B S hS X L s d.V ≤
          RingHom.ker (chartDiagramRestrict B S hS f d)) :
    modulePullbackSections B S hS f L s = 0 := by
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _
    (generate_affineChartDiagram_mem_topology B S hS f (fun _ => True) (fun _ _ => trivial)
      U.unop) ?_
  rintro W g ⟨Z, h, g', ⟨hU, d, rfl, hV, -⟩, rfl⟩
  have hd := modulePullbackSections_val_eq_zero_of_forall_le_ker B S hS f L hinv s hle d
    hU hV
  exact (map_comp_val_eq_of_val_eq B S hS _ 0 h g' hd).trans (map_zero _)

/-- **Stacks 0846 (2).** Let `L` be an invertible `𝒪_X`-module, `s` a global section of `L` and
`f : Y ⟶ X` a morphism of algebraic spaces.  Then `f^*s = 0` exactly when `f` factors through
the zero scheme `Z(s)` of Stacks 0845.

Here `f^*s` is the inverse image of the global section along `f`,
`AlgebraicGeometry.Space.modulePullbackSections`, a global section of the inverse image `f^*L`
of Stacks 03LU. -/
theorem modulePullbackSections_eq_zero_iff_exists_comp_eq_zeroScheme
    (X Y : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS X.1 X.2)
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : L.sections) (f : Y ⟶ X) :
    modulePullbackSections B S hS f L s = 0 ↔
      ∃ g : Y ⟶ (⟨(zeroScheme B S hS X L s).1.toFunctor,
          (zeroScheme B S hS X L s).2.1⟩ : AlgebraicSpaces B S hS),
        g ≫ ObjectProperty.homMk (zeroScheme B S hS X L s).1.ι = f := by
  obtain ⟨Z, hZ⟩ := exists_definingIdealAt_eq_sectionEvaluationIdealAt_of_isInvertible B S hS X L
    s hinv
  have hqc : L.IsQuasicoherentOnSite := isQuasicoherentOnSite_of_isInvertible B S hS X L hinv
  rw [exists_comp_eq_iff_forall_chartDiagram_definingIdealAt_le]
  constructor
  · intro h0 d hU hV
    rw [definingIdealAt_zeroScheme_eq B S hS X L s Z hZ d.V hV]
    refine sectionEvaluationIdealAt_le_ker_of_modulePullbackSections_val_eq_zero B S hS f L hqc s
      d hU hV ?_
    rw [h0]
    rfl
  · intro hle
    refine modulePullbackSections_eq_zero_of_forall_le_ker B S hS f L hinv s fun d hU hV => ?_
    have h := hle d hU hV
    rwa [definingIdealAt_zeroScheme_eq B S hS X L s Z hZ d.V hV] at h

/-- **The inverse image of a global section is compatible with composition, on a chart.**  Over
étale charts `U ⟶ V ⟶ W` of `X'`, `Y` and `X` lying over `a : X' ⟶ Y` and `b : Y ⟶ X`, the
comparison `a^*(b^*M) ⟶ (a ≫ b)^*M` of Stacks 03LU carries the value of `a^*(b^*σ)` at `U` to
the value of `(a ≫ b)^*σ` at `U`. -/
theorem modulePullbackCompIso_hom_val_app_modulePullbackSections
    {X' X Y : AlgebraicSpaces B S hS} (a : X' ⟶ Y) (b : Y ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (σ : M.sections)
    {U : SmallEtale B S hS X'.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS X.1}
    (p : (SmallEtale.toOver B S hS X'.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (q : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj W)
    (hp : U.1.hom ≫ a.hom = yoneda.map p ≫ V.1.hom)
    (hq : V.1.hom ≫ b.hom = yoneda.map q ≫ W.1.hom) :
    ((modulePullbackCompIso B S hS a b).hom.app M).val.app (op U)
        ((modulePullbackSections B S hS a ((modulePullback B S hS b).obj M)
          (modulePullbackSections B S hS b M σ)).val (op U)) =
      (modulePullbackSections B S hS (a ≫ b) M σ).val (op U) := by
  have h1 := modulePullbackSections_val B S hS a ((modulePullback B S hS b).obj M)
    (modulePullbackSections B S hS b M σ) ⟨U, V, p, hp⟩
  have h2 := modulePullbackSections_val B S hS b M σ ⟨V, W, q, hq⟩
  have h3 := modulePullbackSections_val B S hS (a ≫ b) M σ
    (ChartDiagram.comp B S hS a b p q hp hq)
  have h4 := modulePullbackCompIso_hom_val_app_modulePullbackUnitSection B S hS a b p q hp hq M
    (σ.val (op W))
  simp only [modulePullbackUnitSection_eq_modulePullbackChartSection] at h4
  have e_b := modulePullbackUnitSection_eq_modulePullbackChartSection B S hS b M ⟨V, W, q, hq⟩
    (σ.val (op W))
  have e_ab := modulePullbackUnitSection_eq_modulePullbackChartSection B S hS (a ≫ b) M
    (ChartDiagram.comp B S hS a b p q hp hq) (σ.val (op W))
  refine Eq.trans ?_ ((h4.trans e_ab).trans h3.symm)
  refine congrArg _ (h1.trans ?_)
  exact congrArg _ (h2.trans e_b.symm)

/-- Two global sections of a sheaf of modules on the small étale site agree as soon as, on every
étale chart, they agree after restriction along the members of a covering sieve. -/
theorem sections_eq_of_locally_eq {X : AlgebraicSpaces B S hS} {N : Modules.{u, u} B S hS X.1 X.2}
    (ρ τ : N.sections)
    (h : ∀ U : SmallEtale B S hS X.1, ∃ R : Sieve U, R ∈ SmallEtale.topology B S hS X.1 U ∧
      ∀ ⦃Z : SmallEtale B S hS X.1⦄ (g : Z ⟶ U), R g → ρ.val (op Z) = τ.val (op Z)) :
    ρ = τ := by
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  obtain ⟨R, hR, hRe⟩ := h U.unop
  have hz : ρ.val U - τ.val U = 0 := by
    refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _ hR ?_
    intro Z g hg
    have h1 := PresheafOfModules.sections_property (M := N.val) ρ g.op
    have h2 := PresheafOfModules.sections_property (M := N.val) τ g.op
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (h1.trans ((hRe g hg).trans h2.symm)))
  exact sub_eq_zero.1 hz

/-- **The inverse image of a global section is compatible with composition.**  The comparison
`a^*(b^*M) ≅ (a ≫ b)^*M` of Stacks 03LU carries `a^*(b^*σ)` to `(a ≫ b)^*σ`.

Both are computed on composite chart diagrams by
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_val_app_modulePullbackSections`, and the
composite chart diagrams cover every chart, the affine chart diagrams being cofinal (Stacks
03G2). -/
theorem sectionsMap_modulePullbackCompIso_modulePullbackSections
    {X' X Y : AlgebraicSpaces B S hS} (a : X' ⟶ Y) (b : Y ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (σ : M.sections) :
    SheafOfModules.sectionsMap ((modulePullbackCompIso B S hS a b).hom.app M)
        (modulePullbackSections B S hS a ((modulePullback B S hS b).obj M)
          (modulePullbackSections B S hS b M σ)) =
      modulePullbackSections B S hS (a ≫ b) M σ := by
  -- agreement over the chart of an affine chart diagram over `a`
  have hd : ∀ d : ChartDiagram B S hS X'.1 Y.1 a.hom,
      IsAffine ((SmallEtale.toOver B S hS X'.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
      IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
      (SheafOfModules.sectionsMap ((modulePullbackCompIso B S hS a b).hom.app M)
          (modulePullbackSections B S hS a ((modulePullback B S hS b).obj M)
            (modulePullbackSections B S hS b M σ))).val (op d.U) =
        (modulePullbackSections B S hS (a ≫ b) M σ).val (op d.U) := by
    intro d hU hV
    obtain ⟨n, d', a', k, -, -, hT, -, hcov⟩ := exists_affine_chartDiagram_cover_of_sieve B S hS a d
      hU hV (generate_affineChartDiagram_mem_topology B S hS b (fun _ => True)
        (fun _ _ => trivial) d.V)
    have hi : ∀ i, (SheafOfModules.sectionsMap ((modulePullbackCompIso B S hS a b).hom.app M)
          (modulePullbackSections B S hS a ((modulePullback B S hS b).obj M)
            (modulePullbackSections B S hS b M σ))).val (op (d' i).U) =
        (modulePullbackSections B S hS (a ≫ b) M σ).val (op (d' i).U) := by
      intro i
      obtain ⟨Z'', h', g'', ⟨-, e, rfl, -, -⟩, -⟩ := hT i
      have hq : (d' i).V.1.hom ≫ b.hom =
          yoneda.map ((SmallEtale.toOver B S hS Y.1).map h' ≫ e.g) ≫ e.V.1.hom := by
        rw [Functor.map_comp, Category.assoc, ← e.comm, ← Category.assoc]
        exact congrArg (· ≫ b.hom) (CostructuredArrow.w h'.hom).symm
      exact (PresheafOfModules.sectionsMap_coe _ _ _).trans
        (modulePullbackCompIso_hom_val_app_modulePullbackSections B S hS a b M σ (d' i).g
          ((SmallEtale.toOver B S hS Y.1).map h' ≫ e.g) (d' i).comm hq)
    have hz : (SheafOfModules.sectionsMap ((modulePullbackCompIso B S hS a b).hom.app M)
          (modulePullbackSections B S hS a ((modulePullback B S hS b).obj M)
            (modulePullbackSections B S hS b M σ))).val (op d.U) -
        (modulePullbackSections B S hS (a ≫ b) M σ).val (op d.U) = 0 := by
      refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _ hcov ?_
      rintro Z g ⟨Z', h, g', ⟨i⟩, rfl⟩
      refine (map_sub _ _ _).trans (sub_eq_zero.2 ?_)
      exact map_comp_val_eq_of_val_eq B S hS _ _ h (a' i) (hi i)
    exact sub_eq_zero.1 hz
  refine sections_eq_of_locally_eq B S hS _ _ fun U => ⟨_,
    generate_affineChartDiagram_mem_topology B S hS a (fun _ => True) (fun _ _ => trivial) U, ?_⟩
  rintro Z g ⟨Z', h, g', ⟨hU, d, rfl, hV, -⟩, rfl⟩
  exact sections_val_eq_of_restrict_eq B S hS _ _ h (hd d hU hV)

/-- A morphism of sheaves of modules carries the zero global section to zero. -/
theorem sectionsMap_zero {X : AlgebraicSpaces B S hS} {N N' : Modules.{u, u} B S hS X.1 X.2}
    (φ : N ⟶ N') : SheafOfModules.sectionsMap φ 0 = 0 :=
  PresheafOfModules.sections_ext _ _ fun _ => map_zero _

/-- An isomorphism of sheaves of modules carries a global section to zero only if it is zero. -/
theorem sectionsMap_eq_zero_iff_of_iso {X : AlgebraicSpaces B S hS}
    {N N' : Modules.{u, u} B S hS X.1 X.2} (e : N ≅ N') (x : N.sections) :
    SheafOfModules.sectionsMap e.hom x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h' := congrArg (SheafOfModules.sectionsMap e.inv) h
    rwa [← SheafOfModules.sectionsMap_comp, e.hom_inv_id, SheafOfModules.sectionsMap_id,
      sectionsMap_zero] at h'
  · rintro rfl
    exact sectionsMap_zero B S hS e.hom

/-- A morphism `g : T ⟶ Y` factors through the inverse image `f^{-1}(Z)` of a closed subspace
`Z ⊆ X` along `f : Y ⟶ X` exactly when `g ≫ f` factors through `Z`. -/
theorem exists_comp_eq_preimage_iff {X Y T : AlgebraicSpaces B S hS} (f : Y ⟶ X) (g : T ⟶ Y)
    (Z : ClosedSubspaces B S hS X.1) :
    (∃ g' : T ⟶ (⟨(Z.1.preimage f.hom).toFunctor,
        (isClosedSubspace_preimage B S hS f.hom Z.1 X.2 Y.2 Z.2).1⟩ : AlgebraicSpaces B S hS),
      g' ≫ ObjectProperty.homMk (Z.1.preimage f.hom).ι = g) ↔
      ∃ g' : T ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS),
        g' ≫ ObjectProperty.homMk Z.1.ι = g ≫ f := by
  rw [exists_comp_eq_iff_range_le B S hS ⟨Z.1.preimage f.hom,
      isClosedSubspace_preimage B S hS f.hom Z.1 X.2 Y.2 Z.2⟩ g,
    exists_comp_eq_iff_range_le B S hS Z (g ≫ f)]
  show _ ↔ Subfunctor.range (g.hom ≫ f.hom) ≤ Z.1
  rw [Subfunctor.range_comp, Subfunctor.image_le_iff]

/-- Two closed subspaces of an algebraic space through which the same morphisms factor are
equal. -/
theorem closedSubspaces_eq_of_forall_exists_comp_eq_iff {Y : AlgebraicSpaces B S hS}
    (Z₁ Z₂ : ClosedSubspaces B S hS Y.1)
    (h : ∀ (T : AlgebraicSpaces B S hS) (g : T ⟶ Y),
      (∃ g' : T ⟶ (⟨Z₁.1.toFunctor, Z₁.2.1⟩ : AlgebraicSpaces B S hS),
          g' ≫ ObjectProperty.homMk Z₁.1.ι = g) ↔
        ∃ g' : T ⟶ (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS),
          g' ≫ ObjectProperty.homMk Z₂.1.ι = g) :
    Z₁ = Z₂ := by
  have key : ∀ Z Z' : ClosedSubspaces B S hS Y.1,
      (∀ (T : AlgebraicSpaces B S hS) (g : T ⟶ Y),
        (∃ g' : T ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS),
            g' ≫ ObjectProperty.homMk Z.1.ι = g) →
          ∃ g' : T ⟶ (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS),
            g' ≫ ObjectProperty.homMk Z'.1.ι = g) → Z.1 ≤ Z'.1 := by
    intro Z Z' hZ
    have h' := (exists_comp_eq_iff_range_le B S hS Z' (ObjectProperty.homMk Z.1.ι)).1
      (hZ _ _ ⟨𝟙 _, Category.id_comp _⟩)
    rwa [show (ObjectProperty.homMk Z.1.ι : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
        Y).hom = Z.1.ι from rfl, Subfunctor.range_ι] at h'
  exact Subtype.ext (le_antisymm (key Z₁ Z₂ fun T g => (h T g).1)
    (key Z₂ Z₁ fun T g => (h T g).2))

/-- **Stacks 0ER3: the zero scheme of a pulled-back section is the inverse image of the zero
scheme.**  For an
invertible `𝒪_X`-module `L`, a global section `s` and a morphism `f : Y ⟶ X` of algebraic spaces,
`Z(f^*s) = f^{-1}(Z(s)) = Y ×_X Z(s)` as closed subspaces of `Y`.

Both sides are characterized by the morphisms factoring through them: by Stacks 0846 (2) on `Y`
(`f^*L` is invertible, Stacks 0B8P) and on `X`, a morphism `g` factors through `Z(f^*s)` exactly
when `g^*(f^*s) = (g ≫ f)^*s` vanishes, exactly when `g ≫ f` factors through `Z(s)`. -/
theorem zeroScheme_modulePullbackSections (X Y : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : L.sections) (f : Y ⟶ X) :
    zeroScheme B S hS Y ((modulePullback B S hS f).obj L) (modulePullbackSections B S hS f L s) =
      ⟨(zeroScheme B S hS X L s).1.preimage f.hom,
        isClosedSubspace_preimage B S hS f.hom (zeroScheme B S hS X L s).1 X.2 Y.2
          (zeroScheme B S hS X L s).2⟩ := by
  refine closedSubspaces_eq_of_forall_exists_comp_eq_iff B S hS _ _ fun T g => ?_
  rw [exists_comp_eq_preimage_iff B S hS f g (zeroScheme B S hS X L s),
    ← modulePullbackSections_eq_zero_iff_exists_comp_eq_zeroScheme B S hS Y T _
      (isInvertible_modulePullback_obj B S hS f L hinv),
    ← modulePullbackSections_eq_zero_iff_exists_comp_eq_zeroScheme B S hS X T L hinv,
    ← sectionsMap_modulePullbackCompIso_modulePullbackSections B S hS g f]
  exact (sectionsMap_eq_zero_iff_of_iso B S hS ((modulePullbackCompIso B S hS g f).app L) _).symm

end AlgebraicGeometry.Space

end
