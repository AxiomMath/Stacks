module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionTrivialChart
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionValueDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionsMeromorphic
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# A meromorphic section of an invertible module is an honest section on a nonempty chart

Let `X` be an algebraic space over a scheme `S` satisfying hypotheses (a) and (b) of
Stacks 0ENA — every weakly associated point has codimension `0`, and the quasi-compact opens of
the étale scheme charts have finitely many irreducible components — let `ℒ` be an *invertible*
`𝒪_X`-module and let `s` be a meromorphic section of `ℒ`.  Then over a suitable étale chart `s`
is an **honest** section of `ℒ`, that is it lies in the image of the canonical map
`ℒ ⟶ 𝒦_X(ℒ)` of `AlgebraicGeometry.Space.toMeromorphicSectionValue`; and the chart can be taken
over any prescribed chart `C` of `X` and with nonempty underlying scheme, provided `C` itself has
a point.

This is the first sentence of the proof of Stacks 0EPS, in the only form that sentence is used:
the source says that a *regular* `s` generates `ℒ` over a nonempty open subspace, and the
subsequent argument uses only that `s` is there a section of `ℒ`.  Regularity is accordingly not
a hypothesis below — a meromorphic section of an invertible module is honest on a nonempty chart
whether or not it is regular, the zero section being honest everywhere.

## Main results

* `AlgebraicGeometry.Space.exists_nonempty_chart_eval_eq_toMeromorphicSectionValue`: over some
  nonempty étale chart lying over a prescribed chart `C` of `X`, the meromorphic section `s` of
  the invertible module `ℒ` is the image of a section of `ℒ`.

## Implementation notes

The chart is produced by three refinements of `C` and one shrinking inside a Zariski open, and a
point is carried along all four so that the chart finally produced is nonempty — which is what
the consumer needs, the open subset of `|X|` it determines having to be nonempty.

1. Stacks 0B8Q on the small étale site
   (`AlgebraicGeometry.Space.exists_generator_cover_of_isInvertible`) gives a covering family of
   `C` over each member of which `ℒ` is free of rank one, compatibly over all charts below the
   member, so that `a ↦ a ⊗ e` is a bijection of the meromorphic functions onto the meromorphic
   sections.  A member through the given point is chosen by
   `AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range`, the pointwise
   criterion for covering sieves.
2. The sheaf `𝒦_X(ℒ)` of Stacks 0EN5 is a sheafification, so the value of `s` over that member
   is the image of an actual meromorphic section `ℒ ⊗_{𝒪_X} 𝒦_X` only over a covering sieve
   (`AlgebraicGeometry.Space.exists_eval_toMeromorphicSectionSheaf_sieve_mem`); a member of that
   sieve through the point is chosen by the same criterion.
3. An *affine* open of the scheme of that chart through the point is a chart of `X` by
   `AlgebraicGeometry.Space.openChart`, and the sieve is downward closed, so the presentation
   `a₀ ⊗ e` survives there.
4. Over the affine chart Stacks 0EN6, part (2)
   (`AlgebraicGeometry.Space.isFractionRing_meromorphicFunctionSheaf_obj`) writes the
   coefficient as `a₀ = p / q` with `q` a nonzerodivisor, and on the basic open `D(q)` the
   denominator becomes a unit (`AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`), so `a₀` is
   there the image of a regular function `r` and `a₀ ⊗ e = toMeromorphicSectionValue (r • e)` by
   `AlgebraicGeometry.Space.pureMeromorphicSection_smul_eq_algebraMap_tmul`.

That `D(q)` is nonempty is the one place hypothesis (a) is used beyond Stacks 0EN6: the generic
points of the chart scheme are dense, so the affine open chosen in step 3 contains one, and
`AlgebraicGeometry.mem_basicOpen_of_mem_nonZeroDivisors_of_mem_genericPoints` puts every generic
point of the chart scheme lying in an affine open into the basic open of a nonzerodivisor there.
This is the same argument the function-level
`AlgebraicGeometry.Space.exists_openSection_of_affineOpen` makes for `𝒦_X`, transposed to
`𝒦_X(ℒ)`; the two share `AlgebraicGeometry.Space.chartToMeromorphic_mul_eq_section`.

The statement is for an arbitrary invertible module, an arbitrary meromorphic section of it and
an arbitrary chart `C`, rather than for a chart coming from a presentation of the schematic locus
at the codimension-zero points: nothing in the argument looks at codimension zero, and the
consumers instantiate `C` differently — the first collection of Stacks 0EPS at a chart of `X`
itself, Stacks 0EQU at a chart attached to a prime divisor.

## References

* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **A meromorphic section of an invertible module is an honest section over some nonempty
chart.**  Let `X` be an algebraic space over `S` satisfying hypotheses (a) and (b) of
Stacks 0ENA, let `ℒ` be an invertible `𝒪_X`-module, let `s` be a meromorphic section of `ℒ` and
let `C` be an étale chart of `X` with a point.  Then there is an étale chart `W` of `X` over `C`,
with nonempty underlying scheme, over which `s` is the image under
`AlgebraicGeometry.Space.toMeromorphicSectionValue` of a section of `ℒ`.

This is the first sentence of the proof of Stacks 0EPS; see the implementation notes of this
module for the four steps and for why regularity of `s` is not needed. -/
theorem exists_nonempty_chart_eval_eq_toMeromorphicSectionValue
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (C : SmallEtale B S hS X.1) (x : chartScheme C) :
    ∃ (W : SmallEtale B S hS X.1) (_ : W ⟶ C) (e : L.val.obj (op W)),
      Nonempty (chartScheme W) ∧
        s.eval (op W) = toMeromorphicSectionValue B S hS X.1 X.2 L W e := by
  classical
  -- Step 1: a chart of `C` through `x` on which `ℒ` is free of rank one.
  obtain ⟨I, V, a, hcov, hfree⟩ := exists_generator_cover_of_isInvertible B S hS X L hL C
  obtain ⟨V₁, g₁, hg₁, x₁, -⟩ :=
    (SmallEtale.mem_topology_iff_exists_mem_range B S hS X.1 (Sieve.ofArrows V a)).1 hcov x
  obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff V a g₁).1 hg₁
  obtain ⟨e, hcompat, hbij⟩ := hfree i
  -- Step 2: a chart through `x₁` on which the value of `s` is an actual meromorphic section.
  obtain ⟨T, hT, hTloc⟩ :=
    exists_eval_toMeromorphicSectionSheaf_sieve_mem B S hS X.1 X.2 L V₁ (s.eval (op V₁))
  obtain ⟨V₂, k₂, hk₂, x₂, -⟩ :=
    (SmallEtale.mem_topology_iff_exists_mem_range B S hS X.1 T).1 hT x₁
  -- Step 3: an affine open of its scheme through `x₂`.
  obtain ⟨O, hOaff, hx₂O⟩ :
      ∃ O : (chartScheme V₂).Opens, IsAffineOpen O ∧ x₂ ∈ O := by
    obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x₂ ∈ ⨆ O : (chartScheme V₂).affineOpens, (O : (chartScheme V₂).Opens) from
        (iSup_affineOpens_eq_top (chartScheme V₂)).ge trivial)
    exact ⟨O.1, O.2, hO⟩
  -- The six charts, isomorphisms and morphisms below are introduced with `let` rather than
  -- `set`: none of their defining equations is used, and `set` additionally rewrites the
  -- occurrences of its body throughout the goal and context, which here is pure cost --
  -- the goal is still the untouched existential, and a term elaborated afterwards (`σ`)
  -- mentions `openChart ... O` anyway, so the abstraction is not even bought.  With `set`
  -- this proof does not elaborate inside the default heartbeat budget.
  let W : SmallEtale B S hS X.1 := openChart B S hS X.1 V₂ O
  let incl : W ⟶ V₂ := openChartInclusion B S hS X.1 V₂ O
  obtain ⟨t, ht⟩ := hTloc (incl ≫ k₂) (T.downward_closed hk₂ incl)
  have hsec : ∀ {U U' : SmallEtale B S hS X.1} (f : U' ⟶ U),
      ((meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 L).val.map f.op).hom (s.eval (op U)) =
        s.eval (op U') := fun f ↦ PresheafOfModules.sections_property
    (M := (meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 L).val) s f.op
  have hsW : toMeromorphicSectionSheaf B S hS X.1 X.2 L W t = s.eval (op W) := ht.trans (hsec _)
  obtain ⟨a₀, ha₀⟩ := (hbij W ((incl ≫ k₂) ≫ b)).2 t
  -- Step 4: the coefficient is a fraction over the affine chart.
  have hWaff : IsAffine (chartScheme W) := hOaff
  let : Algebra ((structurePresheaf B S hS X.1).obj (op W))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op W)) :=
    ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op W)).hom.toAlgebra
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin W hWaff
  obtain ⟨⟨p, qq⟩, hpq⟩ := IsLocalization.surj
    (nonZeroDivisors ((structurePresheaf B S hS X.1).obj (op W)))
    (show (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op W) from a₀)
  -- The denominator read on the chart scheme, and its basic open.
  let σ := (openChartGlobalSectionsIso V₂ O).commRingCatIsoToRingEquiv
  have hqnzd : σ qq.1 ∈ nonZeroDivisors Γ(chartScheme V₂, O) := by
    rw [← MulEquivClass.map_nonZeroDivisors σ]
    exact ⟨qq.1, qq.2, rfl⟩
  have hDqle : (chartScheme V₂).basicOpen (σ qq.1) ≤ O := Scheme.basicOpen_le _ _
  let W' : SmallEtale B S hS X.1 :=
    openChart B S hS X.1 V₂ ((chartScheme V₂).basicOpen (σ qq.1))
  let j : W' ⟶ W := openChartHomOfLE B S hS X.1 V₂ hDqle
  -- The basic open is nonempty: it contains a generic point of the chart scheme.
  obtain ⟨y, hyO, hygen⟩ :=
    (dense_iff_closure_eq.mpr genericPoints.closure :
      Dense (genericPoints (chartScheme V₂))).inter_open_nonempty _ O.isOpen ⟨x₂, hx₂O⟩
  have hyDq : y ∈ (chartScheme V₂).basicOpen (σ qq.1) :=
    mem_basicOpen_of_mem_nonZeroDivisors_of_mem_genericPoints
      (schemeWeaklyAssociatedPoints_chartScheme_subset_genericPoints B S hS X hwa V₂)
      (fun Wo hWo ↦ finite_irreducibleComponents_chartScheme B S hS hfin V₂ Wo hWo)
      hOaff hqnzd hygen hyO
  -- The denominator is a unit on the basic open.
  let σ' := (openChartGlobalSectionsIso V₂
    ((chartScheme V₂).basicOpen (σ qq.1))).commRingCatIsoToRingEquiv
  have hres : ((structurePresheaf B S hS X.1).map j.op).hom (σ.symm (σ qq.1)) =
      σ'.symm (((chartScheme V₂).presheaf.map (homOfLE hDqle).op).hom (σ qq.1)) :=
    ConcreteCategory.congr_hom
      (openChartGlobalSectionsIso_inv_comp B S hS X.1 V₂ hDqle) (σ qq.1)
  have hunit : IsUnit (((structurePresheaf B S hS X.1).map j.op).hom qq.1) := by
    rw [← σ.symm_apply_apply qq.1, hres]
    exact ((chartScheme V₂).toRingedSpace.isUnit_res_basicOpen (σ qq.1)).map σ'.symm
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hunit
  obtain ⟨r, hrdef⟩ : ∃ ρ : chartRing B S hS X.1 X.2 W',
      ρ = ((structurePresheaf B S hS X.1).map j.op).hom p * w := ⟨_, rfl⟩
  -- The restricted coefficient is the image of the regular function `r`.
  have hA0 : ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map j.op).hom a₀ =
      chartToMeromorphic W' r := by
    rw [hrdef]
    refine (chartToMeromorphic_mul_eq_section W' _ hw ?_).symm
    have h := congrArg (((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map j.op).hom) hpq
    rw [map_mul] at h
    rw [chartToMeromorphic_naturality j qq.1, chartToMeromorphic_naturality j p]
    exact h
  have hA : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS X.1 X.2).O).obj.map j.op).hom a₀ =
      algebraMap (chartRing B S hS X.1 X.2 W')
        ((meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op W')) r := hA0
  -- Assembling.
  refine ⟨W', j ≫ incl ≫ k₂ ≫ b ≫ a i, r • e W' (j ≫ ((incl ≫ k₂) ≫ b)), ⟨⟨y, hyDq⟩⟩, ?_⟩
  rw [← hsec j, ← hsW, toMeromorphicSectionSheaf_map B S hS X.1 X.2 L W W' j t, ← ha₀,
    meromorphicSectionModule_map_tmul B S hS X.1 X.2 L W W' j a₀ (e W ((incl ≫ k₂) ≫ b)),
    hcompat W W' ((incl ≫ k₂) ≫ b) j, hA, toMeromorphicSectionValue_eq,
    pureMeromorphicSection_smul_eq_algebraMap_tmul]

end AlgebraicGeometry.Space

end
