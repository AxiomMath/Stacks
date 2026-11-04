module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentArtinRees
public import StacksFrontier.LinearAlgebra.TensorProduct.SubmoduleFaithfullyFlatDescent

/-!
# The sections of `Iⁿ M` over an affine étale chart

Let `F` be an algebraic space, let `I ⊆ 𝒪_F` be a sheaf of ideals and `M` an `𝒪_F`-module, both
quasi-coherent, and let `V` be an *affine* étale chart of `F`.  Then

`(Iⁿ M)(V) = I(V)ⁿ · M(V)`

as submodules of `M(V)`: the sections of the product over an affine chart are the honest product
of the `n`-th power of the ideal of sections with the sections of the module.

The inclusion `⊇` is formal and is
`AlgebraicGeometry.Space.pow_chartSectionIdeal_smul_top_le_chartSubmodule`.  This file proves
`⊆`, which is not: membership in `Iⁿ M` is étale-local *twice over*, since a section of `Iⁿ M` is
only locally a combination of products of a section of `Iⁿ` with a section of `M`, and a section
of `Iⁿ` is only locally an honest `n`-fold product of sections of `I`.  Reducing the exponent, as
in `Stacks.Sites.idealPowSmul_succ`, does not help: the exponent is not the obstruction.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_faithfullyFlat_refinement`: a covering
  sieve of an affine étale chart is refined by a finite family of affine charts along which the
  rings of regular functions are faithfully flat.
* `AlgebraicGeometry.Space.one_tmul_mem_baseChange_pow_chartSectionIdeal_smul_top`: on an affine
  chart over `V`, membership in the honest product is membership of `1 ⊗ x` in the base change of
  the honest product over `V`.
* `AlgebraicGeometry.Space.chartSubmodule_idealPowSubmodule_le_pow_chartSectionIdeal_smul_top`:
  **the inclusion `⊆`.**
* `AlgebraicGeometry.Space.chartSubmodule_idealPowSubmodule_eq_pow_chartSectionIdeal_smul_top` and
  `AlgebraicGeometry.Space.chartSubmodule_idealPowSubmodule_eq_of_isQuasicoherentOnSite`: **the
  equality**, from cartesianness on affine charts and from quasi-coherence respectively.

## Implementation notes

Both localizations are absorbed at once into the sieve

`R = {f : Y ⟶ V | x|_Y ∈ I(Y)ⁿ · M(Y)}`,

which is a sieve because restriction carries the honest product into the honest product
(`AlgebraicGeometry.Space.map_mem_pow_chartSectionIdeal_smul_top`) and is covering by the
local-character axiom applied to the two localization statements
`AlgebraicGeometry.Space.exists_sieve_of_mem_idealPowSmul` and
`AlgebraicGeometry.Space.exists_sieve_mem_pow_chartIdeal_smul_top`.  After that the statement is
descent along a single finite family, and no interleaving or cofinality of the two filtered
systems is needed.

The descent step uses four inputs, all in the library:

* the refinement of a covering sieve of an affine chart to a finite covering family of the
  *affine* étale site, `AlgebraicGeometry.Space.AffineEtale.exists_covering_refining_pullback`,
  which is where the joint surjectivity on the underlying schemes comes from — a covering sieve
  of the generated topology carries no surjectivity by itself, which is why
  `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement` is not the form used
  here;
* Descent, Proposition 03DX (2) for the small étale site of an algebraic space, in its two
  guises: `AlgebraicGeometry.Space.ideal_map_chartRestrict_chartIdeal` for the ideal and the
  bijectivity of `AlgebraicGeometry.Space.sectionsBaseChange` for the module;
* faithful flatness of the product of the restriction maps of a finite jointly surjective family
  of affine charts, `AlgebraicGeometry.Space.faithfullyFlat_pi_affineEtaleChartRings`;
* descent of membership in a submodule along such a family,
  `Submodule.mem_of_forall_one_tmul_mem_baseChange`.

The two cartesianness hypotheses are carried in the shape
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts` in the intermediate statements and discharged
from quasi-coherence in the final one, so nothing beyond quasi-coherence of `I` and of `M` is
required: in particular neither coherence of the module nor any Noetherian hypothesis on the
space enters.

No declaration here carries a `stacks` tag: this is one clause of the chart description of
Stacks 07UM, whose attribute is placed where both clauses close.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### A finite faithfully flat affine refinement of a covering sieve -/

/-- **A covering sieve of an affine étale chart is refined by a finite family of affine étale
charts along which the rings of regular functions are faithfully flat.**

The refinement is `AlgebraicGeometry.Space.AffineEtale.exists_covering_refining_pullback` at the
identity of the chart, which produces a covering family of the *affine* étale site, hence a
finite family of affine charts which is jointly surjective on the underlying schemes; faithful
flatness of the product of the restriction maps is then
`AlgebraicGeometry.Space.faithfullyFlat_pi_affineEtaleChartRings`. -/
theorem SmallEtale.exists_finite_affine_faithfullyFlat_refinement (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    {R : Sieve U} (hR : R ∈ SmallEtale.topology B S hS F U) :
    ∃ (ι : Type (u + 1)) (_ : Finite ι) (V : ι → SmallEtale B S hS F) (f : ∀ i, V i ⟶ U),
      (∀ i, IsAffine
          ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (V i))) ∧
        (∀ i, R (f i)) ∧
        (RingHom.pi (fun i => chartRestrict (hF := hF) (f i))).FaithfullyFlat := by
  obtain ⟨P, hP, hPle⟩ := AffineEtale.exists_covering_refining_pullback B S hS F hR
    (X := (⟨U, hU⟩ : AffineEtale B S hS F)) (𝟙 U)
  obtain ⟨E, rfl, hE⟩ := (AffineEtale.mem_precoverage_iff B S hS F).mp hP
  have _ : Finite E.I₀ := hE.2
  obtain ⟨hcov, -⟩ := (Scheme.presieve₀_mem_precoverage_iff
    (E.map (AffineEtale.toScheme B S hS F))).mp hE.1.2
  refine ⟨E.I₀, inferInstance, fun i => (AffineEtale.inclusion B S hS F).obj (E.X i),
    fun i => (AffineEtale.inclusion B S hS F).map (E.f i), fun i => (E.X i).property,
    fun i => ?_, ?_⟩
  · exact (congrArg (fun k => R.arrows k)
      (Category.comp_id ((AffineEtale.inclusion B S hS F).map (E.f i)))).mp (hPle (E.f i) ⟨i⟩)
  · exact faithfullyFlat_pi_affineEtaleChartRings B S hS F E.X E.f hcov
      (fun i => AffineEtale.flat_toScheme_map B S hS F (E.f i))

/-! ### The honest product on an affine chart over the given one -/

/-- **A section whose restriction to an affine chart over `V` lies in the honest product
`I(W)ⁿ · M(W)` has `1 ⊗ x` in the base change of the honest product `I(V)ⁿ · M(V)`.**

Both halves of Descent, Proposition 03DX (2) enter: the sections of `M` over `W` are the base
change of the sections over `V`, which identifies the two products, and the ideal of sections of
`I` over `W` is the extension of the ideal over `V`, which identifies the two coefficient
ideals. -/
theorem one_tmul_mem_baseChange_pow_chartSectionIdeal_smul_top
    (I : IdealSheaves B S hS F hF) (n : ℕ) (M : Modules.{u, u} B S hS F hF)
    {V W : SmallEtale B S hS F} (φ : W ⟶ V)
    (hMbij : Function.Bijective (sectionsBaseChange M φ))
    (hIsurj : Function.Surjective (sectionsBaseChange I.toSheafOfModules φ))
    {x : M.val.obj (op V)}
    (hx : chartRestrictLinear M φ x ∈ chartSectionIdeal B S hS F hF I W ^ n •
      (⊤ : Submodule (chartRing B S hS F hF W) (M.val.obj (op W)))) :
    letI := chartAlgebra (hF := hF) φ
    (1 : chartRing B S hS F hF W) ⊗ₜ[chartRing B S hS F hF V] x ∈
      Submodule.baseChange (chartRing B S hS F hF W)
        (chartSectionIdeal B S hS F hF I V ^ n •
          (⊤ : Submodule (chartRing B S hS F hF V) (M.val.obj (op V)))) := by
  let _ := chartAlgebra (hF := hF) φ
  let _ := chartSectionsModule M φ
  set e := LinearEquiv.ofBijective (sectionsBaseChange M φ) hMbij
  have hJ : Ideal.map (algebraMap (chartRing B S hS F hF V) (chartRing B S hS F hF W))
        (chartSectionIdeal B S hS F hF I V ^ n)
      = chartSectionIdeal B S hS F hF I W ^ n := by
    rw [Ideal.map_pow]
    exact congrArg (· ^ n) (ideal_map_chartRestrict_chartIdeal B S hS F hF I φ hIsurj)
  have hbc : Submodule.map e.toLinearMap
        (Submodule.baseChange (chartRing B S hS F hF W)
          (chartSectionIdeal B S hS F hF I V ^ n •
            (⊤ : Submodule (chartRing B S hS F hF V) (M.val.obj (op V)))))
      = chartSectionIdeal B S hS F hF I W ^ n •
        (⊤ : Submodule (chartRing B S hS F hF W) (M.val.obj (op W))) := by
    rw [← ArtinReesBaseChange.ideal_smul_top, Submodule.map_smul'', Submodule.map_top,
      LinearEquiv.range, hJ]
  have hcoe : e ((1 : chartRing B S hS F hF W) ⊗ₜ[chartRing B S hS F hF V] x)
      = chartRestrictLinear M φ x := chartBaseChange_one_tmul M φ x
  rw [← hbc, ← hcoe] at hx
  have h := (Submodule.mem_map_equiv _).1 hx
  rwa [e.symm_apply_apply] at h

/-! ### The sections over an affine chart -/

/-- **The sections of `Iⁿ M` over an affine étale chart are the honest product of the `n`-th
power of the ideal of sections of `I` with the sections of `M`**, the inclusion which is not
formal.

Membership in `Iⁿ M` is étale-local twice over: a section is only locally a combination of
products of a section of `Iⁿ` with a section of `M`, and a section of `Iⁿ` is only locally an
honest `n`-fold product of sections of `I`.  Both localizations are absorbed into the sieve `R`
of arrows along which `x` restricts into the honest product, which is covering by
`AlgebraicGeometry.Space.exists_sieve_mem_pow_chartIdeal_smul_top` and the local-character axiom.
That sieve is then refined by a finite family of affine charts along which the rings of regular
functions are faithfully flat, and membership in a submodule descends along such a family. -/
theorem chartSubmodule_idealPowSubmodule_le_pow_chartSectionIdeal_smul_top
    (I : IdealSheaves B S hS F hF) (n : ℕ) (M : Modules.{u, u} B S hS F hF)
    (hMcart : IsCartesianOnAffineCharts M)
    (hIcart : IsCartesianOnAffineCharts I.toSheafOfModules)
    (V : SmallEtale B S hS F)
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    chartSubmodule B S hS F hF (idealPowSubmodule I n M) V
      ≤ chartSectionIdeal B S hS F hF I V ^ n •
        (⊤ : Submodule (chartRing B S hS F hF V) (M.val.obj (op V))) := by
  classical
  intro x hx
  let R : Sieve V :=
    { arrows := fun Y f => chartRestrictLinear M f x ∈
        chartSectionIdeal B S hS F hF I Y ^ n •
          (⊤ : Submodule (chartRing B S hS F hF Y) (M.val.obj (op Y)))
      downward_closed := by
        intro Y Y' f hf k
        rw [chartRestrictLinear_comp M f k x]
        exact map_mem_pow_chartSectionIdeal_smul_top B S hS F hF I M k n hf }
  have hR : R ∈ SmallEtale.topology B S hS F V := by
    obtain ⟨Sv, hSv, hSv'⟩ :=
      exists_sieve_of_mem_idealPowSmul B S hS F hF I n (⊤ : M.Submodule) hx
    refine (SmallEtale.topology B S hS F).transitive hSv R ?_
    intro Y f hf
    obtain ⟨Sw, hSw, hSw'⟩ :=
      exists_sieve_mem_pow_chartIdeal_smul_top B S hS F hF I M n _ (hSv' f hf)
    refine (SmallEtale.topology B S hS F).superset_covering ?_ hSw
    intro Y' g hg
    show chartRestrictLinear M (g ≫ f) x ∈ _
    rw [chartRestrictLinear_comp M f g x]
    exact hSw' g hg
  obtain ⟨ι, hιfin, W, g, hWaff, hWR, hff⟩ :=
    SmallEtale.exists_finite_affine_faithfullyFlat_refinement B S hS F hF V hV hR
  let alg : ∀ i, Algebra (chartRing B S hS F hF V) (chartRing B S hS F hF (W i)) :=
    fun i => chartAlgebra (hF := hF) (g i)
  exact Submodule.mem_of_forall_one_tmul_mem_baseChange
    (A := fun i => chartRing B S hS F hF (W i)) hff _ fun i =>
      one_tmul_mem_baseChange_pow_chartSectionIdeal_smul_top B S hS F hF I n M (g i)
        (hMcart V (W i) hV (hWaff i) (g i)) (hIcart V (W i) hV (hWaff i) (g i)).2 (hWR i)

/-- **The sections of `Iⁿ M` over an affine étale chart.**  For a sheaf of ideals and an
`𝒪_F`-module cartesian on affine charts and an affine étale chart `V`,

`(Iⁿ M)(V) = I(V)ⁿ · M(V)`

as submodules of `M(V)`. -/
theorem chartSubmodule_idealPowSubmodule_eq_pow_chartSectionIdeal_smul_top
    (I : IdealSheaves B S hS F hF) (n : ℕ) (M : Modules.{u, u} B S hS F hF)
    (hMcart : IsCartesianOnAffineCharts M)
    (hIcart : IsCartesianOnAffineCharts I.toSheafOfModules)
    (V : SmallEtale B S hS F)
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    chartSubmodule B S hS F hF (idealPowSubmodule I n M) V
      = chartSectionIdeal B S hS F hF I V ^ n •
        (⊤ : Submodule (chartRing B S hS F hF V) (M.val.obj (op V))) :=
  le_antisymm
    (chartSubmodule_idealPowSubmodule_le_pow_chartSectionIdeal_smul_top B S hS F hF I n M
      hMcart hIcart V hV)
    (pow_chartSectionIdeal_smul_top_le_chartSubmodule B S hS F hF I n V)

/-- **The sections of `Iⁿ 𝒢` over an affine étale chart, from quasi-coherence.**  For a
quasi-coherent sheaf of ideals `I` and a quasi-coherent `𝒪_F`-module `𝒢`, the sections of
`Iⁿ 𝒢` over an affine étale chart `V` are `I(V)ⁿ · 𝒢(V)`.

The two cartesianness hypotheses are discharged by Descent, Proposition 03DX (2) for the small
étale site of an algebraic space,
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`. -/
theorem chartSubmodule_idealPowSubmodule_eq_of_isQuasicoherentOnSite
    (I : IdealSheaves B S hS F hF) (n : ℕ) (M : Modules.{u, u} B S hS F hF)
    (hM : M.IsQuasicoherentOnSite) (hI : I.toSheafOfModules.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS F)
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    chartSubmodule B S hS F hF (idealPowSubmodule I n M) V
      = chartSectionIdeal B S hS F hF I V ^ n •
        (⊤ : Submodule (chartRing B S hS F hF V) (M.val.obj (op V))) :=
  chartSubmodule_idealPowSubmodule_eq_pow_chartSectionIdeal_smul_top B S hS F hF I n M
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF M hM)
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF I.toSheafOfModules hI) V hV

end AlgebraicGeometry.Space

end
