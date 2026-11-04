module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceSums
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineGeneratedRelations
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators

/-!
# Sections of a quasi-coherent module of finite type over an affine étale chart

Let `F` be an algebraic space and `G` a quasi-coherent `𝒪_F`-module which is of finite type on
the small étale site.  This file proves that the sections of `G` over an affine étale chart `W`
form a finite module over the chart ring `𝒪_F(W)`.

Finite type gives finitely many generating sections only on *some* covering of `W`, and an
epimorphism of sheaves of modules is only locally surjective on sections, so the conclusion does
not follow formally: it needs faithfully flat descent along a finite affine étale refinement of
that covering, together with the bijectivity of the base change comparison of Stacks 03DX(2).

## Main results

* `AlgebraicGeometry.Space.mem_span_of_forall_restrict_mem_span`: a section over an affine chart
  lies in the span of a finite family of sections as soon as its restriction to each member of a
  jointly faithfully flat finite family of affine charts lies in the span of the restrictions.
* `AlgebraicGeometry.Space.span_eq_top_of_generates` and
  `AlgebraicGeometry.Space.module_finite_sections_of_generates`: finitely many sections over an
  affine chart which generate the module only locally already span the sections over that chart.
* `AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite`: **the sections of a
  quasi-coherent `𝒪_F`-module of finite type over an affine étale chart form a finite module over
  the chart ring.**

## Implementation notes

The descent is `Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange`, applied to the
map from a finite free module given by the candidate generators: its injectivity hypothesis over
each member is the injectivity half of `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` and its
surjectivity hypothesis is the base change of a free module, which matches bases.  No universe
lift and no coproduct of copies of the structure sheaf appears: the only input taken from the
categorical side of Stacks 03DL(5) is the finite family of locally generating sections produced by
`Stacks.SheafOfModules.exists_generates_of_hasFiniteGlobalGenerators_over`.

Generation over the chart is reached in two stages, both of which are the descent above.  First
the members of the refinement inherit locally generating sections, by
`Stacks.SheafOfModules.generates_restrict`, and there the descent turns local generation into
generation.  Then the generators of a member are written through the base change comparison as
combinations of restrictions of sections over the chart, and the descent turns generation on the
members into generation over the chart.

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

/-! ### A jointly faithfully flat finite family of affine charts inside a covering sieve -/

/-- A covering sieve of an affine étale chart contains a finite family of affine étale charts
whose restriction maps on regular functions are jointly faithfully flat: the members of the
finite affine refinement are étale, hence flat, and jointly surjective. -/
public theorem exists_finite_affine_faithfullyFlat_pi_le {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    {T : Sieve U} (hT : T ∈ SmallEtale.topology B S hS F U) :
    ∃ (n : ℕ) (z : Fin n → SmallEtale B S hS F) (φ : ∀ i, z i ⟶ U),
      (∀ i, IsAffine
          ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (z i))) ∧
        (∀ i, T (φ i)) ∧
        (RingHom.pi fun i => chartRestrict (hF := hF) (φ i)).FaithfullyFlat := by
  obtain ⟨n, z, φ, hzaff, hzT, -, hpre⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS F hU hT
  obtain ⟨hcov, het⟩ := Scheme.ofArrows_mem_etalePrecoverage_iff.1 hpre
  refine ⟨n, z, φ, hzaff, hzT, ?_⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) := hU
  have (i : Fin n) : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (z i))) := hzaff i
  have (i : Fin n) : Flat ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map (φ i))) :=
    (Etale.iff_flat_and_formallyUnramified.1 (het i)).1
  exact Scheme.faithfullyFlat_pi_appTop
    (fun i => (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (z i)))
    (fun i => (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (φ i)))
    fun x => hcov x

variable {B S hS F hF}

/-! ### Descent of membership in a span along a finite faithfully flat family of charts -/

/-- **A section over an affine étale chart lies in the span of a finite family of sections as soon
as its restriction to each member of a jointly faithfully flat finite family of affine charts lies
in the span of the restricted family.**

The family of coefficients is a finite free module, whose base change along a chart restriction
matches bases, and the base change of the sections over the chart injects into the sections over a
member because the module is cartesian on affine charts; so
`Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange` applies. -/
theorem mem_span_of_forall_restrict_mem_span (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    {n : ℕ} {z : Fin n → SmallEtale B S hS F} (φ : ∀ i, z i ⟶ U)
    (hz : ∀ i, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (z i)))
    (hff : (RingHom.pi fun i => chartRestrict (hF := hF) (φ i)).FaithfullyFlat)
    {κ : Type*} [Finite κ] (τ : κ → G.val.obj (op U))
    {x : G.val.obj (op U)}
    (hx : ∀ i, chartRestrictLinear G (φ i) x ∈
      Submodule.span (chartRing B S hS F hF (z i))
        (Set.range fun l => chartRestrictLinear G (φ i) (τ l))) :
    x ∈ Submodule.span (chartRing B S hS F hF U) (Set.range τ) := by
  classical
  let fκ : Fintype κ := Fintype.ofFinite κ
  let algI : ∀ i, Algebra (chartRing B S hS F hF U) (chartRing B S hS F hF (z i)) :=
    fun i => chartAlgebra (hF := hF) (φ i)
  let modI : ∀ i, Module (chartRing B S hS F hF U) (G.val.obj (op (z i))) :=
    fun i => chartSectionsModule G (φ i)
  have towI : ∀ i, IsScalarTower (chartRing B S hS F hF U) (chartRing B S hS F hF (z i))
      (G.val.obj (op (z i))) := fun i => chartSections_isScalarTower G (φ i)
  have towP : ∀ i, IsScalarTower (chartRing B S hS F hF U) (chartRing B S hS F hF (z i))
      (κ → chartRing B S hS F hF (z i)) :=
    fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hFF : Module.FaithfullyFlat (chartRing B S hS F hF U)
      (∀ i, chartRing B S hS F hF (z i)) := hff
  let rP : ∀ i, (κ → chartRing B S hS F hF U) →ₗ[chartRing B S hS F hF U]
      (κ → chartRing B S hS F hF (z i)) := fun _ => (Algebra.linearMap _ _).compLeft κ
  let rN : ∀ i, G.val.obj (op U) →ₗ[chartRing B S hS F hF U] G.val.obj (op (z i)) :=
    fun i => chartRestrictLinear G (φ i)
  let bT := Fintype.linearCombination (chartRing B S hS F hF U) τ
  let bW : ∀ i, (κ → chartRing B S hS F hF (z i)) →ₗ[chartRing B S hS F hF (z i)]
      G.val.obj (op (z i)) := fun i => Fintype.linearCombination _ fun l => rN i (τ l)
  have hsq : ∀ (i) (q : κ → chartRing B S hS F hF U), rN i (bT q) = bW i (rP i q) := by
    intro i q
    show rN i (Fintype.linearCombination _ τ q) = Fintype.linearCombination _ _ (rP i q)
    rw [Fintype.linearCombination_apply, map_sum, Fintype.linearCombination_apply]
    exact Finset.sum_congr rfl fun l _ => map_smul (rN i) (q l) (τ l)
  have hP : ∀ i, Function.Surjective ((rP i).liftBaseChange (chartRing B S hS F hF (z i))) := by
    intro i
    refine (Module.BaseChange.bijective_liftBaseChange_of_basis
      (Pi.basisFun (chartRing B S hS F hF U) κ)
      (Pi.basisFun (chartRing B S hS F hF (z i)) κ) (rP i) fun l => funext fun j => ?_).2
    show algebraMap (chartRing B S hS F hF U) (chartRing B S hS F hF (z i))
        (Pi.basisFun (chartRing B S hS F hF U) κ l j) =
      Pi.basisFun (chartRing B S hS F hF (z i)) κ l j
    rw [Pi.basisFun_apply, Pi.basisFun_apply]
    by_cases h : j = l
    · subst h
      rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]
  have hN : ∀ i, Function.Injective ((rN i).liftBaseChange (chartRing B S hS F hF (z i))) :=
    fun i => (hG U (z i) hU (hz i) (φ i)).1
  have hn : ∀ i, rN i x ∈ LinearMap.range (bW i) := by
    intro i
    show rN i x ∈ LinearMap.range (Fintype.linearCombination _ fun l => rN i (τ l))
    rw [Fintype.range_linearCombination]
    exact hx i
  have hmem := Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange
    (chartRing B S hS F hF U) (fun i => chartRing B S hS F hF (z i)) bT bW rP rN hsq hP hN hn
  rwa [show LinearMap.range bT =
    Submodule.span (chartRing B S hS F hF U) (Set.range τ) from
      Fintype.range_linearCombination _ _] at hmem

/-! ### Local generation over an affine chart is generation -/

/-- **Finitely many sections over an affine étale chart which generate the module only locally
already span the sections over that chart.**

The covering sieve on which a given section is a combination of the restrictions is refined to a
finite family of affine charts whose chart restrictions are jointly faithfully flat, and
`AlgebraicGeometry.Space.mem_span_of_forall_restrict_mem_span` descends the membership. -/
theorem span_eq_top_of_generates (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    {k : ℕ} (s : Fin k → G.val.obj (op U))
    (hs : PresheafOfModules.Generates (SmallEtale.topology B S hS F) G.val s) :
    Submodule.span (chartRing B S hS F hF U) (Set.range s) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x => ?_
  obtain ⟨T, hT, hcomb⟩ := hs U (𝟙 U) x
  obtain ⟨n, z, φ, hzaff, hzT, hff⟩ :=
    exists_finite_affine_faithfullyFlat_pi_le B S hS F hF hU hT
  refine mem_span_of_forall_restrict_mem_span G hG hU φ hzaff hff s fun i => ?_
  obtain ⟨a, ha⟩ := hcomb (z i) (φ i) (hzT i)
  rw [Category.comp_id] at ha
  exact Submodule.mem_span_set'.2
    ⟨k, a, fun l => ⟨chartRestrictLinear G (φ i) (s l), ⟨l, rfl⟩⟩, ha⟩

/-- Finitely many sections over an affine étale chart which generate the module only locally make
the sections over that chart a finite module over the chart ring. -/
theorem module_finite_sections_of_generates (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    {k : ℕ} (s : Fin k → G.val.obj (op U))
    (hs : PresheafOfModules.Generates (SmallEtale.topology B S hS F) G.val s) :
    Module.Finite (chartRing B S hS F hF U) (G.val.obj (op U)) := by
  have hsurj : Function.Surjective (Fintype.linearCombination (chartRing B S hS F hF U) s) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact span_eq_top_of_generates G hG hU s hs
  exact Module.Finite.of_surjective _ hsurj

/-- **Finiteness of the sections over an affine étale chart descends along a jointly faithfully
flat finite family of affine charts**, for a module cartesian on affine charts.

The generators over each member are combinations of restrictions of sections over the chart,
because the base change comparison is surjective there, so finitely many sections over the chart
span the sections over every member, and
`AlgebraicGeometry.Space.mem_span_of_forall_restrict_mem_span` descends that to the chart. -/
theorem module_finite_sections_of_forall_module_finite (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {W : SmallEtale B S hS F}
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    {n : ℕ} {z : Fin n → SmallEtale B S hS F} (φ : ∀ i, z i ⟶ W)
    (hzaff : ∀ i, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (z i)))
    (hff : (RingHom.pi fun i => chartRestrict (hF := hF) (φ i)).FaithfullyFlat)
    (hfin : ∀ i, Module.Finite (chartRing B S hS F hF (z i)) (G.val.obj (op (z i)))) :
    Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)) := by
  classical
  have hfinz : ∀ i, ∃ (c : ℕ) (γ : Fin c → G.val.obj (op (z i))),
      Submodule.span (chartRing B S hS F hF (z i)) (Set.range γ) = ⊤ := fun i =>
    have := hfin i
    Module.Finite.exists_fin
  choose c γ hγ using hfinz
  have hdec : ∀ (i : Fin n) (l : Fin (c i)), ∃ (kk : ℕ)
      (t : Fin kk → chartRing B S hS F hF (z i)) (mm : Fin kk → G.val.obj (op W)),
      γ i l = ∑ p, t p • chartRestrictLinear G (φ i) (mm p) := by
    intro i l
    let algi : Algebra (chartRing B S hS F hF W) (chartRing B S hS F hF (z i)) :=
      chartAlgebra (hF := hF) (φ i)
    let modi : Module (chartRing B S hS F hF W) (G.val.obj (op (z i))) :=
      chartSectionsModule G (φ i)
    obtain ⟨ζ, hζ⟩ := (hG W (z i) hW (hzaff i) (φ i)).2 (γ i l)
    obtain ⟨kk, t, mm, hmm⟩ := TensorProduct.exists_sum_tmul_eq ζ
    refine ⟨kk, t, mm, ?_⟩
    rw [← hζ, hmm, map_sum]
    exact Finset.sum_congr rfl fun p _ => chartBaseChange_tmul G (φ i) (t p) (mm p)
  choose kk t mm hmm using hdec
  let τ : (Σ i : Fin n, Σ l : Fin (c i), Fin (kk i l)) → G.val.obj (op W) :=
    fun w => mm w.1 w.2.1 w.2.2
  have hspanz : ∀ i, Submodule.span (chartRing B S hS F hF (z i))
      (Set.range fun w => chartRestrictLinear G (φ i) (τ w)) = ⊤ := by
    intro i
    refine top_unique ?_
    rw [← hγ i]
    refine Submodule.span_le.2 ?_
    rintro y ⟨l, rfl⟩
    rw [hmm i l]
    exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, l, p⟩, rfl⟩)
  have hsurj : Function.Surjective (Fintype.linearCombination (chartRing B S hS F hF W) τ) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    refine Submodule.eq_top_iff'.2 fun x => ?_
    refine mem_span_of_forall_restrict_mem_span G hG hW φ hzaff hff τ fun i => ?_
    rw [hspanz i]
    exact Submodule.mem_top
  exact Module.Finite.of_surjective _ hsurj

/-! ### Finiteness of the sections of a module of finite type over an affine chart -/

/-- **The sections of an `𝒪_F`-module of finite type which is cartesian on affine charts over an
affine étale chart form a finite module over the chart ring.**

Finite type provides a covering of the chart on whose members the module has finitely many
generating sections; a finite affine refinement of that covering inherits them
(`Stacks.SheafOfModules.generates_restrict`), and
`AlgebraicGeometry.Space.module_finite_sections_of_generates` makes the sections over each member
finite.  The generators of a member are combinations of restrictions of sections over the chart,
because the base change comparison is surjective there, so finitely many sections over the chart
span the sections over every member, and
`AlgebraicGeometry.Space.mem_span_of_forall_restrict_mem_span` descends that to the chart. -/
theorem module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite
    (G : Modules.{u, u} B S hS F hF) (hG : IsCartesianOnAffineCharts G)
    (hft : SheafOfModules.IsFiniteTypeOnSite G) (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)) := by
  obtain ⟨I, V, f, hcov, hgg⟩ := hft.locally_finitelyGenerated W
  obtain ⟨n, z, φ, hzaff, hzmem, hff⟩ :=
    exists_finite_affine_faithfullyFlat_pi_le B S hS F hF hW hcov
  refine module_finite_sections_of_forall_module_finite G hG hW φ hzaff hff fun i => ?_
  obtain ⟨j, b, -⟩ := (Sieve.mem_ofArrows_iff V f (φ i)).1 (hzmem i)
  obtain ⟨m, σ, hσ⟩ :=
    Stacks.SheafOfModules.exists_generates_of_hasFiniteGlobalGenerators_over G (V j) (hgg j)
  exact module_finite_sections_of_generates G hG (hzaff i) _
    (Stacks.SheafOfModules.generates_restrict b σ hσ)

/-- **The sections of a module cartesian on affine charts over an affine étale chart are finite as
soon as they are finite over each member of a family of affine charts covering the site.**

The objects mapping to a member of the family form a covering sieve of the chart, a finite affine
refinement of which is jointly faithfully flat; over each of its members the sections are the
base change of the sections over a member of the family, hence finite, and
`AlgebraicGeometry.Space.module_finite_sections_of_forall_module_finite` descends that to the
chart.  This is the form in which the finiteness of a quasi-coherent module is checked on a single
affine étale atlas of a quasi-compact algebraic space. -/
theorem module_finite_sections_of_coversTop (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {ι : Type*} {Y : ι → SmallEtale B S hS F}
    (hY : ∀ i, IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y i)))
    (hcov : (SmallEtale.topology B S hS F).CoversTop Y)
    (hfin : ∀ i, Module.Finite (chartRing B S hS F hF (Y i)) (G.val.obj (op (Y i))))
    (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)) := by
  obtain ⟨n, z, φ, hzaff, hzT, hff⟩ :=
    exists_finite_affine_faithfullyFlat_pi_le B S hS F hF hW (hcov W)
  refine module_finite_sections_of_forall_module_finite G hG hW φ hzaff hff fun l => ?_
  obtain ⟨i, ⟨ρ⟩⟩ := hzT l
  let _ := chartAlgebra (hF := hF) ρ
  let _ := chartSectionsModule G ρ
  have _ := chartSections_isScalarTower G ρ
  have := hfin i
  exact Module.Finite.of_surjective (sectionsBaseChange G ρ)
    (hG (Y i) (z l) (hY i) (hzaff l) ρ).2

/-- **A morphism of modules cartesian on affine charts is surjective on the sections over an
affine étale chart as soon as it is surjective over each member of a family of affine charts
covering the site**, provided the sections of its source over that chart are finite.

Let `τ` be finitely many sections of the source generating it over the chart `W`.  Over each
member `z` of a jointly faithfully flat finite family of affine charts of `W` mapping to a member
`Y i` of the family, every section of the target is a combination of restrictions of sections over
`Y i`, which are images of sections of the source; their restrictions to `z` are images of
combinations of the restrictions of `τ`.  So every section of the target over `z` is a
combination of the restrictions of the images of `τ`, and
`AlgebraicGeometry.Space.mem_span_of_forall_restrict_mem_span` descends that to `W`. -/
theorem surjective_val_app_of_coversTop {G H : Modules.{u, u} B S hS F hF} (q : G ⟶ H)
    (hG : IsCartesianOnAffineCharts G) (hH : IsCartesianOnAffineCharts H)
    {ι : Type*} {Y : ι → SmallEtale B S hS F}
    (hY : ∀ i, IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y i)))
    (hcov : (SmallEtale.topology B S hS F).CoversTop Y)
    (hsurj : ∀ i, Function.Surjective (q.val.app (op (Y i))))
    (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (hfin : Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W))) :
    Function.Surjective (q.val.app (op W)) := by
  classical
  obtain ⟨c, τ, hτ⟩ := Module.Finite.exists_fin (R := chartRing B S hS F hF W)
    (M := G.val.obj (op W))
  have hrange : Submodule.span (chartRing B S hS F hF W)
      (Set.range fun j => q.val.app (op W) (τ j)) ≤ LinearMap.range (q.val.app (op W)).hom := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact ⟨τ l, rfl⟩
  intro x
  obtain ⟨n, z, φ, hzaff, hzT, hff⟩ :=
    exists_finite_affine_faithfullyFlat_pi_le B S hS F hF hW (hcov W)
  refine hrange (mem_span_of_forall_restrict_mem_span H hH hW φ hzaff hff _ fun l => ?_)
  obtain ⟨i, ⟨ρ⟩⟩ := hzT l
  let T := Submodule.span (chartRing B S hS F hF (z l))
    (Set.range fun j => chartRestrictLinear H (φ l) (q.val.app (op W) (τ j)))
  have h1 : ∀ g : G.val.obj (op W), q.val.app (op (z l)) (chartRestrictLinear G (φ l) g) ∈ T := by
    intro g
    have hg : g ∈ Submodule.span (chartRing B S hS F hF W) (Set.range τ) := hτ ▸ Submodule.mem_top
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨j, rfl⟩ := hg
      refine Submodule.subset_span ⟨j, ?_⟩
      exact (PresheafOfModules.naturality_apply q.val (φ l).op (τ j)).symm
    | zero => rw [map_zero, map_zero]; exact T.zero_mem
    | add g g' _ _ hg hg' => rw [map_add, map_add]; exact T.add_mem hg hg'
    | smul a g _ hg =>
      have : chartRestrictLinear G (φ l) (a • g) =
          chartRestrict (hF := hF) (φ l) a • chartRestrictLinear G (φ l) g :=
        (G.val.restrictₛₗ (φ l).op).map_smulₛₗ a g
      rw [this, map_smul]
      exact T.smul_mem _ hg
  have h2 : ∀ y : G.val.obj (op (z l)), q.val.app (op (z l)) y ∈ T := by
    intro y
    have hspan := (chartBaseChange_surjective_iff_span_eq_top G (φ l)).1
      (hG W (z l) hW (hzaff l) (φ l)).2
    have hy : y ∈ Submodule.span (chartRing B S hS F hF (z l))
        (Set.range fun g : G.val.obj (op W) => chartRestrictLinear G (φ l) g) :=
      hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact h1 g
    | zero => rw [map_zero]; exact T.zero_mem
    | add y y' _ _ hy hy' => rw [map_add]; exact T.add_mem hy hy'
    | smul a y _ hy => rw [map_smul]; exact T.smul_mem _ hy
  have hspan := (chartBaseChange_surjective_iff_span_eq_top H ρ).1
    (hH (Y i) (z l) (hY i) (hzaff l) ρ).2
  have hx : chartRestrictLinear H (φ l) x ∈ Submodule.span (chartRing B S hS F hF (z l))
      (Set.range fun h : H.val.obj (op (Y i)) => chartRestrictLinear H ρ h) :=
    hspan ▸ Submodule.mem_top
  refine Submodule.span_le.2 ?_ hx
  rintro _ ⟨h, rfl⟩
  obtain ⟨g, rfl⟩ := hsurj i h
  have e : chartRestrictLinear H ρ (q.val.app (op (Y i)) g) =
      q.val.app (op (z l)) (chartRestrictLinear G ρ g) :=
    (PresheafOfModules.naturality_apply q.val ρ.op g).symm
  show chartRestrictLinear H ρ (q.val.app (op (Y i)) g) ∈ T
  rw [e]
  exact h2 _

/-- **The sections of a quasi-coherent `𝒪_F`-module of finite type over an affine étale chart form
a finite module over the chart ring.**

Quasi-coherence makes the module cartesian on affine charts by Stacks 03DX(2),
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, and
`AlgebraicGeometry.Space`'s
`module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite` concludes. -/
theorem module_finite_sections_of_isFiniteTypeOnSite (G : Modules.{u, u} B S hS F hF)
    (hG : G.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite G) :
    ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)) :=
  fun W hW => module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite G
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G hG) hft W hW

end AlgebraicGeometry.Space

end
