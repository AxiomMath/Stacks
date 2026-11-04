module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSectionsConverse
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationExtensionOnSite
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.FinitePresentation

/-!
# A cartesian module finitely presented over an affine chart is finitely presented there

Let `G` be an `𝒪_F`-module on the small étale site of an algebraic space `F`, cartesian on affine
charts (for instance quasi-coherent), and let `U` be an affine étale chart over which the
sections `G(U)` form a finitely presented `𝒪_F(U)`-module. Then the restriction of `G` to the
slice at `U` has a finite global presentation: generators and relations of `G(U)` generate `G`
and all its relations locally, because over an affine chart `V → U` the sections are the base
change `𝒪_F(V) ⊗ G(U)` and base change is right exact.

## Main results

* `exists_coeff_of_sum_tmul_eq_zero`: right exactness of base change, read on coefficients.
* `AlgebraicGeometry.Space.hasSectionsPresentation_of_finitePresentation`,
  `AlgebraicGeometry.Space.hasFiniteGlobalPresentation_over_of_finitePresentation`.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u

/-- **Right exactness of base change on coefficients.** Let `s` span an `R`-module `M` and let the
vectors `rₖ` span the relations among the `sᵢ`. If `∑ τᵢ ⊗ sᵢ = 0` in `R' ⊗_R M`, then `τ` is an
`R'`-combination of the images of the `rₖ`. -/
theorem exists_coeff_of_sum_tmul_eq_zero {R R' M : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] [AddCommGroup M] [Module R M] {n p : ℕ} (s : Fin n → M)
    (hspan : Submodule.span R (Set.range s) = ⊤) (r : Fin p → Fin n → R)
    (hker : LinearMap.ker (Fintype.linearCombination R s) = Submodule.span R (Set.range r))
    (τ : Fin n → R') (hτ : ∑ i, τ i ⊗ₜ[R] s i = 0) :
    ∃ d : Fin p → R', ∀ i, ∑ k, d k * algebraMap R R' (r k i) = τ i := by
  classical
  set π := Fintype.linearCombination R s with hπ
  have hπs : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  set K := LinearMap.ker π
  have hex : Function.Exact K.subtype π := LinearMap.exact_subtype_ker_map π
  have hex' := lTensor_exact R' hex hπs
  set T : R' ⊗[R] (Fin n → R) := ∑ i, τ i ⊗ₜ[R] Pi.single i 1 with hT
  have hT0 : LinearMap.lTensor R' π T = 0 := by
    rw [hT, map_sum]
    simpa [π, Fintype.linearCombination_apply_single] using hτ
  obtain ⟨z, hz⟩ := (hex' T).1 hT0
  -- the image of `R' ⊗ K` is spanned by the `1 ⊗ rₖ`
  set N : Submodule R' (R' ⊗[R] (Fin n → R)) :=
    Submodule.span R' (Set.range fun k => (1 : R') ⊗ₜ[R] r k)
  have hbN : ∀ (b : R') (v : Fin n → R), v ∈ Submodule.span R (Set.range r) → b ⊗ₜ[R] v ∈ N := by
    intro b v hv
    induction hv using Submodule.span_induction generalizing b with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have : b ⊗ₜ[R] r k = b • ((1 : R') ⊗ₜ[R] r k) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact N.add_mem (hx b) (hy b)
    | smul c x _ hx =>
      rw [← TensorProduct.smul_tmul]
      exact hx _
  have key : ∀ w, LinearMap.lTensor R' K.subtype w ∈ N := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul b x =>
      rw [LinearMap.lTensor_tmul]
      exact hbN b x (hker ▸ x.2)
    | add x y hx hy => rw [map_add]; exact N.add_mem hx hy
  have hTN : T ∈ N := hz ▸ key z
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R').1 hTN
  refine ⟨d, fun i => ?_⟩
  set ev : R' ⊗[R] (Fin n → R) →ₗ[R'] R' :=
    LinearMap.liftBaseChange R' ((Algebra.linearMap R R').comp (LinearMap.proj i))
  have h1 := congrArg ev hd
  rw [hT] at h1
  simp only [map_sum, map_smul, LinearMap.liftBaseChange_tmul, LinearMap.coe_comp,
    LinearMap.coe_proj, Function.comp_apply, Function.eval, Algebra.linearMap_apply, smul_eq_mul,
    one_mul, Pi.single_apply, MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ev] at h1
  rw [← h1]

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **Relations among restrictions of generators are locally combinations of the given
relations.** Over each affine chart `Y → V` the sections of a cartesian module are the base
change of the sections over the affine chart `U`, and base change is right exact. -/
theorem exists_sieve_relation_coeff (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {U V : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    {n p : ℕ} (s : Fin n → G.val.obj (op U))
    (hspan : Submodule.span (chartRing B S hS F hF U) (Set.range s) = ⊤)
    (r : Fin p → Fin n → chartRing B S hS F hF U)
    (hker : LinearMap.ker (Fintype.linearCombination (chartRing B S hS F hF U) s) =
      Submodule.span (chartRing B S hS F hF U) (Set.range r))
    (hV : V ⟶ U) (τ : Fin n → chartRing B S hS F hF V)
    (hτ : ∑ i, τ i • (chartRestrictLinear G hV (s i) : G.val.obj (op V)) = 0) :
    ∃ T : Sieve V, T ∈ SmallEtale.topology B S hS F V ∧ ∀ ⦃W : SmallEtale B S hS F⦄ (g : W ⟶ V),
      T g → ∃ d : Fin p → chartRing B S hS F hF W, ∀ i,
        ∑ k, d k * chartRestrict (hF := hF) (g ≫ hV) (r k i) =
          chartRestrict (hF := hF) g (τ i) := by
  classical
  obtain ⟨I, Y, a, hYaff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F V
  refine ⟨Sieve.ofArrows Y a, hcov, ?_⟩
  intro W g hg
  obtain ⟨j, h, rfl⟩ := (Sieve.mem_ofArrows_iff Y a g).1 hg
  set w := a j ≫ hV
  have hτY : ∑ i, chartRestrict (hF := hF) (a j) (τ i) •
      (chartRestrictLinear G w (s i) : G.val.obj (op (Y j))) = 0 := by
    have := congrArg (chartRestrictLinear G (a j)) hτ
    rw [map_sum, map_zero] at this
    refine (Finset.sum_congr rfl fun i _ => ?_).trans this
    rw [chartRestrictLinear_smul, chartRestrictLinear_comp]
  let := chartAlgebra (hF := hF) w
  have hinj := (hG U (Y j) hU (hYaff j) w).injective
  have hsum : ∑ i, chartRestrict (hF := hF) (a j) (τ i) ⊗ₜ[chartRing B S hS F hF U] s i = 0 := by
    apply hinj
    rw [map_sum, map_zero, ← hτY]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact chartBaseChange_tmul G w _ _
  obtain ⟨d, hd⟩ := exists_coeff_of_sum_tmul_eq_zero s hspan r hker _ hsum
  refine ⟨fun k => chartRestrict (hF := hF) h (d k), fun i => ?_⟩
  have := congrArg (chartRestrict (hF := hF) h) (hd i)
  rw [map_sum] at this
  simp only [map_mul] at this
  change ∑ k, chartRestrict (hF := hF) h (d k) *
      chartRestrict (hF := hF) h (chartRestrict (hF := hF) (a j ≫ hV) (r k i)) =
    chartRestrict (hF := hF) h (chartRestrict (hF := hF) (a j) (τ i)) at this
  rw [Category.assoc, chartRestrict_comp, chartRestrict_comp]
  exact this

/-- **Generators and relations of the sections over an affine chart present a cartesian module
there.** -/
theorem hasSectionsPresentation_of_finitePresentation (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    [Module.FinitePresentation (chartRing B S hS F hF U) (G.val.obj (op U))] :
    Stacks.SheafOfModules.HasSectionsPresentation (SmallEtale.topology B S hS F) G U := by
  classical
  obtain ⟨n, s, hspan⟩ :=
    Module.Finite.exists_fin (R := chartRing B S hS F hF U) (M := G.val.obj (op U))
  have hspan' : Submodule.span (chartRing B S hS F hF U) (Set.range s) = ⊤ := hspan
  have hπs : Function.Surjective (Fintype.linearCombination (chartRing B S hS F hF U) s) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan']
  obtain ⟨p, r, hr⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (Module.FinitePresentation.fg_ker _ hπs)
  have hker : LinearMap.ker (Fintype.linearCombination (chartRing B S hS F hF U) s) =
      Submodule.span (chartRing B S hS F hF U) (Set.range r) := hr.symm
  refine ⟨n, p, s, r, fun k => ?_, generates_of_span_eq_top G hG hU s hspan', ?_⟩
  · have hk : r k ∈ LinearMap.ker (Fintype.linearCombination (chartRing B S hS F hF U) s) :=
      hker ▸ Submodule.subset_span ⟨k, rfl⟩
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hk
    exact hk
  · intro V hV τ hτ
    exact exists_sieve_relation_coeff G hG hU s hspan' r hker hV τ hτ

/-- **A cartesian module whose sections over an affine chart are finitely presented has a finite
global presentation on the slice at that chart.** -/
theorem hasFiniteGlobalPresentation_over_of_finitePresentation (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {U : (smallEtaleRingedSite B S hS F hF).C}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    [Module.FinitePresentation (chartRing B S hS F hF U) (G.val.obj (op U))] :
    (G.over U).HasFiniteGlobalPresentation :=
  Stacks.SheafOfModules.hasFiniteGlobalPresentation_over_of_hasSectionsPresentation
    (hasSectionsPresentation_of_finitePresentation G hG hU)

end AlgebraicGeometry.Space
