module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Shrinking a module to a finitely generated submodule away from finitely many elements

Let `N` be a module over a commutative ring `R` and let `f : ι → R` be a finite family of
elements such that each localization `N_{f i}` is a *finite* `R_{f i}`-module. Then `N` contains
a finitely generated submodule `N'` whose localization at each `f i` is all of `N_{f i}`; in
elementary terms, every element of `N` is carried into `N'` by a power of each `f i`. This is the
commutative algebra in the affine case of [Stacks Project, Tag 01PF].

## Main results

* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.exists_finset_span_image_eq_top`: if the
  localization of `N` away from `f` is a finite module, then finitely many elements *of `N`*
  have images generating it.
* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.exists_pow_smul_mem_span_of_span_image_eq_top`:
  conversely, if finitely many elements of `N` have images generating the localization away
  from `f`, then a power of `f` carries any element of `N` into their `R`-span.
* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.exists_fg_forall_exists_pow_smul_mem`: the
  finitely generated submodule `N'` with `N'_{f i} = N_{f i}` for every `i` of a finite family.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

universe u v w

namespace Stacks.AlgebraicGeometry.FiniteTypeSubmodule

/-- If the localization of `N` away from `f` is a finite module, then finitely many elements of
`N` have images generating it. -/
theorem exists_finset_span_image_eq_top
    {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N] [Module R N]
    (f : R) (Rl : Type*) [CommRing Rl] [Algebra R Rl] [IsLocalization.Away f Rl]
    (Nl : Type*) [AddCommGroup Nl] [Module R Nl] [Module Rl Nl] [IsScalarTower R Rl Nl]
    (g : N →ₗ[R] Nl) [IsLocalizedModule (Submonoid.powers f) g]
    (hfin : Module.Finite Rl Nl) :
    ∃ T : Finset N, Submodule.span Rl (g '' (T : Set N)) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := hfin.fg_top
  have key : ∀ y : Nl, ∃ x : N, y ∈ Submodule.span Rl ({g x} : Set Nl) := by
    intro y
    obtain ⟨⟨x, t⟩, ht⟩ := IsLocalizedModule.surj (Submonoid.powers f) g y
    refine ⟨x, ?_⟩
    obtain ⟨u, hu⟩ := (IsLocalization.map_units Rl t).exists_left_inv
    refine Submodule.mem_span_singleton.2 ⟨u, ?_⟩
    have ht' : (algebraMap R Rl (t : R)) • y = g x := by
      rw [← ht, Submonoid.smul_def, algebraMap_smul]
    rw [← ht', smul_smul, hu, one_smul]
  choose x hx using key
  refine ⟨s.image x, top_unique ?_⟩
  rw [← hs]
  refine Submodule.span_le.2 fun y hy => ?_
  exact Submodule.span_mono (Set.singleton_subset_iff.2
    (Set.mem_image_of_mem _ (Finset.mem_coe.2 (Finset.mem_image_of_mem x hy)))) (hx y)

/-- If a set of elements of `N` has images generating the localization of `N` away from `f`, then
a power of `f` carries every element of `N` into its `R`-span. -/
theorem exists_pow_smul_mem_span_of_span_image_eq_top
    {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N] [Module R N]
    (f : R) (Rl : Type*) [CommRing Rl] [Algebra R Rl] [IsLocalization.Away f Rl]
    {Nl : Type*} [AddCommGroup Nl] [Module R Nl] [Module Rl Nl] [IsScalarTower R Rl Nl]
    (g : N →ₗ[R] Nl) [IsLocalizedModule (Submonoid.powers f) g]
    {T : Set N} (hT : Submodule.span Rl (g '' T) = ⊤) (x : N) :
    ∃ n : ℕ, f ^ n • x ∈ Submodule.span R T := by
  have hmem : g x ∈ Submodule.span Rl (g '' T) := hT ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (Submonoid.powers f) Rl
    (g '' T) (g x) hmem
  rw [Submonoid.smul_def, ← LinearMap.map_smul, ← Submodule.map_span] at ht
  obtain ⟨z, hz, hzeq⟩ := ht
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers f) g).1 hzeq
  obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).1 t.2
  obtain ⟨b, hb⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
  refine ⟨b + a, ?_⟩
  have h1 : f ^ (b + a) • x = (c : R) • ((t : R) • x) := by
    rw [← ha, ← hb, smul_smul, pow_add]
  have h2 : (c : R) • ((t : R) • x) = (c : R) • z := by
    simpa only [Submonoid.smul_def] using hc.symm
  rw [h1, h2]
  exact Submodule.smul_mem _ _ hz

/-- Let `N` be a module over `R` and let `f : ι → R` be a finite family such that each
localization `N_{f i}` is a finite `R_{f i}`-module. Then `N` has a finitely generated submodule
`N'` such that for every `i` a power of `f i` carries any element of `N` into `N'`, equivalently
`N'_{f i} = N_{f i}` for every `i`. -/
theorem exists_fg_forall_exists_pow_smul_mem
    {R : Type u} [CommRing R] {N : Type u} [AddCommGroup N] [Module R N]
    {ι : Type w} [Finite ι] (f : ι → R)
    (hfin : ∀ i, Module.Finite (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) N)) :
    ∃ N' : Submodule R N, N'.FG ∧ ∀ (i : ι) (x : N), ∃ n : ℕ, f i ^ n • x ∈ N' := by
  classical
  have h : ∀ i, ∃ T : Finset N, Submodule.span (Localization.Away (f i))
      ((LocalizedModule.mkLinearMap (Submonoid.powers (f i)) N) '' (T : Set N)) = ⊤ :=
    fun i => exists_finset_span_image_eq_top (f i) (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) N)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) N) (hfin i)
  choose T hT using h
  refine ⟨Submodule.span R (⋃ i, (T i : Set N)),
    Submodule.fg_span (Set.finite_iUnion fun i => (T i).finite_toSet), fun i x => ?_⟩
  obtain ⟨n, hn⟩ := exists_pow_smul_mem_span_of_span_image_eq_top (f i) (Localization.Away (f i))
    (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) N) (hT i) x
  exact ⟨n, Submodule.span_mono (Set.subset_iUnion _ i) hn⟩

end Stacks.AlgebraicGeometry.FiniteTypeSubmodule

end
