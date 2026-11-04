module

public import StacksFrontier.RingTheory.Depth.ShortExact

/-!
# The acyclicity lemma

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and let
`0 → M_e → M_{e-1} → ⋯ → M_0` be a complex of finite `R`-modules with `depth(M_j) ≥ j` for every
`j`. If `i > 0` is the largest index at which the complex fails to be exact, then its homology
`H_i = Ker(M_i → M_{i-1})/Im(M_{i+1} → M_i)` has depth at least `1`, that is, `𝔪` is not an
associated prime of `H_i`.

Write `Z_j = Ker(M_j → M_{j-1})` for the cycles and `B_j = Im(M_{j+1} → M_j)` for the
boundaries. The complex breaks into the short exact sequences `0 → Z_{j+1} → M_{j+1} → B_j → 0`
and `0 → B_i → Z_i → H_i → 0`, and the depth inequalities of a short exact sequence
(`Module.min_depth_le_depth_of_exact`) give, by descending induction:

* `depth(Z_j) ≥ j + 1` for every `j > i`. Above `e` the module `M_j` vanishes and `Z_j = 0` has
  depth `⊤`; and for `j > i` exactness at `j` turns `Z_j` into `B_j`, whose depth is bounded
  below by `min {depth(M_{j+1}), depth(Z_{j+1}) - 1} ≥ j + 1`.
* `depth(B_i) ≥ 2`, the same inequality one degree lower.
* `depth(Z_i) ≥ 1`, because `Z_i ⊆ M_i` and `depth(M_i) ≥ i ≥ 1`.
* `depth(H_i) ≥ min {depth(Z_i), depth(B_i) - 1} ≥ 1` from `0 → B_i → Z_i → H_i → 0`.

## Main results

* `Module.one_le_depth_homology_of_forall_le_depth_of_isGreatest_not_exactAt`: the acyclicity
  lemma.

## Implementation notes

The complex is a `ChainComplex (ModuleCat R) ℕ` with `M_j = 0` for `j > e`. The degree `e + 1`
term being zero, `ExactAt e` is injectivity of `M_e → M_{e-1}`. In degree `0` the shape
`ComplexShape.down ℕ` has no outgoing arrow, so `ExactAt 0` is surjectivity of `M_1 → M_0`; the
hypothesis `i > 0` excludes this case, and it must be excluded: over a field `k` the complex with
`M_0 = k` and `M_j = 0` for `j > 0` is exact at every `j ≥ 1` and not at `0`, and `H_0 = k` has
depth `0`.

The index `i` is pinned by `IsGreatest {j | ¬ C.ExactAt j} i`. Only its upper-bound half is used
by the proof: what is needed is exactness at every degree above `i`.

The homology in the statement is the ambient `HomologicalComplex.homology`, while the depth
inequalities are stated for linear maps between plain modules. The two are matched by
`CategoryTheory.ShortComplex.moduleCatHomologyIso`, which identifies the homology of a short
complex of modules with `Ker(g) ⧸ Im(f)`, together with `HomologicalComplex.homologyIsoSc'`.

## References

* [StacksProject 00N0](https://stacks.math.columbia.edu/tag/00N0)
* C. Peskine and L. Szpiro, *Dimension projective finie et cohomologie locale*, Lemma 1.8
  [Peskine-Szpiro]

## Tags

acyclicity lemma, depth, complex, homology, exact, finite module
-/

@[expose] public section

universe v' u' v u

namespace Stacks.Depth.AcyclicityLemma

open CategoryTheory Limits IsLocalRing

/-- In `ℕ∞`, which has no additive cancellation, `a + 1 ≤ b` still implies `a ≤ b - 1`. -/
private theorem le_sub_one_of_add_one_le {a b : ℕ∞} (h : a + 1 ≤ b) : a ≤ b - 1 := by
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp [ENat.top_sub_one]
  · lift b to ℕ using hb
    have ha : a ≠ ⊤ := by rintro rfl; simp at h
    lift a to ℕ using ha
    have h' : a + 1 ≤ b := by exact_mod_cast h
    calc (a : ℕ∞) = ((a : ℕ) : ℕ∞) := rfl
      _ ≤ ((b - 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_sub_one_of_lt (by omega)
      _ = (b : ℕ∞) - 1 := by rw [ENat.natCast_sub]; norm_num

section Depth

variable {R : Type*} [CommRing R] (I : Ideal R)
variable [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The depth of `M/p` is at least `min (depth M) (depth p - 1)`. -/
private theorem min_depth_le_depth_quotient (p : Submodule R M) :
    min (Module.depth R I M) (Module.depth R I p - 1) ≤ Module.depth R I (M ⧸ p) :=
  (Module.min_depth_le_depth_of_exact I (LinearMap.exact_subtype_mkQ p) p.injective_subtype
    p.mkQ_surjective).2.1

/-- The depth of `p` is at least `min (depth M) (depth (M/p) + 1)`. -/
private theorem min_depth_le_depth_submodule (p : Submodule R M) :
    min (Module.depth R I M) (Module.depth R I (M ⧸ p) + 1) ≤ Module.depth R I p :=
  (Module.min_depth_le_depth_of_exact I (LinearMap.exact_subtype_mkQ p) p.injective_subtype
    p.mkQ_surjective).2.2

/-- If `depth M ≥ k` and `depth (Ker f) ≥ k + 1`, then `depth (Im f) ≥ k`. -/
private theorem le_depth_range {N : Type*} [AddCommGroup N] [Module R N] {k : ℕ∞}
    (f : M →ₗ[R] N) (hM : k ≤ Module.depth R I M)
    (hK : k + 1 ≤ Module.depth R I (LinearMap.ker f)) :
    k ≤ Module.depth R I (LinearMap.range f) :=
  le_trans (le_min hM (le_sub_one_of_add_one_le hK))
    (Module.min_depth_le_depth_of_exact I (f := (LinearMap.ker f).subtype) (g := f.rangeRestrict)
      (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
      (LinearMap.ker f).injective_subtype f.surjective_rangeRestrict).2.1

/-- A submodule of a module of positive depth has positive depth. -/
private theorem one_le_depth_submodule (p : Submodule R M)
    (h : 1 ≤ Module.depth R I M) : 1 ≤ Module.depth R I p :=
  le_trans (le_min h le_add_self) (min_depth_le_depth_submodule I p)

end Depth

open CategoryTheory in
/-- **Acyclicity lemma.** Let `R` be a Noetherian local ring and let
`0 → M_e → M_{e-1} → ⋯ → M_0` be a complex of finite `R`-modules, presented as a chain complex
`C` of `R`-modules with `C.X j = 0` for `j > e`. Assume `depth(M_i) ≥ i` for `i ≤ e`. If `i` is
the largest index at which `C` fails to be exact and `i > 0`, then
`Ker(M_i → M_{i-1})/Im(M_{i+1} → M_i)` has depth at least `1`. -/
public theorem solution
    {R : Type u'} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (C : ChainComplex (ModuleCat.{v'} R) ℕ) [∀ j, Module.Finite R (C.X j)] (e : ℕ)
    (hC : ∀ j, e < j → IsZero (C.X j))
    (hdepth : ∀ j ≤ e, (j : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) (C.X j))
    {i : ℕ} (hi : IsGreatest {j : ℕ | ¬ C.ExactAt j} i) (hi0 : 0 < i) :
    1 ≤ Module.depth R (IsLocalRing.maximalIdeal R) (C.homology i) := by
  set 𝔪 := IsLocalRing.maximalIdeal R
  have hzero : ∀ j : ℕ, e < j → Subsingleton (C.X j) := by
    intro j hj
    exact ModuleCat.isZero_iff_subsingleton.1 (hC j hj)
  have hX : ∀ j : ℕ, (j : ℕ∞) ≤ Module.depth R 𝔪 (C.X j) := by
    intro j
    rcases le_or_gt j e with h | h
    · exact hdepth j h
    · have := hzero j h
      simp [Module.depth_eq_top_of_subsingleton]
  have hex : ∀ j : ℕ, i < j → C.ExactAt j := by
    intro j hj
    by_contra h
    exact absurd (hi.2 h) (by omega)
  have hcyc : ∀ m : ℕ, i < m + 1 → LinearMap.range (C.d (m + 2) (m + 1)).hom =
      LinearMap.ker (C.d (m + 1) m).hom := by
    intro m hm
    have h := hex (m + 1) hm
    rw [C.exactAt_iff' (m + 2) (m + 1) m (by simp) (by simp)] at h
    exact h.moduleCat_range_eq_ker
  have hZ : ∀ m : ℕ, i < m + 1 →
      ((m : ℕ∞) + 2) ≤ Module.depth R 𝔪 (LinearMap.ker (C.d (m + 1) m).hom) := by
    have base : ∀ m : ℕ, e ≤ m →
        ((m : ℕ∞) + 2) ≤ Module.depth R 𝔪 (LinearMap.ker (C.d (m + 1) m).hom) := by
      intro m hm
      have := hzero (m + 1) (by omega)
      have : Subsingleton (LinearMap.ker (C.d (m + 1) m).hom) := inferInstance
      simp [Module.depth_eq_top_of_subsingleton]
    have key : ∀ k m : ℕ, e ≤ m + k → i < m + 1 →
        ((m : ℕ∞) + 2) ≤ Module.depth R 𝔪 (LinearMap.ker (C.d (m + 1) m).hom) := by
      intro k
      induction k with
      | zero => intro m hm _; exact base m (by omega)
      | succ k ih =>
        intro m hm hmi
        rcases le_or_gt e m with h | h
        · exact base m h
        · have hup := ih (m + 1) (by omega) (by omega)
          rw [← hcyc m hmi]
          exact le_depth_range 𝔪 _ (le_trans (le_of_eq (by push_cast; ring)) (hX (m + 2)))
            (le_trans (le_of_eq (by push_cast; ring)) hup)
    intro m hm
    exact key e m (by omega) hm
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hd : ∀ x : C.X (n + 2),
      (C.d (n + 2) (n + 1)).hom x ∈ LinearMap.ker (C.d (n + 1) n).hom := by
    intro x
    have h := ModuleCat.hom_ext_iff.1 (C.d_comp_d (n + 2) (n + 1) n)
    exact congrFun (congrArg DFunLike.coe h) x
  set f : C.X (n + 2) →ₗ[R] LinearMap.ker (C.d (n + 1) n).hom :=
    (C.d (n + 2) (n + 1)).hom.codRestrict (LinearMap.ker (C.d (n + 1) n).hom) hd with hf
  have hB : 2 ≤ Module.depth R 𝔪 (LinearMap.range f) := by
    have h3 : (3 : ℕ∞) ≤ Module.depth R 𝔪 (LinearMap.ker f) := by
      rw [hf, LinearMap.ker_codRestrict]
      refine le_trans ?_ (hZ (n + 1) (by omega))
      exact_mod_cast (show (3 : ℕ) ≤ n + 1 + 2 by omega)
    exact le_depth_range 𝔪 f
      (le_trans (by exact_mod_cast (show (2 : ℕ) ≤ n + 2 by omega)) (hX (n + 2)))
      (le_trans (by norm_num) h3)
  have hZi : 1 ≤ Module.depth R 𝔪 (LinearMap.ker (C.d (n + 1) n).hom) :=
    one_le_depth_submodule 𝔪 _
      (le_trans (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by omega)) (hX (n + 1)))
  have heq : C.homology (n + 1) ≃ₗ[R]
      (LinearMap.ker (C.d (n + 1) n).hom ⧸ LinearMap.range f) :=
    ((C.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).trans
      (C.sc' (n + 2) (n + 1) n).moduleCatHomologyIso).toLinearEquiv
  rw [Module.depth_eq_depth_of_linearEquiv 𝔪 heq]
  exact le_trans (le_min hZi (le_sub_one_of_add_one_le (le_trans (by norm_num) hB)))
    (min_depth_le_depth_quotient 𝔪 (LinearMap.range f))

end Stacks.Depth.AcyclicityLemma

open CategoryTheory Limits in
/-- **Acyclicity lemma.** Let `R` be a Noetherian local ring and let
`0 → M_e → M_{e-1} → ⋯ → M_0` be a complex of finite `R`-modules, presented as a chain complex
`C` of `R`-modules with `C.X j = 0` for `j > e`. Assume `depth(M_i) ≥ i` for `i ≤ e`. If `i` is
the largest index at which `C` fails to be exact and `i > 0`, then
`Ker(M_i → M_{i-1})/Im(M_{i+1} → M_i)` has depth at least `1`. -/
@[stacks 00N0]
public theorem Module.one_le_depth_homology_of_forall_le_depth_of_isGreatest_not_exactAt
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (C : ChainComplex (ModuleCat.{v} R) ℕ) [∀ j, Module.Finite R (C.X j)] (e : ℕ)
    (hC : ∀ j, e < j → IsZero (C.X j))
    (hdepth : ∀ j ≤ e, (j : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) (C.X j))
    {i : ℕ} (hi : IsGreatest {j : ℕ | ¬ C.ExactAt j} i) (hi0 : 0 < i) :
    1 ≤ Module.depth R (IsLocalRing.maximalIdeal R) (C.homology i) :=
  Stacks.Depth.AcyclicityLemma.solution C e hC hdepth hi hi0

end
