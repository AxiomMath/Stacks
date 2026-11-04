module

public import StacksFrontier.RingTheory.CohenMacaulay.FreeComplex
public import StacksFrontier.RingTheory.GlobalDimension.Cyclic
public import StacksFrontier.RingTheory.LocalRing.ProjectiveDimension
public import StacksFrontier.RingTheory.LocalRing.EmbeddingDimension
public import StacksFrontier.RingTheory.ProjectiveDimension.KrullDimension
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
import StacksCore.Tactic.EgaSgaAttribute

universe v u

@[expose] public section


/-!
# Finite free resolutions and global dimension over a regular local ring

Let `R` be a regular local ring of dimension `d` and let `M` be a finite `R`-module of depth `e`.
This file proves that `M` has a resolution `0 → F_{d-e} → ⋯ → F₀ → M → 0` by finite free
`R`-modules, and that every `R`-module has projective dimension at most `d`, that is, that `R` has
global dimension at most `d`.

The argument is the source's. A regular local ring is Cohen-Macaulay (Tag 00NQ), so Tag 00NG
produces an exact complex `0 → K → F_{d-e-1} → ⋯ → F₀ → M → 0` with the `Fᵢ` finite free and `K`
maximal Cohen-Macaulay; over a regular local ring a finite maximal Cohen-Macaulay module is free
(Tag 00NT), so all `d - e + 1` left-hand terms are projective, and an exact complex
`0 → P_n → ⋯ → P₀ → M → 0` of projectives bounds the projective dimension of `M` by `n`. Tag 0CXF
turns that bound back into a resolution by finite free modules, and Tag 065T upgrades the bound on
finite modules to a bound on all modules, which is the assertion about global dimension.

## Main results

* `Stacks.RegularLocalRing.ShortFreeResolution.solution`: Stacks 00O7.

## Implementation notes

The step "an exact complex of projectives of length `n` bounds the projective dimension by `n`" is
proved here by induction on `n`, peeling the leftmost term. The inductive invariant is stated for a
`ComposableArrows C (n + 1)` whose objects `X₀, …, X_n` are projective and which is exact at
`X₁, …, X_n` and epi at the right, and it bounds `projdim X_{n+1}` by
`projdim (ker (X₀ → X₁)) + n`. Phrasing the left-hand hypothesis as a bound on that kernel rather
than as `Mono (X₀ → X₁)` is what makes the induction go through: passing to `S.δ₀` replaces the
kernel of `X₀ → X₁` by the kernel of `X₁ → X₂`, and the two are related by the short exact sequence
`0 → ker(X₀ → X₁) → X₀ → ker(X₁ → X₂) → 0` coming from exactness at `X₁`, which raises the bound by
exactly one. All the index bookkeeping is definitional: `S.δ₀.obj' i = S.obj' (i + 1)`,
`S.δ₀.map' 0 1 = S.map' 1 2` and `S.δ₀.right = S.right` all hold by `rfl`.

The depth in the statement is `Module.depth` (Tag 00LI), the supremum of the lengths of the
`M`-regular sequences in `𝔪`, whereas Tag 00NT is stated through the predicate `IsMaxCM`, the
*existence* of an `M`-regular sequence in `𝔪` of length `dim R`. The bridge is
`exists_isRegular_length_eq_depth`: for a nonzero finite module over a Noetherian local ring that
supremum is attained, because `𝔪 • M ≠ M` by Nakayama and every `M`-regular sequence has length at
most `dim_R(supp M) < ∞`.

## References

* [StacksProject 00O7](https://stacks.math.columbia.edu/tag/00O7)
* [StacksProject 00NG](https://stacks.math.columbia.edu/tag/00NG)
* [StacksProject 00NT](https://stacks.math.columbia.edu/tag/00NT)
* [StacksProject 065T](https://stacks.math.columbia.edu/tag/065T)
-/

namespace Stacks.RegularLocalRing.ShortFreeResolution

open CategoryTheory Limits IsLocalRing ComposableArrows RingTheory.Sequence
  IsRegularLocalRing Module.IsMaximalCohenMacaulay



/-! ### Bounded exact complexes of projectives -/

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- For an epimorphism `f : X ⟶ Y`, the sequence `0 → ker f → X → Y → 0` is short exact. -/
private lemma shortExact_kernelι_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    (ShortComplex.mk (kernel.ι f) f (kernel.condition f)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f)
  mono_f := inferInstance
  epi_g := inferInstance

/-- If `X --f--> Y --g--> Z` is exact at `Y`, the sequence `0 → ker f → X → ker g → 0` is short
exact, the second map being the factorisation of `f` through `ker g`. -/
private lemma shortExact_kernelι_kernelLift {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).Exact) :
    (ShortComplex.mk (kernel.ι f) (kernel.lift g f w)
      (by rw [← cancel_mono (kernel.ι g)]; simp)).ShortExact where
  exact := by
    refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
      (fun {W'} k hk => kernel.lift f k ?_) ?_ ?_)
    · have hk' : k ≫ kernel.lift g f w ≫ kernel.ι g = 0 := by
        rw [← Category.assoc, hk, zero_comp]
      simpa using hk'
    · intro W' k hk
      simp
    · intro W' k hk m hm
      rw [← cancel_mono (kernel.ι f)]
      simpa using hm
  mono_f := inferInstance
  epi_g := h.epi_kernelLift

/-- A short exact sequence `0 → A → P → B → 0` with `P` projective raises the bound on the
projective dimension by one: if `projdim A < k` then `projdim B < k + 1`. -/
private lemma hasProjectiveDimensionLT_succ_of_shortExact {S : ShortComplex C}
    (hS : S.ShortExact) (k : ℕ) [Projective S.X₂] (h : HasProjectiveDimensionLT S.X₁ k) :
    HasProjectiveDimensionLT S.X₃ (k + 1) :=
  hS.hasProjectiveDimensionLT_X₃ k h inferInstance

/-- Let `S : X₀ → ⋯ → X_{n+1}` be a complex which is exact at `X₁, …, X_n`, whose last map is
epi and whose objects `X₀, …, X_n` are projective. If `ker (X₀ → X₁)` has projective dimension
`< k`, then `X_{n+1}` has projective dimension `< k + n + 1`.

Applied to an exact complex `0 → P_n → ⋯ → P₀ → M → 0` of projectives, where the leftmost map is
mono and so has zero kernel, this says that `M` has projective dimension at most `n`. -/
private lemma hasProjectiveDimensionLT_right_of_exact (n : ℕ) :
    ∀ {S : ComposableArrows C (n + 1)} (k : ℕ), S.Exact → Epi (S.map' n (n + 1)) →
      (∀ (i : ℕ) (_ : i ≤ n), Projective (S.obj' i (by omega))) →
      HasProjectiveDimensionLT (kernel (S.map' 0 1)) k →
      HasProjectiveDimensionLT S.right (k + n + 1) := by
  induction n with
  | zero =>
      intro S k _ hepi hproj hker
      have hp : Projective (S.obj' 0) := hproj 0 le_rfl
      exact hasProjectiveDimensionLT_succ_of_shortExact (shortExact_kernelι_of_epi _) k hker
  | succ n ih =>
      intro S k hS hepi hproj hker
      have hp0 : Projective (S.obj' 0 (by omega)) := hproj 0 (by omega)
      have hz : S.map' 0 1 ≫ S.map' 1 2 = 0 := hS.toIsComplex.zero 0
      have hK : HasProjectiveDimensionLT (kernel (S.map' 1 2)) (k + 1) :=
        hasProjectiveDimensionLT_succ_of_shortExact
          (shortExact_kernelι_kernelLift (S.map' 0 1) (S.map' 1 2) hz (hS.exact 0)) k hker
      have h2 := ih (S := S.δ₀) (k + 1) hS.δ₀ hepi (fun i hi => hproj (i + 1) (by omega)) hK
      have heq : k + 1 + n + 1 = k + (n + 1) + 1 := by omega
      rw [heq] at h2
      exact h2

end Abelian

/-! ### Depth is attained, and maximal Cohen-Macaulay modules are free -/

/-- Over a Noetherian local ring `(R, 𝔪)` the depth of a nonzero finite module `M` is attained:
there is an `M`-regular sequence in `𝔪` whose length is `depth_𝔪(M)`, and that length is a natural
number. Indeed `𝔪 • M ≠ M` by Nakayama, so the depth is the supremum of the lengths of the
`M`-regular sequences in `𝔪`; each such length is at most `dim_R(supp M) < ∞` because a regular
sequence of length `ℓ` drops the support dimension by `ℓ`; and a nonempty set of natural numbers
that is bounded above contains its supremum. -/
@[ega "0 16.4.5" "partial"]
private lemma exists_isRegular_length_eq_depth {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] :
    ∃ (rs : List R) (e : ℕ), (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular M rs ∧
      rs.length = e ∧ Module.depth R (maximalIdeal R) M = (e : ℕ∞) := by
  classical
  have hne : maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := by
    intro h
    have h0 := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (⊤ : Submodule R M)
      Module.Finite.fg_top (by rw [h]) (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
    exact absurd h0 top_ne_bot
  set T : Set ℕ := {n | ∃ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
    IsRegular M rs ∧ rs.length = n} with hT
  have hTne : T.Nonempty := ⟨0, [], by simp, IsRegular.nil R M, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, Module.supportDim R M = (D : WithBot ℕ∞) := by
    have hne_bot : Module.supportDim R M ≠ ⊥ := Module.supportDim_ne_bot_of_nontrivial R M
    have hle : Module.supportDim R M ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M
    have hne_top : Module.supportDim R M ≠ ⊤ := fun h =>
      ringKrullDim_ne_top (top_le_iff.mp (h ▸ hle))
    obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.mp hne_bot
    have hy' : y ≠ ⊤ := fun hc => hne_top (by rw [← hy, hc]; rfl)
    obtain ⟨D, hDy⟩ := WithTop.ne_top_iff_exists.mp hy'
    exact ⟨D, by rw [← hy, ← hDy]; norm_cast⟩
  have hbdd : ∀ n ∈ T, n ≤ D := by
    rintro n ⟨rs, hmem, hreg, rfl⟩
    have heq := Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg
    rw [hD] at heq
    rcases eq_or_ne (Module.supportDim R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))) ⊥ with h | h
    · rw [h] at heq
      simp at heq
    · lift (Module.supportDim R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))) to ℕ∞ using h with b
      have heq' : b + (rs.length : ℕ∞) = (D : ℕ∞) := by exact_mod_cast heq
      have hle : (rs.length : ℕ∞) ≤ (D : ℕ∞) := heq' ▸ le_add_self
      exact_mod_cast hle
  have hTbdd : BddAbove T := ⟨D, hbdd⟩
  obtain ⟨rs, hmem, hreg, hlen⟩ : sSup T ∈ T := Nat.sSup_mem hTne hTbdd
  refine ⟨rs, sSup T, hmem, hreg, hlen, ?_⟩
  rw [Module.depth]
  simp only [hne, ite_false]
  refine le_antisymm (iSup₂_le ?_) ?_
  · rintro rs' ⟨hmem', hreg'⟩
    exact Nat.cast_le.2 (le_csSup hTbdd ⟨rs', hmem', hreg', rfl⟩)
  · exact hlen ▸ le_iSup₂ (f := fun (rs' : List R) (_ : _) => (rs'.length : ℕ∞)) rs ⟨hmem, hreg⟩

/-- Over a regular local ring a finite maximal Cohen-Macaulay module is free: Tag 00NT, phrased
for `Module.IsMaximalCohenMacaulay` (the equality `depth_𝔪(M) = dim R` of Tag 00NF) and including
the zero module. -/
private lemma free_of_isMaximalCohenMacaulay {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : Module.IsMaximalCohenMacaulay R M) : Module.Free R M := by
  by_cases hM : Nontrivial M
  · obtain ⟨rs, e, hmem, hreg, hlen, he⟩ := exists_isRegular_length_eq_depth (R := R) M
    refine regular_mcm_free R M ⟨rs, hmem, hreg, ?_⟩
    rw [Module.IsMaximalCohenMacaulay, he] at h
    rw [hlen]
    exact_mod_cast h
  · have : Subsingleton M := not_nontrivial_iff_subsingleton.1 hM
    exact Module.Free.of_subsingleton R M

/-! ### Stacks 00O7 -/

/-- **Stacks 00O7.** Let `R` be a regular local ring of dimension at most `d`. Every finite
`R`-module `M` whose `𝔪`-depth is at least `e` has a resolution `0 → F_{d-e} → ⋯ → F_0 → M → 0`
by finite free `R`-modules, and every `R`-module has projective dimension at most `d`. -/
@[stacks 00O7 "Stated with `ringKrullDim R ≤ d` and `e ≤ depth_𝔪(M)`; see the module docstring of
the statement file.",
  ega "0 17.3.4" "dim.proj ≤ n - prof",
  sga "2 IV 5.3" "partial",
  sga "6 IX 1.5" "partial"]
public theorem solution {R : Type u} [CommRing R] [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R ≤ (d : WithBot ℕ∞)) :
    (∀ (M : ModuleCat.{u} R) [Module.Finite R M] (e : ℕ),
        (e : ℕ∞) ≤ Module.depth R (maximalIdeal R) M →
        ∃ F : ObjectProperty.LeftResolution
            (fun N : ModuleCat.{u} R => Module.Free R N ∧ Module.Finite R N) M,
          ∀ i, d - e < i → IsZero (F.complex.X i)) ∧
      ∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M d := by
  have hdim : ringKrullDim R = (((maximalIdeal R).spanFinrank : ℕ) : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  have hd₀ : (maximalIdeal R).spanFinrank ≤ d := by
    have h := hdim ▸ hd
    exact_mod_cast h
  -- the bound on finite modules
  have key : ∀ (M : ModuleCat.{u} R) (_ : Module.Finite R M) (e : ℕ),
      (e : ℕ∞) ≤ Module.depth R (maximalIdeal R) M → HasProjectiveDimensionLE M (d - e) := by
    intro M _ e he
    by_cases hM : Nontrivial (M : Type u)
    · obtain ⟨rs, e₀, -, -, -, he₀⟩ := exists_isRegular_length_eq_depth (R := R) (M : Type u)
      obtain ⟨S, hSright, hSexact, hSmono, hSepi, hSfin, hSfree, hSleft⟩ :=
        exists_composableArrows_exact_free_and_isMaximalCohenMacaulay_left
          (isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).2 M hdim he₀
      have hfree : ∀ X : ModuleCat.{u} R, Module.Free R X → Projective X := fun X _ =>
        ModuleCat.projective_of_free (Module.Free.chooseBasis R X)
      have hproj : ∀ (i : ℕ) (_ : i ≤ (maximalIdeal R).spanFinrank - e₀),
          Projective (S.obj' i (by omega)) := by
        intro i hi
        rcases i with _ | j
        · have : Module.Finite R (S.left : Type u) := hSfin _
          exact hfree _ (free_of_isMaximalCohenMacaulay (R := R) (S.left : Type u) hSleft)
        · exact hfree _ (hSfree j (by omega))
      have hker : HasProjectiveDimensionLT (kernel (S.map' 0 1)) 0 := by
        have := hSmono
        exact (isZero_kernel_of_mono _).hasProjectiveDimensionLT_zero
      have hbound := hasProjectiveDimensionLT_right_of_exact
        ((maximalIdeal R).spanFinrank - e₀) (S := S) 0 hSexact hSepi hproj hker
      rw [hSright] at hbound
      have hle : (maximalIdeal R).spanFinrank - e₀ ≤ d - e := by
        have hee : e ≤ e₀ := by
          have h' := he₀ ▸ he
          exact_mod_cast h'
        omega
      exact hasProjectiveDimensionLT_of_ge M (0 + ((maximalIdeal R).spanFinrank - e₀) + 1)
        (d - e + 1) (by omega)
    · have hsub : Subsingleton (M : Type u) := not_nontrivial_iff_subsingleton.1 hM
      have := ((ModuleCat.isZero_iff_subsingleton (M := M)).2 hsub).hasProjectiveDimensionLT_zero
      exact hasProjectiveDimensionLT_of_ge M 0 (d - e + 1) (by omega)
  refine ⟨fun M _ e he => ?_, fun M => ?_⟩
  · exact (ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_free_finite
      M (d - e)).1 (key M ‹_› e he)
  · have h3 : ∀ N : ModuleCat.{u} R, Module.Finite R N → HasProjectiveDimensionLT N (d + 1) := by
      intro N hN
      have := key N hN 0 (by simp)
      simpa using this
    have htfae : (∀ N : ModuleCat.{u} R, Module.Finite R N →
        HasProjectiveDimensionLT N (d + 1)) ↔
        ∀ N : ModuleCat.{u} R, HasProjectiveDimensionLT N (d + 1) :=
      (ringGlobalDimension_lt_tfae R (d + 1)).out 3 2
    exact htfae.1 h3 M

end Stacks.RegularLocalRing.ShortFreeResolution

/-!
# Finite free resolutions and global dimension over a regular local ring

Let `R` be a regular local ring of dimension `d` with maximal ideal `𝔪`, and let `M` be a
finite `R`-module of depth `e`. Then `M` admits a resolution

`0 → F_{d-e} → ⋯ → F_0 → M → 0`

by finite free `R`-modules: one takes a resolution by finite free modules of length `d - e - 1`
whose last syzygy `K` is maximal Cohen-Macaulay (Tag 00NG, which is where the depth enters) and
notes that a maximal Cohen-Macaulay module over a regular local ring is free (Tag 00NT), so the
resolution stops. In particular the projective dimension of a finite `R`-module is at most `d`,
and, `R` being Noetherian, the same then holds for every `R`-module (Tag 065T): a regular local
ring has global dimension at most its dimension.

## Main results

* `IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE`: over a
  regular local ring of dimension at most `d`, a finite module of depth at least `e` has a
  resolution by finite free modules concentrated in degrees `≤ d - e`, and every module has
  projective dimension at most `d`.

## Implementation notes

A resolution by finite free modules is the resolution of Tag 00LQ (3): a
`CategoryTheory.ObjectProperty.LeftResolution P M` for `P` the property of a `ModuleCat R`-object
of being free and finite over `R`, that is, an `ℕ`-indexed chain complex `F` of finite free
modules together with a quasi-isomorphism `F ⟶ M`, which is exactness of
`⋯ → F₁ → F₀ → M → 0`. That the resolution is *finite*, of length `d - e`, is the vanishing
`IsZero (F.complex.X i)` for `i > d - e`; a resolution vanishing above degree `n` is precisely an
exact complex `0 → Fₙ → ⋯ → F₀ → M → 0`, and the source's `F_{d-e}` is allowed to be zero, so
`≤ d - e` is the source's assertion and not a weakening of it. Truncated subtraction on `ℕ` is
harmless: `e ≤ depth M ≤ dim R ≤ d` under the hypotheses, so `d - e` is the honest difference.

Global dimension has no name in Mathlib, so "`R` has global dimension `≤ d`" is spelled out as
`∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M d`, quantifying over all modules and not only
the finite ones. Both assertions of the source are carried by one theorem, because the second is
stated for all modules and so is not an instance of the first.

Generality beyond the source: the dimension and the depth enter through the inequalities
`ringKrullDim R ≤ d` and `e ≤ depth_𝔪(M)` rather than through equalities. Both are the weakest
hypotheses that give the displayed conclusion — the conclusion weakens as `d` grows and as `e`
shrinks — and taking `d = dim R`, `e = depth_𝔪(M)` returns the source's statement verbatim. This
form also covers `M = 0`, whose depth is `⊤`. The depth is `Module.depth R (maximalIdeal R) M`
(Tag 00LI). All modules are taken in the universe of `R`, where the finite free modules `Rⁿ`
live; `projectiveDimension` and `HasProjectiveDimensionLE` are likewise universe-fixed in Mathlib.

Faithfulness. (1) Every hypothesis is used: `hd` bounds the length of the resolution and the
projective dimension, `IsRegularLocalRing R` is what makes the last syzygy free (it fails for a
Noetherian local ring that is not regular, whose residue field has infinite projective
dimension), and `e` and `Module.Finite R M` are used by the first conjunct.
(2) The scalars and the base are the source's: `M` is an `R`-module, the depth is taken along the
maximal ideal of `R` itself, the resolving modules `Fᵢ` are free and finite over `R`, and the
projective dimensions are computed in `ModuleCat R`; no localisation or base change occurs.
(3) The source names no canonical map here, and the map to `M` is nevertheless pinned: a
`LeftResolution` carries its augmentation `F.π : F.complex ⟶ (single₀ _).obj M`, so the complex
resolves `M` along a given morphism rather than being merely exact.
(4) The instantiation is not degenerate: for `R = k[[x, y]]`, `d = 2` and `M = R/(x)`, which has
depth `e = 1`, the conclusion is realized by `0 → R → R → M → 0`, and the second conjunct is the
classical fact that `k[[x, y]]` has global dimension `2`.

## References

* [StacksProject 00O7](https://stacks.math.columbia.edu/tag/00O7)

## Tags

regular local ring, free resolution, finite free, projective dimension, global dimension, depth
-/




open CategoryTheory Limits IsLocalRing in
/-- **Stacks 00O7.** Let `R` be a regular local ring of dimension at most `d`. Every finite
`R`-module `M` whose `𝔪`-depth is at least `e` has a resolution `0 → F_{d-e} → ⋯ → F_0 → M → 0`
by finite free `R`-modules, and every `R`-module has projective dimension at most `d`; that is,
`R` has global dimension at most `d`. -/
@[stacks 00O7 "Stated with `ringKrullDim R ≤ d` and `e ≤ depth_𝔪(M)`; the length `d - e` of the
resolution is the vanishing of its terms in degrees `> d - e`, and `R` having global dimension
`≤ d` is `∀ M, HasProjectiveDimensionLE M d`. See the module docstring.",
  ega "0 17.3.4" "dim.proj ≤ n - prof",
  ega "0 17.3.1" "Sufficiency, partial",
  sga "2 IV 5.3" "partial",
  sga "6 IX 1.5" "partial"]
public theorem IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE
    {R : Type u} [CommRing R] [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R ≤ (d : WithBot ℕ∞)) :
    (∀ (M : ModuleCat.{u} R) [Module.Finite R M] (e : ℕ),
        (e : ℕ∞) ≤ Module.depth R (maximalIdeal R) M →
        ∃ F : ObjectProperty.LeftResolution
            (fun N : ModuleCat.{u} R => Module.Free R N ∧ Module.Finite R N) M,
          ∀ i, d - e < i → IsZero (F.complex.X i)) ∧
      ∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M d :=
    by exact Stacks.RegularLocalRing.ShortFreeResolution.solution hd

end


/-!
# Serre's characterisation of regular local rings

Let `(R, 𝔪, κ)` be a Noetherian local ring. This file proves that `κ` has finite projective
dimension over `R` if and only if `R` has finite global dimension if and only if `R` is regular,
and that in that case the global dimension of `R` is `dim R = dim_κ 𝔪/𝔪²`.

Write `G = ⨆_M pd_R M` for the global dimension, `p = pd_R κ` and `n = dim_κ 𝔪/𝔪²`. Two lemmas
carry the mathematics, and each is one application of two inequalities:

* if `p ≠ ⊤` then `R` is regular, because `n ≤ p` (Stacks 00OA), `p ≤ dim R` (Stacks 00OB at
  `M = κ`) and `dim R ≤ n` (Krull's height theorem), so `n = dim R`;
* if `R` is regular then `G = n`, because `G ≤ n` by Stacks 00O7 applied with `d = n` — legitimate
  since `dim R = n` — and `n ≤ p ≤ G`, `κ` being one module among all.

The five conditions then close up: regularity gives `G = n` and `G = dim R` in one step each, and
both of those are `≠ ⊤`, which returns to finite global dimension.

## Main results

* `Stacks.RegularLocalRing.GlobalDimension.solution`: Stacks 00OC, the five conditions of the
  statement as one `List.TFAE`.

## Implementation notes

The cycle proved is `1 → 3 → 4 → 2 → 1` together with `3 → 5 → 2`; the source's trivial
implication (2) `⇒` (1) is `le_iSup` and `top_le_iff`, and the source's final sentence is items
(4) and (5), which are the same equality `G = n` read before and after the identity `n = dim R`
of regularity.

The bound of Stacks 00O7 is used at the natural number `n = dim_κ 𝔪/𝔪²` rather than at "the"
dimension of `R`: `ringKrullDim R` lives in `WithBot ℕ∞` and 00O7 needs a natural number `d` with
`dim R ≤ d`, and regularity supplies `dim R = n` with `n : ℕ` on the nose, so no finiteness of
the Krull dimension has to be extracted first.

## References

* [StacksProject 00OC](https://stacks.math.columbia.edu/tag/00OC)
* [StacksProject 00O7](https://stacks.math.columbia.edu/tag/00O7)
* [StacksProject 00OA](https://stacks.math.columbia.edu/tag/00OA)
* [StacksProject 00OB](https://stacks.math.columbia.edu/tag/00OB)
-/

namespace Stacks.RegularLocalRing.GlobalDimension



open CategoryTheory IsLocalRing

/-- A natural number is not `⊤` in `WithBot ℕ∞`. Mathlib has `ENat.natCast_ne_top` in `ℕ∞`, but
no counterpart for `WithBot ℕ∞`, where the goal is closed by neither `norm_cast` nor `simp`. -/
public lemma natCast_ne_top (n : ℕ) : (n : WithBot ℕ∞) ≠ ⊤ :=
  (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n)).ne

/-- Krull's height theorem for the maximal ideal, in terms of the embedding dimension:
`dim R ≤ dim_κ 𝔪/𝔪²`. This is `ringKrullDim_le_spanFinrank_maximalIdeal` read through
`IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`. -/
@[ega "0 16.2.6"]
private lemma ringKrullDim_le_finrank_cotangentSpace (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    ringKrullDim R ≤ (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) :=
  (ringKrullDim_le_spanFinrank_maximalIdeal R).trans_eq
    (by rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace])

/-- **Serre's criterion**, the hard implication: a Noetherian local ring whose residue field has
finite projective dimension is regular. Indeed `dim_κ 𝔪/𝔪² ≤ pd_R κ ≤ dim R` by Stacks 00OA and
Stacks 00OB, while `dim R ≤ dim_κ 𝔪/𝔪²` always, so the two agree. -/
@[ega "0 17.3.1" "Necessity", sga "6 IX 1.5" "partial"]
private lemma isRegularLocalRing_of_projectiveDimension_residueField_ne_top (R : Type u)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤) :
    IsRegularLocalRing R :=
  (IsRegularLocalRing.iff_finrank_cotangentSpace R).mpr <| le_antisymm
    (finrank_cotangentSpace_le_projectiveDimension_residueField.trans
      (Module.projectiveDimension_le_ringKrullDim (ResidueField R) h))
    (ringKrullDim_le_finrank_cotangentSpace R)

/-- The global dimension of a regular local ring is its embedding dimension: Stacks 00O7 applied
with `d = dim_κ 𝔪/𝔪²`, which is `dim R` by regularity, bounds every projective dimension above,
and Stacks 00OA bounds the supremum below by the projective dimension of `κ`. -/
private lemma iSup_projectiveDimension_eq_finrank_cotangentSpace (R : Type u) [CommRing R]
    [IsRegularLocalRing R] :
    (⨆ M : ModuleCat.{u} R, projectiveDimension M) =
      (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) :=
  le_antisymm
    (iSup_le fun M => (projectiveDimension_le_iff M _).mpr
      ((IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE
        ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp ‹_›).ge).2 M))
    (finrank_cotangentSpace_le_projectiveDimension_residueField.trans
      (le_iSup (f := fun M : ModuleCat.{u} R => projectiveDimension M) _))

open CategoryTheory IsLocalRing in
/-- **Stacks 00OC.** For a Noetherian local ring `R` the five conditions are equivalent: `κ` has
finite projective dimension, `R` has finite global dimension, `R` is regular, and the global
dimension equals `dim R`, respectively `dim_κ 𝔪/𝔪²`. -/
public theorem solution {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    List.TFAE
      [projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤,
       (⨆ M : ModuleCat.{u} R, projectiveDimension M) ≠ ⊤,
       IsRegularLocalRing R,
       (⨆ M : ModuleCat.{u} R, projectiveDimension M) = ringKrullDim R,
       (⨆ M : ModuleCat.{u} R, projectiveDimension M) =
         (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞)] := by
  tfae_have 2 → 1 := fun h hp => h (top_le_iff.mp
    (hp ▸ le_iSup (f := fun M : ModuleCat.{u} R => projectiveDimension M) _))
  tfae_have 1 → 3 := isRegularLocalRing_of_projectiveDimension_residueField_ne_top R
  tfae_have 3 → 4 := fun _ => (iSup_projectiveDimension_eq_finrank_cotangentSpace R).trans
    ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp ‹_›)
  tfae_have 3 → 5 := fun _ => iSup_projectiveDimension_eq_finrank_cotangentSpace R
  tfae_have 4 → 2 := fun h => h ▸ ringKrullDim_ne_top
  tfae_have 5 → 2 := fun h => h ▸ natCast_ne_top _
  tfae_finish

end Stacks.RegularLocalRing.GlobalDimension

/-!
# Serre's characterisation of regular local rings

Let `(R, 𝔪, κ)` be a Noetherian local ring. Then the following are equivalent:

1. `κ` has finite projective dimension as an `R`-module;
2. `R` has finite global dimension;
3. `R` is a regular local ring;

and, when these hold, the global dimension of `R` equals `dim R = dim_κ 𝔪/𝔪²`.

The source's proof. (3) `⇒` (2) is Proposition 00O7: over a regular local ring of dimension `d`
every finite module has a finite free resolution of length `≤ d`, and by Lemma 065T the bound
`d` then holds for every module. (2) `⇒` (1) is trivial, `κ` being one module among all. For
(1) `⇒` (3), Lemma 00OA gives `dim_κ 𝔪/𝔪² ≤ pd_R κ` and Lemma 00OB gives `pd_R κ ≤ dim R`, so
`dim_κ 𝔪/𝔪² ≤ dim R`; the reverse inequality `dim R ≤ dim_κ 𝔪/𝔪²` is Krull's height theorem
(`ringKrullDim_le_spanFinrank_maximalIdeal`), so `𝔪` is generated by `dim R` elements and `R` is
regular (Definition 00KU). Granting (1)–(3), Proposition 00O7 bounds the global dimension by
`dim R` and Lemma 00OA bounds it below by `dim_κ 𝔪/𝔪²`, which equals `dim R` by regularity; so
both displayed equalities hold.

## Main results

* `isRegularLocalRing_tfae`: the three equivalent conditions of the source, together with the
  two numerical identities of its final sentence, as one `List.TFAE`.

## Implementation notes

The five conditions are the source's (1), (2), (3) in its order, followed by its two "moreover"
equalities. Folding the equalities into the same `TFAE` list is not a weakening: each of them
forces finite global dimension, `ringKrullDim R` and `Module.finrank _ (CotangentSpace R)` being
`≠ ⊤` for a Noetherian local ring, so `(...).out 2 3` is exactly "if `R` is regular then its
global dimension is `dim R`", `(...).out 2 4` is "… is `dim_κ 𝔪/𝔪²`", and `(...).out 3 4`
composed out of them is the source's chain `gl dim R = dim R = dim_κ 𝔪/𝔪²`. It is also sharper
than a conjunction of the equivalence with an implication, since it records that either equality
already implies regularity.

Mathlib names neither the global dimension of a ring nor the projective dimension of a module
over one, so, following Definition 00O6 and the neighbouring tags 00O7, 00O9 and 00OQ, the global
dimension is the supremum `⨆ M : ModuleCat.{u} R, projectiveDimension M` of the projective
dimensions of all `R`-modules, taken in `WithBot ℕ∞`, and `pd_R κ` is
`projectiveDimension (ModuleCat.of R (ResidueField R))` as in Lemma 00OA. "Finite" is `≠ ⊤`
(`CategoryTheory.projectiveDimension_ne_top_iff`); the supremum being `≠ ⊤` is equivalent to the
existence of a single `n : ℕ` with `∀ M, HasProjectiveDimensionLE M n`, the form in which 00O7
and 00O9 state a bound, because an element of `WithBot ℕ∞` other than `⊤` is `⊥` or a natural
number.

Modules are quantified in the universe of `R`, where `κ` and the finite free modules `Rⁿ` live.
Nothing depends on that choice: by Lemma 065T a bound on the projective dimensions of the cyclic
modules `R ⧸ I` bounds every module, and those already live in `Type u`.

`dim_κ 𝔪/𝔪²` is `Module.finrank (ResidueField R) (CotangentSpace R)`, Mathlib's spelling of the
embedding dimension, as in Lemma 00OA; `IsNoetherianRing R` is what makes it the honest dimension
(`IsLocalRing.instFiniteDimensionalResidueFieldCotangentSpaceOfIsNoetherianRing`), and
`IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace` converts it to the minimal number
of generators of `𝔪`. The source's Definition 00KU of a regular local ring is Mathlib's
`IsRegularLocalRing`, whose unfolding `(maximalIdeal R).spanFinrank = ringKrullDim R` is
`isRegularLocalRing_iff`; the name of this lemma mutates that of its Mathlib sibling.

Faithfulness. (1) No hypothesis is dead: `IsLocalRing R` provides `𝔪` and `κ`, and
`IsNoetherianRing R` is what makes the equivalences true rather than one-sided — a non-Noetherian
local ring is never regular in the sense of `IsRegularLocalRing`, which entails Noetherian, while
finite global dimension does not entail Noetherian (a rank-one non-discrete valuation ring has
global dimension `2`), so without it (2) `⇒` (3) fails; it is also what Lemmas 00OA, 00OB and
00O7 use, and what makes `ringKrullDim R ≠ ⊤`. (2) The scalars and base are the source's
throughout: the projective dimensions are those of `R`-modules in `ModuleCat R`, `𝔪/𝔪²` is
measured over `κ = ResidueField R`, and `ringKrullDim R` is the dimension of `R` itself, with no
localisation, completion or quotient substituted. (3) No canonical map is at issue; every side is
a pinned invariant, `κ` being the residue field `R ⧸ 𝔪` with its canonical `R`-module structure
and the global dimension being pinned as a value rather than asserted to be finite for some
unspecified bound. (4) The instantiation is not degenerate: for `R = k[x, y]` localised at
`(x, y)` all five hold with `gl dim R = dim R = dim_κ 𝔪/𝔪² = 2`, witnessed on `κ` by the Koszul
resolution `0 → R → R² → R → κ → 0`; for `R = k[x]/(x²)` all five fail, `pd_R κ = ⊤` while
`dim R = 0`, so no item is vacuously true or false.

## References

* [StacksProject 00OC](https://stacks.math.columbia.edu/tag/00OC)

## Tags

regular local ring, global dimension, projective dimension, residue field, embedding dimension,
cotangent space, Krull dimension, Noetherian local ring
-/




open CategoryTheory IsLocalRing in
/-- **Serre's characterisation of regular local rings** (Stacks 00OC). For a Noetherian local
ring `(R, 𝔪, κ)` the following are equivalent: (1) `κ` has finite projective dimension over `R`;
(2) `R` has finite global dimension; (3) `R` is a regular local ring; (4) the global dimension of
`R` is `dim R`; (5) the global dimension of `R` is `dim_κ 𝔪/𝔪²`. Items (4) and (5) are the
source's final sentence, and together they give `gl dim R = dim R = dim_κ 𝔪/𝔪²`. -/
@[stacks 00OC "Global dimension is the supremum of the projective dimensions of all `R`-modules
(Mathlib has no name for it) and \"finite\" is `≠ ⊤`; `dim_κ 𝔪/𝔪²` is the `finrank` of
`IsLocalRing.CotangentSpace R` over `IsLocalRing.ResidueField R`. The source's two \"moreover\"
equalities are items (4) and (5) of the list, each of which implies the other three. See the
module docstring.", ega "0 17.3.1"]
public theorem isRegularLocalRing_tfae {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    List.TFAE
      [projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤,
       (⨆ M : ModuleCat.{u} R, projectiveDimension M) ≠ ⊤,
       IsRegularLocalRing R,
       (⨆ M : ModuleCat.{u} R, projectiveDimension M) = ringKrullDim R,
       (⨆ M : ModuleCat.{u} R, projectiveDimension M) =
         (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞)] :=
    by apply Stacks.RegularLocalRing.GlobalDimension.solution

