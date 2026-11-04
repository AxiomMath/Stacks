module

public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.CohenMacaulay.Module
public import StacksFrontier.RingTheory.CohenMacaulay.Syzygy
public import StacksFrontier.RingTheory.Depth.Nakayama
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u

/-!
# Finite free complexes over a Cohen–Macaulay local ring ending in a maximal Cohen–Macaulay module

Proof of
`Module.IsMaximalCohenMacaulay.exists_composableArrows_exact_free_and_isMaximalCohenMacaulay_left`
(Stacks 00NG): over a Noetherian local Cohen–Macaulay ring `(R, 𝔪)` of dimension `d`, a finite
`R`-module `M` of depth `e` fits in an exact complex `0 → K → F_{d-e-1} → ⋯ → F₀ → M → 0` with
the `Fᵢ` finite free and `K` maximal Cohen–Macaulay.

The complex is built one syzygy at a time, from the right. A finite free `F` surjecting onto the
module `N` currently sitting at the left end of the complex is spliced in, replacing `N` by `F`
and adding the kernel `K` of `F ↠ N` as the new left end; each such step lengthens the complex
by one free term. Stacks 00NE says that at every step either the depth of the new left end is
strictly larger than the depth of the old one, or the new left end is already maximal
Cohen–Macaulay. So after `d - e` steps the depth of the left end is at least
`depth_𝔪(M) + (d - e) = e + (d - e) ≥ d`, and since a nonzero finite module has depth at most
`dim R` (Stacks 00LK) the left end is maximal Cohen–Macaulay.

## Main results

* `Stacks.CohenMacaulay.SyzygyComplex.solution`: over a Noetherian local Cohen–Macaulay ring of
  dimension `d`, a finite module `M` of depth `e` fits in an exact complex
  `0 → K → F_{d-e-1} → ⋯ → F₀ → M → 0` with the `Fᵢ` finite free and `K` maximal Cohen–Macaulay.

## Implementation notes

The complexes are `CategoryTheory.ComposableArrows (ModuleCat R) (n + 1)`, and the conjunction of
conditions that Stacks 00NG asks of them — exact, ending in `M`, mono on the left, epi on the
right, all terms finite and the terms other than the leftmost one free — is
`Stacks.CohenMacaulay.SyzygyComplex.IsSyzygyComplex M`, so that it can be carried through an
induction without being spelled out. Its projections are the conjuncts of Stacks 00NG, whose
conclusion is that projection list.

The mathematics splits in two.
`Stacks.CohenMacaulay.SyzygyComplex.depth_add_le_depth_or_isMaximalCohenMacaulay` is the inductive
step for the depth: it turns the invariant "the depth of the left end exceeds `depth_𝔪(M)` by at
least `k`, or the left end is maximal Cohen–Macaulay" into the same statement with `k + 1` across
one syzygy, which is Stacks 00NE plus the observation that the second alternative absorbs the
first, no depth being able to pass `dim R` (Stacks 00LK). It is proved for plain modules, the
complex playing no part in it. `Stacks.CohenMacaulay.SyzygyComplex.IsSyzygyComplex.precomp` is the
inductive step for the complex: splicing a short exact sequence `0 → K → F → N → 0` into the left
end `N` of a complex again gives a complex, with one more free term and left end `K`. Together with
`Stacks.CohenMacaulay.SyzygyComplex.isSyzygyComplex_mk₂`, the same statement for the two-term
complex the induction starts from, it accounts for all of the index bookkeeping. Their exactness
obligations come from an equality of a range and a kernel through
`Stacks.CohenMacaulay.SyzygyComplex.exact_mk₂_of_range_eq_ker`, which is where
`CategoryTheory.ShortComplex.moduleCatMkOfKerLERange` supplies the vanishing of the composite.

The free cover produced by `Stacks.CohenMacaulay.SyzygyComplex.exists_syzygy` is deliberately *not*
minimal: it is `R^n × R` rather than `R^n`, so that its kernel is nonzero (it contains `0 × R`).
This keeps the left end of the complex nonzero at every step, which is what makes
`Module.depth_le_supportDim` (Stacks 00LK) applicable to it, and hence what pins its depth to `dim
R` at the end. Without it a module with a finite free resolution would produce a zero left end, of
depth `∞`, which is never maximal Cohen–Macaulay.

The induction `Stacks.CohenMacaulay.SyzygyComplex.exists_composableArrows_aux` keeps the right end
`M` fixed and grows the complex on the left, so the length is `n + 2` throughout and the last map
is untouched by the splicing; the length `1` complex `M --𝟙--> M` of the degenerate case `d = e` is
therefore not a base case of the induction but a separate branch of
`Stacks.CohenMacaulay.SyzygyComplex.exists_composableArrows_of_le_add`, whose induction starts at
the length `2` complex `0 → K → F → M → 0`.

The three lemmas `Module.depth_eq_top_of_subsingleton`, `Module.maximalIdeal_smul_top_ne_top` and
`coe_depth_le_ringKrullDim` are the same as in the proof of Stacks 00NE; they are read off the
definition of tag 00LI, Nakayama's lemma and Stacks 00LK respectively. Maximal Cohen–Macaulayness
of a module is `depth_𝔪 = dim R` by definition (tag 00NF), and is used here only through
`Stacks.CohenMacaulay.SyzygyComplex.isMaximalCohenMacaulay_of_le_depth`, that a nonzero finite
module whose depth reaches `dim R` is maximal Cohen–Macaulay, and
`Stacks.CohenMacaulay.SyzygyComplex.depth_le_depth_of_isMaximalCohenMacaulay`, that no nonzero
finite module has depth larger than a maximal Cohen–Macaulay one.

## References

* [StackProject 00NG](https://stacks.math.columbia.edu/tag/00NG)
* [StackProject 00NE](https://stacks.math.columbia.edu/tag/00NE)
* [StackProject 00LK](https://stacks.math.columbia.edu/tag/00LK)
-/

@[expose] public section

namespace Stacks.CohenMacaulay.SyzygyComplex

open CategoryTheory IsLocalRing



/-! ### Depth and maximal Cohen–Macaulayness -/

section Depth

variable {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

variable [IsLocalRing R]

/-- **A nonzero finite module has depth at most the dimension of the ring** (Stacks 00LK):
`depth_𝔪(M) ≤ dim Supp(M) ≤ dim R`. -/
@[ega "IV 5.7.3" "special case"]
private theorem coe_depth_le_ringKrullDim [Module.Finite R M] [Nontrivial M] :
    (Module.depth R (maximalIdeal R) M : WithBot ℕ∞) ≤ ringKrullDim R :=
  (Module.depth_le_supportDim R _ M (Module.maximalIdeal_smul_top_ne_top M)).trans
    (Module.supportDim_le_ringKrullDim R M)

/-- The depth of a nonzero finite module over a local ring of dimension `d` is at most `d`. -/
@[ega "IV 5.7.3" "special case"]
private theorem depth_le_of_ringKrullDim_eq {d : ℕ} (hd : ringKrullDim R = d)
    [Module.Finite R M] [Nontrivial M] : Module.depth R (maximalIdeal R) M ≤ (d : ℕ∞) := by
  exact_mod_cast (coe_depth_le_ringKrullDim M).trans_eq hd

/-- **A nonzero finite module whose depth reaches `dim R` is maximal Cohen–Macaulay.** By the
previous bound its depth is then exactly `dim R`, which is the definition (tag 00NF). -/
private theorem isMaximalCohenMacaulay_of_le_depth {d : ℕ} (hd : ringKrullDim R = d)
    [Module.Finite R M] [Nontrivial M] (h : (d : ℕ∞) ≤ Module.depth R (maximalIdeal R) M) :
    Module.IsMaximalCohenMacaulay R M := by
  have hdepth : Module.depth R (maximalIdeal R) M = (d : ℕ∞) :=
    le_antisymm (depth_le_of_ringKrullDim_eq M hd) h
  change ((Module.depth R (maximalIdeal R) M : ℕ∞) : WithBot ℕ∞) = ringKrullDim R
  rw [hdepth, hd]
  norm_cast

/-- **A maximal Cohen–Macaulay module has maximal depth** among the nonzero finite ones: its
depth is `dim R`, which by Stacks 00LK no depth exceeds. -/
private theorem depth_le_depth_of_isMaximalCohenMacaulay [Module.Finite R M] [Nontrivial M]
    (N : Type*) [AddCommGroup N] [Module R N] (hN : Module.IsMaximalCohenMacaulay R N) :
    Module.depth R (maximalIdeal R) M ≤ Module.depth R (maximalIdeal R) N :=
  WithBot.coe_le_coe.mp ((coe_depth_le_ringKrullDim M).trans_eq hN.symm)

/-- **The inductive step for the depth of the left end of the complex.** Let
`0 → K → F → N → 0` be exact with `F` finite free, `N` nonzero and `K` nonzero finite, over a
Noetherian local Cohen–Macaulay ring. If the depth of `N` exceeds that of `M` by at least `k`,
then the depth of `K` exceeds it by at least `k + 1`, by Stacks 00NE — unless `K` is maximal
Cohen–Macaulay, which is also the outcome when `N` already is: a maximal Cohen–Macaulay module
has maximal depth, so Stacks 00NE cannot then produce a jump. -/
private theorem depth_add_le_depth_or_isMaximalCohenMacaulay [IsNoetherianRing R]
    (hR : Module.IsMaximalCohenMacaulay R R) {k : ℕ∞} {K F N : Type*} [AddCommGroup K]
    [Module R K] [Module.Finite R K] [Nontrivial K] [AddCommGroup F] [Module R F]
    [Module.Free R F] [Module.Finite R F] [AddCommGroup N] [Module R N] [Nontrivial N]
    {f : K →ₗ[R] F} {g : F →ₗ[R] N} (h : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g)
    (hN : Module.depth R (maximalIdeal R) M + k ≤ Module.depth R (maximalIdeal R) N ∨
      Module.IsMaximalCohenMacaulay R N) :
    Module.depth R (maximalIdeal R) M + (k + 1) ≤ Module.depth R (maximalIdeal R) K ∨
      Module.IsMaximalCohenMacaulay R K := by
  rcases Module.IsMaximalCohenMacaulay.depth_lt_depth_or_isMaximalCohenMacaulay_of_exact hR h hf hg
    with hlt | ⟨hK, -⟩
  · refine hN.imp (fun hle => ?_) fun hN => absurd hlt (not_lt.2 ?_)
    · rw [← add_assoc]
      exact (Order.add_one_le_of_lt hlt).trans' (by gcongr)
    · exact depth_le_depth_of_isMaximalCohenMacaulay K N hN
  · exact Or.inr hK

end Depth

/-! ### Complexes of modules -/

section Complex

variable {R : Type u} [CommRing R]

/-- A pair of composable maps of modules whose range and kernel agree composes to zero. -/
private theorem comp_eq_zero_of_range_eq_ker {K F N : ModuleCat.{u} R} (f : K ⟶ F) (g : F ⟶ N)
    (h : LinearMap.range f.hom = LinearMap.ker g.hom) : f ≫ g = 0 :=
  (ShortComplex.moduleCatMkOfKerLERange f g h.le).zero

/-- **A pair of maps with `range f = ker g` is an exact complex of length two.** -/
private theorem exact_mk₂_of_range_eq_ker {K F N : ModuleCat.{u} R} (f : K ⟶ F) (g : F ⟶ N)
    (h : LinearMap.range f.hom = LinearMap.ker g.hom) : (ComposableArrows.mk₂ f g).Exact :=
  ComposableArrows.exact₂_mk _ (comp_eq_zero_of_range_eq_ker f g h)
    ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).2 h)

/-- **A finite module has a finite free cover with nonzero kernel.** For `R` a nonzero Noetherian
ring and `M` a finite `R`-module there is a short exact sequence `0 → K → F → M → 0` with `F`
finite free and `K` finite and *nonzero*: take for `F` the non-minimal cover `R^n × R`. -/
private theorem exists_syzygy [IsNoetherianRing R] [Nontrivial R] (M : ModuleCat.{u} R)
    [Module.Finite R M] :
    ∃ (F K : ModuleCat.{u} R) (f : K ⟶ F) (p : F ⟶ M),
      Module.Free R F ∧ Module.Finite R F ∧ Module.Finite R K ∧ Nontrivial K ∧
      Function.Injective f ∧ Function.Surjective p ∧
      LinearMap.range f.hom = LinearMap.ker p.hom := by
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' R M
  set ψ : ((Fin n → R) × R) →ₗ[R] M := φ ∘ₗ LinearMap.fst R (Fin n → R) R with hψ
  refine ⟨ModuleCat.of R ((Fin n → R) × R), ModuleCat.of R (LinearMap.ker ψ),
    ModuleCat.ofHom (LinearMap.ker ψ).subtype, ModuleCat.ofHom ψ, inferInstance, inferInstance,
    Module.Finite.of_injective (LinearMap.ker ψ).subtype (Submodule.subtype_injective _),
    ⟨⟨⟨(0, 1), by simp [hψ]⟩, 0, by simp⟩⟩, Submodule.subtype_injective _, ?_, by simp [hψ]⟩
  intro x
  obtain ⟨y, hy⟩ := hφ x
  exact ⟨(y, 0), hy⟩

/-- **A syzygy complex over `M`:** an exact complex `0 → K → F_{n-1} → ⋯ → F₀ → M → 0` of finite
`R`-modules whose terms other than the leftmost one `K` are free. It is spelled as in Mathlib's
`CategoryTheory.ShortComplex.ShortExact`, of which it is the case `n = 1`: exactness at the
interior terms is `S.Exact`, while the source's `0 →` and `→ 0` are `Mono (S.map' 0 1)` and
`Epi (S.map' n (n + 1))`. The conjunction of the projections below is the conclusion of
Stacks 00NG. -/
private structure IsSyzygyComplex (M : ModuleCat.{u} R) {n : ℕ}
    (S : ComposableArrows (ModuleCat.{u} R) (n + 1)) : Prop where
  /-- The complex ends in `M`, on the nose. -/
  right : S.right = M
  /-- The complex is exact at its interior terms. -/
  exact : S.Exact
  /-- The complex is exact at its leftmost term, i.e. `0 → K` is exact. -/
  mono : Mono (S.map' 0 1)
  /-- The complex is exact at `M`, i.e. `M → 0` is exact. -/
  epi : Epi (S.map' n (n + 1))
  /-- Every term of the complex is a finite `R`-module. -/
  finite : ∀ i, Module.Finite R (S.obj i)
  /-- Every term of the complex other than the leftmost one is free. -/
  free : ∀ (i : ℕ) (_ : i < n), Module.Free R (S.obj' (i + 1))

variable {M : ModuleCat.{u} R} {n : ℕ}

/-- The leftmost term of a syzygy complex is a finite module. -/
private theorem IsSyzygyComplex.finite_left {S : ComposableArrows (ModuleCat.{u} R) (n + 1)}
    (hS : IsSyzygyComplex M S) : Module.Finite R S.left := hS.finite ⟨0, by omega⟩

/-- **A syzygy of `M` is a syzygy complex of length two over `M`:** the two-term complex attached
to a short exact sequence `0 → K → F → M → 0` with `F` finite free and `K` finite. -/
private theorem isSyzygyComplex_mk₂ [Module.Finite R M] {F K : ModuleCat.{u} R}
    (hFfree : Module.Free R F) (hFfin : Module.Finite R F) (hKfin : Module.Finite R K)
    (f : K ⟶ F) (p : F ⟶ M) (hf : Function.Injective f) (hp : Function.Surjective p)
    (hfp : LinearMap.range f.hom = LinearMap.ker p.hom) :
    IsSyzygyComplex M (ComposableArrows.mk₂ f p) := by
  refine ⟨rfl, exact_mk₂_of_range_eq_ker f p hfp, (ModuleCat.mono_iff_injective f).2 hf,
    (ModuleCat.epi_iff_surjective p).2 hp, ?_, ?_⟩
  · intro i
    fin_cases i <;> assumption
  · intro i hi
    match i, hi with
    | 0, _ => exact hFfree

/-- **Splicing a syzygy into the left end of a syzygy complex.** Given a syzygy complex
`0 → N → F_n → ⋯ → F₀ → M → 0` with `N` at the left end and a short exact sequence
`0 → K → F → N → 0` with `F` finite free and `K` finite, the complex
`0 → K → F → F_n → ⋯ → F₀ → M → 0` obtained by replacing `N` by `F` and adding `K` at the left is
again a syzygy complex over `M`; it has one more free term and left end `K`. -/
private theorem IsSyzygyComplex.precomp {S : ComposableArrows (ModuleCat.{u} R) (n + 2)}
    (hS : IsSyzygyComplex M S) {F K : ModuleCat.{u} R} (hFfree : Module.Free R F)
    (hFfin : Module.Finite R F) (hKfin : Module.Finite R K) (f : K ⟶ F) (p : F ⟶ S.left)
    (hf : Function.Injective f) (hp : Function.Surjective p)
    (hfp : LinearMap.range f.hom = LinearMap.ker p.hom) :
    IsSyzygyComplex M ((S.δ₀.precomp (p ≫ S.map' 0 1)).precomp f) := by
  set g : F ⟶ S.obj' 1 := p ≫ S.map' 0 1 with hg
  have hkerg : LinearMap.ker g.hom = LinearMap.ker p.hom := by
    rw [hg, ModuleCat.hom_comp, LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 hS.mono))]
  have hrangeg : LinearMap.range g.hom = LinearMap.ker (S.map' 1 2).hom := by
    rw [hg, ModuleCat.hom_comp, LinearMap.range_comp, LinearMap.range_eq_top.2 hp,
      Submodule.map_top]
    exact (hS.exact.exact' 0 1 2).moduleCat_range_eq_ker
  refine ⟨hS.right, ?_, (ModuleCat.mono_iff_injective f).2 hf, hS.epi, ?_, ?_⟩
  · refine ComposableArrows.exact_of_δ₀ (exact_mk₂_of_range_eq_ker f g (hfp.trans hkerg.symm)) ?_
    exact ComposableArrows.exact_of_δ₀ (exact_mk₂_of_range_eq_ker g _ hrangeg) hS.exact.δ₀
  · rintro ⟨i, hi⟩
    match i, hi with
    | 0, _ => exact hKfin
    | 1, _ => exact hFfin
    | (j + 2), hj => exact hS.finite ⟨j + 1, by omega⟩
  · intro i hi
    match i, hi with
    | 0, _ => exact hFfree
    | (j + 1), hj => exact hS.free j (by omega)

end Complex

/-! ### The iterated syzygy complex -/

section Iterate

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  (hR : Module.IsMaximalCohenMacaulay R R) (M : ModuleCat.{u} R) [Module.Finite R M]

include hR

/-- **The iterated syzygy complex.** Over a Noetherian local Cohen–Macaulay ring, a nonzero
finite module `M` fits, for every `n`, in a syzygy complex `0 → K → F_n → ⋯ → F₀ → M → 0` with
`K` nonzero, such that either the depth of `K` exceeds `depth_𝔪(M)` by at least `n + 1`, or `K`
is maximal Cohen–Macaulay. -/
private theorem exists_composableArrows_aux [Nontrivial M] (n : ℕ) :
    ∃ S : ComposableArrows (ModuleCat.{u} R) (n + 2),
      IsSyzygyComplex M S ∧ Nontrivial S.left ∧
        (Module.depth R (maximalIdeal R) M + ((n : ℕ∞) + 1) ≤
            Module.depth R (maximalIdeal R) S.left ∨
          Module.IsMaximalCohenMacaulay R S.left) := by
  induction n with
  | zero =>
      obtain ⟨F, K, f, p, hFfree, hFfin, hKfin, hKnt, hf, hp, hker⟩ := exists_syzygy M
      refine ⟨_, isSyzygyComplex_mk₂ hFfree hFfin hKfin f p hf hp hker, hKnt, ?_⟩
      simpa using depth_add_le_depth_or_isMaximalCohenMacaulay (M : Type u) hR (k := 0)
        (LinearMap.exact_iff.2 hker.symm) hf hp (Or.inl (by simp))
  | succ n ih =>
      obtain ⟨S, hS, hnt, hdepth⟩ := ih
      have := hS.finite_left
      obtain ⟨F, K, f, p, hFfree, hFfin, hKfin, hKnt, hf, hp, hker⟩ := exists_syzygy S.left
      refine ⟨_, hS.precomp hFfree hFfin hKfin f p hf hp hker, hKnt, ?_⟩
      push_cast
      exact depth_add_le_depth_or_isMaximalCohenMacaulay (M : Type u) hR (K := (K : Type u))
        (LinearMap.exact_iff.2 hker.symm) hf hp hdepth

/-- **Syzygy complexes with a maximal Cohen–Macaulay left end, with the length as a parameter.**
The form of Stacks 00NG in which the number `k` of free terms is any natural number with
`d ≤ e + k`, the case `k = d - e` being Stacks 00NG itself. -/
private theorem exists_composableArrows_of_le_add {d e k : ℕ} (hd : ringKrullDim R = d)
    (he : Module.depth R (maximalIdeal R) M = e) (hk : d ≤ e + k) :
    ∃ S : ComposableArrows (ModuleCat.{u} R) (k + 1),
      IsSyzygyComplex M S ∧ Module.IsMaximalCohenMacaulay R S.left := by
  -- `M` is nonzero, its depth being the natural number `e` rather than `∞`.
  have : Nontrivial (M : Type u) := by
    rcases subsingleton_or_nontrivial (M : Type u) with h | h
    · exact absurd (he.symm.trans (Module.depth_eq_top_of_subsingleton _)) (ENat.natCast_ne_top e)
    · exact h
  rcases k with _ | m
  · -- `d ≤ e`: the complex is `M --𝟙--> M`, and `M` itself is maximal Cohen–Macaulay.
    have hMcm : Module.IsMaximalCohenMacaulay R (M : Type u) :=
      isMaximalCohenMacaulay_of_le_depth _ hd (by rw [he]; exact_mod_cast show d ≤ e by omega)
    refine ⟨ComposableArrows.mk₁ (𝟙 M),
      ⟨rfl, ComposableArrows.exact₁ _, inferInstanceAs (Mono (𝟙 M)), inferInstanceAs (Epi (𝟙 M)),
        ?_, fun i hi => absurd hi (by omega)⟩, hMcm⟩
    intro i
    fin_cases i <;> assumption
  · -- `d ≤ e + (m + 1)`: after `m + 1` syzygies the depth of the left end has reached `d`.
    obtain ⟨S, hS, hnt, hdepth⟩ := exists_composableArrows_aux hR M m
    have := hS.finite_left
    refine ⟨S, hS, hdepth.elim (fun hle => ?_) id⟩
    exact isMaximalCohenMacaulay_of_le_depth (S.left : Type u) hd
      (le_trans (by exact_mod_cast hk) (he ▸ hle))

end Iterate

/-- **Stacks 00NG.** Over a Cohen–Macaulay Noetherian local ring `R` of dimension `d`, a finite
module `M` of depth `e` is the right end of an exact complex `0 → K → F_{d-e-1} → ⋯ → F₀ → M → 0`
with the `Fᵢ` finite free and `K` maximal Cohen–Macaulay. -/
public theorem solution {R : Type u}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (hR : Module.IsMaximalCohenMacaulay R R)
    (M : ModuleCat.{u} R) [Module.Finite R M] {d e : ℕ} (hd : ringKrullDim R = d)
    (he : Module.depth R (maximalIdeal R) M = e) :
    ∃ S : ComposableArrows (ModuleCat.{u} R) (d - e + 1),
      S.right = M ∧ S.Exact ∧ Mono (S.map' 0 1) ∧ Epi (S.map' (d - e) (d - e + 1)) ∧
        (∀ i, Module.Finite R (S.obj i)) ∧
        (∀ (i : ℕ) (hi : i < d - e), Module.Free R (S.obj' (i + 1))) ∧
        Module.IsMaximalCohenMacaulay R S.left := by
  obtain ⟨S, hS, hleft⟩ := exists_composableArrows_of_le_add (k := d - e) hR M hd he (by omega)
  exact ⟨S, hS.right, hS.exact, hS.mono, hS.epi, hS.finite, hS.free, hleft⟩

end Stacks.CohenMacaulay.SyzygyComplex

end

/-!
# Finite free complexes over a Cohen–Macaulay local ring ending in a maximal Cohen–Macaulay module

Let `(R, 𝔪)` be a Noetherian local Cohen–Macaulay ring of dimension `d` and let `M` be a finite
`R`-module of depth `e`. Then there is an exact complex of `R`-modules
$$
  0 \to K \to F_{d - e - 1} \to \cdots \to F_0 \to M \to 0
$$
with each `Fᵢ` finite free and `K` maximal Cohen–Macaulay, that is `depth_𝔪(K) = dim R`.

Such a complex is produced by iterated syzygies: choose a surjection onto `M` from a finite free
module, then a surjection onto its kernel from a finite free module, and so on. Each step either
raises the depth of the kernel strictly or makes it maximal Cohen–Macaulay (Stacks 00NE), and
`depth_𝔪(M) = e ≤ d` because `M` is a nonzero finite module (Stacks 00LK); so after `d - e` steps
the depth of the kernel has reached `d` and the kernel is maximal Cohen–Macaulay.

## Main results

* `IsMaximalCohenMacaulay.exists_composableArrows_exact_free_and_isMaximalCohenMacaulay_left`
  (in the namespace `Module`) — the existence of the complex above, with its `d - e` finite free
  terms.

## Implementation notes

The complex is a `CategoryTheory.ComposableArrows (ModuleCat R) (d - e + 1)`, that is a diagram
`S.obj 0 ⟶ ⋯ ⟶ S.obj (d - e + 1)` of `d - e + 2` modules, whose leftmost object `S.left` is `K`,
whose `d - e` interior objects are the free terms `F_{d - e - 1}, …, F_0` and whose rightmost
object `S.right` is `M` itself. Its exactness is spelled as in Mathlib's
`CategoryTheory.ShortComplex.ShortExact`, which is the case `d - e = 1` of this shape: exactness
at the interior objects is `S.Exact`, while the source's `0 →` and `→ 0` are the two remaining
conditions `Mono (S.map' 0 1)` and `Epi (S.map' (d - e) (d - e + 1))`.

The rightmost object is `M` on the nose, `S.right = M`, rather than merely isomorphic to it; the
two forms of the existence statement are equivalent, since the last map of a complex ending in
`S.right` may be composed with an isomorphism `S.right ≅ M`, and the equality is what a user of
the complex wants. Every object is asserted to be a finite `R`-module. For the interior objects
this is the source's hypothesis; for `K` it is automatic (`K` is a submodule of a finite module
over a Noetherian ring), and it is recorded because Stacks 00NT, the application in Stacks 00O7,
needs `K` finite in order to conclude that it is free.

The source's `d` and `e` are natural numbers pinned by the hypotheses `ringKrullDim R = d` and
`depth_𝔪(M) = e`; the length of the complex is then the truncated difference `d - e`, which is
the genuine one because `e ≤ d`. Neither hypothesis restricts the generality: a Noetherian local
ring has finite Krull dimension, and a finite module of finite depth is exactly a nonzero one.
The latter is why `M ≠ 0` is not assumed: `depth_𝔪(0) = ⊤`, so `depth_𝔪(M) = e` with `e : ℕ`
already forces `M` to be nonzero, and assuming it as well would be assuming it twice.

Cohen–Macaulayness of `R` is the hypothesis `Module.IsMaximalCohenMacaulay R R`, that is
`depth_𝔪(R) = dim R`, which is Definition 00N8 verbatim, as in the statements of tags 00NA,
00NB and 00NE. All modules are objects of `ModuleCat.{u} R` for `R : Type u`, the universe where
the finite free modules `Fin n → R` live.

The quantifier is existential, as in the source, and the length is pinned rather than bounded
below: a complex of the displayed shape whose length exceeds `d - e` may well have a kernel that
is not maximal Cohen–Macaulay, as `0 → 0 → R →(𝟙) R → 0` shows for `M = R` over any
Cohen–Macaulay local ring, where `d - e = 0` while the complex has length `1` and the zero module
has depth `⊤`. Nothing is claimed about lengths other than the source's `d - e`, which is also
the least possible one in general: for `M = R/(x)` with `x` a nonzerodivisor `e = d - 1`, and no
complex `0 → K → M → 0` works because `M` is not maximal Cohen–Macaulay.

Faithfulness to [StackProject 00NG]:

1. No dead hypothesis. `hR` fails the conclusion when dropped: over the non-Cohen–Macaulay ring
   `R = k[[x, y]]/(x², xy)`, which has `dim R = 1` and `depth_𝔪(R) = 0` because `x` is killed by
   `𝔪`, the module `M = R` has `e = 0` and every exact `0 → K → F₀ → R → 0` splits, so `K` is a
   direct summand of a finite free module, hence zero or free, of depth `⊤` or `0` and never
   `1 = dim R`. `[Module.Finite R M]` fails it too: over `R = k[[x, y]]` the infinite-dimensional
   `k`-vector space `M = k^{(ℕ)}` has `e = 0` and `d - e = 2`, and no finite free `F₀` surjects
   onto it, since the image of a finitely generated module is finitely generated; finiteness is
   what makes `F₀ ↠ M` available with `F₀` finite free.
   `[IsNoetherianRing R]` is the source's and is load-bearing behind 00NE and 00LK; `hd` and `he`
   are used by the conclusion, which is a statement about a complex of length `d - e + 1`.
2. The scalars and base are the source's. Every object of the complex is an object of
   `ModuleCat R` and every map is `R`-linear, the depth of `K` inside
   `Module.IsMaximalCohenMacaulay R K` is taken over `R` along `𝔪 = IsLocalRing.maximalIdeal R`,
   and the dimension is `ringKrullDim R`; no localisation or base change intervenes.
3. The quantities are pinned, not merely compared. `d` is `ringKrullDim R` and `e` is
   `Module.depth R (maximalIdeal R) M` (tag 00LI) along the canonical maximal ideal, so the
   number `d - e` of free terms is pinned; the rightmost object of the complex is `M` itself and
   the maximal Cohen–Macaulay object is its leftmost one, so the two ends are pinned as well. The
   source names no map, and the maps of the complex are the data existentially quantified over.
4. The instantiation is not degenerate. Over `R = k[[x, y]]`, with `d = 2`: for `M = k`, of depth
   `e = 0`, the complex `0 → R → R² → R → k → 0` given by the Koszul resolution has `K = R`
   maximal Cohen–Macaulay and two free terms; for `M = R/(x)`, of depth `e = 1`, the complex
   `0 → R →(x) R → R/(x) → 0` has one free term and `K = R`; and for `M = R`, of depth `e = 2`,
   the complex is `0 → R →(𝟙) R → 0` with no free term at all, recording that `M` itself is
   maximal Cohen–Macaulay.

## References

* [StackProject 00NG](https://stacks.math.columbia.edu/tag/00NG)

## Tags

Cohen-Macaulay ring, maximal Cohen-Macaulay module, depth, syzygy, finite free resolution
-/

open CategoryTheory IsLocalRing



namespace Module.IsMaximalCohenMacaulay

/-- **Finite free complexes with a maximal Cohen–Macaulay kernel.** Let `(R, 𝔪)` be a Noetherian
local Cohen–Macaulay ring, that is `depth_𝔪(R) = dim R`, of dimension `d`, and let `M` be a
finite `R`-module of depth `e`. Then there is an exact complex

  `0 → K → F_{d-e-1} → ⋯ → F₀ → M → 0`

of `R`-modules with the `d - e` modules `Fᵢ` finite free and `K` maximal Cohen–Macaulay. The
complex is a `ComposableArrows (ModuleCat R) (d - e + 1)` with rightmost object `M`, whose
exactness at the interior objects `Fᵢ` is `S.Exact` and whose outer two exactness conditions are
`Mono (S.map' 0 1)` and `Epi (S.map' (d - e) (d - e + 1))`; the module `K` is its leftmost
object `S.left`. -/
@[stacks 00NG "Cohen-Macaulayness of the Noetherian local ring `R` is
`Module.IsMaximalCohenMacaulay R R`, i.e. `depth_𝔪(R) = dim R` (Definition 00N8); the complex is a
`ComposableArrows (ModuleCat R) (d - e + 1)` whose rightmost object is `M`, its interior exactness
being `Exact` and the outer two conditions `Mono` and `Epi` as in `ShortComplex.ShortExact`. See
the module docstring."]
public theorem exists_composableArrows_exact_free_and_isMaximalCohenMacaulay_left {R : Type u}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (hR : Module.IsMaximalCohenMacaulay R R)
    (M : ModuleCat.{u} R) [Module.Finite R M] {d e : ℕ} (hd : ringKrullDim R = d)
    (he : Module.depth R (maximalIdeal R) M = e) :
    ∃ S : ComposableArrows (ModuleCat.{u} R) (d - e + 1),
      S.right = M ∧ S.Exact ∧ Mono (S.map' 0 1) ∧ Epi (S.map' (d - e) (d - e + 1)) ∧
        (∀ i, Module.Finite R (S.obj i)) ∧
        (∀ (i : ℕ) (hi : i < d - e), Module.Free R (S.obj' (i + 1))) ∧
        Module.IsMaximalCohenMacaulay R S.left := by exact
          Stacks.CohenMacaulay.SyzygyComplex.solution hR M hd he

end Module.IsMaximalCohenMacaulay
