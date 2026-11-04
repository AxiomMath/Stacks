module

import StacksFrontier.RingTheory.Depth.ShortExact
import StacksFrontier.RingTheory.Depth.Dimension
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

public import StacksFrontier.Algebra.Homology.ProjectiveDimension.Defs
public import StacksFrontier.RingTheory.Depth.Criteria
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe v u

/-!
# The Auslander-Buchsbaum formula

Proof of `Module.projectiveDimension_add_depth_eq_depth_self` (Stacks 090V): for `(R, 𝔪)` a
Noetherian local ring and `M` a nonzero finite `R`-module of finite projective dimension,
`pd_R(M) + depth_𝔪(M) = depth_𝔪(R)`.

The two inequalities are proved separately.

`depth_𝔪(R) ≤ pd_R(M) + depth_𝔪(M)` is an induction on `pd_R(M)`: for `M` projective it is the
equality `depth_𝔪(M) = depth_𝔪(R)` for a nonzero finite free module, and otherwise a finite free
cover `0 → K → F → M → 0` has `pd_R(M) = pd_R(K) + 1`, so that the estimate
`min {depth_𝔪(F), depth_𝔪(K) - 1} ≤ depth_𝔪(M)` for an extension (Tag 00LX) inherits the bound
from `K`. Two steps of that argument are not in the source's list of prerequisites and are proved
here: the invariance of `Module.depth` under a linear equivalence, and the equality
`depth_𝔪(F) = depth_𝔪(R)` for a nonzero finite free `F`, which follows from Tag 00LX applied to
the split sequences `0 → R → R^{n+1} → R^n → 0` together with the finiteness of `depth_𝔪(R)`.

`pd_R(M) + depth_𝔪(M) ≤ depth_𝔪(R)` is an induction on `pd_R(M)` along the same minimal free
covers `0 → K → F → M → 0`, `K ⊆ 𝔪 F`, read through the residue field `κ = R/𝔪`: over a
Noetherian local ring `depth_𝔪(M)` is the least `i` with `Ext^i(κ, M) ≠ 0`, which is Rees'
theorem in the form `n ≤ depth_𝔪(M) ↔ ∀ i < n, Ext^i(κ, M) = 0` (Tag 090R). Put
`t = depth_𝔪(K)`, `d = depth_𝔪(R)`. The inclusion `K → F` induces the zero map on
`Ext^t(κ, -)`: if `t < d` then `Ext^t(κ, F) = 0` already, since `depth_𝔪(F) = d`; and otherwise
the inductive bound forces `pd_R(K) = 0`, so `K` is free and `K ⊆ 𝔪 F` says every matrix
coefficient of the inclusion lies in `𝔪`, which annihilates `κ` and hence all of
`Ext^t(κ, -)`. As `Ext^t(κ, K) ≠ 0`, the long exact sequence of `0 → K → F → M → 0` then makes
`Ext^{t-1}(κ, M) ≠ 0`, so `depth_𝔪(M) ≤ t - 1` and
`pd_R(M) + depth_𝔪(M) ≤ (pd_R(K) + 1) + (t - 1) = pd_R(K) + depth_𝔪(K) ≤ d`.

## Main results

* `Stacks.ProjectiveDimension.DepthFormula.solution`: the Auslander-Buchsbaum formula.

## Implementation notes

Both halves are inductions on `pd_R(M)` over `R` itself, where the source inducts on
`depth_𝔪(M)` and reduces to `depth_𝔪(M) = 0` by dividing by an element `x ∈ 𝔪` that is a
nonzerodivisor on `R` and on `M`. Nothing is lost and two comparisons are avoided: no change of
rings, hence no identification of `depth_R(M/xM)` with `depth_{R/xR}(M/xM)` and no transport of
minimality of a resolution along `- ⊗_R R/xR`. A minimal free cover, rather than a whole minimal
resolution (Tag 00MT), is what each step consumes, and it is produced here from a generating
family of `M` of least cardinality.

In the case `depth_𝔪(M) = 0` the source bounds `depth_𝔪(R)` below by `pd_R(M)` using the
determinantal criterion for the exactness of a complex of finite free modules (Tag 00N1), applied
to a minimal resolution. Here that bound comes instead from the Ext characterisation of depth: the
minimality `K ⊆ 𝔪 F` of the cover is used through the fact that a map of finite free modules
whose coefficients lie in `𝔪` induces the zero map on `Ext^i(κ, -)`, which makes the connecting
map of the long exact sequence carry the nonvanishing of `Ext^{depth_𝔪(K)}(κ, K)` down to `M`.
This is the same use of minimality — the differentials of a minimal resolution are zero modulo
`𝔪` — read off one short exact sequence at a time rather than off the maximal minors of the
last differential.

Four steps are not in the source's list of prerequisites and are proved here: the invariance of
`Module.depth` under a linear equivalence; the equality `depth_𝔪(F) = depth_𝔪(R)` for a nonzero
finite free `F`; the finiteness of `depth_𝔪(M)` for `M` nonzero and finite; and the existence of
a minimal free cover of a finite module over a local ring.

## References

* [StacksProject 090V](https://stacks.math.columbia.edu/tag/090V)

## Tags

Auslander-Buchsbaum, depth, projective dimension, minimal free resolution, Noetherian local ring
-/

namespace Stacks.ProjectiveDimension.DepthFormula

open CategoryTheory IsLocalRing

/-- The kernel of a surjection `p` is the first term of a short exact sequence ending in `p`. -/
private theorem shortExact_ker_subtype {R : Type u} [CommRing R] {P M : Type v}
    [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
    {p : P →ₗ[R] M} (hp : Function.Surjective p) :
    (ShortComplex.moduleCatMk (LinearMap.ker p).subtype p (by ext x; exact x.2)).ShortExact :=
  { exact := by
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      exact (LinearMap.exact_iff.mp p.exact_subtype_ker_map).symm
    mono_f := (ModuleCat.mono_iff_injective _).2 (LinearMap.ker p).injective_subtype
    epi_g := (ModuleCat.epi_iff_surjective _).2 hp }

/-- A finite module of projective dimension at most `0` over a local ring is free. -/
private theorem free_of_hasProjectiveDimensionLE_zero {R : Type u} [CommRing R] [IsLocalRing R]
    [Small.{v} R] (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (h : HasProjectiveDimensionLE (ModuleCat.of R N) 0) : Module.Free R N := by
  have : Projective (ModuleCat.of R N) := (projective_iff_hasProjectiveDimensionLE_zero _).mpr h
  have : Module.Projective R N := (IsProjective.iff_projective (ModuleCat.of R N)).mpr ‹_›
  exact Module.free_of_flat_of_isLocalRing

/-- A nonzero module of finite projective dimension has projective dimension a natural number. -/
private theorem exists_nat_eq_projectiveDimension {R : Type u} [CommRing R] (N : Type v)
    [AddCommGroup N] [Module R N] [Nontrivial N] (hT : Module.projectiveDimension R N ≠ ⊤) :
    ∃ e : ℕ, Module.projectiveDimension R N = (e : WithBot ℕ∞) := by
  have hbot : Module.projectiveDimension R N ≠ ⊥ := by
    rw [ne_eq, CategoryTheory.projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
    exact not_subsingleton N
  generalize Module.projectiveDimension R N = x at hT hbot
  induction x with
  | bot => exact absurd rfl hbot
  | coe y =>
    induction y with
    | top => exact absurd rfl hT
    | coe n => exact ⟨n, rfl⟩

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] in
/-- Nakayama: the maximal ideal of a local ring does not saturate a nonzero finite module. -/
private theorem smul_top_ne_top (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] : maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := by
  intro h
  have : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (Module.Finite.fg_top) h.ge
      (by simpa using (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge)
  exact top_ne_bot this

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- A multiple of an element of `M` by an element of `I` lies in `I • M`. This is
`Submodule.smul_mem_smul` with the module `M` abstract, so that the `IsScalarTower R R M` it needs
is discharged once, for a general `M`, rather than at each concrete module. -/
private theorem smul_mem_smul_top (I : Ideal R) {M : Type*} [AddCommGroup M] [Module R M] {r : R}
    (hr : r ∈ I) (x : M) : r • x ∈ I • (⊤ : Submodule R M) :=
  Submodule.smul_mem_smul hr Submodule.mem_top

/-- The depth of a nonzero finite module over a Noetherian local ring is finite. -/
private theorem depth_ne_top (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] : Module.depth R (maximalIdeal R) M ≠ ⊤ := by
  intro h
  have hle : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((maximalIdeal R).spanFinrank : WithBot ℕ∞) := by
    calc ((⊤ : ℕ∞) : WithBot ℕ∞) = (Module.depth R (maximalIdeal R) M : WithBot ℕ∞) := by rw [h]
      _ ≤ Module.supportDim R M := Module.depth_le_supportDim R _ M (smul_top_ne_top M)
      _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M
      _ ≤ ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
        ringKrullDim_le_spanFinrank_maximalIdeal R
  rw [WithBot.coe_top, top_le_iff] at hle
  exact absurd hle (not_eq_of_beq_eq_false rfl)

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Depth is invariant under linear equivalence. -/
private theorem depth_congr (I : Ideal R) {M M₂ : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M₂] [Module R M₂] (e : M ≃ₗ[R] M₂) :
    Module.depth R I M = Module.depth R I M₂ := by
  have h₁ : I • (⊤ : Submodule R M) = ⊤ → I • (⊤ : Submodule R M₂) = ⊤ := by
    intro h
    have h' : Submodule.map (e : M →ₗ[R] M₂) (I • (⊤ : Submodule R M))
        = I • (⊤ : Submodule R M₂) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
    rw [h, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective] at h'
    exact h'.symm
  have h₂ : I • (⊤ : Submodule R M₂) = ⊤ → I • (⊤ : Submodule R M) = ⊤ := by
    intro h
    have h' : Submodule.map (e.symm : M₂ →ₗ[R] M) (I • (⊤ : Submodule R M₂))
        = I • (⊤ : Submodule R M) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.symm.surjective]
    rw [h, Submodule.map_top, LinearMap.range_eq_top.mpr e.symm.surjective] at h'
    exact h'.symm
  have hset : {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs}
      = {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M₂ rs} := by
    ext rs
    simp only [Set.mem_ofPred_eq, e.isRegular_congr rs]
  unfold Module.depth
  by_cases hc : I • (⊤ : Submodule R M) = ⊤
  · rw [ite_eq_left hc, ite_eq_left (h₁ hc)]
  · rw [ite_eq_right hc, ite_eq_right fun h => hc (h₂ h), hset]

/-- The depth of a nonzero finite free module of finite rank equals the depth of the ring. -/
private theorem depth_pi : ∀ n : ℕ, n ≠ 0 →
    Module.depth R (maximalIdeal R) (Fin n → R) = Module.depth R (maximalIdeal R) R := by
  intro n
  induction n with
  | zero => exact fun h => (h rfl).elim
  | succ m ih =>
    intro _
    obtain rfl | hm := Nat.eq_zero_or_pos m
    · exact depth_congr _ (LinearEquiv.funUnique (Fin 1) R R)
    · have ihm : Module.depth R (maximalIdeal R) (Fin m → R)
          = Module.depth R (maximalIdeal R) R := ih (by omega)
      have e : (Fin (m + 1) → R) ≃ₗ[R] R × (Fin m → R) :=
        { toFun := fun f => (f 0, fun i => f i.succ)
          invFun := fun p => Fin.cons p.1 p.2
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := Fin.cons_self_tail
          right_inv := fun p => by ext <;> simp }
      rw [depth_congr _ e]
      have hex := Module.min_depth_le_depth_of_exact (R := R) (maximalIdeal R)
        (N' := R) (N := R × (Fin m → R)) (N'' := (Fin m → R))
        Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective
      refine le_antisymm ?_ ?_
      · rcases min_le_iff.mp hex.2.2 with h' | h'
        · exact h'
        · rw [ihm] at h'
          exact absurd ((ENat.add_one_le_iff (depth_ne_top R)).mp h') (lt_irrefl _)
      · simpa only [ihm, min_self] using hex.1

/-- The depth of a nonzero finite free module equals the depth of the ring. -/
private theorem depth_eq_depth_self_of_free (F : Type*) [AddCommGroup F] [Module R F]
    [Module.Free R F] [Module.Finite R F] [Nontrivial F] :
    Module.depth R (maximalIdeal R) F = Module.depth R (maximalIdeal R) R := by
  classical
  obtain ⟨n, ⟨b⟩⟩ : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R F) :=
    ⟨_, ⟨(Module.Free.chooseBasis R F).reindex (Fintype.equivFin _)⟩⟩
  have hn : n ≠ 0 := by
    rintro rfl
    exact not_subsingleton F b.equivFun.toEquiv.subsingleton
  rw [depth_congr _ b.equivFun, depth_pi n hn]

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- **Dimension shift along a presentation.** If `p : P → M` is a surjection of `R`-modules with
`P` projective and `M` has projective dimension at most `n + 1`, then its syzygy `ker p` has
projective dimension at most `n`. -/
private theorem hasProjectiveDimensionLE_ker {P M : Type v}
    [AddCommGroup P] [Module R P] [Module.Projective R P] [AddCommGroup M] [Module R M]
    {p : P →ₗ[R] M} (hp : Function.Surjective p) (n : ℕ)
    (h : HasProjectiveDimensionLE (ModuleCat.of R M) (n + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker p)) n := by
  exact (shortExact_ker_subtype hp).hasProjectiveDimensionLT_X₃_iff n
    (ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of R P)) |>.mp h

/-- The easy half, in the form the induction on the length of a finite free resolution gives it:
if `N` is nonzero, finite and of projective dimension at most `n`, then
`depth_𝔪(R) ≤ n + depth_𝔪(N)`. -/
private theorem depth_self_le_add_depth [Small.{v} R] (n : ℕ) :
    ∀ (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N],
      HasProjectiveDimensionLE (ModuleCat.of R N) n →
        Module.depth R (maximalIdeal R) R ≤ (n : ℕ∞) + Module.depth R (maximalIdeal R) N := by
  induction n with
  | zero =>
    intro N _ _ _ _ h
    have := free_of_hasProjectiveDimensionLE_zero N h
    rw [depth_eq_depth_self_of_free N]
    simp
  | succ m ih =>
    intro N _ _ _ _ h
    obtain ⟨k, p₀, hp₀⟩ := Module.Finite.exists_fin' R N
    have eF : Shrink.{v} (Fin k → R) ≃ₗ[R] (Fin k → R) := Shrink.linearEquiv R (Fin k → R)
    have : Module.Finite R (Shrink.{v} (Fin k → R)) := Module.Finite.equiv eF.symm
    have : Module.Free R (Shrink.{v} (Fin k → R)) := Module.Free.of_equiv eF.symm
    set p : Shrink.{v} (Fin k → R) →ₗ[R] N := p₀ ∘ₗ (eF : Shrink.{v} (Fin k → R) →ₗ[R] (Fin k → R))
    have hp : Function.Surjective p := hp₀.comp eF.surjective
    have : Nontrivial (Shrink.{v} (Fin k → R)) := hp.nontrivial
    have hdF : Module.depth R (maximalIdeal R) (Shrink.{v} (Fin k → R))
        = Module.depth R (maximalIdeal R) R := depth_eq_depth_self_of_free _
    have hex := Module.min_depth_le_depth_of_exact (R := R) (maximalIdeal R)
      (N' := LinearMap.ker p) (N := Shrink.{v} (Fin k → R)) (N'' := N)
      p.exact_subtype_ker_map (LinearMap.ker p).injective_subtype hp
    rcases min_le_iff.mp hex.2.1 with h1 | h1
    · rw [hdF] at h1
      exact h1.trans le_add_self
    · rcases subsingleton_or_nontrivial (LinearMap.ker p) with hs | hs
      · have e : Shrink.{v} (Fin k → R) ≃ₗ[R] N :=
          LinearEquiv.ofBijective p ⟨LinearMap.ker_eq_bot.mp Submodule.eq_bot_of_subsingleton, hp⟩
        rw [← depth_congr (maximalIdeal R) e, hdF]
        exact le_add_self
      · have : Module.Finite R (LinearMap.ker p) :=
          Module.Finite.of_injective (LinearMap.ker p).subtype (LinearMap.ker p).injective_subtype
        have hK : Module.depth R (maximalIdeal R) (LinearMap.ker p)
            ≤ Module.depth R (maximalIdeal R) N + 1 := tsub_le_iff_right.mp h1
        calc Module.depth R (maximalIdeal R) R
            ≤ (m : ℕ∞) + Module.depth R (maximalIdeal R) (LinearMap.ker p) :=
              ih _ (hasProjectiveDimensionLE_ker hp m h)
          _ ≤ (m : ℕ∞) + (Module.depth R (maximalIdeal R) N + 1) := by gcongr
          _ = ((m + 1 : ℕ) : ℕ∞) + Module.depth R (maximalIdeal R) N := by
            push_cast
            ring

/-- **The easy half of the Auslander-Buchsbaum formula**: `depth_𝔪(R) ≤ pd_R(N) + depth_𝔪(N)`
for every nonzero finite module `N` over a Noetherian local ring. -/
private theorem depth_self_le_projectiveDimension_add_depth [Small.{v} R] (N : Type v)
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N] :
    (Module.depth R (maximalIdeal R) R : WithBot ℕ∞) ≤
      Module.projectiveDimension R N + (Module.depth R (maximalIdeal R) N : WithBot ℕ∞) := by
  rcases eq_or_ne (Module.projectiveDimension R N) ⊤ with hT | hT
  · rw [hT, ← WithBot.coe_top, ← WithBot.coe_add, top_add]
    exact le_top
  · obtain ⟨e, he⟩ := exists_nat_eq_projectiveDimension N hT
    have hle : HasProjectiveDimensionLE (ModuleCat.of R N) e :=
      (CategoryTheory.projectiveDimension_le_iff _ e).mp (le_of_eq he)
    rw [he]
    exact_mod_cast depth_self_le_add_depth e N hle

end

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Small.{v} R]

/-! ### The reverse inequality -/

/-- **Rees' theorem**, in the form used here: for a nonzero finite module `M` over a Noetherian
local ring, `n ≤ depth_𝔪(M)` if and only if `Ext^i(κ, M)` vanishes for every `i < n`, where `κ`
is the residue field. This is `ModuleCat.exists_isRegular_tfae` together with the existence of a
maximal regular sequence (Tag 090R). -/
@[ega "0 16.4.4" "n ≤ depth iff Ext^i(k",
  sga "2 III 2.2" "special case",
  sga "2 III 2.4" "(3)⇔(4)",
  sga "2 III 3.4" "(1)⇔(3), special case"]
private theorem le_depth_iff_forall_subsingleton_ext (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (n : ℕ) :
    (n : ℕ∞) ≤ Module.depth R (maximalIdeal R) M ↔
      ∀ i < n, Subsingleton
        (Abelian.Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) (ModuleCat.of R M) i) := by
  have hlt : maximalIdeal R • (⊤ : Submodule R M) < ⊤ :=
    lt_of_le_of_ne le_top (smul_top_ne_top M)
  have key : ∀ m : ℕ, (∀ i < m, Subsingleton
      (Abelian.Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) (ModuleCat.of R M) i)) ↔
      ∃ rs : List R, rs.length = m ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular M rs := fun m =>
    (ModuleCat.exists_isRegular_tfae (R := R) (maximalIdeal R) m (ModuleCat.of R M) hlt).out 2 4
  refine ⟨fun h i hi => ?_, fun h => ?_⟩
  · obtain ⟨ss, hmem, hreg, hlen⟩ :=
      (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
        (maximalIdeal R) M).2 (smul_top_ne_top M) [] (by simp)
        (RingTheory.Sequence.IsRegular.nil R M)
    rw [List.nil_append] at hreg hlen
    have hn : n ≤ ss.length := by
      have h' : (n : ℕ∞) ≤ (ss.length : ℕ∞) := hlen ▸ h
      exact_mod_cast h'
    exact (key ss.length).2 ⟨ss, rfl, hmem, hreg⟩ i (lt_of_lt_of_le hi hn)
  · obtain ⟨rs, hlen, hmem, hreg⟩ := (key n).1 h
    have h' := Module.le_depth_of_isRegular (maximalIdeal R) (M := M) (rs := rs) hmem hreg
    rwa [hlen] at h'

/-- `Ext^{depth_𝔪(M)}(κ, M)` is nonzero: the depth is the *least* index with nonvanishing `Ext`
out of the residue field. -/
private theorem not_subsingleton_ext_depth (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (t : ℕ)
    (ht : Module.depth R (maximalIdeal R) M = (t : ℕ∞)) :
    ¬ Subsingleton
      (Abelian.Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) (ModuleCat.of R M) t) := by
  intro hsub
  have hle : ((t + 1 : ℕ) : ℕ∞) ≤ Module.depth R (maximalIdeal R) M := by
    refine (le_depth_iff_forall_subsingleton_ext M (t + 1)).2 fun i hi => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact (le_depth_iff_forall_subsingleton_ext M t).1 ht.ge i hlt
    · exact hsub
  rw [ht] at hle
  have : t + 1 ≤ t := by exact_mod_cast hle
  omega

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- **Dimension shifting for `Ext(κ, -)`.** If the first map of a short exact sequence induces the
zero map on `Ext^t(X, -)` and `Ext^t(X, X₁)` has a nonzero element, then `t` is a successor `s + 1`
and `Ext^s(X, X₃)` has a nonzero element. -/
private theorem exists_ne_zero_ext_of_comp_eq_zero {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) (X : ModuleCat.{v} R) (t : ℕ)
    (hzero : ∀ x : Abelian.Ext X S.X₁ t, x.comp (Abelian.Ext.mk₀ S.f) (add_zero t) = 0)
    (x : Abelian.Ext X S.X₁ t) (hx : x ≠ 0) :
    ∃ s : ℕ, t = s + 1 ∧ ∃ y : Abelian.Ext X S.X₃ s, y ≠ 0 := by
  match t with
  | 0 =>
    have := hS.mono_f
    exact absurd (Abelian.Ext.postcomp_mk₀_injective_of_mono X S.f
      (a₁ := x) (a₂ := 0) (by simpa using hzero x)) hx
  | s + 1 =>
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS x (hzero x) rfl
    refine ⟨s, rfl, y, fun hy0 => hx ?_⟩
    rw [← hy, hy0]
    simp

omit [IsNoetherianRing R] [IsLocalRing R] [Small.{v} R] in
/-- A map out of a finite free module whose image lies in `I • F` lies in `I • Hom(K, F)`. -/
private theorem mem_smul_top_of_range_le_smul_top {I : Ideal R} {K F : Type*} [AddCommGroup K]
    [Module R K] [AddCommGroup F] [Module R F] [Module.Free R K] [Module.Finite R K]
    (φ : K →ₗ[R] F) (hφ : LinearMap.range φ ≤ I • (⊤ : Submodule R F)) :
    φ ∈ I • (⊤ : Submodule R (K →ₗ[R] F)) := by
  classical
  obtain ⟨n, ⟨b⟩⟩ : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R K) :=
    ⟨_, ⟨(Module.Free.chooseBasis R K).reindex (Fintype.equivFin _)⟩⟩
  have hrepr : φ = ∑ i, (b.coord i).smulRight (φ (b i)) := by
    refine LinearMap.ext fun k => ?_
    calc φ k = φ (∑ i, b.repr k i • b i) := by rw [b.sum_repr]
      _ = ∑ i, b.repr k i • φ (b i) := by simp only [map_sum, map_smul]
      _ = (∑ i, (b.coord i).smulRight (φ (b i))) k := by
          simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply]
  have hsmulRight : ∀ (i : Fin n) (y : F), y ∈ I • (⊤ : Submodule R F) →
      (b.coord i).smulRight y ∈ I • (⊤ : Submodule R (K →ₗ[R] F)) := by
    intro i y hy
    refine Submodule.smul_induction_on hy (fun r hr z _ => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
    · have h : (b.coord i).smulRight (r • z) = r • (b.coord i).smulRight z := by
        refine LinearMap.ext fun k => ?_
        simp only [LinearMap.smulRight_apply, LinearMap.smul_apply]
        exact smul_comm _ _ _
      rw [h]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · have h : (b.coord i).smulRight (y₁ + y₂)
          = (b.coord i).smulRight y₁ + (b.coord i).smulRight y₂ := by
        refine LinearMap.ext fun k => ?_
        simp [LinearMap.smulRight_apply, smul_add]
      rw [h]
      exact Submodule.add_mem _ h₁ h₂
  rw [hrepr]
  exact Submodule.sum_mem _ fun i _ => hsmulRight i _ (hφ ⟨b i, rfl⟩)

omit [IsNoetherianRing R] in
/-- A map out of a finite free module whose image lies in `𝔪 F` induces the zero map on
`Ext^t(κ, -)`, because `𝔪` annihilates the residue field `κ` and hence every `Ext^t(κ, -)`. -/
private theorem ext_comp_mk₀_eq_zero_of_range_le_smul_top {K F : Type v} [AddCommGroup K]
    [Module R K] [AddCommGroup F] [Module R F] [Module.Free R K] [Module.Finite R K]
    (φ : K →ₗ[R] F) (hφ : LinearMap.range φ ≤ maximalIdeal R • (⊤ : Submodule R F)) (t : ℕ)
    (x : Abelian.Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) (ModuleCat.of R K) t) :
    x.comp (Abelian.Ext.mk₀ (ModuleCat.ofHom φ)) (add_zero t) = 0 := by
  have hann : maximalIdeal R ≤ Module.annihilator R (Shrink.{v} (R ⧸ maximalIdeal R)) := by
    rw [(Shrink.linearEquiv R (R ⧸ maximalIdeal R)).annihilator_eq, Ideal.annihilator_quotient]
  have hsmul : ∀ (r : R), r ∈ maximalIdeal R →
      ∀ y : Abelian.Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R)))
        (ModuleCat.of R F) t, r • y = 0 := by
    intro r hr y
    have h := Abelian.Ext.postcomp_smul_id_eq_zero_of_mem_annihilator
      (N := ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) (M := ModuleCat.of R F)
      (r := r) (hann hr) t
    simpa [Abelian.Ext.mk₀_smul] using congrArg (fun f => (AddCommGrpCat.Hom.hom f) y) h
  have hmem := mem_smul_top_of_range_le_smul_top (I := maximalIdeal R) φ hφ
  refine Submodule.smul_induction_on hmem (fun r hr ψ _ => ?_) (fun ψ₁ ψ₂ h₁ h₂ => ?_)
  · have hof : ModuleCat.ofHom (r • ψ) = r • ModuleCat.ofHom (X := K) (Y := F) ψ := by
      ext k
      simp
    rw [hof, Abelian.Ext.mk₀_smul, Abelian.Ext.comp_smul]
    exact hsmul r hr _
  · have hof : ModuleCat.ofHom (ψ₁ + ψ₂)
        = ModuleCat.ofHom (X := K) (Y := F) ψ₁ + ModuleCat.ofHom ψ₂ := by
      ext k
      simp
    rw [hof, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add, h₁, h₂, add_zero]

omit [IsNoetherianRing R] in
/-- **Existence of a minimal free cover.** A finite module `N` over a local ring is a quotient of
a finite free module `F` by a submodule of `𝔪 F`: take a generating family of least cardinality;
a relation with a unit coefficient would let one of its members be dropped. -/
private theorem exists_surjective_ker_le_smul_top (N : Type v) [AddCommGroup N] [Module R N]
    [Module.Finite R N] :
    ∃ (m : ℕ) (p : Shrink.{v} (Fin m → R) →ₗ[R] N), Function.Surjective p ∧
      LinearMap.ker p ≤ maximalIdeal R • (⊤ : Submodule R (Shrink.{v} (Fin m → R))) := by
  classical
  obtain ⟨m, f, hf, hmin⟩ : ∃ (m : ℕ) (f : Fin m → N), Submodule.span R (Set.range f) = ⊤ ∧
      ∀ k < m, ∀ g : Fin k → N, Submodule.span R (Set.range g) ≠ ⊤ := by
    have hex : ∃ m : ℕ, ∃ f : Fin m → N, Submodule.span R (Set.range f) = ⊤ :=
      Submodule.fg_iff_exists_fin_generating_family.mp Module.Finite.fg_top
    obtain ⟨f, hf⟩ := Nat.find_spec hex
    exact ⟨Nat.find hex, f, hf, fun k hk g hg => Nat.find_min hex hk ⟨g, hg⟩⟩
  have b : Module.Basis (Fin m) R (Shrink.{v} (Fin m → R)) :=
    Module.Basis.ofEquivFun (Shrink.linearEquiv R (Fin m → R))
  refine ⟨m, b.constr ℕ f, ?_, ?_⟩
  · rwa [← LinearMap.range_eq_top, Module.Basis.constr_range]
  · intro x hx
    have hxsum : ∑ i, b.repr x i • f i = 0 := by
      rw [LinearMap.mem_ker, Module.Basis.constr_apply_fintype] at hx
      simpa [Module.Basis.equivFun_apply] using hx
    have hcoord : ∀ i, b.repr x i ∈ maximalIdeal R := by
      intro j
      by_contra hj
      have hunit : IsUnit (b.repr x j) := IsLocalRing.notMem_maximalIdeal.mp hj
      have hmpos : 0 < m := j.pos
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hspan : Submodule.span R (Set.range (f ∘ j.succAbove)) = ⊤ := by
        rw [eq_top_iff, ← hf, Submodule.span_le]
        rintro y ⟨i, rfl⟩
        by_cases hij : i = j
        · subst hij
          have hsum : b.repr x i • f i
              = - ∑ l ∈ Finset.univ.erase i, b.repr x l • f l := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hxsum
            exact eq_neg_of_add_eq_zero_left hxsum
          have hmem : b.repr x i • f i ∈ Submodule.span R (Set.range (f ∘ i.succAbove)) := by
            rw [hsum]
            refine Submodule.neg_mem _ (Submodule.sum_mem _ fun l hl => ?_)
            obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq (Finset.ne_of_mem_erase hl)
            exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, by simp [hz]⟩)
          obtain ⟨u, hu⟩ := hunit
          have : f i = (↑u⁻¹ : R) • (b.repr x i • f i) := by
            rw [smul_smul, ← hu]
            simp
          rw [this]
          exact Submodule.smul_mem _ _ hmem
        · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hij
          exact Submodule.subset_span ⟨z, by simp [hz]⟩
      exact hmin m' (by omega) (f ∘ j.succAbove) hspan
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => smul_mem_smul_top _ (hcoord i) (b i)

omit [IsNoetherianRing R] [IsLocalRing R] [Small.{v} R] in
/-- **Dimension shift along a presentation, the other way.** If `p : P → M` is a surjection with
`P` projective whose syzygy `ker p` has projective dimension at most `n`, then `M` has projective
dimension at most `n + 1`. -/
private theorem hasProjectiveDimensionLE_of_ker {P M : Type v}
    [AddCommGroup P] [Module R P] [Module.Projective R P] [AddCommGroup M] [Module R M]
    {p : P →ₗ[R] M} (hp : Function.Surjective p) (n : ℕ)
    (h : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker p)) n) :
    HasProjectiveDimensionLE (ModuleCat.of R M) (n + 1) := by
  exact (shortExact_ker_subtype hp).hasProjectiveDimensionLT_X₃_iff n
    (ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of R P)) |>.mpr h

/-- **The reverse inequality, by induction on the length of a projective resolution.** If `N` is
nonzero and finite with `pd_R(N) = e ≤ n`, then `e + depth_𝔪(N) ≤ depth_𝔪(R)`. -/
private theorem add_depth_le_depth_self (n : ℕ) :
    ∀ (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N] (e : ℕ),
      Module.projectiveDimension R N = (e : WithBot ℕ∞) → e ≤ n →
        (e : ℕ∞) + Module.depth R (maximalIdeal R) N
          ≤ Module.depth R (maximalIdeal R) R := by
  induction n with
  | zero =>
    intro N _ _ _ _ e he hen
    obtain rfl : e = 0 := Nat.le_zero.mp hen
    have := free_of_hasProjectiveDimensionLE_zero N
      ((CategoryTheory.projectiveDimension_le_iff _ 0).mp (le_of_eq he))
    rw [depth_eq_depth_self_of_free N]
    simp
  | succ n ih =>
    intro N _ _ _ _ e he hen
    match e with
    | 0 => exact ih N 0 he n.zero_le
    | e + 1 =>
      -- a minimal free cover of `N`
      obtain ⟨k, p, hp, hker⟩ := exists_surjective_ker_le_smul_top (R := R) N
      set F := Shrink.{v} (Fin k → R) with hF
      have eF : F ≃ₗ[R] (Fin k → R) := Shrink.linearEquiv R (Fin k → R)
      have : Module.Finite R F := Module.Finite.equiv eF.symm
      have : Module.Free R F := Module.Free.of_equiv eF.symm
      have hntrF : Nontrivial F := hp.nontrivial
      have hdF : Module.depth R (maximalIdeal R) F = Module.depth R (maximalIdeal R) R :=
        depth_eq_depth_self_of_free F
      have hfin : Module.Finite R (LinearMap.ker p) :=
        Module.Finite.of_injective (LinearMap.ker p).subtype (LinearMap.ker p).injective_subtype
      have hNle : HasProjectiveDimensionLE (ModuleCat.of R N) (e + 1) :=
        (CategoryTheory.projectiveDimension_le_iff _ (e + 1)).mp (le_of_eq he)
      have hKle : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker p)) e :=
        hasProjectiveDimensionLE_ker hp e hNle
      -- the syzygy is nonzero, since `N` is not free
      have hntrK : Nontrivial (LinearMap.ker p) := by
        rcases subsingleton_or_nontrivial (LinearMap.ker p) with hs | hs
        · have hinj : Function.Injective p := by
            rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
            exact fun y hy => congrArg Subtype.val (Subsingleton.elim (⟨y, hy⟩ : LinearMap.ker p) 0)
          have hiso : F ≃ₗ[R] N := LinearEquiv.ofBijective p ⟨hinj, hp⟩
          have : Module.Free R N := Module.Free.of_equiv hiso
          have : Projective (ModuleCat.of R N) :=
            (IsProjective.iff_projective (ModuleCat.of R N)).mp inferInstance
          have h0 : Module.projectiveDimension R N = 0 :=
            ModuleCat.projectiveDimension_eq_zero_of_projective (ModuleCat.of R N)
          rw [he] at h0
          exact absurd (show (e + 1 : ℕ) = 0 by exact_mod_cast h0) (by omega)
        · exact hs
      -- the projective dimension of the syzygy
      obtain ⟨j, hj, hje⟩ : ∃ j : ℕ, Module.projectiveDimension R (LinearMap.ker p)
          = (j : WithBot ℕ∞) ∧ j ≤ e := by
        have hlej : Module.projectiveDimension R (LinearMap.ker p) ≤ (e : WithBot ℕ∞) :=
          (CategoryTheory.projectiveDimension_le_iff _ e).mpr hKle
        obtain ⟨j, hj⟩ := exists_nat_eq_projectiveDimension (LinearMap.ker p)
          (ne_top_of_le_ne_top
            (by rw [← WithBot.coe_top]; exact_mod_cast ENat.natCast_ne_top e) hlej)
        exact ⟨j, hj, by rw [hj] at hlej; exact_mod_cast hlej⟩
      -- `pd_R(N) ≤ pd_R(ker p) + 1`
      have hej : e ≤ j := by
        have h1 : Module.projectiveDimension R N ≤ ((j + 1 : ℕ) : WithBot ℕ∞) :=
          (CategoryTheory.projectiveDimension_le_iff _ (j + 1)).mpr
            (hasProjectiveDimensionLE_of_ker hp j
              ((CategoryTheory.projectiveDimension_le_iff _ j).mp (le_of_eq hj)))
        rw [he] at h1
        have : e + 1 ≤ j + 1 := by exact_mod_cast h1
        omega
      -- the depths, as natural numbers
      obtain ⟨t, ht⟩ : ∃ t : ℕ, Module.depth R (maximalIdeal R) (LinearMap.ker p) = (t : ℕ∞) :=
        Option.ne_none_iff_exists'.mp (depth_ne_top (LinearMap.ker p))
      obtain ⟨d, hd⟩ : ∃ d : ℕ, Module.depth R (maximalIdeal R) R = (d : ℕ∞) :=
        Option.ne_none_iff_exists'.mp (depth_ne_top R)
      -- the induction hypothesis, applied to the syzygy
      have hIH : (j : ℕ∞) + Module.depth R (maximalIdeal R) (LinearMap.ker p)
          ≤ Module.depth R (maximalIdeal R) R := ih (LinearMap.ker p) j hj (by omega)
      -- the short exact sequence `0 → ker p → F → N → 0`
      have hSE := shortExact_ker_subtype hp
      -- the inclusion of the syzygy induces the zero map on `Ext^t(κ, -)`
      have hzero : ∀ x : Abelian.Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R)))
          (ModuleCat.of R (LinearMap.ker p)) t,
          x.comp (Abelian.Ext.mk₀ (ModuleCat.ofHom (LinearMap.ker p).subtype))
            (add_zero t) = 0 := by
        by_cases hcase : t < d
        · intro x
          have hsub : Subsingleton (Abelian.Ext
              (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) (ModuleCat.of R F) t) :=
            (le_depth_iff_forall_subsingleton_ext F d).1 (by rw [hdF, hd]) t hcase
          exact Subsingleton.elim _ _
        · -- then the syzygy is free, and its inclusion has all coefficients in `𝔪`
          have hj0 : j = 0 := by
            have h1 : (j : ℕ∞) + (t : ℕ∞) ≤ (d : ℕ∞) := by rw [← ht, ← hd]; exact hIH
            have h2 : j + t ≤ d := by exact_mod_cast h1
            omega
          have := free_of_hasProjectiveDimensionLE_zero (LinearMap.ker p)
            ((CategoryTheory.projectiveDimension_le_iff _ 0).mp (le_of_eq (hj0 ▸ hj)))
          intro x
          refine ext_comp_mk₀_eq_zero_of_range_le_smul_top (LinearMap.ker p).subtype ?_ t x
          rw [Submodule.range_subtype]
          exact hker
      -- shifting the nonvanishing `Ext^t(κ, ker p)` down to `Ext^{t-1}(κ, N)`
      have hntrExt : ¬ Subsingleton (Abelian.Ext
          (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R)))
          (ModuleCat.of R (LinearMap.ker p)) t) := not_subsingleton_ext_depth _ t ht
      have hntr : Nontrivial (Abelian.Ext
          (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R)))
          (ModuleCat.of R (LinearMap.ker p)) t) := not_subsingleton_iff_nontrivial.mp hntrExt
      obtain ⟨x, hx⟩ := exists_ne (0 : Abelian.Ext
        (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R)))
        (ModuleCat.of R (LinearMap.ker p)) t)
      obtain ⟨s, hts, y, hy⟩ := exists_ne_zero_ext_of_comp_eq_zero hSE _ t hzero x hx
      have hNs : Module.depth R (maximalIdeal R) N ≤ (s : ℕ∞) := by
        by_contra hcon
        have hlt : ((s + 1 : ℕ) : ℕ∞) ≤ Module.depth R (maximalIdeal R) N := by
          push_cast
          exact Order.add_one_le_of_lt (not_le.mp hcon)
        have hsub := (le_depth_iff_forall_subsingleton_ext N (s + 1)).1 hlt s (Nat.lt_succ_self s)
        exact hy (@Subsingleton.elim _ hsub _ _)
      calc ((e + 1 : ℕ) : ℕ∞) + Module.depth R (maximalIdeal R) N
          ≤ ((j : ℕ∞) + 1) + (s : ℕ∞) := by
            gcongr
            · push_cast
              have hej' : (e : ℕ∞) ≤ (j : ℕ∞) := by exact_mod_cast hej
              exact add_le_add hej' le_rfl
        _ = (j : ℕ∞) + (t : ℕ∞) := by rw [hts]; push_cast; ring
        _ ≤ Module.depth R (maximalIdeal R) R := by rw [← ht]; exact hIH
end

/-- The Auslander-Buchsbaum formula: for a nonzero finite module `M` of finite projective
dimension over a Noetherian local ring `(R, 𝔪)`, `pd_R(M) + depth_𝔪(M) = depth_𝔪(R)`. -/
public theorem solution {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (hM : Module.projectiveDimension R M ≠ ⊤) :
    Module.projectiveDimension R M + (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) =
      (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) := by
  refine le_antisymm ?_ (depth_self_le_projectiveDimension_add_depth M)
  obtain ⟨e, he⟩ := exists_nat_eq_projectiveDimension M hM
  rw [he]
  exact_mod_cast add_depth_le_depth_self e M e he le_rfl

end Stacks.ProjectiveDimension.DepthFormula

/-!
# The Auslander-Buchsbaum formula

Let `(R, 𝔪)` be a Noetherian local ring and let `M` be a nonzero finite `R`-module of finite
projective dimension. Then

`pd_R(M) + depth_𝔪(M) = depth_𝔪(R)`.

The case `depth_𝔪(M) = 0` carries the content. Take a minimal finite free resolution
`0 → R^{n_e} → ⋯ → R^{n_0} → M → 0`, so that `e = pd_R(M)` and all matrix coefficients of its
maps lie in `𝔪` (Tag 00MT). The determinantal criterion for the exactness of a complex of
finite free modules (Tag 00N1) then forces `depth_𝔪(R) ≥ e`, while breaking the resolution into
the short exact sequences `0 → K_{i-1} → R^{n_i} → K_i → 0` and applying the depth estimate for
an extension (Tag 00LX) `e` times gives `depth_𝔪(M) ≥ depth_𝔪(R) - e`, whence `depth_𝔪(R) ≤ e`.
For `depth_𝔪(M) > 0` one picks `x ∈ 𝔪` a nonzerodivisor on both `R` and `M`: the resolution
stays minimal after `- ⊗_R R/xR`, so `pd_R(M) = pd_{R/xR}(M/xM)`, and both depths drop by one
(Tag 090R), which is the induction step.

## Main results

* `Module.projectiveDimension_add_depth_eq_depth_self`: the Auslander-Buchsbaum formula
  `pd_R(M) + depth_𝔪(M) = depth_𝔪(R)` for a nonzero finite module of finite projective
  dimension over a Noetherian local ring.

## Implementation notes

Faithfulness to [StacksProject 090V]:

1. Every hypothesis is used. `Nontrivial M` is the source's `M ≠ 0`: for `M = 0` the left side
   is `⊥ + ⊤ = ⊥` and the right side a natural number. `hM` is the source's finiteness of
   `pd_R(M)`: without it the left side is `⊤`. `Module.Finite R M`, `IsNoetherianRing R` and
   `IsLocalRing R` are the source's; locality is what `𝔪` is taken from, finiteness and
   Noetherianity are what make `depth_𝔪(M)` and `depth_𝔪(R)` finite and produce the minimal
   free resolution the formula is read off.
2. The scalars and the base are the source's. `M` is an `R`-module, both depths are taken along
   the maximal ideal of `R` itself with regular sequences drawn from `R`, and the projective
   dimension is the one over `R`; no localisation or base change intervenes.
3. Both invariants are pinned rather than bounded: the statement equates the value of
   `Module.projectiveDimension R M` (Tag 00O4) plus the value of `Module.depth R 𝔪 M`
   (Tag 00LI) with the value of `Module.depth R 𝔪 R`, so it computes `depth_𝔪(R)`.
4. Not degenerate. For `R = k[[x, y]]` and `M = R/xR` the three quantities are `1`, `1`, `2`;
   for `M = k` they are `2`, `0`, `2`, which is the case `depth_𝔪(M) = 0`; for `M = R` they are
   `0`, `2`, `2`. Finite projective dimension cannot be dropped: over `R = k[x]/(x²)` and
   `M = k` both depths are `0` while `pd_R(M) = ⊤`.

Three departures from the source's form, none of them weakening it.

The formula is stated with the sum on the left, as Mathlib's
`ringKrullDim_add_length_eq_ringKrullDim_of_isRegular` is, so that the name reads off the
statement. It is an equality in `WithBot ℕ∞`, the target of
`CategoryTheory.projectiveDimension`, into which the `ℕ∞`-valued depth is coerced; the value `⊥`
there is the projective dimension of the zero module and `⊤` that of a module of infinite
projective dimension, both excluded by the hypotheses, so the left-hand side is a genuine sum of
natural numbers.

The module is a plain type rather than an object of `ModuleCat.{v} R`, since `Module.depth`
(Tag 00LI) is stated for plain modules and `Module.projectiveDimension` (Tag 00O4) is the
projective dimension of one; the two forms agree by `Module.projectiveDimension`'s definition,
which is a reducible `abbrev` for `CategoryTheory.projectiveDimension (ModuleCat.of R M)`.

`Small.{v} R` is where the identification of `pd_R(M)` with the source's invariant lives, and it
is not decoration. Tag 00O4 measures projective dimension by the vanishing of `Ext^i(M, -)` in
`ModuleCat.{v} R`, and `CategoryTheory.projectiveDimension_ne_top_iff` turns the hypothesis
`≠ ⊤` into a bound `HasProjectiveDimensionLE (ModuleCat.of R M) n`. Converting that bound into a
finite projective resolution of length `n`, and the minimal length of such a resolution back
into the number, is the content of tags 00O5 and 0CXC, and both directions need
`ModuleCat.{v} R` to have enough projectives — an instance only under `[Small.{v} R]`
(`ModuleCat.enoughProjectives`). So the hypothesis is stated rather than left implicit: without
it `hM` is a condition on Ext-vanishing in a category that need contain no projective object
surjecting onto `M`, and not the source's "has finite projective dimension". It is also the
`variable` block of `Mathlib.RingTheory.Regular.ProjectiveDimension`, whose
`ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular` is the source's
induction step.

Given the remaining hypotheses the smallness is in fact automatic, so it restricts nothing. With
`M` nonzero and finite over `R` Noetherian local, Nakayama gives `M/𝔪M ≠ 0`, a nonzero vector
space over `k = R/𝔪` lying in `Type v`, so `k` is `Small.{v}`; each `R/𝔪ⁿ` has finite length
over `R` with every Jordan-Hölder factor `k`, hence is `Small.{v}` as well; and `⋂ₙ 𝔪ⁿ = 0`
embeds `R` into `∏ₙ R/𝔪ⁿ`. It is kept because instance search does not find it, and because
dropping it would oblige every appeal to Mathlib's projective-dimension API over a local ring to
reprove that chain first; `v = u` satisfies it in any case.

## References

* [StacksProject 090V](https://stacks.math.columbia.edu/tag/090V)

## Tags

Auslander-Buchsbaum, depth, projective dimension, minimal free resolution, Noetherian local ring
-/

namespace Module

/-- **The Auslander-Buchsbaum formula.** Let `(R, 𝔪)` be a Noetherian local ring and let `M` be
a nonzero finite `R`-module of finite projective dimension. Then
`pd_R(M) + depth_𝔪(M) = depth_𝔪(R)`. The equality is read in `WithBot ℕ∞`; the hypotheses make
all three quantities finite. -/
@[stacks 090V "Stated with the sum on the left, in `WithBot ℕ∞`, for `Module.projectiveDimension`
(Tag 00O4) and `Module.depth` along the maximal ideal (Tag 00LI). See the module docstring.",
  ega "0 17.3.4" "more general"]
public theorem projectiveDimension_add_depth_eq_depth_self {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (hM : projectiveDimension R M ≠ ⊤) :
    projectiveDimension R M + (depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) =
      (depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) :=
  Stacks.ProjectiveDimension.DepthFormula.solution M hM

end Module
