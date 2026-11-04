module

public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Depth.ShortExact
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Depth.Nakayama
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Depth of a syzygy module over a Cohen–Macaulay local ring

Proof of `Module.IsMaximalCohenMacaulay.depth_lt_depth_or_isMaximalCohenMacaulay_of_exact`
(Stacks 00NE): let `(R, 𝔪)` be a Noetherian local Cohen–Macaulay ring, `F` a finite free
`R`-module and `0 → K → F → M → 0` a short exact sequence with `M ≠ 0`; then either
`depth_𝔪(M) < depth_𝔪(K)`, or `K` and `M` are both maximal Cohen–Macaulay.

Write `d = depth_𝔪(R)`, so that `dim R = d` by Cohen–Macaulayness and `d ≠ ∞` because a
Noetherian local ring has finite dimension. The whole argument is the third inequality of
Stacks 00LX,
`min {depth_𝔪(F), depth_𝔪(M) + 1} ≤ depth_𝔪(K)`,
fed the two comparisons `d ≤ depth_𝔪(F)` and `depth_𝔪(M) ≤ d`. The first holds because a finite
free module is a finite direct sum of copies of `R` and depth of a direct sum is at least the
minimum of the depths, again by Stacks 00LX. The second is `depth_𝔪(M) ≤ dim Supp(M) ≤ dim R`
(Stacks 00LK), available because `M` is a nonzero finite module and hence `𝔪 M ≠ M` by
Nakayama.

Given these, the dichotomy is arithmetic in `ℕ∞`. If `depth_𝔪(M) < d` the minimum is
`depth_𝔪(M) + 1`, and `depth_𝔪(M) < depth_𝔪(M) + 1` because `depth_𝔪(M) ≠ ∞`; this is the first
alternative. If `depth_𝔪(M) = d` the minimum is at least `d`, so `d ≤ depth_𝔪(K)`; then either
`depth_𝔪(K) = ∞ > d`, which happens exactly when `K = 0` and gives the first alternative again,
or `depth_𝔪(K) ≤ d` by Stacks 00LK once more and both depths equal `d = dim R`.

## Main results

* `Stacks.CohenMacaulay.SyzygyDepth.solution`: over a Cohen–Macaulay Noetherian local ring, if
  `0 → K → F → M → 0` is exact with `F` finite free and `M ≠ 0`, then either
  `depth_𝔪(M) < depth_𝔪(K)`, or `K` and `M` are both maximal Cohen–Macaulay.

## Implementation notes

Two steps of the argument are proved here.

The comparison `d ≤ depth_𝔪(F)` for a finite free `F` is stated in the source in passing, as "a
finite free module over a Cohen–Macaulay local ring has depth `d`". It is proved here as
`depth_le_depth_of_free`, in the generality it has: over a Noetherian ring and for an arbitrary
ideal `I`, `depth_I(R) ≤ depth_I(F)` for every finite free `R`-module `F`. Only this inequality is
needed, so nothing has to be said about the zero free module, whose depth is `∞`. The proof is an
induction on the rank along `(Fin (n + 1) → R) ≃ R × (Fin n → R)` using the *first* inequality of
Stacks 00LX for the split sequence `0 → R → R × N → N → 0`, so the free case rests on the same
lemma as the main theorem itself. Its ingredients are `Module.depth_eq_depth_of_linearEquiv`, the
invariance of `Module.depth` under a linear equivalence, and `Module.depth_eq_top_of_subsingleton`,
the value of the depth of the zero module; both are read off the definition of tag 00LI.

The bookkeeping that turns the three comparisons into the dichotomy is separated from the
modules as `lt_or_eq_and_eq_of_min_add_one_le`, an inequality in `ℕ∞`: it is where the case
distinction `depth_𝔪(M) < d` versus `depth_𝔪(M) = d` lives, and it is the only place the
finiteness of `d` and the truncation-free arithmetic of `ℕ∞` are used.

Nakayama's lemma is used through `Module.maximalIdeal_smul_top_ne_top`, `𝔪 • M ≠ M` for a nonzero
finite module over a local ring, which is Mathlib's
`Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator` together with
`IsLocalRing.jacobson_eq_maximalIdeal`. Finiteness of `M` comes from surjectivity of `F → M` and
finiteness of `K` from injectivity of `K → F` into the Noetherian module `F`; neither is a
hypothesis of the theorem.

## References

* [StackProject 00NE](https://stacks.math.columbia.edu/tag/00NE)
* [StackProject 00LX](https://stacks.math.columbia.edu/tag/00LX)
* [StackProject 00LK](https://stacks.math.columbia.edu/tag/00LK)
-/

@[expose] public section

namespace Stacks.CohenMacaulay.SyzygyDepth

open IsLocalRing

section Depth

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The depth of a product is at least the minimum of the depths: the first inequality of
Stacks 00LX for the split short exact sequence `0 → M → M × N → N → 0`. -/
private theorem min_depth_le_depth_prod [IsNoetherianRing R] (M N : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [AddCommGroup N] [Module R N] [Module.Finite R N] :
    min (Module.depth R I M) (Module.depth R I N) ≤ Module.depth R I (M × N) :=
  (Module.min_depth_le_depth_of_exact I (f := LinearMap.inl R M N) (g := LinearMap.snd R M N)
    Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective).1

/-- `depth_I(R) ≤ depth_I(R^n)` for every `n`, by induction along
`(Fin (n + 1) → R) ≃ R × (Fin n → R)`. -/
private theorem depth_le_depth_pi_fin [IsNoetherianRing R] (n : ℕ) :
    Module.depth R I R ≤ Module.depth R I (Fin n → R) := by
  induction n with
  | zero =>
      have : Subsingleton (Fin 0 → R) := ⟨fun a b => funext fun i => i.elim0⟩
      exact le_top.trans (Module.depth_eq_top_of_subsingleton I).ge
  | succ n ih =>
      rw [← Module.depth_eq_depth_of_linearEquiv I
        (Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R))]
      exact (le_min le_rfl ih).trans (min_depth_le_depth_prod I R (Fin n → R))

/-- **A finite free module has depth at least that of the ring.** For `R` Noetherian, `I` an
ideal of `R` and `F` a finite free `R`-module, `depth_I(R) ≤ depth_I(F)`. Over a
Cohen–Macaulay local ring and for `I = 𝔪` this says `dim R ≤ depth_𝔪(F)`. -/
@[sga "2 X 2.1" "inequality depth O_{U"]
private theorem depth_le_depth_of_free [IsNoetherianRing R] (F : Type*) [AddCommGroup F]
    [Module R F] [Module.Free R F] [Module.Finite R F] :
    Module.depth R I R ≤ Module.depth R I F := by
  classical
  have e : F ≃ₗ[R] (Fin (Fintype.card (Module.Free.ChooseBasisIndex R F)) → R) :=
    (Module.Free.chooseBasis R F).equivFun.trans
      (LinearEquiv.piCongrLeft' R _ (Fintype.equivFin _))
  rw [Module.depth_eq_depth_of_linearEquiv I e]
  exact depth_le_depth_pi_fin I _

end Depth

section Local

variable {R : Type*} [CommRing R] [IsLocalRing R]
  (hR : Module.IsMaximalCohenMacaulay R R) (M : Type*) [AddCommGroup M] [Module R M]

include hR in
/-- Cohen–Macaulayness of the ring, spelled as the equality of `depth_𝔪(R)` with `dim R` in
`WithBot ℕ∞`, where both comparisons of the argument take place. -/
private theorem coe_depth_eq_ringKrullDim :
    ((Module.depth R (maximalIdeal R) R : ℕ∞) : WithBot ℕ∞) = ringKrullDim R := hR

include hR in
/-- Over a local Cohen–Macaulay ring, a nonzero finite module has depth at most that of the
ring: `depth_𝔪(M) ≤ dim Supp(M) ≤ dim R = depth_𝔪(R)` by Stacks 00LK. -/
private theorem depth_le_depth_ring [Module.Finite R M] [Nontrivial M] :
    Module.depth R (maximalIdeal R) M ≤ Module.depth R (maximalIdeal R) R :=
  WithBot.coe_le_coe.mp <|
    ((Module.depth_le_supportDim R _ M (Module.maximalIdeal_smul_top_ne_top M)).trans
      (Module.supportDim_le_ringKrullDim R M)).trans_eq (coe_depth_eq_ringKrullDim hR).symm

include hR in
/-- The previous inequality without the nonvanishing hypothesis: a finite module over a local
Cohen–Macaulay ring has depth at most `depth_𝔪(R)`, except that the zero module has depth `∞`. -/
private theorem depth_le_depth_ring_or_eq_top [Module.Finite R M] :
    Module.depth R (maximalIdeal R) M ≤ Module.depth R (maximalIdeal R) R ∨
      Module.depth R (maximalIdeal R) M = ⊤ := by
  rcases subsingleton_or_nontrivial M with _ | _
  · exact Or.inr (Module.depth_eq_top_of_subsingleton _)
  · exact Or.inl (depth_le_depth_ring hR M)

include hR in
/-- A finite module whose depth is that of the ring is maximal Cohen–Macaulay, the ring being
Cohen–Macaulay. -/
private theorem isMaximalCohenMacaulay_of_depth_eq
    (h : Module.depth R (maximalIdeal R) M = Module.depth R (maximalIdeal R) R) :
    Module.IsMaximalCohenMacaulay R M := by
  change ((Module.depth R (maximalIdeal R) M : ℕ∞) : WithBot ℕ∞) = ringKrullDim R
  rw [h]
  exact coe_depth_eq_ringKrullDim hR

include hR in
/-- The depth of a Noetherian local Cohen–Macaulay ring is finite, because its Krull dimension
is. -/
private theorem depth_ne_top [IsNoetherianRing R] :
    Module.depth R (maximalIdeal R) R ≠ ⊤ := fun h => by
  refine ringKrullDim_ne_top (R := R) ?_
  rw [← coe_depth_eq_ringKrullDim hR, h]
  simp

end Local

/-- **The dichotomy of Stacks 00NE, as arithmetic in `ℕ∞`.** Read `a = depth_𝔪(M)`,
`b = depth_𝔪(F)`, `c = depth_𝔪(K)` and `d = depth_𝔪(R) = dim R`: from `a ≤ d ≤ b`, the
finiteness of `d`, the third inequality `min {b, a + 1} ≤ c` of Stacks 00LX and the bound on `c`
of Stacks 00LK, either `c` jumps above `a` or both `a` and `c` are equal to `d`. -/
private theorem lt_or_eq_and_eq_of_min_add_one_le {a b c d : ℕ∞} (hd : d ≠ ⊤) (had : a ≤ d)
    (hdb : d ≤ b) (hmin : min b (a + 1) ≤ c) (hc : c ≤ d ∨ c = ⊤) :
    a < c ∨ (c = d ∧ a = d) := by
  rcases had.lt_or_eq with hlt | rfl
  · -- `a < d`: the minimum is `a + 1`, and `a < a + 1` since `a ≠ ⊤`.
    refine Or.inl (lt_of_lt_of_le ?_
      ((le_min ((Order.add_one_le_of_lt hlt).trans hdb) le_rfl).trans hmin))
    rw [ENat.lt_add_one_iff (ne_top_of_lt hlt)]
  · -- `a = d`: the minimum is at least `d`, so `d ≤ c`, and `c` is either `⊤` or `d`.
    have hac : a ≤ c := (le_min hdb le_self_add).trans hmin
    rcases hc with hc | rfl
    · exact Or.inr ⟨le_antisymm hc hac, rfl⟩
    · exact Or.inl (Ne.lt_top hd)

/-- **Stacks 00NE.** Over a Cohen–Macaulay Noetherian local ring, if `0 → K → F → M → 0` is exact
with `F` finite free and `M ≠ 0`, then either `depth_𝔪(M) < depth_𝔪(K)`, or `K` and `M` are both
maximal Cohen–Macaulay. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Module.IsMaximalCohenMacaulay R R) {K F M : Type*} [AddCommGroup K] [Module R K]
    [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F] [AddCommGroup M]
    [Module R M] [Nontrivial M] {f : K →ₗ[R] F} {g : F →ₗ[R] M} (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.depth R (maximalIdeal R) M < Module.depth R (maximalIdeal R) K ∨
      (Module.IsMaximalCohenMacaulay R K ∧ Module.IsMaximalCohenMacaulay R M) := by
  have : Module.Finite R M := Module.Finite.of_surjective g hg
  have : Module.Finite R K := Module.Finite.of_injective f hf
  -- `depth_𝔪(M) ≤ d ≤ depth_𝔪(F)` and `min {depth_𝔪(F), depth_𝔪(M) + 1} ≤ depth_𝔪(K)`, with
  -- `depth_𝔪(K) ≤ d` unless `K = 0`; the dichotomy is then arithmetic in `ℕ∞`.
  exact (lt_or_eq_and_eq_of_min_add_one_le (depth_ne_top hR) (depth_le_depth_ring hR M)
    (depth_le_depth_of_free _ F) (Module.min_depth_le_depth_of_exact (maximalIdeal R) h hf hg).2.2
    (depth_le_depth_ring_or_eq_top hR K)).imp_right fun hKM =>
      ⟨isMaximalCohenMacaulay_of_depth_eq hR K hKM.1,
        isMaximalCohenMacaulay_of_depth_eq hR M hKM.2⟩

end Stacks.CohenMacaulay.SyzygyDepth

end

/-!
# Depth of a syzygy module over a Cohen–Macaulay local ring

Let `(R, 𝔪)` be a Noetherian local Cohen–Macaulay ring of dimension `d`, let `F` be a finite
free `R`-module and let
$$
  0 \to K \to F \to M \to 0
$$
be a short exact sequence of `R`-modules with `M \neq 0`. Then either the depth of the syzygy
module `K` is strictly larger than the depth of `M`, or both depths are equal to `d`, that is,
both `K` and `M` are maximal Cohen–Macaulay.

The reason is the third inequality of Stacks 00LX,
`min {depth_𝔪(F), depth_𝔪(M) + 1} ≤ depth_𝔪(K)`, together with the fact that a finite free
module over a Cohen–Macaulay local ring has depth `d`. Since `M` is a nonzero finite module,
`depth_𝔪(M) ≤ dim(Supp M) ≤ d` (Stacks 00LK), so the minimum is `depth_𝔪(M) + 1` as soon as
`depth_𝔪(M) < d`, and then the depth of `K` jumps: `depth_𝔪(M) < depth_𝔪(K)`. In the remaining
case `depth_𝔪(M) = d` the minimum is `d`, so `d ≤ depth_𝔪(K)`, and `K` is maximal
Cohen–Macaulay: either `K = 0`, where `depth_𝔪(K) = ⊤` and the first alternative holds because
`d ≠ ⊤`, or `K` is a nonzero finite module and `depth_𝔪(K) ≤ d` by 00LK again.

Iterating the alternative produces free resolutions whose last syzygy is maximal
Cohen–Macaulay, which is Stacks 00NG.

## Main results

* `Module.IsMaximalCohenMacaulay.depth_lt_depth_or_isMaximalCohenMacaulay_of_exact`: for
  `0 → K → F → M → 0` exact with `F` finite free over a Noetherian local Cohen–Macaulay ring
  and `M ≠ 0`, either `depth_𝔪(M) < depth_𝔪(K)` or both `K` and `M` are maximal
  Cohen–Macaulay.

## Implementation notes

Cohen–Macaulayness of the Noetherian local ring `R` is the hypothesis
`Module.IsMaximalCohenMacaulay R R` (tag 00NF), that is `depth_𝔪(R) = dim R`. This is
Definition 00N8 verbatim: `R` is Cohen–Macaulay when it is Cohen–Macaulay as a module over
itself, `depth_𝔪(R) = dim Supp(R)` (Definition 00N3), and `Supp(R) = Spec(R)` because `1` has
zero annihilator.

Four departures from the source's form, none of them weakening it.

The source writes the middle term as `R^{⊕n}`; here it is an arbitrary finite free `R`-module
`F`, of which `Fin n → R` and `ι → R` for a finite `ι` are instances. Nothing in the statement
distinguishes a basis, and the proof uses freeness only through `depth_𝔪(F) = dim R`.

The source's alternative `M = 0` is the hypothesis `[Nontrivial M]`, the two forms being
interchangeable by `subsingleton_or_nontrivial`; a user who knows `M ≠ 0` then has no vacuous
case to dismiss. It cannot be dropped: over `R = k[[x]]` the sequence
`0 → R →(id) R → 0 → 0` has `depth_𝔪(K) = 1 = d` and `depth_𝔪(M) = ⊤`, so neither `⊤ < 1` nor
`⊤ = d` holds.

The source's `depth(K) = depth(M) = d` is the conjunction
`Module.IsMaximalCohenMacaulay R K ∧ Module.IsMaximalCohenMacaulay R M`, which unfolds to
exactly that pair of equations with `d = dim R`.
The source's name `d` for `dim R` is dropped, the equations naming `ringKrullDim R` directly.
Depth takes values in `ℕ∞` and `ringKrullDim` in `WithBot ℕ∞`, the value `⊥` being reserved for
the zero ring; those two equations are therefore read in `WithBot ℕ∞`, while the strict
inequality between the two depths is read in `ℕ∞`.

The short exact sequence is spelled as in tag 00LX (`Module.min_depth_le_depth_of_exact`), the
lemma this is a special case of: an exact pair of `R`-linear maps `f : K →ₗ[R] F`,
`g : F →ₗ[R] M` with `f` injective and `g` surjective. Finiteness of `K` and of `M` is not
assumed, both following from `Module.Finite R F` over the Noetherian ring `R`.

Faithfulness to [StackProject 00NE]:

1. No dead hypothesis. Each of `hR`, `[Module.Free R F]`, `[Module.Finite R F]`,
   `[Nontrivial M]`, `h`, `hf`, `hg` fails the conclusion when dropped. Without `hR`, over the
   non-Cohen–Macaulay ring `R = k[[x, y]]/(x², xy)`, which has `dim R = 1` and
   `depth_𝔪(R) = 0`, the split sequence `0 → R → R² → R → 0` has both depths `0`, so neither
   `0 < 0` nor `0 = dim R` holds. Without freeness of `F`, over `R = k[[x, y]]` the sequence
   `0 → k → k² → k → 0` has both depths `0` while `dim R = 2`. Without `Module.Finite R F`,
   over `R = k[[x]]` a free presentation `0 → K → ⊕_I R → Frac R → 0` of the fraction field has
   `depth_𝔪(M) = ⊤`, since `𝔪 · Frac R = Frac R`, so neither alternative holds; this hypothesis
   is what forces `M` to be finite. Without `hg`, over `R = k[[x]]`, taking `f = id : R → R`
   and `g = 0 : R → Frac R` gives an exact pair with `f` injective, `depth_𝔪(K) = 1` and
   `depth_𝔪(M) = ⊤`. Without `hf`, over `R = k[[x]]`, `K = k ⊕ R`, `f (a, r) = x · r`,
   `F = R` and `g : R ↠ k` is exact with `g` surjective, and `depth_𝔪(K) = depth_𝔪(M) = 0`
   while `d = 1`. Without `h`, over `R = k[[x, y]]`, `f : 𝔪 → R` the inclusion and
   `g = id : R → R` has `f` injective and `g` surjective, with `depth_𝔪(K) = 1` and
   `depth_𝔪(M) = 2`, so `2 < 1` fails and `1 ≠ 2 = d`. `[IsNoetherianRing R]` is the source's
   and is load-bearing: it is consumed by Rees' theorem behind 00LX and by 00LK, and it is what
   makes `dim R` finite, without which the case distinction above collapses.
2. The scalars and base are the source's. All three modules are `R`-modules, `f` and `g` are
   `R`-linear, all three depths are taken over `R` along the maximal ideal of `R` itself, and
   the dimension is `ringKrullDim R`; no localisation or base change intervenes.
3. The quantities are pinned, not merely compared. Each depth is a value of `Module.depth`
   (tag 00LI) along the canonical `IsLocalRing.maximalIdeal R`, `d` is `ringKrullDim R`, and
   the sequence is pinned by the maps `f` and `g` carrying `h`, `hf`, `hg`, rather than
   asserted to exist.
4. The instantiation is not degenerate, and both alternatives occur. Over `R = k[[x]]`, with
   `d = 1`: the sequence `0 → xR → R → k → 0` has `depth_𝔪(K) = 1 > 0 = depth_𝔪(M)`, the first
   alternative, while the split sequence `0 → R → R² → R → 0` has
   `depth_𝔪(K) = depth_𝔪(M) = 1 = d`, the second alternative with `K` and `M` both nonzero.

## References

* [StackProject 00NE](https://stacks.math.columbia.edu/tag/00NE)

## Tags

depth, syzygy, Cohen-Macaulay ring, maximal Cohen-Macaulay module, free resolution
-/

open IsLocalRing

namespace Module

/-- **Depth of a syzygy module over a Cohen–Macaulay local ring.** Let `(R, 𝔪)` be a Noetherian
local Cohen–Macaulay ring, that is `depth_𝔪(R) = dim R`, let `F` be a finite free `R`-module and
let `0 → K → F → M → 0` be a short exact sequence of `R`-modules, given by `f : K →ₗ[R] F`
injective, `g : F →ₗ[R] M` surjective and `Function.Exact f g`, with `M` nonzero. Then either
`depth_𝔪(M) < depth_𝔪(K)`, or `depth_𝔪(K) = depth_𝔪(M) = dim R`, i.e. both `K` and `M` are
maximal Cohen–Macaulay.

The source states the third alternative as `depth(K) = depth(M) = d` and the middle term as
`R^{⊕n}`, and lists `M = 0` as a first alternative in place of the hypothesis
`[Nontrivial M]`. -/
@[stacks 00NE "Cohen-Macaulayness of the Noetherian local ring `R` is
`Module.IsMaximalCohenMacaulay R R`, i.e. `depth_𝔪(R) = dim R` (Definition 00N8); `R^{⊕n}` is an
arbitrary finite free module `F`; the alternative `M = 0` is the hypothesis `[Nontrivial M]`;
and `depth(K) = depth(M) = d` is maximal Cohen-Macaulayness of `K` and of `M`. See the module
docstring."]
public theorem IsMaximalCohenMacaulay.depth_lt_depth_or_isMaximalCohenMacaulay_of_exact
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : IsMaximalCohenMacaulay R R) {K F M : Type*} [AddCommGroup K] [Module R K]
    [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F] [AddCommGroup M]
    [Module R M] [Nontrivial M] {f : K →ₗ[R] F} {g : F →ₗ[R] M} (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    depth R (maximalIdeal R) M < depth R (maximalIdeal R) K ∨
      (IsMaximalCohenMacaulay R K ∧ IsMaximalCohenMacaulay R M) :=
  Stacks.CohenMacaulay.SyzygyDepth.solution (g := g) (f := f) (F := F) hR h hf hg

end Module
