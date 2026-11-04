module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Length
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Depth.Nakayama
public import StacksFrontier.RingTheory.Dualizing.ExtShortExact
public import StacksFrontier.RingTheory.Dualizing.ExtSupportBound
public import StacksFrontier.RingTheory.Dualizing.ExtVanishingRange

import all StacksFrontier.RingTheory.Dualizing.ExtSupportBound

/-!
# The dual of a module of finite length is at least as long

Let `(A, 𝔪)` be a Noetherian local ring with a normalized dualizing complex `ω_A^•` and let `Q`
be an `A`-module of finite length. The dual Ext modules `Ext_A^j(Q, ω_A^•)` vanish for every
`j ≠ 0`, so the whole dual of `Q` is the single module `Ext_A^0(Q, ω_A^•)`. This file proves the
length inequality

`length_A(Q) ≤ length_A(Ext_A^0(Q, ω_A^•))`

by induction on the finite-length structure of `Q`. The two lengths are in fact equal, but the
reverse inequality needs the identification `Ext_A^0(κ, ω_A^•) ≅ κ` of the dual of the residue
field and is not proved here.

## Main results

* `Dualizing.injective_objExtPrecomp_g_of_subsingleton_first` and
  `Dualizing.surjective_objExtPrecomp_f_of_subsingleton_third` — the two ends of the contravariant
  long exact Ext sequence of a short exact sequence close off into a short exact sequence as soon
  as one neighbouring Ext group vanishes.
* `Dualizing.length_objExtInto_zero_eq_add` — additivity of the length of `Ext^0` along a short
  exact sequence whose outer Ext groups vanish in the two neighbouring degrees.
* `Dualizing.length_moduleExtInto_zero_eq_add_submodule` — the same additivity for the short exact
  sequence `0 → N → M → M/N → 0` of a submodule.
* `Dualizing.nontrivial_moduleExtInto_zero_of_isFiniteLength` — for a nonzero module of finite
  length the module `Ext_A^0(Q, ω_A^•)` is nonzero.
* `Dualizing.length_le_length_moduleExtInto_zero` — the length inequality.
* `Dualizing.isFiniteLength_moduleExtInto_of_isFiniteLength` — every `Ext_A^j(Q, ω_A^•)` has
  finite length.

## Implementation notes

The short exact sequences live in `CategoryTheory.ShortComplex (ModuleCat A)`, whose objects are
objects of `ModuleCat A` rather than bare types, so the general statements are phrased with
`Dualizing.objExtInto`; on `ModuleCat.of A M` this is `Dualizing.moduleExtInto M` by definition,
which is why `Dualizing.length_moduleExtInto_zero_eq_add_submodule` follows from
`Dualizing.length_objExtInto_zero_eq_add` with no transport.

The connecting map of `StacksFrontier.RingTheory.Dualizing.ExtShortExact` goes from degree `i` to
degree `i + 1`, so the two bijectivity statements take the two degrees and the equation `i + 1 = j`
relating them as separate arguments: this lets the caller supply `(-1, 0)` and `(0, 1)` without
having to transport along `-1 + 1 = 0` or `0 + 1 = 1`.

A module of finite length is finite, but through `isFiniteLength_iff_isNoetherian_isArtinian`
rather than directly, so the `Module.Finite` hypothesis of the results of
`StacksFrontier/RingTheory/Dualizing/DualExtDepthDimension.lean` is produced inside the proofs rather
than demanded of the caller. The bound `dim Supp(Q) ≤ 0` for such a `Q` is
`Dualizing.supportDim_le_zero_of_finiteLength`, which is `private` in
`StacksFrontier/RingTheory/Dualizing/ExtSupportBound.lean` and so is reached through `import all`.

That every `Ext_A^j(Q, ω_A^•)` has finite length is not obtained from the length inequality,
which runs the other way. Outside degree zero the module vanishes; in degree zero it is a finite
module whose support is contained in the support of `Q`, hence in the closed point, and
`isFiniteLength_of_support_subset` applies. The two inclusions of supports are
`Dualizing.support_subset_of_ext_zero` and `Dualizing.support_subset_of_finiteLength`, both
`private` in `StacksFrontier/RingTheory/Dualizing/ExtSupportBound.lean` and so reached through
`import all` rather than restated here.

The nonvanishing of `Ext_A^0(Q, ω_A^•)` is obtained from
`Dualizing.depth_eq_iInf_nontrivial_moduleExtInto` together with `Module.depth_le_supportDim`: a
nonzero module of finite length has depth `0`, and were `Ext_A^0(Q, ω_A^•)` to vanish then, every
other degree vanishing as well, that infimum would be over the empty set and hence `⊤`.

## References

* [Stacks Project, Lemma 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Dualizing

variable {A : Type u} [CommRing A]

section ShortExact

variable {S : ShortComplex (ModuleCat.{v} A)} (hS : S.ShortExact)
  (K : DerivedCategory (ModuleCat.{v} A))

include hS in
/-- **Additivity of the length of `Ext^0`.** For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of
`A`-modules whose Ext groups into `K` vanish in degree `-1` on `X₁` and in degree `1` on `X₃`, the
three degree-zero Ext groups form a short exact sequence
`0 → Ext^0(X₃) → Ext^0(X₂) → Ext^0(X₁) → 0` and so their lengths add up. -/
theorem length_objExtInto_zero_eq_add (h₁ : Subsingleton (objExtInto S.X₁ K (-1)))
    (h₃ : Subsingleton (objExtInto S.X₃ K 1)) :
    Module.length A (objExtInto S.X₂ K 0) =
      Module.length A (objExtInto S.X₃ K 0) + Module.length A (objExtInto S.X₁ K 0) :=
  Module.length_eq_add_of_exact (objExtPrecomp S.g K 0) (objExtPrecomp S.f K 0)
    (injective_objExtPrecomp_g_of_subsingleton_first hS K (-1) 0 (by norm_num) h₁)
    (surjective_objExtPrecomp_f_of_subsingleton_third hS K 0 1 (by norm_num) h₃)
    (exact_objExtPrecomp_g_objExtPrecomp_f hS K 0)

end ShortExact

/-- **Additivity of the length of `Ext^0` along a submodule.** For a submodule `N` of an
`A`-module `M` whose Ext groups into `K` vanish in degree `-1` on `N` and in degree `1` on `M/N`,
the length of `Ext^0(M, K)` is the sum of the lengths of `Ext^0(M/N, K)` and `Ext^0(N, K)`. This
is `Dualizing.length_objExtInto_zero_eq_add` for the short exact sequence
`0 → N → M → M/N → 0`. -/
theorem length_moduleExtInto_zero_eq_add_submodule {M : Type v} [AddCommGroup M] [Module A M]
    (N : Submodule A M) (K : DerivedCategory (ModuleCat.{v} A))
    (h₁ : Subsingleton (moduleExtInto ↥N K (-1)))
    (h₃ : Subsingleton (moduleExtInto (M ⧸ N) K 1)) :
    Module.length A (moduleExtInto M K 0) =
      Module.length A (moduleExtInto (M ⧸ N) K 0) + Module.length A (moduleExtInto ↥N K 0) :=
  length_objExtInto_zero_eq_add
    (ModuleCat.shortComplex_shortExact
      (ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
        (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero)
      (LinearMap.exact_subtype_mkQ N) (Submodule.subtype_injective N)
      (Submodule.mkQ_surjective N)) K h₁ h₃

/-- **The dual of a nonzero module of finite length is nonzero.** For a nonzero module `Q` of
finite length over a Noetherian local ring with normalized dualizing complex `ω`, the module
`Ext_A^0(Q, ω)` is nonzero. Indeed `depth_𝔪(Q) ≤ dim Supp(Q) ≤ 0`, and the depth is the least
degree `i` with `Ext_A^{-i}(Q, ω) ≠ 0`; if degree `0` vanished then, all other degrees vanishing
for a module of finite length, no degree would be nonzero and the depth would be `⊤`. -/
theorem nontrivial_moduleExtInto_zero_of_isFiniteLength {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {Q : Type u} [AddCommGroup Q] [Module A Q] [Nontrivial Q]
    (hQ : IsFiniteLength A Q) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K) :
    Nontrivial (moduleExtInto Q K 0) := by
  let : IsNoetherian A Q := (isFiniteLength_iff_isNoetherian_isArtinian.mp hQ).1
  let : Module.Finite A Q := inferInstance
  have hdepth : Module.depth A (IsLocalRing.maximalIdeal A) Q = 0 := by
    have hle : (Module.depth A (IsLocalRing.maximalIdeal A) Q : WithBot ℕ∞) ≤ 0 :=
      (Module.depth_le_supportDim A (IsLocalRing.maximalIdeal A) Q
          (Module.maximalIdeal_smul_top_ne_top Q)).trans
        (supportDim_le_zero_of_finiteLength Q hQ)
    exact le_antisymm (by exact_mod_cast hle) zero_le
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  have hle : (1 : ℕ∞) ≤ ⨅ (i : ℕ) (_ : Nontrivial (moduleExtInto Q K (-(i : ℤ)))), (i : ℕ∞) := by
    refine le_iInf fun i => le_iInf fun hi => ?_
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [Nat.cast_zero, neg_zero] at hi
      exact absurd hsub (not_subsingleton_iff_nontrivial.mpr hi)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi0
  rw [← depth_eq_iInf_nontrivial_moduleExtInto K hK, hdepth] at hle
  simp at hle

/-- **The dual of a module of finite length is at least as long.** For a module `Q` of finite
length over a Noetherian local ring with normalized dualizing complex `ω`, the length of
`Ext_A^0(Q, ω)` is at least the length of `Q`.

The proof is an induction on the finite-length structure of `Q`. A subsingleton has length `0`.
For the inductive step, let `N ⊆ Q` be a submodule with `Q/N` simple and `N` of finite length.
The short exact sequence `0 → N → Q → Q/N → 0` gives `length(Q) = length(N) + 1`, since a simple
module has length `1`, and, the dual Ext of a module of finite length being concentrated in degree
zero, also `length(Ext^0(Q, ω)) = length(Ext^0(Q/N, ω)) + length(Ext^0(N, ω))`. The second summand
dominates `length(N)` by induction and the first is at least `1` because `Q/N` is a nonzero module
of finite length. -/
theorem length_le_length_moduleExtInto_zero {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] {Q : Type u} [AddCommGroup Q] [Module A Q] (hQ : IsFiniteLength A Q)
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsNormalizedDualizingComplex.{u, u} K) :
    Module.length A Q ≤ Module.length A (moduleExtInto Q K 0) := by
  induction hQ with
  | of_subsingleton =>
      rw [Module.length_eq_zero]
      exact zero_le
  | of_simple_quotient hN ih =>
      rename_i M _ _ N _
      have hNfl : IsFiniteLength A ↥N := hN
      have hQuot : IsFiniteLength A (M ⧸ N) :=
        (IsFiniteLength.of_simple_quotient hN).of_surjective (Submodule.mkQ_surjective N)
      have hMlen : Module.length A M = Module.length A ↥N + 1 := by
        rw [Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.subtype_injective N)
          (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N),
          Module.length_eq_one A (M ⧸ N)]
      have hElen : Module.length A (moduleExtInto M K 0) =
          Module.length A (moduleExtInto (M ⧸ N) K 0) +
            Module.length A (moduleExtInto ↥N K 0) :=
        length_moduleExtInto_zero_eq_add_submodule N K
          (subsingleton_moduleExtInto_of_ne_zero_of_isFiniteLength hNfl K hK (-1) (by norm_num))
          (subsingleton_moduleExtInto_of_ne_zero_of_isFiniteLength hQuot K hK 1 (by norm_num))
      have hQuotNontrivial : Nontrivial (M ⧸ N) := IsSimpleModule.nontrivial A (M ⧸ N)
      have hone : 1 ≤ Module.length A (moduleExtInto (M ⧸ N) K 0) :=
        Order.one_le_iff_pos.mpr (Module.length_pos_iff.mpr
          (nontrivial_moduleExtInto_zero_of_isFiniteLength hQuot K hK))
      rw [hMlen, hElen, add_comm]
      exact add_le_add hone ih

/-- **The dual of a module of finite length has finite length.** For a module `Q` of finite
length over a Noetherian local ring with normalized dualizing complex `ω`, every one of the
modules `Ext_A^j(Q, ω)` has finite length.

Outside degree zero the module vanishes, the dual Ext of a module of finite length being
concentrated in degree zero. In degree zero it is a finite module, by part (1) of
[Stacks, Tag 0DWZ], and an element annihilating `Q` annihilates `Ext_A^0(Q, ω)` as well, so the
support of the latter is contained in the support of `Q`; that support is contained in the closed
point, and a finite module supported at the closed point has finite length. -/
theorem isFiniteLength_moduleExtInto_of_isFiniteLength {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {Q : Type u} [AddCommGroup Q] [Module A Q]
    (hQ : IsFiniteLength A Q) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K) (j : ℤ) :
    IsFiniteLength A (moduleExtInto Q K j) := by
  rcases eq_or_ne j 0 with rfl | hj
  · let : IsNoetherian A Q := (isFiniteLength_iff_isNoetherian_isArtinian.mp hQ).1
    let : Module.Finite A Q := inferInstance
    let : Module.Finite A (moduleExtInto Q K 0) := by
      simpa using moduleExtInto_finite (A := A) (M := Q) K hK 0
    exact isFiniteLength_of_support_subset
      ((support_subset_of_ext_zero (A := A) (M := Q) K).trans
        (support_subset_of_finiteLength Q hQ))
  · let : Subsingleton (moduleExtInto Q K j) :=
      subsingleton_moduleExtInto_of_ne_zero_of_isFiniteLength hQ K hK j hj
    exact IsFiniteLength.of_subsingleton

end Dualizing

end
