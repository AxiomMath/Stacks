module

public import StacksFrontier.RingTheory.Dualizing.DualExtDepthDimension
public import StacksFrontier.RingTheory.Dualizing.ExtSupportBound

import all StacksFrontier.RingTheory.Dualizing.ExtSupportBound

/-!
# Vanishing ranges for the dual Ext modules

Let `(A, 𝔪)` be a Noetherian local ring with a normalized dualizing complex `ω_A^•`, and let
`M` be a finite `A`-module. The modules

`Eⁱ = Ext_A^{-i}(M, ω_A^•)`

are known to vanish outside the range `depth_𝔪(M) ≤ i ≤ dim Supp(M)`. This file records the
two ends of that range as `Subsingleton` statements, which is the form in which they are
consumed, together with the special case of a module of finite length, whose dual Ext is
concentrated in a single degree.

## Main results

* `Dualizing.subsingleton_moduleExtInto_of_lt_depth` — `Eⁱ = 0` for `i < depth_𝔪(M)`.
* `Dualizing.subsingleton_moduleExtInto_of_lt_depth_bound` — the same vanishing phrased
  against a natural-number lower bound for the depth.
* `Dualizing.subsingleton_moduleExtInto_of_pos` — `Ext_A^j(M, ω_A^•) = 0` for `j > 0`,
  i.e. `Eⁱ = 0` for `i < 0`.
* `Dualizing.subsingleton_moduleExtInto_of_ne_zero_of_isFiniteLength` — for a module of
  finite length, `Ext_A^j(Q, ω_A^•) = 0` for every `j ≠ 0`.

## Implementation notes

Vanishing is stated as `Subsingleton`, the statement that the module has at most one
element; for a module this is the negation of `Nontrivial`, by
`not_nontrivial_iff_subsingleton`. The results of
`StacksFrontier/RingTheory/Dualizing/DualExtDepthDimension.lean` are phrased as consequences
of `Nontrivial`, so each proof here assumes nonvanishing and derives a contradiction.

The degree is spelled `-(i : ℤ)` for the depth statements, matching the indexing
`Eⁱ = Ext_A^{-i}(M, ω_A^•)` by a natural number `i`, and is an unconstrained integer `j`
for the two statements that assert vanishing in positive degrees, where no such indexing
is available.

No nonvanishing hypothesis is needed anywhere: for the zero module every `Eⁱ` vanishes and
all four statements hold trivially. For a module `Q` of finite length the hypothesis
`Module.Finite A Q` is likewise not needed as an argument, being a consequence of
`IsFiniteLength A Q` through `isFiniteLength_iff_isNoetherian_isArtinian`. The bound
`dim Supp(Q) ≤ 0` for such a `Q` is `Dualizing.supportDim_le_zero_of_finiteLength`, which
is `private` in `StacksFrontier/RingTheory/Dualizing/ExtSupportBound.lean` and so is reached
through `import all` rather than restated here.

## References

* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **Vanishing below the depth.** For a finite module `M` over a Noetherian local ring with
normalized dualizing complex `ω`, the module `Eⁱ = Ext_A^{-i}(M, ω)` vanishes for every
`i` strictly below the depth of `M`. Indeed the depth is the least degree of nonvanishing,
so nonvanishing in degree `i` would make the depth at most `i`. -/
theorem subsingleton_moduleExtInto_of_lt_depth {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (i : ℕ) (hi : (i : ℕ∞) < Module.depth A (IsLocalRing.maximalIdeal A) M) :
    Subsingleton (moduleExtInto M K (-(i : ℤ))) := by
  rw [← not_nontrivial_iff_subsingleton]
  intro hne
  rw [depth_eq_iInf_nontrivial_moduleExtInto K hK] at hi
  exact hi.not_ge ((iInf_le _ i).trans (iInf_le _ hne))

/-- **Vanishing below a depth bound.** The packaged form of
`Dualizing.subsingleton_moduleExtInto_of_lt_depth` for a caller holding a natural-number
lower bound `k` for the depth of `M`: then `Eⁱ = Ext_A^{-i}(M, ω)` vanishes for every
`i < k`. -/
theorem subsingleton_moduleExtInto_of_lt_depth_bound {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {M : Type u} [AddCommGroup M] [Module A M]
    [Module.Finite A M] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K) (k : ℕ)
    (hk : (k : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) M) (i : ℕ) (hi : i < k) :
    Subsingleton (moduleExtInto M K (-(i : ℤ))) :=
  subsingleton_moduleExtInto_of_lt_depth K hK i
    (lt_of_lt_of_le (by exact_mod_cast hi) hk)

/-- **Vanishing in positive degree.** For a finite module `M` over a Noetherian local ring
with normalized dualizing complex `ω`, the module `Ext_A^j(M, ω)` vanishes for every `j > 0`;
equivalently `Eⁱ = Ext_A^{-i}(M, ω)` vanishes for `i < 0`. Indeed nonvanishing in degree
`j = -i` forces `0 ≤ i`. -/
theorem subsingleton_moduleExtInto_of_pos {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (j : ℤ) (hj : 0 < j) :
    Subsingleton (moduleExtInto M K j) := by
  rw [← not_nontrivial_iff_subsingleton]
  intro hne
  obtain ⟨d, -, hmem⟩ := moduleExtInto_degree_range K hK (-j) (by rwa [neg_neg])
  exact absurd hmem.1 (by omega)

/-- **A module of finite length has dual Ext concentrated in degree zero.** For a module `Q`
of finite length over a Noetherian local ring with normalized dualizing complex `ω`, the
module `Ext_A^j(Q, ω)` vanishes for every `j ≠ 0`. Positive `j` is the general vanishing
above; for negative `j` the degree range confines nonvanishing to `0 ≤ -j ≤ dim Supp(Q)`,
and the support of a module of finite length has dimension at most zero. -/
theorem subsingleton_moduleExtInto_of_ne_zero_of_isFiniteLength {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {Q : Type u} [AddCommGroup Q] [Module A Q]
    (hQ : IsFiniteLength A Q) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K) (j : ℤ) (hj : j ≠ 0) :
    Subsingleton (moduleExtInto Q K j) := by
  let : IsNoetherian A Q := (isFiniteLength_iff_isNoetherian_isArtinian.mp hQ).1
  let : Module.Finite A Q := inferInstance
  rw [← not_nontrivial_iff_subsingleton]
  intro hne
  obtain ⟨d, hd, hmem⟩ := moduleExtInto_degree_range K hK (-j) (by rwa [neg_neg])
  have hle : (d : WithBot ℕ∞) ≤ 0 := hd ▸ supportDim_le_zero_of_finiteLength Q hQ
  have hd0 : d = 0 := Nat.le_zero.mp (by exact_mod_cast hle)
  rw [hd0] at hmem
  have := hmem.1
  have := hmem.2
  omega

end Dualizing

end
