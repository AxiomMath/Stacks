module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.ZMod.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ProductOfStructureSheavesNotQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ProductStructureSheafNotLocallyQuasicoherent

/-!
# The base of the counterexample of Stacks 07DD on the scheme `Spec k[x]`

The discussion of **Stacks 07DC**, which proves **Stacks 07DD**, ends with the observation that a
countable product of copies of `𝒪_S`, `S = Spec k[x]`, is not quasi-coherent. This file records
that observation for modules on the scheme `S` (the Zariski site), together with the fact that
quasi-coherent modules on `Spec k[x]` are therefore not closed under countable products.

**Stacks 07DD** itself — a quasi-compact quasi-separated morphism of algebraic stacks need not
send `D_{LQCoh^fbc}` into `D_{LQCoh^fbc}` under `Rf_*` — is proved, with the source's own
counterexample at `p = 2`, as
`not_forall_derivedPushforward_mem_derivedLocallyQuasicoherentFlatBaseChange` (in this namespace)
in `StacksFrontier/AlgebraicGeometry/Stacks/Examples/UnboundedDerivedPushforwardCounterexample.lean`.
The big-site form of the obstruction used there is
`AlgebraicGeometry.Stack.not_mem_locallyQuasicoherentFlatBaseChange_of_iso_pi`.

## Main results

* `Stacks.Examples.UnboundedDerivedPushforward.not_isQuasicoherent_piStructureSheaf_polynomial`:
  the countable product `∏_{m ≥ 0} 𝒪_{Spec k[x]}` is not quasi-coherent when `k` is nontrivial.
* `Stacks.Examples.UnboundedDerivedPushforward.not_isQuasicoherent_piStructureSheaf_zmod`: the
  case `k = ℤ/pℤ`, `p` prime.
* `Stacks.Examples.UnboundedDerivedPushforward.not_forall_isQuasicoherent_pi`: quasi-coherent
  modules on `Spec k[x]` are not closed under countable products.
* `Stacks.Examples.UnboundedDerivedPushforward.not_isQuasicoherent_of_iso_piStructureSheaf`:
  a module on `Spec k[x]` isomorphic to that countable product is not quasi-coherent.

## References

* [Stacks Project, Tag 07DD](https://stacks.math.columbia.edu/tag/07DD)
* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Examples.UnboundedDerivedPushforward

universe u

/-! ### The base of the counterexample -/

/-- **A countable product of copies of the structure sheaf of `Spec k[x]` is not
quasi-coherent.**  This is the sheaf the discussion of **Stacks 07DC** produces as the
degree-zero cohomology sheaf of `Rf_*E`, over the base `S = Spec k[x]` of its own
counterexample, and its failure to be quasi-coherent is the whole point of the example.

The argument is `Stacks.Duality.not_isQuasicoherent_piStructureSheaf`: a quasi-coherent module
on an affine has localizing sections, so a section over `D(x)` is a global section divided by a
*single* power of `x`, while the product has a section over `D(x)` whose `n`-th coordinate is
`1/x^n`.  The hypothesis that ring element admits no equation `t^j = t^{j+1} b` holds for
`t = x` in `k[x]` as soon as `k` is nontrivial. -/
public theorem not_isQuasicoherent_piStructureSheaf_polynomial (k : Type u) [CommRing k]
    [Nontrivial k] :
    ¬ (∏ᶜ (fun _ : ℕ => SheafOfModules.unit
      (Spec (CommRingCat.of (Polynomial k))).ringCatSheaf)).IsQuasicoherent :=
  Stacks.Duality.not_isQuasicoherent_piStructureSheaf (CommRingCat.of (Polynomial k))
    Polynomial.X fun j b => Polynomial.pow_X_mul_one_sub_mul_ne_zero j b

/-- The source's literal base ring: for `p` prime, `k = ℤ/pℤ` has characteristic `p`, so the
whole discussion of **Stacks 07DC** applies to it, and the countable product
`∏_{m ≥ 0} 𝒪_{Spec 𝔽_p[x]}` is not quasi-coherent. -/
public theorem not_isQuasicoherent_piStructureSheaf_zmod (p : ℕ) [Fact p.Prime] :
    ¬ (∏ᶜ (fun _ : ℕ => SheafOfModules.unit
      (Spec (CommRingCat.of (Polynomial (ZMod p)))).ringCatSheaf)).IsQuasicoherent :=
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  not_isQuasicoherent_piStructureSheaf_polynomial (ZMod p)

/-! ### The obstruction: `D_QCoh` misses the products of its own objects -/

/-- **The quasi-coherent modules on `Spec k[x]` are not closed under countable products.**  The
witness is the constant family `𝒪_{Spec k[x]}`, every member of which is quasi-coherent, while
its product is not.

This is the obstruction the discussion of **Stacks 07DC** exploits.  The derived pushforward,
being a right derived functor, commutes with products, and the counterexample's `E` is a
countable product in `D_QCoh(𝒪_𝒳)` by **Stacks 08IZ**; the product of the resulting family
formed in `D(𝒪_S)` then leaves `D_QCoh(𝒪_S)`, already in degree zero.  Boundedness is what
rules this out in **Stacks 07BC**: a product of a family bounded below *uniformly* is again
bounded below, and the counterexample's family is not. -/
public theorem not_forall_isQuasicoherent_pi (k : Type u) [CommRing k] [Nontrivial k] :
    ¬ ∀ M : ℕ → (Spec (CommRingCat.of (Polynomial k))).Modules,
      (∀ n, (M n).IsQuasicoherent) → (∏ᶜ M).IsQuasicoherent := by
  intro hclosed
  refine not_isQuasicoherent_piStructureSheaf_polynomial k (hclosed _ fun _ => ?_)
  exact (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance

/-- A module on `Spec k[x]` isomorphic to the countable product `∏_{m ≥ 0} 𝒪_{Spec k[x]}` is
not quasi-coherent: non-quasi-coherence of the product
(`not_isQuasicoherent_piStructureSheaf_polynomial`) transported along the isomorphism `hH`.

This is the last step of the discussion of **Stacks 07DC**, where the module is the
degree-zero cohomology sheaf of `Rf_*E`.  **Stacks 07DD** itself is proved, with no such
hypothesis, as `not_forall_derivedPushforward_mem_derivedLocallyQuasicoherentFlatBaseChange`
in `StacksFrontier/AlgebraicGeometry/Stacks/Examples/UnboundedDerivedPushforwardCounterexample.lean`.
-/
public theorem not_isQuasicoherent_of_iso_piStructureSheaf {k : Type u} [CommRing k]
    [Nontrivial k] (H : (Spec (CommRingCat.of (Polynomial k))).Modules)
    (hH : H ≅ ∏ᶜ (fun _ : ℕ => SheafOfModules.unit
      (Spec (CommRingCat.of (Polynomial k))).ringCatSheaf)) :
    ¬ H.IsQuasicoherent := by
  intro hqc
  have hpi : (∏ᶜ (fun _ : ℕ => SheafOfModules.unit
      (Spec (CommRingCat.of (Polynomial k))).ringCatSheaf)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent
      (Spec (CommRingCat.of (Polynomial k))).ringCatSheaf).prop_of_iso hH hqc
  exact not_isQuasicoherent_piStructureSheaf_polynomial k hpi

end Stacks.Examples.UnboundedDerivedPushforward

end
