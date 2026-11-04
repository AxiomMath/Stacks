module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericStalkGeneratingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGeneratingOrderZero

/-!
# Local finiteness of the divisor of any regular meromorphic section

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S`, let `ℒ` be
an invertible `𝒪_X`-module and let `t` be any regular meromorphic section of `ℒ`. The prime
divisors `Z` with `ord_{Z,ℒ}(t) ≠ 0`, the order of vanishing read at the canonical ratios `t / t_ξ`
of Stacks 0EPR, are locally finite in `|X|`: this is the second assertion of Stacks 0EPS for `t`.
Each such prime divisor has its generic point outside the generating locus of `t`, the nonempty
open subspace `AlgebraicGeometry.Space.generatingLocus` over which `t` generates `ℒ`.

## Main results

* `AlgebraicGeometry.Space.genericPoint_mem_compl_generatingLocus_of_divisorCoefficients_ne_zero`:
  a prime divisor with `ord_{Z,ℒ}(t) ≠ 0` has its generic point outside the generating locus
  of `t`.
* `AlgebraicGeometry.Space.locallyFinite_canonicalDivisorCoefficients_ne_zero`: **Stacks 0EPS,
  the second set**, for every regular meromorphic section of an invertible module.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
variable (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
variable [∀ W : PrimeDivisor B S hS X,
  Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]

include hInt hN in
/-- **The order of vanishing of a regular meromorphic section is zero on its generating locus.**
A prime divisor `Z` with `ord_{Z,ℒ}(t) ≠ 0`, read at the canonical ratio `t / t_ξ`, has its
generic point outside the open set of points over which `t` generates `ℒ`. -/
theorem genericPoint_mem_compl_generatingLocus_of_divisorCoefficients_ne_zero
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX L t) (W : PrimeDivisor B S hS X)
    (hW : divisorCoefficients.{u, u} B S hS hX hdec L t
      (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN) W ≠ 0) :
    W.genericPoint B S hS X ∈ (generatingLocus B S hS hX L t)ᶜ := by
  rintro ⟨V, hrange, hgen⟩
  obtain ⟨w, hw, hwc⟩ :=
    W.exists_isUnit_eq_algebraMap_genericStalkCoefficient_of_generatesOnChart B S hS hX hdec
      hInt hN L hL t V hrange hgen
  exact hW (orderOfVanishingSection_canonicalLocalRatio_eq_zero_of_coefficient B S hS hX hdec
    hInt hN W L hL t ht hw hwc)

include hInt hN in
/-- **Stacks 0EPS, the second set, for every regular meromorphic section.** For a regular
meromorphic section `t` of an invertible `𝒪_X`-module `ℒ` on a decent, locally Noetherian,
integral algebraic space, the prime divisors `Z` with `ord_{Z,ℒ}(t) ≠ 0` — read at the canonical
ratios `t / t_ξ` of Stacks 0EPR — are locally finite in `|X|`. -/
theorem locallyFinite_canonicalDivisorCoefficients_ne_zero
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX L t) :
    LocallyFinite fun W : PrimeDivisor B S hS X ↦
      if divisorCoefficients.{u, u} B S hS hX hdec L t
          (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN) W = 0 then ∅
      else W.support B S hS X :=
  locallyFinite_divisorCoefficients_ne_zero.{u, u} B S hS hX hdec hN hInt.irreducibleSpace L t
    (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN) (generatingLocus B S hS hX L t)
    (isOpen_generatingLocus B S hS hX L t)
    (nonempty_generatingLocus_of_isRegularMeromorphicSection B S hS hX L
      hInt.hasEtaleLocalProperty_isReduced hInt.irreducibleSpace.toNonempty hL t ht)
    (genericPoint_mem_compl_generatingLocus_of_divisorCoefficients_ne_zero B S hS hX hdec hInt hN
      L hL t ht)

end AlgebraicGeometry.Space

end
