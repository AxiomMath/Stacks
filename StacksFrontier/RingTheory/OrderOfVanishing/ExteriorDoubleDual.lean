module

public import StacksFrontier.Algebra.Module.DoubleDualTorsionQuotient
public import StacksFrontier.RingTheory.OrderOfVanishing.ExteriorTorsionQuotient

/-!
# The double transpose of an exterior power of a surjection with torsion kernel

Over a discrete valuation ring, let `u : M → M'` be a surjection of finite modules whose kernel
consists of torsion elements — equivalently, a map that becomes an isomorphism over the fraction
field. Then `⋀^r u` is again such a surjection, and so its double transpose
`(⋀^r M)^** → (⋀^r M')^**` is bijective.

This is the step of [Stacks, Tag 0B3T] that says the comparison map of determinant line bundles
is an isomorphism away from the divisor. There `M` and `M'` are the stalks of the two coherent
modules of the tag's right exact sequence at a point off the divisor, where the quotient
vanishes, so `u` is onto; and they have the same rank at the generic point of the ambient
integral scheme — this is assumption (1) of the tag, that both are locally free of rank `r` on a
nonempty open — so the kernel of `u` is torsion.

The torsion hypothesis cannot be dropped: over a two-dimensional regular local ring the double
transpose of `R ^ 2 ↠ (x, y)` has image `(x, y)`, and that kernel is free of rank one.

## Main results

* `Stacks.OrderOfVanishing.bijective_torsionQuotientMap_of_surjective_of_ker_le_torsion`: such a
  surjection is a bijection on torsion-free quotients.
* `Stacks.OrderOfVanishing.bijective_torsionQuotientMap_exteriorPower_map`: so is its `r`-th
  exterior power.
* `Stacks.OrderOfVanishing.bijective_dualMap_dualMap_exteriorPower_map`: **the double transpose
  of `⋀^r u` is bijective.**

## Implementation notes

The exterior power is handled on torsion-free quotients rather than on kernels: the square
`Stacks.OrderOfVanishing.torsionQuotientEquiv_torsionQuotientMap` carries
`torsionQuotientMap (⋀^r u)` to `⋀^r (torsionQuotientMap u)`, and a bijection on torsion-free
quotients is the same information as a torsion kernel together with surjectivity. This avoids
computing the kernel of `⋀^r u`, which is not in the library.

**No `@[stacks]` attribute.** This is a step of the proof of Tag 0B3T, not one of its assertions.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

namespace Stacks.OrderOfVanishing

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- A map whose kernel is torsion is injective on torsion-free quotients. -/
public theorem injective_torsionQuotientMap_of_ker_le_torsion {u : M →ₗ[A] M'}
    (hker : LinearMap.ker u ≤ Submodule.torsion A M) :
    Function.Injective (torsionQuotientMap u) := by
  refine (injective_iff_map_eq_zero _).mpr fun q hq => ?_
  induction q using Submodule.Quotient.induction_on with
  | H m =>
    have hum : u m ∈ Submodule.torsion A M' :=
      (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨a, ha⟩ := hum
    have ha' : (a : A) • u m = 0 := ha
    have hak : (a : A) • m ∈ LinearMap.ker u := by
      simpa only [LinearMap.mem_ker, map_smul] using ha'
    obtain ⟨b, hb⟩ := hker hak
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨b * a, by rw [mul_smul]; exact hb⟩

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- A map that is injective on torsion-free quotients has torsion kernel. -/
public theorem ker_le_torsion_of_injective_torsionQuotientMap {u : M →ₗ[A] M'}
    (h : Function.Injective (torsionQuotientMap u)) :
    LinearMap.ker u ≤ Submodule.torsion A M := fun m hm =>
  (Submodule.Quotient.mk_eq_zero _).mp (h (by
    change (Submodule.Quotient.mk (u m) : M' ⧸ Submodule.torsion A M')
      = torsionQuotientMap u 0
    rw [LinearMap.mem_ker.mp hm, map_zero, Submodule.Quotient.mk_zero]))

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- **A surjection whose kernel is torsion is a bijection on torsion-free quotients.** -/
public theorem bijective_torsionQuotientMap_of_surjective_of_ker_le_torsion {u : M →ₗ[A] M'}
    (hu : Function.Surjective u) (hker : LinearMap.ker u ≤ Submodule.torsion A M) :
    Function.Bijective (torsionQuotientMap u) := by
  refine ⟨injective_torsionQuotientMap_of_ker_le_torsion hker, fun q => ?_⟩
  induction q using Submodule.Quotient.induction_on with
  | H m' =>
    obtain ⟨m, rfl⟩ := hu m'
    exact ⟨Submodule.Quotient.mk m, rfl⟩

variable [Module.Finite A M] [Module.Finite A M']

/-- **The exterior power of a surjection with torsion kernel is again a bijection on
torsion-free quotients**, by the naturality of `(⋀^r M) ⧸ tors ≃ ⋀^r (M ⧸ tors)`. -/
public theorem bijective_torsionQuotientMap_exteriorPower_map (r : ℕ) {u : M →ₗ[A] M'}
    (hu : Function.Surjective u) (hker : LinearMap.ker u ≤ Submodule.torsion A M) :
    Function.Bijective (torsionQuotientMap (exteriorPower.map r u)) := by
  have hq := bijective_torsionQuotientMap_of_surjective_of_ker_le_torsion hu hker
  have hE : Function.Bijective (exteriorPower.map r (torsionQuotientMap u)) :=
    ⟨exteriorPower.map_injective (LinearEquiv.ofBijective _ hq).symm (by ext; simp),
      exteriorPower.map_surjective hq.2⟩
  refine ⟨fun q q' h => ?_, fun y => ?_⟩
  · have hc := congrArg (exteriorPower.torsionQuotientEquiv (A := A) (r := r) (M := M')) h
    rw [torsionQuotientEquiv_torsionQuotientMap, torsionQuotientEquiv_torsionQuotientMap] at hc
    exact exteriorPower.torsionQuotientEquiv.injective (hE.1 hc)
  · obtain ⟨x, hx⟩ := hE.2 (exteriorPower.torsionQuotientEquiv y)
    refine ⟨exteriorPower.torsionQuotientEquiv.symm x, ?_⟩
    refine exteriorPower.torsionQuotientEquiv.injective ?_
    rw [torsionQuotientEquiv_torsionQuotientMap, LinearEquiv.apply_symm_apply, hx]

/-- **The double transpose of `⋀^r` of a surjection whose kernel is torsion is bijective.**
This is the comparison map of determinant modules of [Stacks, Tag 0B3T] away from the divisor,
where the map of the tag's sequence is onto and the two modules have the same generic rank. -/
public theorem bijective_dualMap_dualMap_exteriorPower_map (r : ℕ) {u : M →ₗ[A] M'}
    (hu : Function.Surjective u) (hker : LinearMap.ker u ≤ Submodule.torsion A M) :
    Function.Bijective (exteriorPower.map r u).dualMap.dualMap :=
  bijective_dualMap_dualMap_of_surjective_of_ker_le_torsion
    (exteriorPower.map_surjective hu)
    (ker_le_torsion_of_injective_torsionQuotientMap
      (bijective_torsionQuotientMap_exteriorPower_map r hu hker).1)

end Stacks.OrderOfVanishing

end
