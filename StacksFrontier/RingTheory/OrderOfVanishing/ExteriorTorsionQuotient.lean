module

public import StacksFrontier.LinearAlgebra.ExteriorPower.TorsionQuotient
public import StacksFrontier.RingTheory.OrderOfVanishing.ExteriorDeterminant

/-!
# The determinant bound on the torsion-free quotient of an exterior power

`StacksFrontier.RingTheory.OrderOfVanishing.ExteriorDeterminant` bounds the length of the cokernel
of `⋀^r` of the induced map on torsion-free quotients, an object built from `⋀^r (M ⧸ tors)`.
The stalk computation of [Stacks, Tag 0B3T] instead produces `(⋀^r M) ⧸ tors`. This file carries
the bound across `exteriorPower.torsionQuotientEquiv`, which identifies the two.

## Main results

* `Stacks.OrderOfVanishing.torsionQuotientEquiv_torsionQuotientMap`: the identification is
  natural — it carries the map induced by `⋀^r f` to `⋀^r` of the map induced by `f`.
* `Stacks.OrderOfVanishing.length_quotient_range_torsionQuotientMap_exteriorPower_le_min_of_finrank`
  : **the determinant bound, stated on `(⋀^r M) ⧸ tors`.**

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public section

namespace Stacks.OrderOfVanishing

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {r s : ℕ} {M M' : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
  [AddCommGroup M'] [Module A M'] [Module.Finite A M'] (f : M →ₗ[A] M')

/-- **The identification of `(⋀^r M) ⧸ tors` with `⋀^r (M ⧸ tors)` is natural**: it carries the
map induced by `⋀^r f` to `⋀^r` of the map induced by `f`. -/
public theorem torsionQuotientEquiv_torsionQuotientMap
    (q : ⋀[A]^r M ⧸ Submodule.torsion A (⋀[A]^r M)) :
    exteriorPower.torsionQuotientEquiv (torsionQuotientMap (exteriorPower.map r f) q)
      = exteriorPower.map r (torsionQuotientMap f) (exteriorPower.torsionQuotientEquiv q) := by
  have hcomp : (Submodule.torsion A M').mkQ ∘ₗ f
      = torsionQuotientMap f ∘ₗ (Submodule.torsion A M).mkQ := LinearMap.ext fun _ => rfl
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    have hL : torsionQuotientMap (exteriorPower.map r f)
          (Submodule.Quotient.mk x : ⋀[A]^r M ⧸ Submodule.torsion A (⋀[A]^r M))
        = (Submodule.Quotient.mk (exteriorPower.map r f x) :
            ⋀[A]^r M' ⧸ Submodule.torsion A (⋀[A]^r M')) := rfl
    rw [hL, exteriorPower.torsionQuotientEquiv_mk, exteriorPower.torsionQuotientEquiv_mk,
      ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← exteriorPower.map_comp,
      ← exteriorPower.map_comp, hcomp]

/-- The identification carries the range of the map induced by `⋀^r f` onto the range of `⋀^r`
of the map induced by `f`. -/
public theorem map_range_torsionQuotientMap_exteriorPower :
    Submodule.map (exteriorPower.torsionQuotientEquiv (A := A) (r := r) (M := M') :
        (⋀[A]^r M' ⧸ Submodule.torsion A (⋀[A]^r M')) →ₗ[A]
          ⋀[A]^r (M' ⧸ Submodule.torsion A M'))
        (LinearMap.range (torsionQuotientMap (exteriorPower.map r f)))
      = LinearMap.range (exteriorPower.map r (torsionQuotientMap f)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨exteriorPower.torsionQuotientEquiv p, (torsionQuotientEquiv_torsionQuotientMap f p).symm⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨p, rfl⟩ := (exteriorPower.torsionQuotientEquiv
      (A := A) (r := r) (M := M)).surjective y
    exact ⟨torsionQuotientMap (exteriorPower.map r f) p, ⟨p, rfl⟩,
      torsionQuotientEquiv_torsionQuotientMap f p⟩

/-- The two cokernels have the same length. -/
public theorem length_quotient_range_torsionQuotientMap_exteriorPower :
    Module.length A ((⋀[A]^r M' ⧸ Submodule.torsion A (⋀[A]^r M')) ⧸
        LinearMap.range (torsionQuotientMap (exteriorPower.map r f)))
      = Module.length A (⋀[A]^r (M' ⧸ Submodule.torsion A M') ⧸
        LinearMap.range (exteriorPower.map r (torsionQuotientMap f))) :=
  (Submodule.Quotient.equiv _ _ (exteriorPower.torsionQuotientEquiv (A := A) (r := r) (M := M'))
    (map_range_torsionQuotientMap_exteriorPower f)).length_eq

/-- **The determinant bound on the torsion-free quotient of the exterior power.** For
`M → M' → N → 0` exact with `N ≅ κ^⊕ s` and torsion-free quotients of rank `r`, the cokernel of
the map induced by `⋀^r f` has length at most `min s r`. -/
public theorem length_quotient_range_torsionQuotientMap_exteriorPower_le_min_of_finrank
    (e : (M' ⧸ LinearMap.range f) ≃ₗ[A] (Fin s → IsLocalRing.ResidueField A))
    (hr : Module.finrank A (M ⧸ Submodule.torsion A M) = r)
    (hr' : Module.finrank A (M' ⧸ Submodule.torsion A M') = r) :
    Module.length A ((⋀[A]^r M' ⧸ Submodule.torsion A (⋀[A]^r M')) ⧸
        LinearMap.range (torsionQuotientMap (exteriorPower.map r f))) ≤ (min s r : ℕ) := by
  rw [length_quotient_range_torsionQuotientMap_exteriorPower f]
  exact length_quotient_range_exteriorPower_torsionQuotientMap_le_min_of_finrank f e hr hr'

end Stacks.OrderOfVanishing

end
