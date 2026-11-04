module

public import StacksFrontier.AlgebraicGeometry.Topologies.FppfCompletedLocalRing

/-!
# The spectrum of an adic completion in a big fppf site

The size cutoff of a big fppf site is closed under adic completion of rings: if `Spec R` is in
the site, then so is the spectrum of the completion of `R` along any ideal. The completion is
the image of a subtype of `ℕ → R`, so its cardinality is at most `#R ^ ℵ₀`
(`AlgebraicGeometry.cardinal_mk_adicCompletion_le`).

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_spec_adicCompletion`
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry

namespace BigFppfSite

variable (B : BigFppfSite.{u})

/-- **The size cutoff of a big fppf site is closed under adic completion of rings.** If
`Spec R` is in the site then so is the spectrum of the completion of `R` along any ideal: the
completion is the image of a subtype of `ℕ → R`, so its cardinality is at most `#R ^ ℵ₀`, which
is at most `size (Spec R) ^ ℵ₀`. -/
theorem contains_spec_adicCompletion {R : Type u} [CommRing R]
    (hR : B.Contains (Spec (.of R))) (I : Ideal R) :
    B.Contains (Spec (.of (AdicCompletion I R))) := by
  refine Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (.of (AdicCompletion I R)) hR ((cardinal_mk_adicCompletion_le I).trans ?_)
  refine Cardinal.power_le_power_right ?_
  rw [Scheme.size_Spec]
  exact le_max_right _ _

end BigFppfSite

end AlgebraicGeometry

end
