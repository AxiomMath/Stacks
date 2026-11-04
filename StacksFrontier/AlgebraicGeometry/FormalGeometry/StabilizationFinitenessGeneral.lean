module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationFiniteness
import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle

/-!
# Finiteness of local cohomology at every stabilizing ideal

Let `I` and `J` be ideals of a Noetherian ring `A` with a dualizing complex, let `M` be a finite
`A`-module and let `s` be an integer. Stacks 0EFI produces an ideal `J₀ ⊆ J` with
`V(J₀) ∩ V(I) = V(J) ∩ V(I)` such that every further `J' ⊆ J₀` with the same trace on `V(I)`
has `RΓ_{J₀}(M) → RΓ_{J'}(M)` an isomorphism in degrees `≤ s`, and such that these modules are
annihilated by a power of `J₀ I`; this conclusion, for a pair `(J₀, n)`, is
`Stacks.Algebraization.IsStabilizingData`. Stacks 0EFJ adds hypothesis (2'),
`Stacks.Algebraization.DepthAddDimGtOnZeroLocus`, and concludes that `H^i_{J₀}(M)` is a finite
`A`-module for `i ≤ s`.

## Main results

* `Stacks.Algebraization.IsStabilizingData.finite_localCohomologyModule` — **Stacks 0EFJ**, for
  every ideal `J₀` with the conclusion of Stacks 0EFI.

## Implementation notes

The statement is made for an arbitrary pair `(J₀, n)` with the conclusion of Stacks 0EFI rather
than for one constructed ideal, which is how the source reads: "the conditions also imply that
`H^i_{J₀}(M)` is finite" refers to any `J₀` as in Stacks 0EFI. Of the hypotheses of Stacks 0EFI
only (1), the dualizing complex, is used; (3) and (4) serve to produce `J₀`, and are not needed
once `J₀` is given. For the ideal `Stacks.Algebraization.stabilizingIdeal` constructed in this
library, the existence of such a pair is `Stacks.Algebraization.exists_isStabilizingData`, under
(1)–(4) and `0 ≤ d`. For `d < 0` a pair need not exist (Stacks 0EFI fails there, the source
reading `depth + dim > d + s` as `depth + dim > s` in its last step), so the theorem below is then
vacuous rather than false.

The proof is `Stacks.Algebraization.finite_localCohomologyModule_of_exists_pow_mul_le_annihilator`
(Faltings' finiteness criterion Stacks 0EFD for `V(J₀)`, with the depth inequality off `V(I)`
obtained from Faltings' annihilator theorem Stacks 0EFC), fed with the annihilation clause of the
stabilizing data read at `J' = J₀`. That lemma assumes `0 ≤ s`, as Stacks 0EFC and Stacks 0EFD do;
for `s < 0` the modules `H^i_{J₀}(M)` with `i ≤ s` vanish, so no such hypothesis remains.

The comparison morphisms in `Stacks.Algebraization.IsStabilizingData` live in the standard model
of the derived category, so the dualizing complex is taken there too, as in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationFiniteness`; the model is named in the
binders rather than installed as a local instance.

## References

* [Stacks Project, Tag 0EFJ](https://stacks.math.columbia.edu/tag/0EFJ)
* [Stacks Project, Tag 0EFI](https://stacks.math.columbia.edu/tag/0EFI)
* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)

## Tags

local cohomology, depth, finiteness, algebraization
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.LocalCohomology

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **Stacks 0EFJ.** Let `A` be a Noetherian ring with a dualizing complex `omega`, let `I`, `J`
be ideals, `M` a finite `A`-module and `s` an integer, and assume hypothesis (2'): for
`𝔭 ∈ V(I)` outside `V(J) ∩ V(I)`, `depth(M_𝔭) + dim((A/𝔭)_𝔮) > s` for every
`𝔮 ∈ V(𝔭) ∩ V(J) ∩ V(I)`. Then for every ideal `J₀` with the conclusion of Stacks 0EFI —
`J₀ ⊆ J`, `V(J₀) ∩ V(I) = V(J) ∩ V(I)`, stability of `H^i_{J'}(M)` for `i ≤ s` under further
shrinking `J' ⊆ J₀` with the same trace on `V(I)`, and annihilation of these modules by
`(J₀ I) ^ n` — the module `H^i_{J₀}(M)` is finite for every `i ≤ s`.

Hypotheses (3) and (4) of Stacks 0EFI are not needed here: they enter only in producing `J₀`.
No pair `(J₀, n)` need exist when `d < 0`, where Stacks 0EFI fails; there the statement is
vacuous. -/
@[stacks 0EFJ "H^i_{J₀}(M) is a finite A-module for i ≤ s, for every ideal J₀ with the \
  conclusions of 0EFI"]
public theorem IsStabilizingData.finite_localCohomologyModule {I J J₀ : Ideal A} {s : ℤ}
    {n : ℕ} (hJ₀ : IsStabilizingData (M := M) I J s (J₀, n))
    (omega : letI := HasDerivedCategory.standard (ModuleCat.{u} A)
      DerivedCategory (ModuleCat.{u} A))
    (homega : letI := HasDerivedCategory.standard (ModuleCat.{u} A)
      Dualizing.IsDualizingComplex (A := A) (K := omega))
    (h2 : DepthAddDimGtOnZeroLocus (M := M) I J s) (i : ℤ) (hi : i ≤ s) :
    Module.Finite A
      (localCohomologyModule A J₀ J₀.fg_of_isNoetherianRing (ModuleCat.of A M) i) := by
  by_cases hs : 0 ≤ s
  · exact finite_localCohomologyModule_of_exists_pow_mul_le_annihilator I J J₀ s hs omega
      homega hJ₀.zeroLocus_inter h2
      ⟨n, fun k hk ↦ hJ₀.pow_mul_le_annihilator J₀ le_rfl hJ₀.zeroLocus_inter k hk⟩ i hi
  · have : Subsingleton
        (localCohomologyModule A J₀ J₀.fg_of_isNoetherianRing (ModuleCat.of A M) i) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (isZero_localCohomologyModule_of_neg A J₀ J₀.fg_of_isNoetherianRing
          (ModuleCat.of A M) i (hi.trans_lt (not_le.mp hs)))
    have : Finite
        (localCohomologyModule A J₀ J₀.fg_of_isNoetherianRing (ModuleCat.of A M) i) :=
      Finite.of_subsingleton
    infer_instance

end Stacks.Algebraization

end
