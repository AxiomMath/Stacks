module

public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Exactness

/-!
# The symbol of a finite module of dimension one

For a finite module `M` of support dimension one over a Noetherian local ring, and two elements
acting injectively on `M`, the symbol is the periodic determinant of the exact two-periodic
complex on `M / abM` given by multiplication by the two elements.

## Main definitions

* `AlgebraicGeometry.moduleSymbol` is the residue-field unit associated to `M`, `a` and `b`.

## Implementation notes

The quotient `M / abM` is presented as the quotient by the range of the composite
multiplication map. The order of its two differentials is `a` then `b`. The finite-length and
exactness witnesses come from `Module.isFiniteLength_quotient_range_of_injective` and
`AlgebraicGeometry.exact_periodicQuotient_phi_psi`. This definition is exposed so that
downstream symbol identities can rewrite it to the periodic determinant without rebuilding
those witnesses.

## References

* [Stacks Project, Tag 02PZ](https://stacks.math.columbia.edu/tag/02PZ)
-/

@[expose] public section

namespace AlgebraicGeometry

universe u v

/-- **Stacks Project, Tag 02PZ.** The symbol of a finite module of support dimension one,
evaluated on two elements acting injectively on it. -/
@[stacks 02PZ]
noncomputable def moduleSymbol
    {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) : (IsLocalRing.ResidueField A)ˣ := by
  let φ : M →ₗ[A] M := LinearMap.lsmul A M a
  let ψ : M →ₗ[A] M := LinearMap.lsmul A M b
  have hφ : Function.Injective φ := ha
  have hψ : Function.Injective ψ := hb
  have heq : φ ∘ₗ ψ = ψ ∘ₗ φ := by
    ext m
    simp only [φ, ψ, LinearMap.comp_apply, LinearMap.lsmul_apply]
    exact smul_comm a b m
  have hcomm : LinearMap.range (φ ∘ₗ ψ) = LinearMap.range (ψ ∘ₗ φ) :=
    congrArg LinearMap.range heq
  exact periodicDeterminant
    (periodicQuotientPhi φ ψ hcomm)
    (periodicQuotientPsi φ ψ hcomm)
    (exact_periodicQuotient_phi_psi φ ψ hψ hcomm)
    (exact_periodicQuotient_psi_phi φ ψ hφ hcomm)
    (Module.isFiniteLength_quotient_range_of_injective
      (φ ∘ₗ ψ) (hφ.comp hψ) hdim)

end AlgebraicGeometry
