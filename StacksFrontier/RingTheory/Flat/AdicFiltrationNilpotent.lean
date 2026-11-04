module

public import StacksFrontier.RingTheory.Flat.AdicFiltration
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# Flatness from the adic filtration when the ideal is nilpotent

`Module.flat_quotient_pow_succ_of_flat_quotient_of_exact` (Stacks 0AS8) concludes flatness of
`M/I^{k+1}M` over `R/I^{k+1}`.  When `I^{k+1} = 0` both quotients are the thing itself, so the
conclusion is flatness of `M` over `R` — which is the form an existence argument over an
Artinian local base consumes, the base being `R` and not a quotient of it.

Reading 0AS8 at `I^{k+1} = ⊥` needs a transport, because `R ⧸ ⊥` and `M ⧸ (⊥ • ⊤)` are not `R`
and `M` but are canonically isomorphic to them.  That transport is
`Module.flat_of_flat_quotient_of_eq_bot`, and `Module.flat_of_pow_eq_bot_of_exact` is 0AS8 with
it applied.

## Main results

* `Module.flat_of_flat_quotient_of_eq_bot`: flatness of `M ⧸ (J • ⊤)` over `R ⧸ J` for `J = ⊥`
  is flatness of `M` over `R`.
* `Module.flat_of_pow_eq_bot_of_exact`: **Stacks 0AS8 at a nilpotent ideal.** If `I^{N+1} = ⊥`,
  `M/IM` is flat over `R/I`, and the multiplication map `M ⊗_R I^n/I^{n+1} → I^nM/I^{n+1}M` is
  injective for `n = 1, …, N`, then `M` is flat over `R`.

## Implementation notes

The transport is `Stacks.Flatness.flat_of_ringEquiv` for the pair of canonical quotient maps.
Both are bijective: `Ideal.Quotient.mk ⊥` because its kernel is `⊥`, and `Submodule.mkQ` of
`⊥ • ⊤ = ⊥` for the same reason, `Submodule.bot_smul` identifying the submodule.  The
semilinearity the transport asks for is the defining equation of the `R ⧸ J`-action on
`M ⧸ (J • ⊤)`.

No hypothesis is weakened in passing from 0AS8 to the statement below: `hflat` and `hexact` are
those of 0AS8 verbatim, and `hN` is the extra hypothesis that makes the conclusion about `R` and
`M` rather than about their quotients.

## References

* [Stacks Project, Tag 0AS8](https://stacks.math.columbia.edu/tag/0AS8)
-/

namespace Module

/-- **Flatness over `R ⧸ ⊥` is flatness over `R`.**  For `J = ⊥` the two quotient maps
`R → R ⧸ J` and `M → M ⧸ (J • ⊤)` are bijective, and the second is semilinear over the first, so
`Stacks.Flatness.flat_of_ringEquiv` transports flatness back. -/
public theorem flat_of_flat_quotient_of_eq_bot {R : Type u} [CommRing R] {J : Ideal R}
    (hJ : J = ⊥) (M : Type v) [AddCommGroup M] [Module R M]
    (h : Module.Flat (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))) :
    Module.Flat R M := by
  have := h
  have hsm : J • (⊤ : Submodule R M) = ⊥ := by rw [hJ, Submodule.bot_smul]
  -- `R ⧸ J` is flat over `R`, being `R` itself.
  have : Module.Flat R (R ⧸ J) :=
    Module.Flat.of_linearEquiv (Submodule.quotEquivOfEqBot (J.restrictScalars R) hJ)
  -- hence so is `M ⧸ (J • ⊤)`, flat over `R ⧸ J` by hypothesis.
  have : Module.Flat R (M ⧸ (J • (⊤ : Submodule R M))) :=
    Module.Flat.trans R (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))
  -- and `M ⧸ (J • ⊤)` is `M`.
  exact Module.Flat.of_linearEquiv (Submodule.quotEquivOfEqBot _ hsm).symm

/-- **Stacks 0AS8 at a nilpotent ideal: flatness of `M` itself.**  Let `R` be a ring, `I ⊆ R` an
ideal with `I^{N+1} = 0`, and `M` an `R`-module.  If `M/IM` is flat over `R/I` and the
multiplication map `M ⊗_R I^n/I^{n+1} → I^nM/I^{n+1}M` is injective for `n = 1, …, N`, then `M`
is flat over `R`.

This is `Module.flat_quotient_pow_succ_of_flat_quotient_of_exact` with `k = N`, whose conclusion
`M/I^{N+1}M` flat over `R/I^{N+1}` is flatness of `M` over `R` once `I^{N+1} = ⊥`.  The
injectivity hypothesis is spelled as in 0AS8; see the module docstring there. -/
@[ega "0 10.2.1" "c ⇒ a for nilpotent J"]
public theorem flat_of_pow_eq_bot_of_exact {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (N : ℕ) (hN : I ^ (N + 1) = ⊥)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hexact : ∀ n, 1 ≤ n → n ≤ N →
      Function.Exact
        ((Submodule.inclusion (Ideal.pow_le_pow_right n.le_succ : I ^ (n + 1) ≤ I ^ n)).lTensor M)
        ((I ^ (n + 1) • (⊤ : Submodule R M)).mkQ ∘ₗ
          (TensorProduct.rid R M).toLinearMap ∘ₗ (I ^ n).subtype.lTensor M)) :
    Module.Flat R M :=
  Module.flat_of_flat_quotient_of_eq_bot hN M
    (Module.flat_quotient_pow_succ_of_flat_quotient_of_exact I M N hflat hexact)

end Module

end
