module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Kaehler.Basic

import StacksCore.Tactic.EgaSgaAttribute
import StacksCore.Tactic.StacksAttribute

/-!
# Derivations and the module of differentials

Stacks 00RN defines an `R`-derivation of `S` into an `S`-module `M`, for a ring map
`φ : R → S`, as an additive map killing `φ(R)` and satisfying the Leibniz rule; as the Stacks
text itself notes, this is the same as an `R`-linear map satisfying Leibniz, which is Mathlib's
`Derivation`.

Stacks 07BK names the pair `(Ω_{S/R}, d)`: Mathlib's `KaehlerDifferential` and
`KaehlerDifferential.D`. Stacks 00RO is its universal property, `α ↦ α ∘ d` being an
isomorphism `Hom_S(Ω_{S/R}, M) ≃ Der_R(S, M)` — Mathlib's
`KaehlerDifferential.linearMapEquivDerivation`, whose formula is
`KaehlerDifferential.linearMapEquivDerivation_apply_apply`.

Stacks 00RW is the canonical isomorphism `Ω_{S/R} ≃ J/J²` for `J` the kernel of
`S ⊗[R] S → S`, sending `a d b` to `a ⊗ b - ab ⊗ 1`. Mathlib *defines*
`KaehlerDifferential R S` to be `(KaehlerDifferential.ideal R S).Cotangent`, so the
isomorphism is the identity, and `KaehlerDifferential.D_apply` is the displayed formula.
-/

@[expose] public section

-- The former @[stacks_fixed 00RN] structure is the Mathlib structure.
add_to_stacks 00RN "derivations" Derivation
add_to_sga "3 VIIA 1.2.0" "special case" Derivation
add_to_sga "3 VIIA 5.2" "special case" Derivation
add_to_sga "7 X 2.26" Derivation
add_to_ega "0 20.1.1" "special case" Derivation
add_to_ega "0 20.1.2" "commutative, 1-sided mod" Derivation
add_to_stacks 00RN "the constructor" Derivation.mk
add_to_ega "0 20.1.2" "commutative, 1-sided mod" Derivation.mk
add_to_stacks 00RN "annihilates the image of the base ring map" Derivation.map_algebraMap
add_to_ega "0 20.1.2" "vanishes on image of A" Derivation.map_algebraMap
add_to_stacks 00RN "the Leibniz rule" Derivation.leibniz
add_to_ega "0 20.1.2" "Leibniz rule (ii)" Derivation.leibniz

-- The former @[stacks_fixed 07BK] structure and definition are the Mathlib definitions.
add_to_stacks 07BK "the module of differentials" KaehlerDifferential
add_to_sga "1 II 5.7" KaehlerDifferential
add_to_sga "1 II 5.9" KaehlerDifferential
add_to_sga "6 0 2.1" "special case" KaehlerDifferential
add_to_sga "6 VIII 2.2" KaehlerDifferential
add_to_sga "6 VIII 2.4" KaehlerDifferential
add_to_sga "7 VI 1.17" "Ω when K is a field" KaehlerDifferential
add_to_sga "7 VI 5.1" "special case" KaehlerDifferential
add_to_sga "7 VI 5.5" "special case" KaehlerDifferential
add_to_ega "0 20.4.3" "special case" KaehlerDifferential
add_to_ega "IV 16.3.1" "affine Ω¹_{X/S}" KaehlerDifferential
add_to_ega "IV 16.3.7" KaehlerDifferential
add_to_ega "IV 17.13.5" "Affine case" KaehlerDifferential
add_to_ega "IV 17.15.8" KaehlerDifferential
add_to_stacks 07BK "its universal derivation" KaehlerDifferential.D
add_to_sga "7 VI 1.17" "d, special case" KaehlerDifferential.D
add_to_ega "0 20.4.8" "(ii), derivation clause" KaehlerDifferential.D
add_to_ega "IV 16.3.6" "special case" KaehlerDifferential.D
add_to_ega "IV 16.5.3" "(i), affine case" KaehlerDifferential.D

-- The former @[stacks 00RO] theorem is the Mathlib equivalence.
add_to_stacks 00RO KaehlerDifferential.linearMapEquivDerivation
add_to_sga "1 III 5.2" "special case" KaehlerDifferential.linearMapEquivDerivation
add_to_sga "3 VIIA 1.3.1" "special case" KaehlerDifferential.linearMapEquivDerivation
add_to_ega "IV 16.5.14" "partial" KaehlerDifferential.linearMapEquivDerivation
add_to_ega "IV 16.5.7" "special case" KaehlerDifferential.linearMapEquivDerivation
add_to_ega "IV 16.5.3" "(ii), affine case" KaehlerDifferential.linearMapEquivDerivation
add_to_sga "3 II 3.14" "affine case" KaehlerDifferential.linearMapEquivDerivation
add_to_stacks 00RO "the map is `α ↦ α ∘ d`"
  KaehlerDifferential.linearMapEquivDerivation_apply_apply
add_to_ega "0 20.4.8" "(ii), discrete case"
  KaehlerDifferential.linearMapEquivDerivation
add_to_ega "IV 16.5.3" "(ii), affine/ring case" KaehlerDifferential.linearMapEquivDerivation

-- The former @[stacks 00RW] declarations are Mathlib's definition of `Ω[S⁄R]` as `J / J ^ 2`.
add_to_stacks 00RW "`Ω[S⁄R]` is `J / J ^ 2`" KaehlerDifferential
add_to_stacks 00RW "the ideal `J`" KaehlerDifferential.ideal
add_to_sga "3 VIIA 1.4.1" "special case" KaehlerDifferential.ideal
add_to_ega "0 20.4.1" KaehlerDifferential.ideal
add_to_stacks 00RW "`d b = 1 ⊗ b - b ⊗ 1`" KaehlerDifferential.D_apply
add_to_ega "IV 16.3.6" "special case" KaehlerDifferential.D_apply

end
