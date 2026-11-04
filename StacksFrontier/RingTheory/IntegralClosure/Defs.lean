module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

import StacksCore.Tactic.StacksAttribute

/-!
# Integral elements, integral ring maps and the integral closure

Stacks 00GI defines an element `s : S` to be integral over `R` along a ring map `φ : R →+* S`
when some monic `P : R[X]` has `Polynomial.eval₂ φ s P = 0`, and calls `φ` integral when every
element of `S` is; these are Mathlib's `RingHom.IsIntegralElem` and `RingHom.IsIntegral`
verbatim.

Stacks 00GO records that the integral elements form an `R`-subalgebra of `S`: Mathlib's
`integralClosure`, whose membership is `mem_integralClosure_iff`.

Stacks 00GP names that subalgebra the integral closure of `R` in `S` and calls `R` integrally
closed in `S` when `R → S` is injective with image the whole integral closure. Mathlib's
`IsIntegrallyClosedIn` is that property, unfolded by `isIntegrallyClosedIn_iff` into exactly
injectivity together with every integral element lying in the image.
-/

@[expose] public section

-- The former @[stacks 00GI] definitions are the Mathlib definitions;
-- @[stacks 00GI "(2)"] is already attached to `RingHom.IsIntegral` in Mathlib.
add_to_stacks 00GI "(1)" RingHom.IsIntegralElem

-- The former @[stacks 00GO] theorem is Mathlib's subalgebra of integral elements.
add_to_stacks 00GO "the integral elements form a subalgebra" integralClosure
add_to_sga "3 VIB 5.6.0" integralClosure
add_to_sga "5 VI 1.4.7" integralClosure
add_to_sga "7 X 2.26" integralClosure
add_to_sga "7 XIII 0.2" "partial" integralClosure
add_to_ega "III 4.3.5" "more general" integralClosure
add_to_ega "IV 14.5.5" integralClosure
add_to_ega "IV 18.10.10" "affine case" integralClosure
add_to_ega "IV 18.10.8" "special case" integralClosure
add_to_ega "IV 18.12.14" "partial" integralClosure
add_to_ega "IV 8.12.11" "special case" integralClosure
add_to_ega "IV 9.5.7" integralClosure
add_to_stacks 00GO "its underlying set is the set of integral elements" mem_integralClosure_iff

-- The former @[stacks 00GP] definitions are the Mathlib definitions.
add_to_stacks 00GP "(1)" integralClosure
add_to_stacks 00GP "(2)" IsIntegrallyClosedIn
add_to_stacks 00GP "(2), unfolded" isIntegrallyClosedIn_iff

end
