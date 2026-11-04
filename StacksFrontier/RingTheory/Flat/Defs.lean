module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import StacksCore.Tactic.StacksAttribute

/-!
# Flat and faithfully flat modules and ring maps

Mathlib already states all four parts of Stacks 00HB.

An `R`-module is flat when `M ⊗[R] -` carries exact sequences to exact sequences: this is
`Module.Flat`, with `Module.Flat.iff_lTensor_exact` the exactness form the tag uses. It is
faithfully flat when `M ⊗[R] -` both preserves and reflects exactness: this is
`Module.FaithfullyFlat`, with `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact` the
corresponding form. A ring map is flat, resp. faithfully flat, when its target is so as a
module over its source: `RingHom.Flat` and `RingHom.FaithfullyFlat`, the latter already
carrying part (4) of the tag upstream.
-/

@[expose] public section

add_to_stacks 00HB "(1)" Module.Flat
add_to_stacks 00HB "(1), as the exactness condition the tag states"
  Module.Flat.iff_lTensor_exact
add_to_sga "4 V 1.1" "special case" Module.Flat.iff_lTensor_exact
add_to_sga "4 V 1.7.2" "(i) ⇔ (ii), special case" Module.Flat.iff_lTensor_exact
add_to_sga "4½ Etat_0 6.2" "special case" Module.Flat.iff_lTensor_exact
add_to_sga "6 0 2.9" "affine case" Module.Flat.iff_lTensor_exact
add_to_sga "7 VII 3.7.6" "partial" Module.Flat.iff_lTensor_exact
add_to_ega "0 6.1.1" Module.Flat.iff_lTensor_exact
add_to_ega "0 6.4.1" "a)" Module.Flat.iff_lTensor_exact
add_to_ega "III 6.1.1" "special case" Module.Flat.iff_lTensor_exact
add_to_ega "IV 2.2.7" "partial" Module.Flat.iff_lTensor_exact
add_to_stacks 00HB "(2)" Module.FaithfullyFlat
add_to_sga "1 IV 2.1" Module.FaithfullyFlat
add_to_ega "0 22.4.8" Module.FaithfullyFlat
add_to_ega "0 6.4.1" Module.FaithfullyFlat
add_to_ega "0 6.6.1" Module.FaithfullyFlat
add_to_ega "IV 2.2.4" "special case" Module.FaithfullyFlat
add_to_stacks 00HB "(2), as the exactness condition the tag states"
  Module.FaithfullyFlat.iff_exact_iff_lTensor_exact
add_to_sga "1 IV 2.1" Module.FaithfullyFlat.iff_exact_iff_lTensor_exact
add_to_sga "1 IV 2.6" "(i)⇒(iv)" Module.FaithfullyFlat.iff_exact_iff_lTensor_exact
add_to_sga "4½ Arcata 1.4.2" "Clause (i), special case"
  Module.FaithfullyFlat.iff_exact_iff_lTensor_exact
add_to_ega "0 6.6.1" "more general" Module.FaithfullyFlat.iff_exact_iff_lTensor_exact
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.iff_exact_iff_lTensor_exact
add_to_ega "0 6.4.1" "(a) <=> (d)" Module.FaithfullyFlat.iff_exact_iff_lTensor_exact
add_to_stacks 00HB "(3)" RingHom.Flat
add_to_sga "6 I 3.7" "special case" RingHom.Flat
