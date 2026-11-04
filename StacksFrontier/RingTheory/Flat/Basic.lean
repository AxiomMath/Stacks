module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute
import StacksCore.Tactic.StacksAttribute

/-!
# Composition and base change of flat and faithfully flat maps

Mathlib coverage for Stacks chapter 10 (Algebra), section "Flat modules and flat ring maps":
transitivity of (faithful) flatness for ring maps and for modules (00HC), (faithfully) flat
base change (00HI), and descent of flatness along a faithfully flat base change (00HJ). Every
statement is Mathlib's; the tags are attached below.
-/

@[expose] public section

/- Stacks 00HC makes four assertions, all of them Mathlib's: the two composition statements for
ring maps are `RingHom.Flat.comp` and `RingHom.FaithfullyFlat.stableUnderComposition` (the latter
for three rings in one universe, `RingHom.StableUnderComposition` being stated that way), and the
two transitivity statements for modules are `Module.Flat.trans` and
`Module.FaithfullyFlat.trans`. -/
add_to_stacks 00HC "a composition of flat ring maps is flat" RingHom.Flat.comp
add_to_sga "3 VIIB 1.3.3" "(i), special case" RingHom.Flat.comp
add_to_sga "6 III 3.4" "special case" RingHom.Flat.comp
add_to_ega "0 6.7.5" "Affine schemes" RingHom.Flat.comp
add_to_ega "IV 11.3.10.2" "1°, special case" RingHom.Flat.comp
add_to_ega "IV 2.1.6" "special case" RingHom.Flat.comp
add_to_ega "IV 7.3.5" "special case" RingHom.Flat.comp
add_to_ega "0 6.6.4" "flat maps compose" RingHom.Flat.comp
add_to_stacks 00HC "a composition of faithfully flat ring maps is faithfully flat"
  RingHom.FaithfullyFlat.stableUnderComposition
add_to_ega "IV 2.2.13" "(iii)" RingHom.FaithfullyFlat.stableUnderComposition
add_to_ega "0 6.6.4" "ff maps compose" RingHom.FaithfullyFlat.stableUnderComposition
add_to_stacks 00HC "a flat module over a flat algebra is flat over the base" Module.Flat.trans
add_to_sga "1 IV 5.9" "(i)" Module.Flat.trans
add_to_sga "3 VIIB 1.3.3" "(i), special case" Module.Flat.trans
add_to_ega "0 10.2.5" "(a)" Module.Flat.trans
add_to_ega "0 6.2.1" "more general" Module.Flat.trans
add_to_ega "0 6.7.5" "special case" Module.Flat.trans
add_to_ega "IV 11.3.10.2" "1°" Module.Flat.trans
add_to_ega "IV 2.1.5" "special case" Module.Flat.trans
add_to_ega "IV 2.1.6" "special case" Module.Flat.trans
add_to_ega "IV 2.2.11" "(iii), special case" Module.Flat.trans
add_to_ega "IV 7.3.5" "special case" Module.Flat.trans
add_to_ega "0 6.6.4" "necessity, flat case" Module.Flat.trans
add_to_stacks 00HC "a faithfully flat module over a faithfully flat algebra is faithfully flat"
  Module.FaithfullyFlat.trans
add_to_ega "IV 11.3.10.2" "1°, special case" Module.FaithfullyFlat.trans
add_to_ega "IV 2.2.10" "special case" Module.FaithfullyFlat.trans
add_to_ega "IV 2.2.11" "special case" Module.FaithfullyFlat.trans
add_to_ega "IV 2.2.13" "(iii)" Module.FaithfullyFlat.trans
add_to_ega "0 6.6.4" "necessity, ff case" Module.FaithfullyFlat.trans
/- Stacks 00HI, in both of its cases: Mathlib's `Module.Flat.baseChange` for the flat case and
the instance `Module.FaithfullyFlat.instTensorProduct` for the faithfully flat one. The base ring
is written on the left of the tensor product, where the source writes `M ⊗_R R'`. -/
add_to_stacks 00HI "flat base change" Module.Flat.baseChange
add_to_sga "3 III 0.13" "special case" Module.Flat.baseChange
add_to_sga "3 V 7.4" "(i), special case" Module.Flat.baseChange
add_to_sga "3 VIB 10.1" "special case" Module.Flat.baseChange
add_to_sga "3 VIB 11.1" "special case" Module.Flat.baseChange
add_to_sga "3 VIB 2.1.2" "special case" Module.Flat.baseChange
add_to_sga "3 VIIB 1.2.1" "partial" Module.Flat.baseChange
add_to_sga "3 VIIB 1.3.3" "(iii), special case" Module.Flat.baseChange
add_to_sga "3 XIX 2.1" "special case" Module.Flat.baseChange
add_to_sga "3 XV 3.8" "partial" Module.Flat.baseChange
add_to_sga "4 V 1.7.1" "special case" Module.Flat.baseChange
add_to_sga "4 V 8.2.9" "special case" Module.Flat.baseChange
add_to_sga "6 III 3.5.2" "Affine case" Module.Flat.baseChange
add_to_sga "6 IV 3.1.1" "special case" Module.Flat.baseChange
add_to_sga "6 XII 2.3" "(a)" Module.Flat.baseChange
add_to_sga "7 VII 1.3.8" "flatness clause" Module.Flat.baseChange
add_to_ega "0 6.2.1" "more general" Module.Flat.baseChange
add_to_ega "0 6.6.3" "necessity" Module.Flat.baseChange
add_to_ega "III 7.4.1" "partial" Module.Flat.baseChange
add_to_ega "III 7.7.2" "special case" Module.Flat.baseChange
add_to_ega "III 7.9.7" "special case" Module.Flat.baseChange
add_to_ega "IV 11.2.6.1" "(ii), sufficiency" Module.Flat.baseChange
add_to_ega "IV 11.3.10.2" "1°" Module.Flat.baseChange
add_to_ega "IV 2.1.4" "special case" Module.Flat.baseChange
add_to_ega "IV 2.1.5" "special case" Module.Flat.baseChange
add_to_ega "IV 2.2.10" "special case" Module.Flat.baseChange
add_to_ega "IV 20.6.9" "partial" Module.Flat.baseChange
add_to_ega "IV 21.15.9" "partial" Module.Flat.baseChange
add_to_stacks 00HI "faithfully flat base change" Module.FaithfullyFlat.instTensorProduct
add_to_ega "0 6.6.3" "necessity" Module.FaithfullyFlat.instTensorProduct
add_to_ega "IV 11.9.14" "affine case" Module.FaithfullyFlat.instTensorProduct
add_to_ega "IV 2.2.10" "special case" Module.FaithfullyFlat.instTensorProduct
add_to_ega "IV 2.2.11" "(i), affine case" Module.FaithfullyFlat.instTensorProduct
add_to_ega "IV 2.2.13" "(i) for affine schemes" Module.FaithfullyFlat.instTensorProduct
add_to_ega "IV 2.2.2" "partial" Module.FaithfullyFlat.instTensorProduct
add_to_ega "IV 2.5.1" "special case" Module.FaithfullyFlat.instTensorProduct
add_to_ega "IV 2.5.8.8" "partial" Module.FaithfullyFlat.instTensorProduct
add_to_ega "0 6.4.5" "first assertion" Module.FaithfullyFlat.instTensorProduct
add_to_ega "0 6.4.4" "last assertion"
  Module.FaithfullyFlat.instTensorProduct

/- Stacks 00HJ is Mathlib's `Module.Flat.iff_flat_tensorProduct`, stated in the orientation
`Module.Flat R' (R' ⊗[R] M) ↔ Module.Flat R M`. -/
add_to_stacks 00HJ "flatness descends along a faithfully flat base change"
  Module.Flat.iff_flat_tensorProduct
add_to_sga "3 XIX 2.1" "special case" Module.Flat.iff_flat_tensorProduct
add_to_sga "4½ Arcata 1.4.2" "more general" Module.Flat.iff_flat_tensorProduct
add_to_sga "6 I 5.7" "a), special case" Module.Flat.iff_flat_tensorProduct
add_to_ega "0 6.6.3" Module.Flat.iff_flat_tensorProduct
add_to_ega "IV 2.2.11" "(iii), special case" Module.Flat.iff_flat_tensorProduct
add_to_ega "IV 2.5.1" "flat part, affine"
  Module.Flat.iff_flat_tensorProduct

end
