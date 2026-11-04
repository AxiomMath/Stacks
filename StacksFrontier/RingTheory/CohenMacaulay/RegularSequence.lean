module

public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.DimensionCriterion
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.Depth
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.ReesExchange
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.LocalRingMap

/-!
# Regular sequences in Cohen–Macaulay local rings

Re-exports:

* `StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.DimensionCriterion`: Stacks 02JN, a
  sequence in the maximal ideal of a Cohen–Macaulay local ring is regular if and only if it cuts
  the dimension down by its length.
* `StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.Depth`,
  `StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.ReesExchange`,
  `StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.LocalRingMap`: Stacks 06LC, a regular
  sequence of length `dim B` in a Cohen–Macaulay local ring `B` coming from a map of local rings
  `A → B` with `m_B = √(m_A B)`, together with the depth theory it uses.
-/
