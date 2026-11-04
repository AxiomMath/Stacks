module

public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksFrontier.Deformation.FormalObject.VersalLifting
public import StacksFrontier.Deformation.Formal.VersalObject.MapsToFormalObject
public import StacksFrontier.Deformation.Schlessinger.Basic
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts

/-!
# A versal formal object implies Schlessinger's condition (S1)

This module is a re-export. `Deformation.schlessingerConditionS1_of_versal`, which states that a
predeformation category with a versal formal object satisfies Schlessinger's condition (S1), and
the pushforward and strictification lemmas its proof is built from, were duplicated between this
file and `StacksFrontier/Deformation/Schlessinger/VersalImpliesS1.lean`. Neither of those two
imports the other, so the single copy now lives in their common ancestor
`StacksFrontier/Deformation/Schlessinger/Basic.lean`, which this file re-exports.

## References

* [Stacks Project, Tag 06SY](https://stacks.math.columbia.edu/tag/06SY)
-/
