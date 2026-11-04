module

public import StacksFrontier.Homology.Perfect.Colimit.ModuleDescent
public import StacksFrontier.Homology.Perfect.Colimit.ComplexDescent
public import StacksFrontier.Homology.Perfect.Colimit.HomotopyHomDescent
public import StacksFrontier.Homology.Perfect.Colimit.HomColimit

/-!
# Perfect complexes over filtered colimits of rings

This file collects [stacks 0BC7] on perfect complexes over a filtered colimit of commutative rings,
which is split into four parts: `StacksFrontier.Homology.Perfect.Colimit.ModuleDescent` (the derived
extension-of-scalars data, and descent of finite projective modules and matrices),
`StacksFrontier.Homology.Perfect.Colimit.ComplexDescent` (descent of bounded complexes of finite
projectives and of perfect objects), `StacksFrontier.Homology.Perfect.Colimit.HomotopyHomDescent`
(morphisms and homotopies at a finite stage, and composition of derived extension of scalars) and
`StacksFrontier.Homology.Perfect.Colimit.HomColimit` (the Hom-colimit half and the main theorems
`StacksDraft.Perfect.perfectComplexes_filteredColimit_of_datum` and
`StacksDraft.Perfect.perfectComplexes_filteredColimit`).
-/
