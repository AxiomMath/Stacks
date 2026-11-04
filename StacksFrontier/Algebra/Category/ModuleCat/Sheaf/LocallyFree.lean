module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import StacksCore.Tactic.StacksAttribute

/-!
# Locally free sheaves of modules

Stacks tags realised by Mathlib's locally free sheaves of modules, on an arbitrary site
(a ringed space `(X, O_X)` being the site `Opens X`).
-/

@[expose] public section

-- Tag 01C7: a locally free sheaf of modules is quasi-coherent.
add_to_stacks 01C7 "loc. free ⇒ qcoh" SheafOfModules.instIsQuasicoherentOfIsLocallyFree
add_to_stacks 01C7 "locally free data" SheafOfModules.IsLocallyFree.exists_isLocallyFreeData
add_to_stacks 01C7 "presentation, no rels" SheafOfModules.LocalGeneratorsData.quasiCoherentData
add_to_ega "0 5.4.1" SheafOfModules.LocalGeneratorsData.quasiCoherentData
add_to_ega "0 5.4.1" "loc. free ⇒ qcoh" SheafOfModules.instIsQuasicoherentOfIsLocallyFree
