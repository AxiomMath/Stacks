module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite

/-!
# Quasi-coherent modules on crystalline sites

A sheaf of modules on either the big or the small crystalline site of a divided power
situation is *quasi-coherent* exactly when it is quasi-coherent as a sheaf of modules on a
ringed site: every object of the site admits a covering on whose members the restricted
module has a global presentation.

## Main definitions

* `SheafOfModules.IsQuasicoherentOnSite` is the quasi-coherence condition, recorded here for
  crystalline sheaves of modules.

## Implementation notes

The crystalline notion is the general ringed-site predicate, applied to either crystalline
site. Keeping that predicate rather than introducing a site-specific synonym lets statements
about crystals in quasi-coherent modules use its existing interface directly, and lets the
local-on-a-cover results proved for the general predicate apply unchanged.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
-/

@[expose] public section

add_to_stacks 07IS "part (2): quasi-coherent, on either crystalline site"
  SheafOfModules.IsQuasicoherentOnSite

end
