module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleQuasicoherentHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleRightAcyclic
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent modules on the big sites of an algebraic space, as Stacks tags

For a quasi-coherent `𝒪_X`-module `𝓕` on an algebraic space `X`, the maps
`π_X^*𝓕 ⟶ Rε_{X,*}(a_X^*𝓕)` and `𝓕 ⟶ Ra_{X,*}(a_X^*𝓕)` are isomorphisms (Stacks 0DGP). For a
complex `𝓕₁ ⟶ 𝓕₂ ⟶ 𝓕₃` of quasi-coherent modules, the homology `𝓗_et` of its pullback to
`(Spaces/X)_étale` and the homology `𝓗_fppf` of its pullback to `(Spaces/X)_fppf` satisfy
`𝓗_et ≅ ε_{X,*}𝓗_fppf`, and both have vanishing higher cohomology on affine objects
(Stacks 0DGQ). Both are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleRightAcyclic` and
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleQuasicoherentHomology`; this file
records the tags.

## References

* [Stacks Project, Tag 0DGP](https://stacks.math.columbia.edu/tag/0DGP)
* [Stacks Project, Tag 0DGQ](https://stacks.math.columbia.edu/tag/0DGQ)
-/

@[expose] public section

add_to_stacks 0DGP "both maps: π_X^*𝓕 ≅ ε_{X,*}a_X^*𝓕 ⟶ Rε_{X,*}a_X^*𝓕 and 𝓕 ≅ a_{X,*}a_X^*𝓕 ⟶ \
Ra_{X,*}a_X^*𝓕, the second map in each being the canonical (right acyclicity) isomorphism"
  AlgebraicGeometry.BigFppfSpaceSite.isIso_derivedPushforward_pullback_of_quasicoherent

add_to_stacks 0DGQ AlgebraicGeometry.BigFppfSpaceSite.homology_pullback_of_quasicoherent

end
