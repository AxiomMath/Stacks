module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiDescent
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 095F: constructibility is a Zariski local property

Tag 095F says that, on an arbitrary scheme `X`, constructibility of a sheaf of sets, of abelian
groups, or of modules over a Noetherian ring on the small étale site of `X` can be checked Zariski
locally. Both directions are the equivalences
`AlgebraicGeometry.isConstructibleFiniteSheaf_iff_forall_restrict` and
`AlgebraicGeometry.isConstructibleModuleSheaf_iff_forall_restrict`: for any open covering
`U k ⟶ X` of `X`, a sheaf is constructible exactly when its restriction to every `U k` is. This
file records the tag on them.

## References

* [Stacks Project, Tag 095F](https://stacks.math.columbia.edu/tag/095F)
-/

add_to_stacks 095F
  "sets and abelian groups: constructible iff constructible on every member of any open covering"
  AlgebraicGeometry.isConstructibleFiniteSheaf_iff_forall_restrict

add_to_stacks 095F
  "Noetherian-ring modules: constructible iff constructible on every member of any open covering"
  AlgebraicGeometry.isConstructibleModuleSheaf_iff_forall_restrict
