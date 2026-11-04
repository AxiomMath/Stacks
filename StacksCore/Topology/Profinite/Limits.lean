module

public import Mathlib.Topology.Category.Profinite.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# A limit of profinite spaces is profinite

Mathlib's `Profinite` is the category whose objects are profinite spaces, and
`Profinite.hasLimits` provides a limit object *inside* `Profinite` for every small diagram. Since
that limit object is itself a `Profinite`, Stacks 0ET8 — "a limit of profinite spaces is
profinite" — is exactly that instance.

## References

* [Stacks Project, Tag 0ET8](https://stacks.math.columbia.edu/tag/0ET8)
-/

@[expose] public section

add_to_stacks 0ET8 "every small diagram of profinite spaces has a limit in `Profinite`, i.e. its
  limit is again a profinite space" Profinite.hasLimits
