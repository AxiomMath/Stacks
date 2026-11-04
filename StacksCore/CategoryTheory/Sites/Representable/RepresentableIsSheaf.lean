module

public import Mathlib.CategoryTheory.Sites.Subcanonical
import StacksCore.Tactic.StacksAttribute

/-!
# Subcanonical topologies

Stacks 00WQ says that a topology `J` on a site `C` is *weaker than the canonical topology*, or
*subcanonical*, when all of its coverings are universal effective epimorphisms; equivalently, when
every representable presheaf on `C` is a sheaf for `J`.

That is the form Mathlib records as `CategoryTheory.GrothendieckTopology.Subcanonical`.

## References

* [Stacks Project, Tag 00WQ](https://stacks.math.columbia.edu/tag/00WQ)
-/

@[expose] public section

add_to_stacks 00WQ "a topology is subcanonical when every representable presheaf is a sheaf
  for it" CategoryTheory.GrothendieckTopology.Subcanonical
