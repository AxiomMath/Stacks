module

public import Mathlib.CategoryTheory.Sites.Limits
import StacksCore.Tactic.StacksAttribute

/-!
# Limits of sheaves are computed as presheaf limits

Stacks 00W2 says that for a site `(C, J)` and any indexing category `I`, limits of diagrams of
sheaves of sets exist and coincide with the corresponding limits of presheaves. That is Mathlib's
`CategoryTheory.Sheaf.createsLimitsOfShape`: the inclusion `sheafToPresheaf J` creates limits of
shape `I`.

## References

* [Stacks Project, Tag 00W2](https://stacks.math.columbia.edu/tag/00W2)
-/

@[expose] public section

add_to_stacks 00W2 "the inclusion of sheaves into presheaves creates limits of any shape, so
  limits of diagrams of sheaves of sets exist and agree with the limits computed in presheaves"
  CategoryTheory.Sheaf.createsLimitsOfShape
