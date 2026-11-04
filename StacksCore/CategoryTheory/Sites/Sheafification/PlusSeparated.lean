module

public import Mathlib.CategoryTheory.Sites.Plus
import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of the plus construction

Stacks 00W5 says that the assignment `F ↦ (F ⟶ F⁺)` is functorial, i.e. that the canonical maps
`J.toPlus F : F ⟶ J.plusObj F` are natural in `F`. That naturality square is Mathlib's
`CategoryTheory.GrothendieckTopology.toPlus_naturality`.

## References

* [Stacks Project, Tag 00W5](https://stacks.math.columbia.edu/tag/00W5)
-/

@[expose] public section

add_to_stacks 00W5 "the plus construction is functorial: the canonical maps `F ⟶ F⁺` are natural
  in `F`" CategoryTheory.GrothendieckTopology.toPlus_naturality
