module

public import StacksFrontier.RingTheory.Depth.Defs.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The depth of a zero module

A module with at most one element has depth `⊤` along every ideal: the ideal acts on it
surjectively, which is the convention `Module.depth` takes for the value `⊤`.

## Main results

* `depth_eq_top_of_subsingleton`: the `I`-depth of a subsingleton module is `⊤`.

## Implementation notes

The statement is a one-line consequence of the definition, and was re-proved privately in eleven
modules of the tree before it had a home; it lives here, in a module whose only import is the one
that defines `Module.depth`, so that pointing at it costs an importer nothing.

## References

* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
-/

@[expose] public section

/-- A module with at most one element has depth `⊤` along every ideal: the ideal acts on it
surjectively, and `Module.depth` is `⊤` in that case by convention. -/
@[ega "0 16.4.5" "partial"]
public lemma depth_eq_top_of_subsingleton {R M : Type*} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M] [Subsingleton M] : Module.depth R I M = ⊤ := by
  simp [Module.depth, Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule R M))]

end
