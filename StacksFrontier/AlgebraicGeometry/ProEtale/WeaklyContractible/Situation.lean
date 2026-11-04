module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible

/-!
# Ringed sites with enough weakly contractible objects

Several results on a site `C` hold once one fixes a collection `B` of its objects which is
*covering* — every object of `C` has a `J`-covering by members of `B` — and all of whose
members are *weakly contractible*, meaning that a locally surjective morphism of sheaves of
sets is already surjective on sections over them. This file bundles that situation together
with a sheaf of rings on `C`, so that a result about sheaves of modules may be stated by
quantifying over the bundle instead of repeating its three hypotheses.

## Main definitions

* `Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation`: a sheaf of rings on a site,
  together with a covering collection of weakly contractible objects.

## Implementation notes

The site is a Grothendieck topology `J` on a category `C`, and the covering condition is
`CategoryTheory.GrothendieckTopology.HasEnoughObjects J B`. The collection `B` is part of the
data rather than a hypothesis, because the results that consume the bundle test exactness on
its members and so must name them.

Weak contractibility is tested on sheaves of sets valued in the universe `t` of the modules
the consumers speak about, which is independent of the morphism universe `v` of the site and
of the universe `w` of the sheaf of rings. Stated at `t = v` the condition is
`CategoryTheory.GrothendieckTopology.IsWeaklyContractible`.

## References

* [Stacks Project, Tag 0945](https://stacks.math.columbia.edu/tag/0945)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.WeaklyContractible

/-- A ringed site equipped with a collection `B` of weakly contractible objects such that
every object of the site has a covering by objects in `B`. -/
structure WeaklyContractibleObjectsSituation.{w, v, u, t}
    (C : Type u) [Category.{v} C] (J : GrothendieckTopology C) where
  /-- The chosen collection of objects. -/
  B : ObjectProperty C
  /-- Every object in the chosen collection is weakly contractible. -/
  isWeaklyContractible : ∀ ⦃U : C⦄, B U →
    ∀ (F G : Sheaf J (Type t)) (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (Opposite.op U))
  /-- Every object has a covering by objects in the chosen collection. -/
  hasEnoughObjects : J.HasEnoughObjects B
  /-- The fixed sheaf of rings. -/
  O : Sheaf J RingCat.{w}

end Stacks.WeaklyContractible

end
