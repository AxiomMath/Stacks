module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Formalism
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The upper shriek formalism of Nagata compactifications

Every separated morphism of finite type `f : X ⟶ Y` with Noetherian target has a compactification
by Nagata's theorem ([Stacks, Tag 0F41]). Choosing one for every such `f` gives the canonical
instance `Stacks.Duality.UpperShriek.nagata` of the upper shriek formalism
`Stacks.Duality.UpperShriek.ofCompactifications`, which is `Stacks.Duality.UpperShriek.ofNagata`
at that input.

## Main definitions

* `Stacks.Duality.hasCompactification_of_isShriekable`: a shriekable morphism has a
  compactification.
* `Stacks.Duality.nagataCompactification`: a chosen compactification of each shriekable morphism.
* `Stacks.Duality.UpperShriek.nagata`: the upper shriek formalism on `D⁺_QCoh` of these
  compactifications.

## References

* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

/-- **Nagata compactification for shriekable morphisms** ([Stacks, Tag 0F41]): a separated
morphism of finite type with Noetherian target factors as a quasi-compact open immersion followed
by a proper morphism. -/
@[sga "4 XVII 3.2.3" "(iii), special case",
  sga "4½ Arcata 4.5.1" "more general",
  sga "7 XIII 2.1.6"]
theorem hasCompactification_of_isShriekable {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsShriekable f) : HasCompactification f :=
  have := hf.target_noetherian
  have := hf.isSeparated
  have := hf.locallyOfFiniteType
  have := hf.quasiCompact
  hasCompactification_of_compactSpace_quasiSeparatedSpace f

/-- A chosen compactification of a shriekable morphism, from Nagata's theorem
([Stacks, Tag 0F41]). -/
@[sga "4½ Arcata 4.5.1"]
def nagataCompactification {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsShriekable f) :
    CompactificationOf (Over.mk f) :=
  (hasCompactification_of_isShriekable hf).choose

namespace UpperShriek

/-- **The upper shriek formalism of Nagata compactifications**: the functors `f^!` of
[Stacks, Tag 0A9Y] on `D⁺_QCoh` for every shriekable `f`, with their comparisons
([Stacks, Tag 0ATX], [Stacks, Tag 0ATY]), at the compactifications `nagataCompactification`. -/
abbrev nagata : UpperShriek fun X : Scheme.{u} => quasiCoherentDerivedCategoryPlusOfModel X :=
  ofCompactifications nagataCompactification

/-- The formalism `nagata` is `ofNagata` at Nagata's theorem. -/
theorem nagata_eq_ofNagata :
    nagata.{u} = ofNagata fun _ hf => hasCompactification_of_isShriekable hf :=
  rfl

end UpperShriek

end Stacks.Duality
