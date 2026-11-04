module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Left exactness of the two-field pullback of modules along a flat morphism of ringed topoi

`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap` — Stacks 04JC, second
assertion — is stated for
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`, and for a source and a target whose
section universes agree. This module records the same conclusion for
`AlgebraicGeometry.RingedToposHom.pullbackModules`, the pullback attached to a two-field
morphism of ringed topoi through
`AlgebraicGeometry.RingedToposHom.toModulesHom`, and with the two section universes
independent.

Both changes are needed by a morphism of thickenings of ringed topoi (Stacks 08M7), whose
vertical arrow goes between ringed topoi with unrelated section universes and whose induced map
of defining ideals is written with the two-field pullback.

## The two passages to the four-field morphism agree

The modules development constructs pullback and pushforward over a four-field morphism of ringed
topoi, carrying the inverse-image form of the structure map as data. A two-field morphism of
Stacks 01D3 gives rise to one in two ways, which take that form through two different
adjunctions:

* `AlgebraicGeometry.RingedToposHom.toModulesHom` transposes the ring-level direct-image form
  `f♯` across the adjunction `f⁻¹ ⊣ f_*` for sheaves of *rings*;
* `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` forgets the commutativity of the
  inverse-image form taken across the adjunction for sheaves of *commutative* rings.

`AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom` identifies them. It is
not proved here: it is imported from
`StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison`, the module
dedicated to that comparison, where it is stated at independent section universes and needs only
the two `HasSheafCompose` instances for the forgetful functors to sheaves of rings. The proof
below therefore applies it with nothing further assumed.

## Main results

* `AlgebraicGeometry.RingedToposHom.toModulesHom_pullbackModules_preservesFiniteLimits_of_isFlat`:
  the pullback of sheaves of modules along a flat morphism of ringed topoi, through
  `AlgebraicGeometry.RingedToposHom.toModulesHom`, preserves finite limits. The same conclusion
  for the pullback of `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`, at a common
  section universe, is
  `AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteLimits_of_isFlat`.

## Implementation notes

Only left exactness is recorded, that being what makes the pullback preserve monomorphisms;
right exactness holds with no hypothesis, the pullback being the left adjoint of Stacks 03D7.

No tag is placed here. Stacks 04JC is registered on
`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`, which is where the
mathematics is; the statement below re-spells it and proves nothing new, exactly as
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_preservesFiniteLimits` does for the other
pullback of this development.

## References

* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos)
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe v u w v' u' w'

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 04JC, left exactness, for the pullback of modules attached to a two-field morphism
of ringed topoi.** The pullback of sheaves of modules along a flat morphism of ringed topoi
preserves finite limits.

The pullback of Stacks 03D6 part (2) is the inverse image of Stacks 03D2 followed by extension
of scalars along the inverse-image form of the structure map. The first factor is left exact
with no hypothesis, by
`Stacks.Sheaves.RingedToposModules.inverseImageModules_preservesFiniteLimits`, and at wholly
independent universes; the second is left exact by flatness, which is
`Stacks.Sheaves.RingedToposModules.extendScalars_preservesFiniteLimits`, and is a statement
about the source site alone. The composite is the pullback of the four-field morphism
`toRingedToposModulesHom`, which
`AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom` identifies with the
one this pullback is built from. -/
@[sga "4 IV 13.7" "special case"]
theorem toModulesHom_pullbackModules_preservesFiniteLimits_of_isFlat (f : RingedToposHom X Y)
    (hf : f.IsFlat) : PreservesFiniteLimits
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom) := by
  have hinv := Stacks.Sheaves.RingedToposModules.inverseImageModules_preservesFiniteLimits
    f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
  have hext := Stacks.Sheaves.RingedToposModules.extendScalars_preservesFiniteLimits
    X.J f.fSharpInverseImage hf
  have key := Stacks.Sheaves.RingedToposModules.preservesFiniteLimits_comp_of _ _ hinv hext
  have e : Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom =
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toRingedToposModulesHom :=
    congrArg (fun g ↦ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules g)
      f.toModulesHom_eq_toRingedToposModulesHom
  rw [e]
  exact key

end AlgebraicGeometry.RingedToposHom

end
