module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedProjection

/-!
# The ringed topos of a fibred category over a ringed site

Let `(D, O_D)` be a ringed site and `p : C ⥤ D` a fibred category over its underlying site.
Giving `C` the topology inherited from `D` makes the projection a morphism of topoi
`π : Sh(C) ⟶ Sh(D)`; setting `O_C = π⁻¹O_D` makes `C` a ringed topos and exhibits `π` as a
morphism of ringed topoi, the structure map being the unit of `π⁻¹ ⊣ π_*`.

The standing data, the morphism of topoi and the inverse-image structure sheaf are
`Stacks.Sites.FibredCategory.FibredCategorySituation`, `.inducedProjection` and
`.totalRingedTopos`, which already carry the tag for the first three clauses of the source
where they are declared. The fourth clause, `π` as a morphism of ringed topoi, is
stated here with the two-field `AlgebraicGeometry.RingedToposHom` of Stacks 01D3 part (2),
whose structure map lives at the `CommRingCat` level.

## Main definitions

* `Stacks.Sites.FibredCategory.FibredCategorySituation.commRingRingedProjection`: the
  projection as a morphism of ringed topoi `(Sh(C), π⁻¹O_D) ⟶ (Sh(D), O_D)`.

## Implementation notes

`Stacks.Sites.FibredCategory.FibredCategorySituation.ringedProjection` already exhibits the
projection as a morphism of ringed topoi, but for the richer four-field
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, whose structure map lives at the `RingCat`
level and which stores both forms of that map together with the equation making them adjunct.
The source's clause is the two-field datum of Stacks 01D3 part (2), so it is stated here with
`AlgebraicGeometry.RingedToposHom` instead; the structure map is the unit of the
commutative-ring-level adjunction `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`,
which typechecks because the total structure sheaf is *defined* to be the inverse image of the
base one.

## References

* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward

namespace Stacks.Sites.FibredCategory

universe uD vD uC vC w

namespace FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})
  [s.topology.HasSheafCompose (forget RingCat.{max w uD vD uC vC})]
  [s.base.J.HasSheafCompose (forget RingCat.{max w uD vD uC vC})]
  [s.topology.HasSheafCompose
    (forget₂ CommRingCat.{max w uD vD uC vC} RingCat.{max w uD vD uC vC})]
  [s.base.J.HasSheafCompose
    (forget₂ CommRingCat.{max w uD vD uC vC} RingCat.{max w uD vD uC vC})]

/-- The projection of a fibred category as a morphism of ringed topoi; its structure map is the
unit of the adjunction `π⁻¹ ⊣ π_*` on sheaves of commutative rings. -/
@[stacks 08P8 "morphism of ringed topoi"]
noncomputable def commRingRingedProjection :
    AlgebraicGeometry.RingedToposHom s.totalRingedTopos s.baseRingedTopos where
  toToposHom := s.projection
  fSharp := (commRingImageAdjunction s.projection).unit.app s.liftedBaseSheaf

end FibredCategorySituation

end Stacks.Sites.FibredCategory

end
