module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse-image structure sheaf and the ringed projection of a fibred category

Let `(D, O_D)` be a ringed site and `p : C ⥤ D` a fibred category over its underlying site,
the standing data of [Stacks, Tag 08P8]
(`Stacks.Sites.FibredCategory.FibredCategorySituation`). Giving `C` the topology inherited
from `D` makes the projection a morphism of topoi `π : Sh(C) ⟶ Sh(D)`
(`FibredCategorySituation.projection`). This file completes the situation: it equips `C` with
the structure sheaf `O_C = π⁻¹O_D`, making it a ringed topos, and exhibits `π` as a morphism of
ringed topoi, the structure map being the unit of the adjunction `π⁻¹ ⊣ π_*` on sheaves of
rings.

## Main definitions

* `Stacks.Sites.FibredCategory.FibredCategorySituation.totalRingedTopos`: the total category
  with the inherited topology and the structure sheaf `O_C = π⁻¹O_D`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.ringedProjection`: the projection as a
  morphism of ringed topoi `(Sh(C), O_C) ⟶ (Sh(D), O_D)`.

## Implementation notes

These are the two parts of Stacks 08P8 that could not be stated when the rest of the tag was
formalized. The inverse image of a sheaf of *commutative* rings along a morphism of topoi had
been removed from this development, so `O_C = π⁻¹O_D` could not be typed at all:
`AlgebraicGeometry.RingedTopos.O` is a `Sheaf J CommRingCat`, while the surviving
`Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf` is valued in `Sheaf J RingCat`. It is
now available again as
`Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor`, with its adjunction
`commRingImageAdjunction`, which is what makes both definitions below possible.

`ringedProjection` is stated with the library's `RingedToposHom`, which records the structure
map in both of its forms — the direct-image form `f♯ : O_D ⟶ π_*O_C` and the inverse-image
form `π⁻¹O_D ⟶ O_C` — and requires them to be adjunct. Since `O_C` is *defined* to be `π⁻¹O_D`,
the inverse-image form here is the identity, and the direct-image form is therefore its
adjunct, the unit `ringUnit`. That is the same morphism of ringed topoi as "the structure map
is the adjunction unit": `Stacks.Sheaves.ToposPushforward.ringImageAdjunction_unit_app` says
`ringUnit` *is* the unit of the ring-level adjunction, and `homEquiv_id_eq_ringUnit` says the
adjunct of the identity is that unit, which is exactly the `fSharp_adjunct` field. The two
readings agree because forgetting commutativity commutes with the inverse image on the nose
(`Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_pullbackCommRingSheaf`, an `rfl`), so the
underlying sheaf of rings of `O_C` *is* `π⁻¹` of the underlying sheaf of rings of `O_D`, and
the identity typechecks as the inverse-image form.

The four `GrothendieckTopology.HasSheafCompose` hypotheses are assumed rather than derived,
following `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPushforward.lean` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposModules.lean`: deriving them needs a
`UnivLE` relation between the site's hom universe and the universe of sections, which the
independent universes here do not provide.

## References

* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.RingedToposModules

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

/-- **Stacks 08P8, the inverse-image structure sheaf.** The total ringed topos, with
`O_C = π⁻¹O_D`. -/
@[stacks 08P8 "inverse-image structure sheaf"]
def totalRingedTopos : RingedTopos.{vC, uC, max w uD vD uC vC} where
  C := s.C
  J := s.topology
  O := (inverseImageCommRingFunctor s.projection).obj s.liftedBaseSheaf

/-- **Stacks 08P8, the morphism of ringed topoi.** The projection as a morphism of ringed
topoi; its structure map is the unit of the adjunction `π⁻¹ ⊣ π_*` on sheaves of rings. -/
@[stacks 08P8 "morphism of ringed topoi"]
def ringedProjection : RingedToposHom s.totalRingedTopos s.baseRingedTopos where
  toToposHom := s.projection
  fSharp := ringUnit s.projection (Stacks.SheafOfModules.Tensor.ringSheaf s.baseRingedTopos.O)
  fSharpInverseImage := 𝟙 _
  fSharp_adjunct := by
    change (sheafCompose s.base.J (forget RingCat.{max w uD vD uC vC})).map
        (ringUnit s.projection (Stacks.SheafOfModules.Tensor.ringSheaf s.baseRingedTopos.O)) =
      s.projection.adj.homEquiv
          (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf s.baseRingedTopos.O))
          (Sheaf.ringSheaf (inverseImageRingSheaf s.projection
            (Stacks.SheafOfModules.Tensor.ringSheaf s.baseRingedTopos.O)))
        ((sheafCompose s.topology (forget RingCat.{max w uD vD uC vC})).map
          (𝟙 (inverseImageRingSheaf s.projection
            (Stacks.SheafOfModules.Tensor.ringSheaf s.baseRingedTopos.O))))
    rw [CategoryTheory.Functor.map_id]
    exact (homEquiv_id_eq_ringUnit s.projection
      (Stacks.SheafOfModules.Tensor.ringSheaf s.baseRingedTopos.O)).symm

end FibredCategorySituation

end Stacks.Sites.FibredCategory
