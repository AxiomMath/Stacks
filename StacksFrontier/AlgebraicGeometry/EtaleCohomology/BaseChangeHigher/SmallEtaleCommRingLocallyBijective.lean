module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding

/-!
# Sheafification of rings on the small étale site, at every large universe

Sheafification of presheaves of commutative rings on the small étale site of a scheme
`T : Scheme.{u}`, with rings in any universe `w` containing the objects of the site
(`UnivLE.{u + 1, w}`), inverts exactly the locally bijective maps.

## Main results

* `Stacks.Cohomology.BaseChange.wEqualsLocallyBijective_commRingCat_smallEtale_of_univLE`.

## Implementation notes

This generalizes
`Stacks.Cohomology.BaseChange.wEqualsLocallyBijective_commRingCat_smallEtale` (stated at
`CommRingCat.{u + 1}`); the general instance is stated here under its own name. Stating the
universe as a variable constrained by `UnivLE` rather than as a
`max` lets instance search find it at `max (u + 1) v`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.Cohomology.BaseChange

variable (T : Scheme.{u})

/-- Sheafification of presheaves of commutative rings on the small étale site of a scheme, with
rings in any universe `w` containing the objects of the site, inverts exactly the locally
bijective maps. -/
public instance wEqualsLocallyBijective_commRingCat_smallEtale_of_univLE [UnivLE.{u + 1, w}] :
    (smallEtaleTopology T).WEqualsLocallyBijective CommRingCat.{w} :=
  have h := (essentiallySmall_iff.{u + 1} T.Etale).1 inferInstance
  have hS : Small.{w} (Skeleton T.Etale) := @Small.trans_univLE _ h.1 _
  have : UnivLE.{u, w} := @UnivLE.trans UnivLE.succ.{u, u} ‹_›
  have : EssentiallySmall.{w} T.Etale :=
    (essentiallySmall_iff.{w} T.Etale).2 ⟨hS, locallySmall_of_univLE _⟩
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, w, u + 1, w + 1, w} _

end Stacks.Cohomology.BaseChange

end
