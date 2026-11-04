module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineRingedTopos
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteZariskiSyntomic
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EnoughPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiCovering.BigZariskiMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Precoverage

/-!
# The morphism of ringed topoi of the affine subsite, for the four coarser topologies

`AlgebraicGeometry.Stack.affineToFull` (Stacks 0H0C) builds the morphism of ringed topoi
`(Sh(𝒳_{affine, τ}), 𝒪) ⟶ (Sh(𝒳_τ), 𝒪_𝒳)` from the fact that the inclusion of the affine
subcategory is a dense subsite for the associated topologies. This file supplies that input, and
hence the morphism, for the Zariski, étale, smooth and syntomic topologies; the fppf case is
`AlgebraicGeometry.Stack.affineToFullFppf`.

Each input is the corresponding case of Stacks 0H0B,
`AlgebraicGeometry.Stack.AffineCategory.inclusion_isSpecialCocontinuous_zariski` and its three
companions, once the topology of the slice of the big Zariski, étale, smooth or syntomic site
carried by `B` is identified with the localization at `S` of the corresponding topology on the
underlying category of schemes.

## Main definitions

* `AlgebraicGeometry.Stack.affineToFullZariski`, `.affineToFullEtale`, `.affineToFullSmooth`
  and `.affineToFullSyntomic`: Stacks 0H0C for the Zariski, étale, smooth and syntomic
  topologies.

## Main results

* `AlgebraicGeometry.Stack.isDenseSubsite_affineInclusion_zariski` and its three companions:
  the affine inclusion is a dense subsite for the associated topologies.
* `AlgebraicGeometry.Stack.zariskiTopology_le_topology`, `.smoothTopology_le_topology` and
  `.syntomicTopology_le_topology`: the three topologies are coarser than the fppf one.

## Implementation notes

The four coarser big sites carried by a big fppf site (Stacks 03FF) have the same underlying
category as the fppf one and carry `B`'s own cutoff and covering bound, so the slice over `S`,
its affine subcategory and the inclusion of the one in the other are literally the fppf ones.
The identifications of the four slice topologies with the localizations at `S` of the
topologies of Stacks 03FF are
`AlgebraicGeometry.BigFppfSite.bigZariskiOver_topology_toBigZariskiSite` and its three
companions.

## References

* [Stacks Project, Tag 0H0C](https://stacks.math.columbia.edu/tag/0H0C)
* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 020W](https://stacks.math.columbia.edu/tag/020W)
* [Stacks Project, Tag 021E](https://stacks.math.columbia.edu/tag/021E)
* [Stacks Project, Tag 06VC](https://stacks.math.columbia.edu/tag/06VC)
* [Stacks Project, Tag 06VD](https://stacks.math.columbia.edu/tag/06VD)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u v w

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The big Zariski topology on the underlying category of schemes is coarser than the fppf
one: a selected Zariski covering family is in particular a selected family. -/
theorem zariskiTopology_le_topology : B.zariskiTopology ≤ B.topology := by
  exact Precoverage.toGrothendieck_mono fun _ _ ⟨E, h, hE⟩ => ⟨E, h, hE.1⟩

/-- The big smooth topology on the underlying category of schemes is coarser than the fppf
one: a selected smooth covering family is in particular a selected family. -/
theorem smoothTopology_le_topology : B.smoothTopology ≤ B.topology := by
  exact Precoverage.toGrothendieck_mono fun _ _ ⟨E, h, hE⟩ => ⟨E, h, hE.1⟩

/-- The big syntomic topology on the underlying category of schemes is coarser than the fppf
one: a selected syntomic covering family is in particular a selected family. -/
theorem syntomicTopology_le_topology : B.syntomicTopology ≤ B.topology := by
  exact Precoverage.toGrothendieck_mono fun _ _ ⟨E, h, hE⟩ => ⟨E, h, hE.1⟩

/-! ### The affine inclusion is a dense subsite -/

/-- The affine inclusion of a category fibred in groupoids is a dense subsite for the associated
Zariski topologies (Stacks 0H0B). -/
theorem isDenseSubsite_affineInclusion_zariski (hp : p.IsFiberedInGroupoids) :
    (AffineCategory.inclusion B S hS p).IsDenseSubsite
      (associatedAffineTopology B S hS p
        (BigAffineZariski.topology B.toBigZariskiSite S hS))
      (associatedTopology B S hS p B.zariskiTopology) := by
  simpa only [B.bigZariskiOver_topology_toBigZariskiSite S hS] using
    (AffineCategory.inclusion_isSpecialCocontinuous_zariski B S hS p hp).2

/-- The affine inclusion of a category fibred in groupoids is a dense subsite for the associated
étale topologies (Stacks 0H0B). -/
theorem isDenseSubsite_affineInclusion_etale (hp : p.IsFiberedInGroupoids) :
    (AffineCategory.inclusion B S hS p).IsDenseSubsite
      (associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS))
      (associatedTopology B S hS p B.etaleTopology) := by
  simpa only [B.bigEtaleOver_topology_toBigEtaleSite S hS] using
    (AffineCategory.inclusion_isSpecialCocontinuous_etale B S hS p hp).2

/-- The affine inclusion of a category fibred in groupoids is a dense subsite for the associated
smooth topologies (Stacks 0H0B). -/
theorem isDenseSubsite_affineInclusion_smooth (hp : p.IsFiberedInGroupoids) :
    (AffineCategory.inclusion B S hS p).IsDenseSubsite
      (associatedAffineTopology B S hS p (BigAffineSmooth.topology B.toBigSmoothSite S hS))
      (associatedTopology B S hS p B.smoothTopology) := by
  simpa only [B.bigSmoothOver_topology_toBigSmoothSite S hS] using
    (AffineCategory.inclusion_isSpecialCocontinuous_smooth B S hS p hp).2

/-- The affine inclusion of a category fibred in groupoids is a dense subsite for the associated
syntomic topologies (Stacks 0H0B). -/
theorem isDenseSubsite_affineInclusion_syntomic (hp : p.IsFiberedInGroupoids) :
    (AffineCategory.inclusion B S hS p).IsDenseSubsite
      (associatedAffineTopology B S hS p
        (BigAffineSyntomic.topology B.toBigSyntomicSite S hS))
      (associatedTopology B S hS p B.syntomicTopology) := by
  simpa only [B.bigSyntomicOver_topology_toBigSyntomicSite S hS] using
    (AffineCategory.inclusion_isSpecialCocontinuous_syntomic B S hS p hp).2

/-! ### The morphisms of ringed topoi -/

/-- The inclusion of the affine subsite of the associated Zariski site of a category fibred in
groupoids, as a morphism of ringed topoi for the lifted structure sheaf of Stacks 06TV. Its
inverse image is an equivalence and its structure morphism is an isomorphism, by
`AlgebraicGeometry.Stack.isEquivalence_affineToFull_inverseImage` and
`AlgebraicGeometry.Stack.isIso_affineToFull_fSharpInverseImage`. -/
@[stacks 0H0C "the Zariski topology"]
noncomputable def affineToFullZariski (hp : p.IsFiberedInGroupoids) :
    letI : (AffineCategory.inclusion B S hS p).IsDenseSubsite
        (associatedAffineTopology B S hS p
          (BigAffineZariski.topology B.toBigZariskiSite S hS))
        (associatedTopology B S hS p B.zariskiTopology) :=
      isDenseSubsite_affineInclusion_zariski B S hS p hp
    AlgebraicGeometry.RingedToposHom
      (affineRingedTopos B S hS p B.zariskiTopology
        (BigAffineZariski.topology B.toBigZariskiSite S hS)
        (liftedStructureSheaf B S hS p B.zariskiTopology hp (zariskiTopology_le_topology B)))
      (fullRingedTopos B S hS p B.zariskiTopology
        (liftedStructureSheaf B S hS p B.zariskiTopology hp
          (zariskiTopology_le_topology B))) :=
  letI := isDenseSubsite_affineInclusion_zariski B S hS p hp
  affineToFull B S hS p B.zariskiTopology
    (BigAffineZariski.topology B.toBigZariskiSite S hS)
    (liftedStructureSheaf B S hS p B.zariskiTopology hp (zariskiTopology_le_topology B))

/-- The inclusion of the affine subsite of the associated étale site of a category fibred in
groupoids, as a morphism of ringed topoi for the lifted structure sheaf of Stacks 06TV. Its
inverse image is an equivalence and its structure morphism is an isomorphism, by
`AlgebraicGeometry.Stack.isEquivalence_affineToFull_inverseImage` and
`AlgebraicGeometry.Stack.isIso_affineToFull_fSharpInverseImage`. -/
@[stacks 0H0C "the étale topology"]
noncomputable def affineToFullEtale (hp : p.IsFiberedInGroupoids) :
    letI : (AffineCategory.inclusion B S hS p).IsDenseSubsite
        (associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS))
        (associatedTopology B S hS p B.etaleTopology) :=
      isDenseSubsite_affineInclusion_etale B S hS p hp
    AlgebraicGeometry.RingedToposHom
      (affineRingedTopos B S hS p B.etaleTopology
        (BigAffineEtale.topology B.toBigEtaleSite S hS)
        (liftedStructureSheaf B S hS p B.etaleTopology hp (etaleTopology_le_topology B)))
      (fullRingedTopos B S hS p B.etaleTopology
        (liftedStructureSheaf B S hS p B.etaleTopology hp (etaleTopology_le_topology B))) :=
  letI := isDenseSubsite_affineInclusion_etale B S hS p hp
  affineToFull B S hS p B.etaleTopology (BigAffineEtale.topology B.toBigEtaleSite S hS)
    (liftedStructureSheaf B S hS p B.etaleTopology hp (etaleTopology_le_topology B))

/-- The inclusion of the affine subsite of the associated smooth site of a category fibred in
groupoids, as a morphism of ringed topoi for the lifted structure sheaf of Stacks 06TV. Its
inverse image is an equivalence and its structure morphism is an isomorphism, by
`AlgebraicGeometry.Stack.isEquivalence_affineToFull_inverseImage` and
`AlgebraicGeometry.Stack.isIso_affineToFull_fSharpInverseImage`. -/
@[stacks 0H0C "the smooth topology"]
noncomputable def affineToFullSmooth (hp : p.IsFiberedInGroupoids) :
    letI : (AffineCategory.inclusion B S hS p).IsDenseSubsite
        (associatedAffineTopology B S hS p (BigAffineSmooth.topology B.toBigSmoothSite S hS))
        (associatedTopology B S hS p B.smoothTopology) :=
      isDenseSubsite_affineInclusion_smooth B S hS p hp
    AlgebraicGeometry.RingedToposHom
      (affineRingedTopos B S hS p B.smoothTopology
        (BigAffineSmooth.topology B.toBigSmoothSite S hS)
        (liftedStructureSheaf B S hS p B.smoothTopology hp (smoothTopology_le_topology B)))
      (fullRingedTopos B S hS p B.smoothTopology
        (liftedStructureSheaf B S hS p B.smoothTopology hp (smoothTopology_le_topology B))) :=
  letI := isDenseSubsite_affineInclusion_smooth B S hS p hp
  affineToFull B S hS p B.smoothTopology (BigAffineSmooth.topology B.toBigSmoothSite S hS)
    (liftedStructureSheaf B S hS p B.smoothTopology hp (smoothTopology_le_topology B))

/-- The inclusion of the affine subsite of the associated syntomic site of a category fibred in
groupoids, as a morphism of ringed topoi for the lifted structure sheaf of Stacks 06TV. Its
inverse image is an equivalence and its structure morphism is an isomorphism, by
`AlgebraicGeometry.Stack.isEquivalence_affineToFull_inverseImage` and
`AlgebraicGeometry.Stack.isIso_affineToFull_fSharpInverseImage`. -/
@[stacks 0H0C "the syntomic topology"]
noncomputable def affineToFullSyntomic (hp : p.IsFiberedInGroupoids) :
    letI : (AffineCategory.inclusion B S hS p).IsDenseSubsite
        (associatedAffineTopology B S hS p
          (BigAffineSyntomic.topology B.toBigSyntomicSite S hS))
        (associatedTopology B S hS p B.syntomicTopology) :=
      isDenseSubsite_affineInclusion_syntomic B S hS p hp
    AlgebraicGeometry.RingedToposHom
      (affineRingedTopos B S hS p B.syntomicTopology
        (BigAffineSyntomic.topology B.toBigSyntomicSite S hS)
        (liftedStructureSheaf B S hS p B.syntomicTopology hp
          (syntomicTopology_le_topology B)))
      (fullRingedTopos B S hS p B.syntomicTopology
        (liftedStructureSheaf B S hS p B.syntomicTopology hp
          (syntomicTopology_le_topology B))) :=
  letI := isDenseSubsite_affineInclusion_syntomic B S hS p hp
  affineToFull B S hS p B.syntomicTopology
    (BigAffineSyntomic.topology B.toBigSyntomicSite S hS)
    (liftedStructureSheaf B S hS p B.syntomicTopology hp (syntomicTopology_le_topology B))

end Stack

end AlgebraicGeometry

end
