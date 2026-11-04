module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedSiteHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteInternalHom
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSiteGeneral

/-!
# Pullback and pushforward of modules along a morphism of small étale ringed sites

Let `a : X ⟶ Y` be a morphism of schemes.  The morphism of small étale ringed sites
`(f_small, f_small^♯) : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` of Stacks 070R part (2) is
`AlgebraicGeometry.smallEtaleRingedSiteHom`.  This file attaches to it the pushforward and the
pullback of sheaves of modules of Stacks 03D6 and their adjunction of Stacks 03D7.

The small étale site has its objects in `Type (u + 1)` and its morphisms and structure rings in
`Type u`, so Mathlib's pullback of sheaves of modules — which needs the pushforward of presheaves
of modules to be a right adjoint, and gets that from `SmallCategory` — was not available along
`f_small`: the type of objects of the site is not `u`-small.  It is only essentially `u`-small,
which is what
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesGeneral` asks for.

## Main definitions

* `AlgebraicGeometry.smallEtalePushforwardModules`: the pushforward
  `f_{small,*} : Mod(𝒪_{X_étale}) ⥤ Mod(𝒪_{Y_étale})`.
* `AlgebraicGeometry.smallEtalePullbackModules`: the pullback
  `f_{small}^* : Mod(𝒪_{Y_étale}) ⥤ Mod(𝒪_{X_étale})`.
* `AlgebraicGeometry.smallEtalePullbackAdjPushforwardModules`: the adjunction
  `f_{small}^* ⊣ f_{small,*}` of Stacks 03D7.

## Main results

* `AlgebraicGeometry.smallEtaleRingedSite_essentiallySmall`,
  `AlgebraicGeometry.smallEtaleRingedSite_locallySmall`,
  `AlgebraicGeometry.smallEtaleRingedSite_hasWeakSheafify` and
  `AlgebraicGeometry.smallEtaleRingedSite_wEqualsLocallyBijective`: the smallness and
  sheafification hypotheses of the small étale site, restated for the projections of
  `AlgebraicGeometry.smallEtaleRingedSite`.
* `AlgebraicGeometry.smallEtalePullbackModules_additive` and
  `AlgebraicGeometry.smallEtalePushforwardModules_additive`: both functors are additive.

## Implementation notes

`AlgebraicGeometry.smallEtaleRingedSite` is a `def`, so instance search does not see through its
projections `.C` and `.J`; the four instances below restate for those projections what is
already known of `AlgebraicGeometry.SmallEtale` and `AlgebraicGeometry.SmallEtale.topology`.
This is the pattern of `AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify` for the
small étale site of an algebraic space.

The two functors are those of the morphism of ringed topoi underlying `f_small`, so they are
stated between the categories of sheaves of modules over
`AlgebraicGeometry.RingedSite.ringSheaf` of the two ringed sites, which is the sheaf of rings
over which sheaves of modules on a ringed site are taken.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The small étale site of a scheme is locally small in the universe of its structure rings,
stated for the projection of `AlgebraicGeometry.smallEtaleRingedSite`, which instance search
does not unfold. -/
instance smallEtaleRingedSite_locallySmall :
    LocallySmall.{u} (smallEtaleRingedSite B S hS).C :=
  inferInstanceAs (LocallySmall.{u} (SmallEtale B S hS))

/-- Presheaves of abelian groups on the small étale site of a scheme admit sheafification,
stated for the topology of `AlgebraicGeometry.smallEtaleRingedSite`, which instance search does
not unfold. -/
instance smallEtaleRingedSite_hasWeakSheafify :
    HasWeakSheafify (smallEtaleRingedSite B S hS).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{u})

/-- The sheaf condition for `CommRingCat`-valued sheaves on the small étale site of a scheme is
preserved by forgetting commutativity, stated for the topology of
`AlgebraicGeometry.smallEtaleRingedSite`, which instance search does not unfold. -/
instance smallEtaleRingedSite_hasSheafCompose :
    (smallEtaleRingedSite B S hS).J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
  (smallEtaleRingedSite B S hS).hasSheafCompose_forget₂_ringCat

variable {X Y : B.Scheme}

/-- **Stacks 03D6 part (1) for the small étale sites of schemes.** The pushforward
`f_{small,*} : Mod(𝒪_{X_étale}) ⥤ Mod(𝒪_{Y_étale})` of sheaves of modules along the morphism of
small étale ringed sites of a morphism of schemes: the underlying sheaf of abelian groups is the
direct image, and the module structure is restriction of scalars along `f_{small}^♯`. -/
@[stacks 03D6 "part (1): pushforward of sheaves of modules along the morphism of small étale
ringed sites of a morphism of schemes"]
def smallEtalePushforwardModules (a : X ⟶ Y) :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B X.obj X.property).O) ⥤
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B Y.obj Y.property).O) :=
  (smallEtaleRingedSiteHom B a).pushforwardModulesGeneral

/-- **Stacks 03D6 part (2) for the small étale sites of schemes.** The pullback
`f_{small}^* : Mod(𝒪_{Y_étale}) ⥤ Mod(𝒪_{X_étale})` of sheaves of modules along the morphism of
small étale ringed sites of a morphism of schemes, characterised as the left adjoint of the
pushforward.

The small étale site is not small in the universe of its structure rings, only essentially so,
which is why this is not an instance of Mathlib's `SheafOfModules.pullback` with its
`SmallCategory` hypothesis. -/
@[stacks 03D6 "part (2): pullback of sheaves of modules along the morphism of small étale ringed
sites of a morphism of schemes, whose site is essentially small rather than small in the universe
of the structure rings"]
def smallEtalePullbackModules (a : X ⟶ Y) :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B Y.obj Y.property).O) ⥤
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B X.obj X.property).O) :=
  (smallEtaleRingedSiteHom B a).pullbackModulesGeneral

/-- **Stacks 03D7 for the small étale sites of schemes.** The pullback of sheaves of modules
along `f_small` is left adjoint to the pushforward. -/
@[stacks 03D7 "the small étale sites of schemes"]
def smallEtalePullbackAdjPushforwardModules (a : X ⟶ Y) :
    smallEtalePullbackModules B a ⊣ smallEtalePushforwardModules B a :=
  (smallEtaleRingedSiteHom B a).pullbackAdjPushforwardModulesGeneral

/-- The pushforward of sheaves of modules along `f_small` is additive. -/
instance smallEtalePushforwardModules_additive (a : X ⟶ Y) :
    (smallEtalePushforwardModules B a).Additive :=
  RingedSite.HomGeneral.pushforwardModulesGeneral_additive (smallEtaleRingedSiteHom B a)

/-- The pullback of sheaves of modules along `f_small` is additive, being a left adjoint of the
additive pushforward. -/
instance smallEtalePullbackModules_additive (a : X ⟶ Y) :
    (smallEtalePullbackModules B a).Additive :=
  RingedSite.HomGeneral.pullbackModulesGeneral_additive (smallEtaleRingedSiteHom B a)

end AlgebraicGeometry

end
