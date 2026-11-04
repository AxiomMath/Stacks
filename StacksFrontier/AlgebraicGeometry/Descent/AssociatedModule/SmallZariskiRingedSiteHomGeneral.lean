module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesZariskiExists
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposPullbackEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSiteGeneral

/-!
# `id_{small, Zar, Zar} : (S_Zar, 𝒪) ⟶ (S_Zar, 𝒪_S)` as a morphism of ringed sites

Remark 03FH offers two morphisms of ringed sites along which `𝓕 ↦ 𝓕^a` is a pullback; the
second of them, at `τ = Zariski`, is `id_{small, Zar, Zar} : (S_Zar, 𝒪) ⟶ (S_Zar, 𝒪_S)`.  Its
geometric datum is `AlgebraicGeometry.SmallZariski.opensToSmallZariski`, the inclusion of the
opens of the space of `S` into the small Zariski site — an *equivalence*, being the inverse of
the open-image comparison of Stacks 020X — and its structure map is
`AlgebraicGeometry.smallZariskiCommStructureIso`, the identification of the sections of `𝒪_S`
over an open with the global functions of the corresponding open subscheme.  The pullback of
sheaves of modules along it is `AlgebraicGeometry.SmallZariski.associatedModule`.

This module packages that datum as an `AlgebraicGeometry.RingedSite.HomGeneral`, whose two
sites have objects in different universes: `AlgebraicGeometry.smallZariskiRingedSite` is a
`RingedSite.{u + 1, u, u}`, whereas the small Zariski site presented by the opens of the
underlying space is a `RingedSite.{u, u, u}`.

## Main definitions

* `AlgebraicGeometry.SmallZariski.commStructureMap`: the structure map `𝒪_S ⟶ f_* 𝒪` in
  `CommRingCat`, which is `AlgebraicGeometry.smallZariskiCommStructureIso` read as a morphism
  into the pushforward.
* `AlgebraicGeometry.SmallZariski.toOpensRingedSiteHom`: Remark 03FH's `id_{small, Zar, Zar}`
  as a morphism of ringed sites in the sense of Stacks 03AD part (2), at independent object
  universes.
* `AlgebraicGeometry.SmallZariski.toOpensToposHom`: the morphism of topoi underlying it.

## Main results

* `AlgebraicGeometry.smallZariskiRingedSite_O_obj`,
  `AlgebraicGeometry.smallZariskiRingedSite_ringSheaf`: the structure sheaf of the small Zariski
  ringed site has `AlgebraicGeometry.smallZariskiCommRings` as underlying presheaf, and its
  `RingCat`-valued reading is the structure sheaf of Stacks 03DU (2).
* `AlgebraicGeometry.SmallZariski.opensToSmallZariski_isMorphismOfSites`: the inclusion of the
  opens of the space of `S` into the small Zariski site defines a morphism of sites, for sheaves
  of sets valued in the universe of the sections of the structure sheaves.
* `AlgebraicGeometry.SmallZariski.pullbackToposGeneral_toOpensRingedSiteHom`: the pullback of
  sheaves of modules along `toOpensRingedSiteHom`, in the general form of
  `AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral`, is the associated-module functor
  `𝓕 ↦ 𝓕^a` of Stacks 03DU (4) at `τ = Zariski`.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 00XC](https://stacks.math.columbia.edu/tag/00XC)
* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The structure sheaf of the small Zariski ringed site -/

/-- The structure sheaf of `AlgebraicGeometry.smallZariskiRingedSite` has
`AlgebraicGeometry.smallZariskiCommRings` as its underlying presheaf: the two spellings of the
presheaf of global functions on the small Zariski site — through the canonical functor to
schemes, and through the inclusion into the big Zariski category followed by
`CategoryTheory.Over.post` — agree definitionally. -/
public theorem smallZariskiRingedSite_O_obj :
    (smallZariskiRingedSite B S hS).O.obj = smallZariskiCommRings B S hS :=
  rfl

/-- Forgetting commutativity in `(AlgebraicGeometry.smallZariskiRingedSite B S hS).O` returns
the structure sheaf `AlgebraicGeometry.SmallZariski.structureSheaf` of Stacks 03DU (2). -/
public theorem smallZariskiRingedSite_ringSheaf :
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallZariskiRingedSite B S hS).O) = SmallZariski.structureSheaf B S hS :=
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The site condition -/

/-- The inclusion of the opens of the space of `S` into the small Zariski site of `S` defines a
morphism of sites, for sheaves of sets valued in the universe `u` of the sections of the
structure sheaves. -/
public instance opensToSmallZariski_isMorphismOfSites :
    IsMorphismOfSites.{u} (opensToSmallZariski B S hS)
      (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  let e := Functor.IsDenseSubsite.sheafEquiv (Opens.grothendieckTopology ↥S)
    (topology B S hS) (opensToSmallZariski B S hS) (Type u)
  { __ := (inferInstance : (opensToSmallZariski B S hS).IsContinuous
      (Opens.grothendieckTopology ↥S) (topology B S hS))
    hasExactLeftAdjoint := ⟨e.functor, ⟨e.toAdjunction⟩, inferInstance⟩ }

/-! ### The morphism of ringed sites -/

/-- The comparison of structure sheaves of commutative rings along the inclusion of the opens of
the space of `S` into the small Zariski site of `S`: over an open `U` it is the identification
of the sections of `𝒪_S` over `U` with the global functions of the open subscheme `U`, that
is, `AlgebraicGeometry.smallZariskiCommStructureIso` read as a morphism into the pushforward. -/
public def commStructureMap :
    S.zariskiRingedSite.O ⟶
      ((opensToSmallZariski B S hS).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ↥S) (topology B S hS)).obj
          (smallZariskiRingedSite B S hS).O :=
  ObjectProperty.homMk (smallZariskiCommStructureIso B S hS).hom

/-- The underlying morphism of presheaves of `commStructureMap` is the comparison isomorphism
`smallZariskiCommStructureIso`. -/
@[simp]
public theorem commStructureMap_hom :
    (commStructureMap B S hS).hom = (smallZariskiCommStructureIso B S hS).hom :=
  rfl

/-- Remark 03FH's `id_{small, Zar, Zar} : (S_Zar, 𝒪) ⟶ (S_Zar, 𝒪_S)` as a morphism of ringed
sites at independent object universes: the inclusion of the opens of the space of `S` into the
small Zariski site, a morphism of sites at the universe of the structure rings, together with
the identification of the sections of `𝒪_S` over an open with the functions on it. -/
public def toOpensRingedSiteHom :
    RingedSite.HomGeneral (smallZariskiRingedSite B S hS) S.zariskiRingedSite where
  u := opensToSmallZariski B S hS
  isMorphismOfSites := opensToSmallZariski_isMorphismOfSites B S hS
  fsharp := commStructureMap B S hS

/-- The functor of sites underlying `toOpensRingedSiteHom` is `opensToSmallZariski`. -/
@[simp]
public theorem toOpensRingedSiteHom_u :
    (toOpensRingedSiteHom B S hS).u = opensToSmallZariski B S hS := rfl

/-- The map of structure sheaves underlying `toOpensRingedSiteHom` is `commStructureMap`. -/
@[simp]
public theorem toOpensRingedSiteHom_fsharp :
    (toOpensRingedSiteHom B S hS).fsharp = commStructureMap B S hS := rfl

/-- The morphism of topoi
`Sh(S_Zar) ⟶ Sh(S_Zar)` underlying the morphism of ringed sites of Remark 03FH at
`τ = Zariski`. -/
public abbrev toOpensToposHom :
    MorphismOfTopoi (Sheaf (smallZariskiRingedSite B S hS).J (Type u))
      (Sheaf S.zariskiRingedSite.J (Type u)) :=
  (toOpensRingedSiteHom B S hS).toposHom

/-! ### The pullback of modules along it -/

/-- The pullback of sheaves of modules of Stacks 03D6 part (2) along the morphism of ringed
sites of Remark 03FH at `τ = Zariski`, in the general form of
`AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral`, is the associated-module functor
`𝓕 ↦ 𝓕^a` of Stacks 03DU (4). -/
public theorem pullbackToposGeneral_toOpensRingedSiteHom :
    (toOpensRingedSiteHom B S hS).toRingedToposSiteHom.pullbackToposGeneral =
      associatedModule B S hS :=
  rfl

end AlgebraicGeometry.SmallZariski

end
