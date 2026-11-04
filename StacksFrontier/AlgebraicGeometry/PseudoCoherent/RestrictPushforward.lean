module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardOXMod
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import StacksFrontier.Topology.Sheaves.RingedSpace.RestrictMorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `(i_*F)|_U ≅ (i|_V)_*(F|_V)`: pushforward of modules commutes with restriction

Let `i : Z ⟶ X` be a morphism of ringed spaces, let `U` be an open subspace of `X` and let
`V = i⁻¹U`. Restricting a pushed-forward `𝒪_Z`-module to `U` is the same as restricting it to
`V` and pushing forward along the restricted morphism `i|_V : Z|_V ⟶ X|_U` of
`AlgebraicGeometry.RingedSpace.restrictHom`. This file proves that, as an isomorphism of
functors `Mod(𝒪_Z) ⥤ Mod(𝒪_{X|U})`.

This is the base-change square that makes `Ri_*` interact with a localization step. The
pseudo-coherence predicate `AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom` is local
on `X` and phrased through `restrictModules X U`, while both halves of the induction in Stacks
09VA shrink `X`; the square below is what transports an approximation of `E` over `V` to an
approximation of `i_*E` over `U` and back.

## Main definitions

* `AlgebraicGeometry.RingedSpace.restrictPushforwardIso`:
  `i_* ⋙ (·)|_U ≅ (·)|_V ⋙ (i|_V)_*`.
* `AlgebraicGeometry.RingedSpace.restrictPushforwardStructureModuleIso`:
  `(i_*𝒪_Z)|_U ≅ (i|_V)_*𝒪_{Z|V}`, the square at the structure module.
* `AlgebraicGeometry.RingedSpace.restrictPushforwardOpens` and
  `AlgebraicGeometry.RingedSpace.pushforwardRestrictOpens` are the two functors on opens
  `W ↦ i⁻¹(ι_U W)` and `W ↦ ι_V((i|_V)⁻¹W)` that the two legs of the square push forward along,
  and `AlgebraicGeometry.RingedSpace.restrictPushforwardOpensIso` identifies them.

## Main results

* `AlgebraicGeometry.RingedSpace.pushforward_comp_restrictModules_eq` and
  `AlgebraicGeometry.RingedSpace.restrictModules_comp_pushforward_eq`: each of the two legs of
  the square is, *by definition*, a single pushforward of sheaves of modules.
* `AlgebraicGeometry.RingedSpace.restrictPushforwardData_eq`: the two morphisms of sheaves of
  rings that the two legs push forward along agree once the two functors on opens are identified
  by `restrictPushforwardOpensIso`. This is where the content of `restrictHom` is used, and it
  holds by `rfl`.

## Implementation notes

Restriction of modules to an open subspace and pushforward of modules along a morphism of
ringed spaces are both instances of `CategoryTheory.SheafOfModules.pushforward`: the first along
the covariant functor `ι_U : Opens U ⥤ Opens X` with the identity map of structure sheaves, the
second along `Opens.map i : Opens X ⥤ Opens Z` with `i^♯`. Mathlib's
`CategoryTheory.SheafOfModules.pushforwardComp` is `Iso.refl`, so each leg of the square *equals*
one pushforward along the composite datum; the two composite data differ only in the functor on
opens, by `restrictPushforwardOpensIso`, and
`CategoryTheory.SheafOfModules.pushforwardCongr₂` turns that into the isomorphism. No
computation on sections is performed anywhere.

Two kinds of friction had to be handled.

First, `CategoryTheory.Functor.IsContinuous` for the functors on opens is not an instance in
this development: `AlgebraicGeometry.RingedSpace.restrictModules` supplies it with a local
`letI`. The three continuity facts needed here are therefore proved and registered as *local*
instances. The last of them is obtained from the previous one by
`CategoryTheory.Functor.isContinuous_of_iso` rather than by
`CategoryTheory.Functor.isContinuous_comp`, which saves repeating the argument.

Second, the site of `X|_U` has two definitionally equal spellings — through
`(X.restrict U.isOpenEmbedding).carrier` and through `(Opens.toTopCat X.carrier).obj U`, the
latter being what `Topology.IsOpenEmbedding.functor` records — and which one a statement uses
depends on the order in which its arguments are elaborated. Typeclass resolution unfolds only at
reducible transparency and does not identify them, so a continuity instance stated at one
spelling does not discharge a goal at the other. Every functor on opens appearing here is
therefore given a name whose declared type fixes the first spelling
(`restrictOpensInclusion`, `restrictPushforwardOpens`, `pushforwardRestrictOpens`), and the
bodies rely on definitional equality, which is checked at default transparency and does see
through it.

## References

* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Lemma 17.6.1 (Tag 01AX)](https://stacks.math.columbia.edu/tag/01AX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) (U : Opens X.carrier)

/-! ### The two functors on opens -/

/-- The inclusion functor `ι_U : Opens U ⥤ Opens X` of an open subspace of a ringed space, with
its source written as the site of the restricted ringed space `X|_U`. -/
public def restrictOpensInclusion (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    Opens (X.restrict U.isOpenEmbedding).carrier ⥤ Opens X.carrier :=
  U.isOpenEmbedding.functor

/-- `W ↦ i⁻¹(ι_U W)`, the functor `Opens U ⥤ Opens Z` that the leg `i_* ⋙ (·)|_U` of the square
pushes forward along. -/
public def restrictPushforwardOpens :
    Opens (X.restrict U.isOpenEmbedding).carrier ⥤ Opens Z.carrier :=
  restrictOpensInclusion X U ⋙ Opens.map i.hom.base

/-- `W ↦ ι_V((i|_V)⁻¹W)`, the functor `Opens U ⥤ Opens Z` that the leg `(·)|_V ⋙ (i|_V)_*` of
the square pushes forward along. -/
public def pushforwardRestrictOpens :
    Opens (X.restrict U.isOpenEmbedding).carrier ⥤ Opens Z.carrier :=
  Opens.map (restrictHom i U).hom.base ⋙
    ((Opens.map i.hom.base).obj U).isOpenEmbedding.functor

/-- `AlgebraicGeometry.RingedSpace.restrictOpensIso` with both functors named, so that the site
`Opens U` is spelled through the carrier of the restricted ringed space throughout. -/
public def restrictPushforwardOpensIso :
    pushforwardRestrictOpens i U ≅ restrictPushforwardOpens i U :=
  restrictOpensIso i U

/-! ### Continuity of the functors on opens -/

/-- The inclusion functor of an open subspace of a ringed space is continuous for the
open-cover topologies.

This is Mathlib's `Topology.IsOpenEmbedding.functor_isContinuous`; it is restated because the
pseudo-coherence development does not have it as an instance. -/
@[sga "4 III 1.9.2" "special case"]
public theorem isContinuous_restrictOpensInclusion (X : RingedSpace.{u, u})
    (U : Opens X.carrier) :
    (restrictOpensInclusion X U).IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology X.carrier) :=
  U.isOpenEmbedding.functor_isContinuous

/-- `restrictPushforwardOpens` is continuous, being a composite of continuous functors. -/
public theorem isContinuous_restrictPushforwardOpens :
    (restrictPushforwardOpens i U).IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology Z.carrier) :=
  let := isContinuous_restrictOpensInclusion X U
  Functor.isContinuous_comp (restrictOpensInclusion X U) (Opens.map i.hom.base)
    (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
    (Opens.grothendieckTopology X.carrier)
    (Opens.grothendieckTopology Z.carrier)

/-- `pushforwardRestrictOpens` is continuous, being isomorphic to `restrictPushforwardOpens`
by `restrictPushforwardOpensIso`. -/
public theorem isContinuous_pushforwardRestrictOpens :
    (pushforwardRestrictOpens i U).IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology Z.carrier) :=
  let := isContinuous_restrictPushforwardOpens i U
  Functor.isContinuous_of_iso (restrictPushforwardOpensIso i U).symm
    (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
    (Opens.grothendieckTopology Z.carrier)

attribute [local instance] isContinuous_restrictOpensInclusion
  isContinuous_restrictPushforwardOpens
  isContinuous_pushforwardRestrictOpens

/-! ### The two legs of the square as single pushforwards -/

/-- The morphism of sheaves of rings on `U` that the leg `i_* ⋙ (·)|_U` of the square pushes
forward along: the identity of `𝒪_{X|U}` followed by the restriction to `U` of `i^♯`. -/
public def restrictPushforwardData :
    structureSheafRing (X.restrict U.isOpenEmbedding) ⟶
      ((restrictPushforwardOpens i U).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
        (Opens.grothendieckTopology Z.carrier)).obj (structureSheafRing Z) :=
  𝟙 (structureSheafRing (X.restrict U.isOpenEmbedding)) ≫
    ((restrictOpensInclusion X U).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology X.carrier)).map (structureSheafHom i)

/-- The morphism of sheaves of rings on `U` that the leg `(·)|_V ⋙ (i|_V)_*` of the square
pushes forward along: the structure-sheaf map of `i|_V` followed by the identity of
`𝒪_{Z|V}`. -/
public def pushforwardRestrictData :
    structureSheafRing (X.restrict U.isOpenEmbedding) ⟶
      ((pushforwardRestrictOpens i U).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
        (Opens.grothendieckTopology Z.carrier)).obj (structureSheafRing Z) :=
  structureSheafHom (restrictHom i U) ≫
    ((Opens.map (restrictHom i U).hom.base).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology
        (Z.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding).carrier)).map
      (𝟙 (structureSheafRing (Z.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)))

/-- **Pushing forward along `i` and then restricting to `U` is one pushforward**, along
`restrictPushforwardOpens` and the datum `restrictPushforwardData`. -/
public theorem pushforward_comp_restrictModules_eq :
    pushforwardOXMod i ⋙ restrictModules X U =
      SheafOfModules.pushforward.{u} (F := restrictPushforwardOpens i U)
        (restrictPushforwardData i U) :=
  rfl

/-- **Restricting to `V` and then pushing forward along `i|_V` is one pushforward**, along
`pushforwardRestrictOpens` and the datum `pushforwardRestrictData`. -/
public theorem restrictModules_comp_pushforward_eq :
    restrictModules Z ((Opens.map i.hom.base).obj U) ⋙ pushforwardOXMod (restrictHom i U) =
      SheafOfModules.pushforward.{u} (F := pushforwardRestrictOpens i U)
        (pushforwardRestrictData i U) :=
  rfl

/-- **The two data agree.** Transporting `restrictPushforwardData` along
`restrictPushforwardOpensIso` gives `pushforwardRestrictData`.

This is the whole content of the square, and it holds by `rfl`: the structure-sheaf map of
`i|_V` is by construction `i^♯` over `ι_U W` followed by restriction along
`AlgebraicGeometry.RingedSpace.restrictOpensIso`. -/
public theorem restrictPushforwardData_eq :
    restrictPushforwardData i U ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (restrictPushforwardOpensIso i U).hom RingCat.{u}
          (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
          (Opens.grothendieckTopology Z.carrier)).app (structureSheafRing Z) =
      pushforwardRestrictData i U :=
  rfl

/-! ### The square -/

/-- **`(i_*F)|_U ≅ (i|_V)_*(F|_V)`**, naturally in the `𝒪_Z`-module `F`: pushing forward along
a morphism of ringed spaces `i : Z ⟶ X` and restricting to an open subspace `U` of `X` agrees
with restricting to `V = i⁻¹U` and pushing forward along the restricted morphism
`i|_V : Z|_V ⟶ X|_U`.

This is the base-change square for `AlgebraicGeometry.RingedSpace.restrictHom`, and it is what
a localization step of Stacks 09VA needs: the pseudo-coherence predicate is phrased through
`restrictModules`, while the induction shrinks the ambient space. -/
public def restrictPushforwardIso :
    pushforwardOXMod i ⋙ restrictModules X U ≅
      restrictModules Z ((Opens.map i.hom.base).obj U) ⋙ pushforwardOXMod (restrictHom i U) :=
  eqToIso (pushforward_comp_restrictModules_eq i U) ≪≫
    SheafOfModules.pushforwardCongr₂ (restrictPushforwardData i U)
      (restrictPushforwardOpensIso i U) (restrictPushforwardData_eq i U) ≪≫
    eqToIso (restrictModules_comp_pushforward_eq i U).symm

/-- **`(i_*𝒪_Z)|_U ≅ (i|_V)_*𝒪_{Z|V}`.** The hypothesis of Stacks 09VA — that `i_*𝒪_Z` is a
pseudo-coherent `𝒪_X`-module — localizes: restricting `i_*𝒪_Z` to `U` gives the pushforward of
the structure sheaf of `Z|_V` along `i|_V`.

This is `restrictPushforwardIso` at the structure module, using that restriction to an open
subspace carries `𝒪_Z` to `𝒪_{Z|V}` by definition. -/
public def restrictPushforwardStructureModuleIso :
    (restrictModules X U).obj (pushforwardStructureModule i) ≅
      pushforwardStructureModule (restrictHom i U) :=
  (restrictPushforwardIso i U).app (structureModule Z)

end AlgebraicGeometry.RingedSpace

end
