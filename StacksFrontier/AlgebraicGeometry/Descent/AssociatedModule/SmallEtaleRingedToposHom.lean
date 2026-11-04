module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.SmallAffineRingedTopos
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing

/-!
# The morphism of ringed sites `(S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)`

Stacks Remark 070R makes each of the morphisms of sites of Topologies, Section 03FE into a
morphism of *ringed* sites. Its item (26) is `X_étale → Y_Zar`, which at `X = Y = S` and
`f = id` is the morphism `id_{small, étale, Zar} : S_étale → S_Zar` of Stacks 070S (2) and
Remark 03FH. This module constructs that morphism.

The underlying continuous functor is the inclusion
`AlgebraicGeometry.SmallEtale.opensToSmallEtale` of the small Zariski site of `S`; the structure
sheaf of commutative rings of the small étale site is
`(AlgebraicGeometry.SmallEtale.ringedTopos B S hS).O`; and the comparison of structure sheaves
over an open `U` is the identification `AlgebraicGeometry.Scheme.Opens.topIso` of `Γ(𝒪_S, U)`
with the global functions of the open subscheme `U`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.commRingStructureMap`: the comparison of structure sheaves of
  *commutative* rings along the inclusion of the small Zariski site of `S` into the small étale
  site of `S`.
* `AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom`: **Stacks 070R**, the morphism of
  ringed sites `(S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)`. This is also **Stacks 08H7**, the `ε` of
  Equation 75.4.0.1, which the source introduces as the morphism denoted
  `id_{small, étale, Zar}` in Descent, Lemma 070S.

## Main results

* `AlgebraicGeometry.SmallEtale.ringedTopos_O`: the structure sheaf of commutative rings of the
  ringed topos of the small étale site is the structure sheaf
  `AlgebraicGeometry.SmallEtale.commRingStructureSheaf` of Stacks 04HZ.
* `AlgebraicGeometry.SmallEtale.ringedTopos_ringSheaf`: forgetting commutativity recovers the
  `RingCat`-valued structure sheaf `AlgebraicGeometry.SmallEtale.structureSheaf` of
  Stacks 03DU.
* `AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom_fSharpRing`: the structure map of the
  morphism of ringed sites, read on sheaves of not necessarily commutative rings, is
  `AlgebraicGeometry.SmallEtale.structureMap`.
* `AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom_pushforwardTopos`: the pushforward of
  sheaves of modules along the morphism of ringed sites is
  `AlgebraicGeometry.SmallEtale.restrictModule`, the right adjoint of the associated-module
  functor of Stacks 03DU (4).

## Implementation notes

The small Zariski site `S_Zar` is presented by the opens of the underlying space of `S`, so its
objects form a type one universe *below* those of the small étale site. The two ringed topoi
therefore have different object universes, and the morphism is recorded as an
`AlgebraicGeometry.RingedToposSiteHom`, whose geometric datum is exactly a continuous functor
between the underlying sites in the opposite direction, as in the source's convention for a
morphism of sites. `AlgebraicGeometry.RingedSite.Hom` cannot be used: it requires the objects
and the morphisms of both sites to live in one universe, which `S_Zar` and `S_étale` do not.

For the same reason the *pullback* of sheaves of modules along this morphism is not taken as
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`, which is available only when the two
ringed topoi share all three universes. The pullback is instead
`AlgebraicGeometry.SmallEtale.associatedModule`, formed over
`AlgebraicGeometry.SmallEtale.structureMap`, and
`AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom_fSharpRing` says that that is the
structure map of this morphism; so the associated-module functor of Stacks 03DU (4) is the
pullback of modules along the morphism packaged here, as Remark 03FH says it is.

The two `CommRingCat`-valued structure sheaves of the small étale site,
`AlgebraicGeometry.SmallEtale.commRingStructureSheaf`, for the locally ringed site of
Stacks 04HZ, and the structure sheaf of `AlgebraicGeometry.SmallEtale.ringedTopos`, for the
equivalence of Stacks 0GZW, are the same sheaf, with the same underlying presheaf
`T ↦ Γ(T, 𝒪_T)` and proof-irrelevant sheaf conditions:
`AlgebraicGeometry.SmallEtale.ringedTopos_O`.

The identification of `ε⁻¹𝒪_Zar` with the étale sheafification of
`(V → S) ↦ 𝒪_S(\mathrm{im}\, V)` is not in this module, but it is in the development:
`AlgebraicGeometry.SmallEtale.inverseImageIso` with
`AlgebraicGeometry.SmallEtale.isIso_inverseImageIso`, obtained from
`AlgebraicGeometry.SmallEtale.inverseImageAuxIso`; both `ε⁻¹` and that sheafification are left
adjoint to the pushforward along `opensToSmallEtale`.

That identification is **not** Stacks 070S (2). 070S (2) identifies the *module* pullback `ε^*𝓕`
of an `𝒪_S`-module with the étale sheafification of `(f : T → S) ↦ Γ(T, f^*𝓕)`; at `𝓕 = 𝒪_S` it
is the tautology `ε^*𝒪_{S_Zar} = 𝒪_{S_étale}`, since `ε^*` tensors over `ε⁻¹𝒪_{S_Zar}` up to
`𝒪_{S_étale}`. It says nothing about the *ring-level* inverse image `ε⁻¹𝒪_{S_Zar}`, which is
**not** `𝒪_{S_étale}`: the structure map `AlgebraicGeometry.SmallEtale.inverseImageStructureMap`
between them is asserted by Stacks 0GNA to be flat, not invertible, and over a field with
nontrivial Galois group the two already differ. So no argument may quote 070S (2) for
`ε⁻¹𝒪_{S_Zar} ≅ 𝒪_{S_étale}`.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The structure sheaf of commutative rings and its underlying sheaf of rings -/

/-- The structure sheaf of commutative rings of the ringed topos of the small étale site of `S`
is the structure sheaf of commutative rings used for the locally ringed site of Stacks 04HZ. -/
@[simp]
public theorem ringedTopos_O :
    (ringedTopos B S hS).O = commRingStructureSheaf B S hS := rfl

/-- **Forgetting commutativity in the structure sheaf of the small étale site of `S` recovers
the structure sheaf of rings of Stacks 03DU.** -/
@[simp]
public theorem ringedTopos_ringSheaf :
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos B S hS).O) = structureSheaf B S hS := rfl

/-- The sheaf of rings underlying the structure sheaf of commutative rings of the small étale
site of `S`, written with `sheafCompose`, is the structure sheaf of rings of Stacks 03DU. -/
public theorem sheafCompose_forget₂_commRingStructureSheaf :
    (sheafCompose (topology B S hS) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (commRingStructureSheaf B S hS) = structureSheaf B S hS := rfl

/-! ### The morphism of ringed sites `(S_étale, 𝒪) → (S_Zar, 𝒪_S)` -/

/-- The comparison of structure sheaves of *commutative* rings along the inclusion of the small
Zariski site of `S` into the small étale site of `S`: over an open `U` it is the identification
of the sections of `𝒪_S` over `U` with the global functions of the open subscheme `U`. -/
public noncomputable def commRingStructureMap :
    S.zariskiRingedTopos.O ⟶
      ((opensToSmallEtale B S hS).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ↥S) (topology B S hS)).obj (ringedTopos B S hS).O where
  hom :=
    { app := fun U => (Scheme.Opens.topIso U.unop).inv
      naturality := fun _ _ h =>
        (Scheme.Opens.topIso_inv_appTop (X := S) (leOfHom h.unop)).symm }

/-- Over an open `U`, `commRingStructureMap` is the inverse of `Scheme.Opens.topIso U`. -/
@[simp]
public theorem commRingStructureMap_hom_app (U : (S.Opens)ᵒᵖ) :
    (commRingStructureMap B S hS).hom.app U = (Scheme.Opens.topIso U.unop).inv := rfl

/-- **Stacks 070R.** The morphism of ringed sites
`id_{small, étale, Zar} : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)`: the continuous inclusion of the small
Zariski site of `S` into the small étale site of `S`, with structure map the identification of
the sections of `𝒪_S` over an open with the functions on it. -/
@[stacks 070R "the morphism of ringed sites `id_{small, étale, Zar} : (S_étale, 𝒪) → (S_Zar,
  𝒪_S)`, item (26) of the list of Topologies, Section 03FE at `f = id`"]
public noncomputable def toZariskiRingedToposHom :
    RingedToposSiteHom (ringedTopos B S hS) S.zariskiRingedTopos where
  u := opensToSmallEtale B S hS
  isContinuous := isContinuous_opensToSmallEtale B S hS
  fSharp := commRingStructureMap B S hS

/-! Equation 75.4.0.1, Stacks 08H7, is the morphism of ringed sites
`ε : (X_étale, 𝒪_étale) ⟶ (X_Zar, 𝒪_X)` for a scheme `X`, and the source introduces it as the
morphism "denoted `id_{small, étale, Zar}` in Descent, Lemma 070S". That is exactly
`AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom`. -/
add_to_stacks 08H7 AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom

/-- The continuous functor of `toZariskiRingedToposHom` is the inclusion of the small Zariski
site of `S` into the small étale site. -/
@[simp]
public theorem toZariskiRingedToposHom_u :
    (toZariskiRingedToposHom B S hS).u = opensToSmallEtale B S hS := rfl

/-- The structure map of `toZariskiRingedToposHom` is `commRingStructureMap`. -/
@[simp]
public theorem toZariskiRingedToposHom_fSharp :
    (toZariskiRingedToposHom B S hS).fSharp = commRingStructureMap B S hS := rfl

/-- **The structure map of the morphism of ringed sites, read on sheaves of not necessarily
commutative rings, is `AlgebraicGeometry.SmallEtale.structureMap`.** -/
@[simp]
public theorem toZariskiRingedToposHom_fSharpRing :
    (toZariskiRingedToposHom B S hS).fSharpRing = structureMap B S hS := rfl

/-- The pushforward of sheaves of modules along the morphism of ringed sites
`(S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` is restriction along the inclusion of the small Zariski site of
`S`, the right adjoint of the associated-module functor of Stacks 03DU (4). -/
public theorem toZariskiRingedToposHom_pushforwardTopos :
    (toZariskiRingedToposHom B S hS).pushforwardTopos = restrictModule B S hS := rfl

end AlgebraicGeometry.SmallEtale

end
