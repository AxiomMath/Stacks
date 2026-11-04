module

public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportRestrictToAnOpen

/-!
# Pushforward of sheaves of rings commutes with restriction to an open subspace

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `V ⊆ Y` be open. For a sheaf of rings `𝒜`
on `X` there is a canonical isomorphism

`(f_* 𝒜)|_V ≅ (f|_{f⁻¹V})_* (𝒜|_{f⁻¹V})`

of sheaves of rings on `V`, natural in `𝒜`: on sections over an open `W ⊆ V` both sides are
`𝒜(f⁻¹W)`, the two readings of `f⁻¹W` as an open of `X` being identified by
`Stacks.Cohomology.HigherDirectImage.restrictOpensIso`. This file supplies that isomorphism, as
an isomorphism of functors, and instantiates it at the pushed-forward structure sheaf `i_* 𝒪_Z`
of a closed quotient morphism of ringed spaces.

This is the ring-level counterpart of the module-level base change
`Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso`, and it is built from the same
identification of opens, so no new geometry enters: `(f_* 𝒜)|_V` and `(f|_{f⁻¹V})_*(𝒜|_{f⁻¹V})`
are the pushforwards of `𝒜` along the two composites of
`Stacks.Cohomology.HigherDirectImage.restrictOpensIso`, and
`CategoryTheory.Functor.sheafPushforwardContinuousIso` turns an isomorphism of continuous
functors between sites into an isomorphism of the pushforwards they induce.

## Main definitions

* `Stacks.Cohomology.HigherDirectImage.ringSheafPushforward` and
  `Stacks.Cohomology.HigherDirectImage.ringSheafRestriction`: pushforward of sheaves of rings
  along a morphism of ringed spaces, and restriction of sheaves of rings to an open subspace.
* `Stacks.Cohomology.HigherDirectImage.ringSheafPushforwardRestrictIso`: **the base-change
  isomorphism**, for an arbitrary sheaf of rings and with no hypothesis on `f`.
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.pushedRingSheafRestrictIso`:
  the same at `i_* 𝒪_Z`, identifying `(i_* 𝒪_Z)|_U` with the pushed-forward structure sheaf
  `(i|_{i⁻¹U})_* 𝒪_{Z|_{i⁻¹U}}` of the restricted situation
  `ClosedQuotientMorphismOfRingedSpaces.restrict`.

## Main results

* `Stacks.Cohomology.HigherDirectImage.ringSheafPushforwardRestrictIso_hom_app_hom_app`: on
  sections the isomorphism is the restriction map of `𝒜` along the identification of opens, so it
  is the identity on sections and not that identity composed with an automorphism.
* `ClosedQuotientMorphismOfRingedSpaces.pushedRingHom_comp_pushedRingSheafRestrictIso_inv`:
  **the comorphism is carried along**: the restriction to `U` of `𝒪_X ⟶ i_* 𝒪_Z` is the
  comorphism `𝒪_{X|_U} ⟶ (i|_{i⁻¹U})_* 𝒪_{Z|_{i⁻¹U}}` of the restricted situation, read through
  the isomorphism. So the two sheaves of rings are identified *as algebras over the restricted
  structure sheaf*.
* `Stacks.Cohomology.HigherDirectImage.ringSheafPushforwardRestrictIso_inv_app_hom_app`: the
  component on sections of the inverse of the base-change isomorphism.

## Implementation notes

The two pushforward functors are `CategoryTheory.Functor.sheafPushforwardContinuous` at the
functors on lattices of opens, rather than `RingedSpaceModuleAdjunction.pushOfRing` and the
restricted structure sheaf `OUSh`, because the composition and the transport isomorphisms
`CategoryTheory.Functor.sheafPushforwardContinuousComp` and
`CategoryTheory.Functor.sheafPushforwardContinuousIso` are stated there. Both spellings agree by
`rfl` — `ClosedQuotientMorphismOfRingedSpaces.pushedRingSheaf_eq` and
`Stacks.Cohomology.HigherDirectImage.ringSheaf_restrictToOpen` below say so — and those two
lemmas are the only reason the instantiation typechecks against the vocabulary of the closed
quotient morphism.

## References

* [Stacks Project, Tag 008Z](https://stacks.math.columbia.edu/tag/008Z)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.HigherDirectImage

/-! ### Pushforward and restriction of sheaves of rings -/

/-- **Pushforward of sheaves of rings along a morphism of ringed spaces**: the functor sending a
sheaf of rings `𝒜` on `X` to the sheaf `W ↦ 𝒜(f⁻¹W)` on `Y`. This is
`RingedSpaceModuleAdjunction.pushOfRing` read as a functor of the sheaf of rings. -/
def ringSheafPushforward {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y.carrier) RingCat.{u} :=
  (opensMap f).sheafPushforwardContinuous RingCat.{u} _ _

/-- **Restriction of sheaves of rings to an open subspace**: the functor sending a sheaf of rings
`𝒜` on `X` to the sheaf `W ↦ 𝒜(W)` on `V`, for `W` an open contained in `V`. -/
def ringSheafRestriction (X : RingedSpace.{u, u}) (V : Opens X) :
    Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology ((Opens.toTopCat _).obj V)) RingCat.{u} :=
  (jFun (asRingSheafedSpace X) V).sheafPushforwardContinuous RingCat.{u} _ _

/-- The structure sheaf of rings of an open subspace is the restriction of the structure sheaf of
rings of the ambient space. Both are precomposition of the presheaf with the inclusion of the
opens contained in `V`, so this holds by `rfl`; it is recorded because the two spellings occur in
the statements below and `rw` does not cross between them. -/
theorem ringSheaf_restrictToOpen (X : RingedSpace.{u, u}) (V : Opens X) :
    structureSheafRing (restrictToOpen X V) =
      (ringSheafRestriction X V).obj (structureSheafRing X) :=
  rfl

/-! ### The base-change isomorphism -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)

/-- **Pushforward of sheaves of rings commutes with restriction to an open subspace.** For a
sheaf of rings `𝒜` on `X`,

`(f_* 𝒜)|_V ≅ (f|_{f⁻¹V})_*(𝒜|_{f⁻¹V})`,

naturally in `𝒜` and with no hypothesis on `f` or on `V`. Both sides are the pushforward of `𝒜`
along one of the two composites identified by
`Stacks.Cohomology.HigherDirectImage.restrictOpensIso`: reading an open `W ⊆ V` as an open of `X`
by taking its image in `Y` and then the inverse image under `f`, or by taking its inverse image
under the restricted morphism and then including into `X`. -/
def ringSheafPushforwardRestrictIso :
    ringSheafPushforward f ⋙ ringSheafRestriction Y V ≅
      ringSheafRestriction X (preimageOpen f V) ⋙
        ringSheafPushforward (restrictedMorphism f V) :=
  Functor.sheafPushforwardContinuousComp' (restrictOpensIso f V) RingCat.{u} _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ RingCat.{u} _ _ _).symm

/-- **On sections the base-change isomorphism is the identity.** Its component at a sheaf of
rings `𝒜` and an open `W ⊆ V` is the restriction map of `𝒜` along the identification
`Stacks.Cohomology.HigherDirectImage.restrictOpensIso` of the two readings of `f⁻¹W` as an open of
`X`, which is an isomorphism of opens. This pins the comparison down and rules out composing it
with an automorphism of the structure sheaf. -/
theorem ringSheafPushforwardRestrictIso_hom_app_hom_app
    (A : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u})
    (W : (Opens ((Opens.toTopCat _).obj V))ᵒᵖ) :
    ((ringSheafPushforwardRestrictIso f V).hom.app A).hom.app W =
      A.obj.map ((restrictOpensIso f V).inv.app W.unop).op :=
  rfl

/-- **On sections the inverse of the base-change isomorphism is the identity too**: it is the
restriction map of `𝒜` along the other direction of the identification
`Stacks.Cohomology.HigherDirectImage.restrictOpensIso`. This is the component a consumer that
transports scalars *from* the restricted situation needs, and
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.descendRestrictScalars_compat`
is one. -/
theorem ringSheafPushforwardRestrictIso_inv_app_hom_app
    (A : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u})
    (W : (Opens ((Opens.toTopCat _).obj V))ᵒᵖ) :
    ((ringSheafPushforwardRestrictIso f V).inv.app A).hom.app W =
      A.obj.map ((restrictOpensIso f V).hom.app W.unop).op :=
  rfl

end Stacks.Cohomology.HigherDirectImage

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

open Stacks.Cohomology.HigherDirectImage

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u}) (U : Opens S.X)

/-- `i_* 𝒪_Z` is the pushforward of the structure sheaf of rings of `Z` along `i`, at the
spelling of `Stacks.Cohomology.HigherDirectImage.ringSheafPushforward`. True by `rfl`; recorded
so that the instantiation below can be stated in the vocabulary of the closed quotient
morphism. -/
theorem pushedRingSheaf_eq :
    S.pushedRingSheaf = (ringSheafPushforward S.i).obj (structureSheafRing S.Z) :=
  rfl

/-- **The two sheaves of rings over which the two descent functors are taken are the same.** The
restriction to `U` of `i_* 𝒪_Z` is the pushed-forward structure sheaf
`(i|_{i⁻¹U})_* 𝒪_{Z|_{i⁻¹U}}` of the restricted situation
`ClosedQuotientMorphismOfRingedSpaces.restrict`. This is
`Stacks.Cohomology.HigherDirectImage.ringSheafPushforwardRestrictIso` at `𝒪_Z`. -/
def pushedRingSheafRestrictIso :
    (ringSheafRestriction S.X U).obj S.pushedRingSheaf ≅ (S.restrict U).pushedRingSheaf :=
  (ringSheafPushforwardRestrictIso S.i U).app (structureSheafRing S.Z)

/-- **The comorphism is carried along by the identification.** Composing the comorphism
`𝒪_{X|_U} ⟶ (i|_{i⁻¹U})_* 𝒪_{Z|_{i⁻¹U}}` of the restricted situation with the inverse of
`ClosedQuotientMorphismOfRingedSpaces.pushedRingSheafRestrictIso` gives the restriction to `U` of
the comorphism `𝒪_X ⟶ i_* 𝒪_Z` of `i`. So `(i_* 𝒪_Z)|_U` and `(i|_{i⁻¹U})_* 𝒪_{Z|_{i⁻¹U}}` agree
as algebras over the structure sheaf of `X|_U`, not merely as sheaves of rings.

This is `Stacks.Cohomology.HigherDirectImage.structureSheafHom_restrictedMorphism_compatible`,
the compatibility of the two structure-sheaf comparisons along `restrictOpensIso` that
`Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso` is also built from, read at
the isomorphism of sheaves of rings. -/
theorem pushedRingHom_comp_pushedRingSheafRestrictIso_inv :
    (S.restrict U).pushedRingHom ≫ (S.pushedRingSheafRestrictIso U).inv =
      (ringSheafRestriction S.X U).map S.pushedRingHom := by
  have h := structureSheafHom_restrictedMorphism_compatible S.i U
  simp only [phiSh] at h ⊢
  exact h

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
