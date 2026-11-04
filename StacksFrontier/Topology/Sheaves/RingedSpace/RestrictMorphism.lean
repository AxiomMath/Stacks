module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Topology.LocalAtTarget

/-!
# Restricting a morphism of ringed spaces to an open subspace of the target

Let `i : Z ⟶ X` be a morphism of ringed spaces and let `U` be an open subspace of `X`. Write
`V = i⁻¹U` for the corresponding open subspace of `Z`. Then `i` restricts to a morphism of
ringed spaces `Z|_V ⟶ X|_U`, and this file constructs it.

Only the *topological* restriction `V ⟶ U` is immediate. The content is the map of structure
sheaves: a section of `𝒪_X` over an open `W ⊆ U` is a section over `ι_U(W) ⊆ X`, which `i^♯`
carries to a section of `𝒪_Z` over `i⁻¹(ι_U W)`, and that open of `Z` is `ι_V` of the preimage
of `W` under the restricted map. The required identification of opens of `Z` is
`AlgebraicGeometry.RingedSpace.functor_map_restrictHomBase`; packaged as an isomorphism of
functors `Opens U ⥤ Opens Z` it is
`AlgebraicGeometry.RingedSpace.restrictOpensIsoOfBase`, and the map of structure sheaves is the
composite of `i^♯` whiskered by `ι_U` with that isomorphism. Writing it this way means no
naturality square has to be checked by hand.

## Main definitions

* `AlgebraicGeometry.RingedSpace.restrictHomBase` is the underlying continuous map `V ⟶ U`.
* `AlgebraicGeometry.RingedSpace.restrictOpensIsoOfBase` and
  `AlgebraicGeometry.RingedSpace.restrictOpensIso` identify the two functors
  `Opens U ⥤ Opens Z` given by `W ↦ ι_V((i|_V)⁻¹W)` and `W ↦ i⁻¹(ι_U W)`, the first written
  through `restrictHomBase` and the second through the underlying map of `i|_V` itself.
* `AlgebraicGeometry.RingedSpace.restrictPresheafedSpaceHom` is `i|_V` as a morphism of
  presheafed spaces, and `AlgebraicGeometry.RingedSpace.restrictHom` is `i|_V` itself, a
  morphism of ringed spaces `Z|_V ⟶ X|_U`.

## Main results

* `AlgebraicGeometry.RingedSpace.restrictHom_base_coe` and
  `AlgebraicGeometry.RingedSpace.restrictHom_c_app` characterise `i|_V` completely: its
  underlying map is `z ↦ i(z)` and its map of structure sheaves is `i^♯` over `ι_U W` followed
  by the restriction along `restrictOpensIso`. Both hold by `rfl`.
* `AlgebraicGeometry.RingedSpace.opensMap_restrictHom` records that taking preimages of opens
  along `i|_V` is taking preimages along `restrictHomBase`, again by `rfl`; this is what lets a
  consumer rewrite a statement about `i|_V` into one about the explicit map.
* `AlgebraicGeometry.RingedSpace.isClosedEmbedding_restrictHom`: if the underlying continuous
  map of `i` is a closed embedding, so is that of `i|_V`.

## Implementation notes

The map of structure sheaves is written as a composite of whiskerings rather than by giving its
components. A by-hand definition needs its naturality square proved by `rw`, and that fails:
the carrier of a restricted space has two definitionally equal spellings — through
`(X.restrict U.isOpenEmbedding).carrier` and through `(Opens.toTopCat X.carrier).obj U` — so the
goal is not type-correct at `implicit` transparency and no rewrite matches. Written as a
composite of whiskerings there is no naturality obligation at all. For the same reason every
statement below spells the site of `X|_U` as `Opens (X.restrict U.isOpenEmbedding).carrier`,
which is the spelling the sheaf-of-modules development uses.

`restrictHom` is obtained from the presheafed-space morphism through
`AlgebraicGeometry.SheafedSpace.fullyFaithfulForgetToPresheafedSpace`; a ringed space is a
sheafed space, whose category is an `CategoryTheory.InducedCategory`, so this is just the
constructor for its morphisms and `(restrictHom i U).hom` is the presheafed-space morphism
by `rfl`.

The commuting square `i|_V ≫ ι_U = ι_V ≫ i` of ringed spaces is *not* recorded here. It is
true, and `restrictHom_base_coe` together with `restrictHom_c_app` determine `i|_V` as the
unique morphism making it commute (the open immersion `ι_U` is a monomorphism), but stating
the square needs `AlgebraicGeometry.PresheafedSpace.ext`, which inserts an `eqToHom` between
two spellings of one and the same base map; consumers want the module-level form of the square
instead, and that is built from `restrictOpensIso` directly.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

universe u

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) (U : Opens X.carrier)

/-- The underlying continuous map of the restriction of `i : Z ⟶ X` to `i⁻¹U ⟶ U`: it sends
`z ∈ i⁻¹U` to `i(z) ∈ U`. -/
public def restrictHomBase :
    (Z.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding).carrier ⟶
      (X.restrict U.isOpenEmbedding).carrier :=
  TopCat.ofHom ⟨fun x => ⟨i.hom.base x.1, x.2⟩, by fun_prop⟩

/-- For an open `W` of `U`, the open `ι_{i⁻¹U}((i|_{i⁻¹U})⁻¹W)` of `Z` is the open `i⁻¹(ι_U W)`.

Both are the set of points `z` of `Z` with `i(z) ∈ W`: the left-hand side says in addition that
`z ∈ i⁻¹U`, which is automatic because `W ⊆ U`. -/
public theorem functor_map_restrictHomBase
    (W : Opens (X.restrict U.isOpenEmbedding).carrier) :
    ((Opens.map i.hom.base).obj U).isOpenEmbedding.functor.obj
        ((Opens.map (restrictHomBase i U)).obj W) =
      (Opens.map i.hom.base).obj (U.isOpenEmbedding.functor.obj W) := by
  refine le_antisymm ?_ ?_
  · rintro z ⟨⟨z, hz⟩, hw, rfl⟩
    exact ⟨⟨i.hom.base z, hz⟩, hw, rfl⟩
  · rintro z ⟨⟨x, hx⟩, hw, he⟩
    replace he : x = i.hom.base z := he
    subst he
    exact ⟨⟨z, hx⟩, hw, rfl⟩

/-- `functor_map_restrictHomBase` as an isomorphism of functors `Opens U ⥤ Opens Z`. Naturality
is automatic: the hom types of `Opens Z` are subsingletons. -/
public def restrictOpensIsoOfBase :
    Opens.map (restrictHomBase i U) ⋙
        ((Opens.map i.hom.base).obj U).isOpenEmbedding.functor ≅
      U.isOpenEmbedding.functor ⋙ Opens.map i.hom.base :=
  NatIso.ofComponents (fun W => eqToIso (functor_map_restrictHomBase i U W))
    (fun _ => Subsingleton.elim _ _)

/-- The restriction of a morphism of presheafed spaces `i : Z ⟶ X` to the open subspace `U` of
`X` and its preimage in `Z`.

On sections over an open `W` of `U` it is `i^♯` over `ι_U W` followed by restriction along
`restrictOpensIso`, written as a composite of whiskerings so that no naturality square has to
be verified. -/
public def restrictPresheafedSpaceHom :
    Z.toPresheafedSpace.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding ⟶
      X.toPresheafedSpace.restrict U.isOpenEmbedding where
  base := restrictHomBase i U
  c := Functor.whiskerLeft U.isOpenEmbedding.functor.op i.hom.c ≫
    Functor.whiskerRight (NatTrans.op (restrictOpensIsoOfBase i U).hom) Z.presheaf

/-- **The restriction `i|_V : Z|_V ⟶ X|_U` of a morphism of ringed spaces** `i : Z ⟶ X` to an
open subspace `U` of `X`, where `V = i⁻¹U`.

This is a morphism of ringed spaces, not merely of topological spaces: the map of structure
sheaves is `restrictPresheafedSpaceHom`. -/
public def restrictHom :
    Z.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding ⟶
      X.restrict U.isOpenEmbedding :=
  SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage (restrictPresheafedSpaceHom i U)

/-- `i|_V` is the presheafed-space morphism `restrictPresheafedSpaceHom` with the sheaf
conditions carried along.

Not a `simp` lemma: it unfolds `restrictHom`, so the statements about the components of `i|_V`
below would no longer be in `simp` normal form. -/
public theorem restrictHom_hom : (restrictHom i U).hom = restrictPresheafedSpaceHom i U := rfl

/-- The underlying map of `i|_V` is the underlying map of `i`. -/
@[simp]
public theorem restrictHom_base_coe
    (x : (Z.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding).carrier) :
    ((restrictHom i U).hom.base x).1 = i.hom.base x.1 := rfl

/-- Taking preimages of opens along `i|_V` is taking preimages along `restrictHomBase`. -/
public theorem opensMap_restrictHom :
    Opens.map (restrictHom i U).hom.base = Opens.map (restrictHomBase i U) := rfl

/-- `restrictOpensIsoOfBase` with the base map written as the underlying map of `i|_V` rather
than as `restrictHomBase`.

This is the form consumers need: the structure-sheaf map of `i|_V`, and hence every statement
about pushing modules forward along `i|_V`, is indexed by `Opens.map (restrictHom i U).hom.base`,
and instance resolution does not see through `opensMap_restrictHom`. -/
public def restrictOpensIso :
    Opens.map (restrictHom i U).hom.base ⋙
        ((Opens.map i.hom.base).obj U).isOpenEmbedding.functor ≅
      U.isOpenEmbedding.functor ⋙ Opens.map i.hom.base :=
  restrictOpensIsoOfBase i U

/-- The map of structure sheaves of `i|_V` on sections over an open `W` of `U`: it is `i^♯` over
`ι_U W`, followed by restriction to the open `ι_V((i|_V)⁻¹W) = i⁻¹(ι_U W)` of `Z`. -/
public theorem restrictHom_c_app (W : Opens (X.restrict U.isOpenEmbedding).carrier) :
    (restrictHom i U).hom.c.app (op W) =
      i.hom.c.app (op (U.isOpenEmbedding.functor.obj W)) ≫
        Z.presheaf.map ((restrictOpensIso i U).hom.app W).op := rfl

/-- **A closed immersion of underlying topological spaces restricts to one.** If the underlying
continuous map of `i` is a closed embedding, so is that of `i|_V : Z|_V ⟶ X|_U`.

This is what lets the hypothesis of Stacks 09VA — that `i` is a closed immersion of underlying
topological spaces — be carried into a localization step of its proof, and in particular what
makes `AlgebraicGeometry.RingedSpace.derivedPushforwardOXMod` available for `i|_V`. -/
public theorem isClosedEmbedding_restrictHom (hi : Topology.IsClosedEmbedding i.hom.base) :
    Topology.IsClosedEmbedding (restrictHom i U).hom.base :=
  Set.restrictPreimage_isClosedEmbedding (↑U : Set X.carrier) hi

end AlgebraicGeometry.RingedSpace

end
