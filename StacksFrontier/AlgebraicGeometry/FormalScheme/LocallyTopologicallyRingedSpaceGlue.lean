module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.LocallyTopologicallyRingedSpace
public import StacksFrontier.Geometry.RingedSpace.GlueMorphisms
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction of locally topologically ringed spaces, and gluing of morphisms

Let `LTRS` be the category of locally topologically ringed spaces of Stacks 0AHY, the ambient
category in which EGA formal schemes live. This file restricts an object of `LTRS` to an open
subset and proves that morphisms out of an object of `LTRS` glue along an open cover of the
source: a family of morphisms out of the members of an open cover which agree on the pairwise
overlaps comes from a unique morphism out of the whole space.

This is the Zariski half of the sheaf condition on the functor of points of a formal scheme, the
half the Stacks project omits with the words "we omit the verification that these morphisms glue"
in its proof of Stacks 0AI2. It is stated here for `LTRS`, not for formal schemes, because
nothing in the argument uses more than the sheaf axiom for the structure sheaf of the source.

## Main definitions

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.restrict`: the restriction `X|_V` of an
  object of `LTRS` to an open subset `V`, again an object of `LTRS`.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.ofRestrict`: the morphism `X|_V ⟶ X`.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.resLE`: the morphism `X|_V ⟶ X|_W` for
  `V ≤ W`.

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.hom_ext_of_openCover`: a morphism of `LTRS`
  out of `X` is determined by its restrictions to the members of an open cover of `X`.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.existsUnique_hom_of_openCover`: morphisms
  out of the members of an open cover of `X` which agree on the pairwise overlaps glue to a
  unique morphism out of `X`.

## Implementation notes

The underlying presheafed space of `X|_V` is `AlgebraicGeometry.PresheafedSpace.restrict` of the
underlying presheafed space of `X`, and the underlying morphisms of presheafed spaces of
`ofRestrict` and `resLE` are the ones of the same name for presheafed spaces; so the content
beyond `AlgebraicGeometry.PresheafedSpace.existsUnique_hom_of_openCover` is exactly the locality
conditions that `LTRS` imposes and presheafed spaces do not. There are two of these, and both
reduce to the fact that restriction along an open subset is an isomorphism on stalks: that the
stalks of `X|_V` are local rings, via
`AlgebraicGeometry.PresheafedSpace.restrictStalkIso`, and that the glued morphism is local on
stalks, via `isLocalHom_of_comp` applied to the factorisation `X|_{U i} ⟶ X ⟶ Y` of `f i`.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace TopCommRingCat

/-- An isomorphism of topological commutative rings is in particular a ring isomorphism of the
underlying rings. -/
def ringEquivOfIso {R S : TopCommRingCat.{u}} (e : R ≅ S) : R.α ≃+* S.α where
  toFun := e.hom.1
  invFun := e.inv.1
  left_inv x := congrFun (congrArg (fun m : R ⟶ R => (m.1 : R.α → R.α)) e.hom_inv_id) x
  right_inv x := congrFun (congrArg (fun m : S ⟶ S => (m.1 : S.α → S.α)) e.inv_hom_id) x
  map_mul' := e.hom.1.map_mul
  map_add' := e.hom.1.map_add

end TopCommRingCat

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace

variable {X Y : LTRS.{u}}

/-- The restriction of a locally topologically ringed space to an open subset: the underlying
space is the open subset, and the structure sheaf is the restricted sheaf of topological rings.
Its stalks are the stalks of `X` at the points of `V`, hence local rings. -/
def restrict (X : LTRS.{u}) (V : Opens X) : LTRS.{u} where
  toSheafedSpace := X.toSheafedSpace.restrict V.isOpenEmbedding
  isLocalRing x :=
    haveI : IsLocalRing (X.presheaf.stalk (V.inclusion' x)).α := X.isLocalRing _
    (TopCommRingCat.ringEquivOfIso
      (X.toPresheafedSpace.restrictStalkIso V.isOpenEmbedding x)).symm.isLocalRing

/-- The underlying presheafed space of `X.restrict V` is the restriction of the underlying
presheafed space of `X` to `V`. -/
@[simp]
theorem restrict_toPresheafedSpace (X : LTRS.{u}) (V : Opens X) :
    (X.restrict V).toPresheafedSpace = X.toPresheafedSpace.restrict V.isOpenEmbedding := rfl

/-- The canonical morphism from the restriction of a locally topologically ringed space to an
open subset into the space itself. -/
@[ega "0 4.1.2" "special case"]
def ofRestrict (X : LTRS.{u}) (V : Opens X) : X.restrict V ⟶ X where
  toHom := X.toPresheafedSpace.ofRestrict V.isOpenEmbedding
  isLocalHom x :=
    @TopCommRingCat.isLocalHom_val_of_isIso _ _ _
      (PresheafedSpace.ofRestrict_stalkMap_isIso X.toPresheafedSpace V.isOpenEmbedding x)

/-- The underlying morphism of presheafed spaces of `X.ofRestrict V` is
`AlgebraicGeometry.PresheafedSpace.ofRestrict`. -/
@[simp]
theorem ofRestrict_toHom (X : LTRS.{u}) (V : Opens X) :
    (X.ofRestrict V).toHom = X.toPresheafedSpace.ofRestrict V.isOpenEmbedding := rfl

/-- For open subsets `V ≤ W` of a locally topologically ringed space `X`, the morphism
`X|_V ⟶ X|_W` restricting along the inclusion. -/
def resLE (X : LTRS.{u}) {V W : Opens X} (h : V ≤ W) : X.restrict V ⟶ X.restrict W where
  toHom := X.toPresheafedSpace.resLE h
  isLocalHom x :=
    @TopCommRingCat.isLocalHom_val_of_isIso _ _ _
      (PresheafedSpace.IsOpenImmersion.stalk_iso (X.toPresheafedSpace.resLE h) x)

/-- The underlying morphism of presheafed spaces of `X.resLE h` is
`AlgebraicGeometry.PresheafedSpace.resLE`. -/
@[simp]
theorem resLE_toHom (X : LTRS.{u}) {V W : Opens X} (h : V ≤ W) :
    (X.resLE h).toHom = X.toPresheafedSpace.resLE h := rfl

/-- For open subsets `V ≤ W ≤ T`, the composite `X|_V ⟶ X|_W ⟶ X|_T` is `X|_V ⟶ X|_T`. -/
@[simp]
theorem resLE_comp_resLE (X : LTRS.{u}) {V W T : Opens X} (h₁ : V ≤ W) (h₂ : W ≤ T) :
    X.resLE h₁ ≫ X.resLE h₂ = X.resLE (h₁.trans h₂) :=
  Hom.ext' (X.toPresheafedSpace.resLE_comp_resLE h₁ h₂)

/-- For open subsets `V ≤ W`, the composite `X|_V ⟶ X|_W ⟶ X` is `X|_V ⟶ X`. -/
@[simp]
theorem resLE_comp_ofRestrict (X : LTRS.{u}) {V W : Opens X} (h : V ≤ W) :
    X.resLE h ≫ X.ofRestrict W = X.ofRestrict V :=
  Hom.ext' (X.toPresheafedSpace.resLE_comp_ofRestrict h)

/-- **Separatedness.** A morphism of locally topologically ringed spaces out of `X` is determined
by its restrictions to the members of an open cover of `X`. -/
theorem hom_ext_of_openCover {ι : Type*} (U : ι → Opens X) (hU : iSup U = ⊤) {g₁ g₂ : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i) ≫ g₁ = X.ofRestrict (U i) ≫ g₂) :
    g₁ = g₂ :=
  Hom.ext' (PresheafedSpace.hom_ext_of_openCover U hU X.IsSheaf
    fun i => congrArg Hom.toHom (h i))

/-- **Morphisms of locally topologically ringed spaces glue along an open cover of the source.**
Let `X` and `Y` be locally topologically ringed spaces, let `U` be a family of open subsets
covering `X`, and let `f i : X|_{U i} ⟶ Y` be morphisms agreeing on the overlaps `U i ⊓ U j`.
Then there is a unique morphism `X ⟶ Y` restricting to `f i` on each `U i`.

This is the Zariski half of the sheaf condition on the functor of points, the verification that
Stacks 0AI2 omits. -/
theorem existsUnique_hom_of_openCover {ι : Type*} (U : ι → Opens X) (hU : iSup U = ⊤)
    (f : ∀ i, X.restrict (U i) ⟶ Y)
    (hf : ∀ i j, X.resLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i
        = X.resLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) :
    ∃! g : X ⟶ Y, ∀ i, X.ofRestrict (U i) ≫ g = f i := by
  obtain ⟨g, hg, huniq⟩ := PresheafedSpace.existsUnique_hom_of_openCover
    (X := X.toPresheafedSpace) (Y := Y.toPresheafedSpace) U hU (fun i => (f i).toHom)
    (fun i j => congrArg Hom.toHom (hf i j)) X.IsSheaf
  have hloc : ∀ x : X, IsLocalHom (g.stalkMap x).1 := by
    intro x
    obtain ⟨i, hx⟩ := PresheafedSpace.exists_mem_of_openCover U hU x
    set r := X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding with hr
    set p : (X.toPresheafedSpace.restrict (U i).isOpenEmbedding : TopCat) := ⟨x, hx⟩ with hp
    have key : IsLocalHom ((r ≫ g).stalkMap p).1 := by
      rw [hr, hg i]
      exact (f i).isLocalHom p
    rw [PresheafedSpace.stalkMap.comp r g p] at key
    exact @isLocalHom_of_comp _ _ _ _ _ _ (g.stalkMap (r.base p)).1 (r.stalkMap p).1 key
  refine ⟨⟨g, hloc⟩, fun i => Hom.ext' (hg i), fun g' hg' => ?_⟩
  exact Hom.ext' (huniq g'.toHom fun i => congrArg Hom.toHom (hg' i))

end AlgebraicGeometry.LocallyTopologicallyRingedSpace

end
