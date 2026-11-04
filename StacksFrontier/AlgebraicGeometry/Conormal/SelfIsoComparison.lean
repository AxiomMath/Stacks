module

public import StacksFrontier.AlgebraicGeometry.CartierConormal.Basic
public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization
public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorizationGlue

/-!
# The two self-isomorphisms of the conormal sheaf are mutually inverse

For an immersion of schemes `i : Z ⟶ X` the library carries two isomorphisms between the same
pair of objects, built by two different routes and pointing in opposite directions:

* `Stacks.Immersion.conormalSheafSelfIso i : 𝒞_{i} ≅ 𝒞_{i.liftCoborder}`, where `𝒞_{(·)}` is the
  ringed-space conormal sheaf `Stacks.ClosedImmersion.conormalSheaf`. It is built from
  `Stacks.Immersion.conormalSheafFactorIso` at the defining factorization, read along
  `AlgebraicGeometry.Scheme.Hom.liftCoborder_ι`, hence from
  `Stacks.ClosedImmersion.idealSheafOfRestrictIso`.
* `Stacks.CartierConormal.conormalSheafIsoPullbackSelf i : 𝒞_{Z/X} ≅ i^* ℐ_i`, where `𝒞_{Z/X}` is
  `Stacks.Conormal.conormalSheaf`. It is built from
  `Stacks.Conormal.pullbackIdealSheafIsoOfCompEq`, hence from
  `Stacks.IdealSheafRestrict.pullbackIdealSheafIso`.

The two sources and the two targets agree: `Stacks.Conormal.conormalSheaf i` is by definition
`i.liftCoborder^* ℐ_{i.liftCoborder}`, which is `Stacks.ClosedImmersion.conormalSheaf` of
`i.liftCoborder`, and `Stacks.ClosedImmersion.conormalSheaf` of `i` is `i^* ℐ_i`. So the two
isomorphisms are the two directions of one bridge, and this file proves they are the same bridge.

## Main results

* `Stacks.Immersion.conormalSheafSelfIso_hom` and
  `Stacks.Immersion.conormalSheafSelfIso_inv`: the forward map of one is the backward map of the
  other.
* The isomorphisms themselves, the form a `CategoryTheory.Functor.mapIso` consumer wants, are
  identified by `Stacks.Immersion.conormalSheafSelfIso_eq_symm_conormalSheafIsoPullbackSelf` of
  `StacksFrontier/AlgebraicGeometry/Conormal/QuotientFactorizationGlue.lean`.
* `Stacks.Immersion.conormalSheafSelfIso_hom_comp_conormalSheafIsoPullbackSelf_hom` and
  `Stacks.Immersion.conormalSheafIsoPullbackSelf_hom_comp_conormalSheafSelfIso_hom`: each
  composite is the identity.
* `Stacks.Conormal.pullbackIdealSheafIsoOfCompEq_hom`: the ingredient, which strips the `subst`
  in the construction of `Stacks.Conormal.pullbackIdealSheafIsoOfCompEq` down to a
  `CategoryTheory.eqToHom` followed by `Stacks.Conormal.pullbackIdealSheafCompIso`.

## Route

Both isomorphisms become one composite once the `subst` hidden inside
`Stacks.Conormal.pullbackIdealSheafIsoOfCompEq` is made explicit:

* `Stacks.Conormal.pullbackIdealSheafIsoOfCompEq_hom` rewrites that construction as the transport
  along the factorization equality followed by `Stacks.Conormal.pullbackIdealSheafCompIso`. It is
  proved by substituting the equality, after which the transport is the identity.
* `Stacks.Immersion.conormalSheafFactorIso_eq_pullbackIdealSheafCompIso`, already available,
  identifies the other route's second factor with the same
  `Stacks.Conormal.pullbackIdealSheafCompIso` — that is the content of
  `Stacks.Immersion.idealSheafOfRestrictIso_eq_pullbackIdealSheafIso`, the comparison of the
  kernel-preservation and restriction constructions of `ι_U^* ℐ_{i' ≫ ι_U} ≅ ℐ_{i'}`.
* The two transports are `CategoryTheory.eqToHom` of two proofs of one equality of objects, hence
  equal; the abbreviation `Stacks.ClosedImmersion.conormalSheaf` does not have to be unfolded by
  hand for this, since `Eq` is a proposition.

So no comparison of universal properties, and no value of either isomorphism, is computed
anywhere here.

## Why this bridge is wanted

[Stacks Project, Tag 04G2] part (1) is proved at immersion generality in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreementImmersion.lean`, and its
schemes-side link `Stacks.Conormal.conormalSheafLiftCoborderIso` is
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf` at `i.liftCoborder`. The canonical map of
[Stacks Project, Tag 01R4], `Stacks.Immersion.immersionConormalSheafMap`, is instead conjugated by
`Stacks.Immersion.conormalSheafSelfIso` throughout
`StacksFrontier/AlgebraicGeometry/Thickenings/UniversalConormalGenerators.lean` and its siblings.
The results below are what lets a statement written in one of the two vocabularies be read in the
other; instantiating them at `i.liftCoborder` gives the relation to
`Stacks.Conormal.conormalSheafLiftCoborderIso` with no further work.

**No tag is claimed here.** This is a comparison of two of the repository's own constructions, not
an assertion of the source.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open AlgebraicGeometry

universe u

namespace Stacks.Conormal

/-- **The transport inside `Stacks.Conormal.pullbackIdealSheafIsoOfCompEq`, made explicit.** That
isomorphism is constructed by substituting the equality `k ≫ j = L`; on forward maps it is
therefore the `CategoryTheory.eqToHom` transport along that equality followed by
`Stacks.Conormal.pullbackIdealSheafCompIso`.

Substituting the equality turns the transport into the identity, which is the proof. -/
theorem pullbackIdealSheafIsoOfCompEq_hom {Z U V : Scheme.{u}} (k : Z ⟶ U) (j : U ⟶ V)
    [IsOpenImmersion j] (L : Z ⟶ V) (hL : k ≫ j = L) :
    (pullbackIdealSheafIsoOfCompEq k j L hL).hom =
      eqToHom (congrArg (fun f : Z ⟶ V => (modulePullback f.toLRSHom.toShHom).obj
          (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom)) hL.symm) ≫
        (pullbackIdealSheafCompIso k j).hom := by
  subst hL
  exact (Category.id_comp _).symm

end Stacks.Conormal

namespace Stacks.Immersion

open Stacks.ClosedImmersion

variable {Z X : Scheme.{u}}

/-- **The forward map of `Stacks.Immersion.conormalSheafSelfIso` is the backward map of
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf`.** Both are isomorphisms between
`i^* ℐ_i` and `i.liftCoborder^* ℐ_{i.liftCoborder}`, the latter being
`Stacks.Conormal.conormalSheaf i` by definition, and they are built by two different routes: the
first through `Stacks.Immersion.conormalSheafFactorIso`, the second through
`Stacks.Conormal.pullbackIdealSheafIsoOfCompEq`.

The two routes meet at `Stacks.Conormal.pullbackIdealSheafCompIso`:
`Stacks.Immersion.conormalSheafFactorIso_eq_pullbackIdealSheafCompIso` rewrites the first and
`Stacks.Conormal.pullbackIdealSheafIsoOfCompEq_hom` the second, and the two transports along
`AlgebraicGeometry.Scheme.Hom.liftCoborder_ι` that remain are `CategoryTheory.eqToHom` of two
proofs of one equality. -/
theorem conormalSheafSelfIso_hom (i : Z ⟶ X) [IsImmersion i] :
    (conormalSheafSelfIso i).hom =
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).inv := by
  rw [conormalSheafSelfIso, Iso.trans_hom, Iso.symm_hom, eqToIso.inv,
    conormalSheafFactorIso_eq_pullbackIdealSheafCompIso]
  exact (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq_hom i.liftCoborder i.coborderRange.ι i
    i.liftCoborder_ι).symm

/-- **The backward map of `Stacks.Immersion.conormalSheafSelfIso` is the forward map of
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf`**, the inverse half of
`Stacks.Immersion.conormalSheafSelfIso_hom`. -/
theorem conormalSheafSelfIso_inv (i : Z ⟶ X) [IsImmersion i] :
    (conormalSheafSelfIso i).inv =
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).hom :=
  congrArg Iso.inv (conormalSheafSelfIso_eq_symm_conormalSheafIsoPullbackSelf i)

/-- **The composite `i^* ℐ_i ⟶ 𝒞_{Z/X} ⟶ i^* ℐ_i` of the two self-isomorphisms is the
identity**, in the order that starts at the ringed-space conormal sheaf of `i` itself. -/
theorem conormalSheafSelfIso_hom_comp_conormalSheafIsoPullbackSelf_hom (i : Z ⟶ X)
    [IsImmersion i] :
    (conormalSheafSelfIso i).hom ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).hom =
      𝟙 (conormalSheaf i.toLRSHom.toShHom) := by
  rw [conormalSheafSelfIso_hom]
  exact (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).inv_hom_id

/-- **The composite `𝒞_{Z/X} ⟶ i^* ℐ_i ⟶ 𝒞_{Z/X}` of the two self-isomorphisms is the
identity**, in the order that starts at `Stacks.Conormal.conormalSheaf`. -/
theorem conormalSheafIsoPullbackSelf_hom_comp_conormalSheafSelfIso_hom (i : Z ⟶ X)
    [IsImmersion i] :
    (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).hom ≫
        (conormalSheafSelfIso i).hom =
      𝟙 (Stacks.Conormal.conormalSheaf i) := by
  rw [conormalSheafSelfIso_hom]
  exact (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).hom_inv_id

end Stacks.Immersion

end
