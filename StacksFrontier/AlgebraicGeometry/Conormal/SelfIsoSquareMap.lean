module

public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheafSupplement
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackCompSupplement

/-!
# The change of ambient space of a conormal sheaf is the canonical map of its square

[Stacks Project, Tag 01R2] defines the conormal sheaf of an immersion `i : Z ⟶ X` through the
factorization of `i` as a closed immersion `L = i.liftCoborder` into the open
`i.coborderRange` followed by that open's inclusion `ι`, and
`Stacks.Immersion.conormalSheafSelfIso` identifies the result with the ringed-space conormal
sheaf of `i` itself. That identification is a **change of ambient space**, replacing `X` by the
smaller `i.coborderRange`. [Stacks Project, Tag 01R4] attaches to *every* commutative square of
ringed spaces a canonical map of conormal sheaves,
`Stacks.ClosedImmersion.conormalSheafMap`. This file shows that the two agree: the change of
ambient space of [Stacks Project, Tag 01R2] is the canonical map of [Stacks Project, Tag 01R4]
at the square
```
   Z  --- 𝟙 --->  Z
   |              |
   L              i
   ↓              ↓
  cbR --- ι --->  X
```
whose top edge is the identity of `Z`, left edge the closed factor, bottom edge the inclusion of
the coborder range and right edge the immersion itself. A pullback along an identity intervenes,
so the statement reads

`conormalSheafMap comm = (modulePullbackId Z).hom.app (𝒞_i) ≫ (conormalSheafSelfIso i).hom`.

## Main results

* `Stacks.ClosedImmersion.idealSheafMap_eq_idealSheafOfRestrictIso`: for a factorization
  `g ≫ ι_U` through an open subspace, the ideal-sheaf map of the square with identity top edge is
  `Stacks.ClosedImmersion.idealSheafOfRestrictIso`.
* `Stacks.ClosedImmersion.conormalSheafMap_eq_conormalSheafOfRestrictIso` and its transported form
  `Stacks.ClosedImmersion.conormalSheafMap_eq_conormalSheafOfRestrictIso_of_eq`: the same
  statement for conormal sheaves.
* `Stacks.Immersion.conormalSheafMap_coborder_eq_conormalSheafSelfIso`: the scheme-level
  statement for the defining factorization of an immersion.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2), the conormal sheaf of an
  immersion and its change of ambient space.
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4), the canonical map of a
  square.
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2), its functoriality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

namespace Stacks.ClosedImmersion

/-! ### The square comparison at an identity top edge -/

/-- **The square comparison of a square whose top edge is an identity is the unit isomorphism
followed by the composition isomorphism of the two remaining edges.** For `a : Z ⟶ Z'` and
`b : Z' ⟶ W'` the square with top edge `𝟙 Z` and right edge `a ≫ b` commutes, and
`Stacks.ClosedImmersion.pullbackCompIso` at it is
`RingedSpaceModuleAdjunction.modulePullbackId` followed by
`RingedSpaceModuleAdjunction.modulePullbackComp`. -/
theorem pullbackCompIso_id_left_hom {Zr Zr' Wr' : RingedSpace.{u, u}} {a : Zr ⟶ Zr'}
    {b : Zr' ⟶ Wr'} (comm : a ≫ b = 𝟙 Zr ≫ (a ≫ b))
    (M : SheafOfModules.{u} (structureSheafRing Wr')) :
    (pullbackCompIso comm M).hom =
      (modulePullbackId Zr).hom.app ((modulePullback (a ≫ b)).obj M) ≫
        (modulePullbackComp a b).hom.app M := by
  have hmid : (modulePullbackCongr comm.symm).hom.app M =
      𝟙 ((modulePullback (a ≫ b)).obj M) :=
    (eqToHom_app (congrArg modulePullback comm.symm) M).trans (eqToHom_refl _ _)
  rw [pullbackCompIso_hom, modulePullbackComp_id_left_inv_app, hmid]
  exact congrArg (_ ≫ ·) (Category.id_comp _)

/-! ### The square of a factorization through an open subspace -/

variable {Z X : RingedSpace.{u, u}} (U : Opens X.carrier)
  (g : Z ⟶ X.restrict U.isOpenEmbedding)

/-- **The ideal-sheaf map of the open-factorization square is
`Stacks.ClosedImmersion.idealSheafOfRestrictIso`.** For a morphism of ringed spaces
`g : Z ⟶ X|_U` the square with top edge `𝟙 Z`, left edge `g`, bottom edge `ι_U` and right edge
`g ≫ ι_U` has ideal-sheaf map `ι_U^* ℐ_{g ≫ ι_U} ⟶ ℐ_g`, and that is the canonical
identification of the two ideal sheaves. -/
theorem idealSheafMap_eq_idealSheafOfRestrictIso
    (comm : g ≫ X.ofRestrict U.isOpenEmbedding =
      𝟙 Z ≫ (g ≫ X.ofRestrict U.isOpenEmbedding)) :
    idealSheafMap comm = (idealSheafOfRestrictIso U g).hom := by
  have := mono_idealSheafι g
  rw [← cancel_mono (idealSheafι g), idealSheafMap_comp_ι,
    idealSheafOfRestrictIso_hom_comp_ι]

/-- **The conormal-sheaf map of the open-factorization square is
`Stacks.ClosedImmersion.conormalSheafOfRestrictIso`**, up to the pullback along the identity top
edge: the canonical map of [Stacks Project, Tag 01R4] at a square whose top edge is an identity
and whose right edge is the composite of the other two is the canonical identification of the two
conormal sheaves. -/
theorem conormalSheafMap_eq_conormalSheafOfRestrictIso
    (comm : g ≫ X.ofRestrict U.isOpenEmbedding =
      𝟙 Z ≫ (g ≫ X.ofRestrict U.isOpenEmbedding)) :
    conormalSheafMap comm =
      (modulePullbackId Z).hom.app (conormalSheaf (g ≫ X.ofRestrict U.isOpenEmbedding)) ≫
        (conormalSheafOfRestrictIso U g).hom := by
  rw [conormalSheafMap, idealSheafMap_eq_idealSheafOfRestrictIso, pullbackCompIso_id_left_hom,
    conormalSheafOfRestrictIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]

/-- `Stacks.ClosedImmersion.conormalSheafMap_eq_conormalSheafOfRestrictIso` with the right edge of
the square presented as a morphism `j` equal to the composite, the identification of the two
spellings carried by a `CategoryTheory.eqToHom` in front of
`Stacks.ClosedImmersion.conormalSheafOfRestrictIso`. -/
theorem conormalSheafMap_eq_conormalSheafOfRestrictIso_of_eq {j : Z ⟶ X}
    (hj : g ≫ X.ofRestrict U.isOpenEmbedding = j)
    (comm : g ≫ X.ofRestrict U.isOpenEmbedding = 𝟙 Z ≫ j) :
    conormalSheafMap comm =
      (modulePullbackId Z).hom.app (conormalSheaf j) ≫
        eqToHom (congrArg (fun p : Z ⟶ X => conormalSheaf p) hj.symm) ≫
          (conormalSheafOfRestrictIso U g).hom := by
  subst hj
  rw [eqToHom_refl, Category.id_comp, conormalSheafMap_eq_conormalSheafOfRestrictIso]

end Stacks.ClosedImmersion

namespace Stacks.Immersion

open Stacks.ClosedImmersion

variable {Z X : Scheme.{u}}

/-- **The change of ambient space of [Stacks Project, Tag 01R2] is the canonical map of
[Stacks Project, Tag 01R4] at the coborder square.** For an immersion of schemes `i : Z ⟶ X`,
the canonical map of conormal sheaves attached to the square whose top edge is `𝟙 Z`, left edge
the closed factor `i.liftCoborder`, bottom edge the inclusion of `i.coborderRange` and right edge
`i` itself is the pullback along the identity, followed by
`Stacks.Immersion.conormalSheafSelfIso`. -/
theorem conormalSheafMap_coborder_eq_conormalSheafSelfIso (i : Z ⟶ X) [IsImmersion i]
    (comm : i.liftCoborder.toLRSHom.toShHom ≫ i.coborderRange.ι.toLRSHom.toShHom =
      𝟙 Z.toLocallyRingedSpace.toRingedSpace ≫ i.toLRSHom.toShHom) :
    conormalSheafMap comm =
      (modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).hom.app
          (conormalSheaf i.toLRSHom.toShHom) ≫
        (conormalSheafSelfIso i).hom := by
  refine (conormalSheafMap_eq_conormalSheafOfRestrictIso_of_eq i.coborderRange
    i.liftCoborder.toLRSHom.toShHom
    (congrArg (fun f : Z ⟶ X => f.toLRSHom.toShHom) i.liftCoborder_ι) comm).trans ?_
  rw [conormalSheafSelfIso, Iso.trans_hom, Iso.symm_hom, eqToIso.inv]
  rfl

end Stacks.Immersion

end
