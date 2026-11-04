module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareMate

/-!
# The restriction square carries the conormal quotient map

Let `i : Z ⟶ X` be a morphism of ringed spaces, let `U` be an open subspace of `X` and write
`V = i⁻¹U`, so that `i` restricts to `i|_V : Z|_V ⟶ X|_U` and
`AlgebraicGeometry.RingedSpace.restrictHom_comp_ofRestrict` is the commuting square
```
Z|_V --i|_V--→ X|_U
|              |
ι_V            ι_U
↓              ↓
Z ----i------→ X
```
The ideal sheaf and the conormal sheaf are transported across it by
`Stacks.ClosedImmersion.restrictIdealSheafIso`, which is `ℐ_i|_U ≅ ℐ_{i|_V}`, and
`Stacks.ClosedImmersion.restrictConormalSheafIso`, which is `𝒞_i|_V ≅ 𝒞_{i|_V}`. This file shows
that these transports carry the *conormal quotient map* `ℐ_j ⟶ j_* 𝒞_j` of
[Stacks Project, Tag 01R3] part (1), the unit of `j^* ⊣ j_*` at the ideal sheaf, of `i` to that of
`i|_V`: the square
```
ℐ_i -----------η_i-----------→ i_* 𝒞_i
|                                 |
r                                 c
↓                                 ↓
(ι_U)_* ℐ_{i|_V} ---→ (ι_U)_*((i|_V)_* 𝒞_{i|_V})
```
commutes, where the two vertical morphisms are the canonical restriction-of-sections maps: `r` is
the unit of `(ι_U)^* ⊣ (ι_U)_*` followed by `(ι_U)_*` of the ideal-sheaf transport, and `c` is
`i_*` of the unit of `(ι_V)^* ⊣ (ι_V)_*` followed by
`RingedSpaceModuleAdjunction.modulePushforwardSquareIso` and by the conormal-sheaf
transport. That is `Stacks.ClosedImmersion.restrictConormalSheafIso_comp_unit`.

## Main results

* `Stacks.ClosedImmersion.restrictConormalSheafIso_comp_unit` is the commuting square above.
* `Stacks.ClosedImmersion.restrictConormalSheafIso_comp_unit_scheme` is the same square for a
  morphism of *schemes* `i : Z ⟶ X` and an open `V` of `X`.
* `AlgebraicGeometry.RingedSpace.restrictPullbackIso_hom` identifies the pullback base-change
  square `AlgebraicGeometry.RingedSpace.restrictPullbackIso` with the inverse of
  `RingedSpaceModuleAdjunction.modulePullbackSquareIso`, conjugated by the two instances
  of `AlgebraicGeometry.RingedSpace.modulePullbackRestrictIso` that turn a restriction into a
  pullback along an open immersion.
* `Stacks.ClosedImmersion.squareIso_hom_comp_restrictConormal` reads
  `Stacks.ClosedImmersion.restrictConormalSheafIso` as `(i|_V)^*` of
  `Stacks.ClosedImmersion.restrictIdealSheafIso` twisted by
  `RingedSpaceModuleAdjunction.modulePullbackSquareIso`.

## Implementation notes

`Stacks.ClosedImmersion.restrictConormalSheafIso_comp_unit_scheme` is written with
`Z.toSheafedSpace` and `(Opens.map i.toLRSHom.toShHom.hom.base).obj V`, the terms its
instantiation at `i.toLRSHom.toShHom` produces; do not re-spell them as
`Z.toLocallyRingedSpace.toRingedSpace` or `i ⁻¹ᵁ V`, because the kernel then times out checking
it through a component of `AlgebraicGeometry.RingedSpace.restrictPullbackIso`. For the same
reason, statements about `AlgebraicGeometry.RingedSpace.restrictPullbackIso` are kept at the level
of natural transformations.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.RingedSpace

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) (U : Opens X.carrier)

/-- The definition of `AlgebraicGeometry.RingedSpace.restrictPullbackIso`, as an equation. -/
theorem restrictPullbackIso_eq : restrictPullbackIso i U =
    Functor.isoWhiskerLeft (modulePullback i)
        (modulePullbackRestrictIso Z ((Opens.map i.hom.base).obj U)).symm ≪≫
      (modulePullbackComp (Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding) i).symm ≪≫
      modulePullbackCongr (restrictHom_comp_ofRestrict i U).symm ≪≫
      modulePullbackComp (restrictHom i U) (X.ofRestrict U.isOpenEmbedding) ≪≫
      Functor.isoWhiskerRight (modulePullbackRestrictIso X U)
        (modulePullback (restrictHom i U)) :=
  rfl

/-- **The pullback base-change square of a restriction is the square comparison of
`StacksFrontier.AlgebraicGeometry.Conormal.SquareMate`.** Precisely,
`AlgebraicGeometry.RingedSpace.restrictPullbackIso` is the inverse of
`RingedSpaceModuleAdjunction.modulePullbackSquareIso` for the square
`AlgebraicGeometry.RingedSpace.restrictHom_comp_ofRestrict`, conjugated by the identifications
`AlgebraicGeometry.RingedSpace.modulePullbackRestrictIso` of a restriction with a pullback along
an open immersion. -/
theorem restrictPullbackIso_hom :
    (restrictPullbackIso i U).hom =
      Functor.whiskerLeft (modulePullback i)
          (modulePullbackRestrictIso Z ((Opens.map i.hom.base).obj U)).inv ≫
        (modulePullbackSquareIso (Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)
            (X.ofRestrict U.isOpenEmbedding) (restrictHom i U) i
            (restrictHom_comp_ofRestrict i U)).inv ≫
          Functor.whiskerRight (modulePullbackRestrictIso X U).hom
            (modulePullback (restrictHom i U)) := by
  rw [restrictPullbackIso_eq, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom, Iso.symm_hom,
    modulePullbackSquareIso_inv]
  simp only [Category.assoc]

/-- `AlgebraicGeometry.RingedSpace.restrictPullbackIso_hom` at an `𝒪_X`-module. -/
theorem restrictPullbackIso_hom_app (M : SheafOfModules.{u} (structureSheafRing X)) :
    (restrictPullbackIso i U).hom.app M =
      (modulePullbackRestrictIso Z ((Opens.map i.hom.base).obj U)).inv.app
          ((modulePullback i).obj M) ≫
        (modulePullbackSquareIso (Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)
            (X.ofRestrict U.isOpenEmbedding) (restrictHom i U) i
            (restrictHom_comp_ofRestrict i U)).inv.app M ≫
          (modulePullback (restrictHom i U)).map
            ((modulePullbackRestrictIso X U).hom.app M) :=
  congrArg (fun α : modulePullback i ⋙ moduleRestrict Z ((Opens.map i.hom.base).obj U) ⟶
      moduleRestrict X U ⋙ modulePullback (restrictHom i U) => α.app M)
    (restrictPullbackIso_hom i U)

end AlgebraicGeometry.RingedSpace

namespace Stacks.ClosedImmersion

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) (U : Opens X.carrier)

/-- **`Stacks.ClosedImmersion.restrictConormalSheafIso` is `(i|_V)^*` of
`Stacks.ClosedImmersion.restrictIdealSheafIso`.** Read through
`AlgebraicGeometry.RingedSpace.modulePullbackRestrictIso` on both sides and twisted by
`RingedSpaceModuleAdjunction.modulePullbackSquareIso` for the restriction square, the
conormal-sheaf transport is the pullback along `i|_V` of the ideal-sheaf transport. -/
theorem squareIso_hom_comp_restrictConormal :
    (modulePullbackSquareIso (Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)
          (X.ofRestrict U.isOpenEmbedding) (restrictHom i U) i
          (restrictHom_comp_ofRestrict i U)).hom.app (idealSheaf i) ≫
        (modulePullbackRestrictIso Z ((Opens.map i.hom.base).obj U)).hom.app (conormalSheaf i) ≫
          (restrictConormalSheafIso i U).hom =
      (modulePullback (restrictHom i U)).map
        ((modulePullbackRestrictIso X U).hom.app (idealSheaf i) ≫
          (restrictIdealSheafIso i U).hom) := by
  rw [restrictConormalSheafIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    restrictPullbackIso_hom_app, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- **The transports across the restriction square carry the conormal quotient map of `i` to that
of `i|_V`.** Both sides are the two ways around the square
```
ℐ_i -----------η_i-----------→ i_* 𝒞_i
|                                 |
↓                                 ↓
(ι_U)_* ℐ_{i|_V} ---→ (ι_U)_*((i|_V)_* 𝒞_{i|_V})
```
whose vertical morphisms are the canonical restriction-of-sections maps: on the left the unit of
`(ι_U)^* ⊣ (ι_U)_*` followed by `(ι_U)_*` of `Stacks.ClosedImmersion.restrictIdealSheafIso`, on
the right `i_*` of the unit of `(ι_V)^* ⊣ (ι_V)_*` followed by
`RingedSpaceModuleAdjunction.modulePushforwardSquareIso` and by
`(ι_U)_*((i|_V)_*)` of `Stacks.ClosedImmersion.restrictConormalSheafIso`. The bottom edge is the
conormal quotient map of `i|_V`, pushed forward to `X`. -/
theorem restrictConormalSheafIso_comp_unit :
    (modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding)).unit.app
          (idealSheaf i) ≫
        (modulePushforward (X.ofRestrict U.isOpenEmbedding)).map
          ((modulePullbackRestrictIso X U).hom.app (idealSheaf i) ≫
            (restrictIdealSheafIso i U).hom ≫
              (modulePullbackPushforwardAdjunction (restrictHom i U)).unit.app
                (idealSheaf (restrictHom i U))) =
      (modulePullbackPushforwardAdjunction i).unit.app (idealSheaf i) ≫
        (modulePushforward i).map
            ((modulePullbackPushforwardAdjunction
              (Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)).unit.app
                (conormalSheaf i)) ≫
          (modulePushforwardSquareIso
                (Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)
                (X.ofRestrict U.isOpenEmbedding) (restrictHom i U) i
                (restrictHom_comp_ofRestrict i U)).inv.app
              ((modulePullback (Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)).obj
                (conormalSheaf i)) ≫
            (modulePushforward (X.ofRestrict U.isOpenEmbedding)).map
              ((modulePushforward (restrictHom i U)).map
                ((modulePullbackRestrictIso Z ((Opens.map i.hom.base).obj U)).hom.app
                    (conormalSheaf i) ≫
                  (restrictConormalSheafIso i U).hom)) := by
  have hnat : (modulePullbackRestrictIso X U).hom.app (idealSheaf i) ≫
      (restrictIdealSheafIso i U).hom ≫
        (modulePullbackPushforwardAdjunction (restrictHom i U)).unit.app
          (idealSheaf (restrictHom i U)) =
      (modulePullbackPushforwardAdjunction (restrictHom i U)).unit.app
          ((modulePullback (X.ofRestrict U.isOpenEmbedding)).obj (idealSheaf i)) ≫
        (modulePushforward (restrictHom i U)).map
          ((modulePullback (restrictHom i U)).map
            ((modulePullbackRestrictIso X U).hom.app (idealSheaf i) ≫
              (restrictIdealSheafIso i U).hom)) := by
    have h := (modulePullbackPushforwardAdjunction (restrictHom i U)).unit.naturality
      ((modulePullbackRestrictIso X U).hom.app (idealSheaf i) ≫ (restrictIdealSheafIso i U).hom)
    simpa only [Functor.id_map, Functor.comp_map, Category.assoc] using h
  have hkey : ((modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding)).unit.app
          (idealSheaf i) ≫
        (modulePushforward (X.ofRestrict U.isOpenEmbedding)).map
          ((modulePullbackPushforwardAdjunction (restrictHom i U)).unit.app
            ((modulePullback (X.ofRestrict U.isOpenEmbedding)).obj (idealSheaf i)))) ≫
      (modulePushforward (restrictHom i U) ⋙
          modulePushforward (X.ofRestrict U.isOpenEmbedding)).map
          ((modulePullbackSquareIso
              (Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)
              (X.ofRestrict U.isOpenEmbedding) (restrictHom i U) i
              (restrictHom_comp_ofRestrict i U)).hom.app (idealSheaf i)) ≫
        (modulePushforwardSquareIso
            (Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)
            (X.ofRestrict U.isOpenEmbedding) (restrictHom i U) i
            (restrictHom_comp_ofRestrict i U)).hom.app
          ((modulePullback (Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)).obj
            (conormalSheaf i)) =
      (modulePullbackPushforwardAdjunction i).unit.app (idealSheaf i) ≫
        (modulePushforward i).map
          ((modulePullbackPushforwardAdjunction
            (Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)).unit.app
              (conormalSheaf i)) :=
    unit_modulePullbackSquareIso
      (Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)
      (X.ofRestrict U.isOpenEmbedding) (restrictHom i U) i (restrictHom_comp_ofRestrict i U)
      (idealSheaf i)
  rw [hnat, ← squareIso_hom_comp_restrictConormal i U]
  simp only [Functor.comp_map, CategoryTheory.Functor.map_comp] at hkey ⊢
  simp only [← Category.assoc] at hkey ⊢
  rw [← hkey]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- **`Stacks.ClosedImmersion.restrictConormalSheafIso_comp_unit` for a morphism of schemes.**
The same commuting square, with the ringed-space data read off a morphism of schemes `i : Z ⟶ X`
and an open `V` of `X`. -/
theorem restrictConormalSheafIso_comp_unit_scheme {Z X : Scheme.{u}} (i : Z ⟶ X) (V : X.Opens) :
    (modulePullbackPushforwardAdjunction (X.toSheafedSpace.ofRestrict
          V.isOpenEmbedding)).unit.app (idealSheaf i.toLRSHom.toShHom) ≫
        (modulePushforward (X.toSheafedSpace.ofRestrict V.isOpenEmbedding)).map
          ((modulePullbackRestrictIso X.toSheafedSpace V).hom.app
              (idealSheaf i.toLRSHom.toShHom) ≫
            (restrictIdealSheafIso i.toLRSHom.toShHom V).hom ≫
              (modulePullbackPushforwardAdjunction
                (restrictHom i.toLRSHom.toShHom V)).unit.app
                (idealSheaf (restrictHom i.toLRSHom.toShHom V))) =
      (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
          (idealSheaf i.toLRSHom.toShHom) ≫
        (modulePushforward i.toLRSHom.toShHom).map
            ((modulePullbackPushforwardAdjunction (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).unit.app
                (conormalSheaf i.toLRSHom.toShHom)) ≫
          (modulePushforwardSquareIso
                (Z.toSheafedSpace.ofRestrict
                  ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)
                (X.toSheafedSpace.ofRestrict V.isOpenEmbedding)
                (restrictHom i.toLRSHom.toShHom V) i.toLRSHom.toShHom
                (restrictHom_comp_ofRestrict i.toLRSHom.toShHom V)).inv.app
              ((modulePullback (Z.toSheafedSpace.ofRestrict
                ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).obj
                (conormalSheaf i.toLRSHom.toShHom)) ≫
            (modulePushforward (X.toSheafedSpace.ofRestrict V.isOpenEmbedding)).map
              ((modulePushforward (restrictHom i.toLRSHom.toShHom V)).map
                ((modulePullbackRestrictIso Z.toSheafedSpace
                    ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.app
                    (conormalSheaf i.toLRSHom.toShHom) ≫
                  (restrictConormalSheafIso i.toLRSHom.toShHom V).hom)) :=
  restrictConormalSheafIso_comp_unit i.toLRSHom.toShHom V

end Stacks.ClosedImmersion

end
