module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictPullback
public import StacksFrontier.AlgebraicGeometry.ConormalOpenFactorizations.Basic
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf

/-!
# The conormal sheaf does not depend on the open the immersion is factored through

Let `i : Z ⟶ X` be an immersion of schemes. [Stacks Project, Tag 01R2] defines its conormal
sheaf as `(i')^* ℐ_{i'}` for the canonical factorization `i = i' ≫ ι_U` through the open
`U = X ∖ ∂Z` (`AlgebraicGeometry.Scheme.Hom.coborderRange`), on which `i'` is a closed
immersion. The first assertion of [Stacks Project, Tag 01R3] part (1) is that *any* open `U`
through which `i` factors as a closed immersion gives the same answer.

This file proves that, and the proof needs no hypothesis on the factorization at all: for a
morphism of ringed spaces `g : Z ⟶ X|_U` the ideal sheaf of `g ≫ ι_U` pulls back along `ι_U` to
the ideal sheaf of `g`, so the conormal sheaf of `g` is the conormal sheaf of `g ≫ ι_U`. Any two
factorizations of one `i` are then compared through the common value at `i` itself.

The three facts about an open immersion `ι_U : X|_U ⟶ X` that make this work are proved in
`StacksFrontier.AlgebraicGeometry.Conormal.RestrictPullback`: the counit of `ι_U^* ⊣ (ι_U)_*` is an
isomorphism, the transpose `ι_U^* 𝒪_X ⟶ 𝒪_{X|U}` of the structure-sheaf map is an isomorphism,
and `ι_U^*` is left exact. Given them, `ι_U^*` applied to the structure-sheaf map of `g ≫ ι_U`
is the structure-sheaf map of `g` conjugated by those two isomorphisms
(`Stacks.ClosedImmersion.modulePullback_structureSheafModuleHom_comp_counit`), so the two
kernels agree.

Note what is *not* needed: no comparison of `↥U` with `↥(ι_W⁻¹U)` for a second open `W`, and no
containment `U ≤ i.coborderRange`. Going through
`Stacks.ClosedImmersion.restrictConormalSheafIso` — the statement that the conormal sheaf is
local on the ambient space — would require both, because its restricted source and target are
`AlgebraicGeometry.SheafedSpace.ofRestrict`s of other restrictions. Conjugating the
structure-sheaf map instead keeps every object in the vocabulary the statement is already
written in.

## Main definitions

* `Stacks.ClosedImmersion.idealSheafOfRestrictIso` is `ι_U^* ℐ_{g ≫ ι_U} ≅ ℐ_g`.
* `Stacks.ClosedImmersion.conormalSheafOfRestrictIso` is `𝒞_{g ≫ ι_U} ≅ 𝒞_g`.
* `Stacks.Immersion.conormalSheafFactorIso` is the same isomorphism for schemes.

## Main results

* `Stacks.ClosedImmersion.modulePullback_structureSheafModuleHom_comp_counit` is the conjugation
  identity the file turns on.
* `Stacks.ClosedImmersion.idealSheafOfRestrictIso_hom_comp_ι` and
  `Stacks.ClosedImmersion.conormalSheafOfRestrictIso_hom_comp_pullback_ι` pin down the two
  isomorphisms above; `Stacks.Immersion.conormalSheafFactorIso_hom_comp_pullback_ι` is the
  second of them for schemes. A bundled isomorphism whose type does not mention its
  characterisation asserts nothing by itself, so each one is recorded.
* `Stacks.Immersion.idealSheafOfRestrictIso_eq_pullbackIdealSheafIso` and
  `Stacks.Immersion.conormalSheafFactorIso_eq_pullbackIdealSheafCompIso` identify the two
  isomorphisms with `Stacks.IdealSheafRestrict.pullbackIdealSheafIso` and
  `Stacks.Conormal.pullbackIdealSheafCompIso`, the restriction-theoretic constructions of the
  same comparisons.
* `Stacks.Immersion.conormalSheafFactorIso_hom_comp_conormalSheafIsoPullbackIdealSheaf_hom`
  pins [Stacks Project, Tag 01R3] part (1)'s isomorphism
  `Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf` through the two
  `Stacks.Immersion.conormalSheafFactorIso`s.

[Stacks Project, Tag 01R3] part (1) itself — the isomorphism, its normalization at the defining
factorization, and the quotient map `ℐ_{i'} ⟶ (i')_* 𝒞_{Z/X}` it makes available — is
`Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf`,
`Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf_liftCoborder` and
`Stacks.Conormal.conormalQuotientMap`.

## Implementation notes

`Stacks.Immersion.conormalSheafFactorIso` is stated for the morphism `i' ≫ U.ι` rather than for
an arbitrary `i` with a hypothesis `i' ≫ U.ι = i`, so that it carries no `CategoryTheory.eqToIso`
and its characterisation is a clean equation. The `eqToHom` comparing the two factorizations of
`i` appears once, in
`Stacks.Immersion.conormalSheafFactorIso_hom_comp_conormalSheafIsoPullbackIdealSheaf_hom`.

`AlgebraicGeometry.Scheme.Opens.toScheme` and `AlgebraicGeometry.Scheme.Opens.ι` are, on
underlying ringed spaces, `AlgebraicGeometry.SheafedSpace.restrict` and
`AlgebraicGeometry.SheafedSpace.ofRestrict` by definition, and
`AlgebraicGeometry.Scheme.Hom.toLRSHom` followed by
`AlgebraicGeometry.LocallyRingedSpace.Hom.toShHom` is functorial on the nose; so the passage
from schemes to ringed spaces is by `rfl` throughout. The statements are nevertheless given at
the ringed-space level first, because that is where
`Stacks.ClosedImmersion.idealSheaf` and `Stacks.ClosedImmersion.conormalSheaf` are defined.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

namespace Stacks.ClosedImmersion

variable {Z X : RingedSpace.{u, u}} (U : Opens X.carrier)
  (g : Z ⟶ X.restrict U.isOpenEmbedding)

/-! ### The structure-sheaf map of `g ≫ ι_U`, pulled back along `ι_U` -/

/-- **The structure-sheaf map of `g ≫ ι_U`, pulled back along `ι_U`, is the structure-sheaf map
of `g`** — conjugated by the two isomorphisms `ι_U^* 𝒪_X ≅ 𝒪_{X|U}` and
`ι_U^*((ι_U)_*(g_* 𝒪_Z)) ≅ g_* 𝒪_Z`.

Both sides are transposes under `ι_U^* ⊣ (ι_U)_*` of the structure-sheaf map of `g ≫ ι_U`: the
left-hand side by the formula for the inverse hom-set bijection, the right-hand side because
transposing is natural in the target and the transpose of `ι_U^* 𝒪_X ⟶ 𝒪_{X|U}` is the
structure-sheaf map of `ι_U`, which composed with `(ι_U)_*` of the structure-sheaf map of `g` is
the cocycle formula for `g ≫ ι_U`.

This is the whole content of the file: it says the two ideal sheaves below are the kernels of one
morphism read in two vocabularies. -/
theorem modulePullback_structureSheafModuleHom_comp_counit :
    (modulePullback (X.ofRestrict U.isOpenEmbedding)).map
          (structureSheafModuleHom (g ≫ X.ofRestrict U.isOpenEmbedding)) ≫
        (modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding)).counit.app
          ((modulePushforward g).obj (SheafOfModules.unit (structureSheafRing Z))) =
      modulePullbackUnitToUnit (X.ofRestrict U.isOpenEmbedding) ≫
        structureSheafModuleHom g := by
  refine ((modulePullbackPushforwardAdjunction
    (X.ofRestrict U.isOpenEmbedding)).homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_right, homEquiv_modulePullbackUnitToUnit]
  exact (congrArg ((modulePullbackPushforwardAdjunction
      (X.ofRestrict U.isOpenEmbedding)).homEquiv _ _)
    (Adjunction.homEquiv_counit _ _ _ _).symm).trans (Equiv.apply_symm_apply _ _)

/-! ### The ideal sheaf of a factorization through an open subspace -/

/-- **`ι_U^* ℐ_{g ≫ ι_U} ≅ ℐ_g`.** For a morphism of ringed spaces `g : Z ⟶ X|_U` the ideal
sheaf of `g ≫ ι_U` pulls back along the open immersion `ι_U` to the ideal sheaf of `g`.

Pullback along an open immersion is left exact
(`AlgebraicGeometry.RingedSpace.modulePullback_ofRestrict_preservesFiniteLimits`), so the
left-hand side is the kernel of the pulled-back structure-sheaf map; and that morphism is the
structure-sheaf map of `g` conjugated by two isomorphisms, by
`Stacks.ClosedImmersion.modulePullback_structureSheafModuleHom_comp_counit`. The isomorphism is
pinned by `Stacks.ClosedImmersion.idealSheafOfRestrictIso_hom_comp_ι`. -/
def idealSheafOfRestrictIso :
    (modulePullback (X.ofRestrict U.isOpenEmbedding)).obj
        (idealSheaf (g ≫ X.ofRestrict U.isOpenEmbedding)) ≅ idealSheaf g :=
  PreservesKernel.iso (modulePullback (X.ofRestrict U.isOpenEmbedding))
      (structureSheafModuleHom (g ≫ X.ofRestrict U.isOpenEmbedding)) ≪≫
    kernel.mapIso _ (structureSheafModuleHom g)
      (modulePullbackUnitOfRestrictIso X U)
      (modulePullbackPushforwardCounitOfRestrictIso X U
        ((modulePushforward g).obj (SheafOfModules.unit (structureSheafRing Z))))
      (modulePullback_structureSheafModuleHom_comp_counit U g)

/-- **The characterising property of `Stacks.ClosedImmersion.idealSheafOfRestrictIso`.**
Followed by the inclusion of `ℐ_g` into `𝒪_{X|U}` it is the pullback along `ι_U` of the
inclusion of `ℐ_{g ≫ ι_U}` into `𝒪_X`, read in `𝒪_{X|U}` through
`RingedSpaceModuleAdjunction.modulePullbackUnitToUnit`. Since the inclusion of an ideal
sheaf is a monomorphism, this determines the isomorphism. -/
theorem idealSheafOfRestrictIso_hom_comp_ι :
    (idealSheafOfRestrictIso U g).hom ≫ idealSheafι g =
      (modulePullback (X.ofRestrict U.isOpenEmbedding)).map
          (idealSheafι (g ≫ X.ofRestrict U.isOpenEmbedding)) ≫
        modulePullbackUnitToUnit (X.ofRestrict U.isOpenEmbedding) := by
  have h1 : (kernel.mapIso
        ((modulePullback (X.ofRestrict U.isOpenEmbedding)).map
          (structureSheafModuleHom (g ≫ X.ofRestrict U.isOpenEmbedding)))
        (structureSheafModuleHom g) (modulePullbackUnitOfRestrictIso X U)
        (modulePullbackPushforwardCounitOfRestrictIso X U
          ((modulePushforward g).obj (SheafOfModules.unit (structureSheafRing Z))))
        (modulePullback_structureSheafModuleHom_comp_counit U g)).hom ≫
      idealSheafι g =
      kernel.ι ((modulePullback (X.ofRestrict U.isOpenEmbedding)).map
          (structureSheafModuleHom (g ≫ X.ofRestrict U.isOpenEmbedding))) ≫
        modulePullbackUnitToUnit (X.ofRestrict U.isOpenEmbedding) :=
    kernel.lift_ι _ _ _
  have h2 : (PreservesKernel.iso (modulePullback (X.ofRestrict U.isOpenEmbedding))
        (structureSheafModuleHom (g ≫ X.ofRestrict U.isOpenEmbedding))).hom ≫
      kernel.ι ((modulePullback (X.ofRestrict U.isOpenEmbedding)).map
        (structureSheafModuleHom (g ≫ X.ofRestrict U.isOpenEmbedding))) =
      (modulePullback (X.ofRestrict U.isOpenEmbedding)).map
        (idealSheafι (g ≫ X.ofRestrict U.isOpenEmbedding)) := by
    rw [← PreservesKernel.iso_inv_ι, Iso.hom_inv_id_assoc]
    rfl
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (PreservesKernel.iso (modulePullback
        (X.ofRestrict U.isOpenEmbedding))
          (structureSheafModuleHom (g ≫ X.ofRestrict U.isOpenEmbedding))).hom ≫ z) h1).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ modulePullbackUnitToUnit
          (X.ofRestrict U.isOpenEmbedding)) h2)))

/-! ### The conormal sheaf of a factorization through an open subspace -/

/-- **`𝒞_{g ≫ ι_U} ≅ 𝒞_g`.** The conormal sheaf of a morphism of ringed spaces `g : Z ⟶ X|_U`
agrees with the conormal sheaf of `g ≫ ι_U : Z ⟶ X`.

The conormal sheaf of `g ≫ ι_U` is `(g ≫ ι_U)^* ℐ_{g ≫ ι_U} = g^*(ι_U^* ℐ_{g ≫ ι_U})`, by the
composition law `RingedSpaceModuleAdjunction.modulePullbackComp`, and the inner pullback
is `ℐ_g` by `Stacks.ClosedImmersion.idealSheafOfRestrictIso`. Pinned by
`Stacks.ClosedImmersion.conormalSheafOfRestrictIso_hom_comp_pullback_ι`. -/
def conormalSheafOfRestrictIso :
    conormalSheaf (g ≫ X.ofRestrict U.isOpenEmbedding) ≅ conormalSheaf g :=
  (modulePullbackComp g (X.ofRestrict U.isOpenEmbedding)).app
      (idealSheaf (g ≫ X.ofRestrict U.isOpenEmbedding)) ≪≫
    (modulePullback g).mapIso (idealSheafOfRestrictIso U g)

/-- **The characterising property of `Stacks.ClosedImmersion.conormalSheafOfRestrictIso`.** Read
inside `g^* 𝒪_{X|U}` — that is, after mapping both conormal sheaves along the pullback of the
relevant ideal-sheaf inclusion — the isomorphism is the composition law for pullback followed by
`RingedSpaceModuleAdjunction.modulePullbackUnitToUnit`.

Since `RingedSpaceModuleAdjunction.modulePullbackComp` is itself characterised by
`RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackComp_hom`, and the ideal-sheaf
inclusions are monomorphisms, this fixes the isomorphism rather than leaving it an arbitrary
witness of its type. -/
theorem conormalSheafOfRestrictIso_hom_comp_pullback_ι :
    (conormalSheafOfRestrictIso U g).hom ≫ (modulePullback g).map (idealSheafι g) =
      (modulePullback (g ≫ X.ofRestrict U.isOpenEmbedding)).map
          (idealSheafι (g ≫ X.ofRestrict U.isOpenEmbedding)) ≫
        (modulePullbackComp g (X.ofRestrict U.isOpenEmbedding)).hom.app
            (SheafOfModules.unit (structureSheafRing X)) ≫
          (modulePullback g).map
            (modulePullbackUnitToUnit (X.ofRestrict U.isOpenEmbedding)) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => (modulePullbackComp g (X.ofRestrict U.isOpenEmbedding)).hom.app
          (idealSheaf (g ≫ X.ofRestrict U.isOpenEmbedding)) ≫ z)
        ((((modulePullback g).map_comp _ _).symm.trans
          (congrArg (modulePullback g).map (idealSheafOfRestrictIso_hom_comp_ι U g))).trans
            ((modulePullback g).map_comp _ _))).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (modulePullback g).map (modulePullbackUnitToUnit
            (X.ofRestrict U.isOpenEmbedding)))
          ((modulePullbackComp g (X.ofRestrict U.isOpenEmbedding)).hom.naturality
            (idealSheafι (g ≫ X.ofRestrict U.isOpenEmbedding))).symm).trans
          (Category.assoc _ _ _))))

end Stacks.ClosedImmersion

namespace Stacks.Immersion

open Stacks.ClosedImmersion

variable {Z X : Scheme.{u}}

/-- **`𝒞_{i' ≫ ι_U} ≅ 𝒞_{i'}` for schemes**: a morphism of schemes `i' : Z ⟶ U` into an open
subscheme of `X` has the same conormal sheaf as its composite with the inclusion `U ⟶ X`.

This is `Stacks.ClosedImmersion.conormalSheafOfRestrictIso` on the underlying ringed spaces; the
translation is by `rfl`, since `AlgebraicGeometry.Scheme.Opens.ι` is
`AlgebraicGeometry.SheafedSpace.ofRestrict` and passing to ringed spaces is functorial on the
nose. Pinned by `Stacks.Immersion.conormalSheafFactorIso_hom_comp_pullback_ι`. -/
def conormalSheafFactorIso (U : X.Opens) (i' : Z ⟶ U.toScheme) :
    conormalSheaf (i' ≫ U.ι).toLRSHom.toShHom ≅ conormalSheaf i'.toLRSHom.toShHom :=
  conormalSheafOfRestrictIso U i'.toLRSHom.toShHom

/-- **The characterising property of `Stacks.Immersion.conormalSheafFactorIso`**, which is
`Stacks.ClosedImmersion.conormalSheafOfRestrictIso_hom_comp_pullback_ι` read for schemes. -/
theorem conormalSheafFactorIso_hom_comp_pullback_ι (U : X.Opens) (i' : Z ⟶ U.toScheme) :
    (conormalSheafFactorIso U i').hom ≫
        (modulePullback i'.toLRSHom.toShHom).map (idealSheafι i'.toLRSHom.toShHom) =
      (modulePullback (i' ≫ U.ι).toLRSHom.toShHom).map
          (idealSheafι (i' ≫ U.ι).toLRSHom.toShHom) ≫
        (modulePullbackComp i'.toLRSHom.toShHom
              (X.toLocallyRingedSpace.toRingedSpace.ofRestrict U.isOpenEmbedding)).hom.app
            (SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toRingedSpace)) ≫
          (modulePullback i'.toLRSHom.toShHom).map (modulePullbackUnitToUnit
            (X.toLocallyRingedSpace.toRingedSpace.ofRestrict U.isOpenEmbedding)) :=
  conormalSheafOfRestrictIso_hom_comp_pullback_ι U i'.toLRSHom.toShHom

/-- **`ι_U^* ℐ_{i' ≫ ι_U} ≅ ℐ_{i'}` is the ideal-sheaf restriction isomorphism.** The
kernel-preservation construction of `Stacks.ClosedImmersion.idealSheafOfRestrictIso` and the
restriction construction of `Stacks.IdealSheafRestrict.pullbackIdealSheafIso` give the same
isomorphism: both commute with the inclusions of the two ideal sheaves into the two structure
sheaves, and those inclusions are monomorphisms. -/
theorem idealSheafOfRestrictIso_eq_pullbackIdealSheafIso (U : X.Opens) (i' : Z ⟶ U.toScheme) :
    idealSheafOfRestrictIso U i'.toLRSHom.toShHom =
      Stacks.IdealSheafRestrict.pullbackIdealSheafIso U.ι i' := by
  have hC : (Stacks.IdealSheafRestrict.pullbackIdealSheafIso U.ι i').hom ≫
        idealSheafι i'.toLRSHom.toShHom =
      (modulePullback U.ι.toLRSHom.toShHom).map
          (idealSheafι (i' ≫ U.ι).toLRSHom.toShHom) ≫
        modulePullbackUnitToUnit U.ι.toLRSHom.toShHom :=
    (Stacks.IdealSheafRestrict.pullbackIdealSheafIso_hom_comp_ι U.ι i').trans
      (congrArg (fun z => (modulePullback U.ι.toLRSHom.toShHom).map
          (idealSheafι (i' ≫ U.ι).toLRSHom.toShHom) ≫ z)
        (Stacks.Conormal.pullbackUnitIso_hom_eq_modulePullbackUnitToUnit U.ι))
  have : Mono (idealSheafι i'.toLRSHom.toShHom) :=
    inferInstanceAs (Mono (kernel.ι (structureSheafModuleHom i'.toLRSHom.toShHom)))
  exact Iso.ext ((cancel_mono (idealSheafι i'.toLRSHom.toShHom)).mp
    ((idealSheafOfRestrictIso_hom_comp_ι U i'.toLRSHom.toShHom).trans hC.symm))

/-- **`Stacks.Immersion.conormalSheafFactorIso` is
`Stacks.Conormal.pullbackIdealSheafCompIso`.** Both are the pullback composition isomorphism
followed by `(i')^*` of the ideal-sheaf restriction isomorphism, which is
`Stacks.Immersion.idealSheafOfRestrictIso_eq_pullbackIdealSheafIso`. -/
theorem conormalSheafFactorIso_eq_pullbackIdealSheafCompIso (U : X.Opens)
    (i' : Z ⟶ U.toScheme) :
    conormalSheafFactorIso U i' = Stacks.Conormal.pullbackIdealSheafCompIso i' U.ι :=
  congrArg (fun e => (modulePullbackComp i'.toLRSHom.toShHom
        (X.toLocallyRingedSpace.toRingedSpace.ofRestrict U.isOpenEmbedding)).app
          (idealSheaf (i' ≫ U.ι).toLRSHom.toShHom) ≪≫
        (modulePullback i'.toLRSHom.toShHom).mapIso e)
    (idealSheafOfRestrictIso_eq_pullbackIdealSheafIso U i')

/-- **The characterising property of `Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf`.**
Preceded by the identification of the conormal sheaf of `i` with that of its defining
factorization, it is the identification of the conormal sheaf of `i` with that of the given
factorization, up to the canonical comparison of the two spellings `i.liftCoborder ≫
i.coborderRange.ι` and `i' ≫ U.ι` of `i`.

Both `Stacks.Immersion.conormalSheafFactorIso`s are pinned by
`Stacks.Immersion.conormalSheafFactorIso_hom_comp_pullback_ι`, and
`CategoryTheory.eqToHom` of an equality of morphisms of schemes is canonical, so this fixes
`Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf` uniquely. It is the cocycle condition
`Stacks.Conormal.pullbackIdealSheafCompIso_hom_comp_isoOfCompEq_hom` for the factorization of
`ι_U` through `i.coborderRange`. -/
theorem conormalSheafFactorIso_hom_comp_conormalSheafIsoPullbackIdealSheaf_hom (i : Z ⟶ X)
    [IsImmersion i] (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hfac : i' ≫ U.ι = i) :
    (conormalSheafFactorIso i.coborderRange i.liftCoborder).hom ≫
        (Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf i U i' hfac).hom =
      eqToHom (congrArg (fun f : Z ⟶ X => conormalSheaf f.toLRSHom.toShHom)
          (i.liftCoborder_ι.trans hfac.symm)) ≫
        (conormalSheafFactorIso U i').hom := by
  rw [conormalSheafFactorIso_eq_pullbackIdealSheafCompIso,
    conormalSheafFactorIso_eq_pullbackIdealSheafCompIso,
    Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf]
  exact Stacks.Conormal.pullbackIdealSheafCompIso_hom_comp_isoOfCompEq_hom i'
    (X.homOfLE (Stacks.Conormal.le_coborderRange_of_comp_eq i U i' hfac)) i.coborderRange.ι
    U.ι (X.homOfLE_ι _) i.liftCoborder
    (Stacks.Conormal.comp_homOfLE_eq_liftCoborder i U i' hfac)
    (i.liftCoborder_ι.trans hfac.symm)

end Stacks.Immersion

end
