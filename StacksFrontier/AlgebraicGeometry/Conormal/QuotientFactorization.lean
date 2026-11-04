module

public import StacksFrontier.AlgebraicGeometry.Conormal.AffineSections

/-!
# The conormal quotient map does not depend on the open factorization

[Stacks Project, Tag 01R3] part (1) attaches to every closed-immersion factorization
`i = i' ≫ ι_U` of an immersion of schemes a quotient map
`Stacks.Conormal.conormalQuotientMap : ℐ_{i'} ⟶ (i')_* 𝒞_{Z/X}`. Different factorizations give
maps out of *different* ideal sheaves, living on different open subschemes of `X`, so they cannot
be compared directly. This file shows that they are all one map read in different vocabularies:
each of them, pushed forward to `X` and precomposed with the canonical comparison
`ℐ_i ⟶ (ι_U)_* ℐ_{i'}`, is the single map

`Stacks.Immersion.canonicalConormalQuotientMap : ℐ_i ⟶ i_* 𝒞_{Z/X}`

built from the unit of `i^* ⊣ i_*` and nothing else.

The point of the statement is that the right-hand side mentions no factorization. Since the
comparison on the left is itself the unit of `ι_U^* ⊣ (ι_U)_*` followed by the pushforward of a
pinned isomorphism, and on sections over an open `A ⊆ X` it is restriction of sections to the
largest open of `A` lying in `U`, this is exactly the compatibility of generators from two
different factorizations that [Stacks Project, Tag 01R3] part (1) needs, *before* any affine
computation enters.

## Main definitions

* `Stacks.ClosedImmersion.idealSheafOfRestrictComparison` is the canonical map
  `ℐ_{g ≫ ι_U} ⟶ (ι_U)_* ℐ_g` for a morphism of ringed spaces `g : Z ⟶ X|_U`, and
  `Stacks.Immersion.idealSheafComparison` is the same map for schemes, read at `i` itself.
* `Stacks.Immersion.conormalSheafSelfIso` identifies the conormal sheaf of an immersion of
  schemes, which [Stacks Project, Tag 01R2] defines through the factorization over
  `AlgebraicGeometry.Scheme.Hom.coborderRange`, with the ringed-space conormal sheaf of the
  immersion itself.
* `Stacks.Immersion.canonicalConormalQuotientMap` is the factorization-free quotient map
  `ℐ_i ⟶ i_* 𝒞_{Z/X}`.

## Main results

* `Stacks.ClosedImmersion.idealSheafOfRestrictComparison_comp_unit` is the ringed-space core: the
  comparison followed by `(ι_U)_*` of the unit of `g^* ⊣ g_*` is the unit of
  `(g ≫ ι_U)^* ⊣ (g ≫ ι_U)_*` followed by the pushforward of
  `Stacks.ClosedImmersion.conormalSheafOfRestrictIso`.
* `Stacks.Immersion.conormalQuotientMap_apply_idealSheafComparison` is the scheme-level
  consequence, on sections: every `Stacks.Conormal.conormalQuotientMap` sends a section of `ℐ_i`,
  compared along `Stacks.Immersion.idealSheafComparison`, to its image under the canonical map.
  That generators coming from two different open factorizations agree on any common open is
  `Stacks.Conormal.OpenFactorizations.conormalQuotientMap_eq_of_factorization`.
* `Stacks.ClosedImmersion.idealSheafOfRestrictComparison_comp_ι` and
  `Stacks.Immersion.idealSheafComparison_comp_ι` say the comparison is, on the underlying
  structure sheaves, the structure-sheaf map of `ι_U`, i.e. plain restriction of sections. This is
  what turns the previous items into statements about ambient ideal generators.

## Implementation notes

The ringed-space core is three rewrites: naturality of the unit of `g^* ⊣ g_*` in its argument,
`RingedSpaceModuleAdjunction.unit_modulePullbackComp` — which reads the pullback
composition isomorphism on units — and the definition of
`Stacks.ClosedImmersion.conormalSheafOfRestrictIso`, which is that very composition isomorphism
followed by `g^*` of `Stacks.ClosedImmersion.idealSheafOfRestrictIso`. Multiplicativity of
pushforward being an equality with identity components is what lets the three steps be composed
without a single comparison morphism surviving.

The scheme-level consequence is stated **on sections** rather than as an equality of morphisms of
sheaves of modules, and that is not a weakening but a necessity. The two targets
`(ι_U)_* ((i')_* 𝒞)` and `i_* 𝒞` are definitionally equal and not syntactically equal — the two
spellings `i' ≫ ι_U` and `i` of the immersion go through
`CategoryTheory.InducedCategory` differently — so a goal mentioning both is not type-correct at
`implicit` transparency and `rw` cannot build a motive for it; proving the morphism
equality instead runs out of heartbeats inside a single `whnf`. Over a *fixed* open the two objects
are literally the same module, because taking preimages of opens is multiplicative on the nose
(`RingedSpaceModuleAdjunction.opensMap_comp`), so the sectionwise statement has no such
mismatch and is what every consumer wants anyway.

The factorization hypothesis is carried by a `CategoryTheory.eqToHom` inside
`Stacks.Immersion.idealSheafComparison` and removed by `subst` in each proof. After the
substitution the `CategoryTheory.eqToHom` in the pin
`Stacks.Immersion.conormalSheafFactorIso_hom_comp_conormalSheafIsoPullbackIdealSheaf_hom` of
`Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf` is the one coming from
`AlgebraicGeometry.Scheme.Hom.liftCoborder_ι` alone, which is precisely the one
`Stacks.Immersion.conormalSheafSelfIso` is built from, so the two cancel; that cancellation is
`Stacks.Immersion.conormalSheafFactorIso_hom_comp_conormalSheafIsoPullbackIdealSheaf_inv`.

**No tag is claimed here.** The statements are the factorization-independence of the quotient
map, which is the *mechanism* behind two clauses of [Stacks Project, Tag 01R3] part (1), not
either clause: the tag asserts that the quotient map is an epimorphism with kernel `ℐ²`, and that
generators coming from different factorizations agree — the latter being a statement about
sections, which needs in addition that the ambient ideal lies in the ideal sheaf.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
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

/-- **The canonical comparison `ℐ_{g ≫ ι_U} ⟶ (ι_U)_* ℐ_g`.** The unit of `ι_U^* ⊣ (ι_U)_*` at the
ideal sheaf of `g ≫ ι_U`, followed by the pushforward of
`Stacks.ClosedImmersion.idealSheafOfRestrictIso`.

On sections over an open `A` of `X` it is restriction to the largest open of `A` lying in `U`, by
`Stacks.ClosedImmersion.idealSheafOfRestrictComparison_comp_ι` together with the description of
the structure-sheaf map of `ι_U`. -/
def idealSheafOfRestrictComparison :
    idealSheaf (g ≫ X.ofRestrict U.isOpenEmbedding) ⟶
      (modulePushforward (X.ofRestrict U.isOpenEmbedding)).obj (idealSheaf g) :=
  (modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding)).unit.app
      (idealSheaf (g ≫ X.ofRestrict U.isOpenEmbedding)) ≫
    (modulePushforward (X.ofRestrict U.isOpenEmbedding)).map (idealSheafOfRestrictIso U g).hom

/-- **The comparison is restriction of sections.** Read inside the structure sheaf — that is,
followed by `(ι_U)_*` of the inclusion `ℐ_g ⟶ 𝒪_{X|U}` — the comparison
`Stacks.ClosedImmersion.idealSheafOfRestrictComparison` is the inclusion
`ℐ_{g ≫ ι_U} ⟶ 𝒪_X` followed by the structure-sheaf map of `ι_U`.

Since the inclusion of an ideal sheaf is a monomorphism, and the structure-sheaf map of `ι_U` is
restriction of sections to the largest subopen lying in `U`, this determines the comparison and
identifies it on sections. The proof is `Stacks.ClosedImmersion.idealSheafOfRestrictIso_hom_comp_ι`
followed by naturality of the unit and
`RingedSpaceModuleAdjunction.structureSheafModuleHom_eq_unit_comp`. -/
theorem idealSheafOfRestrictComparison_comp_ι :
    idealSheafOfRestrictComparison U g ≫
        (modulePushforward (X.ofRestrict U.isOpenEmbedding)).map (idealSheafι g) =
      idealSheafι (g ≫ X.ofRestrict U.isOpenEmbedding) ≫
        structureSheafModuleHom (X.ofRestrict U.isOpenEmbedding) := by
  have hnat : (modulePullbackPushforwardAdjunction
          (X.ofRestrict U.isOpenEmbedding)).unit.app
        (idealSheaf (g ≫ X.ofRestrict U.isOpenEmbedding)) ≫
      (modulePushforward (X.ofRestrict U.isOpenEmbedding)).map
        ((modulePullback (X.ofRestrict U.isOpenEmbedding)).map
          (idealSheafι (g ≫ X.ofRestrict U.isOpenEmbedding))) =
      idealSheafι (g ≫ X.ofRestrict U.isOpenEmbedding) ≫
        (modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding)).unit.app
          (SheafOfModules.unit (structureSheafRing X)) := by
    have h := (modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding)).unit.naturality
      (idealSheafι (g ≫ X.ofRestrict U.isOpenEmbedding))
    simpa only [Functor.id_map, Functor.comp_map] using h.symm
  rw [idealSheafOfRestrictComparison, Category.assoc, ← CategoryTheory.Functor.map_comp,
    idealSheafOfRestrictIso_hom_comp_ι, CategoryTheory.Functor.map_comp, ← Category.assoc, hnat,
    Category.assoc, structureSheafModuleHom_eq_unit_comp]

/-- **The comparison carries the unit of `g^* ⊣ g_*` to the unit of
`(g ≫ ι_U)^* ⊣ (g ≫ ι_U)_*`.** This is the ringed-space core of the file: the quotient map of the
factorization `g` through the open subspace `U`, pushed forward to `X` along `ι_U` and preceded by
`Stacks.ClosedImmersion.idealSheafOfRestrictComparison`, is the unit of the adjunction for
`g ≫ ι_U` followed by the pushforward of
`Stacks.ClosedImmersion.conormalSheafOfRestrictIso`.

The proof is naturality of the unit of `g^* ⊣ g_*` in its argument, which moves
`Stacks.ClosedImmersion.idealSheafOfRestrictIso` past it, followed by
`RingedSpaceModuleAdjunction.unit_modulePullbackComp`; what is left is the definition of
`Stacks.ClosedImmersion.conormalSheafOfRestrictIso`. No comparison morphism for pushforwards
appears, because `RingedSpaceModuleAdjunction.modulePushforwardComp` has identity
components. -/
theorem idealSheafOfRestrictComparison_comp_unit :
    idealSheafOfRestrictComparison U g ≫
        (modulePushforward (X.ofRestrict U.isOpenEmbedding)).map
          ((modulePullbackPushforwardAdjunction g).unit.app (idealSheaf g)) =
      (modulePullbackPushforwardAdjunction (g ≫ X.ofRestrict U.isOpenEmbedding)).unit.app
          (idealSheaf (g ≫ X.ofRestrict U.isOpenEmbedding)) ≫
        (modulePushforward (g ≫ X.ofRestrict U.isOpenEmbedding)).map
          (conormalSheafOfRestrictIso U g).hom := by
  have hnat : (idealSheafOfRestrictIso U g).hom ≫
      (modulePullbackPushforwardAdjunction g).unit.app (idealSheaf g) =
      (modulePullbackPushforwardAdjunction g).unit.app
          ((modulePullback (X.ofRestrict U.isOpenEmbedding)).obj
            (idealSheaf (g ≫ X.ofRestrict U.isOpenEmbedding))) ≫
        (modulePushforward g).map
          ((modulePullback g).map (idealSheafOfRestrictIso U g).hom) := by
    have h := (modulePullbackPushforwardAdjunction g).unit.naturality
      (idealSheafOfRestrictIso U g).hom
    simpa only [Functor.id_map, Functor.comp_map] using h
  have hcomp := unit_modulePullbackComp g (X.ofRestrict U.isOpenEmbedding)
    (idealSheaf (g ≫ X.ofRestrict U.isOpenEmbedding))
  rw [idealSheafOfRestrictComparison, Category.assoc, ← CategoryTheory.Functor.map_comp, hnat,
    CategoryTheory.Functor.map_comp, ← Category.assoc, hcomp]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => (modulePullbackPushforwardAdjunction
        (g ≫ X.ofRestrict U.isOpenEmbedding)).unit.app
      (idealSheaf (g ≫ X.ofRestrict U.isOpenEmbedding)) ≫ z)
      ((modulePushforward (g ≫ X.ofRestrict U.isOpenEmbedding)).map_comp _ _).symm)

end Stacks.ClosedImmersion

namespace Stacks.Immersion

open Stacks.ClosedImmersion

variable {Z X : Scheme.{u}}

/-- **The canonical comparison `ℐ_i ⟶ (ι_U)_* ℐ_{i'}` for schemes.** For a closed-immersion
factorization `i = i' ≫ ι_U` of an immersion of schemes, this is
`Stacks.ClosedImmersion.idealSheafOfRestrictComparison` read at `i` itself.

The transport along the factorization hypothesis is put in front, so that the source is the ideal
sheaf of `i` on the nose and the target is the pushforward of the ideal sheaf of `i'`; both
spellings then appear uniformly in the statements below. On sections it is plain restriction, by
`Stacks.Immersion.idealSheafComparison_comp_ι`. -/
def idealSheafComparison (i : Z ⟶ X) (U : X.Opens) (i' : Z ⟶ U.toScheme)
    (hfac : i' ≫ U.ι = i) :
    idealSheaf i.toLRSHom.toShHom ⟶
      (modulePushforward U.ι.toLRSHom.toShHom).obj (idealSheaf i'.toLRSHom.toShHom) :=
  eqToHom (congrArg (fun f : Z ⟶ X => idealSheaf f.toLRSHom.toShHom) hfac.symm) ≫
    idealSheafOfRestrictComparison U i'.toLRSHom.toShHom

/-- At the factorization `i = i' ≫ ι_U` itself the transport in front of
`Stacks.Immersion.idealSheafComparison` is the identity, so the comparison is the ringed-space
one. -/
theorem idealSheafComparison_self (U : X.Opens) (i' : Z ⟶ U.toScheme) :
    idealSheafComparison (i' ≫ U.ι) U i' rfl =
      idealSheafOfRestrictComparison U i'.toLRSHom.toShHom :=
  Category.id_comp _

/-- **The scheme-level comparison is restriction of sections.** This is
`Stacks.ClosedImmersion.idealSheafOfRestrictComparison_comp_ι` read at `i`: inside the structure
sheaf the comparison is the inclusion `ℐ_i ⟶ 𝒪_X` followed by the structure-sheaf map of `ι_U`,
which on sections over an open `A` is restriction to the largest open of `A` lying in `U`.

Since the inclusion of an ideal sheaf is a monomorphism, this determines the comparison. -/
theorem idealSheafComparison_comp_ι (i : Z ⟶ X) (U : X.Opens) (i' : Z ⟶ U.toScheme)
    (hfac : i' ≫ U.ι = i) :
    idealSheafComparison i U i' hfac ≫
        (modulePushforward U.ι.toLRSHom.toShHom).map (idealSheafι i'.toLRSHom.toShHom) =
      idealSheafι i.toLRSHom.toShHom ≫ structureSheafModuleHom U.ι.toLRSHom.toShHom := by
  subst hfac
  exact (congrArg (fun z => z ≫ (modulePushforward U.ι.toLRSHom.toShHom).map
      (idealSheafι i'.toLRSHom.toShHom)) (idealSheafComparison_self U i')).trans
    (idealSheafOfRestrictComparison_comp_ι U i'.toLRSHom.toShHom)

/-- **`𝒞_{Z/X} ≅ i^* ℐ_i`.** [Stacks Project, Tag 01R2] defines the conormal sheaf of an immersion
`i : Z ⟶ X` through the canonical factorization over
`AlgebraicGeometry.Scheme.Hom.coborderRange`; this identifies it with the ringed-space conormal
sheaf of `i` itself, which mentions no factorization.

It is `Stacks.Immersion.conormalSheafFactorIso` at the defining factorization, read along
`AlgebraicGeometry.Scheme.Hom.liftCoborder_ι`. Both factors are canonical: the first is pinned by
`Stacks.Immersion.conormalSheafFactorIso_hom_comp_pullback_ι` and the second is a
`CategoryTheory.eqToIso` along an equality of morphisms of schemes. -/
def conormalSheafSelfIso (i : Z ⟶ X) [IsImmersion i] :
    conormalSheaf i.toLRSHom.toShHom ≅ conormalSheaf i.liftCoborder.toLRSHom.toShHom :=
  (eqToIso (congrArg (fun f : Z ⟶ X => conormalSheaf f.toLRSHom.toShHom)
      i.liftCoborder_ι)).symm ≪≫
    conormalSheafFactorIso i.coborderRange i.liftCoborder

/-- **The factorization-free quotient map `ℐ_i ⟶ i_* 𝒞_{Z/X}`.** The unit of `i^* ⊣ i_*` at the
ideal sheaf of `i`, read through `Stacks.Immersion.conormalSheafSelfIso`.

Every `Stacks.Immersion.conormalQuotientMap` is this map read through the comparison
`Stacks.Immersion.idealSheafComparison`, by
`Stacks.Immersion.conormalQuotientMap_apply_idealSheafComparison`; that is the content of the
file, and the reason this map is worth naming. -/
def canonicalConormalQuotientMap (i : Z ⟶ X) [IsImmersion i] :
    idealSheaf i.toLRSHom.toShHom ⟶
      (modulePushforward i.toLRSHom.toShHom).obj
        (conormalSheaf i.liftCoborder.toLRSHom.toShHom) :=
  (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
      (idealSheaf i.toLRSHom.toShHom) ≫
    (modulePushforward i.toLRSHom.toShHom).map (conormalSheafSelfIso i).hom

/-- **The pullback identification of a factorization cancels the identification of the conormal
sheaf of that factorization with the conormal sheaf of `i`.** This is the single cancellation
behind the file: `Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf` is pinned by
`Stacks.Immersion.conormalSheafFactorIso_hom_comp_conormalSheafIsoPullbackIdealSheaf_hom`
through the identification `Ψ_U` of the given factorization and the identification `Ψ₁` at the
defining one, so precomposing with `Ψ_U` leaves exactly
`Stacks.Immersion.conormalSheafSelfIso`. -/
theorem conormalSheafFactorIso_hom_comp_conormalSheafIsoPullbackIdealSheaf_inv (U : X.Opens)
    (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] [IsImmersion (i' ≫ U.ι)] :
    (conormalSheafFactorIso U i').hom ≫
        (Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf (i' ≫ U.ι) U i' rfl).inv =
      (conormalSheafSelfIso (i' ≫ U.ι)).hom := by
  have h := conormalSheafFactorIso_hom_comp_conormalSheafIsoPullbackIdealSheaf_hom
    (i' ≫ U.ι) U i' rfl
  rw [conormalSheafSelfIso, Iso.trans_hom, Iso.symm_hom, eqToIso.inv, Iso.comp_inv_eq,
    Category.assoc, h, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- **The quotient map of a factorization is the canonical quotient map, on sections.** For a
closed-immersion factorization `i = i' ≫ ι_U` of an immersion of schemes, an open `A` of `X` and a
section `y` of `ℐ_i` over `A`, the image of `y` under the quotient map of the factorization —
after comparing along `Stacks.Immersion.idealSheafComparison` — is its image under
`Stacks.Immersion.canonicalConormalQuotientMap`, which mentions no factorization. Both are read
over an open `T` of `Z` contained in the relevant preimage of `A`.

The two hypotheses `hT` and `hT'` are the same containment written for the two spellings `i` and
`i' ≫ ι_U` of the immersion; both are needed for the statement to be type-correct before the
factorization hypothesis is substituted.

This is `Stacks.ClosedImmersion.idealSheafOfRestrictComparison_comp_unit` on sections, followed by
`Stacks.Immersion.conormalSheafFactorIso_hom_comp_conormalSheafIsoPullbackIdealSheaf_inv`. -/
theorem conormalQuotientMap_apply_idealSheafComparison (i : Z ⟶ X) [IsImmersion i] (U : X.Opens)
    (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i) (A : X.Opens)
    (T : Z.Opens) (hT : T ≤ i ⁻¹ᵁ A) (hT' : T ≤ i' ⁻¹ᵁ (U.ι ⁻¹ᵁ A))
    (y : (idealSheaf i.toLRSHom.toShHom).val.obj (op A)) :
    (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map (homOfLE hT').op
        ((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (op (U.ι ⁻¹ᵁ A))
          ((idealSheafComparison i U i' hfac).val.app (op A) y)) =
      (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map (homOfLE hT).op
        ((canonicalConormalQuotientMap i).val.app (op A) y) := by
  subst hfac
  have hunit : ((modulePullbackPushforwardAdjunction i'.toLRSHom.toShHom).unit.app
          (idealSheaf i'.toLRSHom.toShHom)).val.app (op (U.ι ⁻¹ᵁ A))
        ((idealSheafOfRestrictComparison U i'.toLRSHom.toShHom).val.app (op A) y) =
      (conormalSheafFactorIso U i').hom.val.app (op ((i' ≫ U.ι) ⁻¹ᵁ A))
        (((modulePullbackPushforwardAdjunction (i' ≫ U.ι).toLRSHom.toShHom).unit.app
          (idealSheaf (i' ≫ U.ι).toLRSHom.toShHom)).val.app (op A) y) :=
    congr($(idealSheafOfRestrictComparison_comp_unit U i'.toLRSHom.toShHom).val.app (op A) y)
  have hkey : (Stacks.Conormal.conormalQuotientMap (i' ≫ U.ι) U i' rfl).val.app
          (op (U.ι ⁻¹ᵁ A))
        ((idealSheafComparison (i' ≫ U.ι) U i' rfl).val.app (op A) y) =
      (canonicalConormalQuotientMap (i' ≫ U.ι)).val.app (op A) y :=
    (congrArg (fun w => (Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf
        (i' ≫ U.ι) U i' rfl).inv.val.app (op ((i' ≫ U.ι) ⁻¹ᵁ A)) w) hunit).trans
      (congr($(conormalSheafFactorIso_hom_comp_conormalSheafIsoPullbackIdealSheaf_inv U
          i').val.app (op ((i' ≫ U.ι) ⁻¹ᵁ A))
        (((modulePullbackPushforwardAdjunction (i' ≫ U.ι).toLRSHom.toShHom).unit.app
          (idealSheaf (i' ≫ U.ι).toLRSHom.toShHom)).val.app (op A) y)))
  rw [Subsingleton.elim (homOfLE hT') (homOfLE hT), hkey]
  rfl

end Stacks.Immersion

end
