module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Locality

/-!
# The generator formula for the locality isomorphism of the conormal sheaf

This file closes the one gap that the part (2) assertions of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3) were waiting on.

## The gap, and that it is the only one

The part (2) identification of the conormal sections over an affine open with `Ideal.Cotangent`
is assembled in `StacksFrontier.AlgebraicGeometry.CotangentAppIso.Sections` out of six factors.
Five of them are described on a named section already: the two pushforward comparisons and the
two restriction-of-scalars comparisons are the identity or a presheaf restriction map, the
source-slot junction is characterized through the units by
`Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare_unit`, the
pseudofunctoriality factor by
`Stacks.PullbackPseudofunctor.unit_comp_map_modulePullbackCompIso_hom_app`, and the affine model
`Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent` carries its own generator formula.

The sixth is the **locality comparison**, and it had no description on sections anywhere in the
tree. Three module docstrings record this as the missing step; the engine
`Stacks.Conormal.CotangentAppIso.restrictAffineModelIso` takes that comparison as a bare
hypothesis precisely because nothing could be said about it.

## What was actually missing

The obstruction was **not** that the adjoint characterization is unusable. It is
`Stacks.Conormal.Locality.unit_comp_map_pullbackRestrictIsoOf`, an equality of morphisms of
sheaves of modules written in terms of two *composite* adjunctions,
`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictAdjunction` and
`restrictPullbackAdjunction`. The question nobody had asked is what those two composite units do
on a section, and the answer is that **both reduce by `rfl`**:

* the unit of `pullbackRestrictAdjunction` on sections over `O` is the unit of
  `f^* ⊣ f_*` followed by one presheaf restriction map (`pullbackRestrictAdjunction_unit_app`);
* the unit of `restrictPullbackAdjunction`, corrected by
  `AlgebraicGeometry.Scheme.Modules.pushforwardCongr` as the characterization requires, is one
  presheaf restriction map followed by the unit of `(f ∣_ O)^* ⊣ (f ∣_ O)_*`
  (`restrictPullbackAdjunction_unit_app`).

Both are `Adjunction.comp` followed by `CategoryTheory.Adjunction.ofNatIsoRight`, and every
correction factor involved — the two components of
`AlgebraicGeometry.Scheme.Modules.pushforwardComp` and the unit of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction` — is already `rfl` in Mathlib. So the
adjoint characterization descends to sections with no work at all, and
`pullbackRestrictIsoOf_unit_app` is a one-line term proof.

## Main results

* `Stacks.Conormal.Locality.pullbackRestrictIsoOf_unit_app`: **the generator formula for the
  locality comparison.** For a morphism `f : A ⟶ B`, a module `M` on `B`, an open `O` of `B` and
  an identification `ρ` of `M ∣_ O` with a module `N` on `O`, the comparison carries the
  restriction of the unit generator of `f^* M` named by a section `x` of `M` over `O` to the
  unit generator of `(f ∣_ O)^* N` named by the image of `x` under `ρ`.
* `Stacks.Conormal.Locality.conormalRestrictIso_unit_app`: the same at the ideal sheaf, where
  `ρ` is `Stacks.Conormal.Restriction.restrictIdealSheafIso'`.
* `Stacks.Conormal.Locality.restrictIdealSheafIso'_app_ι`: which section of the ideal sheaf of
  `f ∣_ O` that is — the one whose image in the structure sheaf is
  `AlgebraicGeometry.Scheme.Hom.appIso` of the image of `x`. Since the inclusion of an ideal
  sheaf is a monomorphism, this pins the section down
  (`Stacks.Conormal.Locality.idealSheaf_section_injective`).
* `Stacks.Conormal.Locality.conormalSheafRestrictIso_unit_app`: **the form Tag 01R3 needs.** For
  *any* closed-immersion factorization `i'` of an immersion `i`, the locality comparison carries
  the restriction of the quotient generator `Stacks.Conormal.conormalQuotientMap` to the unit
  generator of the ideal sheaf of `i' ∣_ O`. The factorization is arbitrary — nothing here is
  special to the coborder one, and no affineness, Noetherian or finiteness hypothesis appears.

## Why no tag is attached

Every assertion of [Stacks, Tag 01R3] is about `Ideal.Cotangent`, and nothing here mentions it:
this is the locality half of the part (2) route, and the remaining half — transporting the
generator through the affine model — is a separate assembly. The statements here carry no
labelled assertion of Tag 01R3, so no attribute is attached and none should be read into them.

## Universe situation

A single universe `u`, as in the statements of Tag 01R3.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.AffinePushforward

universe u

namespace Stacks.Conormal.Locality

/-! ### The two opens that the comparison lives between -/

/-- The open of `(f ⁻¹ᵁ O).toScheme` over which the adjoint characterization of the locality
comparison is read. Both spellings are the top open, reached from the two sides of the square
`(f ∣_ O) ≫ O.ι = (f ⁻¹ᵁ O).ι ≫ f`. -/
theorem preimage_ι_preimage_eq {A B : Scheme.{u}} (f : A ⟶ B) (O : B.Opens) :
    (f ⁻¹ᵁ O).ι ⁻¹ᵁ (f ⁻¹ᵁ O) = (f ∣_ O) ⁻¹ᵁ (O.ι ⁻¹ᵁ O) := by
  simp

/-! ### The two composite units, on sections -/

/-- **The unit of `pullbackRestrictAdjunction` on a section.** It is the unit of `f^* ⊣ f_*`
followed by one presheaf restriction map, on the nose.

`pullbackRestrictAdjunction` is `CategoryTheory.Adjunction.comp` of the pullback-pushforward
adjunction with `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, corrected on the right by
`AlgebraicGeometry.Scheme.Modules.pushforwardComp`; the components of that correction are the
identity and the unit of `restrictAdjunction` is a presheaf restriction map, both by `rfl` in
Mathlib. -/
theorem pullbackRestrictAdjunction_unit_app {A B : Scheme.{u}} (f : A ⟶ B) (O : B.Opens)
    (M : B.Modules) (x : M.val.obj (.op O)) :
    ((pullbackRestrictAdjunction f O).unit.app M).val.app (.op O) x =
      ((Scheme.Modules.pullback f).obj M).val.map
          (homOfLE ((f ⁻¹ᵁ O).ι.image_preimage_le (f ⁻¹ᵁ O))).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (.op O) x) :=
  rfl

/-- **The unit of `restrictPullbackAdjunction` on a section**, in the spelling the adjoint
characterization of the locality comparison uses — that is, after the correction by
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr` along
`AlgebraicGeometry.morphismRestrict_ι`. It is one presheaf restriction map followed by the unit
of `(f ∣_ O)^* ⊣ (f ∣_ O)_*`, again on the nose. -/
theorem restrictPullbackAdjunction_unit_app {A B : Scheme.{u}} (f : A ⟶ B) (O : B.Opens)
    (M : B.Modules) (x : M.val.obj (.op O)) :
    (((restrictPullbackAdjunction f O).ofNatIsoRight
        (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f O))).unit.app M).val.app
          (.op O) x =
      ((Scheme.Modules.pullback (f ∣_ O)).obj
          ((Scheme.Modules.restrictFunctor O.ι).obj M)).val.map
            (eqToHom (preimage_ι_preimage_eq f O)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ O)).unit.app
            ((Scheme.Modules.restrictFunctor O.ι).obj M)).val.app (.op (O.ι ⁻¹ᵁ O))
          (M.val.map (homOfLE (O.ι.image_preimage_le O)).op x)) :=
  rfl

/-- Equal morphisms of modules agree on every section. -/
private theorem val_app_apply_congr {X : Scheme.{u}} {P Q : X.Modules} {φ ψ : P ⟶ Q} (h : φ = ψ)
    (W : X.Opensᵒᵖ) (t : P.val.obj W) : φ.val.app W t = ψ.val.app W t := by
  subst h; rfl

/-! ### The generator formula for the locality comparison -/

/-- **The generator formula for `pullbackRestrictIsoOf`.** For a morphism `f : A ⟶ B`, a module
`M` on `B`, an open `O` of `B` and an identification `ρ` of the restriction of `M` to `O` with a
module `N` on `O`, the locality comparison carries the restriction to the top open of the unit
generator of `f^* M` attached to a section `x` of `M` over `O` to the unit generator of
`(f ∣_ O)^* N` attached to the image of `x` under `ρ`.

This is `unit_comp_map_pullbackRestrictIsoOf` read on sections over `O` at `x`, the two composite
units being computed by `pullbackRestrictAdjunction_unit_app` and
`restrictPullbackAdjunction_unit_app`. Since both of those hold by `rfl`, the whole statement is
a `congrArg` of the adjoint characterization and nothing else. -/
theorem pullbackRestrictIsoOf_unit_app {A B : Scheme.{u}} (f : A ⟶ B) (O : B.Opens)
    (M : B.Modules) (N : O.toScheme.Modules)
    (ρ : (Scheme.Modules.restrictFunctor O.ι).obj M ≅ N) (x : M.val.obj (.op O)) :
    (pullbackRestrictIsoOf f O M N ρ).hom.val.app (.op ((f ⁻¹ᵁ O).ι ⁻¹ᵁ (f ⁻¹ᵁ O)))
        (((Scheme.Modules.pullback f).obj M).val.map
          (homOfLE ((f ⁻¹ᵁ O).ι.image_preimage_le (f ⁻¹ᵁ O))).op
            (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (.op O) x)) =
      ((Scheme.Modules.pullback (f ∣_ O)).map ρ.hom).val.app
        (.op ((f ⁻¹ᵁ O).ι ⁻¹ᵁ (f ⁻¹ᵁ O)))
        (((Scheme.Modules.pullback (f ∣_ O)).obj
            ((Scheme.Modules.restrictFunctor O.ι).obj M)).val.map
              (eqToHom (preimage_ι_preimage_eq f O)).op
          (((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ O)).unit.app
              ((Scheme.Modules.restrictFunctor O.ι).obj M)).val.app (.op (O.ι ⁻¹ᵁ O))
            (M.val.map (homOfLE (O.ι.image_preimage_le O)).op x))) :=
  val_app_apply_congr (unit_comp_map_pullbackRestrictIsoOf f O M N ρ) (.op O) x

/-- Naturality of the unit of `f^* ⊣ f_*`, on a section: the inverse image of a morphism of
modules carries the unit generator attached to `t` to the unit generator attached to the image
of `t`. -/
theorem unit_naturality_app {A B : Scheme.{u}} (g : A ⟶ B) {M N : B.Modules} (ψ : M ⟶ N)
    (W : B.Opens) (t : M.val.obj (.op W)) :
    ((Scheme.Modules.pullback g).map ψ).val.app (.op (g ⁻¹ᵁ W))
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (.op W) t) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).val.app (.op W)
        (ψ.val.app (.op W) t) :=
  val_app_apply_congr ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality ψ).symm
    (.op W) t

/-- **`restrictIdealSheafIso'` on a named section.** The section of the ideal sheaf of `f ∣_ O`
that corresponds to a section `x` of the restriction to `O` of the ideal sheaf of `f` is the one
whose image in the structure sheaf is `AlgebraicGeometry.Scheme.Hom.appIso` of the image of `x`.

The inclusion of an ideal sheaf into the structure sheaf is injective on sections
(`idealSheaf_section_injective`), so this determines the corresponding section; that is what
makes the generator formula below a statement about a section named by an ambient element rather
than about an opaque transport. -/
theorem restrictIdealSheafIso'_app_ι {A B : Scheme.{u}} (f : A ⟶ B) (O : B.Opens)
    (W : O.toScheme.Opens)
    (x : ((Scheme.Modules.restrictFunctor O.ι).obj
      (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom)).val.obj (.op W)) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (f ∣_ O).toLRSHom.toShHom))).val.app (.op W)
        ((Restriction.restrictIdealSheafIso' f O).hom.val.app (.op W) x) =
      (O.ι.appIso W).hom
        ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom f.toLRSHom.toShHom))).val.app (.op (O.ι ''ᵁ W)) x) :=
  val_app_apply_congr (Restriction.restrictIdealSheafIso_hom_comp_ι f O) (.op W) x

/-- **The generator formula for `conormalRestrictIso`**: `pullbackRestrictIsoOf_unit_app` at the
ideal sheaf, with the unit of the target moved outside by `unit_naturality_app`. So the
comparison carries the restriction of the unit generator of `f^* I(f)` named by a section `y` of
`I(f)` over `O` to the unit generator of `(f ∣_ O)^* I(f ∣_ O)` named by the corresponding
section, which `restrictIdealSheafIso'_app_ι` identifies. -/
theorem conormalRestrictIso_unit_app {A B : Scheme.{u}} (f : A ⟶ B) (O : B.Opens)
    (y : (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.obj (.op O)) :
    (conormalRestrictIso f O).hom.val.app (.op ((f ⁻¹ᵁ O).ι ⁻¹ᵁ (f ⁻¹ᵁ O)))
        (((Scheme.Modules.pullback f).obj
            (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom)).val.map
          (homOfLE ((f ⁻¹ᵁ O).ι.image_preimage_le (f ⁻¹ᵁ O))).op
            (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
              (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom)).val.app (.op O) y)) =
      ((Scheme.Modules.pullback (f ∣_ O)).obj
          (Stacks.ClosedImmersion.idealSheaf (f ∣_ O).toLRSHom.toShHom)).val.map
            (eqToHom (preimage_ι_preimage_eq f O)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ O)).unit.app
            (Stacks.ClosedImmersion.idealSheaf (f ∣_ O).toLRSHom.toShHom)).val.app
              (.op (O.ι ⁻¹ᵁ O))
          ((Restriction.restrictIdealSheafIso' f O).hom.val.app (.op (O.ι ⁻¹ᵁ O))
            ((Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.map
              (homOfLE (O.ι.image_preimage_le O)).op y))) := by
  refine (pullbackRestrictIsoOf_unit_app f O _ _
    (Restriction.restrictIdealSheafIso' f O) y).trans ?_
  refine (PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullback (f ∣_ O)).map
      (Restriction.restrictIdealSheafIso' f O).hom).val
        (eqToHom (preimage_ι_preimage_eq f O)).op _).trans ?_
  exact congrArg (fun z => (((Scheme.Modules.pullback (f ∣_ O)).obj
      (Stacks.ClosedImmersion.idealSheaf (f ∣_ O).toLRSHom.toShHom)).val.map
        (eqToHom (preimage_ι_preimage_eq f O)).op) z)
    (unit_naturality_app (f ∣_ O) (Restriction.restrictIdealSheafIso' f O).hom (O.ι ⁻¹ᵁ O) _)

/-! ### The form Tag 01R3 needs -/

/-- Restriction along an open immersion, on a morphism and then on sections: it is the original
morphism on sections over the image open. -/
theorem restrictFunctor_map_val_app {Y : Scheme.{u}} (O : Y.Opens) {P Q : Y.Modules} (ψ : P ⟶ Q)
    (W : O.toScheme.Opens) (t : ((Scheme.Modules.restrictFunctor O.ι).obj P).val.obj (.op W)) :
    ((Scheme.Modules.restrictFunctor O.ι).map ψ).val.app (.op W) t =
      ψ.val.app (.op (O.ι ''ᵁ W)) t :=
  rfl

/-- `Stacks.Conormal.conormalQuotientMap` on a section: the unit generator of the ideal sheaf of
the factorization, carried by the inverse of the comparison isomorphism. This is its definition
read on sections. -/
theorem conormalQuotientMap_val_app {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    (O : U.toScheme.Opens)
    (y : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op O)) :
    (Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op O) y =
      (Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf i U i' hfac).inv.val.app
        (.op (i' ⁻¹ᵁ O))
        (((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
          (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom)).val.app (.op O) y) :=
  rfl

/-- The locality comparison of a factorization on sections: the comparison isomorphism of the
factorization, read over the image open, followed by `conormalRestrictIso`. This is its
definition, with the composite of two morphisms of sheaves and the restriction of a morphism both
read on sections, all three by `rfl`. -/
theorem conormalSheafRestrictIso_val_app {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    (O : U.toScheme.Opens) (W : (i' ⁻¹ᵁ O).toScheme.Opens)
    (t : ((Scheme.Modules.restrictFunctor (i' ⁻¹ᵁ O).ι).obj
      (Stacks.Conormal.conormalSheaf i)).val.obj (.op W)) :
    (conormalSheafRestrictIso i U i' hfac O).hom.val.app (.op W) t =
      (conormalRestrictIso i' O).hom.val.app (.op W)
        ((Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf i U i' hfac).hom.val.app
          (.op ((i' ⁻¹ᵁ O).ι ''ᵁ W)) t) :=
  rfl

/-- **The generator formula for `conormalSheafRestrictIso`, at an arbitrary factorization.** For
an immersion `i : Z ⟶ X`, *any* closed-immersion factorization `i' : Z ⟶ U` of it and any open
`O` of `U`, the locality comparison carries the restriction to the top open of the quotient
generator `Stacks.Conormal.conormalQuotientMap` attached to a section `y` of the ideal sheaf of
`i'` over `O` to the unit generator of the module pullback along `i' ∣_ O` of the ideal sheaf of
`i' ∣_ O`, attached to the corresponding section.

So the quotient generators of [Stacks, Tag 01R3] are carried to unit generators of the affine
model's shape, which is what the part (2) assembly needs of the locality step. Two moves on top
of `conormalRestrictIso_unit_app`: the comparison isomorphism of the factorization is commuted
past the restriction map by naturality, and then cancelled against its inverse inside
`conormalQuotientMap`. Nothing here is special to the coborder factorization, and no affineness,
Noetherian or finiteness hypothesis appears. -/
theorem conormalSheafRestrictIso_unit_app {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    (O : U.toScheme.Opens)
    (y : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op O)) :
    (conormalSheafRestrictIso i U i' hfac O).hom.val.app
        (.op ((i' ⁻¹ᵁ O).ι ⁻¹ᵁ (i' ⁻¹ᵁ O)))
        ((Stacks.Conormal.conormalSheaf i).val.map
          (homOfLE ((i' ⁻¹ᵁ O).ι.image_preimage_le (i' ⁻¹ᵁ O))).op
            ((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op O) y)) =
      ((Scheme.Modules.pullback (i' ∣_ O)).obj
          (Stacks.ClosedImmersion.idealSheaf (i' ∣_ O).toLRSHom.toShHom)).val.map
            (eqToHom (preimage_ι_preimage_eq i' O)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (i' ∣_ O)).unit.app
            (Stacks.ClosedImmersion.idealSheaf (i' ∣_ O).toLRSHom.toShHom)).val.app
              (.op (O.ι ⁻¹ᵁ O))
          ((Restriction.restrictIdealSheafIso' i' O).hom.val.app (.op (O.ι ⁻¹ᵁ O))
            ((Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.map
              (homOfLE (O.ι.image_preimage_le O)).op y))) := by
  refine Eq.trans (conormalSheafRestrictIso_val_app i U i' hfac O _ _) ?_
  refine Eq.trans ?_ (conormalRestrictIso_unit_app i' O y)
  refine congrArg ((conormalRestrictIso i' O).hom.val.app
    (.op ((i' ⁻¹ᵁ O).ι ⁻¹ᵁ (i' ⁻¹ᵁ O)))) ?_
  refine Eq.trans (congrArg (fun w =>
      (Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf i U i' hfac).hom.val.app
        (.op ((i' ⁻¹ᵁ O).ι ''ᵁ ((i' ⁻¹ᵁ O).ι ⁻¹ᵁ (i' ⁻¹ᵁ O))))
          ((Stacks.Conormal.conormalSheaf i).val.map
            (homOfLE ((i' ⁻¹ᵁ O).ι.image_preimage_le (i' ⁻¹ᵁ O))).op w))
      (conormalQuotientMap_val_app i U i' hfac O y)) ?_
  refine Eq.trans (congrArg
      ((Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf i U i' hfac).hom.val.app
        (.op ((i' ⁻¹ᵁ O).ι ''ᵁ ((i' ⁻¹ᵁ O).ι ⁻¹ᵁ (i' ⁻¹ᵁ O)))))
      (PresheafOfModules.naturality_apply
        (Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf i U i' hfac).inv.val
        (homOfLE ((i' ⁻¹ᵁ O).ι.image_preimage_le (i' ⁻¹ᵁ O))).op _).symm) ?_
  exact val_app_apply_congr
    (Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf i U i' hfac).inv_hom_id _ _

end Stacks.Conormal.Locality

end
