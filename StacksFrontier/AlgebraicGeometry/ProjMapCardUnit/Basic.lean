module

public import StacksFrontier.AlgebraicGeometry.ProjMapCard.Multiplication
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Unit
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Normalization
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Restriction

/-!
# Tag 01MY: the comparison maps on twists preserve the unit of the graded algebra

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings, `U(ψ) ⊆ Proj ℬ` its domain
of definition, `r_ψ : U(ψ) ⟶ Proj 𝒜` the induced morphism and `θ n` the comparison map on the
`n`-th twist. The twists of `Proj 𝒜` carry a unit `𝒪 ⟶ 𝒪(0)` making `⨁_n 𝒪(n)` a graded
algebra, and Tag 01MY asserts that the family `θ` is a map of graded algebras. This file proves
the unit clause, in the shape of the Stacks statement:

`𝒪_{U(ψ)} ⟶ r_ψ^* 𝒪(0) ⟶ ι^* 𝒪(0)` equals `𝒪_{U(ψ)} ⟶ ι^* 𝒪(0)`,

where both pulled-back units are formed with Mathlib's comparison
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit`, which is invertible because the
inverse-image functor on opens is final.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjMapCardUnit.pullbackTwistUnit`: Tag 01MY's
  `pullbackTwistUnit`, the unit of the twisting algebra after pullback along an arbitrary
  morphism into `Proj 𝒜`.

## Main results

* `Stacks.AlgebraicGeometry.ProjMapCardUnit.twistMap_comp_pullbackTwistUnit`: the clause for
  the morphism and the comparison maps separately.
* `Stacks.AlgebraicGeometry.ProjMapCardUnit.projMapData_preserves_unit`: **Tag 01MY, the
  graded-algebra unit**, written on the canonical bundle
  `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`, which is the spelling of the Stacks
  statement.
* `restrictFunctorIsoPullback_hom_comp_pullbackObjUnitToUnit`, in this namespace: for an open
  immersion, Mathlib's comparison `j^* 𝒪_V ⟶ 𝒪_U` agrees with
  `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` across
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.
* `Stacks.AlgebraicGeometry.ProjMapCardUnit.unitHomEquiv_symm_eq_twistUnitMap`: Tag 01MY's own
  construction of the unit is `Stacks.AlgebraicGeometry.ProjTwistCompare.twistUnitMap`.

## The route

Both sides of the clause are morphisms out of the structure sheaf of `U(ψ)` written through the
inverse of a comparison isomorphism, so the first move is to cancel the comparison of `r_ψ` and
work with morphisms out of `r_ψ^* 𝒪_{Proj 𝒜}`. There the adjoint transpose is injective, and
transposing turns the left-hand side into

`𝒪_{Proj 𝒜} ⟶ 𝒪(0) ⟶ (r_ψ)_*(ι^* 𝒪(0))`,

which is the unit followed by the adjoint form of `θ 0` — exactly
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap_twistUnitMap`, the unit law in
the shape in which both sides are concrete families of homogeneous fractions. The right-hand
side transposes to the structure-sheaf map of `r_ψ` followed by the same morphism, by Mathlib's
description of the transpose of `pullbackObjUnitToUnit`. So the clause reduces to one statement
about the open immersion `ι` alone, with no twists in it: the pulled-back unit of `ℬ`'s twisting
algebra is the restricted unit, read across `restrictFunctorIsoPullback`.

## The identification that was recorded as absent, and is not

`StacksDraft.AlgebraicGeometry.F3.ProjTwistCompare.Unit` named the single missing input for
this clause as: for an open immersion `ι`, the comparison `ι^* 𝒪_Y ⟶ 𝒪_X` of the
pullback-pushforward adjunction agrees with
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso` through `restrictFunctorIsoPullback`; and
recorded it as absent from Mathlib and belonging upstream. The claim about *Mathlib* holds --
the only references to either isomorphism outside their defining files are three in
`Mathlib/AlgebraicGeometry/Modules/Tilde.lean` -- but the statement is a two-line consequence
of what this repository already has. `Stacks.Conormal` has it for
`pullbackUnitModuleIso`, as `restrictFunctorIsoPullback_hom_comp_pullbackUnitModuleIso`
(`StacksFrontier/AlgebraicGeometry/ConormalComparison/Normalization.lean`), namely for
`Stacks.IdealSheafRestrict.pullbackUnitModuleIso`, and
`Stacks.Conormal.unit_comp_map_pullbackUnitModuleIso` (`:218`) computes that isomorphism's
adjoint transpose as the structure-sheaf map -- which is exactly Mathlib's description of the
transpose of `pullbackObjUnitToUnit`. Since the transposition is a bijection, the two
isomorphisms are equal (`pullbackUnitModuleIso_hom_eq` below), and the recorded gap closes with
no new mathematics. Nothing in this file is upstream work.

## Faithfulness of the unit

Tag 01MY's `twistUnitMap` is built as `unitHomEquiv.symm` of the global section of `𝒪(0)`
attached to `1`, restricted to each open, and raises `maxHeartbeats` twentyfold to elaborate
that; `Stacks.AlgebraicGeometry.ProjTwistCompare.twistUnitMap` is built instead through
`CategoryTheory.PresheafOfModules.homMk` and needs no option. The two are the same morphism,
and `unitHomEquiv_symm_eq_twistUnitMap` proves it without re-elaborating the expensive route:
for *any* section whose value over every open is Tag 01MY's, `unitHomEquiv.symm` of it is the
library morphism. The computation behind that is `twistUnitMap_app_one`, where both sides are
the constant family `1/1`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` and the twisting sheaf's index category is
`Opens ↑(ProjectiveSpectrum.top 𝒮)` rather than `Opens ↑(Proj 𝒮)`, so several goals here are
not type-correct at the elaborator's `implicit` transparency and a `rw` fails its motive check
even where both sides print identically: `rw [Iso.eq_inv_comp]` fails on the very goal that
`(Iso.eq_inv_comp _).mpr` closes. Every assembly below is therefore a chain of `Eq.trans` and
`congrArg` in term mode, and the two cancellations of an isomorphism are the `Iso` lemmas used
as terms rather than as rewrites.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.IdealSheafRestrict
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.Conormal.Restriction

namespace Stacks.AlgebraicGeometry.ProjMapCardUnit

universe u

variable {U V : Scheme.{u}}

/-- Mathlib's comparison `j^* 𝒪_V ⟶ 𝒪_U` is this repository's `pullbackUnitModuleIso`: both
transpose to the structure-sheaf map of `j`, and the transposition is a bijection. -/
theorem pullbackUnitModuleIso_hom_eq (j : U ⟶ V) [IsOpenImmersion j] :
    (pullbackUnitModuleIso j).hom =
      SheafOfModules.pullbackObjUnitToUnit (structureSheafHom j.toLRSHom.toShHom) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).eq_symm_apply).mpr
    ((Adjunction.homEquiv_unit _ _ _ _).trans
      (Stacks.Conormal.unit_comp_map_pullbackUnitModuleIso j))

/-- The identification of the pullback of the structure sheaf along an open immersion with the
structure sheaf agrees with the restriction one, across `restrictFunctorIsoPullback`. -/
theorem restrictFunctorIsoPullback_hom_comp_pullbackObjUnitToUnit (j : U ⟶ V)
    [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctorIsoPullback j).hom.app (unitModule V) ≫
        SheafOfModules.pullbackObjUnitToUnit (structureSheafHom j.toLRSHom.toShHom) =
      (restrictUnitModuleIso j).hom :=
  (congrArg (fun k => (Scheme.Modules.restrictFunctorIsoPullback j).hom.app (unitModule V) ≫ k)
    (pullbackUnitModuleIso_hom_eq j)).symm.trans
      (Stacks.Conormal.restrictFunctorIsoPullback_hom_comp_pullbackUnitModuleIso j)

/-- The two spellings of the structure-sheaf map agree. -/
theorem structureMap_eq (f : U ⟶ V) :
    structureMap f = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  rfl

/-- The adjoint transpose of the comparison `f^* 𝒪_Y ⟶ 𝒪_X` is the structure-sheaf map. -/
theorem homEquiv_pullbackObjUnitToUnit (f : U ⟶ V) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f.toLRSHom.toShHom)) =
      structureMap f :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (structureSheafHom f.toLRSHom.toShHom)

section Proj

universe w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The inverse-image functor on opens of a morphism of schemes is final. -/
local instance final_opensMap_of_scheme {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (opensMap f.toLRSHom.toShHom).Final :=
  CategoryTheory.final_of_representablyFlat _

/-- The unit of the twisting algebra after pullback along an arbitrary morphism. -/
noncomputable def pullbackTwistUnit {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Proj 𝒜) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pullback f).obj (twistingSheaf 𝒜 0) :=
  (asIso (SheafOfModules.pullbackObjUnitToUnit
      (structureSheafHom f.toLRSHom.toShHom))).inv ≫
    (Scheme.Modules.pullback f).map (twistUnitMap 𝒜)

/-- The defining formula for `pullbackTwistUnit`. -/
theorem pullbackTwistUnit_def {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Proj 𝒜) :
    pullbackTwistUnit 𝒜 f =
      (asIso (SheafOfModules.pullbackObjUnitToUnit
          (structureSheafHom f.toLRSHom.toShHom))).inv ≫
        (Scheme.Modules.pullback f).map (twistUnitMap 𝒜) :=
  rfl

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The restriction of the unit of the twisting algebra of `ℬ` is the unit on `U(ψ)`. -/
theorem restrictUnitModuleIso_comp_restrictTwistUnit (ψ : 𝒜 →+*ᵍ ℬ) :
    (restrictUnitModuleIso (mapDomain 𝒜 ℬ ψ).ι).hom ≫ restrictTwistUnit 𝒜 ℬ ψ =
      (Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).map (twistUnitMap ℬ) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine Eq.trans (congrArg (unitSection ℬ ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ V.unop))
      (restrictUnitModuleIso_ι_hom_app (mapDomain 𝒜 ℬ ψ) V.unop x)) ?_
  exact (ProjMapCard.restrictFunctor_map_app_apply (mapDomain 𝒜 ℬ ψ).ι
    (twistUnitMap ℬ) V.unop x).symm

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The pulled-back unit of `ℬ`'s twisting algebra along the inclusion of `U(ψ)` is the
restricted unit, read across the identification of restriction with pullback. -/
theorem restrictTwistUnit_comp_restrictFunctorIsoPullback (ψ : 𝒜 →+*ᵍ ℬ) :
    restrictTwistUnit 𝒜 ℬ ψ ≫
        (Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
          (twistingSheaf ℬ 0) =
      pullbackTwistUnit ℬ (mapDomain 𝒜 ℬ ψ).ι := by
  have hA : (Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
        (unitModule (AlgebraicGeometry.Proj ℬ)) ≫
      (SheafOfModules.pullbackObjUnitToUnit
          (structureSheafHom (mapDomain 𝒜 ℬ ψ).ι.toLRSHom.toShHom) ≫
        (restrictTwistUnit 𝒜 ℬ ψ ≫
          (Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
            (twistingSheaf ℬ 0))) =
      (Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
          (unitModule (AlgebraicGeometry.Proj ℬ)) ≫
        (Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).map (twistUnitMap ℬ) :=
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (restrictTwistUnit 𝒜 ℬ ψ ≫
            (Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
              (twistingSheaf ℬ 0)))
          (restrictFunctorIsoPullback_hom_comp_pullbackObjUnitToUnit
            (mapDomain 𝒜 ℬ ψ).ι)).trans
        (((Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫
                (Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
                  (twistingSheaf ℬ 0))
              (restrictUnitModuleIso_comp_restrictTwistUnit 𝒜 ℬ ψ))).trans
          ((Scheme.Modules.restrictFunctorIsoPullback
            (mapDomain 𝒜 ℬ ψ).ι).hom.naturality (twistUnitMap ℬ)))))
  exact (Iso.eq_inv_comp (asIso (SheafOfModules.pullbackObjUnitToUnit
      (structureSheafHom (mapDomain 𝒜 ℬ ψ).ι.toLRSHom.toShHom)))).mpr
    ((Iso.cancel_iso_hom_left
      ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).app
        (unitModule (AlgebraicGeometry.Proj ℬ))) _ _).mp hA)

section Card

variable {S : Type u} {ρ : Type w} [CommRing S] [SetLike ρ S] [AddSubgroupClass ρ S]
  (𝒮 : ℕ → ρ) [GradedRing 𝒮]

/-- The global section of the degree-zero twist attached to `1`, restricted to `U`, is the
value of the unit on `1`. -/
theorem twistUnitMap_app_one (U : (Opens ↑(AlgebraicGeometry.Proj 𝒮))ᵒᵖ) :
    ((twistUnitMap 𝒮).val.app U).hom'
        (1 : (AlgebraicGeometry.Proj 𝒮).ringCatSheaf.obj.obj U) =
      (twistingSheaf 𝒮 0).val.map (homOfLE (le_top (a := U.unop))).op
        (degreeSection 𝒮 0
          ⟨1, SetLike.one_mem_graded 𝒮⟩) := by
  refine Subtype.ext (funext fun x => ?_)
  refine Eq.trans (twistUnitMap_app_val 𝒮 U
    (1 : (AlgebraicGeometry.Proj 𝒮).ringCatSheaf.obj.obj U) x) ?_
  refine Eq.trans ?_ (degreeSection_apply 𝒮 0
    ⟨1, SetLike.one_mem_graded 𝒮⟩ ⟨x.1, trivial⟩).symm
  refine Eq.trans HomogeneousLocalization.val_one ?_
  exact OreLocalization.one_def

/-- **Tag 01MY's construction of the unit is the library one.** Tag 01MY builds the unit as
`unitHomEquiv.symm` of the global section of the degree-zero twist attached to `1`, restricted
to each open; any section with those values gives `twistUnitMap`. -/
theorem unitHomEquiv_symm_eq_twistUnitMap (t : (twistingSheaf 𝒮 0).sections)
    (ht : ∀ U : (Opens ↑(AlgebraicGeometry.Proj 𝒮))ᵒᵖ, t.val U =
      (twistingSheaf 𝒮 0).val.map (homOfLE (le_top (a := U.unop))).op
        (degreeSection 𝒮 0
          ⟨1, SetLike.one_mem_graded 𝒮⟩)) :
    (twistingSheaf 𝒮 0).unitHomEquiv.symm t = twistUnitMap 𝒮 :=
  (twistingSheaf 𝒮 0).unitHomEquiv.symm_apply_eq.mpr
    (PresheafOfModules.sections_ext _ _ fun U =>
      (ht U).trans (twistUnitMap_app_one 𝒮 U).symm)

end Card

/-- **Tag 01MY, the graded-algebra unit.** The comparison map `θ 0` on the degree-zero twist
carries the unit of `𝒜`'s twisting algebra, pulled back along `r_ψ`, to the unit of `ℬ`'s,
pulled back along the inclusion of the domain of definition. -/
theorem twistMap_comp_pullbackTwistUnit (ψ : 𝒜 →+*ᵍ ℬ) :
    pullbackTwistUnit 𝒜 (mapHom 𝒜 ℬ ψ) ≫ twistMap 𝒜 ℬ ψ 0 =
      pullbackTwistUnit ℬ (mapDomain 𝒜 ℬ ψ).ι := by
  have key : (Scheme.Modules.pullback (mapHom 𝒜 ℬ ψ)).map (twistUnitMap 𝒜) ≫
        twistMap 𝒜 ℬ ψ 0 =
      SheafOfModules.pullbackObjUnitToUnit
          (structureSheafHom (mapHom 𝒜 ℬ ψ).toLRSHom.toShHom) ≫
        (restrictTwistUnit 𝒜 ℬ ψ ≫
          (Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
            (twistingSheaf ℬ 0)) := by
    refine ((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv
      _ _).injective ?_
    refine Eq.trans (Adjunction.homEquiv_naturality_left _ (twistUnitMap 𝒜)
      (twistMap 𝒜 ℬ ψ 0)) ?_
    refine Eq.trans (congrArg (fun k => twistUnitMap 𝒜 ≫ k)
      (((Adjunction.homEquiv_naturality_right
            (Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ))
            (((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv _ _).symm
              (twistPushforwardMap 𝒜 ℬ ψ 0))
            ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
              (twistingSheaf ℬ 0))).trans
          (congrArg (fun k => k ≫ (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map
              ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
                (twistingSheaf ℬ 0)))
            (Equiv.apply_symm_apply _ (twistPushforwardMap 𝒜 ℬ ψ 0)))))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫ (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map
        ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
          (twistingSheaf ℬ 0)))
      (twistPushforwardMap_twistUnitMap 𝒜 ℬ ψ)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k => SheafOfModules.unitToPushforwardObjUnit
        (mapHom 𝒜 ℬ ψ).toRingCatSheafHom ≫ k)
      (Functor.map_comp (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ))
        (restrictTwistUnit 𝒜 ℬ ψ)
        ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
          (twistingSheaf ℬ 0))).symm) ?_
    refine Eq.trans (congrArg (fun k => k ≫ (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map
        (restrictTwistUnit 𝒜 ℬ ψ ≫
          (Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
            (twistingSheaf ℬ 0)))
      ((structureMap_eq (mapHom 𝒜 ℬ ψ)).symm.trans
        (homEquiv_pullbackObjUnitToUnit (mapHom 𝒜 ℬ ψ)).symm)) ?_
    exact (Adjunction.homEquiv_naturality_right _ _ _).symm
  exact (Iso.inv_comp_eq (asIso (SheafOfModules.pullbackObjUnitToUnit
      (structureSheafHom (mapHom 𝒜 ℬ ψ).toLRSHom.toShHom)))).mpr
    (key.trans (congrArg (fun k => SheafOfModules.pullbackObjUnitToUnit
        (structureSheafHom (mapHom 𝒜 ℬ ψ).toLRSHom.toShHom) ≫ k)
      (restrictTwistUnit_comp_restrictFunctorIsoPullback 𝒜 ℬ ψ)))

/-- **Tag 01MY, the graded-algebra unit, on the canonical bundle.** The Stacks statement's
spelling of `twistMap_comp_pullbackTwistUnit`: the morphism and the twist maps are the fields of
`Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`. -/
@[stacks 01MY "graded-algebra unit"]
theorem projMapData_preserves_unit (ψ : 𝒜 →+*ᵍ ℬ) :
    pullbackTwistUnit 𝒜 (projMapData 𝒜 ℬ ψ).hom ≫ (projMapData 𝒜 ℬ ψ).twistMap 0 =
      pullbackTwistUnit ℬ (mapDomain 𝒜 ℬ ψ).ι :=
  twistMap_comp_pullbackTwistUnit 𝒜 ℬ ψ

end Proj

section Faithfulness

universe w w'

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- **Faithfulness.** The graded-algebra unit assertion of Tag 01MY in the reference
statement's own text and binder order, with its vocabulary folded to this library's: the domain
of the induced morphism to `Stacks.AlgebraicGeometry.ProjShared.mapDomain`, the twisting sheaf
(Tag 01MN) to `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf`, the induced morphism
datum to `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData` and the pulled-back unit to
`pullbackTwistUnit`. No hypothesis is added, dropped or reordered, and no quantifier is
changed. -/
example {A B : Type u} {σ : Type w} {τ : Type w'}
    [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) :
    pullbackTwistUnit 𝒜 (projMapData 𝒜 ℬ ψ).hom ≫
      (projMapData 𝒜 ℬ ψ).twistMap 0 =
    pullbackTwistUnit ℬ (mapDomain 𝒜 ℬ ψ).ι :=
  projMapData_preserves_unit 𝒜 ℬ ψ

end Faithfulness

end Stacks.AlgebraicGeometry.ProjMapCardUnit

end
