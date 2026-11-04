module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestrictionCocycle
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationCocycleDegreeZero

/-!
# Restriction along an inclusion of opens: the nested-opens cocycle in every degree

[Stacks, Tag 01E5] asserts an equality of sheaves, so the comparisons it attaches to a nested
pair of opens `W ≤ V` must agree. For a morphism of schemes `f : X ⟶ Y` this file proves that
cocycle identity for the comparison isomorphisms of the higher direct images `R^p f_*` in every
degree `p : ℕ`, zero included, both for the `ℕ`-indexed derived functors and for the `ℤ`-indexed
ones. In degree zero the comparison is the normalised one
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIsoZero`, and the statements here
are transports of the ringed-space cocycle
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso_ofLE_anyDegree`. A consumer
whose degree is the dimension `d` of a situation, which may be zero, so has the cocycle without a
case split; conclusion (b) of [Stacks, Tag 0EX3] is such a consumer.

## Main definitions

* `restrictIsoOfLEAnyDegree`: the middle comparison across `W ≤ V` in every degree, the transport
  of `Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIsoOfLE` to schemes. It
  differs from `Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.higherDirectImageRestrictIsoOfLE`
  precisely in degree zero, where the latter transports the positive-degree comparison and
  satisfies no cocycle.
* `rightDerivedPlusRestrictIsoOfLEAnyDegree`: the same comparison for the `ℤ`-indexed derived
  functors.

## Main results

* `higherDirectImageRestrictIso_ofLE_anyDegree_app`: the ringed-space cocycle in every degree,
  read at a module.
* `restrictIso_ofLE_anyDegree`: **[Stacks, Tag 01E5]**, compatibility of the comparisons across a
  nested pair of opens, in every degree, for schemes.
* `restrictIso_ofLE_anyDegree_app`: its component at a module.
* `rightDerivedPlusRestrictObjIso_ofLE_anyDegree`: the same compatibility for the objectwise
  `ℤ`-indexed comparison
  `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso`.

## Implementation notes

The comparisons cross between the `AlgebraicGeometry.Scheme.Modules` and the `SheafOfModules`
spelling of the same category, and a composite whose factors were elaborated in different
spellings is rejected by the kernel. Every crossing here is a
`Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.transportIso`, in which the ringed-space
morphism enters only as an argument.

Every scheme-level ingredient of the positive-degree proof (the functor equalities, the reading of
each comparison as a `transportIso` of its ringed-space counterpart, and the composition law
`Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.comp_eq_comp_of_transport`) holds in an
arbitrary degree, so the proofs here are the positive-degree ones with the degree left general and
the degree-uniform ringed-space cocycle in place of the positive-degree one.

## References

* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage

universe u

namespace Stacks.AlgebraicGeometry.SchemeRestrictionDegreeZero

attribute [local instance] HasDerivedCategory.standard

open SchemeHigherDirectImage (higherDirectImageRestrictIso_source
  higherDirectImageRestrictIso_target)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {W V : Y.Opens} (h : W ≤ V) (p : ℕ)

/-- **The middle comparison across a nested pair of opens, for schemes, in every degree.**
Restricting the comparison for `V` along `W ≤ V` lands on the source of the comparison for `W`.
It is the ringed-space `Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIsoOfLE`
transported along
`Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.higherDirectImageRestrictIsoOfLE_source` and
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso_source`.

In positive degree this is
`Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.higherDirectImageRestrictIsoOfLE`; in degree
zero it is the normalised comparison instead, which is what makes the cocycle below hold
there. -/
noncomputable def restrictIsoOfLEAnyDegree :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
          (Scheme.Modules.pushforward (f ∣_ V)).rightDerived p) ⋙
        Scheme.Modules.restrictFunctor (Y.homOfLE h) ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W).ι ⋙
        (Scheme.Modules.pushforward (f ∣_ W)).rightDerived p :=
  SchemeRestrictionCocycle.transportIso
    (SchemeRestrictionCocycle.higherDirectImageRestrictIsoOfLE_source f h p)
    (higherDirectImageRestrictIso_source f W p).symm
    (higherDirectImageRestrictIsoOfLE f.toLRSHom.toShHom h p)

/-- The scheme-level degree-uniform middle comparison *is* the
`Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.transportIso` of the ringed-space one, by
construction. -/
theorem restrictIsoOfLEAnyDegree_eq_transport :
    restrictIsoOfLEAnyDegree f h p =
      SchemeRestrictionCocycle.transportIso
        (SchemeRestrictionCocycle.higherDirectImageRestrictIsoOfLE_source f h p)
        (higherDirectImageRestrictIso_source f W p).symm
        (higherDirectImageRestrictIsoOfLE f.toLRSHom.toShHom h p) :=
  rfl

/-- **The ringed-space cocycle of [Stacks, Tag 01E5] in every degree, read at a module.**  The
component at `F` of
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso_ofLE_anyDegree`, with the module
written in the scheme spelling. -/
theorem higherDirectImageRestrictIso_ofLE_anyDegree_app (F : X.Modules) :
    (moduleRestrictionOfLE Y.toRingedSpace h).map
          ((higherDirectImageRestrictIso f.toLRSHom.toShHom V p).hom.app F) ≫
        (moduleRestrictionOfLEIso Y.toRingedSpace h).hom.app
          (((modulePushforward f.toLRSHom.toShHom).rightDerived p).obj F) =
      (higherDirectImageRestrictIsoOfLE f.toLRSHom.toShHom h p).hom.app F ≫
        (higherDirectImageRestrictIso f.toLRSHom.toShHom W p).hom.app F :=
  congrArg (fun t => NatTrans.app t F)
    (higherDirectImageRestrictIso_ofLE_anyDegree f.toLRSHom.toShHom h p)

/-- **[Stacks, Tag 01E5], compatibility across a nested pair of opens, for schemes, in every
degree.**  The comparison attached to `V`, restricted along `W ≤ V` and followed by the
transitivity isomorphism `Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso`, agrees with the
middle comparison `restrictIsoOfLEAnyDegree` followed by the comparison attached to `W`.

This is the degree-uniform ringed-space cocycle
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso_ofLE_anyDegree` read in the
scheme vocabulary. -/
theorem restrictIso_ofLE_anyDegree :
    Functor.whiskerRight (SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom
          (Scheme.Modules.restrictFunctor (Y.homOfLE h)) ≫
        Functor.whiskerLeft ((Scheme.Modules.pushforward f).rightDerived p)
          (Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso h).hom =
      (restrictIsoOfLEAnyDegree f h p).hom ≫
        (SchemeHigherDirectImage.higherDirectImageRestrictIso f W p).hom := by
  have eA := SchemeRestrictionCocycle.higherDirectImageRestrictIsoOfLE_source f h p
  have eB := SchemeRestrictionCocycle.higherDirectImageRestrictIso_target_ofLE f h p
  have eC := higherDirectImageRestrictIso_source f W p
  have eD := higherDirectImageRestrictIso_target f W p
  rw [SchemeRestrictionCocycle.higherDirectImageRestrictIso_eq_transport f V p,
    SchemeRestrictionCocycle.higherDirectImageRestrictIso_eq_transport f W p,
    restrictIsoOfLEAnyDegree_eq_transport f h p,
    SchemeRestrictionCocycle.restrictLEIso_eq_transport Y h]
  exact SchemeRestrictionCocycle.comp_eq_comp_of_transport eA eB eC eD
    (SchemeRestrictionCocycle.whiskerRight_transportIso_hom _ _ _
      (SchemeRestrictionCocycle.restrictFunctor_homOfLE_eq Y h) eA eB.symm)
    (SchemeRestrictionCocycle.whiskerLeft_transportIso_hom rfl _ _ _ eB eD.symm)
    (SchemeRestrictionCocycle.transportIso_hom _ _ _)
    (SchemeRestrictionCocycle.transportIso_hom _ _ _)
    (higherDirectImageRestrictIso_ofLE_anyDegree f.toLRSHom.toShHom h p)

/-- **The nested-opens cocycle at a module, in every degree.**  The component at `F` of
`restrictIso_ofLE_anyDegree`. -/
theorem restrictIso_ofLE_anyDegree_app (F : X.Modules) :
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).map
          ((SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom.app F) ≫
        (Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso h).hom.app
          (((Scheme.Modules.pushforward f).rightDerived p).obj F) =
      (restrictIsoOfLEAnyDegree f h p).hom.app F ≫
        (SchemeHigherDirectImage.higherDirectImageRestrictIso f W p).hom.app F := by
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    using NatTrans.congr_app (restrictIso_ofLE_anyDegree f h p) F

/-- **The middle comparison across a nested pair of opens, for the `ℤ`-indexed derived functors,
in every degree.**  `restrictIsoOfLEAnyDegree` conjugated by
`Stacks.DerivedIndexing.rightDerivedIso` on either side. -/
noncomputable def rightDerivedPlusRestrictIsoOfLEAnyDegree :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
          (Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)) ⋙
        Scheme.Modules.restrictFunctor (Y.homOfLE h) ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W).ι ⋙
        (Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (p : ℤ) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι)
        (Stacks.DerivedIndexing.rightDerivedIso
          (Scheme.Modules.pushforward (f ∣_ V)) p).symm)
      (Scheme.Modules.restrictFunctor (Y.homOfLE h)) ≪≫
    restrictIsoOfLEAnyDegree f h p ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W).ι)
      (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward (f ∣_ W)) p)

/-- **[Stacks, Tag 01E5], compatibility across a nested pair of opens, for the `ℤ`-indexed
comparison, in every degree.**  The objectwise `ℤ`-indexed comparison
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` attached to
`V`, restricted along `W ≤ V` and followed by the transitivity isomorphism, agrees with
`rightDerivedPlusRestrictIsoOfLEAnyDegree` followed by the comparison attached to `W`.

Both comparisons are the `ℕ`-indexed ones conjugated by `Stacks.DerivedIndexing.rightDerivedIso`,
so the two inner conjugations cancel and the naturality of the transitivity isomorphism moves the
outer one across the restriction; what remains is `restrictIso_ofLE_anyDegree_app`. -/
theorem rightDerivedPlusRestrictObjIso_ofLE_anyDegree (F : X.Modules) :
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).map
          (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f V p F).hom ≫
        (Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso h).hom.app
          (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F) =
      (rightDerivedPlusRestrictIsoOfLEAnyDegree f h p).hom.app F ≫
        (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f W p F).hom := by
  have key := restrictIso_ofLE_anyDegree_app f h p F
  have hnat := (Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso h).hom.naturality
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) p).hom.app F)
  rw [SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso_eq_app,
    SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso_eq_app]
  dsimp only [SchemeHigherDirectImage.rightDerivedPlusRestrictIso,
    rightDerivedPlusRestrictIsoOfLEAnyDegree,
    Iso.app_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map] at *
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hnat]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [SchemeHigherDirectImage.higherDirectImageRestrictIso_eq_eqToIso_trans] at key ⊢
  rw [reassoc_of% key]

end Stacks.AlgebraicGeometry.SchemeRestrictionDegreeZero

end
