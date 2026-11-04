module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeComparison

/-!
# The stalk of the differential of the base change of a naive cotangent complex

Let `a : A ⟶ B` and `b : B ⟶ C` be morphisms of sheaves of commutative rings on a topological
space `T` and let `z` be a point of `T`.  `Stacks.SheafOfModules.baseChangeNaiveCotangentComplex`
is the complex `NL_{B/A} ⊗_B C` of sheaves of `C`-modules, and
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeMap` identifies its stalk at
`z` degreewise with the two terms of `NaiveCotangent.nlExtensionBaseChange` for the canonical
presentation `Algebra.Generators.self A_z B_z`.  This file completes that degreewise
identification to an identification of *complexes*: the stalk of the differential of
`NL_{B/A} ⊗_B C`, read through those two identifications, is the differential

`NaiveCotangent.nlExtensionBaseChange (Generators.self A_z B_z).toExtension C_z |>.d`,

namely the base change to `C_z` of `Algebra.Extension.cotangentComplex`.

Together with
`Stacks.NaiveCotangentStalkBaseChange.stalkLegNegOneLinear_baseChangeNaiveCotangentMap` and
`stalkLegZeroLinear_baseChangeNaiveCotangentMap`, which identify the stalk of the canonical map
of Stacks 0E1Y, this supplies the two "differential" hypotheses of
`CochainComplex.quasiIso_of_isZero_X_of_addEquiv` for the source of that map — the hypotheses
`hdK` of that criterion — the target's being
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegLinear_d`.

This is the half of the stalkwise comparison of Stacks 0FJZ which concerns the differentials.

## The proof

`(towerExtendScalarsComplexes J B C b).obj K` is the termwise extension of scalars, so its
differential is the extension of scalars of the differential of `K`.  Its stalk is therefore the
base change along the stalk of `b` of the stalk of the differential of `K`
(`Opens.stalkTowerExtendScalars_d_apply`), and on a pure tensor `c ⊗ ω` it is `c ⊗ dω`.  The
scalar factor is carried across by `Stacks.NaiveCotangentStalkBaseChange.fiberStalkRingEquiv` and
the module factor by the legs of Stacks 0D09, whose compatibility with the differential is
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegLinear_d`.  Both sides are additive, so `tmul_ext`
reduces the statement to pure tensors.

## Main results

* `Stacks.NaiveCotangentStalkBaseChange.stalkBaseChangeAddEquiv_d`: **the stalk of the
  differential of `NL_{B/A} ⊗_B C`.**
* `Stacks.NaiveCotangentStalkBaseChange.stalkBaseChangeAddEquiv_d_tmul`: the same on a pure
  tensor, which is where the computation happens.
* `Stacks.NaiveCotangentStalkBaseChange.stalkFunctor_map_towerExtendScalarsComplexes_d_inv_tmul`
  and `stalkTowerExtendScalarsXIso_hom_stalk_d_inv_tmul`: the stalk of the differential of the
  termwise extension of scalars on a pure tensor, in the two spellings the computation uses.

## Implementation notes

The computation is split across three lemmas, each stating one leg of the chain, because the
whole chain does not fit inside the default heartbeat budget: the terms involved are the stalks
of sheafifications, and each `Eq.trans` step costs a comparison of two of them.

As in `StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeComparison`, `rw`
cannot be used on these goals — the pure tensors of an extension of scalars of sheaves of
modules carry `ModuleCat.ExtendScalars`'s own `Module.compHom` instance, which `rw` rejects as
type-incorrect at `implicit` transparency — so the proofs are `Eq.trans`/`congrArg` chains, and
the scalar rings are supplied by `letI` in the order the ring-level comparison consumes them.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the base-change and
  relative maps of naive cotangent complexes of a tower of sheaves of rings.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 0FJZ](https://stacks.math.columbia.edu/tag/0FJZ), flat base change for the
  naive cotangent complex, whose stalkwise comparison this serves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules
open scoped ChangeOfRings

universe u

noncomputable section

namespace Stacks.NaiveCotangentStalkBaseChange

open Stacks.SheafOfModules Stacks.NaiveCotangentAffineStalkLegs
open Stacks.RelativeDifferentialStalk (algebraStalk)

section Differential

variable {T : TopCat.{u}}
  (A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C) (z : T)

/-- **The stalk of the differential of `NL_{B/A} ⊗_B C` on a pure tensor**, read through
`Opens.stalkTowerExtendScalarsXIso` in degree `0`: it carries the image under the inverse of that
identification of `c ⊗ ω` to `c ⊗ dω`, for `d` the stalk of the differential of `NL_{B/A}`. -/
theorem stalkTowerExtendScalarsXIso_hom_stalk_d_inv_tmul
    (c : ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) C.obj))
    (ω : ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z ⋙
        ModuleCat.restrictScalars.{u} (Opens.commRingFiberStalkHom z B).hom).obj
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X (-1)))) :
    (Opens.stalkTowerExtendScalarsXIso z B C b
          (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) 0).hom
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
            (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
                (Opens.grothendieckTopology T) B C b).obj
              (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).d
                (-1) 0)).hom
          ((Opens.stalkTowerExtendScalarsXIso z B C b
            (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) (-1)).inv
              (c ⊗ₜ[ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj),
                Stacks.SitePointBaseChange.stalkRingHom b.hom
                  (Opens.pointGrothendieckTopology z)] ω))) =
      c ⊗ₜ[ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj),
          Stacks.SitePointBaseChange.stalkRingHom b.hom
            (Opens.pointGrothendieckTopology z)]
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z ⋙
            ModuleCat.restrictScalars.{u} (Opens.commRingFiberStalkHom z B).hom).map
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).d
            (-1) 0)).hom ω) := by
  refine Eq.trans (Opens.stalkTowerExtendScalars_d_apply z B C b
    (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) (-1) 0 _) ?_
  exact congrArg _ (Iso.inv_hom_id_apply (Opens.stalkTowerExtendScalarsXIso z B C b
    (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) (-1)) _)


/-- `Stacks.NaiveCotangentStalkBaseChange.stalkTowerExtendScalarsXIso_hom_stalk_d_inv_tmul` with
the identification of the degree `0` term moved to the other side. -/
theorem stalkFunctor_map_towerExtendScalarsComplexes_d_inv_tmul
    (c : ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) C.obj))
    (ω : ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z ⋙
        ModuleCat.restrictScalars.{u} (Opens.commRingFiberStalkHom z B).hom).obj
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X (-1)))) :
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
            (Opens.grothendieckTopology T) B C b).obj
          (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).d
            (-1) 0)).hom
        ((Opens.stalkTowerExtendScalarsXIso z B C b
          (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) (-1)).inv
            (c ⊗ₜ[ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj),
              Stacks.SitePointBaseChange.stalkRingHom b.hom
                (Opens.pointGrothendieckTopology z)] ω)) =
      (Opens.stalkTowerExtendScalarsXIso z B C b
          (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) 0).inv
        (c ⊗ₜ[ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj),
            Stacks.SitePointBaseChange.stalkRingHom b.hom
              (Opens.pointGrothendieckTopology z)]
          (((AlgebraicGeometry.SheafOfModules.stalkFunctor
                (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z ⋙
              ModuleCat.restrictScalars.{u} (Opens.commRingFiberStalkHom z B).hom).map
            ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).d
              (-1) 0)).hom ω)) :=
  (Iso.hom_inv_id_apply (Opens.stalkTowerExtendScalarsXIso z B C b
      (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) 0) _).symm.trans
    (congrArg (fun y => (Opens.stalkTowerExtendScalarsXIso z B C b
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) 0).inv y)
      (stalkTowerExtendScalarsXIso_hom_stalk_d_inv_tmul A B C a b z c ω))


/-- **The stalk of the differential of `NL_{B/A} ⊗_B C` on a pure tensor `t ⊗ κ`**, read through
the two degreewise identifications: it is `t ⊗ (cotangent complex of the canonical presentation
of `B_z` over `A_z`) κ`, which is the value of the differential of
`NaiveCotangent.nlExtensionBaseChange` on `t ⊗ κ`. -/
theorem stalkBaseChangeAddEquiv_d_tmul
    (t : ToType (TopCat.Presheaf.stalk C.obj z))
    (κ : letI := algebraStalk a.hom z
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.Cotangent) :
    letI := algebraStalk a.hom z
    letI := algebraStalk b.hom z
    letI := moduleRingStalkCotangent A B a z
    stalkBaseChangeAddEquivZero A B C a b z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
              (Opens.grothendieckTopology T) B C b).obj
            (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).d
              (-1) 0)).hom
          ((stalkBaseChangeAddEquivNegOne A B C a b z).symm
            (t ⊗ₜ[ToType (TopCat.Presheaf.stalk B.obj z)] κ))) =
      (NaiveCotangent.nlExtensionBaseChange
          (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
            (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension
          (ToType (TopCat.Presheaf.stalk C.obj z))).d
        (t ⊗ₜ[ToType (TopCat.Presheaf.stalk B.obj z)] κ) := by
  let := algebraStalk a.hom z
  let := algebraStalk b.hom z
  let := moduleRingStalkCotangent A B a z
  let := moduleRingStalkCotangentSpace A B a z
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds z)) := Classical.decEq _
  refine Eq.trans (congrArg (fun ζ => stalkBaseChangeAddEquivZero A B C a b z
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
            (Opens.grothendieckTopology T) B C b).obj
          (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).d
            (-1) 0)).hom ζ))
    (stalkBaseChangeAddEquivNegOne_symm_tmul A B C a b z t κ)) ?_
  refine Eq.trans (congrArg (stalkBaseChangeAddEquivZero A B C a b z)
    (stalkFunctor_map_towerExtendScalarsComplexes_d_inv_tmul A B C a b z
      ((fiberStalkRingEquiv C z).symm t) ((stalkLegNegOneLinear A B a z).symm κ))) ?_
  refine Eq.trans (congrArg (fun y => stalkBaseChangeAddEquivZero A B C a b z
      ((Opens.stalkTowerExtendScalarsXIso z B C b
          (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) 0).inv
        ((fiberStalkRingEquiv C z).symm t
          ⊗ₜ[ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj),
            Stacks.SitePointBaseChange.stalkRingHom b.hom
              (Opens.pointGrothendieckTopology z)] y)))
    ((stalkLegZeroLinear A B a z).symm_apply_apply
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z ⋙
          ModuleCat.restrictScalars.{u} (Opens.commRingFiberStalkHom z B).hom).map
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).d
          (-1) 0)).hom ((stalkLegNegOneLinear A B a z).symm κ))).symm) ?_
  refine Eq.trans (congrArg (stalkBaseChangeAddEquivZero A B C a b z)
    (stalkBaseChangeAddEquivZero_symm_tmul A B C a b z t
      (stalkLegZeroLinear A B a z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z ⋙
            ModuleCat.restrictScalars.{u} (Opens.commRingFiberStalkHom z B).hom).map
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).d
            (-1) 0)).hom ((stalkLegNegOneLinear A B a z).symm κ)))).symm) ?_
  refine Eq.trans ((stalkBaseChangeAddEquivZero A B C a b z).apply_symm_apply _) ?_
  refine congrArg (fun (w : (Algebra.Generators.self
      (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.CotangentSpace) =>
      t ⊗ₜ[ToType (TopCat.Presheaf.stalk B.obj z)] w) ?_
  refine Eq.trans (stalkLegLinear_d A B a z ((stalkLegNegOneLinear A B a z).symm κ)) ?_
  exact congrArg (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
      (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.cotangentComplex
    ((stalkLegNegOneLinear A B a z).apply_symm_apply κ)

/-- **The stalk of the differential of `NL_{B/A} ⊗_B C`**, read through the two degreewise
identifications `stalkBaseChangeAddEquivNegOne` and `stalkBaseChangeAddEquivZero`, is the
differential of `NaiveCotangent.nlExtensionBaseChange` of the canonical presentation of `B_z` over
`A_z`, base changed to `C_z`. -/
theorem stalkBaseChangeAddEquiv_d
    (ξ : ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
          (Opens.grothendieckTopology T) B C b).obj
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).X (-1)))) :
    letI := algebraStalk a.hom z
    letI := algebraStalk b.hom z
    stalkBaseChangeAddEquivZero A B C a b z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
              (Opens.grothendieckTopology T) B C b).obj
            (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).d
              (-1) 0)).hom ξ) =
      (NaiveCotangent.nlExtensionBaseChange
          (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
            (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension
          (ToType (TopCat.Presheaf.stalk C.obj z))).d
        (stalkBaseChangeAddEquivNegOne A B C a b z ξ) := by
  let := algebraStalk a.hom z
  let := algebraStalk b.hom z
  let := moduleRingStalkCotangent A B a z
  refine Eq.trans ?_ (tmul_ext
    ((stalkBaseChangeAddEquivZero A B C a b z).toAddMonoidHom.comp
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
              (Opens.grothendieckTopology T) B C b).obj
            (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).d
              (-1) 0)).hom.toAddMonoidHom.comp
        (stalkBaseChangeAddEquivNegOne A B C a b z).symm.toAddMonoidHom))
    (NaiveCotangent.nlExtensionBaseChange
        (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
          (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension
        (ToType (TopCat.Presheaf.stalk C.obj z))).d.toAddMonoidHom
    (fun t κ => stalkBaseChangeAddEquiv_d_tmul A B C a b z t κ)
    (stalkBaseChangeAddEquivNegOne A B C a b z ξ))
  exact congrArg (fun ζ => stalkBaseChangeAddEquivZero A B C a b z
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
            (Opens.grothendieckTopology T) B C b).obj
          (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).d
            (-1) 0)).hom ζ))
    ((stalkBaseChangeAddEquivNegOne A B C a b z).symm_apply_apply ξ).symm

end Differential

end Stacks.NaiveCotangentStalkBaseChange

end

end
