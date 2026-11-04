module

public import StacksFrontier.AlgebraicGeometry.ModuleTwistIso.Basic
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.ShiftedTruncation
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.Multiplication

/-!
# The comparison `N → N'` of Tag 0B5R is a map of graded `S`-modules

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `M = ⨁_{n ∈ ℤ} 𝒨 n` a graded `S`-module
and `X = Proj 𝒮`. [Stacks, Tag 0B5R] compares the two graded `S`-modules

`N  = ⨁_n Γ(X, M̃(n))`   and   `N' = ⨁_n Γ(X, M(n)~)`

through the global sections of the canonical map `M̃ ⊗ 𝒪(n) ⟶ M(n)~` of [Stacks, Tag 01MQ],
assembled over the direct sum as
`Stacks.AlgebraicGeometry.ProjCoherentII.twistedToShiftedSections`. This file shows that this
map is `S`-linear for the twisted module structure of [Stacks, Tag 03GK] on `N` and the one of
[Stacks, Tag 01MR] on `N'`.

## Main results

* `Stacks.AlgebraicGeometry.ProjCoherentII.twistedToShiftedComponent_homogeneousScalar`: for a
  homogeneous `a` of degree `i`, the comparison in degree `i + n` applied to the twisted action
  of `a` is the shifted action of `a` on the comparison in degree `n`.
* `Stacks.AlgebraicGeometry.ProjCoherentII.twistedToShiftedSections_smul`: the assembled
  comparison is `S`-linear for the module structures
  `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsModule` and
  `Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap`.

## Implementation notes

The twisted action is `𝟙_{M̃} ⊗ σ_a` on sections over `⊤`, where `σ_a : 𝒪(n) ⟶ 𝒪(i + n)` is
multiplication by `a`; the shifted action is multiplication by `a` in every module fibre. A global
section of `M̃ ⊗ 𝒪(n)` is a section of a sheafified tensor product and need not be a sum of pure
tensors, so the identity is proved between morphisms of sheaves out of `M̃ ⊗ 𝒪(n)`, which are
determined by their values on pure tensors of local sections
(`Stacks.AlgebraicGeometry.ProjTwistTheta.tensorSheaf_hom_ext`). The shifted action is realised
as the morphism `M(n)~ ⟶ M(i + n)~` of associated sheaves induced by multiplication by `a`, via
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap`.

In the fibres both sides reduce to one identity in `LocalizedModule`: a fraction whose numerator
has been multiplied by `a` acts as `a` times the original fraction.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (associatedModuleSheaf twistingSheaf twistGrading twistedGlobalSections)
open Stacks.AlgebraicGeometry.ModuleTwistIso (moduleTwistMap_tmul)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap)
open Stacks.AlgebraicGeometry.ProjShifted (moduleTwistMap)
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (shiftedSectionsComponent globalSectionsModuleMap homogeneousScalarGlobalSections)
open Stacks.AlgebraicGeometry.ProjTwistedSections
  (twistedSectionsComponent homogeneousScalarTwistedSections twistScalarSheafMap
    twistedGlobalSectionsModule)
open Stacks.AlgebraicGeometry.ProjTwistTheta (tensorSheaf_hom_ext)
open Stacks.SheafOfModules.TensorStalkRingedSpace
  (toTensorSheafSection tensorSheafMap_app_toTensorSheafSection)
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization TensorProduct

namespace Stacks.AlgebraicGeometry.ProjCoherentII

universe u w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {S : Type u} {M : Type u} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-! ### Two identities in the module fibres -/

/-- Localizing multiplication by `a` on the module is the action of `a` on the localization. -/
private lemma localizedMap_eq_smul {P : Submonoid S} (a : S) (φ : M →ₗ[S] M)
    (hφ : ∀ m : M, φ m = a • m) (z : LocalizedModule P M) :
    LocalizedModule.map P φ z = a • z := by
  induction z using LocalizedModule.induction_on with
  | h m t => rw [LocalizedModule.map_mk, hφ, LocalizedModule.smul'_mk]

/-- Localizing multiplication by `a` on the ring and acting with the result is acting with `a`
after the original action. -/
private lemma localizedMap_mul_smul {P : Submonoid S} (a : S) (u : LocalizedModule P S)
    (v : LocalizedModule P M) :
    LocalizedModule.map P (LinearMap.mul S S a) u • v = a • (u • v) := by
  rw [localizedMap_eq_smul a _ (fun _ => rfl) u, smul_assoc]

/-! ### The degreewise comparison is equivariant -/

/-- The degreewise comparison of [Stacks, Tag 0B5R] (3) is equivariant for the homogeneous scalar
actions: for `a` homogeneous of degree `i`, applying the comparison in degree `i + n` to the
twisted action of `a` on a section gives the shifted action of `a` on the comparison in degree
`n` of that section. -/
public theorem twistedToShiftedComponent_homogeneousScalar (i : ℕ) (n : ℤ) (a : 𝒮 i)
    (s : twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) n) :
    twistedToShiftedComponent 𝒮 𝒨 ((i : ℤ) + n)
        (homogeneousScalarTwistedSections 𝒮 (associatedModuleSheaf 𝒮 𝒨) i n a s) =
      homogeneousScalarGlobalSections 𝒮 𝒨 i n a (twistedToShiftedComponent 𝒮 𝒨 n s) := by
  obtain ⟨φ, hφ, hmem⟩ :
      ∃ φ : M →ₗ[S] M, (∀ m : M, φ m = (a : S) • m) ∧
        ∀ (j : ℤ) (m : M), m ∈ shiftedGrading 𝒨 n j →
          φ m ∈ shiftedGrading 𝒨 ((i : ℤ) + n) j := by
    refine ⟨{ toFun := fun m => (a : S) • m
              map_add' := fun x y => smul_add (a : S) x y
              map_smul' := fun c m => smul_comm (a : S) c m }, fun _ => rfl, ?_⟩
    intro j m hm
    have h := SetLike.GradedSMul.smul_mem (A := 𝒮) (B := shiftedGrading 𝒨 n) a.2 hm
    change (a : S) • m ∈ 𝒨 (((i : ℤ) + j) + n) at h
    show (a : S) • m ∈ 𝒨 (j + ((i : ℤ) + n))
    rwa [show j + ((i : ℤ) + n) = ((i : ℤ) + j) + n from by omega]
  set ψ := associatedModuleSheafMap 𝒮 (shiftedGrading 𝒨 n)
    (shiftedGrading 𝒨 ((i : ℤ) + n)) φ hmem
  have happ : ∀ w : shiftedSectionsComponent 𝒮 𝒨 n,
      (ψ.val.app (op ⊤)).hom w = homogeneousScalarGlobalSections 𝒮 𝒨 i n a w := by
    intro w
    refine Subtype.ext (funext fun x => ?_)
    show LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl φ (w.1 x)
        = (a : S) • w.1 x
    exact localizedMap_eq_smul (a : S) φ hφ (w.1 x)
  have hsq :
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((AlgebraicGeometry.Proj 𝒮).toRingedSpace).presheaf,
                ((AlgebraicGeometry.Proj 𝒮).toRingedSpace).IsSheaf⟩)).map
            ((𝟙 (associatedModuleSheaf 𝒮 𝒨),
              twistScalarSheafMap 𝒮 i n ((i : ℤ) + n) rfl a) : (_, _) ⟶ (_, _)) ≫
          moduleTwistMap 𝒮 𝒨 ((i : ℤ) + n) =
        moduleTwistMap 𝒮 𝒨 n ≫ ψ := by
    refine tensorSheaf_hom_ext _ _ ?_
    intro U ς ϑ
    obtain ⟨W⟩ := U
    have h1 := tensorSheafMap_app_toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace
      (associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 n) (associatedModuleSheaf 𝒮 𝒨)
      (twistingSheaf 𝒮 ((i : ℤ) + n)) (𝟙 (associatedModuleSheaf 𝒮 𝒨))
      (twistScalarSheafMap 𝒮 i n ((i : ℤ) + n) rfl a) W ς ϑ
    have hgoal : ((moduleTwistMap 𝒮 𝒨 ((i : ℤ) + n)).val.app (op W)).hom
          (toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace
            (associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 ((i : ℤ) + n)) (op W)
            (ς ⊗ₜ[_] ((twistScalarSheafMap 𝒮 i n ((i : ℤ) + n) rfl a).val.app (op W)).hom ϑ))
        = (ψ.val.app (op W)).hom (((moduleTwistMap 𝒮 𝒨 n).val.app (op W)).hom
            (toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace
              (associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 n) (op W) (ς ⊗ₜ[_] ϑ))) := by
      refine Subtype.ext (funext fun x => ?_)
      have hLv := moduleTwistMap_tmul 𝒮 𝒨 ((i : ℤ) + n) W ς
        (((twistScalarSheafMap 𝒮 i n ((i : ℤ) + n) rfl a).val.app (op W)).hom ϑ) x
      have hRv := moduleTwistMap_tmul 𝒮 𝒨 n W ς ϑ x
      have hR : ((ψ.val.app (op W)).hom (((moduleTwistMap 𝒮 𝒨 n).val.app (op W)).hom
            (toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace
              (associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 n) (op W) (ς ⊗ₜ[_] ϑ)))).1 x
          = LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl φ (ϑ.1 x • ς.1 x) :=
        congrArg (LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl φ) hRv
      rw [hLv, hR]
      show LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl
            (LinearMap.mul S S (a : S)) (ϑ.1 x) • ς.1 x
          = LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl φ (ϑ.1 x • ς.1 x)
      rw [localizedMap_mul_smul, localizedMap_eq_smul (a : S) φ hφ]
    exact (congrArg
      (fun z => ((moduleTwistMap 𝒮 𝒨 ((i : ℤ) + n)).val.app (op W)).hom z) h1).trans hgoal
  exact (congrArg (fun m => ((SheafOfModules.Hom.val m).app (op ⊤)).hom s) hsq).trans
    (happ (((moduleTwistMap 𝒮 𝒨 n).val.app (op ⊤)).hom s))

/-! ### The assembled comparison is `S`-linear -/

/-- The comparison `⨁_n Γ(X, M̃(n)) → ⨁_n Γ(X, M(n)~)` of [Stacks, Tag 0B5R] (3) is `S`-linear,
for the graded module structure of [Stacks, Tag 03GK] on the source and that of
[Stacks, Tag 01MR] on the target. -/
public theorem twistedToShiftedSections_smul (c : S)
    (x : twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨)) :
    letI := (twistedGlobalSectionsModule 𝒮 (associatedModuleSheaf 𝒮 𝒨)).moduleInst
    letI := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
    twistedToShiftedSections 𝒮 𝒨 (c • x) = c • twistedToShiftedSections 𝒮 𝒨 x := by
  classical
  let := (twistedGlobalSectionsModule 𝒮 (associatedModuleSheaf 𝒮 𝒨)).moduleInst
  let := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
  have hof : ∀ (m : ℤ) (t : twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) m),
      twistedToShiftedSections 𝒮 𝒨
          (DirectSum.of (fun k : ℤ => twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) k)
            m t) =
        DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) m
          (twistedToShiftedComponent 𝒮 𝒨 m t) := by
    intro m t
    rw [twistedToShiftedSections, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
  have key : ∀ (p : ℕ) (b : 𝒮 p) (y : twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨)),
      twistedToShiftedSections 𝒮 𝒨 ((b : S) • y) =
        (b : S) • twistedToShiftedSections 𝒮 𝒨 y := by
    intro p b y
    induction y using DirectSum.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | of j t =>
        have h1 : twistedToShiftedSections 𝒮 𝒨 ((b : S) •
              (DirectSum.of
                (fun k : ℤ => twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) k) j t :
                  twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨))) =
            DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) ((p : ℤ) + j)
              (twistedToShiftedComponent 𝒮 𝒨 ((p : ℤ) + j)
                (homogeneousScalarTwistedSections 𝒮 (associatedModuleSheaf 𝒮 𝒨) p j b t)) :=
          (congrArg (twistedToShiftedSections 𝒮 𝒨)
            ((twistedGlobalSectionsModule 𝒮
              (associatedModuleSheaf 𝒮 𝒨)).smul_homogeneous p j b t)).trans (hof _ _)
        have h2 : (b : S) • twistedToShiftedSections 𝒮 𝒨
              (DirectSum.of
                (fun k : ℤ => twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) k) j t) =
            DirectSum.of (fun k : ℤ => shiftedSectionsComponent 𝒮 𝒨 k) ((p : ℤ) + j)
              (homogeneousScalarGlobalSections 𝒮 𝒨 p j b
                (twistedToShiftedComponent 𝒮 𝒨 j t)) :=
          (congrArg (fun z => (b : S) • z) (hof j t)).trans
            ((globalSectionsModuleMap 𝒮 𝒨).smul_of 𝒮 𝒨 p j b
              (twistedToShiftedComponent 𝒮 𝒨 j t))
        rw [h1, h2, twistedToShiftedComponent_homogeneousScalar]
    | add y z hy hz => rw [smul_add, map_add, map_add, smul_add, hy, hz]
  rw [← DirectSum.sum_support_decompose 𝒮 c, Finset.sum_smul, map_sum, Finset.sum_smul]
  exact Finset.sum_congr rfl fun p _ => key p _ x

end Stacks.AlgebraicGeometry.ProjCoherentII

end
