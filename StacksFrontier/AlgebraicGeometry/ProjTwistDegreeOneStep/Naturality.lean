module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleGraded
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Functoriality
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Tensor
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.Multiplication
public import StacksFrontier.AlgebraicGeometry.TwistTensor.Basic

/-!
# Multiplication of twists carries the scalar action to multiplication of sections

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring and `X = Proj 𝒮`. For integers `e`, `d` the canonical
multiplication map `𝒪(e) ⊗ 𝒪(d) ⟶ 𝒪(e + d)` of [Stacks, Tag 01MO] is **natural in the second
factor**, for the maps given by multiplication by a homogeneous scalar: for `a ∈ 𝒮 i` and
`i + d = k` the square

```
𝒪(e) ⊗ 𝒪(d)  --(1 ⊗ a)-->  𝒪(e) ⊗ 𝒪(k)
     |                           |
  mult_{e,d}                  mult_{e,k}
     v                           v
  𝒪(e + d)   ----(a)---->     𝒪(e + k)
```

commutes, where the horizontal maps are
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafScalarMap` on the left and
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap` on the right.

This is the compatibility that lets the comparison `𝒪(e)(d) ≅ 𝒪(e + d)` of
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin` carry the
graded `S`-module structure of [Stacks, Tag 03GK] on `⨁_d Γ(X, 𝒪(e)(d))` to multiplication of
sections of the twisting sheaves — the step that
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/TwistSectionsFiniteness.lean` records
as missing.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.mul_comp_twistMultiplicationMap`: the square
  above.

## Implementation notes

Both composites are morphisms out of the sheafified tensor product, so they are equal as soon as
they agree on the image of every pure tensor of honest sections
(`Stacks.AlgebraicGeometry.ProjTwistTheta.tensorSheaf_hom_ext`). On such a section both sides are
computed pointwise: `Stacks.AlgebraicGeometry.TwistTensor.twistMultiplicationMap_tmul` says the
multiplication map takes the pure tensor to the pointwise product of the two local fractions, and
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafMap_app_apply` says
multiplication by `a` acts fibrewise as the localization of multiplication by `a`. What remains is
`u * (a • v) = a • (u * v)` in the localization, which is `mul_smul_comm`.

## References

* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.ProjTwistedSections
open Stacks.AlgebraicGeometry.TwistTensor (twistMultiplicationMap_tmul)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep

universe u w

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The multiplication `𝒪(e) ⊗ 𝒪(d) ⟶ 𝒪(e + d)` is natural in the second factor** for the
maps given by multiplication by a homogeneous scalar `a ∈ 𝒮 i`: tensoring `𝒪(e)` with
multiplication by `a` and then multiplying is multiplying and then multiplying by `a`. -/
theorem mul_comp_twistMultiplicationMap
    (e : ℤ) (i : ℕ) (d k : ℤ) (hk : (i : ℤ) + d = k) (hek : (i : ℤ) + (e + d) = e + k)
    (a : 𝒮 i) :
    twistSheafScalarMap 𝒮 (twistingSheaf 𝒮 e) i d k hk a ≫ twistMultiplicationMap 𝒮 e k =
      twistMultiplicationMap 𝒮 e d ≫ twistScalarSheafMap 𝒮 i (e + d) (e + k) hek a := by
  refine Stacks.AlgebraicGeometry.ProjTwistTheta.tensorSheaf_hom_ext
    (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace) (F := twistingSheaf 𝒮 e)
    (G := twistingSheaf 𝒮 d) (N := twistingSheaf 𝒮 (e + k))
    (twistSheafScalarMap 𝒮 (twistingSheaf 𝒮 e) i d k hk a ≫ twistMultiplicationMap 𝒮 e k)
    (twistMultiplicationMap 𝒮 e d ≫ twistScalarSheafMap 𝒮 i (e + d) (e + k) hek a) ?_
  intro U x y
  obtain ⟨W⟩ := U
  apply Subtype.ext
  funext p
  have hL : (((twistSheafScalarMap 𝒮 (twistingSheaf 𝒮 e) i d k hk a ≫
          twistMultiplicationMap 𝒮 e k).val.app (op W)).hom
      (toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace
        (twistingSheaf 𝒮 e) (twistingSheaf 𝒮 d) (op W) (x ⊗ₜ[_] y))).1 p =
      x.1 p * (((twistScalarSheafMap 𝒮 i d k hk a).val.app (op W)).hom y).1 p := by
    refine Eq.trans (congrArg
      (fun s : ProjectiveSpectrum.Proj.moduleSections 𝒮 (twistGrading (S := S) 𝒮 (e + k)) W =>
        s.1 p) ?_)
      (twistMultiplicationMap_tmul 𝒮 e k W x
        (((twistScalarSheafMap 𝒮 i d k hk a).val.app (op W)).hom y) p)
    exact congrArg ((twistMultiplicationMap 𝒮 e k).val.app (op W)).hom
      (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
        (AlgebraicGeometry.Proj 𝒮).toRingedSpace (twistingSheaf 𝒮 e) (twistingSheaf 𝒮 d)
        (twistingSheaf 𝒮 e) (twistingSheaf 𝒮 k) (𝟙 (twistingSheaf 𝒮 e))
        (twistScalarSheafMap 𝒮 i d k hk a) W x y)
  have hmap : ∀ (c c' : ℤ) (h : (i : ℤ) + c = c') (s : (twistingSheaf 𝒮 c).val.obj (op W)),
      (((twistScalarSheafMap 𝒮 i c c' h a).val.app (op W)).hom s).1 p = (a : S) • s.1 p := by
    intro c c' h s
    refine (ProjStalkGlobalSections.associatedModuleSheafMap_app_apply 𝒮
      (twistGrading (S := S) 𝒮 c) (twistGrading (S := S) 𝒮 c') (LinearMap.mul S S (a : S))
      (homogeneousMul_mem_twistGrading 𝒮 i c c' h a) W s p).trans ?_
    induction s.1 p using LocalizedModule.induction_on with
    | _ n t =>
      rw [LocalizedModule.map_mk, LocalizedModule.smul'_mk]
      exact congrArg (fun z => LocalizedModule.mk z t) (by simp)
  have hR : (((twistMultiplicationMap 𝒮 e d ≫
        twistScalarSheafMap 𝒮 i (e + d) (e + k) hek a).val.app (op W)).hom
      (toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace
        (twistingSheaf 𝒮 e) (twistingSheaf 𝒮 d) (op W) (x ⊗ₜ[_] y))).1 p =
      (a : S) • (x.1 p * y.1 p) :=
    (hmap _ _ hek _).trans (congrArg _ (twistMultiplicationMap_tmul 𝒮 e d W x y p))
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [hmap d k hk y, mul_smul_comm]

end Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep

end
