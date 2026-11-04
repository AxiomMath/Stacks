module

public import StacksFrontier.AlgebraicGeometry.RelativeProjLeftGradedTensorSections
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheafFunctorial

/-!
# The module fibres of the chart comparison of property (6) of Tag 01O7

Let `s` be a relative `Proj` situation and let `ℳ`, `𝒩` be left graded modules over its graded
algebra. The chart comparison
`Stacks.RelativeProj.Situation.moduleChartTensorMap` of property (6) of Tag 01O7 over an affine
open `W` of the base is the canonical morphism of Tag 01MK followed by the morphism of Tag 01M7
induced by the comparison `Stacks.RelativeProj.Situation.sectionTensorMap` of the graded modules
of sections. Both of those are pointwise in the module fibres, so the chart comparison is too,
and this file reads it there and compares the readings over two nested charts.

The canonical morphism of Tag 01MK is the sheafification of the pointwise tensor of sections, so
on the image of a pure tensor of honest sections its value at a point of the chart is the tensor
of the two local values, read through the identification
`...ProjSheafFunctoriality.tensorLocalizationEquivOverLocalization` of the localization of a
tensor product with the tensor product of the localizations.

## Main results

* `ProjSheafFunctoriality.associatedModuleSheafTensorMap_toTensorSheafSection_tmul_apply`:
  **the value at a point of the canonical morphism of Tag 01MK on the image of a pure tensor of
  honest sections** is the tensor of the two local values.
* `Stacks.ProjModuleComparison.fibreMap_tensorLocalization`: **the module fibre comparison of a
  graded ring homomorphism commutes with the identification of the localization of a tensor
  product with the tensor product of the localizations.** This is the tensor-source companion of
  `Stacks.ProjModuleComparison.fibreMap_localizedModuleMap`, which does not serve a tensor
  source: the fibre reading of the morphism of Tag 01MK is
  `tensorLocalizationEquivOverLocalization`, whose source is a tensor of two localized modules
  rather than a localization of one. On a pair of fractions `m / s`, `n / t` both sides are
  `(fM m ⊗ fN n) / (φ s · φ t)`.
* `Stacks.ProjModuleComparison.fibreMap_tensorLocalizationEquiv`: the same with a localized
  linear map out of the tensor product applied as well, which is the two halves of the chart
  comparison in one statement.
* `Stacks.RelativeProj.Situation.moduleChartTensorMap_toTensorSheafSection_tmul_apply`: **the
  value at a point of the chart comparison of property (6) of Tag 01O7 on the image of a pure
  tensor of honest sections**: the comparison of the graded modules of sections, localized, of
  the tensor of the two local values.
* `Stacks.RelativeProj.Situation.restrictTensorₛₗ_mem_grading`: **restriction of the tensor
  products of the graded modules of sections preserves the tensor grading** — the
  degree-preservation datum the tensor product of the graded modules of sections needs to have a
  comparison of its chart sheaves at all.
* `Stacks.RelativeProj.Situation.fibreMap_restrictTensorₛₗ` and
  `Stacks.RelativeProj.Situation.fibreMap_localizedModuleMap_sectionTensorMap`: **the Tag 01MK
  half and the Tag 01M7 half of the nested-chart compatibility of the chart comparison, in the
  module fibres**, the first from `Stacks.RelativeProj.Situation.restrictTensorₛₗ_tmul` and the
  second from `Stacks.RelativeProj.Situation.sectionModuleRestrict_sectionTensorMap`.
* `Stacks.RelativeProj.Situation.fibreMap_sectionTensorMap`: **the chart comparison of property
  (6) of Tag 01O7 commutes, in the module fibres, with the comparison of the charts over an
  inclusion `W ≤ W'` of affine opens of the base** — the two halves composed.

## Implementation notes

`Stacks.ProjModuleComparison.fibreMap_tensorLocalizationEquiv` takes the commuting square of
linear maps as a hypothesis on pure tensors only. This suffices here: the restriction maps of
the graded modules of sections are semilinear over the restriction of the graded section rings,
and the comparison of the graded modules of sections commutes with them on
pure tensors by `Stacks.RelativeProj.Situation.sectionTensorMap_restrict`. No degree
bookkeeping survives into the fibres: the hypothesis is an equation of linear maps and the two
localizations are at the homogeneous primes, so the whole statement is one `LocalizedModule`
induction in each variable.

The `IsPrime` instance of the homogeneous prime at a point is not found by instance search, so
`AlgebraicGeometry.ProjectiveSpectrum.isPrime` is installed as a local instance at the top of the
file rather than inside a namespace: an `attribute [local instance]` inside one does not survive
the `end`, and the failure it causes is reported as a missing `IsPrime` instance several
declarations later.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01MK](https://stacks.math.columbia.edu/tag/01MK)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)

-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite TopCat DirectSum HomogeneousIdeal
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.GradedLocalization
open Stacks.GradedModule (tensorGrading)
open scoped Stacks.GradedLocalization
open scoped TensorProduct

universe u w t t'

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.AlgebraicGeometry.ProjSheafFunctoriality

variable {S M N : Type u} {σ : Type w} {τ : Type t} {υ : Type t'}
  [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]
  [SetLike υ N] [AddSubgroupClass υ N] (𝒩 : ℤ → υ) [Decomposition 𝒩]
  [SetLike.GradedSMul 𝒮 𝒩]

attribute [local instance] tensorGrading_gradedSMul

/-- **The value, at a point, of the canonical morphism of Tag 01MK on the image of a pure tensor
of honest sections.** -/
theorem associatedModuleSheafTensorMap_toTensorSheafSection_tmul_apply
    (W : Opens (ProjectiveSpectrum.top 𝒮))
    (a : ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒨 W)
    (b : ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒩 W) (x : W) :
    letI := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
    (((associatedModuleSheafTensorMap 𝒮 𝒨 𝒩).val.app (op W)).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨)
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩) (op W) (a ⊗ₜ[_] b))).1 x
      = tensorLocalizationEquivOverLocalization (S := S) (M := M) (N := N)
          x.1.asHomogeneousIdeal.toIdeal.primeCompl (a.1 x ⊗ₜ[S] b.1 x) := by
  let := tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
  exact congrArg (fun z => z.1 x)
    ((associatedModuleSheafTensorMap_app_toTensorSheafSection 𝒮 𝒨 𝒩 (op W) _).trans
      (tensorModuleSectionsAddHom_tmul 𝒮 𝒨 𝒩 W a b))

end Stacks.AlgebraicGeometry.ProjSheafFunctoriality

namespace Stacks.ProjModuleComparison

open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

variable {A B M N Q M' N' Q' : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup Q] [Module A Q]
  [AddCommGroup M'] [Module B M'] [AddCommGroup N'] [Module B N']
  [AddCommGroup Q'] [Module B Q']
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **The module fibre comparison of a graded ring homomorphism commutes with the identification
of the localization of a tensor product with the tensor product of the localizations**, given a
semilinear map of the tensor products which is the tensor of the two semilinear maps on pure
tensors. On a pair of fractions `m / s`, `n / t` both sides are
`(fM m ⊗ fN n) / (φ s · φ t)`.

This is the fibre reading of the canonical morphism of Tag 01MK across a comparison of charts.
`Stacks.ProjModuleComparison.fibreMap_localizedModuleMap` does not serve it: its source is a
`LocalizedModule` of a single module, and this one's is a tensor product of two of them. -/
theorem fibreMap_tensorLocalization (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)
    (fM : M →ₛₗ[φ.toRingHom] M') (fN : N →ₛₗ[φ.toRingHom] N')
    (fT : M ⊗[A] N →ₛₗ[φ.toRingHom] M' ⊗[B] N')
    (hfT : ∀ (m : M) (n : N), fT (m ⊗ₜ[A] n) = fM m ⊗ₜ[B] fN n)
    (y : ProjectiveSpectrum ℬ)
    (zM : ModuleFiber (M := M) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y))
    (zN : ModuleFiber (M := N) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y)) :
    fibreMap φ hφ fT y
        (tensorLocalizationEquivOverLocalization (S := A) (M := M) (N := N)
          (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal.primeCompl
          (zM ⊗ₜ[A] zN))
      = tensorLocalizationEquivOverLocalization (S := B) (M := M') (N := N')
          y.asHomogeneousIdeal.toIdeal.primeCompl
          (fibreMap φ hφ fM y zM ⊗ₜ[B] fibreMap φ hφ fN y zN) := by
  induction zM using LocalizedModule.induction_on with
  | h m s =>
    induction zN using LocalizedModule.induction_on with
    | h n t =>
      rw [tensorLocalizationEquivOverLocalization_mk, fibreMap_mk, fibreMap_mk, fibreMap_mk,
        tensorLocalizationEquivOverLocalization_mk, hfT]
      exact congrArg (LocalizedModule.mk (fM m ⊗ₜ[B] fN n))
        (map_mul (denomMap φ hφ y) s t)

/-- **The module fibre comparison of a graded ring homomorphism commutes with a localized linear
map out of a tensor product**, read through the identification of the localization of a tensor
product with the tensor product of the localizations. This is
`Stacks.ProjModuleComparison.fibreMap_tensorLocalization` followed by
`Stacks.ProjModuleComparison.fibreMap_localizedModuleMap`, the two halves of the chart comparison
of property (6) of Tag 01O7 in the fibres. -/
theorem fibreMap_tensorLocalizationEquiv (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)
    (fM : M →ₛₗ[φ.toRingHom] M') (fN : N →ₛₗ[φ.toRingHom] N') (fQ : Q →ₛₗ[φ.toRingHom] Q')
    (u : M ⊗[A] N →ₗ[A] Q) (v : M' ⊗[B] N' →ₗ[B] Q')
    (huv : ∀ (m : M) (n : N), fQ (u (m ⊗ₜ[A] n)) = v (fM m ⊗ₜ[B] fN n))
    (y : ProjectiveSpectrum ℬ)
    (zM : ModuleFiber (M := M) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y))
    (zN : ModuleFiber (M := N) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y)) :
    fibreMap φ hφ fQ y
        (LocalizedModule.map
          (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal.primeCompl u
          (tensorLocalizationEquivOverLocalization (S := A) (M := M) (N := N)
            (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal.primeCompl
            (zM ⊗ₜ[A] zN)))
      = LocalizedModule.map y.asHomogeneousIdeal.toIdeal.primeCompl v
          (tensorLocalizationEquivOverLocalization (S := B) (M := M') (N := N')
            y.asHomogeneousIdeal.toIdeal.primeCompl
            (fibreMap φ hφ fM y zM ⊗ₜ[B] fibreMap φ hφ fN y zN)) := by
  rw [← fibreMap_tensorLocalization φ hφ fM fN (TensorProduct.map fM fN) (fun _ _ => rfl) y zM zN,
    fibreMap_localizedModuleMap φ hφ (TensorProduct.map fM fN) fQ u v
      (fun z => TensorProduct.induction_on z (by simp) (fun m n => by simpa using huv m n)
        fun x y hx hy => by simp [hx, hy]) y]

end Stacks.ProjModuleComparison

namespace Stacks.RelativeProj.Situation

open Stacks.AlgebraicGeometry.ProjSheafFunctoriality Stacks.ProjModuleComparison

attribute [local instance] sectionModuleDecomposition

variable {s : Situation.{u}} (ℳ 𝒩 : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra)

/-- **The value, at a point of the chart, of the chart comparison of property (6) of Tag 01O7 on
the image of a pure tensor of honest sections.** -/
theorem moduleChartTensorMap_toTensorSheafSection_tmul_apply (W : s.base.affineOpens)
    (V : Opens (ProjectiveSpectrum.top (s.sectionRingGrading W.1)))
    (a : ProjectiveSpectrum.Proj.moduleSections (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) V)
    (b : ProjectiveSpectrum.Proj.moduleSections (s.sectionRingGrading W.1)
      (sectionModuleGrading 𝒩 W.1) V) (x : V) :
    letI := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_decomposition
      (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    letI := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_gradedSMul
      (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    (((moduleChartTensorMap ℳ 𝒩 W).val.app (op V)).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).toRingedSpace
          (moduleChart ℳ W) (moduleChart 𝒩 W) (op V) (a ⊗ₜ[_] b))).1 x
      = LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl
          (sectionTensorMap ℳ 𝒩 W.1)
          (tensorLocalizationEquivOverLocalization
            (S := s.sectionRing W.1) (M := sectionModule ℳ W.1) (N := sectionModule 𝒩 W.1)
            x.1.asHomogeneousIdeal.toIdeal.primeCompl
            (a.1 x ⊗ₜ[s.sectionRing W.1] b.1 x)) := by
  exact congrArg
    (LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl (sectionTensorMap ℳ 𝒩 W.1))
    (associatedModuleSheafTensorMap_toTensorSheafSection_tmul_apply
      (s.sectionRingGrading W.1) (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
      V a b x)

/-- **Restriction of the tensor products of the graded modules of sections preserves the tensor
grading.** This is the degree-preservation datum that the tensor product of the graded modules of
sections needs in order to have a comparison of its chart sheaves at all: it is the hypothesis
`hf` of `Stacks.ProjModuleComparison.pushforwardModuleMap` for
`Stacks.RelativeProj.Situation.restrictTensorₛₗ`, the analogue for the tensor product of
`Stacks.RelativeProj.Situation.sectionModuleRestrictₛₗ_mem_grading`. The tensor grading is
generated by the pure tensors of homogeneous sections, restriction carries such a tensor to the
tensor of the restrictions, and restriction of the graded modules of sections preserves
degrees. -/
theorem restrictTensorₛₗ_mem_grading {V W : s.base.Opens} (h : V ≤ W) (i : ℤ)
    {z : sectionModule ℳ W ⊗[s.sectionRing W] sectionModule 𝒩 W}
    (hz : z ∈ Stacks.GradedModule.tensorGrading
      (sectionModuleGrading ℳ W) (sectionModuleGrading 𝒩 W) i) :
    restrictTensorₛₗ ℳ 𝒩 h z ∈ Stacks.GradedModule.tensorGrading
      (sectionModuleGrading ℳ V) (sectionModuleGrading 𝒩 V) i := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
      obtain ⟨p, q, hpq, m, hm, n, hn, rfl⟩ := hz
      rw [restrictTensorₛₗ_tmul]
      exact Stacks.GradedModule.tmul_mem_tensorGrading _ _ hpq
        (sectionModuleRestrictₛₗ_mem_grading ℳ h p hm)
        (sectionModuleRestrictₛₗ_mem_grading 𝒩 h q hn)
  | zero => simpa only [map_zero] using AddSubgroup.zero_mem _
  | add x y _ _ ihx ihy => simpa only [map_add] using AddSubgroup.add_mem _ ihx ihy
  | neg x _ ih => simpa only [map_neg] using AddSubgroup.neg_mem _ ih

/-- **The Tag 01MK half of the chart comparison, in the module fibres**: the fibre comparison of
the restriction of the graded modules of sections carries the fraction of a tensor to the tensor
of the fractions. This is
`Stacks.ProjModuleComparison.fibreMap_tensorLocalization` for the restriction maps, whose
commuting square on pure tensors is
`Stacks.RelativeProj.Situation.restrictTensorₛₗ_tmul`. -/
theorem fibreMap_restrictTensorₛₗ {W W' : s.base.affineOpens} (h : W ≤ W')
    (y : ProjectiveSpectrum (s.sectionRingGrading W.1))
    (zM : ModuleFiber (M := sectionModule ℳ W'.1) (s.sectionRingGrading W'.1)
      (ProjectiveSpectrum.comapFun (gradedSectionRestriction s W.1 W'.1 h)
        (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2) y))
    (zN : ModuleFiber (M := sectionModule 𝒩 W'.1) (s.sectionRingGrading W'.1)
      (ProjectiveSpectrum.comapFun (gradedSectionRestriction s W.1 W'.1 h)
        (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2) y)) :
    fibreMap (gradedSectionRestriction s W.1 W'.1 h)
        (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
        (restrictTensorₛₗ ℳ 𝒩 h) y
        (tensorLocalizationEquivOverLocalization _ (zM ⊗ₜ[s.sectionRing W'.1] zN))
      = tensorLocalizationEquivOverLocalization _
          (fibreMap (gradedSectionRestriction s W.1 W'.1 h)
              (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
              (sectionModuleRestrictₛₗ ℳ h) y zM
            ⊗ₜ[s.sectionRing W.1]
            fibreMap (gradedSectionRestriction s W.1 W'.1 h)
              (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
              (sectionModuleRestrictₛₗ 𝒩 h) y zN) :=
  fibreMap_tensorLocalization (gradedSectionRestriction s W.1 W'.1 h)
    (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
    (sectionModuleRestrictₛₗ ℳ h) (sectionModuleRestrictₛₗ 𝒩 h) (restrictTensorₛₗ ℳ 𝒩 h)
    (fun z w => restrictTensorₛₗ_tmul ℳ 𝒩 h z w) y zM zN

/-- **The Tag 01M7 half of the chart comparison, in the module fibres**: the fibre comparison of
the restriction of the graded modules of sections commutes with the localization of the
comparison `Stacks.RelativeProj.Situation.sectionTensorMap` of the graded modules of sections,
on an arbitrary element of the fibre of the tensor product. This is
`Stacks.ProjModuleComparison.fibreMap_localizedModuleMap` for the restriction maps, whose
commuting square is `Stacks.RelativeProj.Situation.sectionModuleRestrict_sectionTensorMap`. -/
theorem fibreMap_localizedModuleMap_sectionTensorMap {W W' : s.base.affineOpens} (h : W ≤ W')
    (y : ProjectiveSpectrum (s.sectionRingGrading W.1))
    (z : ModuleFiber
      (M := sectionModule ℳ W'.1 ⊗[s.sectionRing W'.1] sectionModule 𝒩 W'.1)
      (s.sectionRingGrading W'.1)
      (ProjectiveSpectrum.comapFun (gradedSectionRestriction s W.1 W'.1 h)
        (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2) y)) :
    fibreMap (gradedSectionRestriction s W.1 W'.1 h)
        (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
        (sectionModuleRestrictₛₗ (s.leftGradedTensor ℳ 𝒩) h) y
        (LocalizedModule.map _ (sectionTensorMap ℳ 𝒩 W'.1) z)
      = LocalizedModule.map _ (sectionTensorMap ℳ 𝒩 W.1)
          (fibreMap (gradedSectionRestriction s W.1 W'.1 h)
            (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
            (restrictTensorₛₗ ℳ 𝒩 h) y z) :=
  fibreMap_localizedModuleMap (gradedSectionRestriction s W.1 W'.1 h)
    (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
    (restrictTensorₛₗ ℳ 𝒩 h) (sectionModuleRestrictₛₗ (s.leftGradedTensor ℳ 𝒩) h)
    (sectionTensorMap ℳ 𝒩 W'.1) (sectionTensorMap ℳ 𝒩 W.1)
    (fun z => (sectionModuleRestrict_sectionTensorMap ℳ 𝒩 h z).symm) y z

/-- **The chart comparison of property (6) of Tag 01O7 commutes, in the module fibres, with the
comparison of the charts over an inclusion `W ≤ W'` of affine opens of the base.** -/
theorem fibreMap_sectionTensorMap {W W' : s.base.affineOpens} (h : W ≤ W')
    (y : ProjectiveSpectrum (s.sectionRingGrading W.1))
    (zM : ModuleFiber (M := sectionModule ℳ W'.1) (s.sectionRingGrading W'.1)
      (ProjectiveSpectrum.comapFun (gradedSectionRestriction s W.1 W'.1 h)
        (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2) y))
    (zN : ModuleFiber (M := sectionModule 𝒩 W'.1) (s.sectionRingGrading W'.1)
      (ProjectiveSpectrum.comapFun (gradedSectionRestriction s W.1 W'.1 h)
        (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2) y)) :
    fibreMap (gradedSectionRestriction s W.1 W'.1 h)
        (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
        (sectionModuleRestrictₛₗ (s.leftGradedTensor ℳ 𝒩) h) y
        (LocalizedModule.map _ (sectionTensorMap ℳ 𝒩 W'.1)
          (tensorLocalizationEquivOverLocalization _ (zM ⊗ₜ[s.sectionRing W'.1] zN)))
      = LocalizedModule.map _ (sectionTensorMap ℳ 𝒩 W.1)
          (tensorLocalizationEquivOverLocalization _
            (fibreMap (gradedSectionRestriction s W.1 W'.1 h)
                (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
                (sectionModuleRestrictₛₗ ℳ h) y zM
              ⊗ₜ[s.sectionRing W.1]
              fibreMap (gradedSectionRestriction s W.1 W'.1 h)
                (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
                (sectionModuleRestrictₛₗ 𝒩 h) y zN)) :=
  fibreMap_tensorLocalizationEquiv (gradedSectionRestriction s W.1 W'.1 h)
    (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
    (sectionModuleRestrictₛₗ ℳ h) (sectionModuleRestrictₛₗ 𝒩 h)
    (sectionModuleRestrictₛₗ (s.leftGradedTensor ℳ 𝒩) h)
    (sectionTensorMap ℳ 𝒩 W'.1) (sectionTensorMap ℳ 𝒩 W.1)
    (fun z w => (sectionTensorMap_restrict ℳ 𝒩 h z w).symm) y zM zN

end Stacks.RelativeProj.Situation

end
