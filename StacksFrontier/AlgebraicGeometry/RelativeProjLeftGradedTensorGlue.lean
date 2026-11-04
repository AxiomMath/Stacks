module

public import StacksFrontier.AlgebraicGeometry.Morphism.Twist
public import StacksFrontier.AlgebraicGeometry.RelativeProjLeftGradedTensorFibre

/-!
# The glue square of the chart comparison of property (6) of Tag 01O7

Let `s` be a relative `Proj` situation and let `ℳ`, `𝒩` be left graded modules over its graded
algebra with quasi-coherent homogeneous pieces. The chart comparison
`Stacks.RelativeProj.Situation.moduleChartTensorMap` of property (6) of Tag 01O7 is given one
member per affine open `W` of the base, and gluing those members asks that they agree where two
charts overlap. `StacksFrontier/AlgebraicGeometry/RelativeProjLeftGradedTensorFibre.lean` proves the
agreement for two *nested* charts in the *module fibres*; this file lifts that identity to the
sheaves, as an identity of maps on sections over an arbitrary open `V` of the relative projective
spectrum.

The comparison of the chart sheaves over `W ≤ W'` is
`Stacks.RelativeProj.Situation.modulePushforwardMap`, and it is defined for the sheaf attached to
a graded module. The source of property (6) is a *tensor product* of two such sheaves, which is
not of that form, so there is no `modulePushforwardMap` for it. None is needed: pushing a tensor
product forward is not required, only the image of a pure tensor of honest sections, and that
image is supplied by the sheafification unit
`Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`. The square therefore compares
the two chart comparisons on the image of a pure tensor, with the two factors transported
separately by their own `modulePushforwardMap`.

## Main results

* `Stacks.RelativeProj.Situation.modulePushforwardMap_moduleChartTensorMap`: **the chart
  comparisons of property (6) of Tag 01O7 commute with the comparisons of the chart sheaves
  attached to an inclusion `W ≤ W'` of affine opens of the base, on the image of a pure tensor of
  honest sections.** This is the analogue for property (6) of
  `Stacks.RelativeProj.Situation.modulePushforwardMap_moduleChartMap`, which is the glue square of
  property (4).
* `Stacks.RelativeProj.Situation.image_top_relativeProjChart_inf_le_iSup`: the overlap of two
  charts is covered by the charts over the affine opens of the base below both.
* `Stacks.RelativeProj.Situation.localApp_relativeProjChart_eq_of_nested`: **for the chart cover
  of a relative projective spectrum, the gluing compatibility over an arbitrary pair of affine
  opens of the base follows from the nested case** — the hypothesis `hψ` of
  `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` reduced to
  inclusions, for an arbitrary pair of sheaves of modules on the relative projective spectrum and
  arbitrary local morphism data on the charts. Neither this nor the preceding statement mentions
  the tensor product; both are the chart-cover half of any such gluing.

## Implementation notes

The square is the single fibre identity
`Stacks.RelativeProj.Situation.fibreMap_sectionTensorMap`, flanked by the two readings of the
chart comparison on a pure tensor given by
`Stacks.RelativeProj.Situation.moduleChartTensorMap_toTensorSheafSection_tmul_apply` — once over
`W'` at the point below `x`, and once over `W` at `x`. The value of `modulePushforwardMap` at a
point of the smaller chart is a module fibre comparison by
`Stacks.RelativeProj.Situation.modulePushforwardMap_val`, which holds by `rfl`, so the two
transported factors on the right need no step of their own.

The chart comparisons are applied at the preimages of `V` rather than pushed forward along the
charts. The two are definitionally equal, but asking `whnf` to see that while unifying the whole
right-hand side exhausts the heartbeat budget; applied at the preimage the same proof is
immediate. The statement is also the one a consumer wants, since the comparison of the chart
sheaves is already indexed by `V`.

The sections are typed as `AlgebraicGeometry.ProjectiveSpectrum.Proj.moduleSections` over the
preimage of `V` rather than as `Stacks.RelativeProj.Situation.openSections` of the pushforward.
The two are definitionally equal, and the pure tensor elaborates only at the first spelling: the
module structure registered on `openSections` is over the functions on `V` on the relative
projective spectrum, while the tensor product whose sheafification unit is wanted is over the
functions on the preimage of `V` on the chart.

`AlgebraicGeometry.ProjectiveSpectrum.isPrime` is installed as a local instance at file scope, as
in the file proving the fibre identities: an `attribute [local instance]` inside a namespace does
not survive the `end`, and the failure it causes is reported as a missing `IsPrime` instance
several declarations later.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01MK](https://stacks.math.columbia.edu/tag/01MK)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)

-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.GradedLocalization Stacks.ProjModuleComparison
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open scoped TensorProduct

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.RelativeProj.Situation

open Stacks.AlgebraicGeometry.ModuleHomGlue

/-! ### The chart cover refines its own overlaps

Nothing in this section mentions the tensor product: it is the gluing compatibility for the chart
cover of a relative projective spectrum, for an arbitrary pair of sheaves of modules on it. -/

/-- **The overlap of two charts of a relative projective spectrum is covered by the charts over
the affine opens of the base below both.** This is
`Stacks.RelativeProj.Situation.locallyDirected_relativeProjChart` with the chart images written as
images of the top open, which is the shape
`Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine` consumes. -/
public theorem image_top_relativeProjChart_inf_le_iSup (s : Situation.{u})
    (W W' : s.base.affineOpens) :
    relativeProjChart s W ''ᵁ ⊤ ⊓ relativeProjChart s W' ''ᵁ ⊤
      ≤ ⨆ m : {m : s.base.affineOpens // m ≤ W ∧ m ≤ W'},
          relativeProjChart s m.1 ''ᵁ ⊤ := by
  simpa only [Scheme.Hom.image_top_eq_opensRange]
    using locallyDirected_relativeProjChart s W W'

/-- **For the chart cover of a relative projective spectrum, the gluing compatibility over an
arbitrary pair of affine opens of the base follows from the nested case.** Given local morphism
data on the charts which agrees wherever one affine open of the base contains another, the data
agrees wherever two charts see the same open of the relative projective spectrum — which is the
hypothesis `hψ` of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for the cover
`Stacks.RelativeProj.Situation.iSup_opensRange_relativeProjChart`.

This is `Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine` for the chart cover: the
relation on the index is the containment of affine opens of the base, and the covering of each
pairwise overlap by members below both is
`Stacks.RelativeProj.Situation.image_top_relativeProjChart_inf_le_iSup`. Nothing is assumed of
the two sheaves of modules. -/
public theorem localApp_relativeProjChart_eq_of_nested {s : Situation.{u}}
    {M N : (relativeProj s).Modules}
    (Θ : ∀ W : s.base.affineOpens,
      M.restrict (relativeProjChart s W) ⟶ N.restrict (relativeProjChart s W))
    (hnest : ∀ W W' : s.base.affineOpens, W' ≤ W →
      ∀ (V : (relativeProj s).Opens)
        (W₁ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens)
        (W₂ : (AlgebraicGeometry.Proj (s.sectionRingGrading W'.1)).Opens)
        (h₁ : relativeProjChart s W ''ᵁ W₁ = V) (h₂ : relativeProjChart s W' ''ᵁ W₂ = V),
        localApp (relativeProjChart s W) (Θ W) h₁
          = localApp (relativeProjChart s W') (Θ W') h₂)
    (W W' : s.base.affineOpens)
    (W₁ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens)
    (W₂ : (AlgebraicGeometry.Proj (s.sectionRingGrading W'.1)).Opens)
    (V : (relativeProj s).Opens)
    (h₁ : relativeProjChart s W ''ᵁ W₁ = V) (h₂ : relativeProjChart s W' ''ᵁ W₂ = V) :
    localApp (relativeProjChart s W) (Θ W) h₁
      = localApp (relativeProjChart s W') (Θ W') h₂ :=
  Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine (relativeProjChart s) Θ
    (κ := fun T U => {m : s.base.affineOpens // m ≤ T ∧ m ≤ U})
    (fun _ _ m => m.1) (fun T U => U ≤ T)
    (fun _ _ m => m.2.1) (fun _ _ m => m.2.2)
    (image_top_relativeProjChart_inf_le_iSup s)
    (fun i j hij => hnest i j hij) W W' W₁ W₂ V h₁ h₂

/-! ### The glue square of the chart comparison -/

attribute [local instance] sectionModuleDecomposition

variable {s : Situation.{u}} (ℳ 𝒩 : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (𝒩.piece n).IsQuasicoherent]

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (𝒩.piece n).IsQuasicoherent] in
/-- **The chart comparisons of property (6) of Tag 01O7 commute with the comparisons of the chart
sheaves** attached to an inclusion `W ≤ W'` of affine opens of the base, on the image of a pure
tensor of honest sections.

This is the glue square of property (6), the analogue of
`Stacks.RelativeProj.Situation.modulePushforwardMap_moduleChartMap` for property (4). Both sides
are pointwise in the module fibres, where the comparison of the chart sheaves is a module fibre
comparison and the chart comparison is the comparison of the graded modules of sections localized
at the point; so the square is the fibre identity
`Stacks.RelativeProj.Situation.fibreMap_sectionTensorMap`. -/
public theorem modulePushforwardMap_moduleChartTensorMap
    {W W' : s.base.affineOpens} (h : W ≤ W') {V : (relativeProj s).Opens}
    (a : ProjectiveSpectrum.Proj.moduleSections (s.sectionRingGrading W'.1)
      (sectionModuleGrading ℳ W'.1) (relativeProjChart s W' ⁻¹ᵁ V))
    (b : ProjectiveSpectrum.Proj.moduleSections (s.sectionRingGrading W'.1)
      (sectionModuleGrading 𝒩 W'.1) (relativeProjChart s W' ⁻¹ᵁ V))
    (x : relativeProjChart s W ⁻¹ᵁ V) :
    letI := tensorGrading_decomposition (S := s.sectionRing W'.1) (s.sectionRingGrading W'.1)
      (sectionModuleGrading ℳ W'.1) (sectionModuleGrading 𝒩 W'.1)
    letI := tensorGrading_gradedSMul (S := s.sectionRing W'.1) (s.sectionRingGrading W'.1)
      (sectionModuleGrading ℳ W'.1) (sectionModuleGrading 𝒩 W'.1)
    letI := tensorGrading_decomposition (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    letI := tensorGrading_gradedSMul (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    (((modulePushforwardMap (s.leftGradedTensor ℳ 𝒩) h).val.app (op V)).hom
        (((moduleChartTensorMap ℳ 𝒩 W').val.app
              (op (relativeProjChart s W' ⁻¹ᵁ V))).hom
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
            (AlgebraicGeometry.Proj (s.sectionRingGrading W'.1)).toRingedSpace
            (moduleChart ℳ W') (moduleChart 𝒩 W')
            (op (relativeProjChart s W' ⁻¹ᵁ V)) (a ⊗ₜ[_] b)))).1 x
      = (((moduleChartTensorMap ℳ 𝒩 W).val.app
              (op (relativeProjChart s W ⁻¹ᵁ V))).hom
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
            (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).toRingedSpace
            (moduleChart ℳ W) (moduleChart 𝒩 W)
            (op (relativeProjChart s W ⁻¹ᵁ V))
            (((modulePushforwardMap ℳ h).val.app (op V)).hom a ⊗ₜ[_]
              ((modulePushforwardMap 𝒩 h).val.app (op V)).hom b))).1 x := by
  let := tensorGrading_decomposition (S := s.sectionRing W'.1) (s.sectionRingGrading W'.1)
    (sectionModuleGrading ℳ W'.1) (sectionModuleGrading 𝒩 W'.1)
  let := tensorGrading_gradedSMul (S := s.sectionRing W'.1) (s.sectionRingGrading W'.1)
    (sectionModuleGrading ℳ W'.1) (sectionModuleGrading 𝒩 W'.1)
  let := tensorGrading_decomposition (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
  let := tensorGrading_gradedSMul (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
  refine Eq.trans (congrArg
    (fibreMap (gradedSectionRestriction s W.1 W'.1 h)
      (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
      (sectionModuleRestrictₛₗ (s.leftGradedTensor ℳ 𝒩) h) x.1)
    (moduleChartTensorMap_toTensorSheafSection_tmul_apply ℳ 𝒩 W'
      (relativeProjChart s W' ⁻¹ᵁ V) a b
      ⟨_, comapFun_gradedSectionRestriction_mem s h x⟩)) ?_
  refine Eq.trans (fibreMap_sectionTensorMap ℳ 𝒩 h x.1 _ _) ?_
  exact (moduleChartTensorMap_toTensorSheafSection_tmul_apply ℳ 𝒩 W
    (relativeProjChart s W ⁻¹ᵁ V)
    (((modulePushforwardMap ℳ h).val.app (op V)).hom a)
    (((modulePushforwardMap 𝒩 h).val.app (op V)).hom b) x).symm

end Stacks.RelativeProj.Situation

end
