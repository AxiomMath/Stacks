module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ConvolutionPerfect
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernelPerfect
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalenceLimitDescent
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# The limit theorem for relative equivalences over Noetherian stages

The assembly `AlgebraicGeometry.exists_isRelativeEquivalenceKernel_of_descentSituation` of
[Stacks, Tag 0G0L] takes the perfectness of the diagonal kernel and of the convolution kernel
as an input `hperf`. Over an arbitrary base that input is
`AlgebraicGeometry.diagonalKernelAndConvolutionPerfect`, and [Stacks, Tag 0G0L] itself is
`AlgebraicGeometry.exists_isRelativeEquivalenceKernel_of_limit`. This file gives a second route
for situations with Noetherian stages: it proves the perfectness input over a Noetherian base
from `AlgebraicGeometry.isPerfect_fourierMukaiConvolution_of_isNoetherian`, which suffices since
the source's proof uses the input at the stages of the system, and restates the limit theorem
for such situations; its base-change input is
`AlgebraicGeometry.diagonalKernelAndConvolutionBaseChange`.

## Main results

* `AlgebraicGeometry.isPerfect_iff_ringedSpace_isPerfect` — the two spellings of perfectness of
  [Stacks, Tag 08CM] agree.
* `AlgebraicGeometry.diagonalKernelAndConvolutionPerfectOfNoetherian` — perfectness of the
  diagonal and convolution kernels over a Noetherian base.
* `AlgebraicGeometry.exists_isRelativeEquivalenceKernel_of_descentSituation_of_isNoetherian` —
  [Stacks, Tag 0G0L] for Noetherian stages, with only the two halves of [Stacks, Tag 09RF] as
  inputs.

## References

* [Stacks Project, Tag 0G0L](https://stacks.math.columbia.edu/tag/0G0L)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

universe v u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **The two spellings of perfectness of [Stacks, Tag 08CM] agree**: they are the same
definition, stated once with independent universes and once at a single universe. -/
theorem isPerfect_iff_ringedSpace_isPerfect {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{v} (StrictlyPerfect.OXMod.{u, u} X)]
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)) :
    IsPerfect K ↔ RingedSpace.IsPerfect K := by
  constructor <;> rintro ⟨E, ⟨I, U, hU, h⟩, e⟩ <;>
    exact ⟨E, ⟨I, U, hU, fun i => by
      obtain ⟨P, hP, φ, hφ⟩ := h i
      exact ⟨P, hP, φ, hφ⟩⟩, e⟩

/-- **Perfectness of the diagonal kernel and of the convolution kernel over a Noetherian base**:
for smooth proper `f : X ⟶ S` and `g : Y ⟶ S` with `S` Noetherian. -/
abbrev DiagonalKernelAndConvolutionPerfectOfNoetherian : Prop :=
  ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S), IsNoetherian S → Smooth f → IsProper f →
    Smooth g → IsProper g →
    IsPerfect (X := (pullback f f).toRingedSpace) (diagonalKernel f) ∧
      ∀ (K : DerivedCategory (pullback f g).Modules)
        (K' : DerivedCategory (pullback g f).Modules),
        IsPerfect (X := (pullback f g).toRingedSpace) K →
        IsPerfect (X := (pullback g f).toRingedSpace) K' →
        IsPerfect (X := (pullback f f).toRingedSpace)
          (fourierMukaiConvolution f g f K K')

/-- **The diagonal kernel and the convolution kernel are perfect over a Noetherian base.** The
first is `AlgebraicGeometry.isPerfect_diagonalKernel_ringedSpace` ([Stacks, Tag 0FDP] with
[Stacks, Tag 0G2E]); the second is
`AlgebraicGeometry.isPerfect_fourierMukaiConvolution_of_isNoetherian` ([Stacks, Tag 0B6G]),
`X ×_S X` being of finite type over the Noetherian `S`. -/
theorem diagonalKernelAndConvolutionPerfectOfNoetherian :
    DiagonalKernelAndConvolutionPerfectOfNoetherian.{u} := by
  intro S X Y f g hS hfs hfp hgs hgp
  refine ⟨?_, fun K K' hK hK' => ?_⟩
  · exact (isPerfect_iff_ringedSpace_isPerfect (diagonalKernel f)).mpr
      (isPerfect_diagonalKernel_ringedSpace f)
  · have : IsNoetherian (pullback f f : Scheme.{u}) :=
      isNoetherian_of_locallyOfFiniteType (pullback.fst f f ≫ f)
    exact isPerfect_fourierMukaiConvolution_of_isNoetherian f g f hK hK'

section Main

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation.{v, u} I)

/-- **One descent step.** Given a stage `i`, perfect kernels `Ki` and `Ki'` there whose derived
pullbacks to the limit are `K` and `K'`, and the first displayed isomorphism of
[Stacks, Tag 0G0I] over the limit, the first displayed isomorphism holds at some stage `j ≥ i`
for the derived pullbacks of `Ki` and `Ki'` to that stage. -/
lemma exists_stage_diagonal_iso_of_isNoetherian
    (h09RFiso : PerfectIsoDescendsAlongBaseChangedTower.{v, u})
    (hN : ∀ i : I, IsNoetherian (D.stage i))
    (hperf : DiagonalKernelAndConvolutionPerfectOfNoetherian.{u})
    {X₀ Y₀ : Scheme.{u}} (x : X₀ ⟶ D.stage D.base) (y : Y₀ ⟶ D.stage D.base)
    [Smooth x] [IsProper x] [Smooth y] [IsProper y] (i : I) (hi : D.base ≤ i)
    (Ki : DerivedCategory (pullback (pullback.snd x (D.transition hi))
      (pullback.snd y (D.transition hi))).Modules)
    (Ki' : DerivedCategory (pullback (pullback.snd y (D.transition hi))
      (pullback.snd x (D.transition hi))).Modules)
    (hKi : IsPerfect (X := (pullback (pullback.snd x (D.transition hi))
      (pullback.snd y (D.transition hi))).toRingedSpace) Ki)
    (hKi' : IsPerfect (X := (pullback (pullback.snd y (D.transition hi))
      (pullback.snd x (D.transition hi))).toRingedSpace) Ki')
    (e : Nonempty (diagonalKernel (pullback.snd x (D.projection D.base)) ≅
      fourierMukaiConvolution (pullback.snd x (D.projection D.base))
        (pullback.snd y (D.projection D.base)) (pullback.snd x (D.projection D.base))
        ((derivedPullback (baseChangeProduct x y
          (D.projection_comp_transition hi)).toLRSHom.toShHom).obj Ki)
        ((derivedPullback (baseChangeProduct y x
          (D.projection_comp_transition hi)).toLRSHom.toShHom).obj Ki'))) :
    ∃ (j : I) (hij : i ≤ j),
      Nonempty (diagonalKernel (pullback.snd x (D.transition (hi.trans hij))) ≅
        fourierMukaiConvolution (pullback.snd x (D.transition (hi.trans hij)))
          (pullback.snd y (D.transition (hi.trans hij)))
          (pullback.snd x (D.transition (hi.trans hij)))
          ((derivedPullback (baseChangeProduct x y
            (D.transition_comp_transition hi hij)).toLRSHom.toShHom).obj Ki)
          ((derivedPullback (baseChangeProduct y x
            (D.transition_comp_transition hi hij)).toLRSHom.toShHom).obj Ki')) := by
  have hcmp := nonempty_pullback_iso_of_diagonal_iso diagonalKernelAndConvolutionBaseChange x y
    (D.projection_comp_transition hi) Ki Ki' hKi hKi' e
  obtain ⟨hdiag, hconv⟩ := hperf (pullback.snd x (D.transition hi))
    (pullback.snd y (D.transition hi)) (hN i) inferInstance inferInstance
    inferInstance inferInstance
  obtain ⟨j, hij, hj⟩ := h09RFiso D x x inferInstance inferInstance inferInstance inferInstance
    i hi (diagonalKernel (pullback.snd x (D.transition hi)))
    (fourierMukaiConvolution (pullback.snd x (D.transition hi))
      (pullback.snd y (D.transition hi)) (pullback.snd x (D.transition hi)) Ki Ki')
    hdiag (hconv Ki Ki' hKi hKi') hcmp
  exact ⟨j, hij, nonempty_diagonal_iso_of_pullback_iso diagonalKernelAndConvolutionBaseChange x y
    (D.transition_comp_transition hi hij) Ki Ki' hKi hKi' hj⟩

/-- **The descent of a relative equivalence, starting from a stage at which the kernel and its
partner already live.** Given a stage `i`, perfect objects `Ki` and `Ki'` there whose derived
pullbacks to the limit are the kernel `K` of a relative equivalence over the limit and its
partner `K'`, there is a stage carrying a Fourier-Mukai kernel of a relative equivalence. -/
lemma exists_isRelativeEquivalenceKernel_of_stage_of_isNoetherian
    (h09RFiso : PerfectIsoDescendsAlongBaseChangedTower.{v, u})
    (hN : ∀ i : I, IsNoetherian (D.stage i))
    (hperf : DiagonalKernelAndConvolutionPerfectOfNoetherian.{u})
    {X₀ Y₀ : Scheme.{u}} (x : X₀ ⟶ D.stage D.base) (y : Y₀ ⟶ D.stage D.base)
    [Smooth x] [IsProper x] [Smooth y] [IsProper y]
    {K : DerivedCategory (pullback (pullback.snd x (D.projection D.base))
      (pullback.snd y (D.projection D.base))).Modules}
    {K' : DerivedCategory (pullback (pullback.snd y (D.projection D.base))
      (pullback.snd x (D.projection D.base))).Modules}
    (i : I) (hi : D.base ≤ i)
    (Ki : DerivedCategory (pullback (pullback.snd x (D.transition hi))
      (pullback.snd y (D.transition hi))).Modules)
    (Ki' : DerivedCategory (pullback (pullback.snd y (D.transition hi))
      (pullback.snd x (D.transition hi))).Modules)
    (hKi : IsPerfect (X := (pullback (pullback.snd x (D.transition hi))
      (pullback.snd y (D.transition hi))).toRingedSpace) Ki)
    (hKi' : IsPerfect (X := (pullback (pullback.snd y (D.transition hi))
      (pullback.snd x (D.transition hi))).toRingedSpace) Ki')
    (eKi : Nonempty ((derivedPullback (baseChangeProduct x y
      (D.projection_comp_transition hi)).toLRSHom.toShHom).obj Ki ≅ K))
    (eKi' : Nonempty ((derivedPullback (baseChangeProduct y x
      (D.projection_comp_transition hi)).toLRSHom.toShHom).obj Ki' ≅ K'))
    (e₁ : Nonempty (diagonalKernel (pullback.snd x (D.projection D.base)) ≅
      fourierMukaiConvolution (pullback.snd x (D.projection D.base))
        (pullback.snd y (D.projection D.base)) (pullback.snd x (D.projection D.base)) K K'))
    (e₂ : Nonempty (diagonalKernel (pullback.snd y (D.projection D.base)) ≅
      fourierMukaiConvolution (pullback.snd y (D.projection D.base))
        (pullback.snd x (D.projection D.base)) (pullback.snd y (D.projection D.base)) K' K)) :
    ∃ (j : I) (hj : D.base ≤ j) (Kj : DerivedCategory (pullback
      (pullback.snd x (D.transition hj)) (pullback.snd y (D.transition hj))).Modules),
      IsRelativeEquivalenceKernel (pullback.snd x (D.transition hj))
        (pullback.snd y (D.transition hj)) Kj := by
  obtain ⟨eKi⟩ := eKi
  obtain ⟨eKi'⟩ := eKi'
  obtain ⟨e₁⟩ := e₁
  obtain ⟨e₂⟩ := e₂
  obtain ⟨j, hij, g₁⟩ := exists_stage_diagonal_iso_of_isNoetherian D h09RFiso hN hperf
    x y i hi Ki Ki' hKi hKi' ⟨e₁ ≪≫ fourierMukaiConvolutionMapIso _ _ _ eKi.symm eKi'.symm⟩
  have hLj := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (baseChangeProduct x y (D.transition_comp_transition hi hij)).toLRSHom.toShHom Ki hKi
  have hLj' := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (baseChangeProduct y x (D.transition_comp_transition hi hij)).toLRSHom.toShHom Ki' hKi'
  obtain ⟨a⟩ := nonempty_limitPullback_iso_transition D x y hi hij Ki ⟨eKi⟩
  obtain ⟨b⟩ := nonempty_limitPullback_iso_transition D y x hi hij Ki' ⟨eKi'⟩
  obtain ⟨k, hjk, g₂⟩ := exists_stage_diagonal_iso_of_isNoetherian D h09RFiso hN hperf
    y x j (hi.trans hij)
    ((derivedPullback (baseChangeProduct y x
      (D.transition_comp_transition hi hij)).toLRSHom.toShHom).obj Ki')
    ((derivedPullback (baseChangeProduct x y
      (D.transition_comp_transition hi hij)).toLRSHom.toShHom).obj Ki)
    hLj' hLj ⟨e₂ ≪≫ fourierMukaiConvolutionMapIso _ _ _ b.symm a.symm⟩
  obtain ⟨g₁⟩ := g₁
  refine ⟨k, (hi.trans hij).trans hjk, _,
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback.{u} _ _ hLj, _,
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback.{u} _ _ hLj', ?_, g₂⟩
  exact nonempty_diagonal_iso_of_pullback_iso diagonalKernelAndConvolutionBaseChange x y
    (D.transition_comp_transition (hi.trans hij) hjk) _ _ hLj hLj'
    ⟨(derivedPullback (baseChangeProduct x x
      (D.transition_comp_transition (hi.trans hij) hjk)).toLRSHom.toShHom).mapIso g₁⟩

/-- **[Stacks, Tag 0G0L] over Noetherian stages, with its base-change and perfectness inputs
proved.** As `AlgebraicGeometry.exists_isRelativeEquivalenceKernel_of_descentSituation`, for a
situation all of whose stages are Noetherian; the base-change input of that theorem is
`AlgebraicGeometry.diagonalKernelAndConvolutionBaseChange` and its perfectness input, at
Noetherian stages, `AlgebraicGeometry.diagonalKernelAndConvolutionPerfectOfNoetherian`. -/
theorem exists_isRelativeEquivalenceKernel_of_descentSituation_of_isNoetherian
    (h09RFobj : PerfectDescendsAlongBaseChangedTower.{v, u})
    (h09RFiso : PerfectIsoDescendsAlongBaseChangedTower.{v, u})
    (hN : ∀ i : I, IsNoetherian (D.stage i))
    (hperf : DiagonalKernelAndConvolutionPerfectOfNoetherian.{u})
    {X₀ Y₀ : Scheme.{u}} (x : X₀ ⟶ D.stage D.base) (y : Y₀ ⟶ D.stage D.base)
    [Smooth x] [IsProper x] [Smooth y] [IsProper y]
    {K : DerivedCategory (pullback (pullback.snd x (D.projection D.base))
      (pullback.snd y (D.projection D.base))).Modules}
    (hK : IsRelativeEquivalenceKernel (pullback.snd x (D.projection D.base))
      (pullback.snd y (D.projection D.base)) K) :
    ∃ (i : I) (hi : D.base ≤ i) (Ki : DerivedCategory (pullback
      (pullback.snd x (D.transition hi)) (pullback.snd y (D.transition hi))).Modules),
      IsRelativeEquivalenceKernel (pullback.snd x (D.transition hi))
        (pullback.snd y (D.transition hi)) Ki := by
  obtain ⟨hKp, K', hK'p, e₁, e₂⟩ := hK
  obtain ⟨i₁, hi₁, K₁, hK₁p, eK₁⟩ := h09RFobj D x y inferInstance inferInstance inferInstance
    inferInstance K hKp
  obtain ⟨i₂, hi₂, K₂, hK₂p, eK₂⟩ := h09RFobj D y x inferInstance inferInstance inferInstance
    inferInstance K' hK'p
  obtain ⟨i, hii₁, hii₂⟩ := directed_of (· ≤ ·) i₁ i₂
  exact exists_isRelativeEquivalenceKernel_of_stage_of_isNoetherian D h09RFiso hN hperf
    x y i (hi₁.trans hii₁)
    ((derivedPullback (baseChangeProduct x y
      (D.transition_comp_transition hi₁ hii₁)).toLRSHom.toShHom).obj K₁)
    ((derivedPullback (baseChangeProduct y x
      (D.transition_comp_transition hi₂ hii₂)).toLRSHom.toShHom).obj K₂)
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ K₁ hK₁p)
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ K₂ hK₂p)
    (nonempty_limitPullback_iso_transition D x y hi₁ hii₁ K₁ eK₁)
    (nonempty_limitPullback_iso_transition D y x hi₂ hii₂ K₂ eK₂) e₁ e₂

end Main

end AlgebraicGeometry

end
