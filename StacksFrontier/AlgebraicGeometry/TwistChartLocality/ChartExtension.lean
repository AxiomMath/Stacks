module

public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma

/-!
# The coefficient extension of the chart comparison, for gradings by any subgroup class

For a homomorphism `ψ : 𝒜 →+*ᵍ ℬ` of nonnegatively graded rings and `f` homogeneous of positive
degree, the affine invertibility criterion
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_of_isIso_extension` consumes the
extension of scalars `ℬ₍ψ f₎ ⊗_{𝒜₍f₎} 𝒜(n)₍f₎ ⟶ ℬ(n)₍ψ f₎` of the algebraic chart comparison.
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartGamma.lean` names it for gradings by
submodules of an algebra; this file names it for gradings by any additive-subgroup class and runs
the chart-transpose argument of
`StacksFrontier/AlgebraicGeometry/Blowup/ProjBaseChangeTwist.lean` in that generality.

## Main definitions

* `twistDegreeZeroChartExtension`: the extension of scalars of the algebraic chart comparison.

## Main results

* `isIso_transpose_chartAdjointTwistMap_of_isIso_chartExtension`: the chart transpose of
  Tag 01MY's comparison map is invertible as soon as the extension is.
* `isIso_pullback_awayι_map_twistMap_of_isIso_chartExtension`: the same for the chart inverse
  image of the comparison map.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum HomogeneousIdeal HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open AlgebraicGeometry.Scheme.Modules
open Stacks.GradedLocalization
open scoped ChangeOfRings TensorProduct

namespace Stacks.AlgebraicGeometry.TwistChartLocality

universe u

section ChartExtension

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ) {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) (n : ℤ)

/-! ### The algebraic chart comparison and its coefficient extension -/

/-- **The extension of scalars of the algebraic chart comparison**, for gradings by any
additive-subgroup class: the morphism of `ModuleCat (ℬ₍ψ f₎)` out of `ℬ₍ψ f₎ ⊗_{𝒜₍f₎} 𝒜(n)₍f₎`
that the affine invertibility criterion consumes.

It is the inverse adjoint transpose of the algebraic chart comparison read as a semilinear map
(a morphism into the restriction of scalars of its target along the chart ring homomorphism),
written out as the extension of scalars of that map followed by the counit rather than through
`CategoryTheory.Equiv.symm`: in that form its value on a pure tensor is `ModuleCat.map_tmul`,
which is a reflexivity, followed by
`ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul`. -/
public def twistDegreeZeroChartExtension :
    (ModuleCat.extendScalars (Away.map ψ f)).obj
        (ModuleCat.of (Away 𝒜 f)
          (GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) f)) ⟶
      ModuleCat.of (Away ℬ (ψ f))
        (GradedModuleDegreeZeroLocalization ℬ (twistGrading (S := B) ℬ n) (ψ f)) :=
  (ModuleCat.extendScalars (Away.map ψ f)).map
      (ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (Away.map ψ f)).obj
          (ModuleCat.of (Away ℬ (ψ f))
            (GradedModuleDegreeZeroLocalization ℬ (twistGrading (S := B) ℬ n) (ψ f))))
        { toFun := twistDegreeZeroMap 𝒜 ℬ ψ f n
          map_add' := fun a b => map_add (twistDegreeZeroMap 𝒜 ℬ ψ f n) a b
          map_smul' := twistDegreeZeroMap_smul 𝒜 ℬ ψ f n }) ≫
    (ModuleCat.extendRestrictScalarsAdj (Away.map ψ f)).counit.app
      (ModuleCat.of (Away ℬ (ψ f))
        (GradedModuleDegreeZeroLocalization ℬ (twistGrading (S := B) ℬ n) (ψ f)))

/-- **The extension of scalars of the chart comparison, on a pure tensor.** -/
public theorem twistDegreeZeroChartExtension_tmul
    (z : GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) f) :
    twistDegreeZeroChartExtension 𝒜 ℬ ψ n
        ((1 : Away ℬ (ψ f)) ⊗ₜ[Away 𝒜 f, Away.map ψ f] z) =
      twistDegreeZeroMap 𝒜 ℬ ψ f n z := by
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  exact ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul (f := Away.map ψ f)
    (ModuleCat.of (Away ℬ (ψ f))
      (GradedModuleDegreeZeroLocalization ℬ (twistGrading (S := B) ℬ n) (ψ f)))
    (twistDegreeZeroMap 𝒜 ℬ ψ f n z)

/-- **The chart transpose of Tag 01MY's comparison map is invertible as soon as the coefficient
extension of the algebraic chart comparison is**, for gradings by any additive-subgroup class and
at a homogeneous element of any positive degree.

This is `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_chartAdjointTwistMap` with
the degree-one hypothesis traded for the invertibility of
`Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroChartExtension`, which in degree one is
supplied by rank-one freeness of the two chart modules and in general is not. Everything else in
the chain is already stated at an arbitrary positive degree: the quasi-coherence of the two
chart inverse images, the chart identification
`Stacks.AlgebraicGeometry.TwistChartLocality.chartΓIso` and the Γ bridge
`Stacks.AlgebraicGeometry.TwistChartLocality.chartΓIso_moduleSpecΓ_chartAdjointTwistMap`. -/
public theorem isIso_transpose_chartAdjointTwistMap_of_isIso_chartExtension
    (hext : IsIso (twistDegreeZeroChartExtension 𝒜 ℬ ψ (f := f) n)) :
    IsIso (transpose (CommRingCat.ofHom (Away.map ψ f))
      ((pullback (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).obj (twistingSheaf 𝒜 n))
      ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).obj
        (twistingSheaf ℬ n))
      (chartAdjointTwistMap 𝒜 ℬ ψ hψ hd hf n)) := by
  have := isQuasicoherent_pullback_awayι_twistingSheaf 𝒜 hd hf n
  have := isQuasicoherent_pullback_awayι_twistingSheaf ℬ hd (ψ.map_mem hf) n
  have := hext
  have hinv : ∀ v, (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).inv
      ((chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).hom v) = v := by
    intro v
    have h := ConcreteCategory.congr_hom
      (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).hom_inv_id v
    rwa [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h
  refine isIso_transpose_of_isIso_extension _ _ _ _
    ((ModuleCat.extendScalars (Away.map ψ f)).map
        (chartΓIso 𝒜 (twistGrading (S := A) 𝒜 n) hf hd).hom ≫
      twistDegreeZeroChartExtension 𝒜 ℬ ψ n ≫
      (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).inv) ?_
  intro m
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom
      (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).inv)
    (twistDegreeZeroChartExtension_tmul 𝒜 ℬ ψ n _)) ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom
      (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).inv)
    (chartΓIso_moduleSpecΓ_chartAdjointTwistMap 𝒜 ℬ ψ hψ hd hf n m).symm) ?_
  exact hinv _

/-- **The chart inverse image of Tag 01MY's comparison map is invertible as soon as the
coefficient extension of the algebraic chart comparison is**, at a homogeneous element of any
positive degree. -/
public theorem isIso_pullback_awayι_map_twistMap_of_isIso_chartExtension
    (hext : IsIso (twistDegreeZeroChartExtension 𝒜 ℬ ψ (f := f) n)) :
    IsIso ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).map
      (Stacks.ProjTwistComparison.twistMap ψ hψ n)) :=
  (isIso_pullback_awayι_map_twistMap_iff 𝒜 ℬ ψ hψ hd hf n).mpr
    (isIso_transpose_chartAdjointTwistMap_of_isIso_chartExtension 𝒜 ℬ ψ hψ hd hf n hext)

end ChartExtension

end Stacks.AlgebraicGeometry.TwistChartLocality

end
