module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ProjHyperplane
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistGlue.Basic

/-!
# A relative `Proj` of a graded quotient cut out by one degree-one equation

Let `ψ : A ⟶ B` be a homomorphism of quasi-coherent graded algebras on a scheme `S` that is
surjective on homogeneous sections over affine opens, so that it induces a closed immersion
`Proj_S(B) ⟶ Proj_S(A)` (`Stacks.AlgebraicGeometry.ProjBundleSurjection.map`). Suppose a global
section `s` of an invertible module `ℒ` on `Proj_S(A)` is, over the charts of a cover of `S` by
affine opens `Uᵢ`, the degree-one section attached to a generator `tᵢ` of the kernel of
`Γ(Uᵢ, A) ⟶ Γ(Uᵢ, B)`, in the sense that the zero scheme of `s` pulls back along the chart to the
zero scheme of `tᵢ`. Then the zero scheme of `s` is the closed subscheme `Proj_S(B)`, and it is an
effective Cartier divisor as soon as every `tᵢ` is a nonzerodivisor.

Both are checked chart by chart: over the chart of `Uᵢ` the inverse image of the kernel of the
induced morphism is the kernel of the chart morphism `Proj Γ(Uᵢ, B) ⟶ Proj Γ(Uᵢ, A)`, because
the chart of `B` is the inverse image of the chart of `A`
(`Stacks.AlgebraicGeometry.ProjBundleSurjection.isPullback_chart`), and on `Proj Γ(Uᵢ, A)` the
statements are `Stacks.Chow.GenuineChern.zeroScheme_degreeSection_eq_ker_projMap` and
`Stacks.Chow.GenuineChern.isEffectiveCartierDivisor_zeroScheme_degreeSection`.

## Main results

* `Stacks.Chow.GenuineChern.comap_chart_ker_map`: the kernel of the induced morphism read on a
  chart.
* `Stacks.Chow.GenuineChern.zeroScheme_eq_ker_map_of_charts`: the zero scheme of `s` is the
  kernel of the induced closed immersion.
* `Stacks.Chow.GenuineChern.isEffectiveCartierDivisor_zeroScheme_of_charts`: it is an effective
  Cartier divisor when the chart equations are nonzerodivisors.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.ProjBundleSurjection
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProjMapDomain

universe u

namespace Stacks.Chow.GenuineChern

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} {ψ : SheafGradedAlgebraHom A B}
  (hψ : SurjectiveOnAffineSections ψ)

/-- **The kernel of the induced closed immersion, read on a chart**: its inverse image along the
chart of an affine open `U` of the base is the kernel of the chart morphism
`Proj Γ(U, B) ⟶ Proj Γ(U, A)`. -/
theorem comap_chart_ker_map (U : S.Opens) (hU : IsAffineOpen U) :
    (map hψ).ker.comap ((relativeProj A).chart U hU) = (chartMap hψ U hU).ker := by
  have := isClosedImmersion_map hψ
  have h := (isPullback_chart hψ U hU).flip
  calc (map hψ).ker.comap ((relativeProj A).chart U hU)
      = (pullback.fst ((relativeProj A).chart U hU) (map hψ)).ker :=
        (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _).symm
    _ = (h.isoPullback.hom ≫ pullback.fst ((relativeProj A).chart U hU) (map hψ)).ker :=
        (Scheme.Hom.ker_comp_of_isIso _ _).symm
    _ = (chartMap hψ U hU).ker := by rw [h.isoPullback_hom_fst]

/-- The charts over a family of affine opens covering the base cover the relative `Proj`. -/
theorem iSup_opensRange_chart_eq_top {ι : Type*} (U : ι → S.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) : ⨆ i, ((relativeProj A).chart (U i) (hU i)).opensRange = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (relativeProj A).toBase x ∈ ⨆ i, U i := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  refine Opens.mem_iSup.2 ⟨i, ?_⟩
  rw [← Scheme.Hom.image_top_eq_opensRange,
    Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top (relativeProj A) (U i) (hU i)]
  exact hi

variable {ι : Type*} (U : ι → S.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
  (hgen : ∀ i, Algebra.adjoin (A.grading (U i) 0)
    (A.grading (U i) 1 : Set (A.sectionRing (U i))) = ⊤)
  (t : ∀ i, A.grading (U i) 1)
  (L : (relativeProj A).scheme.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (relativeProj A).scheme.sheaf.obj
    (relativeProj A).scheme.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (hZ : ∀ i,
    haveI := algebraicGeometry_isInvertible_twistingSheaf (A.grading (U i)) (hgen i) ((1 : ℕ) : ℤ)
    letI := Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart
      (relativeProj A) (U i) (hU i)
    (Stacks.Divisors.zeroScheme _ L s).comap ((relativeProj A).chart (U i) (hU i)) =
      Stacks.Divisors.zeroScheme (Proj (A.grading (U i)))
        (twistingSheafModule (A.grading (U i)) ((1 : ℕ) : ℤ))
        (degreeSection (A.grading (U i)) 1 (t i)))

include hcov hZ in
/-- **The zero scheme of `s` is the closed subscheme `Proj_S(B)`**: if on the chart of each
`Uᵢ` of an affine cover of the base the zero scheme of `s` is the zero scheme of the degree-one
section of a generator `tᵢ` of the kernel of `Γ(Uᵢ, A) ⟶ Γ(Uᵢ, B)`, then the zero scheme of `s`
is the kernel of the induced closed immersion. -/
theorem zeroScheme_eq_ker_map_of_charts
    (hker : ∀ i, RingHom.ker (ψ.sectionHom (U i) : A.sectionRing (U i) →+* B.sectionRing (U i)) =
      Ideal.span {(t i : A.sectionRing (U i))}) :
    Stacks.Divisors.zeroScheme _ L s = (map hψ).ker := by
  let := fun i => Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart
    (relativeProj A) (U i) (hU i)
  refine eq_of_comap_eq_of_iSup_opensRange_eq_top (fun i => (relativeProj A).chart (U i) (hU i))
    (iSup_opensRange_chart_eq_top U hU hcov) fun i => ?_
  have := algebraicGeometry_isInvertible_twistingSheaf (A.grading (U i)) (hgen i) ((1 : ℕ) : ℤ)
  refine (hZ i).trans ?_
  rw [comap_chart_ker_map hψ (U i) (hU i), chartMap_eq_map hψ (U i) (hU i)]
  exact zeroScheme_degreeSection_eq_ker_projMap (A.grading (U i)) (B.grading (U i)) (hgen i)
    (ψ.sectionHom (U i)) _ (surjective_sectionHom hψ (hU i)) (t i) (hker i)

include hcov hZ in
/-- **The zero scheme of `s` is an effective Cartier divisor** when, on the chart of each `Uᵢ` of
an affine cover of the base, it is the zero scheme of the degree-one section of a nonzerodivisor
`tᵢ`. -/
theorem isEffectiveCartierDivisor_zeroScheme_of_charts
    (ht : ∀ i, IsRegular (t i : A.sectionRing (U i))) :
    Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme _ L s) := by
  let := fun i => Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart
    (relativeProj A) (U i) (hU i)
  refine isEffectiveCartierDivisor_of_comap (fun i => (relativeProj A).chart (U i) (hU i))
    (iSup_opensRange_chart_eq_top U hU hcov) _ fun i => ?_
  have := algebraicGeometry_isInvertible_twistingSheaf (A.grading (U i)) (hgen i) ((1 : ℕ) : ℤ)
  rw [hZ i]
  exact isEffectiveCartierDivisor_zeroScheme_degreeSection (A.grading (U i)) (hgen i) (t i) (ht i)

end Stacks.Chow.GenuineChern

end
