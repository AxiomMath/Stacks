module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCriteria

/-!
# Finiteness of the sections of a direct image along a finite morphism

Let `f : X ⟶ Y` be a finite morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, let `𝓕` be a coherent `𝒪_X`-module on the small étale site of `X`, and let `A` be
an étale scheme chart of `Y` whose underlying scheme is affine. The sections `(f_*𝓕)(A)` form a
finite module over the ring `𝒪_Y(A)` of regular functions on that chart. This is the étale-site
form of [Stacks, Tag 01Y6].

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChangeChartRingHom`: the ring homomorphism
  `𝒪_Y(A) ⟶ 𝒪_X(A ×_Y X)` given by pullback of regular functions along the cartesian
  projection.

## Main results

* `Stacks.Module.finite_of_tower`: finiteness of a module passes down a module-finite ring
  extension, for two actions compatible through the structure map.
* `AlgebraicGeometry.Space.finite_smallBaseChangeChartRingHom`: for a finite `f` and an affine
  chart `A` of `Y`, the chart-level structure map `𝒪_Y(A) ⟶ 𝒪_X(A ×_Y X)` is module-finite.
* `AlgebraicGeometry.Space.moduleFinite_sections_modulePushforward_of_isFinite`: the sections
  of `f_*𝓕` over an affine étale chart of `Y` form a finite module over the functions on that
  chart.

## References

* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.Module

/-- Finiteness of a module passes down a module-finite ring extension: if the action of `R` on
`N` is the action of `A` read through the structure map of a module-finite `R`-algebra `A`, then
`N` is a finite `R`-module as soon as it is a finite `A`-module. -/
theorem finite_of_tower {R A N : Type*} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N]
    (hsmul : ∀ (r : R) (n : N), r • n = algebraMap R A r • n)
    (hRA : Module.Finite R A) (hAN : Module.Finite A N) : Module.Finite R N := by
  have : IsScalarTower R A N :=
    ⟨fun r a n => by rw [Algebra.smul_def, mul_smul, hsmul]⟩
  exact Module.Finite.trans A N

end Stacks.Module

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- The structure map of small-chart base change on sections over an étale chart `A` of `Y`:
the ring homomorphism `𝒪_Y(A) ⟶ 𝒪_X(A ×_Y X)` given by pullback of regular functions along
the cartesian projection. -/
noncomputable abbrev smallBaseChangeChartRingHom (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (A : SmallEtale B S hS Y.1) :
    chartRing B S hS Y.1 Y.2 A →+*
      chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj A) :=
  ((smallBaseChangeSharp B S hS f hrep).hom.app (op A)).hom

/-- The chart-level structure map is pullback of regular functions along the cartesian
projection of the representing square. -/
theorem smallBaseChangeChartRingHom_eq (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (A : SmallEtale B S hS Y.1) :
    smallBaseChangeChartRingHom B S hS f hrep A =
      ((BigFppfOver.toScheme B S hS).map (hrep.snd A.1.hom)).appTop.hom := by
  rw [← Scheme.Γ_map_op]
  rfl

/-- The chart-level structure map of a finite morphism is module-finite: for a finite morphism
`f : X ⟶ Y` of algebraic spaces and an étale chart `A` of `Y` whose underlying scheme is affine,
the ring `𝒪_X(A ×_Y X)` is a finite `𝒪_Y(A)`-module. -/
theorem finite_smallBaseChangeChartRingHom (f : X ⟶ Y) (hf : IsFinite B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom) (A : SmallEtale B S hS Y.1)
    (hA : IsAffine (chartScheme A)) :
    (smallBaseChangeChartRingHom B S hS f hrep A).Finite := by
  have : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (hrep.snd A.1.hom)) :=
    (presheaf_isFinite_of_isFinite f.hom hrep hf).property A.1.hom (hrep.fst A.1.hom)
      (hrep.snd A.1.hom) (hrep.isPullback A.1.hom)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj A.obj.left) := hA
  rw [smallBaseChangeChartRingHom_eq]
  exact Scheme.Hom.finite_appTop ((BigFppfOver.toScheme B S hS).map (hrep.snd A.1.hom))

/-- Let `f : X ⟶ Y` be a finite morphism of algebraic spaces over `S`, let `𝓕` be a coherent
`𝒪_X`-module and let `A` be an étale scheme chart of `Y` with affine underlying scheme. Then
`(f_*𝓕)(A)` is a finite `𝒪_Y(A)`-module. -/
theorem moduleFinite_sections_modulePushforward_of_isFinite (f : X ⟶ Y)
    (hf : IsFinite B S hS f.hom) (hrep : yoneda.relativelyRepresentable f.hom)
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCoherent B S hS X.1 X.2 G)
    (A : SmallEtale B S hS Y.1) (hA : IsAffine (chartScheme A)) :
    Module.Finite (chartRing B S hS Y.1 Y.2 A)
      (((modulePushforward B S hS f).obj G).val.obj (op A)) := by
  let : Algebra (chartRing B S hS Y.1 Y.2 A)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj A)) :=
    (smallBaseChangeChartRingHom B S hS f hrep A).toAlgebra
  refine Stacks.SheafOfModules.moduleFinite_sections_of_iso
    ((modulePushforwardChartIso B S hS f hrep).app G) A ?_
  refine @Stacks.Module.finite_of_tower (chartRing B S hS Y.1 Y.2 A)
    (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj A)) _ _ _ _ _ _
    (G.val.obj (op ((smallBaseChange B S hS f hrep).obj A))).isModule (fun _ _ => rfl) ?_ ?_
  · exact finite_smallBaseChangeChartRingHom B S hS f hf hrep A hA
  · exact moduleFinite_sections_of_isCoherent B S hS X.1 X.2 G hG
      (isAffine_smallBaseChange_obj B S hS f hrep hf.isAffineHom A hA)

end AlgebraicGeometry.Space

end
