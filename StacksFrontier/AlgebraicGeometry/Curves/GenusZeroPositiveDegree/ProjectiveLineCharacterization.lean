module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.DegreeOneFromPoints
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.ProjectiveEmbedding
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.ProjectiveLineProperties
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Regular
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.FreePresentation
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeDivisibility
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# The characterization of the projective line

[Stacks, Tag 0C6U] lists eight equivalent conditions on a proper curve `X` over a field `k`, the
first being `X ≅ 𝐏¹_k`. This file proves the implications among the conditions that reduce each
of them to "`H⁰(X, 𝒪_X) = k`, genus `0`, and an invertible module of degree `1`", together with
the step from that condition to `X ≅ 𝐏¹_k`.

## Main results

* `AlgebraicGeometry.geometricallyIntegral_and_isGorenstein_of_smooth`: a smooth geometrically
  irreducible scheme over `k` is geometrically integral and Gorenstein.
* `AlgebraicGeometry.isIso_globalSections_of_invertibleCurveDegree_eq_one`: on a proper curve an
  invertible module of degree `1` forces `H⁰(X, 𝒪_X) = k`.
* `AlgebraicGeometry.exists_invertibleCurveDegree_eq_one_of_odd`: degrees of invertible modules
  form a subgroup of `ℤ`, so an odd degree together with degree `-2` gives degree `1`.

## References

* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
* [Stacks Project, Tag 0C6P](https://stacks.math.columbia.edu/tag/0C6P)
* [Stacks Project, Tag 04L2](https://stacks.math.columbia.edu/tag/04L2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Invertible (tensorPowerModule)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **A smooth geometrically irreducible scheme over a field is geometrically integral and
Gorenstein.** Smoothness gives geometric reducedness ([Stacks, Tag 056T]) and regularity
([Stacks, Tag 056S]), and a regular scheme is Gorenstein ([Stacks, Tag 0DWG]). -/
theorem geometricallyIntegral_and_isGorenstein_of_smooth [Smooth f] [GeometricallyIrreducible f] :
    GeometricallyIntegral f ∧ IsGorenstein X := by
  have : GeometricallyReduced f := geometricallyReduced_of_smooth f
  exact ⟨GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f,
    isGorenstein_of_isRegular X (isRegular_of_smooth_over_field f)⟩

/-- **`H⁰(X, 𝒪_X) = k` when the global functions are one-dimensional over `k`.** The structure
map `k → Γ(X, 𝒪_X)` is an injective `k`-linear map between one-dimensional spaces. -/
theorem isIso_globalSections_of_finrank_eq_one
    (h : letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
      Module.finrank k Γ(X, ⊤) = 1) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have : Nontrivial Γ(X, ⊤) := Module.nontrivial_of_finrank_pos (R := k) (by rw [h]; norm_num)
  have hinj : Function.Injective (Algebra.linearMap k Γ(X, ⊤)) :=
    (algebraMap k Γ(X, ⊤)).injective
  have : Module.Finite k Γ(X, ⊤) := Module.finite_of_finrank_eq_succ h
  have hsurj : Function.Surjective (Algebra.linearMap k Γ(X, ⊤)) := by
    have hrange : LinearMap.range (Algebra.linearMap k Γ(X, ⊤)) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_self, h]
    exact LinearMap.range_eq_top.mp hrange
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩

/-- **An invertible module of degree `1` on a proper curve forces `H⁰(X, 𝒪_X) = k`.** The degree
of the field extension `Γ(X, 𝒪_X)/k` divides every degree ([Stacks, Tag 0C6P]), hence divides
`1`. -/
theorem isIso_globalSections_of_invertibleCurveDegree_eq_one [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : invertibleCurveDegree k f hdim L = 1) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    Stacks.ProjectiveFromSections.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule L
  have hdvd := finrank_globalSections_dvd_curveDegree k f hdim L 1
  rw [← invertibleCurveDegree_eq_curveDegree, hdeg] at hdvd
  refine isIso_globalSections_of_finrank_eq_one f ?_
  exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hdvd

/-- **The genus is zero when `H¹(X, 𝒪_X)` vanishes.** -/
theorem genus_eq_zero_of_isZero
    (h : IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1)) :
    genus f = 0 := by
  rw [← finrank_cohomologyOverField_one_unit_eq_genus k f]
  have := ModuleCat.subsingleton_of_isZero h
  exact Module.finrank_zero_of_subsingleton

/-- **An odd degree and degree `-2` give degree `1`.** On a proper curve with invertible modules
of odd degree and of degree `-2`, there is an invertible module of degree `1`: the degrees form a
subgroup of `ℤ` (`AlgebraicGeometry.invertibleCurveDegreeSubgroup`). -/
theorem exists_invertibleCurveDegree_eq_one_of_odd [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hodd : Odd (invertibleCurveDegree k f hdim L)) (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (hN : invertibleCurveDegree k f hdim N = -2) :
    ∃ (M : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M),
      invertibleCurveDegree k f hdim M = 1 := by
  obtain ⟨m, hm⟩ := hodd
  have hL : invertibleCurveDegree k f hdim L ∈ invertibleCurveDegreeSubgroup f hdim := ⟨L, ‹_›, rfl⟩
  have hN' : (-2 : ℤ) ∈ invertibleCurveDegreeSubgroup f hdim := ⟨N, ‹_›, hN⟩
  have h1 : (1 : ℤ) ∈ invertibleCurveDegreeSubgroup f hdim := by
    have := (invertibleCurveDegreeSubgroup f hdim).add_mem hL
      ((invertibleCurveDegreeSubgroup f hdim).zsmul_mem hN' m)
    convert this using 1
    rw [hm, smul_eq_mul]
    ring
  exact h1

end AlgebraicGeometry

end
