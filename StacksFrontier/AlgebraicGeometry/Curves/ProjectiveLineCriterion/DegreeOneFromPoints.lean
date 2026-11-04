module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.CurveFiniteMorphism.Basic
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusZeroVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.DegreeOneFromPoints
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ExceptionalComponentsMeet
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.IntegralSupport
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegreeHom
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.FreePresentation
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeDivisibility
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree

/-!
# An invertible module of degree one from normal closed points of coprime degrees

Let `X` be a proper curve over a field `k`. This file proves the steps "(8) ⟹ (7)" and
"(7) ⟹ (6)" of the proof of [Stacks, Tag 0C6U].

* If `x₁, …, xₙ` are closed points of `X` with normal local rings and
  `gcd [κ(xᵢ) : k] = 1`, then `X` has an invertible module of degree `1`. A closed point with
  normal local ring is an effective Cartier divisor ([Stacks, Tag 0B8Y]); the canonical section
  of `𝒪_X(xᵢ)` is regular with zero scheme the reduced point, so `deg 𝒪_X(xᵢ) = [κ(xᵢ) : k]`;
  and the degrees of invertible modules are the image of the degree homomorphism
  `Pic(X) → ℤ`, a subgroup of `ℤ`, which therefore contains the gcd `1`.
* Under the same hypothesis `H⁰(X, 𝒪_X) = k`: `κ = H⁰(X, 𝒪_X)` is a field finite over `k`
  ([Stacks, Tag 04L2]) contained in every `κ(xᵢ)`, so `[κ : k]` divides the gcd.
* An invertible module of degree `1` also forces `H⁰(X, 𝒪_X) = k`: `[κ : k]` divides every
  degree ([Stacks, Tag 0C6P]).
* An odd degree together with degree `-2` gives degree `1` (the numerical step of
  "(4) ⟹ (6)").
* For `X` proper over `k`, `genus X = 0` exactly when `H¹(X, 𝒪_X) = 0`.

## Main results

* `AlgebraicGeometry.ProjectiveLineCriterion.exists_invertibleCurveDegree_eq_one_of_gcd`
* `AlgebraicGeometry.ProjectiveLineCriterion.isIso_globalSections_of_gcd`
* `AlgebraicGeometry.ProjectiveLineCriterion.isIso_globalSections_of_invertibleCurveDegree_eq_one`
* `AlgebraicGeometry.ProjectiveLineCriterion.exists_invertibleCurveDegree_eq_one_of_odd`
* `AlgebraicGeometry.ProjectiveLineCriterion.genus_eq_zero_iff_isZero`

## References

* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 0C6P](https://stacks.math.columbia.edu/tag/0C6P)
* [Stacks Project, Tag 04L2](https://stacks.math.columbia.edu/tag/04L2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.ProjectiveLineCriterion

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **`H⁰(X, 𝒪_X) = k` from the global sections having dimension one.** -/
theorem isIso_globalSections_of_finrank_eq_one
    (h : letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
      Module.finrank k Γ(X, ⊤) = 1) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have : Nontrivial Γ(X, ⊤) := Module.nontrivial_of_finrank_pos (R := k) (by rw [h]; norm_num)
  exact Stacks.Models.isIso_constants_of_finrank_globalSections_eq_one f h

/-- If `1` is a degree of an invertible module, then some invertible module has degree `1`. -/
private theorem exists_invertibleCurveDegree_eq_one_of_one_mem_range [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (h : (1 : ℤ) ∈ (invertibleCurveDegreeHom k f hdim).range) :
    ∃ (M : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M),
      invertibleCurveDegree k f hdim M = 1 := by
  obtain ⟨c, hc⟩ := h
  exact ⟨_, (Stacks.Picard.picardRepresentative X.toRingedSpace c).property, hc⟩

section Curve

variable [IsCurve k f] [IsProper f]

/-- The degree of a closed point with normal local ring lies in the image of the degree
homomorphism `Pic(X) → ℤ`. -/
theorem finrank_residueField_mem_range_invertibleCurveDegreeHom
    (hdim : topologicalKrullDim X ≤ 1) {x : X} (hx : IsClosed ({x} : Set X))
    (hnorm : IsNormalRing (X.presheaf.stalk x)) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    (Module.finrank k (X.residueField x) : ℤ) ∈ (invertibleCurveDegreeHom k f hdim).range := by
  have hC : Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) :=
    ((isEffectiveCartierDivisor_closedPoint_tfae_of_isCurve k f hx).out 2 4).mp hnorm
  have hL := Stacks.Divisors.isInvertible_invertibleSheaf
    (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))
  refine ⟨Stacks.SheafOfModules.picardClass X.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) _ hL, ?_⟩
  exact (invertibleCurveDegreeHom_picardClass k f hdim _ hL).trans
    (AlgebraicGeometry.invertibleCurveDegree_modulesInvertibleSheaf_vanishingIdeal_singleton
      f hdim hx)

/-- **Normal closed points of coprime residue degrees give an invertible module of degree
one** (the step "(8) ⟹ (7)" of [Stacks, Tag 0C6U]). Let `X` be a proper curve over `k` and
`x₁, …, xₙ` closed points with normal local rings and `gcd [κ(xᵢ) : k] = 1`. Then some invertible
`𝒪_X`-module has degree `1`. -/
theorem exists_invertibleCurveDegree_eq_one_of_gcd (hdim : topologicalKrullDim X ≤ 1) {n : ℕ}
    (x : Fin n → X) (hx : ∀ i, IsClosed ({x i} : Set X))
    (hnorm : ∀ i, IsNormalRing (X.presheaf.stalk (x i)))
    (hgcd : Finset.univ.gcd (fun i => letI : Algebra k (X.residueField (x i)) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (x i)).hom.toAlgebra
      Module.finrank k (X.residueField (x i))) = 1) :
    ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      invertibleCurveDegree k f hdim L = 1 := by
  set d : Fin n → ℕ := fun i => let : Algebra k (X.residueField (x i)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (x i)).hom.toAlgebra
    Module.finrank k (X.residueField (x i)) with hd
  set H := (invertibleCurveDegreeHom k f hdim).range
  have hmem : ∀ i, (d i : ℤ) ∈ H := fun i =>
    finrank_residueField_mem_range_invertibleCurveDegreeHom f hdim (hx i) (hnorm i)
  -- `H = gℤ` for some `g`, and `g` divides every `dᵢ`, hence their gcd `1`
  let I : Ideal ℤ := AddSubgroup.toIntSubmodule H
  obtain ⟨g, hg⟩ := (inferInstance : I.IsPrincipal)
  have hI : ∀ z : ℤ, z ∈ I ↔ g ∣ z := fun z => by
    rw [hg, Ideal.submodule_span_eq, Ideal.mem_span_singleton]
  have hnat : g.natAbs ∣ Finset.univ.gcd d :=
    Finset.dvd_gcd fun i _ => by simpa using Int.natAbs_dvd_natAbs.mpr ((hI (d i)).mp (hmem i))
  rw [hd, hgcd, Nat.dvd_one] at hnat
  exact exists_invertibleCurveDegree_eq_one_of_one_mem_range f hdim
    ((hI 1).mpr (Int.isUnit_iff_natAbs_eq.mpr hnat).dvd)

/-- **Under condition (8) of [Stacks, Tag 0C6U], `H⁰(X, 𝒪_X) = k`.** The field
`κ = H⁰(X, 𝒪_X)`, finite over `k` ([Stacks, Tag 04L2]), is contained in every residue field
`κ(xᵢ)`, so `[κ : k]` divides `gcd [κ(xᵢ) : k] = 1`. -/
theorem isIso_globalSections_of_gcd {n : ℕ} (x : Fin n → X)
    (hgcd : Finset.univ.gcd (fun i => letI : Algebra k (X.residueField (x i)) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (x i)).hom.toAlgebra
      Module.finrank k (X.residueField (x i))) = 1) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  refine isIso_globalSections_of_finrank_eq_one f ?_
  rw [← Nat.dvd_one, ← hgcd]
  exact Finset.dvd_gcd fun i _ => finrank_globalSections_dvd_finrank_residueField k f (x i)

/-- **Under condition (7) of [Stacks, Tag 0C6U], `H⁰(X, 𝒪_X) = k`.** The degree of the field
extension `H⁰(X, 𝒪_X)/k` divides the degree of every invertible module ([Stacks, Tag 0C6P]),
hence divides `1`. -/
theorem isIso_globalSections_of_invertibleCurveDegree_eq_one
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

end Curve

/-- **An invertible module of odd degree and one of degree `-2` give one of degree `1`** (the
numerical step of "(4) ⟹ (6)" in [Stacks, Tag 0C6U], where the second module is the dualizing
module). The degrees of invertible modules on a proper scheme of dimension at most one over `k`
are the image of the degree homomorphism `Pic(X) → ℤ`, a subgroup of `ℤ`; it contains
`(2m + 1) + m · (-2) = 1`. -/
theorem exists_invertibleCurveDegree_eq_one_of_odd [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hodd : Odd (invertibleCurveDegree k f hdim L)) (N : X.Modules)
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (hNdeg : invertibleCurveDegree k f hdim N = -2) :
    ∃ (M : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M),
      invertibleCurveDegree k f hdim M = 1 := by
  obtain ⟨m, hm⟩ := hodd
  set H := (invertibleCurveDegreeHom k f hdim).range
  have hLmem : invertibleCurveDegree k f hdim L ∈ H :=
    ⟨_, invertibleCurveDegreeHom_picardClass k f hdim L hL⟩
  have hNmem : (-2 : ℤ) ∈ H := hNdeg ▸ ⟨_, invertibleCurveDegreeHom_picardClass k f hdim N hN⟩
  refine exists_invertibleCurveDegree_eq_one_of_one_mem_range f hdim ?_
  have := H.add_mem hLmem (H.zsmul_mem hNmem m)
  convert this using 1
  rw [hm, smul_eq_mul]
  ring

/-- **A proper scheme over `k` has genus `0` exactly when `H¹(X, 𝒪_X) = 0`.** The genus is the
dimension of `H¹(X, 𝒪_X)`, which is finite-dimensional ([Stacks, Tag 02O6]). -/
theorem genus_eq_zero_iff_isZero [IsProper f] :
    genus f = 0 ↔ IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) := by
  refine ⟨isZero_cohomologyOverField_unit_one_of_genus_eq_zero k f, fun h => ?_⟩
  have := ModuleCat.subsingleton_of_isZero h
  rw [genus_eq_finrank_structureSheafCohomology,
    (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq]
  exact Module.finrank_zero_of_subsingleton

end AlgebraicGeometry.ProjectiveLineCriterion

end
