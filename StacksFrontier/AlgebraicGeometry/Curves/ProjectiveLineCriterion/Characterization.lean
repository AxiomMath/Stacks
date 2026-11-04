module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.DegreeOneFromPoints
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.ProjectiveLineProperties
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.SectionPoint
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.SmoothGeometricallyIntegral
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections

/-!
# Characterization of the projective line

Let `k` be a field and `X` a proper curve over `k`. [Stacks, Tag 0C6U] lists eight conditions
equivalent to `X ≅ 𝐏¹_k`:

1. `X ≅ 𝐏¹_k` over `k`,
2. `X` is smooth and geometrically irreducible over `k`, of genus `0`, with an invertible module
   of odd degree,
3. `X` is geometrically integral over `k`, of genus `0`, Gorenstein, with an invertible module of
   odd degree,
4. `H⁰(X, 𝒪_X) = k`, `X` has genus `0`, is Gorenstein and has an invertible module of odd degree,
5. `X` is geometrically integral over `k`, of genus `0`, with an invertible module of degree `1`,
6. `H⁰(X, 𝒪_X) = k`, `X` has genus `0` and an invertible module of degree `1`,
7. `H¹(X, 𝒪_X) = 0` and `X` has an invertible module of degree `1`,
8. `H¹(X, 𝒪_X) = 0` and `X` has closed points `x₁, …, xₙ` with normal local rings and
   `gcd [κ(xᵢ) : k] = 1`.

This file proves their equivalence.

## Main results

* `AlgebraicGeometry.ProjectiveLineCriterion.projectiveLine_tfae`: **[Stacks, Tag 0C6U]**.
* `AlgebraicGeometry.ProjectiveLineCriterion.projectiveLine_tfae_of_degree_one`: the
  equivalence of (1), (5), (6), (7) and (8).
* `AlgebraicGeometry.ProjectiveLineCriterion.cond_two_three_four_of_iso_projectiveLine`:
  (1) implies (2), (3) and (4).
* `AlgebraicGeometry.ProjectiveLineCriterion.nonempty_iso_projectiveLine_of_section`: a smooth
  proper curve of genus `0` with `H⁰(X, 𝒪_X) = k` and a rational point is `𝐏¹_k`.

## Implementation notes

The proof is the source's: (8) gives a degree-one invertible module (the divisor
`∑ aᵢ xᵢ` with `∑ aᵢ [κ(xᵢ) : k] = 1`) and `H⁰(X, 𝒪_X) = k`; (7) gives `H⁰(X, 𝒪_X) = k` by
divisibility of degrees ([Stacks, Tag 0C6P]); (5) gives it by [Stacks, Tag 04L2]; and (6)
gives `X ≅ 𝐏¹_k` by the embedding of [Stacks, Tag 0C6T] for an invertible module of degree `1`
(`ProjectiveLineCriterion.exists_iso_projectiveLine_of_invertibleCurveDegree_eq_one`).
Conditions (2), (3) and (4) reach (6) as in the source: a smooth scheme over `k` is
Gorenstein (and smooth geometrically irreducible is geometrically integral), geometric
integrality gives `H⁰(X, 𝒪_X) = k`, and then the dualizing module has degree `2g - 2 = -2`
([Stacks, Tag 0C19],
`AlgebraicGeometry.invertibleCurveDegree_dualizingSheafOverField`), which
together with an odd degree gives degree `1`.

The dimension bound needed by the degree is the curve's own,
`le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))`.

## References

* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
* [Stacks Project, Tag 0C6T](https://stacks.math.columbia.edu/tag/0C6T)
* [Stacks Project, Tag 0C6P](https://stacks.math.columbia.edu/tag/0C6P)
* [Stacks Project, Tag 04L2](https://stacks.math.columbia.edu/tag/04L2)
* [Stacks Project, Tag 0C19](https://stacks.math.columbia.edu/tag/0C19)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveLineCriterion

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Conditions (1), (5), (6), (7) and (8) of [Stacks, Tag 0C6U] are equivalent.** For a
proper curve `X` over a field `k`: `X ≅ 𝐏¹_k` over `k`; or `X` is geometrically integral of
genus `0` with an invertible module of degree `1`; or `H⁰(X, 𝒪_X) = k`, the genus is `0` and
there is an invertible module of degree `1`; or `H¹(X, 𝒪_X) = 0` and there is an invertible
module of degree `1`; or `H¹(X, 𝒪_X) = 0` and there are closed points with normal local rings
whose residue degrees have greatest common divisor `1`. -/
theorem projectiveLine_tfae_of_degree_one [IsProper f] [IsCurve k f] :
    List.TFAE
      [Nonempty (Over.mk f ≅
          Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))),
        GeometricallyIntegral f ∧ genus f = 0 ∧
          ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
            invertibleCurveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f)))
              L = 1,
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ∧ genus f = 0 ∧
          ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
            invertibleCurveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f)))
              L = 1,
        IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) ∧
          ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
            invertibleCurveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f)))
              L = 1,
        IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) ∧
          ∃ (n : ℕ) (x : Fin n → X), (∀ i, IsClosed ({x i} : Set X)) ∧
            (∀ i, IsNormalRing (X.presheaf.stalk (x i))) ∧
            Finset.univ.gcd (fun i => letI : Algebra k (X.residueField (x i)) :=
                ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (x i)).hom.toAlgebra
              Module.finrank k (X.residueField (x i))) = 1] := by
  have hdim : topologicalKrullDim X ≤ 1 :=
    le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))
  -- positions in the list: 1 ↦ (1), 2 ↦ (5), 3 ↦ (6), 4 ↦ (7), 5 ↦ (8)
  tfae_have 1 → 2 := by
    rintro ⟨e⟩
    exact ⟨geometricallyIntegral_of_iso_projectiveLine e, genus_of_iso_projectiveLine e,
      exists_invertibleCurveDegree_eq_one_of_iso_projectiveLine e hdim⟩
  tfae_have 2 → 3 := by
    rintro ⟨hgi, hg, hL⟩
    exact ⟨isIso_globalSections_of_geometricallyIntegral k f, hg, hL⟩
  tfae_have 3 → 1 := by
    rintro ⟨hiso, hg, L, hL, hdeg⟩
    exact exists_iso_projectiveLine_of_invertibleCurveDegree_eq_one f hdim hg L hdeg
  tfae_have 1 → 4 := by
    rintro ⟨e⟩
    exact ⟨isZero_cohomologyOverField_one_of_iso_projectiveLine e,
      exists_invertibleCurveDegree_eq_one_of_iso_projectiveLine e hdim⟩
  tfae_have 4 → 3 := by
    rintro ⟨h1, L, hL, hdeg⟩
    exact ⟨isIso_globalSections_of_invertibleCurveDegree_eq_one f hdim L hdeg,
      (genus_eq_zero_iff_isZero f).mpr h1, L, hL, hdeg⟩
  tfae_have 1 → 5 := by
    rintro ⟨e⟩
    exact ⟨isZero_cohomologyOverField_one_of_iso_projectiveLine e,
      exists_normalPoints_gcd_eq_one_of_iso_projectiveLine e⟩
  tfae_have 5 → 4 := by
    rintro ⟨h1, n, x, hx, hnorm, hgcd⟩
    exact ⟨h1, exists_invertibleCurveDegree_eq_one_of_gcd f hdim x hx hnorm hgcd⟩
  tfae_finish

/-- **Condition (1) of [Stacks, Tag 0C6U] implies conditions (2), (3) and (4).** A scheme
isomorphic over `k` to `𝐏¹_k` is smooth and geometrically irreducible, geometrically integral
and Gorenstein, has `H⁰(X, 𝒪_X) = k` and genus `0`, and carries an invertible module of odd
degree. -/
theorem cond_two_three_four_of_iso_projectiveLine [IsProper f] [IsCurve k f]
    (e : Over.mk f ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))) :
    (Smooth f ∧ GeometricallyIrreducible f ∧ genus f = 0 ∧
        ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
          Odd (invertibleCurveDegree k f
            (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) L)) ∧
      (GeometricallyIntegral f ∧ genus f = 0 ∧ IsGorenstein X ∧
        ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
          Odd (invertibleCurveDegree k f
            (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) L)) ∧
      (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ∧ genus f = 0 ∧ IsGorenstein X ∧
        ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
          Odd (invertibleCurveDegree k f
            (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) L)) := by
  have hodd := exists_invertibleCurveDegree_odd_of_iso_projectiveLine e
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f)))
  exact ⟨⟨smooth_of_iso_projectiveLine e, geometricallyIrreducible_of_iso_projectiveLine e,
      genus_of_iso_projectiveLine e, hodd⟩,
    ⟨geometricallyIntegral_of_iso_projectiveLine e, genus_of_iso_projectiveLine e,
      isGorenstein_of_iso_projectiveLine e, hodd⟩,
    ⟨isIso_globalSections_of_iso_projectiveLine e, genus_of_iso_projectiveLine e,
      isGorenstein_of_iso_projectiveLine e, hodd⟩⟩

/-- **Stacks Project, Tag 0C6U (characterization of the projective line).** For a proper curve
`X` over a field `k` the following are equivalent:
1. `X ≅ 𝐏¹_k` over `k`;
2. `X` is smooth and geometrically irreducible over `k`, has genus `0`, and has an invertible
   module of odd degree;
3. `X` is geometrically integral over `k`, has genus `0`, is Gorenstein, and has an invertible
   module of odd degree;
4. `H⁰(X, 𝒪_X) = k`, `X` has genus `0`, is Gorenstein, and has an invertible module of odd degree;
5. `X` is geometrically integral over `k`, has genus `0`, and has an invertible module of degree
   `1`;
6. `H⁰(X, 𝒪_X) = k`, `X` has genus `0`, and has an invertible module of degree `1`;
7. `H¹(X, 𝒪_X) = 0` and `X` has an invertible module of degree `1`;
8. `H¹(X, 𝒪_X) = 0` and `X` has closed points `x₁, …, xₙ` with normal local rings `𝒪_{X,xᵢ}`
   and `gcd [κ(xᵢ) : k] = 1`. -/
@[stacks 0C6U]
theorem projectiveLine_tfae [IsProper f] [IsCurve k f] :
    List.TFAE
      [Nonempty (Over.mk f ≅
          Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))),
        Smooth f ∧ GeometricallyIrreducible f ∧ genus f = 0 ∧
          ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
            Odd (invertibleCurveDegree k f
              (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) L),
        GeometricallyIntegral f ∧ genus f = 0 ∧ IsGorenstein X ∧
          ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
            Odd (invertibleCurveDegree k f
              (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) L),
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ∧ genus f = 0 ∧ IsGorenstein X ∧
          ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
            Odd (invertibleCurveDegree k f
              (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) L),
        GeometricallyIntegral f ∧ genus f = 0 ∧
          ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
            invertibleCurveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f)))
              L = 1,
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ∧ genus f = 0 ∧
          ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
            invertibleCurveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f)))
              L = 1,
        IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) ∧
          ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
            invertibleCurveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f)))
              L = 1,
        IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) ∧
          ∃ (n : ℕ) (x : Fin n → X), (∀ i, IsClosed ({x i} : Set X)) ∧
            (∀ i, IsNormalRing (X.presheaf.stalk (x i))) ∧
            Finset.univ.gcd (fun i => letI : Algebra k (X.residueField (x i)) :=
                ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (x i)).hom.toAlgebra
              Module.finrank k (X.residueField (x i))) = 1] := by
  have hdim : topologicalKrullDim X ≤ 1 :=
    le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))
  have h := projectiveLine_tfae_of_degree_one k f
  tfae_have 1 → 2 := fun ⟨e⟩ => (cond_two_three_four_of_iso_projectiveLine k f e).1
  tfae_have 1 → 3 := fun ⟨e⟩ => (cond_two_three_four_of_iso_projectiveLine k f e).2.1
  tfae_have 1 → 4 := fun ⟨e⟩ => (cond_two_three_four_of_iso_projectiveLine k f e).2.2
  tfae_have 2 → 3 := by
    rintro ⟨hsm, hgi, hg, hL⟩
    obtain ⟨hint, hgor⟩ := geometricallyIntegral_and_isGorenstein_of_smooth f
    exact ⟨hint, hg, hgor, hL⟩
  tfae_have 3 → 4 := by
    rintro ⟨hgi, hg, hgor, hL⟩
    exact ⟨isIso_globalSections_of_geometricallyIntegral k f, hg, hgor, hL⟩
  tfae_have 4 → 6 := by
    rintro ⟨hiso, hg, hgor, L, hL, hodd⟩
    have hdim1 : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one (f := f)
    have := connectedSpace_of_isIso_globalSections k f
    have := isInvertible_dualizingSheafOverField_of_connectedSpace k f hdim1
    have hω : invertibleCurveDegree k f hdim (Stacks.Duality.dualizingSheafOverField f) = -2 := by
      have := AlgebraicGeometry.invertibleCurveDegree_dualizingSheafOverField k f hdim1
      rw [hg] at this
      simpa using this
    exact ⟨hiso, hg, exists_invertibleCurveDegree_eq_one_of_odd f hdim L hodd _ hω⟩
  tfae_have 1 ↔ 5 := h.out 1 2 rfl rfl
  tfae_have 1 ↔ 6 := h.out 1 3 rfl rfl
  tfae_have 1 ↔ 7 := h.out 1 4 rfl rfl
  tfae_have 1 ↔ 8 := h.out 1 5 rfl rfl
  tfae_finish

/-- **A smooth proper curve of genus zero with `H⁰(X, 𝒪_X) = k` and a rational point is the
projective line.** The rational point is a closed point with a normal local ring and residue
degree `1`, which is condition (8) of [Stacks, Tag 0C6U]. -/
theorem nonempty_iso_projectiveLine_of_section [IsProper f] [IsCurve k f] [Smooth f]
    (hgenus : genus f = 0) (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    Nonempty (Over.mk f ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))) :=
  ((projectiveLine_tfae_of_degree_one k f).out 5 1 rfl rfl).mp
    ⟨(genus_eq_zero_iff_isZero f).mp hgenus, exists_normalPoints_gcd_eq_one_of_section f s hs⟩

end AlgebraicGeometry.ProjectiveLineCriterion

end
