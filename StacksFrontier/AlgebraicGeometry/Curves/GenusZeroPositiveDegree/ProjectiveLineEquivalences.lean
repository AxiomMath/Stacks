module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.ProjectiveLineCharacterization

/-!
# Eight characterizations of the projective line

A proper curve `X` over a field `k` is isomorphic to `𝐏¹_k` if and only if any of the conditions
of [Stacks, Tag 0C6U] holds: genus `0` together with an invertible module of degree `1` or, in the
Gorenstein case, of odd degree, under one of several hypotheses forcing `H⁰(X, 𝒪_X) = k`.

## Main results

* `AlgebraicGeometry.projectiveLine_tfae`: [Stacks, Tag 0C6U].

## References

* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
* [Stacks Project, Tag 0C19](https://stacks.math.columbia.edu/tag/0C19)
* [Stacks Project, Tag 0C6T](https://stacks.math.columbia.edu/tag/0C6T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Stacks Project, Tag 0C6U.** Let `X` be a proper curve over a field `k`. The following are
equivalent:

1. `X ≅ 𝐏¹_k` over `k`;
2. `X` is smooth and geometrically irreducible over `k`, of genus `0`, with an invertible module of
   odd degree;
3. `X` is geometrically integral over `k`, of genus `0`, Gorenstein, with an invertible module of
   odd degree;
4. `H⁰(X, 𝒪_X) = k`, `X` has genus `0`, is Gorenstein, and has an invertible module of odd
   degree;
5. `X` is geometrically integral over `k`, of genus `0`, with an invertible module of degree `1`;
6. `H⁰(X, 𝒪_X) = k`, `X` has genus `0`, and has an invertible module of degree `1`;
7. `H¹(X, 𝒪_X) = 0` and `X` has an invertible module of degree `1`;
8. `H¹(X, 𝒪_X) = 0` and `X` has closed points `x₁, …, xₙ` with normal local rings and
   `gcd [κ(xᵢ) : k] = 1`.

For `(4) ⇒ (6)`: `ω_X` is invertible of degree `2g - 2 = -2` ([Stacks, Tag 0C19]), and the degrees
of invertible modules form a subgroup of `ℤ`. -/
@[stacks 0C6U "the final item (9) of the source is the placeholder `add more here`"]
theorem projectiveLine_tfae [IsCurve k f] [IsProper f] :
    List.TFAE [
      ∃ e : X ≅ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 1),
        e.hom ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1 = f,
      Smooth f ∧ GeometricallyIrreducible f ∧ genus f = 0 ∧
        ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
          Odd (invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L),
      GeometricallyIntegral f ∧ genus f = 0 ∧ IsGorenstein X ∧
        ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
          Odd (invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L),
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ∧ genus f = 0 ∧ IsGorenstein X ∧
        ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
          Odd (invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L),
      GeometricallyIntegral f ∧ genus f = 0 ∧
        ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
          invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L = 1,
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ∧ genus f = 0 ∧
        ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
          invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L = 1,
      IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) ∧
        ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
          invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L = 1,
      IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) ∧
        ∃ (n : ℕ) (x : Fin n → X), (∀ i, IsClosed ({x i} : Set X)) ∧
          (∀ i, IsIntegrallyClosed (X.presheaf.stalk (x i))) ∧
          Finset.univ.gcd (fun i => letI : Algebra k (X.residueField (x i)) :=
              ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (x i)).hom.toAlgebra
            Module.finrank k (X.residueField (x i))) = 1] := by
  have hdim1 : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one (f := f)
  tfae_have 1 → 2 := fun ⟨e, he⟩ =>
    smooth_geometricallyIrreducible_genus_odd_of_iso_projectiveLine f e he
  tfae_have 1 → 5 := fun ⟨e, he⟩ =>
    geometricallyIntegral_genus_degree_one_of_iso_projectiveLine f e he
  tfae_have 1 → 7 := fun ⟨e, he⟩ => isZero_h1_degree_one_of_iso_projectiveLine f e he
  tfae_have 1 → 8 := fun ⟨e, he⟩ => isZero_h1_rationalNormalPoint_of_iso_projectiveLine f e he
  tfae_have 2 → 3 := by
    rintro ⟨hs, hirr, hg, hL⟩
    obtain ⟨hgi, hgor⟩ := geometricallyIntegral_and_isGorenstein_of_smooth f
    exact ⟨hgi, hg, hgor, hL⟩
  tfae_have 3 → 4 := by
    rintro ⟨hgi, hg, hgor, hL⟩
    exact ⟨isIso_globalSections_of_geometricallyIntegral k f, hg, hgor, hL⟩
  tfae_have 4 → 6 := by
    rintro ⟨hH0, hg, hgor, L, hL, hodd⟩
    let := connectedSpace_of_isIso_globalSections k f
    let := isInvertible_dualizingSheafOverField_of_connectedSpace k f hdim1
    have hω := invertibleCurveDegree_dualizingSheafOverField k f hdim1
    rw [hg] at hω
    exact ⟨hH0, hg, exists_invertibleCurveDegree_eq_one_of_odd f hdim1.le L hodd
      (Stacks.Duality.dualizingSheafOverField f) (by rw [hω]; norm_num)⟩
  tfae_have 5 → 6 := fun ⟨hgi, hg, hL⟩ =>
    ⟨isIso_globalSections_of_geometricallyIntegral k f, hg, hL⟩
  tfae_have 7 → 6 := by
    rintro ⟨h1, L, hL, hdeg⟩
    exact ⟨isIso_globalSections_of_invertibleCurveDegree_eq_one f hdim1.le L hdeg,
      genus_eq_zero_of_isZero f h1, L, hL, hdeg⟩
  tfae_have 8 → 7 := by
    rintro ⟨h1, n, x, hx, hnorm, hgcd⟩
    exact ⟨h1, exists_invertibleCurveDegree_eq_one_of_gcd f hdim1.le x hx hnorm hgcd⟩
  tfae_have 6 → 1 := by
    rintro ⟨hH0, hg, L, hL, hdeg⟩
    exact exists_iso_projectiveLine_of_invertibleCurveDegree_eq_one f hdim1 hg L hdeg
  tfae_finish

end AlgebraicGeometry

end
