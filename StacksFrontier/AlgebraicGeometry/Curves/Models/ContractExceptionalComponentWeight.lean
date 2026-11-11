module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractExceptionalComponentGenus
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractExceptionalComponentIntersection
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormulaSpecialFiber
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Contraction

/-!
# The numerical type after contracting an exceptional curve

In the situation of [Stacks, Tag 0C61] let `f : X ⟶ X'` contract an irreducible component `C_n`
of the special fibre, and let `C'_i = f(C_i)` for `i < n` be the components of the special fibre
of the contracted model. Write `wᵢ = [κᵢ : k]` and `w'ᵢ = [κ'ᵢ : k]` for the weights. The maps
`κᵢ ← κ'ᵢ → κₙ` of [Stacks, Tag 0C6C] (2) show that `w'ᵢ` divides `wᵢ`, and divides `wₙ` when
`Cᵢ` meets `Cₙ`. Together with [Stacks, Tag 0C6C] (1) and [Stacks, Tag 0CA8] this gives the
geometric half of [Stacks, Tag 0CA9]: when `Cₙ` is an exceptional curve of the first kind, the
numerical type associated to `X'` is the contraction of Tag 0C77 of the numerical type associated
to `X`, except that its weights `w'ᵢ` are divisors of `wᵢ`. The full comparison of Tag 0CA9 is
`associatedNumericalType_contraction_comparison` in
`StacksFrontier.AlgebraicGeometry.Curves.Models.ContractExceptionalComponentNumericalType`.

## Main results

* `Stacks.Models.RegularProperModelSituation.contractedComponentWeight_dvd` — `w'ᵢ ∣ wᵢ`.
* `Stacks.Models.RegularProperModelSituation.contractedComponentWeight_dvd_of_inter_nonempty` —
  `w'ᵢ ∣ wₙ` when `Cᵢ ∩ Cₙ ≠ ∅`.
* `Stacks.Models.RegularProperModelSituation.contractedComponentWeight_eq_of_inter_eq_empty` —
  `w'ᵢ = wᵢ` when `Cᵢ ∩ Cₙ = ∅`.
* `Stacks.Models.RegularProperModelSituation.isContractionUpToWeight_associatedNumericalType` —
  the numerical type of `X'` is a contraction up to weight of that of `X`.

## References

* [Stacks Project, Tag 0CA9](https://stacks.math.columbia.edu/tag/0CA9)
* [Stacks Project, Tag 0C6C](https://stacks.math.columbia.edu/tag/0C6C)
* [Stacks Project, Tag 0CA8](https://stacks.math.columbia.edu/tag/0CA8)
* [Stacks Project, Tag 0C77](https://stacks.math.columbia.edu/tag/0C77)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u}) {N : irreducibleComponents S.specialFiber}
  {X' : Scheme.{u}} {f : S.X ⟶ X'}

/-- **The weight of a contracted component divides the old weight**: `C_i ⟶ C'_i` is a morphism
over `k`, so `κ'ᵢ ⟶ κᵢ` makes `κᵢ` a vector space over `κ'ᵢ` and `w'ᵢ ∣ wᵢ`. -/
public theorem contractedComponentWeight_dvd
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    (S.contractedSituation hf).specialFiberComponentWeight (S.contractedComponentEquiv hf Z) ∣
      S.specialFiberComponentWeight Z.1 :=
  S.finrank_dvd_specialFiberComponentWeight Z.1 _ (S.contractedComponentMap hf Z)
    (S.contractedComponentMap_specialFiberComponentToSpec hf Z)
    ((S.contractedSituation hf).isField_and_finite_globalSections_specialFiberComponent _).1

/-- **The weight of a contracted component meeting `C_n` divides the weight of `C_n`**: the
contraction carries `C_n` to a point of `C'_i`, which gives a morphism `C_n ⟶ C'_i` over `k`. -/
public theorem contractedComponentWeight_dvd_of_inter_nonempty
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N})
    (hmeet : ((Z.1.1 : Set S.specialFiber) ∩ N.1).Nonempty) :
    (S.contractedSituation hf).specialFiberComponentWeight (S.contractedComponentEquiv hf Z) ∣
      S.specialFiberComponentWeight N := by
  obtain ⟨-, -, -, h, -, hh, -, -⟩ := S.exists_contractedComponentMap hf Z hmeet
  refine S.finrank_dvd_specialFiberComponentWeight N _ h ?_
    ((S.contractedSituation hf).isField_and_finite_globalSections_specialFiberComponent _).1
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) :=
    IsClosedImmersion.spec_of_surjective _ S.surjective_algebraMap_residueField
  refine (cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))).mp ?_
  rw [Category.assoc, (S.contractedSituation hf).specialFiberComponentToSpec_comp,
    ← Category.assoc, hh, Category.assoc, S.specialFiberComponentToSpec_comp]
  exact congrArg _ (S.contraction_comp_contractionToBase hf)

/-- The weight of a component is computed on any closed subscheme of `X_k` with the same ideal. -/
theorem finrank_globalSections_fibreSubscheme_eq_weight {I : S.X.IdealSheafData}
    (hI : S.specialFiberIdeal ≤ I) (Z : irreducibleComponents S.specialFiber)
    (h : I = S.specialFiberComponentIdeal Z) :
    letI : Algebra S.k Γ(I.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.fibreSubschemeToSpec I hI).appTop).hom.toAlgebra
    Module.finrank S.k Γ(I.subscheme, ⊤) = S.specialFiberComponentWeight Z := by
  subst h
  have hι : S.fibreSubschemeToSpec _ hI = S.specialFiberComponentToSpec Z := by
    rw [fibreSubschemeToSpec, RegularModelSituation.specialFiberComponentToSpec]
    congr 1
    rw [← cancel_mono S.specialFiberι, S.fibreSubschemeι_comp,
      S.specialFiberComponentι_specialFiberι]
  rw [hι]
  rfl

/-- **A contracted component missing `C_n` keeps its weight**: if `C_i ∩ C_n = ∅` then
`(C_i · C_n) = 0` forces `f⁻¹C'_i = C_i`, and `H⁰(f⁻¹C'_i, 𝒪) ≅ H⁰(C'_i, 𝒪)` gives `w'ᵢ = wᵢ`. -/
public theorem contractedComponentWeight_eq_of_inter_eq_empty
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (κ : Type u) [Field κ] {ε : projectiveLineProj κ ≅ (S.specialFiberComponentIdeal N).subscheme}
    (hE : (S.specialFiberComponentIdeal N).IsExceptionalCurveOfFirstKind κ ε)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N})
    (hdisj : (Z.1.1 : Set S.specialFiber) ∩ N.1 = ∅) :
    (S.contractedSituation hf).specialFiberComponentWeight (S.contractedComponentEquiv hf Z) =
      S.specialFiberComponentWeight Z.1 := by
  classical
  obtain ⟨-, e, he⟩ := S.exists_comap_contractedComponent_eq hf Z
  have hNN : S.specialFiberIntersectionMatrix N N = -(S.specialFiberComponentWeight N : ℤ) := by
    rw [S.specialFiberIntersectionMatrix_self_eq_neg_weight_add_genus N κ hE,
      Stacks.Curves.genus_eq_zero_of_iso_projectiveLine ε.symm _]
    simp
  have hZN : S.specialFiberIntersectionMatrix Z.1 N = 0 :=
    (S.specialFiberIntersectionMatrix_nonneg_and_eq_zero_iff Z.2).2.2 hdisj
  have hrel := S.specialFiberIntersectionMatrix_add_mul_eq_zero hf Z e he
  rw [hZN, hNN] at hrel
  have hw := S.specialFiberComponentWeight_pos N
  have he0 : e = 0 := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exact h
    · exfalso
      have : (0 : ℤ) < e * S.specialFiberComponentWeight N := by positivity
      linarith
  rw [he0, pow_zero, mul_one] at he
  have h0 := S.finrank_cohomologyOverField_comap_contractedComponent_eq hf Z 0
  rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections] at h0
  rw [← S.finrank_globalSections_fibreSubscheme_eq_weight _ Z.1 he]
  exact h0.symm

open AlgebraicGeometry.NumericalType in
/-- **The numerical type after contracting an exceptional curve.** Let `f : X ⟶ X'` contract a component `C_n` of the special
fibre of a regular proper model which is an exceptional curve of the first kind. Enumerate the
components of `X_k` by `e`, with `C_n` last, and those of `X'_k` by `e'`, compatibly with
`C'_i = f(C_i)`. Let `T` and `T'` be the numerical types associated to `X` and `X'`. Then `n` is a
`(-1)`-index of `T`, and `T'` agrees with the contraction of `T` of Tag 0C77 except for the
weights: `n' = n - 1`, `m'_i = m_i`, `a'_{ij} = a_{ij} - a_{in}a_{jn}/a_{nn}`, `g'_i` is the genus
formula at `w'_i`, and `w'_i` is a positive integer dividing `w_i`. Moreover `w'_i` divides `w_n`
whenever `a_{in} ≠ 0`, i.e. whenever `C_i` meets `C_n`, and `w'_i = w_i` whenever `a_{in} = 0`. The
divisibility `w'_i ∣ w_n` is stated where the maps `κ_i ← κ'_i → κ_n` of Tag 0C6C (2) exist; for a
component missing `C_n` the weight is `w_i`, which need not divide `w_n`
(`AlgebraicGeometry.NumericalType.exists_intersection_eq_zero_not_weight_dvd`). This is the
geometric part of Tag 0CA9, whose full statement is
`associatedNumericalType_contraction_comparison`. -/
public theorem isContractionUpToWeight_associatedNumericalType
    [DecidableEq (irreducibleComponents S.specialFiber)]
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    [DecidableEq (irreducibleComponents (S.contractedSituation hf).specialFiber)]
    (κ : Type u) [Field κ] {ε : projectiveLineProj κ ≅ (S.specialFiberComponentIdeal N).subscheme}
    (hE : (S.specialFiberComponentIdeal N).IsExceptionalCurveOfFirstKind κ ε)
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (e' : Fin (n - 1) ≃ irreducibleComponents (S.contractedSituation hf).specialFiber)
    (hN : e (lastIndex (S.associatedNumericalType n e)) = N)
    (he' : ∀ i, ((S.contractedComponentEquiv hf).symm (e' i)).1 =
      e (remainingIndex (S.associatedNumericalType n e) i)) :
    IsMinusOneIndex (S.associatedNumericalType n e) (lastIndex (S.associatedNumericalType n e)) ∧
      ∃ hT : IsContractionUpToWeight (S.associatedNumericalType n e)
          ((S.contractedSituation hf).associatedNumericalType (n - 1) e'),
        (∀ i, (S.associatedNumericalType n e).intersection
            (remainingIndex (S.associatedNumericalType n e) i)
            (lastIndex (S.associatedNumericalType n e)) ≠ 0 →
          ((S.contractedSituation hf).associatedNumericalType (n - 1) e').weight
              (Fin.cast hT.componentCount_eq.symm i) ∣
            (S.associatedNumericalType n e).weight (lastIndex (S.associatedNumericalType n e))) ∧
        ∀ i, (S.associatedNumericalType n e).intersection
            (remainingIndex (S.associatedNumericalType n e) i)
            (lastIndex (S.associatedNumericalType n e)) = 0 →
          ((S.contractedSituation hf).associatedNumericalType (n - 1) e').weight
              (Fin.cast hT.componentCount_eq.symm i) =
            (S.associatedNumericalType n e).weight
              (remainingIndex (S.associatedNumericalType n e) i) := by
  have hgN : S.specialFiberComponentGenus N = 0 := by
    let := (S.isField_and_finite_globalSections_specialFiberComponent N).1.toField
    exact Stacks.Curves.genus_eq_zero_of_iso_projectiveLine ε.symm _
  have hNN : S.specialFiberIntersectionMatrix N N = -(S.specialFiberComponentWeight N : ℤ) := by
    rw [S.specialFiberIntersectionMatrix_self_eq_neg_weight_add_genus N κ hE,
      Stacks.Curves.genus_eq_zero_of_iso_projectiveLine ε.symm _]
    simp
  -- the component `C_i` of `X_k` and its image `C'_i`
  let Zc (i : Fin (n - 1)) : {Z : irreducibleComponents S.specialFiber // Z ≠ N} :=
    (S.contractedComponentEquiv hf).symm (e' i)
  have hZc (i : Fin (n - 1)) : e (remainingIndex (S.associatedNumericalType n e) i) = (Zc i).1 :=
    (he' i).symm
  have hZc' (i : Fin (n - 1)) : e' i = S.contractedComponentEquiv hf (Zc i) :=
    ((S.contractedComponentEquiv hf).apply_symm_apply (e' i)).symm
  have hT : IsContractionUpToWeight (S.associatedNumericalType n e)
      ((S.contractedSituation hf).associatedNumericalType (n - 1) e') :=
    { componentCount_eq := rfl
      multiplicity_eq := fun i => by
        change ((S.contractedSituation hf).specialFiberMultiplicity (e' i) : ℤ) =
          S.specialFiberMultiplicity (e _)
        rw [hZc' i, hZc i, S.specialFiberMultiplicity_contractedComponentEquiv hf]
      intersection_eq := fun i j => by
        change ((S.contractedSituation hf).specialFiberIntersectionMatrix (e' i) (e' j) : ℚ) =
          S.specialFiberIntersectionMatrix (e _) (e _) -
            (S.specialFiberIntersectionMatrix (e _) (e _) *
              S.specialFiberIntersectionMatrix (e _) (e _) : ℚ) /
              S.specialFiberIntersectionMatrix (e _) (e _)
        rw [hZc' i, hZc' j, hZc i, hZc j, hN, S.contractedSpecialFiberIntersectionMatrix hf]
      weight_dvd := fun i => by
        change ((S.contractedSituation hf).specialFiberComponentWeight (e' i) : ℤ) ∣
          S.specialFiberComponentWeight (e _)
        rw [hZc' i, hZc i]
        exact Int.natCast_dvd_natCast.mpr (S.contractedComponentWeight_dvd hf (Zc i))
      componentGenus_eq := fun i => by
        change ((S.contractedSituation hf).specialFiberComponentGenus (e' i) : ℚ) =
          (S.specialFiberComponentWeight (e _) : ℚ) /
              ((S.contractedSituation hf).specialFiberComponentWeight (e' i) : ℚ) *
              ((S.specialFiberComponentGenus (e _) : ℚ) - 1) + 1 +
            ((S.specialFiberIntersectionMatrix (e _) (e _) : ℚ) ^ 2 -
                (S.specialFiberComponentWeight (e _) : ℚ) *
                  S.specialFiberIntersectionMatrix (e _) (e _)) /
              (2 * ((S.contractedSituation hf).specialFiberComponentWeight (e' i) : ℚ) *
                (S.specialFiberComponentWeight (e _) : ℚ))
        rw [hZc' i, hZc i, hN]
        exact S.cast_specialFiberComponentGenus_contractedComponentEquiv hf κ hE (Zc i) }
  refine ⟨⟨?_, ?_⟩, hT, fun i hi => ?_, fun i hi => ?_⟩
  · change (S.specialFiberComponentGenus (e _) : ℤ) = 0
    rw [hN, hgN]
    rfl
  · change S.specialFiberIntersectionMatrix (e _) (e _) = -(S.specialFiberComponentWeight (e _) : ℤ)
    rw [hN, hNN]
  · change S.specialFiberIntersectionMatrix (e _) (e _) ≠ 0 at hi
    change ((S.contractedSituation hf).specialFiberComponentWeight (e' i) : ℤ) ∣
      S.specialFiberComponentWeight (e _)
    rw [hZc i, hN] at hi
    rw [hZc' i, hN]
    have hmeet : ((Zc i).1.1 ∩ N.1 : Set S.specialFiber).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr fun h =>
        hi ((S.specialFiberIntersectionMatrix_nonneg_and_eq_zero_iff (Zc i).2).2.2 h)
    exact Int.natCast_dvd_natCast.mpr
      (S.contractedComponentWeight_dvd_of_inter_nonempty hf (Zc i) hmeet)
  · change S.specialFiberIntersectionMatrix (e _) (e _) = 0 at hi
    change ((S.contractedSituation hf).specialFiberComponentWeight (e' i) : ℤ) =
      S.specialFiberComponentWeight (e _)
    rw [hZc i, hN] at hi
    rw [hZc' i, hZc i]
    exact congrArg _ (S.contractedComponentWeight_eq_of_inter_eq_empty hf κ hE (Zc i)
      ((S.specialFiberIntersectionMatrix_nonneg_and_eq_zero_iff (Zc i).2).2.1 hi))

end RegularProperModelSituation

end Stacks.Models

end
