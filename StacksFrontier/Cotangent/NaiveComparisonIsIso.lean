module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Algebra.Homology.TwoTermHomologyExact
public import StacksFrontier.Cotangent.NaiveComparisonAgreement
public import StacksFrontier.Cotangent.NaiveComparisonQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# The naive cotangent complex is the truncation `τ_{≥ -1} L_{B/A}` (Stacks 08RB)

For a ring map `A → B`, let `P = A[B] → B` be the canonical presentation, with kernel `I`. The
naive cotangent complex `NL_{B/A} = (I/I² → Ω_{P/A} ⊗_P B)` maps to `τ_{≥ -1} L_{B/A}` by the
map `c` of Tag 08R9 at the object `P → B` of `C_{B/A}`, which is
`Stacks.Cotangent.comparisonAtNaive`. This file proves that `c` is an isomorphism in `D(B)`.

## Main results

* `Stacks.Cotangent.isIso_comparisonAtNaive`: **Stacks 08RB**, `c` is an isomorphism.
* `Stacks.Cotangent.naiveComparisonIso`: the resulting isomorphism
  `NL_{B/A} ≅ τ_{≥ -1} L_{B/A}` in `D(B)`, whose underlying map is `c`.
* `Stacks.Cotangent.isIso_homologyMap_explicitNaiveComparison`: the explicit chain map
  `L_{B/A} → NL_{B/A}` of Remark 08UP is an isomorphism on cohomology in degrees `-1` and `0`.

## Implementation notes

The source reduces the statement to a compatibility of long exact sequences and omits the
verification. The route here uses instead the two facts the library already has about `c`:

* in degree `-1`, `c` is the evaluation of the two-term complex `𝒥/𝒥² → Ω` at `P₀ → B` followed
  by isomorphisms, and that evaluation is an isomorphism on `H^{-1}`
  (`Stacks.Cotangent.isIso_homologyMap_evalCone_conormalExtension`);
* the explicit chain map `g : L_{B/A} → NL_{B/A}` of Remark 08UP satisfies `g ≫ c = π`, the
  truncation map (`Stacks.Cotangent.explicitNaiveComparison_comp_comparisonAtNaive`). In degree
  `0` the map `g` is an isomorphism of terms and both complexes vanish in degree `1`, so `H⁰(g)`
  is an epimorphism; as `H⁰(g) ≫ H⁰(c) = H⁰(π)` is an isomorphism, so is `H⁰(c)`.

In every other degree both sides of `c` have no cohomology: `NL_{B/A}` lives in degrees `-1`
and `0`, the truncation in degrees `≥ -1`, and `L_{B/A}` in degrees `≤ 0`. A map in `D(B)` which
is an isomorphism on all cohomology is an isomorphism (`DerivedCategory.isIso_iff`).

## References

* [Stacks Project, Tag 08RB](https://stacks.math.columbia.edu/tag/08RB)
* [Stacks Project, Tag 08R9](https://stacks.math.columbia.edu/tag/08R9)
* [Stacks Project, Tag 08UP](https://stacks.math.columbia.edu/tag/08UP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v

namespace Stacks.Cotangent

open CommAlgCat

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-- The explicit chain map of Remark 08UP, landing in the spelling
`conormalExtension A B (op ⦋0⦌)` of the canonical presentation which is the source of
`Stacks.Cotangent.comparisonAtNaive`. -/
abbrev explicitNaiveComparisonAtNaive :
    cotangentComplex A B ⟶
      Algebra.Extension.naiveComplex (conormalExtension A B (op ⦋0⦌)) :=
  explicitNaiveComparison A B ≫ (naiveSpellingIso A B 0).hom

/-- In degree `0` the explicit chain map is an isomorphism of terms. -/
instance isIso_explicitNaiveComparisonAtNaive_f_zero :
    IsIso ((explicitNaiveComparisonAtNaive A B).f 0) := by
  have := isIso_comparisonDegreeZero A B
  rw [HomologicalComplex.comp_f, explicitNaiveComparison_f, comparisonComponent_zero]
  infer_instance

/-- The explicit chain map is an epimorphism on cohomology in degree `0`: it is an isomorphism of
terms there, and neither complex has a term in degree `1`. -/
theorem epi_homologyMap_explicitNaiveComparisonAtNaive_zero :
    Epi (HomologicalComplex.homologyMap (explicitNaiveComparisonAtNaive A B) 0) := by
  refine HomologicalComplex.epi_homologyMap_of_epi_opcyclesMap _ 0 1 (by simp)
    ((cotangentComplex_isZero_pos A B 1 (by norm_num)).eq_of_tgt _ _)
    ((Algebra.Extension.isZero_naiveComplex_X _ 1 (by decide) (by decide)).eq_of_tgt _ _) ?_
  have : Epi ((cotangentComplex A B).pOpcycles 0 ≫
      HomologicalComplex.opcyclesMap (explicitNaiveComparisonAtNaive A B) 0) := by
    rw [HomologicalComplex.p_opcyclesMap]
    infer_instance
  exact epi_of_epi ((cotangentComplex A B).pOpcycles 0) _

/-- `Q` of a complex with a zero term in degree `n` has no cohomology in degree `n`. -/
private theorem isZero_homologyFunctor_obj_Q_of_isZero_X
    {K : CochainComplex (ModuleCat.{max u v} B) ℤ} (n : ℤ) (h : IsZero (K.X n)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj
      (DerivedCategory.Q.obj K)) :=
  IsZero.of_iso (HomologicalComplex.ExactAt.of_isZero h).isZero_homology
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B) n).app _)

/-- A chain map is an isomorphism on cohomology iff its image in `D(B)` is. -/
private theorem isIso_homologyFunctor_map_Q_iff
    {K L : CochainComplex (ModuleCat.{max u v} B) ℤ} (f : K ⟶ L) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).map
      (DerivedCategory.Q.map f)) ↔ IsIso (HomologicalComplex.homologyMap f n) :=
  NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B) n) f

/-- In degree `-1` the comparison map `c` is an isomorphism on cohomology: it is the evaluation of
the two-term complex at `P₀ → B`, an isomorphism on `H^{-1}`, followed by the truncation and the
identification of Remark 08R7. -/
theorem isIso_homologyFunctor_map_comparisonAtNaive_negOne :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) (-1)).map
      (comparisonAtNaive A B)) := by
  rw [comparisonAtNaive, comparison_eq_comparisonOfHom A B (conormalExtension A B (op ⦋0⦌))
    (Algebra.Extension.Hom.id (conormalExtension A B (op ⦋0⦌))), comparisonOfHom,
    Functor.map_comp, Functor.map_comp]
  have h₁ : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) (-1)).map
      (DerivedCategory.Q.map (evalCone A B (conormalExtension A B (op ⦋0⦌))
        (Algebra.Extension.Hom.id (conormalExtension A B (op ⦋0⦌)))))) :=
    (isIso_homologyFunctor_map_Q_iff A B _ (-1)).2
      (isIso_homologyMap_evalCone_conormalExtension A B _)
  have h₂ := DerivedCategory.isIso_homologyMap_truncGEπ_app (-1) (-1) le_rfl
    (DerivedCategory.Q.obj (cotangentCone A B))
  infer_instance

/-- In degree `0` the comparison map `c` is an isomorphism on cohomology. -/
theorem isIso_homologyFunctor_map_comparisonAtNaive_zero :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) 0).map
      (comparisonAtNaive A B)) := by
  set H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) 0
  have hπ := DerivedCategory.isIso_homologyMap_truncGEπ_app (-1) 0 (by norm_num)
    (DerivedCategory.Q.obj (cotangentComplex A B))
  have hcomp : H.map (DerivedCategory.Q.map (explicitNaiveComparisonAtNaive A B)) ≫
      H.map (comparisonAtNaive A B) =
        H.map ((DerivedCategory.TStructure.t.truncGEπ (-1)).app
          (DerivedCategory.Q.obj (cotangentComplex A B))) := by
    rw [← H.map_comp, explicitNaiveComparison_comp_comparisonAtNaive]
  have hepi : Epi (H.map (DerivedCategory.Q.map (explicitNaiveComparisonAtNaive A B))) := by
    have e := (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B) 0).hom.naturality
      (explicitNaiveComparisonAtNaive A B)
    have e' : H.map (DerivedCategory.Q.map (explicitNaiveComparisonAtNaive A B)) =
        (((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B) 0).app _).hom ≫
          (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} B) (ComplexShape.up ℤ) 0).map
            (explicitNaiveComparisonAtNaive A B)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B) 0).app _).inv :=
      (Iso.eq_comp_inv _).2 e
    have : Epi ((HomologicalComplex.homologyFunctor (ModuleCat.{max u v} B)
        (ComplexShape.up ℤ) 0).map (explicitNaiveComparisonAtNaive A B)) :=
      epi_homologyMap_explicitNaiveComparisonAtNaive_zero A B
    rw [e']
    infer_instance
  have : IsIso (H.map (DerivedCategory.Q.map (explicitNaiveComparisonAtNaive A B)) ≫
      H.map (comparisonAtNaive A B)) := by
    rw [hcomp]
    infer_instance
  have : Mono (H.map (DerivedCategory.Q.map (explicitNaiveComparisonAtNaive A B))) :=
    mono_of_mono _ (H.map (comparisonAtNaive A B))
  have := isIso_of_mono_of_epi (H.map (DerivedCategory.Q.map (explicitNaiveComparisonAtNaive A B)))
  exact IsIso.of_isIso_comp_left
    (H.map (DerivedCategory.Q.map (explicitNaiveComparisonAtNaive A B))) _

/-- **Stacks 08RB.** For a ring map `A → B`, the canonical map
`c : NL_{B/A} → τ_{≥ -1} L_{B/A}` of Tag 08R9 at the canonical presentation `A[B] → B` is an
isomorphism in `D(B)`: the truncation `τ_{≥ -1} L_{B/A}` is canonically quasi-isomorphic to the
naive cotangent complex. -/
@[stacks 08RB "the canonical map c : NL_{B/A} → τ_{≥ -1} L_{B/A} of Tag 08R9, at the canonical \
  presentation A[B] → B, is an isomorphism in D(B)"]
theorem isIso_comparisonAtNaive : IsIso (comparisonAtNaive A B) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  by_cases hn : n = -1
  · subst hn
    exact isIso_homologyFunctor_map_comparisonAtNaive_negOne A B
  by_cases hn' : n = 0
  · subst hn'
    exact isIso_homologyFunctor_map_comparisonAtNaive_zero A B
  have hsrc : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj
      (DerivedCategory.Q.obj
        (Algebra.Extension.naiveComplex (conormalExtension A B (op ⦋0⦌))))) :=
    isZero_homologyFunctor_obj_Q_of_isZero_X A B n
      (Algebra.Extension.isZero_naiveComplex_X _ n hn hn')
  have htgt : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj
      ((DerivedCategory.TStructure.t.truncGE (-1)).obj
        (DerivedCategory.Q.obj (cotangentComplex A B)))) := by
    rcases lt_or_gt_of_ne hn with h | h
    · exact DerivedCategory.isZero_of_isGE _ (-1) n h
    · have hπ := DerivedCategory.isIso_homologyMap_truncGEπ_app (-1) n h.le
        (DerivedCategory.Q.obj (cotangentComplex A B))
      refine IsZero.of_iso ?_ (asIso ((DerivedCategory.homologyFunctor _ n).map
        ((DerivedCategory.TStructure.t.truncGEπ (-1)).app
          (DerivedCategory.Q.obj (cotangentComplex A B))))).symm
      exact isZero_homologyFunctor_obj_Q_of_isZero_X A B n
        (cotangentComplex_isZero_pos A B n (by omega))
  exact ⟨⟨htgt.to_ _, hsrc.eq_of_src _ _, htgt.eq_of_src _ _⟩⟩

/-- **Stacks 08RB.** The isomorphism `NL_{B/A} ≅ τ_{≥ -1} L_{B/A}` in `D(B)`, with the naive
cotangent complex the two-term complex `I/I² → Ω_{A[B]/A} ⊗_{A[B]} B` of the canonical
presentation; its underlying map is the canonical map `c` of Tag 08R9. -/
@[stacks 08RB "the isomorphism NL_{B/A} ≅ τ_{≥ -1} L_{B/A} in D(B) whose underlying map is the \
  canonical map c of Tag 08R9"]
def naiveComparisonIso :
    DerivedCategory.Q.obj (Algebra.Extension.naiveComplex (conormalExtension A B (op ⦋0⦌))) ≅
      (DerivedCategory.TStructure.t.truncGE (-1)).obj
        (DerivedCategory.Q.obj (cotangentComplex A B)) :=
  haveI := isIso_comparisonAtNaive A B
  asIso (comparisonAtNaive A B)

/-- The underlying map of `naiveComparisonIso` is the comparison map `comparisonAtNaive`. -/
@[simp]
theorem naiveComparisonIso_hom : (naiveComparisonIso A B).hom = comparisonAtNaive A B := rfl

/-- The explicit chain map of Remark 08UP, in `D(B)`, is the truncation map followed by the
inverse of the isomorphism of Tag 08RB. -/
theorem Q_map_explicitNaiveComparisonAtNaive :
    DerivedCategory.Q.map (explicitNaiveComparisonAtNaive A B) =
      (DerivedCategory.TStructure.t.truncGEπ (-1)).app
          (DerivedCategory.Q.obj (cotangentComplex A B)) ≫ (naiveComparisonIso A B).inv := by
  rw [Iso.eq_comp_inv, naiveComparisonIso_hom]
  exact explicitNaiveComparison_comp_comparisonAtNaive A B

/-- **The explicit chain map of Remark 08UP is an isomorphism on cohomology in degrees `-1` and
`0`.** In `D(B)` it is the truncation map `L_{B/A} → τ_{≥ -1} L_{B/A}` followed by the inverse of
the isomorphism of Tag 08RB, and the truncation map is an isomorphism on cohomology in degrees
`≥ -1`. -/
theorem isIso_homologyMap_explicitNaiveComparison (i : ℤ) (hi : i = -1 ∨ i = 0) :
    IsIso (HomologicalComplex.homologyMap (explicitNaiveComparison A B) i) := by
  have hπ := DerivedCategory.isIso_homologyMap_truncGEπ_app (-1) i (by omega)
    (DerivedCategory.Q.obj (cotangentComplex A B))
  have hQ : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i).map
      (DerivedCategory.Q.map (explicitNaiveComparisonAtNaive A B))) := by
    rw [Q_map_explicitNaiveComparisonAtNaive, Functor.map_comp]
    infer_instance
  replace hQ : IsIso (HomologicalComplex.homologyMap
      (explicitNaiveComparison A B ≫ (naiveSpellingIso A B 0).hom) i) :=
    (isIso_homologyFunctor_map_Q_iff A B _ i).1 hQ
  rw [HomologicalComplex.homologyMap_comp] at hQ
  exact IsIso.of_isIso_comp_right _
    (HomologicalComplex.homologyMap (naiveSpellingIso A B 0).hom i)

/-! ### The tautological presentation -/

/-- The augmentation of the standard resolution in degree zero, read through the identification
`P₀ = A[B]` of `CommAlgCat.standardResolutionZeroAlgEquiv`, is the evaluation `[b] ↦ b`. -/
theorem standardResolutionAugmentationHom_zeroAlgEquiv_symm (p : MvPolynomial B A) :
    standardResolutionAugmentationHom A B (op ⦋0⦌)
        ((standardResolutionZeroAlgEquiv A B).symm p) =
      MvPolynomial.aeval (fun b : B => b) p := by
  have h : ((standardResolution A B).hom.app (op ⦋0⦌)).hom.comp
      (standardResolutionZeroAlgEquiv A B).symm.toAlgHom =
        MvPolynomial.aeval (fun b : B => b) := by
    refine MvPolynomial.algHom_ext fun b => ?_
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X]
    exact standardResolution_augmentation_X A B b
  exact AlgHom.congr_fun h p

/-- The degree-zero term `P₀ → B` of the standard resolution maps to the tautological
presentation `A[B] → B` of `Algebra.Generators.self`, by the identification `P₀ = A[B]`. -/
def standardResolutionExtensionZeroToNaive :
    (standardResolutionExtension A B 0).Hom (naiveExtension A B) where
  toRingHom := (standardResolutionZeroAlgEquiv A B).toAlgHom.toRingHom
  toRingHom_algebraMap x := (standardResolutionZeroAlgEquiv A B).commutes x
  algebraMap_toRingHom x := by
    obtain ⟨p, rfl⟩ := (standardResolutionZeroAlgEquiv A B).symm.surjective x
    change MvPolynomial.aeval (fun b : B => b)
        ((standardResolutionZeroAlgEquiv A B) ((standardResolutionZeroAlgEquiv A B).symm p)) =
      standardResolutionAugmentationHom A B (op ⦋0⦌) ((standardResolutionZeroAlgEquiv A B).symm p)
    rw [AlgEquiv.apply_symm_apply, standardResolutionAugmentationHom_zeroAlgEquiv_symm]

/-- The tautological presentation `A[B] → B` maps to the degree-zero term of the standard
resolution, by the identification `A[B] = P₀`. -/
def naiveToStandardResolutionExtensionZero :
    (naiveExtension A B).Hom (standardResolutionExtension A B 0) where
  toRingHom := (standardResolutionZeroAlgEquiv A B).symm.toAlgHom.toRingHom
  toRingHom_algebraMap x := (standardResolutionZeroAlgEquiv A B).symm.commutes x
  algebraMap_toRingHom p := standardResolutionAugmentationHom_zeroAlgEquiv_symm A B p

/-- The identification of the degree-zero term of the standard resolution with the tautological
presentation of `B` induces an isomorphism of naive cotangent complexes. -/
def naiveComplexStandardResolutionZeroIso :
    Algebra.Extension.naiveComplex (standardResolutionExtension A B 0) ≅
      Algebra.Extension.naiveComplex (naiveExtension A B) :=
  haveI := Algebra.Extension.isIso_naiveComplexMap (standardResolutionExtensionZeroToNaive A B)
    (naiveToStandardResolutionExtensionZero A B)
    (Algebra.Extension.Hom.ext (RingHom.ext fun x =>
      (standardResolutionZeroAlgEquiv A B).symm_apply_apply x))
    (Algebra.Extension.Hom.ext (RingHom.ext fun p =>
      (standardResolutionZeroAlgEquiv A B).apply_symm_apply p))
  asIso (Algebra.Extension.naiveComplexMap (standardResolutionExtensionZeroToNaive A B))

/-- The explicit chain map of Remark 08UP, landing in the naive cotangent complex
`NL_{B/A} = Algebra.Extension.naiveComplex (Algebra.Generators.self A B).toExtension` of the
tautological presentation, the presentation of `Algebra.naiveCotangentComplex`. -/
noncomputable def cotangentComplexToNaive :
    cotangentComplex A B ⟶ Algebra.Extension.naiveComplex (naiveExtension A B) :=
  explicitNaiveComparison A B ≫ (naiveComplexStandardResolutionZeroIso A B).hom

/-- The chain map `L_{B/A} → NL_{B/A}` into the naive cotangent complex of the tautological
presentation is an isomorphism on cohomology in degrees `-1` and `0`. -/
theorem isIso_homologyMap_cotangentComplexToNaive (i : ℤ) (hi : i = -1 ∨ i = 0) :
    IsIso (HomologicalComplex.homologyMap (cotangentComplexToNaive A B) i) := by
  have := isIso_homologyMap_explicitNaiveComparison A B i hi
  rw [cotangentComplexToNaive, HomologicalComplex.homologyMap_comp]
  infer_instance

end Stacks.Cotangent

end
