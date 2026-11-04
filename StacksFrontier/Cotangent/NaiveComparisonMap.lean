module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.NaiveComparison
public import StacksFrontier.Cotangent.NaiveComparisonCone

/-!
# The comparison map of Tag 08R9

Let `A → B` be a ring map and let `U = (P → B)` be an object of `C_{B/A}` with kernel `J`.
Remark 08R7 produces from `τ_{≥ -1} Lπ_!(𝒥/𝒥² → Ω) = τ_{≥ -1} L_{B/A}` a canonical map

`(J/J² → Ω_{P/A} ⊗_P B) ⟶ τ_{≥ -1} L_{B/A}`

in `D(B)`, which is the displayed map of Tag 08R9. This file constructs it.

## Main definitions

* `Stacks.Cotangent.evalCone`: the evaluation at `U` of the two-term complex, as a map of
  complexes into the mapping cone of `𝒥/𝒥² ⟶ Ω` on the standard resolution.
* `Stacks.Cotangent.comparisonOfHom`: the comparison map of Tag 08R9, built from a chosen
  morphism `U ⟶ (P₀ → B)` into the degree-zero term of the standard resolution.
* `Stacks.Cotangent.comparison`: the same at the canonical such morphism, attached to a
  presentation of `P` by variables, and `Stacks.Cotangent.comparisonAtNaive` its value at the
  object `A[B] → B`, which is the map `c` of Lemma 08RB.

## Main results

* `Stacks.Cotangent.evalCone_f_negOne` and `Stacks.Cotangent.evalCone_f_zero`: the two nonzero
  components of the evaluation.
* `Stacks.Cotangent.comparisonOfHom_comp_truncGEConeIso`: the equation that pins the map down,
  namely that after the identification of Remark 08R7 it is the evaluation at `U` followed by
  the truncation.

## Implementation notes

**How the map is built.** The source constructs the map by evaluating at `U` the complex of
sheaves `𝒥/𝒥² → Ω` on `C_{B/A}` and following it by the canonical map of Tag 08Q6 into
`Lπ_!`, then by the identification of Remark 08R7. Here that is carried on the standard
resolution, where by Tag 08PS the two lower shrieks `Lπ_!(𝒥/𝒥²)` and `Lπ_!(Ω) = L_{B/A}` are
the complexes `Stacks.Cotangent.conormalComplex` and `CommAlgCat.cotangentComplex`: the
evaluation at `U` becomes the pair of maps `J/J² ⟶ 𝒥₀/𝒥₀²` and
`Ω_{P/A} ⊗_P B ⟶ Ω_{P₀/A} ⊗_{P₀} B` induced by a morphism `P ⟶ P₀` over `B`, and the
identification of Remark 08R7 is `Stacks.Cotangent.truncGEConeIso`, which rests on the
vanishing of `H₀(C_{B/A}, 𝒥/𝒥²)` and `H₁(C_{B/A}, 𝒥/𝒥²)`.

**Which objects.** The source writes the degree `-1` term of the displayed complex as `J/J²`.
For that to be a `B`-module — so that the displayed complex is an object of `D(B)`, as the
source asserts — the augmentation `P → B` must be surjective: `J/J²` is a module over the image
of `P` in `B`. Accordingly an object of `C_{B/A}` is carried here by Mathlib's
`Algebra.Extension A B`, which is a surjective augmentation together with a set-theoretic
section, with `Algebra.Extension.Cotangent` its `J/J²` and
`Algebra.Extension.CotangentSpace` its `Ω_{P/A} ⊗_P B`; the two-term complex is
`Algebra.Extension.naiveComplex`, which
`StacksFrontier/Cotangent/NaiveComparison.lean` already registers as the source of the displayed
map. Both objects at which the source later uses the map are of this kind: `(A → B)` for a
surjection `A → B` in Tag 08RA, and `(A[B] → B)` in Lemma 08RB and Remark 08UP.

**The morphism into the standard resolution.** The construction takes as data a morphism of
extensions `U ⟶ (P₀ → B)`, which exists whenever `P` is a polynomial `A`-algebra — that is,
whenever `U` is an object of `C_{B/A}` — because `P₀ = A[B]` surjects onto `B`:
`Stacks.Cotangent.toResolutionZero` sends a variable `x` of `P` to the variable `[α x]` of
`A[B]`, and `Stacks.Cotangent.comparison` is `Stacks.Cotangent.comparisonOfHom` at that
morphism. The resulting map in `D(B)` does not depend on the morphism chosen:
`Stacks.Cotangent.comparisonOfHom_eq` of
`StacksFrontier/Cotangent/NaiveComparisonIndependence.lean`, whose homotopy is Mathlib's
`Algebra.Extension.Hom.sub`. That is what makes the map computable at a concrete object, the
presentation by variables being extracted from a `Classical.choice`.

## References

* [Stacks Project, Tag 08R9](https://stacks.math.columbia.edu/tag/08R9)
* [Stacks Project, Tag 08R7](https://stacks.math.columbia.edu/tag/08R7)
* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v

namespace Stacks.Cotangent

open CommAlgCat

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-! ### The degree-zero terms of the two complexes on the standard resolution -/

/-- In cohomological degree `0` the conormal complex is `𝒥₀/𝒥₀²`. -/
def conormalComplexXZeroIso :
    (conormalComplex A B).X 0 ≅ conormalTerm A B (op ⦋0⦌) :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := 0) (by simp)

/-- In cohomological degree `0` the cotangent complex is `Ω_{P₀/A} ⊗_{P₀} B`. -/
def cotangentComplexXZeroIso :
    (cotangentComplex A B).X 0 ≅ cotangentTerm A B (op ⦋0⦌) :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := 0) (by simp)

/-- In cohomological degree `0` the map `𝒥/𝒥² ⟶ Ω` is `d`. -/
theorem conormalToCotangentComplex_f_zero :
    (conormalToCotangentComplex A B).f 0 =
      (conormalComplexXZeroIso A B).hom ≫ conormalToCotangentApp A B (op ⦋0⦌) ≫
        (cotangentComplexXZeroIso A B).inv := by
  rw [conormalToCotangentComplex,
    HomologicalComplex.extendMap_f _ (ComplexShape.embeddingUpIntLE (0 : ℤ))
      (i := 0) (i' := 0) (by simp)]
  rfl

/-- The conormal complex has no differential out of degree `0`. -/
theorem conormalComplex_d_zero_one : (conormalComplex A B).d 0 1 = 0 :=
  (isZero_conormalComplex_X_pos A B 1 one_pos).eq_of_tgt _ _

/-- The cone vanishes in cohomological degree `1`. -/
theorem isZero_cotangentCone_X_one : IsZero ((cotangentCone A B).X 1) := by
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨isZero_conormalComplex_X_pos A B 2 (by norm_num),
    cotangentComplex_isZero_pos A B 1 one_pos⟩

/-! ### The evaluation of the two-term complex at an object of `C_{B/A}` -/

section Evaluation

variable (E : Algebra.Extension.{max u v} A ↥B)
  (hom : E.Hom (conormalExtension A B (op ⦋0⦌)))

/-- The map `J/J² ⟶ 𝒥₀/𝒥₀²` induced by a morphism of `U` into the degree-zero term of the
standard resolution: the degree `-1` part of the evaluation at `U`. -/
def evalCotangent : ModuleCat.of ↥B E.Cotangent ⟶ conormalTerm A B (op ⦋0⦌) :=
  ModuleCat.ofHom (Algebra.Extension.Cotangent.map hom)

/-- The map `Ω_{P/A} ⊗_P B ⟶ Ω_{P₀/A} ⊗_{P₀} B` induced by a morphism of `U` into the
degree-zero term of the standard resolution: the degree `0` part of the evaluation at `U`. -/
def evalCotangentSpace : ModuleCat.of ↥B E.CotangentSpace ⟶ cotangentTerm A B (op ⦋0⦌) := by
  change ModuleCat.of ↥B E.CotangentSpace ⟶
    ModuleCat.of ↥B ((conormalExtension A B (op ⦋0⦌)).CotangentSpace)
  exact ModuleCat.ofHom (Algebra.Extension.CotangentSpace.map hom)

/-- The evaluation at `U` commutes with the two differentials `d`. -/
theorem evalCotangent_comp :
    evalCotangent A B E hom ≫ conormalToCotangentApp A B (op ⦋0⦌) =
      ModuleCat.ofHom E.cotangentComplex ≫ evalCotangentSpace A B E hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact (Algebra.Extension.CotangentSpace.map_cotangentComplex hom x).symm

/-- The degree `-1` component of the evaluation at `U`, landing in the `𝒥/𝒥²` summand of the
cone. -/
def evalConeNegOne :
    (Algebra.Extension.naiveComplex E).X (-1) ⟶ (cotangentCone A B).X (-1) :=
  (Algebra.Extension.naiveComplexXNegOneIso E).hom ≫ evalCotangent A B E hom ≫
    (conormalComplexXZeroIso A B).inv ≫
    (CochainComplex.mappingCone.inl (conormalToCotangentComplex A B)).v 0 (-1) (by norm_num)

/-- The degree `0` component of the evaluation at `U`, landing in the `L_{B/A}` summand of the
cone. -/
def evalConeZero :
    (Algebra.Extension.naiveComplex E).X 0 ⟶ (cotangentCone A B).X 0 :=
  (Algebra.Extension.naiveComplexXZeroIso E).hom ≫ evalCotangentSpace A B E hom ≫
    (cotangentComplexXZeroIso A B).inv ≫
    (CochainComplex.mappingCone.inr (conormalToCotangentComplex A B)).f 0

/-- The component of the evaluation in an arbitrary cohomological degree. -/
def evalConeComponent (i : ℤ) :
    (Algebra.Extension.naiveComplex E).X i ⟶ (cotangentCone A B).X i :=
  if h : i = -1 then
    eqToHom (by rw [h]) ≫ evalConeNegOne A B E hom ≫ eqToHom (by rw [h])
  else if h' : i = 0 then
    eqToHom (by rw [h']) ≫ evalConeZero A B E hom ≫ eqToHom (by rw [h'])
  else 0

/-- In degree `-1`, `evalConeComponent` is `evalConeNegOne`. -/
theorem evalConeComponent_negOne :
    evalConeComponent A B E hom (-1) = evalConeNegOne A B E hom := by
  simp [evalConeComponent]

/-- In degree `0`, `evalConeComponent` is `evalConeZero`. -/
theorem evalConeComponent_zero :
    evalConeComponent A B E hom 0 = evalConeZero A B E hom := by
  simp [evalConeComponent]

/-- In every degree other than `-1` and `0`, `evalConeComponent` vanishes. -/
theorem evalConeComponent_eq_zero (i : ℤ) (h : i ≠ -1) (h' : i ≠ 0) :
    evalConeComponent A B E hom i = 0 := by
  rw [evalConeComponent, dif_neg h, dif_neg h']

/-- **The evaluation at `U` of the two-term complex**, as a map of complexes into the cone of
`𝒥/𝒥² ⟶ Ω` on the standard resolution. In degree `-1` it is `J/J² ⟶ 𝒥₀/𝒥₀²` and in degree `0`
it is `Ω_{P/A} ⊗_P B ⟶ Ω_{P₀/A} ⊗_{P₀} B`, both induced by the chosen morphism of `U` into the
degree-zero term of the standard resolution. -/
def evalCone : Algebra.Extension.naiveComplex E ⟶ cotangentCone A B where
  f := evalConeComponent A B E hom
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases h1 : i = -1
    · have hj : j = 0 := by lia
      subst hj; subst h1
      rw [evalConeComponent_negOne, evalConeComponent_zero, evalConeNegOne, evalConeZero,
        Algebra.Extension.naiveComplex_d]
      rw [Category.assoc, Category.assoc, Category.assoc,
        CochainComplex.mappingCone.inl_v_d (conormalToCotangentComplex A B) 0 (-1) 1
          (by norm_num) (by norm_num),
        conormalComplex_d_zero_one, Limits.zero_comp, sub_zero,
        conormalToCotangentComplex_f_zero]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (evalCotangent A B E hom), evalCotangent_comp]
      simp [Category.assoc]
    · by_cases h2 : i = 0
      · have hj : j = 1 := by lia
        subst hj; subst h2
        exact (isZero_cotangentCone_X_one A B).eq_of_tgt _ _
      · exact (Algebra.Extension.isZero_naiveComplex_X E i h1 h2).eq_of_src _ _

/-- The degree-`i` component of `evalCone` is `evalConeComponent` at `i`. -/
theorem evalCone_f (i : ℤ) : (evalCone A B E hom).f i = evalConeComponent A B E hom i := rfl

/-- The degree `-1` component of `evalCone` is `evalConeNegOne`. -/
theorem evalCone_f_negOne : (evalCone A B E hom).f (-1) = evalConeNegOne A B E hom :=
  evalConeComponent_negOne A B E hom

/-- The degree `0` component of `evalCone` is `evalConeZero`. -/
theorem evalCone_f_zero : (evalCone A B E hom).f 0 = evalConeZero A B E hom :=
  evalConeComponent_zero A B E hom

/-! ### The comparison map -/

/-- **Stacks Project, Tag 08R9.** The comparison map

`(J/J² → Ω_{P/A} ⊗_P B) ⟶ τ_{≥ -1} L_{B/A}`

at the object `U = (P → B)` of `C_{B/A}`, built from a chosen morphism of `U` into the
degree-zero term `A[B] → B` of the standard resolution. It is the evaluation at `U` of the
two-term complex, followed by the truncation and by the identification
`τ_{≥ -1} Lπ_!(𝒥/𝒥² → Ω) = τ_{≥ -1} L_{B/A}` of Remark 08R7. -/
def comparisonOfHom :
    DerivedCategory.Q.obj (Algebra.Extension.naiveComplex E) ⟶
      (DerivedCategory.TStructure.t.truncGE (-1)).obj
        (DerivedCategory.Q.obj (cotangentComplex A B)) :=
  DerivedCategory.Q.map (evalCone A B E hom) ≫
    (DerivedCategory.TStructure.t.truncGEπ (-1)).app
      (DerivedCategory.Q.obj (cotangentCone A B)) ≫
    (truncGEConeIso A B).inv

/-- The equation that pins `Stacks.Cotangent.comparisonOfHom` down: composed with the
identification `τ_{≥ -1} L_{B/A} ≅ τ_{≥ -1} (𝒥/𝒥² → Ω)` of Remark 08R7 it is the evaluation at
`U`, followed by the truncation. -/
theorem comparisonOfHom_comp_truncGEConeIso :
    comparisonOfHom A B E hom ≫ (truncGEConeIso A B).hom =
      DerivedCategory.Q.map (evalCone A B E hom) ≫
        (DerivedCategory.TStructure.t.truncGEπ (-1)).app
          (DerivedCategory.Q.obj (cotangentCone A B)) := by
  rw [comparisonOfHom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Evaluation

/-! ### The comparison map at an object of `C_{B/A}` -/

/-- The morphism of `U = (P → B)` into the degree-zero term `A[B] → B` of the standard
resolution attached to a presentation of `P` by variables: a variable `x` goes to the variable
`[α x]` of `A[B]`. It exists because `P` is a polynomial `A`-algebra, that is, because `U` is an
object of `C_{B/A}`. -/
def toResolutionZero (E : Algebra.Extension.{max u v} A ↥B)
    (hP : Algebra.IsPolynomialAlgebra A E.Ring) :
    E.Hom (conormalExtension A B (op ⦋0⦌)) := by
  refine Algebra.Extension.Hom.ofAlgHom
    ((MvPolynomial.aeval (fun i : hP.choose => standardResolutionVarZero A B
        (algebraMap E.Ring ↥B (hP.choose_spec.some (MvPolynomial.X i))))).comp
      hP.choose_spec.some.symm.toAlgHom) ?_
  have key : ((IsScalarTower.toAlgHom A (conormalExtension A B (op ⦋0⦌)).Ring ↥B).comp
        ((MvPolynomial.aeval (fun i : hP.choose => standardResolutionVarZero A B
            (algebraMap E.Ring ↥B (hP.choose_spec.some (MvPolynomial.X i))))).comp
          hP.choose_spec.some.symm.toAlgHom)).comp hP.choose_spec.some.toAlgHom =
      (((IsScalarTower.toAlgHom A ↥B ↥B).comp
        (IsScalarTower.toAlgHom A E.Ring ↥B))).comp hP.choose_spec.some.toAlgHom := by
    refine MvPolynomial.algHom_ext fun i => ?_
    change algebraMap (conormalExtension A B (op ⦋0⦌)).Ring ↥B
        ((MvPolynomial.aeval (fun i : hP.choose => standardResolutionVarZero A B
            (algebraMap E.Ring ↥B (hP.choose_spec.some (MvPolynomial.X i)))))
          (hP.choose_spec.some.symm (hP.choose_spec.some (MvPolynomial.X i)))) =
      algebraMap E.Ring ↥B (hP.choose_spec.some (MvPolynomial.X i))
    rw [AlgEquiv.symm_apply_apply, MvPolynomial.aeval_X]
    exact standardResolution_augmentation_varZero A B _
  refine AlgHom.ext fun x => ?_
  obtain ⟨q, rfl⟩ := hP.choose_spec.some.surjective x
  exact AlgHom.congr_fun key q

/-- **Stacks Project, Tag 08R9.** The comparison map

`(J/J² → Ω_{P/A} ⊗_P B) ⟶ τ_{≥ -1} L_{B/A}`

in `D(B)`, at an object `U = (P → B)` of `C_{B/A}` with kernel `J`. It is the evaluation at `U`
of the two-term complex `𝒥/𝒥² → Ω` of Remark 08R7, followed by the identification
`τ_{≥ -1} Lπ_!(𝒥/𝒥² → Ω) = τ_{≥ -1} L_{B/A}` of that remark, both read on the standard
resolution. -/
@[stacks 08R9 "the displayed map (J/J² → Ω_{P/A} ⊗_P B) → τ_{≥ -1} L_{B/A} in D(B), at an \
  object (P → B) of C_{B/A}, with the source the two-term complex \
  Algebra.Extension.naiveComplex of that object and the target the degree ≥ -1 truncation of \
  the cotangent complex of Tag 08PN"]
def comparison (E : Algebra.Extension.{max u v} A ↥B)
    (hP : Algebra.IsPolynomialAlgebra A E.Ring) :
    DerivedCategory.Q.obj (Algebra.Extension.naiveComplex E) ⟶
      (DerivedCategory.TStructure.t.truncGE (-1)).obj
        (DerivedCategory.Q.obj (cotangentComplex A B)) :=
  comparisonOfHom A B E (toResolutionZero A B E hP)

/-- The comparison map is `Stacks.Cotangent.comparisonOfHom` at the morphism
`Stacks.Cotangent.toResolutionZero`. -/
theorem comparison_eq (E : Algebra.Extension.{max u v} A ↥B)
    (hP : Algebra.IsPolynomialAlgebra A E.Ring) :
    comparison A B E hP = comparisonOfHom A B E (toResolutionZero A B E hP) := rfl

/-- **Stacks Project, Tag 08R9 at the canonical presentation.** The comparison map

`NL_{B/A} = (I/I² → Ω_{A[B]⁄A} ⊗_{A[B]} B) ⟶ τ_{≥ -1} L_{B/A}`

at the object `A[B] → B` of `C_{B/A}`, that is, at the degree-zero term of the standard
resolution. This is the map `c` of Lemma 08RB; that it is a quasi-isomorphism is not proved
here. -/
def comparisonAtNaive :
    DerivedCategory.Q.obj
        (Algebra.Extension.naiveComplex (conormalExtension A B (op ⦋0⦌))) ⟶
      (DerivedCategory.TStructure.t.truncGE (-1)).obj
        (DerivedCategory.Q.obj (cotangentComplex A B)) :=
  comparison A B (conormalExtension A B (op ⦋0⦌))
    (isPolynomialAlgebra_conormalExtension_ring A B (op ⦋0⦌))

end Stacks.Cotangent

end
