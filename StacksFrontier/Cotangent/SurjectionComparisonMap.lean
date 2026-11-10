module

public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.Cotangent.NaiveComparisonQuasiIso

/-!
# The comparison map of Tag 08R9 at the object `(A → B)`, for a surjection `A → B`

Let `A → B` be a surjective ring map with kernel `I`. Tag 08RA asserts that `H⁰(L_{B/A}) = 0` and
`H^{-1}(L_{B/A}) = I/I²`, *the latter identification being the one induced by the comparison map
of Tag 08R9 at the object `(A → B)` of `C_{B/A}`*. This file proves that closing clause: the
comparison map at that object is an isomorphism on `H^{-1}`, so it produces the identification
itself.

The route is the one of `StacksFrontier/Cotangent/NaiveComparisonQuasiIso.lean`, which carries it
out
at the object `(A[B] → B)`. The two-term complex `NL(A → B)` is concentrated in cohomological
degree `-1`, where it is `I/I²`, because `Ω[A⁄A] = 0`; and the cone of `Ker(d) ⟶ 0` is likewise
concentrated there, where it is `Ker(d)` in simplicial degree `0`. The comparison between the two
is an isomorphism because `I/I²` is the whole first cotangent homology of the presentation
`A → B` (`CommAlgCat.surjectionH1CotangentEquiv`) and first cotangent homology does not depend on
the presentation (`Algebra.Extension.H1Cotangent.equiv`). So
`cone (Ker(d) ⟶ 0) ⟶ NL(A → B) ⟶ cone(d)` is an isomorphism on `H^{-1}` in its first factor and,
by `Stacks.Cotangent.isIso_homologyMap_kernelConeToCotangentCone`, in the composite.

## Main definitions

* `Stacks.Cotangent.surjectionToConormal`: the morphism of extensions `(A → B) ⟶ (Pₙ → B)`.
* `Stacks.Cotangent.kernelConeToNaiveSurjection`: the comparison
  `cone (Ker(d) ⟶ 0) ⟶ NL(A → B)`.
* `CommAlgCat.cotangentComplexHomologyNegOneIsoComparison`: **the identification
  `H^{-1}(L_{B/A}) ≅ I/I²` induced by the comparison map of Tag 08R9 at `(A → B)`.**

## Main results

* `Stacks.Cotangent.isIso_homologyMap_evalCone_surjectionExtension`: the evaluation at `(A → B)`
  of the two-term complex is an isomorphism on `H^{-1}`.
* `Stacks.Cotangent.isIso_homologyFunctor_map_comparison_surjectionExtension`: **the comparison
  map of Tag 08R9 at `(A → B)` is an isomorphism on `H^{-1}` in `D(B)`.**

## Implementation notes

The presentation `Pₙ → B` is `Stacks.Cotangent.conormalExtension`, not
`CommAlgCat.resolutionExtension`: the two have the same ring and the same augmentation but
different set-theoretic sections, so they are distinct terms, and the complexes of
`StacksFrontier/Cotangent/SurjectivePresentationHigherHomology.lean` — which carry no surjectivity
hypothesis — are built from the former. The morphism `(A → B) ⟶ (Pₙ → B)` and the comparison of
first cotangent homologies are therefore reproved here for `conormalExtension`, by the arguments
of `CommAlgCat.surjectionToResolution` and
`CommAlgCat.bijective_h1Cotangent_map_surjectionToResolution`. All the statements about a morphism
`(A → B) ⟶ (Pₙ → B)` hold for an arbitrary one, `Algebra.Extension.H1Cotangent.map_eq` making the
induced map on first cotangent homology independent of it.

`Stacks.Cotangent.evalSurjectionNegOne` is the degree `-1` component of the evaluation *before*
the inclusion into the `𝒥₀/𝒥₀²` summand of the cone, which is the shape in which it is a kernel of
`d` in simplicial degree `0`; `Stacks.Cotangent.isLimitKernelForkConormalKernelIota` says the same
of `Ker(d)` there, and `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso` turns the two into an
isomorphism compatible with both by construction, so no identification of the two descriptions has
to be made by hand afterwards.

## References

* [Stacks Project, Tag 08RA](https://stacks.math.columbia.edu/tag/08RA)
* [Stacks Project, Tag 08R9](https://stacks.math.columbia.edu/tag/08R9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

open scoped ZeroObject

universe u v

namespace Stacks.Cotangent

open CommAlgCat

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)
  (h : Function.Surjective (algebraMap A B))

/-! ### The presentation `A → B` against the standard resolution -/

/-- The presentation `A → B` is a polynomial algebra over `A`: it is `A` itself, universe-lifted,
which is the polynomial algebra on no variables. -/
theorem isPolynomialAlgebra_surjectionExtension_ring :
    Algebra.IsPolynomialAlgebra A (surjectionExtension A B h).Ring :=
  ⟨PEmpty.{max u v + 1}, ⟨(MvPolynomial.isEmptyAlgEquiv A PEmpty).trans
    (ULift.algEquiv (R := A) (A := A)).symm⟩⟩

/-- The canonical morphism from the presentation `A → B` to the `n`-th term of the standard
resolution, as a morphism of `Stacks.Cotangent.conormalExtension`. -/
def surjectionToConormal (n : SimplexCategoryᵒᵖ) :
    (surjectionExtension A B h).Hom (conormalExtension A B n) :=
  Algebra.Extension.Hom.ofAlgHom
    ((Algebra.ofId A ((standardResolution A B).left.obj n)).comp
      (ULift.algEquiv (R := A) (A := A)).toAlgHom) (by
    apply AlgHom.ext
    intro x
    have hx : x = algebraMap A (surjectionExtension A B h).Ring x.down := rfl
    rw [hx, AlgHom.commutes, AlgHom.commutes])

/-- Comparing the presentation `A → B` with a term of the standard resolution is a bijection on
first cotangent homology: the terms of the standard resolution are polynomial algebras, so they
receive a morphism from, and map to, every presentation of `B`. The statement is for an arbitrary
morphism, two morphisms inducing the same map. -/
theorem bijective_h1Cotangent_map_surjection (n : SimplexCategoryᵒᵖ)
    (hom : (surjectionExtension A B h).Hom (conormalExtension A B n)) :
    Function.Bijective (Algebra.Extension.H1Cotangent.map hom) := by
  rw [Algebra.Extension.H1Cotangent.map_eq hom (surjectionToConormal A B h n)]
  obtain ⟨ι, ⟨e⟩⟩ := standardResolution_obj_isPolynomialAlgebra A B n
  set P := conormalExtension A B n with hP
  set E := surjectionExtension A B h with hE
  have hrev : P.Hom E := Algebra.Extension.Hom.ofAlgHom
    ((MvPolynomial.aeval
        (fun i => E.σ (algebraMap P.Ring B (e (MvPolynomial.X i))))).comp
      e.symm.toAlgHom) (by
        have hh : ((IsScalarTower.toAlgHom A E.Ring B).comp
              ((MvPolynomial.aeval
                  (fun i => E.σ (algebraMap P.Ring B (e (MvPolynomial.X i))))).comp
                e.symm.toAlgHom)).comp e.toAlgHom =
            ((IsScalarTower.toAlgHom A B B).comp
              (IsScalarTower.toAlgHom A P.Ring B)).comp e.toAlgHom := by
          ext i
          simp [Algebra.Extension.algebraMap_σ]
          rfl
        refine AlgHom.ext fun p => ?_
        obtain ⟨q, rfl⟩ := e.surjective p
        exact AlgHom.congr_fun hh q)
  exact (Algebra.Extension.H1Cotangent.equiv (surjectionToConormal A B h n) hrev).bijective

/-- The conormal module of the presentation `A → B` maps to the conormal module of `Pₙ → B` by
the inclusion of the first cotangent homology, read through
`CommAlgCat.surjectionH1CotangentEquiv`: since `Ω[A⁄A] = 0`, the whole of `I/I²` is first
cotangent homology. -/
theorem cotangentMap_surjection_eq (n : SimplexCategoryᵒᵖ)
    (hom : (surjectionExtension A B h).Hom (conormalExtension A B n))
    (x : (surjectionExtension A B h).Cotangent) :
    Algebra.Extension.Cotangent.map hom x =
      (conormalExtension A B n).h1Cotangentι
        (Algebra.Extension.H1Cotangent.map hom
          ((surjectionH1CotangentEquiv A B h).symm x)) := by
  have key := LinearMap.congr_fun
    (Algebra.Extension.Cotangent.map_comp_h1Cotangentι hom)
    ((surjectionH1CotangentEquiv A B h).symm x)
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars] at key
  have hx : Algebra.Extension.h1Cotangentι ((surjectionH1CotangentEquiv A B h).symm x) = x :=
    (surjectionH1CotangentEquiv A B h).apply_symm_apply x
  rw [← key, hx]

/-- The comparison of conormal modules is injective: it is the inclusion of the first cotangent
homology of `Pₙ → B` precomposed with two bijections. -/
theorem injective_cotangentMap_surjection (n : SimplexCategoryᵒᵖ)
    (hom : (surjectionExtension A B h).Hom (conormalExtension A B n)) :
    Function.Injective (Algebra.Extension.Cotangent.map hom) := by
  intro x y hxy
  rw [cotangentMap_surjection_eq A B h n hom x, cotangentMap_surjection_eq A B h n hom y] at hxy
  exact (surjectionH1CotangentEquiv A B h).symm.injective
    ((bijective_h1Cotangent_map_surjection A B h n hom).1 (Subtype.ext hxy))

/-- The comparison of conormal modules hits every class killed by `d`: those classes are the
first cotangent homology of `Pₙ → B`, which the comparison reaches. -/
theorem exists_cotangentMap_surjection (n : SimplexCategoryᵒᵖ)
    (hom : (surjectionExtension A B h).Hom (conormalExtension A B n))
    (z : (conormalExtension A B n).Cotangent)
    (hz : (conormalExtension A B n).cotangentComplex z = 0) :
    ∃ x : (surjectionExtension A B h).Cotangent,
      Algebra.Extension.Cotangent.map hom x = z := by
  obtain ⟨y, hy⟩ := (bijective_h1Cotangent_map_surjection A B h n hom).2 ⟨z, hz⟩
  refine ⟨surjectionH1CotangentEquiv A B h y, ?_⟩
  rw [cotangentMap_surjection_eq A B h n hom,
    (surjectionH1CotangentEquiv A B h).symm_apply_apply, hy]
  rfl

/-! ### The two-term complex at `A → B` -/

/-- Since `Ω[A⁄A] = 0`, the differential of the two-term complex at `A → B` vanishes. -/
theorem surjectionExtension_cotangentComplex :
    (surjectionExtension A B h).cotangentComplex = 0 := by
  have := KaehlerDifferential.subsingleton_of_surjective A (surjectionExtension A B h).Ring
    (surjectionExtension_algebraMap_surjective A B h)
  exact Subsingleton.elim _ _

/-- The two-term complex at `A → B` vanishes in cohomological degree `0`, its term there being
`Ω[A⁄A] ⊗[A] B = 0`. -/
theorem isZero_naiveSurjection_X_zero :
    IsZero ((Algebra.Extension.naiveComplex (surjectionExtension A B h)).X 0) := by
  have := KaehlerDifferential.subsingleton_of_surjective A (surjectionExtension A B h).Ring
    (surjectionExtension_algebraMap_surjective A B h)
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of B (surjectionExtension A B h).CotangentSpace)).of_iso
      (Algebra.Extension.naiveComplexXZeroIso (surjectionExtension A B h))

/-- The differential of the two-term complex at `A → B` out of cohomological degree `-2`
vanishes, its source being zero. -/
theorem naiveSurjection_d_negTwo :
    (Algebra.Extension.naiveComplex (surjectionExtension A B h)).d (-2) (-1) = 0 :=
  (Algebra.Extension.isZero_naiveComplex_X (surjectionExtension A B h) (-2)
    (by decide) (by decide)).eq_of_src _ _

/-- The differential of the two-term complex at `A → B` out of cohomological degree `-1`
vanishes, its target being zero. -/
theorem naiveSurjection_d_negOne :
    (Algebra.Extension.naiveComplex (surjectionExtension A B h)).d (-1) 0 = 0 :=
  (isZero_naiveSurjection_X_zero A B h).eq_of_tgt _ _

/-- The cone of `Ker(d) ⟶ 0` vanishes in cohomological degree `0`. -/
theorem isZero_kernelCone_X_zero : IsZero ((kernelCone A B).X 0) := by
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨HomologicalComplex.isZero_extend_X _ _ 1
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff (0 : ℤ) 1).2 (by norm_num)),
    CochainComplex.mappingCone.isZero_zero_X 0⟩

/-- `d` in simplicial degree `0`, read off the cohomological degree `0` component of the map of
complexes. -/
theorem conormalToCotangentApp_eq :
    conormalToCotangentApp A B (op ⦋0⦌) =
      (conormalComplexXZeroIso A B).inv ≫ (conormalToCotangentComplex A B).f 0 ≫
        (cotangentComplexXZeroIso A B).hom := by
  rw [conormalToCotangentComplex_f_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### The evaluation at `A → B` in cohomological degree `-1` -/

section Evaluation

variable (hom : (surjectionExtension A B h).Hom (conormalExtension A B (op ⦋0⦌)))

/-- The evaluation of `𝒥/𝒥²` at `A → B` is killed by `d`, the differential of the two-term
complex at `A → B` vanishing. -/
theorem evalCotangent_comp_conormalToCotangentApp :
    evalCotangent A B (surjectionExtension A B h) hom ≫
      conormalToCotangentApp A B (op ⦋0⦌) = 0 := by
  rw [evalCotangent_comp, surjectionExtension_cotangentComplex, ModuleCat.ofHom_zero,
    Limits.zero_comp]

/-- The evaluation of `𝒥/𝒥²` at `A → B` is a monomorphism. -/
theorem mono_evalCotangent_surjection :
    Mono (evalCotangent A B (surjectionExtension A B h) hom) :=
  (ModuleCat.mono_iff_injective _).2 (injective_cotangentMap_surjection A B h (op ⦋0⦌) hom)

/-- `I/I² → 𝒥₀/𝒥₀² → Ω[P₀⁄A] ⊗[P₀] B` is exact: the classes killed by `d` are exactly the first
cotangent homology of `P₀ → B`, which `I/I²` reaches. -/
theorem exact_evalCotangent_surjection :
    (ShortComplex.mk (evalCotangent A B (surjectionExtension A B h) hom)
      (conormalToCotangentApp A B (op ⦋0⦌))
      (evalCotangent_comp_conormalToCotangentApp A B h hom)).Exact :=
  (ShortComplex.moduleCat_exact_iff _).2 fun z hz =>
    exists_cotangentMap_surjection A B h (op ⦋0⦌) hom z hz

/-- The evaluation of `𝒥/𝒥²` at `A → B` is a kernel of `d` in simplicial degree `0`. -/
def isLimitKernelForkEvalCotangentSurjection :
    IsLimit (KernelFork.ofι (evalCotangent A B (surjectionExtension A B h) hom)
      (evalCotangent_comp_conormalToCotangentApp A B h hom)) :=
  haveI := mono_evalCotangent_surjection A B h hom
  (exact_evalCotangent_surjection A B h hom).fIsKernel

/-- The degree `-1` component of the evaluation at `A → B`, before the inclusion into the
`𝒥₀/𝒥₀²` summand of the cone. -/
def evalSurjectionNegOne :
    (Algebra.Extension.naiveComplex (surjectionExtension A B h)).X (-1) ⟶
      (conormalComplex A B).X 0 :=
  (Algebra.Extension.naiveComplexXNegOneIso (surjectionExtension A B h)).hom ≫
    evalCotangent A B (surjectionExtension A B h) hom ≫ (conormalComplexXZeroIso A B).inv

/-- The degree `-1` component of the evaluation at `A → B` is that map followed by the inclusion
into the `𝒥₀/𝒥₀²` summand of the cone. -/
theorem evalCone_f_negOne_surjection :
    (evalCone A B (surjectionExtension A B h) hom).f (-1) =
      evalSurjectionNegOne A B h hom ≫
        (CochainComplex.mappingCone.inl (conormalToCotangentComplex A B)).v 0 (-1)
          (by norm_num) := by
  rw [evalCone_f_negOne, evalConeNegOne, evalSurjectionNegOne, Category.assoc, Category.assoc]

/-- The degree `-1` component of the evaluation at `A → B` is killed by `d` in cohomological
degree `0`. -/
theorem evalSurjectionNegOne_comp_d :
    evalSurjectionNegOne A B h hom ≫ (conormalToCotangentComplex A B).f 0 = 0 := by
  rw [evalSurjectionNegOne, conormalToCotangentComplex_f_zero, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, ← Category.assoc (evalCotangent A B (surjectionExtension A B h) hom),
    evalCotangent_comp_conormalToCotangentApp, Limits.zero_comp, Limits.comp_zero]

/-- The degree `-1` component of the evaluation at `A → B` is a monomorphism. -/
theorem mono_evalSurjectionNegOne : Mono (evalSurjectionNegOne A B h hom) := by
  have := mono_evalCotangent_surjection A B h hom
  rw [evalSurjectionNegOne]
  infer_instance

/-- The degree `-1` component of the evaluation at `A → B` is a kernel of `d` in cohomological
degree `0`: it is `Stacks.Cotangent.isLimitKernelForkEvalCotangentSurjection` read through the
identifications of the two degree-zero terms. -/
def isLimitKernelForkEvalSurjectionNegOne :
    IsLimit (KernelFork.ofι (evalSurjectionNegOne A B h hom)
      (evalSurjectionNegOne_comp_d A B h hom)) := by
  haveI := mono_evalSurjectionNegOne A B h hom
  refine KernelFork.IsLimit.ofι' _ _ (fun {T} c hc => ?_)
  have hc' : (c ≫ (conormalComplexXZeroIso A B).hom) ≫
      conormalToCotangentApp A B (op ⦋0⦌) = 0 := by
    rw [conormalToCotangentApp_eq]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hc, Limits.zero_comp]
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift'
    (isLimitKernelForkEvalCotangentSurjection A B h hom) _ hc'
  have hl' : l ≫ evalCotangent A B (surjectionExtension A B h) hom =
    c ≫ (conormalComplexXZeroIso A B).hom := hl
  refine ⟨l ≫ (Algebra.Extension.naiveComplexXNegOneIso
    (surjectionExtension A B h)).inv, ?_⟩
  rw [evalSurjectionNegOne, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, hl',
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **`Ker(d)` in simplicial degree `0` is the conormal module `I/I²` of the presentation
`A → B`.** Both are kernels of `d` in cohomological degree `0`, so the isomorphism between them is
compatible with the two inclusions by construction. -/
def conormalKernelXZeroIsoNaiveSurjection :
    (conormalKernelComplex A B).X 0 ≅
      (Algebra.Extension.naiveComplex (surjectionExtension A B h)).X (-1) :=
  IsLimit.conePointUniqueUpToIso (isLimitKernelForkConormalKernelIota A B)
    (isLimitKernelForkEvalSurjectionNegOne A B h hom)

/-- That isomorphism is compatible with the two inclusions into `𝒥₀/𝒥₀²`. -/
theorem conormalKernelXZeroIsoNaiveSurjection_hom_comp :
    (conormalKernelXZeroIsoNaiveSurjection A B h hom).hom ≫ evalSurjectionNegOne A B h hom =
      (conormalKernelIota A B).f 0 :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isLimitKernelForkConormalKernelIota A B)
    (isLimitKernelForkEvalSurjectionNegOne A B h hom) WalkingParallelPair.zero

/-- The degree `-1` component of the comparison from the cone of `Ker(d) ⟶ 0` into the two-term
complex at `A → B`: an isomorphism, both sides being `Ker(d)` in simplicial degree `0`. -/
def kernelConeToNaiveSurjectionNegOne :
    (kernelCone A B).X (-1) ⟶
      (Algebra.Extension.naiveComplex (surjectionExtension A B h)).X (-1) :=
  inv ((CochainComplex.mappingCone.inl
      (0 : conormalKernelComplex A B ⟶
        (0 : CochainComplex (ModuleCat.{max u v} B) ℤ))).v 0 (-1) (by norm_num)) ≫
    (conormalKernelXZeroIsoNaiveSurjection A B h hom).hom

/-- The map `kernelConeToNaiveSurjectionNegOne` is an isomorphism. -/
theorem isIso_kernelConeToNaiveSurjectionNegOne :
    IsIso (kernelConeToNaiveSurjectionNegOne A B h hom) := by
  rw [kernelConeToNaiveSurjectionNegOne]
  infer_instance

/-- The components of the comparison into the two-term complex at `A → B`: the isomorphism
`kernelConeToNaiveSurjectionNegOne` in degree `-1`, zero elsewhere. -/
def kernelConeToNaiveSurjectionComponent (i : ℤ) :
    (kernelCone A B).X i ⟶
      (Algebra.Extension.naiveComplex (surjectionExtension A B h)).X i :=
  if hi : i = -1 then
    eqToHom (by rw [hi]) ≫ kernelConeToNaiveSurjectionNegOne A B h hom ≫ eqToHom (by rw [hi])
  else 0

/-- In degree `-1`, `kernelConeToNaiveSurjectionComponent` is
`kernelConeToNaiveSurjectionNegOne`. -/
theorem kernelConeToNaiveSurjectionComponent_negOne :
    kernelConeToNaiveSurjectionComponent A B h hom (-1) =
      kernelConeToNaiveSurjectionNegOne A B h hom := by
  rw [kernelConeToNaiveSurjectionComponent, dite_eq_left rfl, eqToHom_refl, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- In every degree `i ≠ -1`, `kernelConeToNaiveSurjectionComponent` is zero. -/
theorem kernelConeToNaiveSurjectionComponent_eq_zero (i : ℤ) (hi : i ≠ -1) :
    kernelConeToNaiveSurjectionComponent A B h hom i = 0 := by
  rw [kernelConeToNaiveSurjectionComponent, dite_eq_right hi]

/-- **The comparison from the cone of `Ker(d) ⟶ 0` into the two-term complex at `A → B`.** -/
def kernelConeToNaiveSurjection :
    kernelCone A B ⟶ Algebra.Extension.naiveComplex (surjectionExtension A B h) where
  f := kernelConeToNaiveSurjectionComponent A B h hom
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases hj : j = -1
    · subst hj
      obtain rfl : i = -2 := by lia
      rw [kernelCone_d, Limits.zero_comp,
        kernelConeToNaiveSurjectionComponent_eq_zero A B h hom (-2) (by decide),
        Limits.zero_comp]
    · by_cases hj0 : j = 0
      · subst hj0
        obtain rfl : i = -1 := by lia
        rw [naiveSurjection_d_negOne, Limits.comp_zero,
          kernelConeToNaiveSurjectionComponent_eq_zero A B h hom 0 (by decide),
          Limits.comp_zero]
      · exact (Algebra.Extension.isZero_naiveComplex_X (surjectionExtension A B h) j hj
          hj0).eq_of_tgt _ _

/-- The degree `-1` component of `kernelConeToNaiveSurjection` is
`kernelConeToNaiveSurjectionNegOne`. -/
theorem kernelConeToNaiveSurjection_f_negOne :
    (kernelConeToNaiveSurjection A B h hom).f (-1) =
      kernelConeToNaiveSurjectionNegOne A B h hom :=
  kernelConeToNaiveSurjectionComponent_negOne A B h hom

/-- **The comparison from the cone of `Ker(d) ⟶ 0` into the two-term complex at `A → B` is an
isomorphism on `H^{-1}`.** Both complexes vanish in degree `0` and have no differential into
degree `-1`, and the comparison is an isomorphism there. -/
theorem isIso_homologyMap_kernelConeToNaiveSurjection :
    IsIso (HomologicalComplex.homologyMap (kernelConeToNaiveSurjection A B h hom) (-1)) := by
  refine HomologicalComplex.isIso_homologyMap_of_isIso_f_of_isZero
    (kernelConeToNaiveSurjection A B h hom) (-1) (-2) 0
    ((ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (-2) (-1) by norm_num))
    ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel (-1) 0 by norm_num))
    (isZero_kernelCone_X_zero A B) (isZero_naiveSurjection_X_zero A B h)
    (kernelCone_d A B) (naiveSurjection_d_negTwo A B h) ?_
  rw [kernelConeToNaiveSurjection_f_negOne]
  exact isIso_kernelConeToNaiveSurjectionNegOne A B h hom

/-- The degree `-1` components of `kernelConeToNaiveSurjection ≫ evalCone` and of
`kernelConeToCotangentCone` agree: both are the inclusion of `Ker(d)` in simplicial degree `0`
into the `𝒥₀/𝒥₀²` summand of the cone. The two chain maps themselves do not agree, the two-term
complex vanishing in degrees `≤ -2`. -/
theorem kernelConeToNaiveSurjection_comp_evalCone_f_negOne :
    (kernelConeToNaiveSurjection A B h hom ≫
        evalCone A B (surjectionExtension A B h) hom).f (-1) =
      (kernelConeToCotangentCone A B).f (-1) := by
  rw [HomologicalComplex.comp_f, kernelConeToNaiveSurjection_f_negOne,
    evalCone_f_negOne_surjection, kernelConeToNaiveSurjectionNegOne,
    ← cancel_epi ((CochainComplex.mappingCone.inl
      (0 : conormalKernelComplex A B ⟶
        (0 : CochainComplex (ModuleCat.{max u v} B) ℤ))).v 0 (-1) (by norm_num)),
    kernelConeToCotangentCone, CochainComplex.mappingCone.inl_v_mapFromZero_f]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, conormalKernelXZeroIsoNaiveSurjection_hom_comp A B h hom]

/-- **The evaluation at `(A → B)` of the two-term complex is an isomorphism on cohomology in
degree `-1`.** This is the closing clause of Tag 08RA at chain level: the comparison map of Tag
08R9 at the object `(A → B)` of `C_{B/A}` induces an isomorphism `I/I² ≅ H^{-1}(L_{B/A})`. -/
theorem isIso_homologyMap_evalCone_surjectionExtension :
    IsIso (HomologicalComplex.homologyMap
      (evalCone A B (surjectionExtension A B h) hom) (-1)) := by
  have hcomp : HomologicalComplex.homologyMap (kernelConeToNaiveSurjection A B h hom) (-1) ≫
      HomologicalComplex.homologyMap (evalCone A B (surjectionExtension A B h) hom) (-1) =
      HomologicalComplex.homologyMap (kernelConeToCotangentCone A B) (-1) := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact HomologicalComplex.homologyMap_congr (-1)
      (kernelConeToNaiveSurjection_comp_evalCone_f_negOne A B h hom)
  have := isIso_homologyMap_kernelConeToNaiveSurjection A B h hom
  have := isIso_homologyMap_kernelConeToCotangentCone A B
  exact IsIso.of_isIso_fac_left hcomp

end Evaluation

/-! ### The comparison map in `D(B)` -/

/-- **The comparison map of Tag 08R9 at the object `(A → B)` is an isomorphism on `H^{-1}`.**
It is the evaluation at `(A → B)` followed by the truncation and by the identification of Remark
08R7; the first is an isomorphism on `H^{-1}` by
`Stacks.Cotangent.isIso_homologyMap_evalCone_surjectionExtension`, the second by
`DerivedCategory.isIso_homologyFunctor_map_truncGEπ`, and the third is an isomorphism. -/
theorem isIso_homologyFunctor_map_comparison_surjectionExtension :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) (-1)).map
      (comparison A B (surjectionExtension A B h)
        (isPolynomialAlgebra_surjectionExtension_ring A B h))) := by
  rw [comparison_eq_comparisonOfHom A B (surjectionExtension A B h)
      (surjectionToConormal A B h (op ⦋0⦌)) (isPolynomialAlgebra_surjectionExtension_ring A B h),
    comparisonOfHom]
  have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) (-1)).map
      (DerivedCategory.Q.map (evalCone A B (surjectionExtension A B h)
        (surjectionToConormal A B h (op ⦋0⦌))))) :=
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B) (-1))
      (evalCone A B (surjectionExtension A B h)
        (surjectionToConormal A B h (op ⦋0⦌)))).2
      (isIso_homologyMap_evalCone_surjectionExtension A B h _)
  have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ (C := ModuleCat.{max u v} B)
    (-1) (-1) le_rfl (DerivedCategory.Q.obj (cotangentCone A B))
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

end Stacks.Cotangent

namespace CommAlgCat

open Stacks.Cotangent

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)
  (h : Function.Surjective (algebraMap A B))

/-- The degree `-1` cohomology of the two-term complex at `A → B` is its only term, the conormal
module `I/I²`: the complex is concentrated in that degree. -/
def naiveSurjectionHomologyNegOneIso :
    (Algebra.Extension.naiveComplex (surjectionExtension A B h)).homology (-1) ≅
      ModuleCat.of B (surjectionExtension A B h).Cotangent :=
  (Algebra.Extension.naiveComplex (surjectionExtension A B h)).isoHomologyι (-1) 0 (by simp)
      (naiveSurjection_d_negOne A B h) ≪≫
    ((Algebra.Extension.naiveComplex (surjectionExtension A B h)).pOpcyclesIso (-2) (-1)
      (by simp) (naiveSurjection_d_negTwo A B h)).symm ≪≫
    Algebra.Extension.naiveComplexXNegOneIso (surjectionExtension A B h)

/-- **Stacks Project, Tag 08RA.** For a surjective ring map `A → B` with kernel `I`, the
identification `H^{-1}(L_{B/A}) ≅ I/I²` *induced by the comparison map of Tag 08R9 at the object
`(A → B)` of `C_{B/A}`* — which is the identification the source's statement names.

Read from right to left it is: the conormal module `I/I²` is the degree `-1` cohomology of the
two-term complex `NL(A → B)`, that cohomology is carried into `H^{-1}(τ_{≥ -1} L_{B/A})` by the
comparison map, and `τ_{≥ -1}` changes no cohomology in degree `-1`. -/
@[stacks 08RA "the degree-minus-one conclusion H⁻¹(L_{B/A}) = I/I², with the isomorphism the one
induced by the comparison map of Tag 08R9 at the object (A → B) of C_{B/A}, which is the
identification the source's statement names"]
def cotangentComplexHomologyNegOneIsoComparison :
    (cotangentComplex A B).homology (-1) ≅
      ModuleCat.of B (surjectionExtension A B h).Cotangent :=
  haveI := isIso_homologyFunctor_map_comparison_surjectionExtension A B h
  haveI := DerivedCategory.isIso_homologyFunctor_map_truncGEπ (C := ModuleCat.{max u v} B)
    (-1) (-1) le_rfl (DerivedCategory.Q.obj (cotangentComplex A B))
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B) (-1)).app
      (cotangentComplex A B)).symm ≪≫
    asIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) (-1)).map
      ((DerivedCategory.TStructure.t.truncGEπ (-1)).app
        (DerivedCategory.Q.obj (cotangentComplex A B)))) ≪≫
    (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) (-1)).map
      (comparison A B (surjectionExtension A B h)
        (isPolynomialAlgebra_surjectionExtension_ring A B h)))).symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B) (-1)).app
      (Algebra.Extension.naiveComplex (surjectionExtension A B h)) ≪≫
    naiveSurjectionHomologyNegOneIso A B h

end CommAlgCat

end
