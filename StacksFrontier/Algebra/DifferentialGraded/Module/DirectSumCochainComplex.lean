module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryCoproducts

/-! # The cochain complex underlying a direct sum of differential graded modules

Let `(A, d)` be a differential graded algebra over a commutative ring `R` and let `Nᵢ` be a
family of right differential graded `A`-modules. The forgetful functor
`DifferentialGradedModule.forgetToCochainComplex` to cochain complexes of `R`-modules preserves
direct sums: the cochain complex underlying `⨁ᵢ Nᵢ` is the coproduct of the cochain complexes
underlying the summands.

The content is one degreewise identification. The degree-`n` part of `⨁ᵢ Nᵢ` is by construction
the submodule `{x ∈ ⨁ᵢ (Nᵢ).M | ∀ i, xᵢ ∈ (Nᵢ)ⁿ}` of the direct sum of the carriers, and the
claim is that this submodule *is* `⨁ᵢ (Nᵢ)ⁿ`. Mathlib has no statement of that shape for a
family of submodules, so it is proved here: the comparison is the descent of the inclusions
`(Nᵢ)ⁿ ↪ ⨁ᵢ (Nᵢ).M`, and it is injective because it is componentwise an inclusion and
surjective because an element of a direct sum has finite support.

## Main definitions

* `DifferentialGradedModule.directSumGradingEquiv`: the degreewise identification
  `⨁ᵢ (Nᵢ)ⁿ ≃ (⨁ᵢ Nᵢ)ⁿ`.
* `DifferentialGradedModule.isColimitCofanToCochainComplex`: the cochain complexes underlying
  the summands, with the cochain maps underlying the coprojections, exhibit the cochain complex
  underlying `⨁ᵢ Nᵢ` as their coproduct.
* `DifferentialGradedModule.directSumObjToCochainComplexIso`: the same statement read against
  the chosen coproduct, `(⨁ᵢ Nᵢ)^• ≅ ∐ᵢ (Nᵢ)^•`.

## Main results

* `DifferentialGradedModule.forgetToCochainComplex_preservesCoproducts`:
  `DifferentialGradedModule.forgetToCochainComplex` preserves direct sums.

## Implementation notes

*Why the degreewise step is phrased with `IsColimit.ofExistsUnique`.* The cocone produced by
`Functor.mapCocone` from a `Cofan` is a cocone over `Discrete.functor _ ⋙ F`, which is not
syntactically a `Cofan`, so `Cofan.IsColimit.mk` does not apply to it directly. Mathlib's
`CategoryTheory.Limits.Cofan.isColimitMapCoconeEquiv` is the bridge, and it asks for the
`IsColimit` of a genuine `Cofan` whose injections are the images of the original ones; that is
what is built here, by `Cofan.IsColimit.mk`, with `HomologicalComplex.isColimitOfEval` assembling
the degreewise statements into the statement about complexes.

*Why the comparison is built over the bare direct sum.* As in
`StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryCoproducts`, the carrier of
`DifferentialGradedModule.directSumObj` is `⨁ᵢ (Nᵢ).M` only up to unfolding at default
transparency. So the descent, its componentwise description and its membership in the degree-`n`
part are all stated over `⨁ᵢ (Nᵢ).M` and `DifferentialGradedModule.directSumGrading`, and only
the final equivalence is read against `(⨁ᵢ Nᵢ)ⁿ`.

## References

* [Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI), the forgetful functor.
* [Stacks Project, Tag 09JJ](https://stacks.math.columbia.edu/tag/09JJ), direct sums of
  differential graded modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

section DirectSumGrading

variable {ι : Type u} [DecidableEq ι] (N : ι → DifferentialGradedModule A)

/-- The descent of the inclusions `(Nᵢ)ⁿ ↪ ⨁ᵢ (Nᵢ).M` of the degree-`n` parts of the summands,
as a linear map out of `⨁ᵢ (Nᵢ)ⁿ` at the honest type. -/
def directSumGradingDescLinear (n : ℤ) :
    (⨁ i, ((N i).grading n)) →ₗ[R] (⨁ i, (N i).M) :=
  DirectSum.toModule R ι _
    (fun i => (DirectSum.lof R ι (fun i => (N i).M) i).comp ((N i).grading n).subtype)

/-- The descent reads off the inclusion on the `i`-th summand. -/
theorem directSumGradingDescLinear_lof (n : ℤ) (i : ι) (y : (N i).grading n) :
    directSumGradingDescLinear N n (DirectSum.lof R ι (fun i => ((N i).grading n)) i y)
      = DirectSum.lof R ι (fun i => (N i).M) i (y : (N i).M) :=
  DirectSum.toModule_lof (R := R)
    (φ := fun i => (DirectSum.lof R ι (fun i => (N i).M) i).comp ((N i).grading n).subtype) i y

/-- The descent acts componentwise: the `j`-th component of the image is the `j`-th component of
the argument, read inside `(N j).M`. -/
theorem directSumGradingDescLinear_apply (n : ℤ) (z : ⨁ i, ((N i).grading n)) (j : ι) :
    directSumGradingDescLinear N n z j = ((z j : (N j).grading n) : (N j).M) := by
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
  | of i y =>
      rw [← DirectSum.lof_eq_of (R := R), directSumGradingDescLinear_lof,
        DirectSum.lof_eq_of (R := R), DirectSum.lof_eq_of (R := R)]
      by_cases h : j = i
      · subst h; simp
      · simp only [DirectSum.of_eq_of_ne _ _ _ h, ZeroMemClass.coe_zero]
  | add z w hz hw =>
      simp only [map_add, DirectSum.add_apply, hz, hw, AddMemClass.coe_add]

/-- The image of the descent is homogeneous of degree `n`. -/
theorem directSumGradingDescLinear_mem (n : ℤ) (z : ⨁ i, ((N i).grading n)) :
    directSumGradingDescLinear N n z ∈ directSumGrading N n := by
  intro j
  rw [directSumGradingDescLinear_apply]
  exact (z j).property

/-- The descent is injective: it is componentwise the inclusion of a submodule. -/
theorem directSumGradingDescLinear_injective (n : ℤ) :
    Function.Injective (directSumGradingDescLinear N n) := by
  intro z w h
  refine DirectSum.ext (fun j => Subtype.ext ?_)
  rw [← directSumGradingDescLinear_apply N n z j, ← directSumGradingDescLinear_apply N n w j, h]

/-- Every homogeneous element of degree `n` of `⨁ᵢ (Nᵢ).M` is in the image of the descent: it has
finite support, and on each component of the support it is homogeneous of degree `n`. -/
theorem exists_directSumGradingDescLinear_eq (n : ℤ) (x : ⨁ i, (N i).M)
    (hx : ∀ i, x i ∈ (N i).grading n) :
    ∃ z : ⨁ i, ((N i).grading n), directSumGradingDescLinear N n z = x := by
  classical
  refine ⟨∑ j ∈ x.support, DirectSum.lof R ι (fun i => ((N i).grading n)) j ⟨x j, hx j⟩, ?_⟩
  calc directSumGradingDescLinear N n
          (∑ j ∈ x.support, DirectSum.lof R ι (fun i => ((N i).grading n)) j ⟨x j, hx j⟩)
      = ∑ j ∈ x.support, DirectSum.of (fun i => (N i).M) j (x j) := by
        rw [map_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [directSumGradingDescLinear_lof, DirectSum.lof_eq_of (R := R)]
    _ = x := DirectSum.sum_support_of x

/-- **The degree-`n` part of `⨁ᵢ Nᵢ` is `⨁ᵢ (Nᵢ)ⁿ`.** Homogeneity in a direct sum is
componentwise, so the degree-`n` part is the submodule of `⨁ᵢ (Nᵢ).M` of elements all of whose
components are homogeneous of degree `n`; the descent of the inclusions of the degree-`n` parts
of the summands identifies it with their direct sum. -/
def directSumGradingEquiv (n : ℤ) :
    (⨁ i, ((N i).grading n)) ≃ₗ[R] directSumGrading N n :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (directSumGrading N n) (directSumGradingDescLinear N n)
      (directSumGradingDescLinear_mem N n))
    ⟨fun z w h => directSumGradingDescLinear_injective N n (congrArg Subtype.val h),
      fun x => by
        obtain ⟨z, hz⟩ := exists_directSumGradingDescLinear_eq N n (x : ⨁ i, (N i).M) x.property
        exact ⟨z, Subtype.ext hz⟩⟩

/-- The identification carries the `i`-th coprojection of `⨁ᵢ (Nᵢ)ⁿ` to the `i`-th coprojection
of `⨁ᵢ Nᵢ`, restricted to degree `n`. -/
theorem directSumGradingEquiv_lof (n : ℤ) (i : ι) (y : (N i).grading n) :
    directSumGradingEquiv N n (DirectSum.lof R ι (fun i => ((N i).grading n)) i y)
      = (directSumInj N i).gradedMap n y :=
  Subtype.ext (directSumGradingDescLinear_lof N n i y)

/-- The inverse identification carries the `i`-th coprojection of `⨁ᵢ Nᵢ`, restricted to degree
`n`, to the `i`-th coprojection of `⨁ᵢ (Nᵢ)ⁿ`. -/
theorem directSumGradingEquiv_symm_gradedMap (n : ℤ) (i : ι) (y : (N i).grading n) :
    (directSumGradingEquiv N n).symm ((directSumInj N i).gradedMap n y)
      = DirectSum.lof R ι (fun i => ((N i).grading n)) i y :=
  (directSumGradingEquiv N n).symm_apply_eq.2 (directSumGradingEquiv_lof N n i y).symm

end DirectSumGrading

/-! ### The coproduct of the underlying cochain complexes -/

section Cofan

variable {ι : Type u} [DecidableEq ι] (N : ι → DifferentialGradedModule A)

/-- The degree-`n` parts of the summands, with the degree-`n` parts of the coprojections, exhibit
the degree-`n` part of `⨁ᵢ Nᵢ` as their coproduct in `ModuleCat R`. This is
`DifferentialGradedModule.directSumGradingEquiv` together with the universal property of a direct
sum of modules. -/
def isColimitCofanEvalToCochainComplex (n : ℤ) :
    IsColimit (Cofan.mk ((directSumObj N).toCochainComplex.X n)
      (fun i => (directSumInj N i).toCochainMap.f n)) := by
  refine Cofan.IsColimit.mk _
    (fun t => ModuleCat.ofHom
      ((DirectSum.toModule R ι t.pt (fun i => (t.inj i).hom)).comp
        (directSumGradingEquiv N n).symm.toLinearMap)) (fun t i => ?_) (fun t m hm => ?_)
  · refine ModuleCat.hom_ext (LinearMap.ext fun (y : (N i).grading n) => ?_)
    exact (congrArg (DirectSum.toModule R ι t.pt (fun i => (t.inj i).hom))
        (directSumGradingEquiv_symm_gradedMap N n i y)).trans
      (DirectSum.toModule_lof (R := R) (φ := fun i => (t.inj i).hom) i y)
  · have key : m.hom.comp (directSumGradingEquiv N n).toLinearMap
        = DirectSum.toModule R ι t.pt (fun i => (t.inj i).hom) := by
      refine DirectSum.linearMap_ext R (fun i => LinearMap.ext fun y => ?_)
      have hmi := congrArg
        (fun f : ModuleCat.of R ((N i).grading n) ⟶ t.pt => f.hom y) (hm i)
      refine Eq.trans ?_ (DirectSum.toModule_lof (R := R)
        (φ := fun i => (t.inj i).hom) i y).symm
      exact (congrArg m.hom (directSumGradingEquiv_lof N n i y)).trans hmi
    refine ModuleCat.hom_ext (LinearMap.ext fun (x : directSumGrading N n) => ?_)
    have hx := congrArg (fun f : _ →ₗ[R] t.pt => f ((directSumGradingEquiv N n).symm x)) key
    exact ((congrArg m.hom ((directSumGradingEquiv N n).apply_symm_apply x)).symm.trans hx)

/-- **The cochain complex underlying `⨁ᵢ Nᵢ` is the coproduct of the cochain complexes underlying
the summands.** Coproducts of complexes are computed degreewise
(`HomologicalComplex.isColimitOfEval`), and in degree `n` the statement is
`DifferentialGradedModule.isColimitCofanEvalToCochainComplex`. -/
def isColimitCofanToCochainComplex :
    IsColimit (Cofan.mk ((directSumObj N).toCochainComplex)
      (fun i => (directSumInj N i).toCochainMap)) :=
  HomologicalComplex.isColimitOfEval _ _ (fun n =>
    (Cofan.isColimitMapCoconeEquiv
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n)
      (fun i => (N i).toCochainComplex)
      (Cofan.mk ((directSumObj N).toCochainComplex)
        (fun i => (directSumInj N i).toCochainMap))).symm
      (isColimitCofanEvalToCochainComplex N n))

/-- The cochain complex underlying `⨁ᵢ Nᵢ` is the chosen coproduct of the cochain complexes
underlying the summands. -/
def directSumObjToCochainComplexIso :
    (directSumObj N).toCochainComplex ≅ ∐ fun i => (N i).toCochainComplex :=
  (isColimitCofanToCochainComplex N).coconePointUniqueUpToIso (coproductIsCoproduct _)

end Cofan

/-- **The forgetful functor to cochain complexes of `R`-modules preserves direct sums.** For a
family `Nᵢ` of right differential graded `A`-modules the explicit direct sum `⨁ᵢ Nᵢ` is a
coproduct in `Mod_{(A,d)}` (`DifferentialGradedModule.isColimit_directSumObj`) and its underlying
cochain complex is a coproduct of the underlying cochain complexes
(`DifferentialGradedModule.isColimitCofanToCochainComplex`); an arbitrary discrete diagram is
reduced to that case by `CategoryTheory.Discrete.natIsoFunctor`. -/
instance forgetToCochainComplex_preservesCoproducts (A : DifferentialGradedAlgebra R)
    (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι) (forgetToCochainComplex.{u, u, u} A) := by
  classical
  have key : ∀ N : ι → DifferentialGradedModule A,
      PreservesColimit (Discrete.functor N) (forgetToCochainComplex A) := by
    intro N
    refine preservesColimit_of_preserves_colimit_cocone (isColimit_directSumObj N) ?_
    exact (Cofan.isColimitMapCoconeEquiv (forgetToCochainComplex A) N
      (Cofan.mk (directSumObj N) (directSumInj N))).symm
      (isColimitCofanToCochainComplex N)
  refine ⟨fun {F} => ?_⟩
  have := key (F.obj ∘ Discrete.mk)
  exact preservesColimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := F)).symm

end DifferentialGradedModule

end
