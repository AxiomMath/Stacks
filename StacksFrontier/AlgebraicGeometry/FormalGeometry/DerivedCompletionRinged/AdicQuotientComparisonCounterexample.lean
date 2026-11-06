module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientComparisonCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientTriangles
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.FiniteTypeReflector
public import StacksFrontier.CategoryTheory.Sites.Modules.PointAnnihilatorSequence
public import StacksFrontier.RingTheory.ShiftIdealization.Basic

/-!
# The comparison map of Tag 0CQH is not an isomorphism in general

Let `A` be a commutative ring and `x ∈ A` a non-unit together with elements `eₙ ∈ A` such that
`ann(xⁿ⁺¹) = eₙ A`, `ann(eₙ) = xⁿ⁺¹ A` and `x eₙ₊₁ = eₙ`. On the one-point ringed site of `A`,
with `ℐ = (x)` and `K = (𝒪/ℐ)[0]`, no map from the derived completion `K^∧` to a derived limit
of the reduction tower `n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` is an isomorphism; in particular the comparison map of
[Stacks, Tag 0CQH] is not. The ring `k[X] ⋉ k[X, X⁻¹]/k[X]` of `Stacks.ShiftIdealization`, for
any non-zero commutative ring `k`, is such an `A`, which gives the counterexample.

## Main results

* `AlgebraicGeometry.RingedSite.not_isIso_derivedCompletionComparison_of_periodic`: the
  statement for an `A` with periodic annihilators.
* `AlgebraicGeometry.RingedSite.not_isIso_derivedCompletionComparison_shiftIdealization`: the
  statement at `k[X] ⋉ k[X, X⁻¹]/k[X]`.

## Implementation notes

`K = (𝒪/ℐ)[0]` is derived complete, so `K^∧ = K` is a single complex and admits no non-zero
map from a complex concentrated in negative degrees. The reductions of `K` sit in two towers of
distinguished triangles, tensored up from the quotient sequences `0 → ℐⁿ⁺¹ → 𝒪 → 𝒪/ℐⁿ⁺¹ → 0`
and the annihilator sequences `0 → 𝒪/ℐⁿ⁺¹ --eₙ--> 𝒪 --xⁿ⁺¹--> ℐⁿ⁺¹ → 0`; the reduction maps
themselves are a non-zero compatible family of degree-`0` classes dying in `K` (since `eₙ ∈ ℐ`
kills `𝒪/ℐ`), and
`AlgebraicGeometry.RingedSite.not_isIso_derivedCompletionComparison_of_periodicPresentation`
carries them into degree `-2`, where they see the derived limit but not `K^∧`.

## References

* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.PointRingedSite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] hasProductsOfShape_nat_derivedCategory_ringSheaf

variable (A : Type u) [CommRing A] (x : A)

/-- The sheaf of ideals `(x)` on the one-point ringed site is of finite type. -/
instance isFiniteType_idealX : (idealX A x).toSheafOfModules.IsFiniteType :=
  isFiniteType_idealOfGlobalSections (site A) _

/-- The tower `n ↦ ℐⁿ⁺¹` of the positive powers of a sheaf of ideals, with the inclusions. -/
def idealPowTower
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)))) :
    ℕᵒᵖ ⥤ SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)) :=
  Functor.ofOpSequence
    (X := fun n : ℕ => (Stacks.Sites.idealPow I (n + 1)).toSheafOfModules)
    fun n : ℕ => Stacks.SheafOfModules.Submodule.homOfLE
      (Stacks.Sites.idealPow_antitone I (Nat.le_succ (n + 1)))

/-- The transition map `ℐⁿ⁺² → ℐⁿ⁺¹` of `idealPowTower` is the inclusion of sheaves of ideals. -/
theorem idealPowTower_map_succ
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)))) (n : ℕ) :
    (idealPowTower A I).map (homOfLE (Nat.le_succ n)).op =
      Stacks.SheafOfModules.Submodule.homOfLE
        (Stacks.Sites.idealPow_antitone I (Nat.le_succ (n + 1))) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The quotient sequence `0 → ℐⁿ → 𝒪 → 𝒪/ℐⁿ → 0` is short exact. -/
theorem shortExact_quotientSequence
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)))) (n : ℕ) :
    (ShortComplex.mk (Stacks.Sites.idealPow I n).ι
      (Stacks.Sites.adicQuotientModuleπ (X := site A) I n)
      (Stacks.Sites.ι_comp_adicQuotientModuleπ (X := site A) I n)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _) inferInstance
    (Stacks.Sites.epi_adicQuotientModuleπ (X := site A) I n)

/-- The map from the quotient sequence of `ℐⁿ⁺¹` to that of `ℐⁿ`. -/
def quotientSequenceMap
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)))) (n : ℕ) :
    ShortComplex.mk (Stacks.Sites.idealPow I (n + 1)).ι
        (Stacks.Sites.adicQuotientModuleπ (X := site A) I (n + 1))
        (Stacks.Sites.ι_comp_adicQuotientModuleπ (X := site A) I (n + 1)) ⟶
      ShortComplex.mk (Stacks.Sites.idealPow I n).ι
        (Stacks.Sites.adicQuotientModuleπ (X := site A) I n)
        (Stacks.Sites.ι_comp_adicQuotientModuleπ (X := site A) I n) where
  τ₁ := Stacks.SheafOfModules.Submodule.homOfLE (Stacks.Sites.idealPow_antitone I (Nat.le_succ n))
  τ₂ := 𝟙 _
  τ₃ := Stacks.Sites.adicQuotientModuleMap (X := site A) I (Nat.le_succ n)
  comm₁₂ := by
    change Stacks.SheafOfModules.Submodule.homOfLE _ ≫ (Stacks.Sites.idealPow I n).ι =
      (Stacks.Sites.idealPow I (n + 1)).ι ≫ 𝟙 _
    rw [Stacks.SheafOfModules.Submodule.homOfLE_comp_ι, Category.comp_id]
  comm₂₃ := by
    change 𝟙 _ ≫ Stacks.Sites.adicQuotientModuleπ (X := site A) I n =
      Stacks.Sites.adicQuotientModuleπ (X := site A) I (n + 1) ≫
        Stacks.Sites.adicQuotientModuleMap (X := site A) I (Nat.le_succ n)
    rw [Category.id_comp]
    exact (Stacks.Sites.adicQuotientModuleπ_comp_adicQuotientModuleMap (X := site A) I
      (Nat.le_succ n)).symm

/-- **The comparison map of [Stacks, Tag 0CQH] fails to be an isomorphism at a ring with periodic
annihilators.** Let `x ∈ A` be a non-unit and `eₙ ∈ A` with `ann(xⁿ⁺¹) = eₙ A`,
`ann(eₙ) = xⁿ⁺¹ A` and `x eₙ₊₁ = eₙ`. On the one-point ringed site of `A`, with `ℐ = (x)` and
`K = (𝒪/ℐ)[0]`, no map `K^∧ ⟶ L` into a derived limit `L` of the reduction tower
`n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` is an isomorphism. -/
theorem not_isIso_derivedCompletionComparison_of_periodic (e : ℕ → A)
    (hx : (1 : A) ∉ Ideal.span {x})
    (h1 : ∀ n, e n * x ^ (n + 1) = 0)
    (h2 : ∀ n (a : A), x ^ (n + 1) * a = 0 → ∃ c, a = c * e n)
    (h3 : ∀ n (a : A), e n * a = 0 → ∃ c, a = x ^ (n + 1) * c)
    (he : ∀ n, x * e (n + 1) = e n)
    {L : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)))}
    {p : L ⟶ ∏ᶜ fun n : ℕ => (adicReductionTower (site A) (idealX A x)
        (adicQuotientObj (site A) (idealX A x) 1)).obj ⟨n⟩}
    {δ : (∏ᶜ fun n : ℕ => (adicReductionTower (site A) (idealX A x)
        (adicQuotientObj (site A) (idealX A x) 1)).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧}
    (htri : Triangle.mk p (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => (adicReductionTower (site A) (idealX A x)
          (adicQuotientObj (site A) (idealX A x) 1)).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => (adicReductionTower (site A) (idealX A x)
            (adicQuotientObj (site A) (idealX A x) 1)).obj ⟨n⟩) (n + 1) ≫
            (adicReductionTower (site A) (idealX A x)
              (adicQuotientObj (site A) (idealX A x) 1)).map (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang (DerivedCategory
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)))))
    (c : (derivedCompletion (site A) (idealX A x)).obj
        (adicQuotientObj (site A) (idealX A x) 1) ⟶ L) :
    ¬ IsIso c := by
  let I := idealX A x
  let M := Stacks.Sites.adicQuotientModule (X := site A) I 1
  let K := adicQuotientObj (site A) I 1
  let F := (Stacks.SheafOfModules.derivedTensorProductFunctor (site A)).obj K
  let ε := (Stacks.SheafOfModules.canonicalDerivedTensorProduct (site A)).unitIso K
  let J := idealPowTower A I ⋙
    DerivedCategory.singleFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O))) 0 ⋙ F
  have hS₁ := fun n : ℕ => shortExact_quotientSequence A I (n + 1)
  have hS₂ := fun n : ℕ =>
    annihilatorShortComplex_shortExact x (e n) (n + 1) (h1 n) (h2 n) (h3 n)
  have hmap : ∀ (T : ℕᵒᵖ ⥤ SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)))
      (n : ℕ) (f : T.obj ⟨n + 1⟩ ⟶ T.obj ⟨n⟩), T.map (homOfLE (Nat.le_succ n)).op = f →
      (T ⋙ DerivedCategory.singleFunctor _ 0 ⋙ F).map (homOfLE (Nat.le_succ n)).op =
        F.map ((DerivedCategory.singleFunctor _ 0).map f) := by
    rintro T n f rfl
    rfl
  have hmemI : ∀ n, toO A (e n) ∈ Ideal.span {toO A x ^ 1} := fun n =>
    Ideal.mem_span_singleton'.2 ⟨toO A (e (n + 1)),
      (by rw [pow_one, mul_comm]; exact he n : e (n + 1) * x ^ 1 = e n)⟩
  have ha : ∀ n, (mulEnd A (e n)).asHom.app M = 0 := fun n =>
    Stacks.Sites.globalSectionToEnd_app_adicQuotientModule_eq_zero I 1 (constFamily A (e n))
      fun U => by
        obtain rfl := eq_op_pt A U
        exact (mem_idealPow_iff A x 1 (e n)).2 (hmemI n)
  refine not_isIso_derivedCompletionComparison_of_periodicPresentation (site A) I M
    (isDerivedComplete_adicQuotientObj (site A) I 1) M J
    (fun n => F.map ((DerivedCategory.singleFunctor _ 0).map
      (annihilatorα x (e n) (n + 1) (h1 n))) ≫ ε.hom)
    (fun n => ε.inv ≫ F.map ((DerivedCategory.singleFunctor _ 0).map (annihilatorβ x (n + 1))))
    (fun n => tensorShortExactδ (site A) K (hS₂ n))
    (fun n => tensorShortExact_distinguished (site A) K (hS₂ n)) ?_
    (fun n => F.map ((DerivedCategory.singleFunctor _ 0).map
      (Stacks.Sites.idealPow I (n + 1)).ι) ≫ ε.hom)
    (fun n => ε.inv ≫ F.map ((DerivedCategory.singleFunctor _ 0).map
      (Stacks.Sites.adicQuotientModuleπ (X := site A) I (n + 1))))
    (fun n => tensorShortExactδ (site A) K (hS₁ n))
    (fun n => tensorShortExact_distinguished (site A) K (hS₁ n)) ?_
    (fun n => adicQuotientReduction (site A) I K (n + 1))
    (fun n => adicQuotientReduction_comp_eq_zero (site A) I M (n + 1) _ (constFamily A (e n))
      (adicQuotientModuleπ_comp_annihilatorα x (e n) (n + 1) (h1 n)) (ha n))
    (adicQuotientReduction_comp_adicReductionTower_map_succ (site A) I K) (m := 0) ?_ htri c
  · intro n
    rw [hmap _ n _ (idealPowTower_map_succ A I n),
      hmap _ n _ (adicQuotientTower_map_succ (site A) I n)]
    exact (tensorShortExactδ_naturality (site A) K (hS₂ (n + 1)) (hS₂ n)
      (annihilatorShortComplexMap x (e n) (n + 1) (h1 n) (e (n + 1)) (h1 (n + 1)) (he n))).symm
  · intro n
    rw [hmap _ n _ (idealPowTower_map_succ A I n),
      hmap _ n _ (adicQuotientTower_map_succ (site A) I n)]
    exact (tensorShortExactδ_naturality (site A) K (hS₁ (n + 1)) (hS₁ n)
      (quotientSequenceMap A I (n + 1))).symm
  · intro h0
    have hsplit := isSplitMono_adicQuotientReduction_single (site A) I M 1
      (fun U a ha g => Stacks.Sites.smul_adicQuotientModule_eq_zero I 1 U a ha g)
    obtain ⟨⟨r, hr⟩⟩ := hsplit
    have hK : IsZero K := by
      rw [IsZero.iff_id_eq_zero, ← hr]
      rw [show adicQuotientReduction (site A) I K 1 = 0 from h0, zero_comp]
    refine not_isZero_adicQuotientModule_one x hx ((IsZero.iff_id_eq_zero M).2 ?_)
    refine (DerivedCategory.singleFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (site A).O))) 0).map_injective ?_
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact hK.eq_of_src _ _

/-- **The comparison map of [Stacks, Tag 0CQH] fails to be an isomorphism at
`k[X] ⋉ k[X, X⁻¹]/k[X]`.** For a non-zero commutative ring `k`, on the one-point ringed site of
`A = k[X] ⋉ k[X, X⁻¹]/k[X]`, with `ℐ = (X)` and `K = (𝒪/ℐ)[0]`, no map `K^∧ ⟶ L` into a derived
limit `L` of the reduction tower `n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` is an isomorphism. -/
theorem not_isIso_derivedCompletionComparison_shiftIdealization (k : Type u) [CommRing k]
    [Nontrivial k]
    {L : DerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (site (Stacks.ShiftIdealization.Ring k)).O)))}
    {p : L ⟶ ∏ᶜ fun n : ℕ => (adicReductionTower (site (Stacks.ShiftIdealization.Ring k))
        (idealX _ (Stacks.ShiftIdealization.x k))
        (adicQuotientObj (site _) (idealX _ (Stacks.ShiftIdealization.x k)) 1)).obj ⟨n⟩}
    {δ : (∏ᶜ fun n : ℕ => (adicReductionTower (site (Stacks.ShiftIdealization.Ring k))
        (idealX _ (Stacks.ShiftIdealization.x k))
        (adicQuotientObj (site _) (idealX _ (Stacks.ShiftIdealization.x k)) 1)).obj ⟨n⟩) ⟶
          L⟦(1 : ℤ)⟧}
    (htri : Triangle.mk p (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => (adicReductionTower (site (Stacks.ShiftIdealization.Ring k))
          (idealX _ (Stacks.ShiftIdealization.x k))
          (adicQuotientObj (site _) (idealX _ (Stacks.ShiftIdealization.x k)) 1)).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => (adicReductionTower (site (Stacks.ShiftIdealization.Ring k))
            (idealX _ (Stacks.ShiftIdealization.x k))
            (adicQuotientObj (site _) (idealX _ (Stacks.ShiftIdealization.x k)) 1)).obj ⟨n⟩)
              (n + 1) ≫
            (adicReductionTower (site (Stacks.ShiftIdealization.Ring k))
              (idealX _ (Stacks.ShiftIdealization.x k))
              (adicQuotientObj (site _) (idealX _ (Stacks.ShiftIdealization.x k)) 1)).map
                (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang _)
    (c : (derivedCompletion (site (Stacks.ShiftIdealization.Ring k))
        (idealX _ (Stacks.ShiftIdealization.x k))).obj
        (adicQuotientObj (site _) (idealX _ (Stacks.ShiftIdealization.x k)) 1) ⟶ L) :
    ¬ IsIso c :=
  not_isIso_derivedCompletionComparison_of_periodic (Stacks.ShiftIdealization.Ring k)
    (Stacks.ShiftIdealization.x k) (Stacks.ShiftIdealization.e k)
    Stacks.ShiftIdealization.one_not_mem_span_x
    (fun n => by rw [mul_comm]; exact Stacks.ShiftIdealization.x_pow_mul_e n)
    (fun n _ => Stacks.ShiftIdealization.exists_eq_mul_e_of_x_pow_mul_eq_zero n)
    (fun n _ => Stacks.ShiftIdealization.exists_eq_x_pow_mul_of_e_mul_eq_zero n)
    Stacks.ShiftIdealization.x_mul_e_succ htri c

end AlgebraicGeometry.RingedSite
