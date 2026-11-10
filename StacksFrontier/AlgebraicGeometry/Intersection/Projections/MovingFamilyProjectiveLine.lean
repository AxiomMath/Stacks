module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyMain

/-!
# The Moving Lemma for a closed `X`: a family over a projective line

For `C, X ⊆ 𝐏^N` closed subvarieties which intersect properly and `T i ⊆ X` a finite collection of
closed subvarieties there is a closed subvariety `C' ⊆ 𝐏^N × 𝐏^1` with

1. `C' → 𝐏^1` dominant;
2. `C'_0 = C` as sets;
3. `C'` and `X × 𝐏^1` intersect properly;
4. `C'_∞` properly intersects each `T i`.

Here `𝐏^1` is the projective space of a two-dimensional vector space.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.intersectProperly_of_eq_univ`: the whole of a
  scheme intersects every closed subvariety of it properly.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_movingFamily_over_projectiveLine_of_eq_univ`:
  the four clauses for `C = 𝐏(V)`, satisfied by the constant family `𝐏(V) × 𝐏^1`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_movingFamily_over_projectiveLine`: the four
  clauses for a closed `X`, with clause (2) read on the underlying sets.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

/-- The whole of a scheme intersects every closed subvariety of it properly. -/
public theorem intersectProperly_of_eq_univ {Y : Scheme.{u}} (A Z : IrreducibleCloseds Y)
    (hA : (A : Set Y) = Set.univ) : IntersectProperly A Z := by
  have hdim : topologicalKrullDim ↥(A : Set Y) = topologicalKrullDim Y := by
    rw [hA]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph
  have hint : (A : Set Y) ∩ (Z : Set Y) = (Z : Set Y) := by rw [hA, Set.univ_inter]
  rw [intersectProperly_iff, hint, hdim]
  exact (add_comm _ _).le

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]

/-- The projection of `𝐏(W) × 𝐏(V)` to `𝐏(W)` has dense image. -/
public theorem closure_image_lineProductLine_univ (W : Type u) [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] [Nontrivial W] :
    closure ((lineProductLine k V W).base '' (Set.univ : Set (lineProduct k V W))) =
      Set.univ := by
  refine closure_eq_univ_of_closedPoints_subset fun lam hlam => ?_
  refine mem_image_lineProductLine_of_lineProductFibre_nonempty k V W lam
    (mem_closedPoints_iff.mp hlam) ?_
  rw [lineProductFibre_univ]
  exact Set.univ_nonempty

omit [IsAlgClosed k] in
/-- A nontrivial vector space carries a nonzero linear functional. -/
private theorem exists_dual_ne_zero_of_nontrivial (W : Type u) [AddCommGroup W] [Module k W]
    [Nontrivial W] : ∃ f : Module.Dual k W, f ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  obtain ⟨f, hfx⟩ := Module.Projective.exists_dual_ne_zero k hx
  exact ⟨f, fun h => hfx (by rw [h]; simp)⟩

/-- The four clauses of Tag 0B1T when `C` is the whole of `𝐏(V)`, with no hypothesis on `X`:
there are a projective line `𝐏(W)`, `dim_k W = 2`, closed points `0` and `∞` of it (not asserted
distinct), and a closed subvariety `C'` of `𝐏(W) × 𝐏(V)` such that `C'` is dominant over `𝐏(W)`,
its fibre over `0` is `C`, it intersects the constant family `X × 𝐏(W)` properly, and its fibre
over `∞` intersects each `T i` properly. -/
public theorem exists_movingFamily_over_projectiveLine_of_eq_univ
    (C X : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hC : (C : Set (projectiveSpaceOfModule k V)) = Set.univ)
    {ι : Type*} (T : ι → IrreducibleCloseds (projectiveSpaceOfModule k V)) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module k W) (_ : FiniteDimensional k W)
        (_ : Nontrivial W), Module.finrank k W = 2 ∧
      ∃ (zero infty : projectiveSpaceOfModule k W)
        (hzero : IsClosed ({zero} : Set (projectiveSpaceOfModule k W)))
        (hinfty : IsClosed ({infty} : Set (projectiveSpaceOfModule k W)))
        (Cfam : IrreducibleCloseds (lineProduct k V W)),
        closure ((lineProductLine k V W).base ''
            (Cfam : Set (lineProduct k V W))) = Set.univ ∧
          lineProductFibre k V W zero hzero (Cfam : Set (lineProduct k V W)) =
            (C : Set (projectiveSpaceOfModule k V)) ∧
          (∃ Xfam : IrreducibleCloseds (lineProduct k V W),
            (Xfam : Set (lineProduct k V W)) =
              lineProductConstant k V W (X : Set (projectiveSpaceOfModule k V)) ∧
            IntersectProperly Cfam Xfam) ∧
          ∀ i, ∃ F : IrreducibleCloseds (projectiveSpaceOfModule k V),
            (F : Set (projectiveSpaceOfModule k V)) =
              lineProductFibre k V W infty hinfty (Cfam : Set (lineProduct k V W)) ∧
            IntersectProperly F (T i) := by
  refine ⟨Fin 2 → k, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.finrank_fin_fun k, ?_⟩
  obtain ⟨f, hf⟩ := exists_dual_ne_zero_of_nontrivial k (Fin 2 → k)
  set lam := linearFunctionalPoint k (Fin 2 → k) f hf with hlamdef
  have hlamc : IsClosed ({lam} : Set (projectiveSpaceOfModule k (Fin 2 → k))) :=
    linearFunctionalPoint_isClosed k (Fin 2 → k) f hf
  have hirrW : IrreducibleSpace (lineProduct k V (Fin 2 → k)) :=
    irreducibleSpace_lineProduct k V (Fin 2 → k)
  refine ⟨lam, lam, hlamc, hlamc,
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩,
    closure_image_lineProductLine_univ k V (Fin 2 → k), ?_, ?_, ?_⟩
  · change lineProductFibre k V (Fin 2 → k) lam hlamc Set.univ =
      (C : Set (projectiveSpaceOfModule k V))
    rw [lineProductFibre_univ, hC]
  · refine ⟨⟨lineProductConstant k V (Fin 2 → k) (X : Set (projectiveSpaceOfModule k V)),
      isIrreducible_lineProductConstant k V (Fin 2 → k) _ X.isClosed' X.isIrreducible',
      isClosed_lineProductConstant k V (Fin 2 → k) _ X.isClosed'⟩, rfl, ?_⟩
    exact intersectProperly_of_eq_univ _ _ rfl
  · intro i
    refine ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩, ?_,
      intersectProperly_of_eq_univ _ _ rfl⟩
    change (Set.univ : Set (projectiveSpaceOfModule k V)) =
      lineProductFibre k V (Fin 2 → k) lam hlamc Set.univ
    rw [lineProductFibre_univ]

/-- The four clauses of Tag 0B1T for a closed `X`, clause (2) on sets. Let `C` be a closed
subvariety of `𝐏(V)`, let `X` be a closed subvariety of `𝐏(V)` intersecting `C` properly and let
`T i ⊆ X` be a finite collection of closed subvarieties. Then there are a projective line
`𝐏^1 = 𝐏(W)`, `dim_k W = 2`, closed points `0` and `∞` of it (not asserted distinct), and a
closed subvariety `C'` of `𝐏(W) × 𝐏(V)` such that: `C'` is dominant over `𝐏(W)`; its fibre over
`0` is `C`; it intersects the constant family `X × 𝐏(W)` properly; and its fibre over `∞`
intersects each `T i` properly. -/
public theorem exists_movingFamily_over_projectiveLine
    (C X : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hCX : IntersectProperly C X)
    {ι : Type*} [Finite ι] (T : ι → IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hTX : ∀ i, (T i : Set (projectiveSpaceOfModule k V)) ⊆
      (X : Set (projectiveSpaceOfModule k V))) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module k W) (_ : FiniteDimensional k W)
        (_ : Nontrivial W), Module.finrank k W = 2 ∧
      ∃ (zero infty : projectiveSpaceOfModule k W)
        (hzero : IsClosed ({zero} : Set (projectiveSpaceOfModule k W)))
        (hinfty : IsClosed ({infty} : Set (projectiveSpaceOfModule k W)))
        (Cfam : IrreducibleCloseds (lineProduct k V W)),
        closure ((lineProductLine k V W).base ''
            (Cfam : Set (lineProduct k V W))) = Set.univ ∧
          lineProductFibre k V W zero hzero (Cfam : Set (lineProduct k V W)) =
            (C : Set (projectiveSpaceOfModule k V)) ∧
          (∃ Xfam : IrreducibleCloseds (lineProduct k V W),
            (Xfam : Set (lineProduct k V W)) =
              lineProductConstant k V W (X : Set (projectiveSpaceOfModule k V)) ∧
            IntersectProperly Cfam Xfam) ∧
          ∀ i, ∃ F : IrreducibleCloseds (projectiveSpaceOfModule k V),
            (F : Set (projectiveSpaceOfModule k V)) =
              lineProductFibre k V W infty hinfty (Cfam : Set (lineProduct k V W)) ∧
            IntersectProperly F (T i) := by
  by_cases hCne : (C : Set (projectiveSpaceOfModule k V)) = Set.univ
  · exact exists_movingFamily_over_projectiveLine_of_eq_univ k V C X hCne T
  obtain ⟨U, hUopen, hUne, hU⟩ :=
    exists_isOpen_forall_closedPoint_movingFamily k V C X hCX hCne T hTX
  have hnt : Nontrivial (ParameterModule k V) := by
    refine Module.nontrivial_of_finrank_pos (R := k) ?_
    rw [Subspace.dual_finrank_eq, Module.finrank_linearMap]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) := by
    have := isProper_projectiveSpaceOfModuleToSpec k (ParameterModule k V)
    infer_instance
  have : JacobsonSpace (projectiveSpaceOfModule k (ParameterModule k V)) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k (ParameterModule k V))
  obtain ⟨q, hqU, hqc⟩ :=
    exists_isClosed_singleton_mem_of_isLocallyClosed hUne hUopen.isLocallyClosed
  obtain ⟨L, hL2, zero, infty, hzero, hinfty, -, -, Cfam, hdom, hfib0, hXfam, hTfam⟩ :=
    hU q hqU hqc
  have hNT : Nontrivial (lineSpace k V L) :=
    Module.nontrivial_of_finrank_pos (R := k) (by rw [hL2]; lia)
  exact ⟨lineSpace k V L, inferInstance, inferInstance, inferInstance, inferInstance, hL2,
    zero, infty, hzero, hinfty, Cfam, hdom, hfib0, hXfam, hTfam⟩

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
