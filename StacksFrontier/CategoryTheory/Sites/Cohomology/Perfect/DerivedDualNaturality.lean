module

public import StacksFrontier.CategoryTheory.Monoidal.MateAsInternalHomPre
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingInternalHomNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualIsTheDerivedDual

/-!
# Naturality of the identification of a left dual with the derived dual

Let `(C, O)` be a ringed site. The second assertion of [Stacks, Tag 0FPV] —
`AlgebraicGeometry.RingedSite.derivedDualIsoLeftDual` — identifies a left dual `N` of an object
`M` of `D(O)` with the derived dual `M^∨ = RSheafHom(M, O)` of [Stacks, Tag 08JD]. It is stated
at one object. This file makes it **natural in `M`**: for `u : M ⟶ M'` and left duals `N`, `N'`
of `M`, `M'` the square

```
M'^∨  --≅-->  N'
 |             |
u^∨           u^∨
 v             v
M^∨   --≅-->  N
```

commutes, the left edge being the derived dual of `u` and the right edge the mate of `u` for the
two pairings. So an objectwise family of such identifications over a diagram assembles into an
isomorphism of diagrams, which is what a pro-isomorphism of towers of duals needs.

## Main results

* `AlgebraicGeometry.RingedSite.derivedTensorMap_comp_derivedDualEvaluation`: **the evaluation
  of [Stacks, Tag 0FPU] is natural**, in the spelling of the derived tensor product that
  [Stacks, Tag 08J8] is stated over.
* `AlgebraicGeometry.RingedSite.whiskerRight_derivedDualMap_comp_derivedDualEvaluationMonoidal`:
  the same, read in the monoidal category of [Stacks, Tag 0FPT].
* `AlgebraicGeometry.RingedSite.derivedDualMap_comp_derivedDualToLeftDual` and
  `AlgebraicGeometry.RingedSite.derivedDualMap_comp_derivedDualIsoLeftDual`: **the square above
  commutes**, for the morphism of [Stacks, Tag 0FPV] and for the isomorphism it is.
* `CategoryTheory.ExactPairing.map_mate`: **a monoidal functor carries the mate to the mate**,
  for the image pairings of `CategoryTheory.ExactPairing.map`.

## Implementation notes

**Why the evaluation is all that is needed.** `derivedDualToLeftDual M N` is pinned down by
`AlgebraicGeometry.RingedSite.whiskerRight_derivedDualToLeftDual`, which contracts it with the
evaluation `ε` of the pairing, and a morphism into `N` is determined by that contraction
(`CategoryTheory.ExactPairing.eq_of_whiskerRight_comp_evaluation`). Contracting the two
composites of the square therefore reduces the square to the naturality of the evaluation of
[Stacks, Tag 0FPU] — the mate side by `CategoryTheory.ExactPairing.mate_comp_evaluation` and one
application of `CategoryTheory.MonoidalCategory.whisker_exchange`, the derived-dual side by
`whiskerRight_derivedDualMap_comp_derivedDualEvaluationMonoidal`.

**Which naturality clauses of Stacks 08J8 are used.** Two of the three: naturality in the source
variable, `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`, and
dinaturality in the internal-Hom variable,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_dinaturality`. The evaluation
`ε' : M^∨ ⊗^L_O M ⟶ O` is the image of the identity of `M^∨` under the bijection, and the two
composites of its naturality square are the images of the two factorizations of the derived dual
of `u` as `u^∨ ≫ 1` and `1 ≫ u^∨`. The passage to the monoidal spelling of the tensor product
needs, beside the comparison's naturality in the left factor
(`AlgebraicGeometry.RingedSite.derivedTensorRightComparison_naturality`), its naturality in the
right factor, which is `derivedTensorRightComparison_naturality_right` below.

**No tag.** [Stacks, Tag 0FPV] states the identification at one object; §21.48 has no numbered
statement of its naturality.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactPairing

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

/-- **A monoidal functor carries the mate of a morphism to the mate of its image**, for the
image pairings of `CategoryTheory.ExactPairing.map`. Mathlib has the two mate identities for
`HasRightDual` and the transport of a pairing along a monoidal functor, but not their
compatibility. -/
theorem map_mate (F : C ⥤ D) [F.Monoidal] {A A' B B' : C} (pA : ExactPairing A A')
    (pB : ExactPairing B B') (f : A ⟶ B) :
    F.map (mate pA pB f) =
      mate (@ExactPairing.map C D _ _ _ _ F _ A A' pA)
        (@ExactPairing.map C D _ _ _ _ F _ B B' pB) (F.map f) := by
  refine eq_mate _ _ _ _ ?_
  change F.map (mate pA pB f) ▷ F.obj A ≫ μ F A' A ≫ F.map pA.evaluation' ≫ η F =
    F.obj B' ◁ F.map f ≫ μ F B' B ≫ F.map pB.evaluation' ≫ η F
  rw [μ_natural_left_assoc, ← Functor.map_comp_assoc, mate_comp_evaluation pA pB f,
    Functor.map_comp_assoc, ← μ_natural_right_assoc]

end CategoryTheory.ExactPairing

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-! ### Naturality of the evaluation of Example 0FPU

Nothing in this section mentions the monoidal structure of [Stacks, Tag 0FPT]: the statements
are about the derived tensor product that [Stacks, Tag 08J8] is stated over, and the monoidal
structure is deliberately kept out of scope — with both it and the derived tensor product
available, a single `MonoidalCategory` query cannot serve the two, and the defining equation of
`AlgebraicGeometry.RingedSite.derivedDualEvaluation` is then no longer reachable.
-/

section Evaluation

/-- **The derived dual of a morphism**: for `u : M ⟶ M'` the morphism
`u^∨ : M'^∨ ⟶ M^∨` of derived duals, the derived internal Hom of [Stacks, Tag 08JD] being
contravariant in its source variable. -/
abbrev derivedDualMap
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : M ⟶ M') :
    derivedDual X M' ⟶ derivedDual X M :=
  ((derivedSheafHomBifunctor X).map u.op).app (derivedStructureSheaf X)

/-- **The evaluation of [Stacks, Tag 0FPU] is natural.** Contracting the derived dual of
`u : M ⟶ M'` against the evaluation of `M` is contracting `u` against the evaluation of `M'`.
Both composites are the image of `u^∨ : M'^∨ ⟶ M^∨` under the bijection of [Stacks, Tag 08J8]:
the first by naturality in the source variable applied to `u^∨ ≫ 1`, the second by dinaturality
in the internal-Hom variable applied to `1 ≫ u^∨`. -/
theorem derivedTensorMap_comp_derivedDualEvaluation
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : M ⟶ M') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map (derivedDualMap X u)).app M ≫
        derivedDualEvaluation X M =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj (derivedDual X M')).map u ≫
        derivedDualEvaluation X M' := by
  have h1 := derivedCurryHomEquiv_naturality_source X (derivedDualMap X u)
    (𝟙 (derivedDual X M))
  have h2 := derivedCurryHomEquiv_dinaturality X (derivedDual X M') (derivedStructureSheaf X) u
    (𝟙 (derivedDual X M'))
  -- Every hypothesis is instantiated at its arguments before it is rewritten, and every rewrite
  -- is on the goal: matching a pattern with metavariables against terms of this size, or
  -- reverting a hypothesis that mentions the coercion of the morphism-group bijection, exhausts
  -- the elaborator's recursion budget.
  have hev := derivedDualEvaluation_eq X M
  have hev' := derivedDualEvaluation_eq X M'
  rw [hev, hev', ← h1, ← h2, Category.comp_id, Category.id_comp]

end Evaluation

/-! ### Naturality of the identification of Stacks 0FPV

The monoidal structure of [Stacks, Tag 0FPT] enters only here. -/

section Monoidal

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory
attribute [local instance] derivedMonoidalStructure

/-- The comparison of the two derived tensor products is natural in the right factor. -/
theorem derivedTensorRightComparison_naturality_right
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : M ⟶ M')
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    A ◁ u ≫ (derivedTensorRightComparison M' A).hom =
      (derivedTensorRightComparison M A).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map u :=
  ((derivedMonoidalTensorComparison X).app A).hom.naturality u

/-- **The evaluation of [Stacks, Tag 0FPU], read in the monoidal category of
[Stacks, Tag 0FPT], is natural.** This is
`AlgebraicGeometry.RingedSite.derivedTensorMap_comp_derivedDualEvaluation` carried across the
comparison of the two derived tensor products, which is natural in both factors. -/
theorem whiskerRight_derivedDualMap_comp_derivedDualEvaluationMonoidal
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : M ⟶ M') :
    derivedDualMap X u ▷ M ≫ derivedDualEvaluationMonoidal M =
      derivedDual X M' ◁ u ≫ derivedDualEvaluationMonoidal M' := by
  have e1 := derivedTensorRightComparison_naturality M (derivedDualMap X u)
  have e2 := derivedTensorRightComparison_naturality_right X u (derivedDual X M')
  have e3 := derivedTensorMap_comp_derivedDualEvaluation X u
  dsimp only [derivedDualEvaluationMonoidal]
  rw [reassoc_of% e1, reassoc_of% e3, reassoc_of% e2]

section Pairing

variable
  (M N M' N' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  [ExactPairing M N] [ExactPairing M' N']

/-- **The identification of [Stacks, Tag 0FPV] is natural in `M`.** For `u : M ⟶ M'`, the
derived dual `u^∨ : M'^∨ ⟶ M^∨` of [Stacks, Tag 08JD] and the mate `N' ⟶ N` of `u` for the two
pairings are carried to one another by the morphisms
`AlgebraicGeometry.RingedSite.derivedDualToLeftDual`.

Both composites are morphisms into `N`, so they are equal as soon as their contractions with the
evaluation of the pairing agree
(`CategoryTheory.ExactPairing.eq_of_whiskerRight_comp_evaluation`); contracting turns the
left-hand one into the naturality of the evaluation of [Stacks, Tag 0FPU] and the right-hand one
into the defining identity of the mate. -/
theorem derivedDualMap_comp_derivedDualToLeftDual (u : M ⟶ M') :
    derivedDualMap X u ≫ derivedDualToLeftDual M N =
      derivedDualToLeftDual M' N' ≫
        ExactPairing.mate (inferInstance : ExactPairing M N)
          (inferInstance : ExactPairing M' N') u := by
  refine ExactPairing.eq_of_whiskerRight_comp_evaluation (inferInstance : ExactPairing M N) _ _ ?_
  change (derivedDualMap X u ≫ derivedDualToLeftDual M N) ▷ M ≫ ε_ M N =
    (derivedDualToLeftDual M' N' ≫
      ExactPairing.mate (inferInstance : ExactPairing M N)
        (inferInstance : ExactPairing M' N') u) ▷ M ≫ ε_ M N
  rw [MonoidalCategory.comp_whiskerRight_assoc, MonoidalCategory.comp_whiskerRight_assoc,
    whiskerRight_derivedDualToLeftDual M N,
    whiskerRight_derivedDualMap_comp_derivedDualEvaluationMonoidal X u,
    show ExactPairing.mate (inferInstance : ExactPairing M N)
        (inferInstance : ExactPairing M' N') u ▷ M ≫ ε_ M N = N' ◁ u ≫ ε_ M' N' from
      ExactPairing.mate_comp_evaluation _ _ u,
    ← MonoidalCategory.whisker_exchange_assoc, whiskerRight_derivedDualToLeftDual M' N']

/-- **The identification `M^∨ ≅ N` of [Stacks, Tag 0FPV] is natural in `M`**: the square of the
two isomorphisms, the derived dual of `u` and the mate of `u`, commutes. -/
theorem derivedDualMap_comp_derivedDualIsoLeftDual (u : M ⟶ M') :
    derivedDualMap X u ≫ (derivedDualIsoLeftDual M N).hom =
      (derivedDualIsoLeftDual M' N').hom ≫
        ExactPairing.mate (inferInstance : ExactPairing M N)
          (inferInstance : ExactPairing M' N') u :=
  derivedDualMap_comp_derivedDualToLeftDual X M N M' N' u

end Pairing

end Monoidal

end AlgebraicGeometry.RingedSite

end
