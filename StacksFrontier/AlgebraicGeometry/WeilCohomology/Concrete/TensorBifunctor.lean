module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorCone
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat

/-!
# The tensor product of correspondences is a bifunctor

For schemes `A, A', B, B', C, C'` smooth over a field `k`, of constant dimension, with `B` and
`B'` proper, and correspondences `x ∈ Corrʳ(A, B)`, `x' ∈ Corr^{r'}(A', B')`, `y ∈ Corrˢ(B, C)`,
`y' ∈ Corr^{s'}(B', C')`, this file proves

  `(y ⊗ y') ∘ (x ⊗ x') = (y ∘ x) ⊗ (y' ∘ x')`.

This is the compatibility of the tensor product with composition which makes the tensor product
a functor of two variables on the category of correspondences (Stacks 0FG7).

The proof computes both sides on the sixfold product
`T = (A × A') × (B × B') × (C × C')`, read as the product `(A × B × C) × (A' × B' × C')` through
the two projections `q₁` and `q₂` (`Stacks.WeilCohomology.isPullback_sixfoldPr`). Both sides
are `π₁₃,*(q₁^*(p₁₂^* x · p₂₃^* y) · q₂^*(p₁₂^* x' · p₂₃^* y'))`, by the three rules of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorCone`.

## Main results

* `Stacks.WeilCohomology.compositionInt_tensorInt_heq`: the identity on integral Chow groups.
* `Stacks.WeilCohomology.composition_tensorBlock`: the identity on rational correspondences.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### The sixfold product as a product of two triple products -/

section Sixfold

variable {S A A' B B' C C' : Scheme.{u}} (sA : A ⟶ S) (sA' : A' ⟶ S) (sB : B ⟶ S)
  (sB' : B' ⟶ S) (sC : C ⟶ S) (sC' : C' ⟶ S)

/-- The sixfold product `(A × A') × (B × B') × (C × C')`. -/
abbrev sixfold : Scheme.{u} := tripleProduct (prodBase sA sA') (prodBase sB sB') (prodBase sC sC')

/-- The projection `q₁ : (A × A') × (B × B') × (C × C') ⟶ A × B × C`. -/
def sixfoldPr₁ : sixfold sA sA' sB sB' sC sC' ⟶ tripleProduct sA sB sC :=
  Limits.pullback.lift
    (pr₁₂ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') ≫ tensorPr₁₃ sA sA' sB sB')
    (Limits.pullback.snd (prodBase (prodBase sA sA') (prodBase sB sB')) (prodBase sC sC') ≫
      Limits.pullback.fst sC sC')
    (by
      rw [Category.assoc, tensorPr₁₃_comp_prodBase, Category.assoc,
        show Limits.pullback.fst sC sC' ≫ sC = prodBase sC sC' from rfl]
      exact Limits.pullback.condition)

/-- The projection `q₂ : (A × A') × (B × B') × (C × C') ⟶ A' × B' × C'`. -/
def sixfoldPr₂ : sixfold sA sA' sB sB' sC sC' ⟶ tripleProduct sA' sB' sC' :=
  Limits.pullback.lift
    (pr₁₂ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') ≫ tensorPr₂₄ sA sA' sB sB')
    (Limits.pullback.snd (prodBase (prodBase sA sA') (prodBase sB sB')) (prodBase sC sC') ≫
      Limits.pullback.snd sC sC')
    (by
      rw [Category.assoc, tensorPr₂₄_comp_prodBase, Category.assoc,
        ← Limits.pullback.condition (f := sC) (g := sC'),
        show Limits.pullback.fst sC sC' ≫ sC = prodBase sC sC' from rfl]
      exact Limits.pullback.condition)

/-- The projection `q₁` followed by `A × B × C ⟶ A × B` is the projection to
`(A × A') × (B × B')` followed by `(A × A') × (B × B') ⟶ A × B`. -/
@[reassoc (attr := simp)]
theorem sixfoldPr₁_fst : sixfoldPr₁ sA sA' sB sB' sC sC' ≫ pr₁₂ sA sB sC =
    pr₁₂ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') ≫ tensorPr₁₃ sA sA' sB sB' :=
  Limits.pullback.lift_fst _ _ _

/-- The projection `q₁` followed by `A × B × C ⟶ C` is the projection to `C × C'` followed by
`C × C' ⟶ C`. -/
@[reassoc (attr := simp)]
theorem sixfoldPr₁_snd : sixfoldPr₁ sA sA' sB sB' sC sC' ≫
      Limits.pullback.snd (prodBase sA sB) sC =
    Limits.pullback.snd (prodBase (prodBase sA sA') (prodBase sB sB')) (prodBase sC sC') ≫
      Limits.pullback.fst sC sC' :=
  Limits.pullback.lift_snd _ _ _

/-- The projection `q₂` followed by `A' × B' × C' ⟶ A' × B'` is the projection to
`(A × A') × (B × B')` followed by `(A × A') × (B × B') ⟶ A' × B'`. -/
@[reassoc (attr := simp)]
theorem sixfoldPr₂_fst : sixfoldPr₂ sA sA' sB sB' sC sC' ≫ pr₁₂ sA' sB' sC' =
    pr₁₂ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') ≫ tensorPr₂₄ sA sA' sB sB' :=
  Limits.pullback.lift_fst _ _ _

/-- The projection `q₂` followed by `A' × B' × C' ⟶ C'` is the projection to `C × C'` followed by
`C × C' ⟶ C'`. -/
@[reassoc (attr := simp)]
theorem sixfoldPr₂_snd : sixfoldPr₂ sA sA' sB sB' sC sC' ≫
      Limits.pullback.snd (prodBase sA' sB') sC' =
    Limits.pullback.snd (prodBase (prodBase sA sA') (prodBase sB sB')) (prodBase sC sC') ≫
      Limits.pullback.snd sC sC' :=
  Limits.pullback.lift_snd _ _ _

/-- The projection `q₁` is a morphism over the base. -/
theorem sixfoldPr₁_comp_tripleBase :
    sixfoldPr₁ sA sA' sB sB' sC sC' ≫ tripleBase sA sB sC =
      tripleBase (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') := by
  rw [tripleBase, ← Category.assoc, sixfoldPr₁_fst, Category.assoc, tensorPr₁₃_comp_prodBase]

/-- The projection `q₂` is a morphism over the base. -/
theorem sixfoldPr₂_comp_tripleBase :
    sixfoldPr₂ sA sA' sB sB' sC sC' ≫ tripleBase sA' sB' sC' =
      tripleBase (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') := by
  rw [tripleBase, ← Category.assoc, sixfoldPr₂_fst, Category.assoc, tensorPr₂₄_comp_prodBase]

/-- Morphisms into the sixfold product are determined by their two projections to `A × B × C`
and `A' × B' × C'`. -/
theorem sixfold_hom_ext {W : Scheme.{u}} {m m' : W ⟶ sixfold sA sA' sB sB' sC sC'}
    (h₁ : m ≫ sixfoldPr₁ sA sA' sB sB' sC sC' = m' ≫ sixfoldPr₁ sA sA' sB sB' sC sC')
    (h₂ : m ≫ sixfoldPr₂ sA sA' sB sB' sC sC' = m' ≫ sixfoldPr₂ sA sA' sB sB' sC sC') :
    m = m' := by
  have h₁₁ := congrArg (· ≫ pr₁₂ sA sB sC) h₁
  have h₁₂ := congrArg (· ≫ Limits.pullback.snd (prodBase sA sB) sC) h₁
  have h₂₁ := congrArg (· ≫ pr₁₂ sA' sB' sC') h₂
  have h₂₂ := congrArg (· ≫ Limits.pullback.snd (prodBase sA' sB') sC') h₂
  simp only [Category.assoc, sixfoldPr₁_fst, sixfoldPr₁_snd, sixfoldPr₂_fst,
    sixfoldPr₂_snd] at h₁₁ h₁₂ h₂₁ h₂₂
  apply Limits.pullback.hom_ext
  · refine tensorProduct_hom_ext sA sA' sB sB' ?_ ?_
    · simpa only [Category.assoc] using h₁₁
    · simpa only [Category.assoc] using h₂₁
  · apply Limits.pullback.hom_ext
    · simpa only [Category.assoc] using h₁₂
    · simpa only [Category.assoc] using h₂₂

/-- **The sixfold product is the product of the two triple products**:
`(A × A') × (B × B') × (C × C') = (A × B × C) × (A' × B' × C')` through `q₁` and `q₂`. -/
theorem isPullback_sixfoldPr :
    IsPullback (sixfoldPr₁ sA sA' sB sB' sC sC') (sixfoldPr₂ sA sA' sB sB' sC sC')
      (tripleBase sA sB sC) (tripleBase sA' sB' sC') := by
  have key : ∀ s : PullbackCone (tripleBase sA sB sC) (tripleBase sA' sB' sC'),
      ∃ l : s.pt ⟶ sixfold sA sA' sB sB' sC sC',
        l ≫ sixfoldPr₁ sA sA' sB sB' sC sC' = s.fst ∧
          l ≫ sixfoldPr₂ sA sA' sB sB' sC sC' = s.snd := fun s ↦ by
    refine ⟨Limits.pullback.lift
      (tensorLift sA sA' sB sB' (s.fst ≫ pr₁₂ sA sB sC) (s.snd ≫ pr₁₂ sA' sB' sC')
        (by simpa only [Category.assoc] using s.condition))
      (Limits.pullback.lift (s.fst ≫ Limits.pullback.snd (prodBase sA sB) sC)
        (s.snd ≫ Limits.pullback.snd (prodBase sA' sB') sC') (by
          have h := s.condition
          simp only [tripleBase] at h
          rw [Category.assoc, Category.assoc, ← Limits.pullback.condition,
            ← Limits.pullback.condition, ← Category.assoc, ← Category.assoc]
          simpa only [Category.assoc] using h))
      (by
        have h := congrArg (s.fst ≫ ·) (Limits.pullback.condition (f := prodBase sA sB) (g := sC))
        simp only [prodBase, tensorLift, Category.assoc, Limits.pullback.lift_fst_assoc] at h ⊢
        exact h), ?_, ?_⟩
    · apply Limits.pullback.hom_ext
      · rw [Category.assoc, sixfoldPr₁_fst, ← Category.assoc, Limits.pullback.lift_fst,
          tensorLift_tensorPr₁₃]
      · rw [Category.assoc, sixfoldPr₁_snd, ← Category.assoc, Limits.pullback.lift_snd,
          Limits.pullback.lift_fst]
    · apply Limits.pullback.hom_ext
      · rw [Category.assoc, sixfoldPr₂_fst, ← Category.assoc, Limits.pullback.lift_fst,
          tensorLift_tensorPr₂₄]
      · rw [Category.assoc, sixfoldPr₂_snd, ← Category.assoc, Limits.pullback.lift_snd,
          Limits.pullback.lift_snd]
  refine IsPullback.of_isLimit' ⟨by rw [sixfoldPr₁_comp_tripleBase, sixfoldPr₂_comp_tripleBase]⟩ ?_
  exact PullbackCone.IsLimit.mk _ (fun s ↦ (key s).choose) (fun s ↦ (key s).choose_spec.1)
    (fun s ↦ (key s).choose_spec.2) fun s m h₁ h₂ ↦
      sixfold_hom_ext sA sA' sB sB' sC sC' (h₁.trans (key s).choose_spec.1.symm)
        (h₂.trans (key s).choose_spec.2.symm)

/-! The six projections, read through `q₁` and `q₂`. -/

/-- The projection of the sixfold product to `A × B` factors as `p₁₂ ∘ q₁`. -/
theorem pr₁₂_tensorPr₁₃_sixfold :
    pr₁₂ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') ≫ tensorPr₁₃ sA sA' sB sB' =
      sixfoldPr₁ sA sA' sB sB' sC sC' ≫ pr₁₂ sA sB sC :=
  (sixfoldPr₁_fst _ _ _ _ _ _).symm

/-- The projection of the sixfold product to `A' × B'` factors as `p₁₂ ∘ q₂`. -/
theorem pr₁₂_tensorPr₂₄_sixfold :
    pr₁₂ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') ≫ tensorPr₂₄ sA sA' sB sB' =
      sixfoldPr₂ sA sA' sB sB' sC sC' ≫ pr₁₂ sA' sB' sC' :=
  (sixfoldPr₂_fst _ _ _ _ _ _).symm

/-- The projection of the sixfold product to `B × C` factors as `p₂₃ ∘ q₁`. -/
theorem pr₂₃_tensorPr₁₃_sixfold :
    pr₂₃ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') ≫ tensorPr₁₃ sB sB' sC sC' =
      sixfoldPr₁ sA sA' sB sB' sC sC' ≫ pr₂₃ sA sB sC := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, Category.assoc, tensorPr₁₃_fst, pr₂₃_fst_assoc, pr₂₃_fst,
      sixfoldPr₁_fst_assoc, tensorPr₁₃_snd]
  · rw [Category.assoc, Category.assoc, tensorPr₁₃_snd, pr₂₃_snd_assoc, pr₂₃_snd, sixfoldPr₁_snd]

/-- The projection of the sixfold product to `B' × C'` factors as `p₂₃ ∘ q₂`. -/
theorem pr₂₃_tensorPr₂₄_sixfold :
    pr₂₃ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') ≫ tensorPr₂₄ sB sB' sC sC' =
      sixfoldPr₂ sA sA' sB sB' sC sC' ≫ pr₂₃ sA' sB' sC' := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, Category.assoc, tensorPr₂₄_fst, pr₂₃_fst_assoc, pr₂₃_fst,
      sixfoldPr₂_fst_assoc, tensorPr₂₄_snd]
  · rw [Category.assoc, Category.assoc, tensorPr₂₄_snd, pr₂₃_snd_assoc, pr₂₃_snd, sixfoldPr₂_snd]

/-- The projection of the sixfold product to `A × C` factors as `p₁₃ ∘ q₁`. -/
theorem pr₁₃_tensorPr₁₃_sixfold :
    pr₁₃ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') ≫ tensorPr₁₃ sA sA' sC sC' =
      sixfoldPr₁ sA sA' sB sB' sC sC' ≫ pr₁₃ sA sB sC := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, Category.assoc, tensorPr₁₃_fst, pr₁₃_fst_assoc, pr₁₃_fst,
      sixfoldPr₁_fst_assoc, tensorPr₁₃_fst]
  · rw [Category.assoc, Category.assoc, tensorPr₁₃_snd, pr₁₃_snd_assoc, pr₁₃_snd, sixfoldPr₁_snd]

/-- The projection of the sixfold product to `A' × C'` factors as `p₁₃ ∘ q₂`. -/
theorem pr₁₃_tensorPr₂₄_sixfold :
    pr₁₃ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') ≫ tensorPr₂₄ sA sA' sC sC' =
      sixfoldPr₂ sA sA' sB sB' sC sC' ≫ pr₁₃ sA' sB' sC' := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, Category.assoc, tensorPr₂₄_fst, pr₁₃_fst_assoc, pr₁₃_fst,
      sixfoldPr₂_fst_assoc, tensorPr₂₄_fst]
  · rw [Category.assoc, Category.assoc, tensorPr₂₄_snd, pr₁₃_snd_assoc, pr₁₃_snd, sixfoldPr₂_snd]

end Sixfold

/-! ### Bifunctoriality -/

section Bifunctor

variable (k : Type u) [Field k] {A A' B B' C C' : Scheme.{u}}
  (sA : A ⟶ (fieldChowSituation k).S) (sA' : A' ⟶ (fieldChowSituation k).S)
  (sB : B ⟶ (fieldChowSituation k).S) (sB' : B' ⟶ (fieldChowSituation k).S)
  (sC : C ⟶ (fieldChowSituation k).S) (sC' : C' ⟶ (fieldChowSituation k).S)
  [Smooth sA] [IsSeparated sA] [Smooth sA'] [IsSeparated sA'] [Smooth sB] [IsSeparated sB]
  [Smooth sB'] [IsSeparated sB'] [Smooth sC] [IsSeparated sC] [Smooth sC'] [IsSeparated sC']
  [IsProper sB] [IsProper sB'] {Δ : DiagonalClassFamily k}

local notation "μ" =>
  selfIntersectionProduct (fieldChowSituation k)
      (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
    (fieldGysinSystem k)

local notation "pb[" sA ", " sB ", " v ", " hv ", " r ", " hr ", " n "]" =>
  flatPullbackChow (fieldChowSituation k) sA sB v hv r hr n
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)

local notation "pf[" sA ", " sB ", " v ", " hv ", " n "]" =>
  properChowPushforward (fieldChowSituation k) sA sB v hv n
    (properPushforwardDescends _ _ _ _ _ _)

/-- The projection `q₁` is locally of finite type. -/
instance : LocallyOfFiniteType (sixfoldPr₁ sA sA' sB sB' sC sC') :=
  MorphismProperty.of_isPullback (isPullback_sixfoldPr sA sA' sB sB' sC sC').flip inferInstance

/-- The projection `q₁` is flat. -/
instance : Flat (sixfoldPr₁ sA sA' sB sB' sC sC') :=
  MorphismProperty.of_isPullback (isPullback_sixfoldPr sA sA' sB sB' sC sC').flip inferInstance

/-- The projection `q₂` is locally of finite type. -/
instance : LocallyOfFiniteType (sixfoldPr₂ sA sA' sB sB' sC sC') :=
  MorphismProperty.of_isPullback (isPullback_sixfoldPr sA sA' sB sB' sC sC') inferInstance

/-- The projection `q₂` is flat. -/
instance : Flat (sixfoldPr₂ sA sA' sB sB' sC sC') :=
  MorphismProperty.of_isPullback (isPullback_sixfoldPr sA sA' sB sB' sC sC') inferInstance

omit [IsSeparated sA] [IsSeparated sA'] [IsSeparated sB] [IsSeparated sB'] [IsProper sB]
  [IsProper sB'] in
/-- The tensor product, unfolded: `x ⊗ x' = pr₁₃^* x · pr₂₄^* x'`, up to the transport of
degrees. -/
theorem tensorInt_heq {d d' e e' : ℕ} (hA : RelativeDimension sA d)
    (hA' : RelativeDimension sA' d') (hB : RelativeDimension sB e)
    (hB' : RelativeDimension sB' e') (r r' : ℤ)
    (x : chowGroup (fieldChowSituation k) (prodBase sA sB) ((e : ℤ) - r))
    (x' : chowGroup (fieldChowSituation k) (prodBase sA' sB') ((e' : ℤ) - r')) :
    tensorInt k sA sA' sB sB' Δ hA hA' hB hB' r r' x x' ≍
      μ (tensorBase sA sA' sB sB') _
          (Δ _ _ (relativeDimension_tensorBase k sA sA' sB sB' hA hA' hB hB'))
        (((e : ℤ) - r) + ((e' + d' : ℕ) : ℤ)) (((e' : ℤ) - r') + ((e + d : ℕ) : ℤ))
        (pb[tensorBase sA sA' sB sB', prodBase sA sB, tensorPr₁₃ sA sA' sB sB',
          tensorPr₁₃_comp_prodBase sA sA' sB sB', e' + d',
          relativeDimension_tensorPr₁₃ k sA sA' sB sB' hA' hB', (e : ℤ) - r] x)
        (pb[tensorBase sA sA' sB sB', prodBase sA' sB', tensorPr₂₄ sA sA' sB sB',
          tensorPr₂₄_comp_prodBase sA sA' sB sB', e + d,
          relativeDimension_tensorPr₂₄ k sA sA' sB sB' hA hB, (e' : ℤ) - r'] x') :=
  chowGroupDegreeEquiv_heq _ _ _ _

/-- **The tensor product of correspondences is compatible with composition**, on integral Chow
groups: for schemes of constant dimension with `B`, `B'` proper,

  `(y ⊗ y') ∘ (x ⊗ x') = (y ∘ x) ⊗ (y' ∘ x')`,

up to the identification of the degrees `(r + r') + (s + s') = (r + s) + (r' + s')`, for a family
of diagonal classes satisfying Stacks 0FFB for flat morphisms, the projection formula of Stacks
0FFC, associativity (Stacks 0FC1) and commutativity of the intersection product. -/
theorem compositionInt_tensorInt_heq (hmul : Δ.FlatPullbackMul) (hproj : Δ.ProjectionFormula)
    (hassoc : Δ.IntersectionAssoc) (hsymm : Δ.IsSymmetric) {d d' e e' f f' : ℕ}
    (hA : RelativeDimension sA d) (hA' : RelativeDimension sA' d')
    (hB : RelativeDimension sB e) (hB' : RelativeDimension sB' e')
    (hC : RelativeDimension sC f) (hC' : RelativeDimension sC' f')
    (hP : RelativeDimension (prodBase sA sA') (d + d'))
    (hQ : RelativeDimension (prodBase sB sB') (e + e'))
    (hR : RelativeDimension (prodBase sC sC') (f + f')) (r r' s s' : ℤ)
    (x : chowGroup (fieldChowSituation k) (prodBase sA sB) ((e : ℤ) - r))
    (x' : chowGroup (fieldChowSituation k) (prodBase sA' sB') ((e' : ℤ) - r'))
    (y : chowGroup (fieldChowSituation k) (prodBase sB sC) ((f : ℤ) - s))
    (y' : chowGroup (fieldChowSituation k) (prodBase sB' sC') ((f' : ℤ) - s')) :
    compositionInt k (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') Δ hP hQ hR (r + r')
        (s + s') (tensorInt k sA sA' sB sB' Δ hA hA' hB hB' r r' x x')
        (tensorInt k sB sB' sC sC' Δ hB hB' hC hC' s s' y y') ≍
      tensorInt k sA sA' sC sC' Δ hA hA' hC hC' (r + s) (r' + s')
        (compositionInt k sA sB sC Δ hA hB hC r s x y)
        (compositionInt k sA' sB' sC' Δ hA' hB' hC' r' s' x' y') := by
  have hT := relativeDimension_tripleBase k (prodBase sA sA') (prodBase sB sB')
    (prodBase sC sC') hP hQ hR
  have hq₁ : RelativeDimension (sixfoldPr₁ sA sA' sB sB' sC sC') (f' + (e' + d')) :=
    RelativeDimension.of_isPullback (isPullback_sixfoldPr sA sA' sB sB' sC sC').flip
      (relativeDimension_tripleBase k sA' sB' sC' hA' hB' hC')
  have hq₂ : RelativeDimension (sixfoldPr₂ sA sA' sB sB' sC sC') (f + (e + d)) :=
    RelativeDimension.of_isPullback (isPullback_sixfoldPr sA sA' sB sB' sC sC')
      (relativeDimension_tripleBase k sA sB sC hA hB hC)
  have h₁₂ := (flatPullbackChow_heq_congr _ _ _
      (pr₁₂ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC'))
      (pr₁₂ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC')) (pr₁₂_comp_prodBase _ _ _)
      (pr₁₂_comp_prodBase _ _ _) rfl rfl (relativeDimension_pr₁₂ k _ _ _ hR)
      (relativeDimension_pr₁₂ k _ _ _ hR) (by push_cast; omega)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) _ _
      (tensorInt_heq k sA sA' sB sB' hA hA' hB hB' r r' x x')).trans
    (flatPullbackChow_selfIntersectionProduct_heq hmul (tensorBase sA sA' sB sB')
      (prodBase sA sB) (prodBase sA' sB') (tripleBase (prodBase sA sA') (prodBase sB sB')
        (prodBase sC sC')) (tripleBase sA sB sC) (tripleBase sA' sB' sC')
      (tensorPr₁₃ sA sA' sB sB') (tensorPr₂₄ sA sA' sB sB') (sixfoldPr₁ sA sA' sB sB' sC sC')
      (sixfoldPr₂ sA sA' sB sB' sC sC')
      (pr₁₂ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC')) (pr₁₂ sA sB sC)
      (pr₁₂ sA' sB' sC') (tensorPr₁₃_comp_prodBase _ _ _ _) (tensorPr₂₄_comp_prodBase _ _ _ _)
      (sixfoldPr₁_comp_tripleBase _ _ _ _ _ _) (sixfoldPr₂_comp_tripleBase _ _ _ _ _ _)
      (pr₁₂_comp_prodBase _ _ _) (pr₁₂_comp_prodBase _ _ _) (pr₁₂_comp_prodBase _ _ _)
      (pr₁₂_tensorPr₁₃_sixfold _ _ _ _ _ _) (pr₁₂_tensorPr₂₄_sixfold _ _ _ _ _ _)
      (relativeDimension_tensorPr₁₃ k sA sA' sB sB' hA' hB')
      (relativeDimension_tensorPr₂₄ k sA sA' sB sB' hA hB) hq₁ hq₂
      (relativeDimension_pr₁₂ k _ _ _ hR) (relativeDimension_pr₁₂ k sA sB sC hC)
      (relativeDimension_pr₁₂ k sA' sB' sC' hC')
      (relativeDimension_tensorBase k sA sA' sB sB' hA hA' hB hB') hT (by omega) (by omega)
      (by omega) _ _ x x')
  have h₂₃ := (flatPullbackChow_heq_congr _ _ _
      (pr₂₃ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC'))
      (pr₂₃ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC')) (pr₂₃_comp_prodBase _ _ _)
      (pr₂₃_comp_prodBase _ _ _) rfl rfl (relativeDimension_pr₂₃ k _ _ _ hP)
      (relativeDimension_pr₂₃ k _ _ _ hP) (by push_cast; omega)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) _ _
      (tensorInt_heq k sB sB' sC sC' hB hB' hC hC' s s' y y')).trans
    (flatPullbackChow_selfIntersectionProduct_heq hmul (tensorBase sB sB' sC sC')
      (prodBase sB sC) (prodBase sB' sC') (tripleBase (prodBase sA sA') (prodBase sB sB')
        (prodBase sC sC')) (tripleBase sA sB sC) (tripleBase sA' sB' sC')
      (tensorPr₁₃ sB sB' sC sC') (tensorPr₂₄ sB sB' sC sC') (sixfoldPr₁ sA sA' sB sB' sC sC')
      (sixfoldPr₂ sA sA' sB sB' sC sC')
      (pr₂₃ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC')) (pr₂₃ sA sB sC)
      (pr₂₃ sA' sB' sC') (tensorPr₁₃_comp_prodBase _ _ _ _) (tensorPr₂₄_comp_prodBase _ _ _ _)
      (sixfoldPr₁_comp_tripleBase _ _ _ _ _ _) (sixfoldPr₂_comp_tripleBase _ _ _ _ _ _)
      (pr₂₃_comp_prodBase _ _ _) (pr₂₃_comp_prodBase _ _ _) (pr₂₃_comp_prodBase _ _ _)
      (pr₂₃_tensorPr₁₃_sixfold _ _ _ _ _ _) (pr₂₃_tensorPr₂₄_sixfold _ _ _ _ _ _)
      (relativeDimension_tensorPr₁₃ k sB sB' sC sC' hB' hC')
      (relativeDimension_tensorPr₂₄ k sB sB' sC sC' hB hC) hq₁ hq₂
      (relativeDimension_pr₂₃ k _ _ _ hP) (relativeDimension_pr₂₃ k sA sB sC hA)
      (relativeDimension_pr₂₃ k sA' sB' sC' hA')
      (relativeDimension_tensorBase k sB sB' sC sC' hB hB' hC hC') hT (by omega) (by omega)
      (by omega) _ _ y y')
  have hμ := (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by push_cast; omega)
      (by push_cast; omega) h₁₂ h₂₃).trans
    (selfIntersectionProduct_pullback_pullback_heq hmul hassoc hsymm
      (tripleBase (prodBase sA sA') (prodBase sB sB') (prodBase sC sC')) (tripleBase sA sB sC)
      (tripleBase sA' sB' sC') (sixfoldPr₁ sA sA' sB sB' sC sC')
      (sixfoldPr₂ sA sA' sB sB' sC sC') (sixfoldPr₁_comp_tripleBase _ _ _ _ _ _)
      (sixfoldPr₂_comp_tripleBase _ _ _ _ _ _) hq₁ hq₂
      (relativeDimension_tripleBase k sA sB sC hA hB hC)
      (relativeDimension_tripleBase k sA' sB' sC' hA' hB' hC') hT (by omega) (by omega) _ _ _ _
      _ _ _ _)
  have hπ := properChowPushforward_selfIntersectionProduct_heq hproj
    (tensorBase sA sA' sC sC') (prodBase sA sC) (prodBase sA' sC')
    (tripleBase (prodBase sA sA') (prodBase sB sB') (prodBase sC sC')) (tripleBase sA sB sC)
    (tripleBase sA' sB' sC') (tensorPr₁₃ sA sA' sC sC') (tensorPr₂₄ sA sA' sC sC')
    (sixfoldPr₁ sA sA' sB sB' sC sC') (sixfoldPr₂ sA sA' sB sB' sC sC')
    (isPullback_tensorPr₁₃_tensorPr₂₄ sA sA' sC sC') (isPullback_sixfoldPr sA sA' sB sB' sC sC')
    (pr₁₃ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC')) (pr₁₃ sA sB sC)
    (pr₁₃ sA' sB' sC') (tensorPr₁₃_comp_prodBase _ _ _ _) (tensorPr₂₄_comp_prodBase _ _ _ _)
    (sixfoldPr₁_comp_tripleBase _ _ _ _ _ _) (sixfoldPr₂_comp_tripleBase _ _ _ _ _ _)
    (pr₁₃_comp_prodBase _ _ _) (pr₁₃_comp_prodBase _ _ _) (pr₁₃_comp_prodBase _ _ _)
    (pr₁₃_tensorPr₁₃_sixfold _ _ _ _ _ _) (pr₁₃_tensorPr₂₄_sixfold _ _ _ _ _ _)
    (relativeDimension_tensorPr₁₃ k sA sA' sC sC' hA' hC')
    (relativeDimension_tensorPr₂₄ k sA sA' sC sC' hA hC) hq₁ hq₂
    (relativeDimension_pr₁₃ k sA sB sC hB) (relativeDimension_pr₁₃ k sA' sB' sC' hB')
    (relativeDimension_prodBase k sA sC hA hC)
    (relativeDimension_tripleBase k sA' sB' sC' hA' hB' hC')
    (relativeDimension_tensorBase k sA sA' sC sC' hA hA' hC hC') hT (by omega) (by omega)
    (by omega) (by omega) _ _
    (μ (tripleBase sA sB sC) _ (Δ _ _ (relativeDimension_tripleBase k sA sB sC hA hB hC)) _ _
      (pb[tripleBase sA sB sC, prodBase sA sB, pr₁₂ sA sB sC, pr₁₂_comp_prodBase sA sB sC, f,
        relativeDimension_pr₁₂ k sA sB sC hC, (e : ℤ) - r] x)
      (pb[tripleBase sA sB sC, prodBase sB sC, pr₂₃ sA sB sC, pr₂₃_comp_prodBase sA sB sC, d,
        relativeDimension_pr₂₃ k sA sB sC hA, (f : ℤ) - s] y))
    (μ (tripleBase sA' sB' sC') _ (Δ _ _ (relativeDimension_tripleBase k sA' sB' sC' hA' hB' hC'))
      _ _
      (pb[tripleBase sA' sB' sC', prodBase sA' sB', pr₁₂ sA' sB' sC',
        pr₁₂_comp_prodBase sA' sB' sC', f', relativeDimension_pr₁₂ k sA' sB' sC' hC',
        (e' : ℤ) - r'] x')
      (pb[tripleBase sA' sB' sC', prodBase sB' sC', pr₂₃ sA' sB' sC',
        pr₂₃_comp_prodBase sA' sB' sC', d', relativeDimension_pr₂₃ k sA' sB' sC' hA',
        (f' : ℤ) - s'] y'))
  refine (compositionInt_heq k Δ (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') hP hQ hR
    (r + r') (s + s') _ _).trans ?_
  refine HEq.trans ?_ (tensorInt_heq k sA sA' sC sC' hA hA' hC hC' (r + s) (r' + s') _ _).symm
  refine (properChowPushforward_heq_congr _ _ _ _ _ (by push_cast; omega)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _) _ _
    hμ).trans ?_
  refine hπ.trans (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by push_cast; omega)
    (by push_cast; omega) ?_ ?_) <;>
  exact flatPullbackChow_heq_congr _ _ _ _ _ _ _ rfl rfl _ _ (by push_cast; omega)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) _ _
    (compositionInt_heq k Δ _ _ _ _ _ _ _ _ _ _).symm

/-- **The tensor product of correspondences is compatible with composition**: for schemes of
constant dimension with `B`, `B'` proper and rational correspondences `x ∈ Corrʳ(A, B)`,
`x' ∈ Corr^{r'}(A', B')`, `y ∈ Corrˢ(B, C)`, `y' ∈ Corr^{s'}(B', C')`,

  `(y ⊗ y') ∘ (x ⊗ x') = (y ∘ x) ⊗ (y' ∘ x')`  in  `Corr^{r+r'+s+s'}(A × A', C × C')`.

The two sides are compared through the identification of degrees
`(r + s) + (r' + s') = (r + r') + (s + s')`. -/
theorem composition_tensorBlock (hmul : Δ.FlatPullbackMul) (hproj : Δ.ProjectionFormula)
    (hassoc : Δ.IntersectionAssoc) (hsymm : Δ.IsSymmetric) {d d' e e' f f' : ℕ}
    (hA : RelativeDimension sA d) (hA' : RelativeDimension sA' d')
    (hB : RelativeDimension sB e) (hB' : RelativeDimension sB' e')
    (hC : RelativeDimension sC f) (hC' : RelativeDimension sC' f')
    (hP : RelativeDimension (prodBase sA sA') (d + d'))
    (hQ : RelativeDimension (prodBase sB sB') (e + e'))
    (hR : RelativeDimension (prodBase sC sC') (f + f')) (r r' s s' : ℤ)
    (x : Correspondence (fieldChowSituation k) sA sB e r)
    (x' : Correspondence (fieldChowSituation k) sA' sB' e' r')
    (y : Correspondence (fieldChowSituation k) sB sC f s)
    (y' : Correspondence (fieldChowSituation k) sB' sC' f' s') :
    composition k (prodBase sA sA') (prodBase sB sB') (prodBase sC sC') Δ hP hQ hR (r + r')
        (s + s') (tensorBlock k sA sA' sB sB' Δ hA hA' hB hB' r r' x x')
        (tensorBlock k sB sB' sC sC' Δ hB hB' hC hC' s s' y y') =
      correspondenceCongr k (prodBase sA sA') (prodBase sC sC') (by ring)
        (tensorBlock k sA sA' sC sC' Δ hA hA' hC hC' (r + s) (r' + s')
          (composition k sA sB sC Δ hA hB hC r s x y)
          (composition k sA' sB' sC' Δ hA' hB' hC' r' s' x' y')) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul q a =>
    induction x' using TensorProduct.induction_on with
    | zero => simp
    | add a' b' ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | tmul q' a' =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a'' b'' ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
      | tmul p c =>
        induction y' using TensorProduct.induction_on with
        | zero => simp
        | add a'' b'' ha hb => simp only [map_add, ha, hb]
        | tmul p' c' =>
          rw [tensorBlock_tmul, tensorBlock_tmul, composition_tmul, composition_tmul,
            composition_tmul, tensorBlock_tmul, correspondenceCongr_tmul,
            show q * q' * (p * p') = q * p * (q' * p') by ring]
          congr 1
          exact ((chowGroupDegreeEquiv_eq_iff_heq _ _ _ _ _).2
            (compositionInt_tensorInt_heq k sA sA' sB sB' sC sC' hmul hproj hassoc hsymm hA hA'
              hB hB' hC hC' hP hQ hR r r' s s' a a' c c').symm).symm

/-- `Stacks.WeilCohomology.composition_tensorBlock` for the canonical diagonal classes. -/
theorem composition_tensorBlock_canonical {d d' e e' f f' : ℕ}
    (hA : RelativeDimension sA d) (hA' : RelativeDimension sA' d')
    (hB : RelativeDimension sB e) (hB' : RelativeDimension sB' e')
    (hC : RelativeDimension sC f) (hC' : RelativeDimension sC' f')
    (hP : RelativeDimension (prodBase sA sA') (d + d'))
    (hQ : RelativeDimension (prodBase sB sB') (e + e'))
    (hR : RelativeDimension (prodBase sC sC') (f + f')) (r r' s s' : ℤ)
    (x : Correspondence (fieldChowSituation k) sA sB e r)
    (x' : Correspondence (fieldChowSituation k) sA' sB' e' r')
    (y : Correspondence (fieldChowSituation k) sB sC f s)
    (y' : Correspondence (fieldChowSituation k) sB' sC' f' s') :
    composition k (prodBase sA sA') (prodBase sB sB') (prodBase sC sC')
        (canonicalDiagonalClassFamily k) hP hQ hR (r + r') (s + s')
        (tensorBlock k sA sA' sB sB' (canonicalDiagonalClassFamily k) hA hA' hB hB' r r' x x')
        (tensorBlock k sB sB' sC sC' (canonicalDiagonalClassFamily k) hB hB' hC hC' s s' y y') =
      correspondenceCongr k (prodBase sA sA') (prodBase sC sC') (by ring)
        (tensorBlock k sA sA' sC sC' (canonicalDiagonalClassFamily k) hA hA' hC hC' (r + s)
          (r' + s') (composition k sA sB sC (canonicalDiagonalClassFamily k) hA hB hC r s x y)
          (composition k sA' sB' sC' (canonicalDiagonalClassFamily k) hA' hB' hC' r' s' x' y')) :=
  composition_tensorBlock k sA sA' sB sB' sC sC' (canonicalDiagonalClassFamily_flatPullbackMul k)
    (canonicalDiagonalClassFamily_projectionFormula k)
    (canonicalDiagonalClassFamily_intersectionAssoc k) (canonicalDiagonalClassFamily_isSymmetric k)
    hA hA' hB hB' hC hC' hP hQ hR r r' s s' x x' y y'

end Bifunctor

end Stacks.WeilCohomology

end
