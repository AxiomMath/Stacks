module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionBasePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional

/-!
# The tensor product of correspondences

Before Stacks 0FG7 the source defines, for smooth projective schemes `X, X', Y, Y'` over a field
`k`, the tensor product of correspondences

  `⊗ : Corrʳ(X, Y) × Corr^{r'}(X', Y') ⟶ Corr^{r+r'}(X × X', Y × Y')`,
  `c ⊗ c' = pr₁₃^* c · pr₂₄^* c'`,

where `pr₁₃ : X × X' × Y × Y' ⟶ X × Y` and `pr₂₄ : X × X' × Y × Y' ⟶ X' × Y'` are the
projections. This file constructs it.

## Main definitions

* `Stacks.WeilCohomology.tensorPr₁₃` and `Stacks.WeilCohomology.tensorPr₂₄`: the two projections
  of `(A × A') × (B × B')`, with the cartesian square
  `Stacks.WeilCohomology.isPullback_tensorPr₁₃_tensorPr₂₄` exhibiting `(A × A') × (B × B')` as
  `(A × B) × (A' × B')`. Hence `pr₁₃` and `pr₂₄` are flat, of the relative dimensions of `A' × B'`
  and `A × B`.
* `Stacks.WeilCohomology.tensorInt` and `Stacks.WeilCohomology.tensorBlock`: the tensor product
  `c ⊗ c' = pr₁₃^* c · pr₂₄^* c'` for schemes of constant dimension, on integral Chow groups and
  on rational correspondences.
* `Stacks.WeilCohomology.partProdHom`: the open and closed immersion
  `X_d × X'_{d'} ⟶ (X × X')_{d+d'}` of the product of two equidimensional parts into the part of
  the product of the same dimension.
* `Stacks.WeilCohomology.tensor`: **the tensor product of correspondences**
  `Corrʳ(X, Y) × Corr^{r'}(X', Y') ⟶ Corr^{r+r'}(X × X', Y × Y')` between smooth schemes of mixed
  dimension. On the blocks `c_{d,e} ∈ Corrʳ(X_d, Y_e)` and
  `c'_{d',e'} ∈ Corr^{r'}(X'_{d'}, Y'_{e'})` it is `pr₁₃^* c_{d,e} · pr₂₄^* c'_{d',e'}` on
  `X_d × X'_{d'} × Y_e × Y'_{e'}`, pushed into the block `(d + d', e + e')` of `X × X'` and
  `Y × Y'`.

## Implementation notes

The source's formula is used verbatim on the equidimensional parts, where `pr₁₃` and `pr₂₄` are
flat of constant relative dimension and the intersection product of Stacks 0FC0 is formed on the
equidimensional scheme `X_d × X'_{d'} × Y_e × Y'_{e'}`. A general smooth projective scheme is the
disjoint union of its equidimensional parts, and `X_d × X'_{d'} × Y_e × Y'_{e'}` is an open and
closed subscheme of `(X × X')_{d+d'} × (Y × Y')_{e+e'}`. So the pushforward along that inclusion
is the identification of a cycle on the piece with a cycle on the whole product, and the sum over
all blocks is `pr₁₃^* c · pr₂₄^* c'` on `X × X' × Y × Y'`.

As in `StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Composition`, the intersection
products are formed with a family `Δ` of diagonal classes; the category of correspondences uses
the canonical family.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### The fourfold product `(A × A') × (B × B')` and its projections -/

section Fourfold

variable {S A A' B B' : Scheme.{u}} (sA : A ⟶ S) (sA' : A' ⟶ S) (sB : B ⟶ S) (sB' : B' ⟶ S)

/-- The product `(A × A') × (B × B')` over `S`. -/
abbrev tensorProduct : Scheme.{u} := Limits.pullback (prodBase sA sA') (prodBase sB sB')

/-- The structure morphism of `(A × A') × (B × B')`. -/
abbrev tensorBase : tensorProduct sA sA' sB sB' ⟶ S := prodBase (prodBase sA sA') (prodBase sB sB')

/-- The projection `pr₁₃ : (A × A') × (B × B') ⟶ A × B`. -/
def tensorPr₁₃ : tensorProduct sA sA' sB sB' ⟶ Limits.pullback sA sB :=
  Limits.pullback.lift
    (Limits.pullback.fst (prodBase sA sA') (prodBase sB sB') ≫ Limits.pullback.fst sA sA')
    (Limits.pullback.snd (prodBase sA sA') (prodBase sB sB') ≫ Limits.pullback.fst sB sB')
    (by simpa only [Category.assoc] using Limits.pullback.condition)

/-- The projection `pr₂₄ : (A × A') × (B × B') ⟶ A' × B'`. -/
def tensorPr₂₄ : tensorProduct sA sA' sB sB' ⟶ Limits.pullback sA' sB' :=
  Limits.pullback.lift
    (Limits.pullback.fst (prodBase sA sA') (prodBase sB sB') ≫ Limits.pullback.snd sA sA')
    (Limits.pullback.snd (prodBase sA sA') (prodBase sB sB') ≫ Limits.pullback.snd sB sB')
    (by
      rw [Category.assoc, Category.assoc, ← Limits.pullback.condition (f := sA) (g := sA'),
        ← Limits.pullback.condition (f := sB) (g := sB')]
      simpa only [Category.assoc] using
        Limits.pullback.condition (f := prodBase sA sA') (g := prodBase sB sB'))

/-- The first component of `pr₁₃` is the projection `(A × A') × (B × B') ⟶ A × A' ⟶ A`. -/
@[reassoc (attr := simp)]
theorem tensorPr₁₃_fst : tensorPr₁₃ sA sA' sB sB' ≫ Limits.pullback.fst sA sB =
    Limits.pullback.fst (prodBase sA sA') (prodBase sB sB') ≫ Limits.pullback.fst sA sA' :=
  Limits.pullback.lift_fst _ _ _

/-- The second component of `pr₁₃` is the projection `(A × A') × (B × B') ⟶ B × B' ⟶ B`. -/
@[reassoc (attr := simp)]
theorem tensorPr₁₃_snd : tensorPr₁₃ sA sA' sB sB' ≫ Limits.pullback.snd sA sB =
    Limits.pullback.snd (prodBase sA sA') (prodBase sB sB') ≫ Limits.pullback.fst sB sB' :=
  Limits.pullback.lift_snd _ _ _

/-- The first component of `pr₂₄` is the projection `(A × A') × (B × B') ⟶ A × A' ⟶ A'`. -/
@[reassoc (attr := simp)]
theorem tensorPr₂₄_fst : tensorPr₂₄ sA sA' sB sB' ≫ Limits.pullback.fst sA' sB' =
    Limits.pullback.fst (prodBase sA sA') (prodBase sB sB') ≫ Limits.pullback.snd sA sA' :=
  Limits.pullback.lift_fst _ _ _

/-- The second component of `pr₂₄` is the projection `(A × A') × (B × B') ⟶ B × B' ⟶ B'`. -/
@[reassoc (attr := simp)]
theorem tensorPr₂₄_snd : tensorPr₂₄ sA sA' sB sB' ≫ Limits.pullback.snd sA' sB' =
    Limits.pullback.snd (prodBase sA sA') (prodBase sB sB') ≫ Limits.pullback.snd sB sB' :=
  Limits.pullback.lift_snd _ _ _

/-- `pr₁₃` is a morphism over `S`. -/
theorem tensorPr₁₃_comp_prodBase :
    tensorPr₁₃ sA sA' sB sB' ≫ prodBase sA sB = tensorBase sA sA' sB sB' := by
  rw [prodBase, tensorPr₁₃_fst_assoc]

/-- `pr₂₄` is a morphism over `S`. -/
theorem tensorPr₂₄_comp_prodBase :
    tensorPr₂₄ sA sA' sB sB' ≫ prodBase sA' sB' = tensorBase sA sA' sB sB' := by
  rw [prodBase, tensorPr₂₄_fst_assoc, ← Limits.pullback.condition (f := sA) (g := sA')]

/-- The morphism `T ⟶ (A × A') × (B × B')` determined by morphisms `T ⟶ A × B` and
`T ⟶ A' × B'` over `S`. -/
def tensorLift {T : Scheme.{u}} (u : T ⟶ Limits.pullback sA sB) (v : T ⟶ Limits.pullback sA' sB')
    (h : u ≫ prodBase sA sB = v ≫ prodBase sA' sB') : T ⟶ tensorProduct sA sA' sB sB' :=
  Limits.pullback.lift
    (Limits.pullback.lift (u ≫ Limits.pullback.fst sA sB) (v ≫ Limits.pullback.fst sA' sB')
      (by simpa only [Category.assoc] using h))
    (Limits.pullback.lift (u ≫ Limits.pullback.snd sA sB) (v ≫ Limits.pullback.snd sA' sB') (by
      rw [Category.assoc, Category.assoc, ← Limits.pullback.condition (f := sA) (g := sB),
        ← Limits.pullback.condition (f := sA') (g := sB')]
      simpa only [Category.assoc] using h))
    (by
      rw [prodBase, prodBase, Limits.pullback.lift_fst_assoc, Limits.pullback.lift_fst_assoc,
        Category.assoc, Category.assoc, Limits.pullback.condition (f := sA) (g := sB)])

/-- The composite of `tensorLift u v h` with `pr₁₃` is `u`. -/
@[reassoc (attr := simp)]
theorem tensorLift_tensorPr₁₃ {T : Scheme.{u}} (u : T ⟶ Limits.pullback sA sB)
    (v : T ⟶ Limits.pullback sA' sB') (h : u ≫ prodBase sA sB = v ≫ prodBase sA' sB') :
    tensorLift sA sA' sB sB' u v h ≫ tensorPr₁₃ sA sA' sB sB' = u := by
  apply Limits.pullback.hom_ext <;> simp [tensorLift, Limits.pullback.lift_fst_assoc,
    Limits.pullback.lift_snd_assoc, Limits.pullback.lift_fst]

/-- The composite of `tensorLift u v h` with `pr₂₄` is `v`. -/
@[reassoc (attr := simp)]
theorem tensorLift_tensorPr₂₄ {T : Scheme.{u}} (u : T ⟶ Limits.pullback sA sB)
    (v : T ⟶ Limits.pullback sA' sB') (h : u ≫ prodBase sA sB = v ≫ prodBase sA' sB') :
    tensorLift sA sA' sB sB' u v h ≫ tensorPr₂₄ sA sA' sB sB' = v := by
  apply Limits.pullback.hom_ext <;> simp [tensorLift, Limits.pullback.lift_fst_assoc,
    Limits.pullback.lift_snd_assoc, Limits.pullback.lift_snd]

/-- Morphisms into `(A × A') × (B × B')` are determined by their composites with `pr₁₃` and
`pr₂₄`. -/
theorem tensorProduct_hom_ext {T : Scheme.{u}} {m m' : T ⟶ tensorProduct sA sA' sB sB'}
    (h₁ : m ≫ tensorPr₁₃ sA sA' sB sB' = m' ≫ tensorPr₁₃ sA sA' sB sB')
    (h₂ : m ≫ tensorPr₂₄ sA sA' sB sB' = m' ≫ tensorPr₂₄ sA sA' sB sB') : m = m' := by
  have h₁₁ := congrArg (· ≫ Limits.pullback.fst sA sB) h₁
  have h₁₂ := congrArg (· ≫ Limits.pullback.snd sA sB) h₁
  have h₂₁ := congrArg (· ≫ Limits.pullback.fst sA' sB') h₂
  have h₂₂ := congrArg (· ≫ Limits.pullback.snd sA' sB') h₂
  simp only [Category.assoc, tensorPr₁₃_fst, tensorPr₁₃_snd, tensorPr₂₄_fst,
    tensorPr₂₄_snd] at h₁₁ h₁₂ h₂₁ h₂₂
  apply Limits.pullback.hom_ext <;> apply Limits.pullback.hom_ext <;>
    simpa only [Category.assoc]

/-- `(A × A') × (B × B')` is the product `(A × B) × (A' × B')`, through `pr₁₃` and `pr₂₄`. -/
theorem isPullback_tensorPr₁₃_tensorPr₂₄ :
    IsPullback (tensorPr₁₃ sA sA' sB sB') (tensorPr₂₄ sA sA' sB sB') (prodBase sA sB)
      (prodBase sA' sB') := by
  refine IsPullback.of_isLimit' ⟨by rw [tensorPr₁₃_comp_prodBase, tensorPr₂₄_comp_prodBase]⟩ ?_
  refine PullbackCone.IsLimit.mk _ (fun s ↦ tensorLift sA sA' sB sB' s.fst s.snd s.condition)
    (fun s ↦ tensorLift_tensorPr₁₃ _ _ _ _ _ _ _) (fun s ↦ tensorLift_tensorPr₂₄ _ _ _ _ _ _ _)
    (fun s m h₁ h₂ ↦ tensorProduct_hom_ext sA sA' sB sB'
      ((h₁.trans (tensorLift_tensorPr₁₃ _ _ _ _ _ _ _).symm))
      ((h₂.trans (tensorLift_tensorPr₂₄ _ _ _ _ _ _ _).symm)))

end Fourfold

/-! ### The tensor product for schemes of constant dimension -/

section Equidimensional

variable (k : Type u) [Field k] {A A' B B' : Scheme.{u}}
  (sA : A ⟶ (fieldChowSituation k).S) (sA' : A' ⟶ (fieldChowSituation k).S)
  (sB : B ⟶ (fieldChowSituation k).S) (sB' : B' ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] [LocallyOfFiniteType sB]
  [LocallyOfFiniteType sB']

/-- `pr₁₃` is locally of finite type. -/
instance : LocallyOfFiniteType (tensorPr₁₃ sA sA' sB sB') :=
  MorphismProperty.of_isPullback (isPullback_tensorPr₁₃_tensorPr₂₄ sA sA' sB sB').flip
    inferInstance

/-- `pr₂₄` is locally of finite type. -/
instance : LocallyOfFiniteType (tensorPr₂₄ sA sA' sB sB') :=
  MorphismProperty.of_isPullback (isPullback_tensorPr₁₃_tensorPr₂₄ sA sA' sB sB') inferInstance

/-- `pr₁₃` is flat when `A'` and `B'` are flat over `S`. -/
instance [Flat sA'] [Flat sB'] : Flat (tensorPr₁₃ sA sA' sB sB') :=
  MorphismProperty.of_isPullback (isPullback_tensorPr₁₃_tensorPr₂₄ sA sA' sB sB').flip
    inferInstance

/-- `pr₂₄` is flat when `A` and `B` are flat over `S`. -/
instance [Flat sA] [Flat sB] : Flat (tensorPr₂₄ sA sA' sB sB') :=
  MorphismProperty.of_isPullback (isPullback_tensorPr₁₃_tensorPr₂₄ sA sA' sB sB') inferInstance

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] in
/-- `pr₁₃` has the relative dimension `e' + d'` of `A' × B'`. -/
theorem relativeDimension_tensorPr₁₃ {d' e' : ℕ} (hA' : RelativeDimension sA' d')
    (hB' : RelativeDimension sB' e') : RelativeDimension (tensorPr₁₃ sA sA' sB sB') (e' + d') :=
  RelativeDimension.of_isPullback (isPullback_tensorPr₁₃_tensorPr₂₄ sA sA' sB sB').flip
    (relativeDimension_prodBase k sA' sB' hA' hB')

omit [LocallyOfFiniteType sA'] [LocallyOfFiniteType sB'] in
/-- `pr₂₄` has the relative dimension `e + d` of `A × B`. -/
theorem relativeDimension_tensorPr₂₄ {d e : ℕ} (hA : RelativeDimension sA d)
    (hB : RelativeDimension sB e) : RelativeDimension (tensorPr₂₄ sA sA' sB sB') (e + d) :=
  RelativeDimension.of_isPullback (isPullback_tensorPr₁₃_tensorPr₂₄ sA sA' sB sB')
    (relativeDimension_prodBase k sA sB hA hB)

/-- `(A × A') × (B × B')` has dimension `(e' + e) + (d' + d)`. -/
theorem relativeDimension_tensorBase {d d' e e' : ℕ} (hA : RelativeDimension sA d)
    (hA' : RelativeDimension sA' d') (hB : RelativeDimension sB e)
    (hB' : RelativeDimension sB' e') :
    RelativeDimension (tensorBase sA sA' sB sB') ((e' + e) + (d' + d)) :=
  relativeDimension_prodBase k (prodBase sA sA') (prodBase sB sB')
    (relativeDimension_prodBase k sA sA' hA hA') (relativeDimension_prodBase k sB sB' hB hB')

variable [Smooth sA] [Smooth sA'] [Smooth sB] [Smooth sB'] (Δ : DiagonalClassFamily k)

/-- **The tensor product** `c ⊗ c' = pr₁₃^* c · pr₂₄^* c'` on integral Chow groups, for `A`, `A'`,
`B`, `B'` of dimensions `d`, `d'`, `e`, `e'` and `c ∈ A_{e-r}(A × B)`, `c' ∈ A_{e'-r'}(A' × B')`: a
class in `A_{(e+e')-(r+r')}((A × A') × (B × B'))`, as a `ℤ`-bilinear map. The product is formed
with the diagonal class `Δ` of `(A × A') × (B × B')`. -/
def tensorInt {d d' e e' : ℕ} (hA : RelativeDimension sA d) (hA' : RelativeDimension sA' d')
    (hB : RelativeDimension sB e) (hB' : RelativeDimension sB' e') (r r' : ℤ) :
    chowGroup (fieldChowSituation k) (prodBase sA sB) ((e : ℤ) - r) →ₗ[ℤ]
      chowGroup (fieldChowSituation k) (prodBase sA' sB') ((e' : ℤ) - r') →ₗ[ℤ]
        chowGroup (fieldChowSituation k) (tensorBase sA sA' sB sB')
          (((e + e' : ℕ) : ℤ) - (r + r')) :=
  ((selfIntersectionProduct (fieldChowSituation k)
      (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
      (fieldGysinSystem k) (tensorBase sA sA' sB sB') _
      (Δ _ _ (relativeDimension_tensorBase k sA sA' sB sB' hA hA' hB hB'))
      (((e : ℤ) - r) + ((e' + d' : ℕ) : ℤ)) (((e' : ℤ) - r') + ((e + d : ℕ) : ℤ))).compl₁₂
    (flatPullbackChow (fieldChowSituation k) (tensorBase sA sA' sB sB') (prodBase sA sB)
      (tensorPr₁₃ sA sA' sB sB') (tensorPr₁₃_comp_prodBase sA sA' sB sB') (e' + d')
      (relativeDimension_tensorPr₁₃ k sA sA' sB sB' hA' hB') _
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)).toIntLinearMap
    (flatPullbackChow (fieldChowSituation k) (tensorBase sA sA' sB sB') (prodBase sA' sB')
      (tensorPr₂₄ sA sA' sB sB') (tensorPr₂₄_comp_prodBase sA sA' sB sB') (e + d)
      (relativeDimension_tensorPr₂₄ k sA sA' sB sB' hA hB) _
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)).toIntLinearMap
    ).compr₂
    (chowGroupDegreeEquiv (fieldChowSituation k) (tensorBase sA sA' sB sB')
      (by push_cast; ring)).toIntLinearEquiv.toLinearMap

/-- **The tensor product of correspondences**
`Corrʳ(A, B) × Corr^{r'}(A', B') ⟶ Corr^{r+r'}(A × A', B × B')`,
`(c, c') ↦ pr₁₃^* c · pr₂₄^* c'`, as a `ℚ`-bilinear map, for `A`, `A'`, `B`, `B'` of dimensions
`d`, `d'`, `e`, `e'`. -/
def tensorBlock {d d' e e' : ℕ} (hA : RelativeDimension sA d) (hA' : RelativeDimension sA' d')
    (hB : RelativeDimension sB e) (hB' : RelativeDimension sB' e') (r r' : ℤ) :
    Correspondence (fieldChowSituation k) sA sB e r →ₗ[ℚ]
      Correspondence (fieldChowSituation k) sA' sB' e' r' →ₗ[ℚ]
        Correspondence (fieldChowSituation k) (prodBase sA sA') (prodBase sB sB')
          ((e + e' : ℕ) : ℤ) (r + r') :=
  rationalBilin (tensorInt k sA sA' sB sB' Δ hA hA' hB hB' r r')

/-- On pure tensors, `tensorBlock` is `tensorInt` with the rational coefficients multiplied. -/
@[simp]
theorem tensorBlock_tmul {d d' e e' : ℕ} (hA : RelativeDimension sA d)
    (hA' : RelativeDimension sA' d') (hB : RelativeDimension sB e)
    (hB' : RelativeDimension sB' e') (r r' : ℤ) (q q' : ℚ)
    (c : chowGroup (fieldChowSituation k) (prodBase sA sB) ((e : ℤ) - r))
    (c' : chowGroup (fieldChowSituation k) (prodBase sA' sB') ((e' : ℤ) - r')) :
    tensorBlock k sA sA' sB sB' Δ hA hA' hB hB' r r' (q ⊗ₜ[ℤ] c) (q' ⊗ₜ[ℤ] c') =
      (q * q') ⊗ₜ[ℤ] tensorInt k sA sA' sB sB' Δ hA hA' hB hB' r r' c c' :=
  rationalBilin_tmul _ _ _ _ _

end Equidimensional

/-! ### Products of equidimensional parts -/

section Parts

variable {S X X' : Scheme.{u}} (sX : X ⟶ S) (sX' : X' ⟶ S) [Smooth sX] [Smooth sX']

/-- Relative dimension is a property of the morphism, whatever the proof of local finite type. -/
theorem relativeDimension_of_eq {V : Scheme.{u}} {f g : V ⟶ S} [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] (h : f = g) {n : ℕ} (hf : RelativeDimension f n) :
    RelativeDimension g n := by
  subst h; exact hf

/-- An open subscheme over which a smooth morphism has relative dimension `n` lies in the part of
relative dimension `n`. -/
theorem range_subset_dimPart {V : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] {n : ℕ}
    (h : RelativeDimension (j ≫ sX) n) : Set.range j ⊆ (dimPart sX n : Set X) := by
  rintro _ ⟨v, rfl⟩
  obtain ⟨m, hm⟩ := (isClopenDecomposition_dimPart sX).exists_mem (j v)
  have h₁ := topologicalKrullDimAt_fiber_eq_of_relativeDimension sX (dimPart sX m) m
    (relativeDimension_partBase sX m) (j v) hm
  have h₂ := topologicalKrullDimAt_fiber_eq_of_relativeDimension (j ≫ sX) ⊤ n
    (RelativeDimension.comp_isOpenImmersion (⊤ : V.Opens).ι (j ≫ sX) h) v trivial
  rw [fiberDimensionAt_comp_openImmersion j sX v, h₁] at h₂
  have hmn : m = n := by exact_mod_cast h₂
  exact hmn ▸ hm

/-- The inclusion `X_d × X'_{d'} ⟶ X × X'` of the product of two parts. -/
abbrev partProdMap (d d' : ℕ) :
    (Limits.pullback (partBase sX d) (partBase sX' d') : Scheme.{u}) ⟶ Limits.pullback sX sX' :=
  Limits.pullback.map (partBase sX d) (partBase sX' d') sX sX' (dimPart sX d).ι
    (dimPart sX' d').ι (𝟙 S) ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)

/-- The inclusion `X_d × X'_{d'} ⟶ X × X'` is an open immersion. -/
instance (d d' : ℕ) : IsOpenImmersion (partProdMap sX sX' d d') :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl rfl

/-- The first component of `X_d × X'_{d'} ⟶ X × X'` is the inclusion `X_d ⟶ X`. -/
@[reassoc (attr := simp)]
theorem partProdMap_fst (d d' : ℕ) :
    partProdMap sX sX' d d' ≫ Limits.pullback.fst sX sX' =
      Limits.pullback.fst (partBase sX d) (partBase sX' d') ≫ (dimPart sX d).ι :=
  Limits.pullback.lift_fst _ _ _

/-- The second component of `X_d × X'_{d'} ⟶ X × X'` is the inclusion `X'_{d'} ⟶ X'`. -/
@[reassoc (attr := simp)]
theorem partProdMap_snd (d d' : ℕ) :
    partProdMap sX sX' d d' ≫ Limits.pullback.snd sX sX' =
      Limits.pullback.snd (partBase sX d) (partBase sX' d') ≫ (dimPart sX' d').ι :=
  Limits.pullback.lift_snd _ _ _

/-- The inclusion `X_d × X'_{d'} ⟶ X × X'` is a morphism over `S`. -/
theorem partProdMap_comp_prodBase (d d' : ℕ) :
    partProdMap sX sX' d d' ≫ prodBase sX sX' = prodBase (partBase sX d) (partBase sX' d') := by
  rw [prodBase, partProdMap_fst_assoc]

end Parts

section PartsOverField

variable (k : Type u) [Field k] {X X' : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sX' : X' ⟶ (fieldChowSituation k).S) [Smooth sX] [Smooth sX']

/-- The product `X_d × X'_{d'}` of two parts lies in the part `(X × X')_{d+d'}` of the product. -/
theorem range_partProdMap_subset (d d' : ℕ) :
    Set.range (partProdMap sX sX' d d') ⊆ (dimPart (prodBase sX sX') (d + d') : Set _) := by
  refine range_subset_dimPart (prodBase sX sX') (partProdMap sX sX' d d') ?_
  rw [Nat.add_comm]
  exact relativeDimension_of_eq (partProdMap_comp_prodBase sX sX' d d').symm
    (relativeDimension_prodBase k _ _ (relativeDimension_partBase sX d)
      (relativeDimension_partBase sX' d'))

/-- **The product of two parts in the part of the product**: the open immersion
`X_d × X'_{d'} ⟶ (X × X')_{d+d'}`. -/
def partProdHom (d d' : ℕ) :
    (Limits.pullback (partBase sX d) (partBase sX' d') : Scheme.{u}) ⟶
      (dimPart (prodBase sX sX') (d + d')).toScheme :=
  IsOpenImmersion.lift (dimPart (prodBase sX sX') (d + d')).ι (partProdMap sX sX' d d')
    (by rw [Scheme.Opens.range_ι]; exact range_partProdMap_subset k sX sX' d d')

/-- The composite of `partProdHom` with the inclusion of `(X × X')_{d+d'}` is `partProdMap`. -/
@[reassoc (attr := simp)]
theorem partProdHom_ι (d d' : ℕ) :
    partProdHom k sX sX' d d' ≫ (dimPart (prodBase sX sX') (d + d')).ι =
      partProdMap sX sX' d d' :=
  IsOpenImmersion.lift_fac _ _ _

/-- The morphism `X_d × X'_{d'} ⟶ (X × X')_{d+d'}` is an open immersion. -/
instance (d d' : ℕ) : IsOpenImmersion (partProdHom k sX sX' d d') := by
  have : IsOpenImmersion (partProdHom k sX sX' d d' ≫ (dimPart (prodBase sX sX') (d + d')).ι) := by
    rw [partProdHom_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ (dimPart (prodBase sX sX') (d + d')).ι

/-- The morphism `X_d × X'_{d'} ⟶ (X × X')_{d+d'}` is a morphism over `k`. -/
theorem partProdHom_comp_partBase (d d' : ℕ) :
    partProdHom k sX sX' d d' ≫ partBase (prodBase sX sX') (d + d') =
      prodBase (partBase sX d) (partBase sX' d') := by
  show partProdHom k sX sX' d d' ≫ (dimPart (prodBase sX sX') (d + d')).ι ≫ prodBase sX sX' = _
  rw [partProdHom_ι_assoc, partProdMap_comp_prodBase]

/-- For `X` and `X'` proper, `X_d × X'_{d'} ⟶ (X × X')_{d+d'}` is proper. -/
instance [IsProper sX] [IsProper sX'] (d d' : ℕ) : IsProper (partProdHom k sX sX' d d') := by
  have : IsProper (partProdHom k sX sX' d d' ≫ partBase (prodBase sX sX') (d + d')) := by
    rw [partProdHom_comp_partBase]; infer_instance
  exact IsProper.of_comp _ (partBase (prodBase sX sX') (d + d'))

end PartsOverField

/-! ### The tensor product of correspondences -/

section Mixed

variable (k : Type u) [Field k] {X X' Y Y' : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sY' : Y' ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX'] [Smooth sY] [IsSeparated sY]
  [Smooth sY'] [IsSeparated sY'] [IsProper sX] [IsProper sX'] [IsProper sY] [IsProper sY']
  (Δ : DiagonalClassFamily k)

/-- The open and closed immersion
`(X_d × X'_{d'}) × (Y_e × Y'_{e'}) ⟶ (X × X')_{d+d'} × (Y × Y')_{e+e'}` of a block of the fourfold
product into the corresponding block. -/
abbrev tensorBlockHom (d d' e e' : ℕ) :
    tensorProduct (partBase sX d) (partBase sX' d') (partBase sY e) (partBase sY' e') ⟶
      Limits.pullback (partBase (prodBase sX sX') (d + d'))
        (partBase (prodBase sY sY') (e + e')) :=
  prodHom (partBase (prodBase sX sX') (d + d')) (partBase (prodBase sY sY') (e + e'))
    (prodBase (partBase sX d) (partBase sX' d')) (prodBase (partBase sY e) (partBase sY' e'))
    (partProdHom k sX sX' d d') (partProdHom k sY sY' e e')
    (partProdHom_comp_partBase k sX sX' d d') (partProdHom_comp_partBase k sY sY' e e')

/-- The inclusion of a block of the fourfold product is a morphism over `k`. -/
theorem tensorBlockHom_comp_prodBase (d d' e e' : ℕ) :
    tensorBlockHom k sX sX' sY sY' d d' e e' ≫
        prodBase (partBase (prodBase sX sX') (d + d')) (partBase (prodBase sY sY') (e + e')) =
      tensorBase (partBase sX d) (partBase sX' d') (partBase sY e) (partBase sY' e') :=
  prodHom_comp_prodBase _ _ _ _ _ _ _ _

/-- The inclusion of a block of the fourfold product is proper. -/
instance (d d' e e' : ℕ) : IsProper (tensorBlockHom k sX sX' sY sY' d d' e e') := by
  have : IsProper (tensorBlockHom k sX sX' sY sY' d d' e e' ≫
      prodBase (partBase (prodBase sX sX') (d + d')) (partBase (prodBase sY sY') (e + e'))) := by
    rw [tensorBlockHom_comp_prodBase]; infer_instance
  exact IsProper.of_comp _
    (prodBase (partBase (prodBase sX sX') (d + d')) (partBase (prodBase sY sY') (e + e')))

/-- Pushforward of a correspondence on the block `(X_d × X'_{d'}) × (Y_e × Y'_{e'})` into the block
`(X × X')_{d+d'} × (Y × Y')_{e+e'}` of `Corr(X × X', Y × Y')`. -/
def tensorBlockInclusion (d d' e e' : ℕ) (r : ℤ) :
    Correspondence (fieldChowSituation k) (prodBase (partBase sX d) (partBase sX' d'))
        (prodBase (partBase sY e) (partBase sY' e')) ((e + e' : ℕ) : ℤ) r →ₗ[ℚ]
      Correspondence (fieldChowSituation k) (partBase (prodBase sX sX') (d + d'))
        (partBase (prodBase sY sY') (e + e')) ((e + e' : ℕ) : ℤ) r :=
  (properChowPushforward (fieldChowSituation k) _ _ (tensorBlockHom k sX sX' sY sY' d d' e e')
    (tensorBlockHom_comp_prodBase k sX sX' sY sY' d d' e e') _
    (properPushforwardDescends _ _ _ _ _ _)).toIntLinearMap.baseChange ℚ

/-- On pure tensors, `tensorBlockInclusion` is the proper pushforward along `tensorBlockHom`. -/
@[simp]
theorem tensorBlockInclusion_tmul (d d' e e' : ℕ) (r : ℤ) (q : ℚ)
    (c : chowGroup (fieldChowSituation k) (tensorBase (partBase sX d) (partBase sX' d')
      (partBase sY e) (partBase sY' e')) (((e + e' : ℕ) : ℤ) - r)) :
    tensorBlockInclusion k sX sX' sY sY' d d' e e' r (q ⊗ₜ[ℤ] c) =
      q ⊗ₜ[ℤ] properChowPushforward (fieldChowSituation k) _ _
        (tensorBlockHom k sX sX' sY sY' d d' e e')
        (tensorBlockHom_comp_prodBase k sX sX' sY sY' d d' e e') _
        (properPushforwardDescends _ _ _ _ _ _) c :=
  rfl

/-- The `((d, e), (d', e'))` block of the tensor product, `c ⊗ c'` for `c ∈ Corrʳ(X_d, Y_e)` and
`c' ∈ Corr^{r'}(X'_{d'}, Y'_{e'})`, read in the block `(d + d', e + e')` of
`Corr(X × X', Y × Y')`. -/
def tensorBlockMixed (r r' : ℤ) (d e d' e' : ℕ) :
    Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r →ₗ[ℚ]
      Correspondence (fieldChowSituation k) (partBase sX' d') (partBase sY' e') e' r' →ₗ[ℚ]
        Corr k (prodBase sX sX') (prodBase sY sY') (r + r') :=
  (tensorBlock k (partBase sX d) (partBase sX' d') (partBase sY e) (partBase sY' e') Δ
      (relativeDimension_partBase sX d) (relativeDimension_partBase sX' d')
      (relativeDimension_partBase sY e) (relativeDimension_partBase sY' e') r r').compr₂
    ((DirectSum.lof ℚ ℕ (fun D : ℕ ↦ DirectSum ℕ fun E : ℕ ↦
        Correspondence (fieldChowSituation k) (partBase (prodBase sX sX') D)
          (partBase (prodBase sY sY') E) E (r + r')) (d + d')).comp
      ((DirectSum.lof ℚ ℕ (fun E : ℕ ↦
        Correspondence (fieldChowSituation k) (partBase (prodBase sX sX') (d + d'))
          (partBase (prodBase sY sY') E) E (r + r')) (e + e')).comp
        (tensorBlockInclusion k sX sX' sY sY' d d' e e' (r + r'))))

/-- **The tensor product of correspondences** (before Stacks 0FG7)

  `⊗ : Corrʳ(X, Y) × Corr^{r'}(X', Y') ⟶ Corr^{r+r'}(X × X', Y × Y')`,
  `c ⊗ c' = pr₁₃^* c · pr₂₄^* c'`,

as a `ℚ`-bilinear map, for smooth proper `X, X', Y, Y'` over `k` of mixed dimension. On the blocks
`c_{d,e} ∈ Corrʳ(X_d, Y_e)` and `c'_{d',e'} ∈ Corr^{r'}(X'_{d'}, Y'_{e'})` of `c` and `c'` it is
`pr₁₃^* c_{d,e} · pr₂₄^* c'_{d',e'}` on `(X_d × X'_{d'}) × (Y_e × Y'_{e'})`, read in the block
`(d + d', e + e')` of `X × X'` and `Y × Y'` through the open and closed immersion
`Stacks.WeilCohomology.tensorBlockHom`. Here `X × X'` and `Y × Y'` are the fibre products
`Limits.pullback sX sX'` and `Limits.pullback sY sY'`, and the fourfold product is
`(X × X') × (Y × Y')`. -/
def tensor (r r' : ℤ) :
    Corr k sX sY r →ₗ[ℚ] Corr k sX' sY' r' →ₗ[ℚ]
      Corr k (prodBase sX sX') (prodBase sY sY') (r + r') :=
  DirectSum.toModule ℚ ℕ _ fun d ↦ DirectSum.toModule ℚ ℕ _ fun e ↦
    (DirectSum.toModule ℚ ℕ _ fun d' ↦ DirectSum.toModule ℚ ℕ _ fun e' ↦
      (tensorBlockMixed k sX sX' sY sY' Δ r r' d e d' e').flip).flip

/-- The tensor product on blocks. -/
@[simp]
theorem tensor_lof_lof (r r' : ℤ) (d e d' e' : ℕ)
    (c : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (c' : Correspondence (fieldChowSituation k) (partBase sX' d') (partBase sY' e') e' r') :
    tensor k sX sX' sY sY' Δ r r'
        (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c))
        (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' c')) =
      DirectSum.lof ℚ ℕ _ (d + d') (DirectSum.lof ℚ ℕ _ (e + e')
        (tensorBlockInclusion k sX sX' sY sY' d d' e e' (r + r')
          (tensorBlock k (partBase sX d) (partBase sX' d') (partBase sY e) (partBase sY' e') Δ
            (relativeDimension_partBase sX d) (relativeDimension_partBase sX' d')
            (relativeDimension_partBase sY e) (relativeDimension_partBase sY' e') r r' c c'))) := by
  simp [tensor, tensorBlockMixed]

end Mixed

end Stacks.WeilCohomology

end
