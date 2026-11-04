module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Tensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.SmoothTransversalComposition

/-!
# The tensor product of the classes of two smooth closed subschemes

Let `k` be a field and let `X, X', Y, Y'` be smooth over `k` of constant dimensions
`d, d', e, e'`. For closed subschemes `A ⊆ X × Y` and `A' ⊆ X' × Y'` which are themselves smooth
over `k`, of constant dimensions `e - r` and `e' - r'`, the tensor product of correspondences of
Section 0FFZ, `[A] ⊗ [A'] = pr₁₃^*[A] · pr₂₄^*[A']`, is the class of the product

  `A ×_k A' ⟶ (X × X') × (Y × Y')`,   `(α, α') ↦ ((pr₁ α, pr₁ α'), (pr₂ α, pr₂ α'))`.

The inverse images `pr₁₃⁻¹(A)` and `pr₂₄⁻¹(A')` meet in `A ×_k A'`, in the expected dimension
`(e - r) + (e' - r')`, and all local rings involved are Cohen–Macaulay because everything is smooth
over `k`; so the proper-intersection formula of Stacks 0FFD, for the canonical family of diagonal
classes, computes the product.

## Main definitions

* `Stacks.WeilCohomology.tensorEmbedding`: the morphism `A ×_k A' ⟶ (X × X') × (Y × Y')`.
* `Stacks.WeilCohomology.tensorIntersectionIso`: the identification of the scheme-theoretic
  intersection `pr₁₃⁻¹(A) ∩ pr₂₄⁻¹(A')` with `A ×_k A'`.

## Main results

* `Stacks.WeilCohomology.isClosedImmersion_tensorEmbedding`: `A ×_k A'` is a closed subscheme of
  `(X × X') × (Y × Y')`.
* `Stacks.WeilCohomology.tensorInt_closedSubscheme`: `[A] ⊗ [A'] = [A ×_k A']` on integral Chow
  groups, for the canonical family of diagonal classes.
* `Stacks.WeilCohomology.tensorBlock_closedSubscheme`: the same on rational correspondences.

## References

* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

section Embedding

variable {S X X' Y Y' A A' : Scheme.{u}} (sX : X ⟶ S) (sX' : X' ⟶ S) (sY : Y ⟶ S) (sY' : Y' ⟶ S)
  (a : A ⟶ Limits.pullback sX sY) (a' : A' ⟶ Limits.pullback sX' sY') {qA : A ⟶ S}
  {qA' : A' ⟶ S} (hqA : a ≫ prodBase sX sY = qA) (hqA' : a' ≫ prodBase sX' sY' = qA')

/-- The morphism `A ×_k A' ⟶ (X × X') × (Y × Y')`, `(α, α') ↦ ((pr₁ α, pr₁ α'), (pr₂ α, pr₂ α'))`,
of two schemes `A ⟶ X × Y` and `A' ⟶ X' × Y'` over the base. -/
def tensorEmbedding : (Limits.pullback qA qA' : Scheme.{u}) ⟶ tensorProduct sX sX' sY sY' :=
  tensorLift sX sX' sY sY' (pullback.fst qA qA' ≫ a) (pullback.snd qA qA' ≫ a')
    (by rw [Category.assoc, Category.assoc, hqA, hqA', pullback.condition])

/-- The composite of the embedding with `pr₁₃` is `A ×_k A' ⟶ A ⟶ X × Y`. -/
@[reassoc (attr := simp)]
theorem tensorEmbedding_tensorPr₁₃ :
    tensorEmbedding sX sX' sY sY' a a' hqA hqA' ≫ tensorPr₁₃ sX sX' sY sY' =
      pullback.fst qA qA' ≫ a :=
  tensorLift_tensorPr₁₃ _ _ _ _ _ _ _

/-- The composite of the embedding with `pr₂₄` is `A ×_k A' ⟶ A' ⟶ X' × Y'`. -/
@[reassoc (attr := simp)]
theorem tensorEmbedding_tensorPr₂₄ :
    tensorEmbedding sX sX' sY sY' a a' hqA hqA' ≫ tensorPr₂₄ sX sX' sY sY' =
      pullback.snd qA qA' ≫ a' :=
  tensorLift_tensorPr₂₄ _ _ _ _ _ _ _

/-- The `X`-coordinate of the embedding is `A ×_k A' ⟶ A ⟶ X × Y ⟶ X`. -/
@[reassoc (attr := simp)]
theorem tensorEmbedding_fst_fst :
    tensorEmbedding sX sX' sY sY' a a' hqA hqA' ≫ pullback.fst (prodBase sX sX') (prodBase sY sY') ≫
        pullback.fst sX sX' = pullback.fst qA qA' ≫ a ≫ pullback.fst sX sY := by
  rw [← tensorPr₁₃_fst, tensorEmbedding_tensorPr₁₃_assoc]

/-- The `X'`-coordinate of the embedding is `A ×_k A' ⟶ A' ⟶ X' × Y' ⟶ X'`. -/
@[reassoc (attr := simp)]
theorem tensorEmbedding_fst_snd :
    tensorEmbedding sX sX' sY sY' a a' hqA hqA' ≫ pullback.fst (prodBase sX sX') (prodBase sY sY') ≫
        pullback.snd sX sX' = pullback.snd qA qA' ≫ a' ≫ pullback.fst sX' sY' := by
  rw [← tensorPr₂₄_fst, tensorEmbedding_tensorPr₂₄_assoc]

/-- The `Y`-coordinate of the embedding is `A ×_k A' ⟶ A ⟶ X × Y ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem tensorEmbedding_snd_fst :
    tensorEmbedding sX sX' sY sY' a a' hqA hqA' ≫ pullback.snd (prodBase sX sX') (prodBase sY sY') ≫
        pullback.fst sY sY' = pullback.fst qA qA' ≫ a ≫ pullback.snd sX sY := by
  rw [← tensorPr₁₃_snd, tensorEmbedding_tensorPr₁₃_assoc]

/-- The `Y'`-coordinate of the embedding is `A ×_k A' ⟶ A' ⟶ X' × Y' ⟶ Y'`. -/
@[reassoc (attr := simp)]
theorem tensorEmbedding_snd_snd :
    tensorEmbedding sX sX' sY sY' a a' hqA hqA' ≫ pullback.snd (prodBase sX sX') (prodBase sY sY') ≫
        pullback.snd sY sY' = pullback.snd qA qA' ≫ a' ≫ pullback.snd sX' sY' := by
  rw [← tensorPr₂₄_snd, tensorEmbedding_tensorPr₂₄_assoc]

/-- The structure morphism of `(X × X') × (Y × Y')` restricts along the embedding to the
structure morphism `A ×_k A' ⟶ A ⟶ S`. -/
theorem tensorEmbedding_tensorBase :
    tensorEmbedding sX sX' sY sY' a a' hqA hqA' ≫ tensorBase sX sX' sY sY' =
      pullback.fst qA qA' ≫ qA := by
  rw [← tensorPr₁₃_comp_prodBase, tensorEmbedding_tensorPr₁₃_assoc, hqA]

/-- The comparison morphism from `pr₁₃⁻¹(A) ∩ pr₂₄⁻¹(A')` to `A ×_k A'`. -/
def tensorIntersectionHom :
    (Limits.pullback (pullback.fst (tensorPr₁₃ sX sX' sY sY') a)
        (pullback.fst (tensorPr₂₄ sX sX' sY sY') a') : Scheme.{u}) ⟶ Limits.pullback qA qA' :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
    simp only [Category.assoc]
    rw [← hqA, ← hqA', ← pullback.condition_assoc, ← pullback.condition_assoc (g := a'),
      tensorPr₁₃_comp_prodBase, tensorPr₂₄_comp_prodBase, pullback.condition_assoc])

/-- The comparison morphism from `A ×_k A'` to `pr₁₃⁻¹(A) ∩ pr₂₄⁻¹(A')`. -/
def tensorIntersectionInv : (Limits.pullback qA qA' : Scheme.{u}) ⟶
    Limits.pullback (pullback.fst (tensorPr₁₃ sX sX' sY sY') a)
      (pullback.fst (tensorPr₂₄ sX sX' sY sY') a') :=
  pullback.lift
    (pullback.lift (tensorEmbedding sX sX' sY sY' a a' hqA hqA') (pullback.fst _ _)
      (tensorEmbedding_tensorPr₁₃ _ _ _ _ _ _ _ _))
    (pullback.lift (tensorEmbedding sX sX' sY sY' a a' hqA hqA') (pullback.snd _ _)
      (tensorEmbedding_tensorPr₂₄ _ _ _ _ _ _ _ _))
    (by rw [pullback.lift_fst, pullback.lift_fst])

/-- The scheme-theoretic intersection of `pr₁₃⁻¹(A)` and `pr₂₄⁻¹(A')` inside
`(X × X') × (Y × Y')` is `A ×_k A'`. -/
def tensorIntersectionIso :
    (Limits.pullback (pullback.fst (tensorPr₁₃ sX sX' sY sY') a)
        (pullback.fst (tensorPr₂₄ sX sX' sY sY') a') : Scheme.{u}) ≅ Limits.pullback qA qA' where
  hom := tensorIntersectionHom sX sX' sY sY' a a' hqA hqA'
  inv := tensorIntersectionInv sX sX' sY sY' a a' hqA hqA'
  hom_inv_id := by
    have h₁ := pullback.condition (f := tensorPr₁₃ sX sX' sY sY') (g := a)
    have h₂ := pullback.condition (f := tensorPr₂₄ sX sX' sY sY') (g := a')
    have h₃ := pullback.condition (f := pullback.fst (tensorPr₁₃ sX sX' sY sY') a)
      (g := pullback.fst (tensorPr₂₄ sX sX' sY sY') a')
    have he : tensorIntersectionHom sX sX' sY sY' a a' hqA hqA' ≫
        tensorEmbedding sX sX' sY sY' a a' hqA hqA' =
          pullback.fst _ _ ≫ pullback.fst (tensorPr₁₃ sX sX' sY sY') a := by
      apply tensorProduct_hom_ext
      · rw [Category.assoc, tensorEmbedding_tensorPr₁₃, tensorIntersectionHom,
          pullback.lift_fst_assoc, Category.assoc, Category.assoc, ← h₁]
      · rw [Category.assoc, tensorEmbedding_tensorPr₂₄, tensorIntersectionHom,
          pullback.lift_snd_assoc, Category.assoc, Category.assoc, ← h₂, reassoc_of% h₃]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, tensorIntersectionInv, pullback.lift_fst_assoc,
          pullback.lift_fst, he, Category.id_comp]
      · rw [Category.assoc, Category.assoc, tensorIntersectionInv, pullback.lift_fst_assoc,
          pullback.lift_snd, tensorIntersectionHom, pullback.lift_fst, Category.id_comp]
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, tensorIntersectionInv, pullback.lift_snd_assoc,
          pullback.lift_fst, he, Category.id_comp, h₃]
      · rw [Category.assoc, Category.assoc, tensorIntersectionInv, pullback.lift_snd_assoc,
          pullback.lift_snd, tensorIntersectionHom, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, tensorIntersectionHom, pullback.lift_fst, tensorIntersectionInv,
        pullback.lift_fst_assoc, pullback.lift_snd, Category.id_comp]
    · rw [Category.assoc, tensorIntersectionHom, pullback.lift_snd, tensorIntersectionInv,
        pullback.lift_snd_assoc, pullback.lift_snd, Category.id_comp]

/-- The identification of the intersection with `A ×_k A'` is compatible with the embeddings
into `(X × X') × (Y × Y')`. -/
theorem tensorIntersectionIso_hom_tensorEmbedding :
    (tensorIntersectionIso sX sX' sY sY' a a' hqA hqA').hom ≫
        tensorEmbedding sX sX' sY sY' a a' hqA hqA' =
      pullback.fst _ _ ≫ pullback.fst (tensorPr₁₃ sX sX' sY sY') a := by
  rw [← Iso.eq_inv_comp]
  show _ = tensorIntersectionInv sX sX' sY sY' a a' hqA hqA' ≫ _ ≫ _
  rw [tensorIntersectionInv, pullback.lift_fst_assoc, pullback.lift_fst]

/-- `A ×_k A'` is a closed subscheme of `(X × X') × (Y × Y')` when `A ⊆ X × Y` and
`A' ⊆ X' × Y'` are closed subschemes. -/
theorem isClosedImmersion_tensorEmbedding [IsClosedImmersion a] [IsClosedImmersion a'] :
    IsClosedImmersion (tensorEmbedding sX sX' sY sY' a a' hqA hqA') := by
  rw [← Iso.inv_hom_id_assoc (tensorIntersectionIso sX sX' sY sY' a a' hqA hqA')
    (tensorEmbedding sX sX' sY sY' a a' hqA hqA'), tensorIntersectionIso_hom_tensorEmbedding]
  infer_instance

end Embedding

section Formula

variable (k : Type u) [Field k] {X X' Y Y' : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sY' : Y' ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] [LocallyOfFiniteType sY]
  [LocallyOfFiniteType sY'] [Smooth sX] [Smooth sX'] [Smooth sY] [Smooth sY']
  [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY']

/-- The projection `pr₁₃ : (X × X') × (Y × Y') ⟶ X × Y` is smooth. -/
instance : Smooth (tensorPr₁₃ sX sX' sY sY') :=
  MorphismProperty.of_isPullback (isPullback_tensorPr₁₃_tensorPr₂₄ sX sX' sY sY').flip
    inferInstance

/-- The projection `pr₂₄ : (X × X') × (Y × Y') ⟶ X' × Y'` is smooth. -/
instance : Smooth (tensorPr₂₄ sX sX' sY sY') :=
  MorphismProperty.of_isPullback (isPullback_tensorPr₁₃_tensorPr₂₄ sX sX' sY sY') inferInstance

/-- The inverse image of a closed subscheme `a : A ⟶ Q` under a flat morphism `p : P ⟶ Q` of
relative dimension `r` has delta-dimension `m + r` on each irreducible component, when `A` has
delta-dimension `m` on each. -/
private theorem deltaDimension_pullback_fst_comp (k : Type u) [Field k] {P Q A : Scheme.{u}}
    (p : P ⟶ Q) [LocallyOfFiniteType p] [Flat p] (a : A ⟶ Q)
    [LocallyOfFiniteType a] {sP : P ⟶ (fieldChowSituation k).S} [LocallyOfFiniteType sP]
    (sQ : Q ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sQ] (hsP : p ≫ sQ = sP) (r : ℕ)
    (hp : RelativeDimension p r) {m : ℤ}
    (hA : ∀ T : irreducibleComponents A, deltaDimension (fieldChowSituation k) (a ≫ sQ)
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = m)
    (T : irreducibleComponents (Limits.pullback p a : Scheme.{u})) :
    deltaDimension (fieldChowSituation k) (pullback.fst p a ≫ sP)
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = m + r := by
  rw [deltaDimension_congr (g := pullback.snd p a ≫ a ≫ sQ)
    (by rw [← pullback.condition_assoc, hsP])]
  exact deltaDimension_irreducibleComponent_of_flat _ _ r (relativeDimension_pullback_snd _ a _ hp)
    hA T

/-- **`[A] ⊗ [A'] = [A ×_k A']`.** Let `a : A ⟶ X × Y` and `a' : A' ⟶ X' × Y'` be closed immersions
with `A` and `A'` smooth over `k` of constant dimensions `e - r` and `e' - r'`. Then, for the
canonical family of diagonal classes, the tensor product `pr₁₃^*[A] · pr₂₄^*[A']` of their classes
is the class of `A ×_k A'` embedded in `(X × X') × (Y × Y')`. -/
theorem tensorInt_closedSubscheme {d d' e e' : ℕ} (hX : RelativeDimension sX d)
    (hX' : RelativeDimension sX' d') (hY : RelativeDimension sY e)
    (hY' : RelativeDimension sY' e') (r r' : ℤ) {A A' : Scheme.{u}}
    (a : A ⟶ Limits.pullback sX sY) [IsClosedImmersion a]
    (a' : A' ⟶ Limits.pullback sX' sY') [IsClosedImmersion a']
    {qA : A ⟶ (fieldChowSituation k).S} {qA' : A' ⟶ (fieldChowSituation k).S}
    [Smooth qA] [Smooth qA'] (hqA : a ≫ prodBase sX sY = qA)
    (hqA' : a' ≫ prodBase sX' sY' = qA') {nA nA' : ℕ} (hA : RelativeDimension qA nA)
    (hA' : RelativeDimension qA' nA') (hnA : (nA : ℤ) = e - r) (hnA' : (nA' : ℤ) = e' - r') :
    haveI := isClosedImmersion_tensorEmbedding sX sX' sY sY' a a' hqA hqA'
    tensorInt k sX sX' sY sY' (canonicalDiagonalClassFamily k) hX hX' hY hY' r r'
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sY) a ((e : ℤ) - r)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX' sY') a' ((e' : ℤ) - r'))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (tensorBase sX sX' sY sY') (tensorEmbedding sX sX' sY sY' a a' hqA hqA')
        (((e + e' : ℕ) : ℤ) - (r + r'))) := by
  have := isClosedImmersion_tensorEmbedding sX sX' sY sY' a a' hqA hqA'
  let : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian qA
  let : IsLocallyNoetherian A' := LocallyOfFiniteType.isLocallyNoetherian qA'
  set i₁ := pullback.fst (tensorPr₁₃ sX sX' sY sY') a
  set i₂ := pullback.fst (tensorPr₂₄ sX sX' sY sY') a'
  have hAc : ∀ T : irreducibleComponents A, deltaDimension (fieldChowSituation k)
      (a ≫ prodBase sX sY) ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ =
        (e : ℤ) - r := fun T ↦ (deltaDimension_congr hqA _).trans
    (deltaDimension_irreducibleComponent_of_relativeDimension_eq k _ hA hnA T)
  have hAc' : ∀ T : irreducibleComponents A', deltaDimension (fieldChowSituation k)
      (a' ≫ prodBase sX' sY') ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ =
        (e' : ℤ) - r' := fun T ↦ (deltaDimension_congr hqA' _).trans
    (deltaDimension_irreducibleComponent_of_relativeDimension_eq k _ hA' hnA' T)
  have h₁ := deltaDimension_pullback_fst_comp k (tensorPr₁₃ sX sX' sY sY') a (prodBase sX sY)
    (tensorPr₁₃_comp_prodBase sX sX' sY sY') (e' + d')
    (relativeDimension_tensorPr₁₃ k sX sX' sY sY' hX' hY') hAc
  have h₂ := deltaDimension_pullback_fst_comp k (tensorPr₂₄ sX sX' sY sY') a' (prodBase sX' sY')
    (tensorPr₂₄_comp_prodBase sX sX' sY sY') (e + d)
    (relativeDimension_tensorPr₂₄ k sX sX' sY sY' hX hY) hAc'
  set φ := tensorIntersectionIso sX sX' sY sY' a a' hqA hqA' with hφ
  have hmor : pullback.fst i₁ i₂ ≫ i₁ ≫ tensorBase sX sX' sY sY' =
      φ.hom ≫ prodBase qA qA' := by
    rw [← Category.assoc, ← tensorIntersectionIso_hom_tensorEmbedding, Category.assoc,
      tensorEmbedding_tensorBase]
  have h₃ : schemeDeltaDimension (fieldChowSituation k)
      (pullback.fst i₁ i₂ ≫ i₁ ≫ tensorBase sX sX' sY sY') ≤
        ((((e + e' : ℕ) : ℤ) - (r + r') : ℤ) : EInt) := by
    rw [schemeDeltaDimension_congr _ hmor, schemeDeltaDimension_comp_iso]
    exact schemeDeltaDimension_le_of_forall_irreducibleComponent _
      (deltaDimension_irreducibleComponent_of_relativeDimension_eq k _
        (relativeDimension_prodBase k qA qA' hA hA') (by push_cast; omega))
  have h₄ : Intersection.CohenMacaulayAtIntersection k (tensorBase sX sX' sY sY') i₁ i₂
      (((e + e' : ℕ) : ℤ) - (r + r')) := by
    intro ζ _
    exact ⟨isCohenMacaulayLocalRing_stalk_of_smooth_of_isCohenMacaulayLocalRing k
        (pullback.snd (tensorPr₁₃ sX sX' sY sY') a) qA _
        (isCohenMacaulayLocalRing_stalk_of_smooth k qA _),
      isCohenMacaulayLocalRing_stalk_of_smooth_of_isCohenMacaulayLocalRing k
        (pullback.snd (tensorPr₂₄ sX sX' sY sY') a') qA' _
        (isCohenMacaulayLocalRing_stalk_of_smooth k qA' _)⟩
  simp only [tensorInt, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
    AddMonoidHom.coe_toIntLinearMap, LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv]
  rw [flatPullbackChow_mk_cycleAssociatedToClosedSubscheme (tensorBase sX sX' sY sY')
      (prodBase sX sY) (tensorPr₁₃ sX sX' sY sY') (tensorPr₁₃_comp_prodBase sX sX' sY sY')
      (e' + d') (relativeDimension_tensorPr₁₃ k sX sX' sY sY' hX' hY') a _
      (schemeDeltaDimension_le_of_forall_irreducibleComponent _ hAc),
    flatPullbackChow_mk_cycleAssociatedToClosedSubscheme (tensorBase sX sX' sY sY')
      (prodBase sX' sY') (tensorPr₂₄ sX sX' sY sY') (tensorPr₂₄_comp_prodBase sX sX' sY sY')
      (e + d) (relativeDimension_tensorPr₂₄ k sX sX' sY sY' hX hY) a' _
      (schemeDeltaDimension_le_of_forall_irreducibleComponent _ hAc')]
  refine (canonicalDiagonalClassFamily_properIntersectionFormula k (tensorBase sX sX' sY sY') _
    (relativeDimension_tensorBase k sX sX' sY sY' hX hX' hY hY') i₁ i₂ _ _ _ _ h₁ h₂ h₃
    h₄).trans ?_
  rw [cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ φ
    (tensorIntersectionIso_hom_tensorEmbedding sX sX' sY sY' a a' hqA hqA')]

/-- **`[A] ⊗ [A'] = [A ×_k A']` on rational correspondences**, for the canonical family of diagonal
classes. -/
theorem tensorBlock_closedSubscheme {d d' e e' : ℕ} (hX : RelativeDimension sX d)
    (hX' : RelativeDimension sX' d') (hY : RelativeDimension sY e)
    (hY' : RelativeDimension sY' e') (r r' : ℤ) {A A' : Scheme.{u}}
    (a : A ⟶ Limits.pullback sX sY) [IsClosedImmersion a]
    (a' : A' ⟶ Limits.pullback sX' sY') [IsClosedImmersion a']
    {qA : A ⟶ (fieldChowSituation k).S} {qA' : A' ⟶ (fieldChowSituation k).S}
    [Smooth qA] [Smooth qA'] (hqA : a ≫ prodBase sX sY = qA)
    (hqA' : a' ≫ prodBase sX' sY' = qA') {nA nA' : ℕ} (hA : RelativeDimension qA nA)
    (hA' : RelativeDimension qA' nA') (hnA : (nA : ℤ) = e - r) (hnA' : (nA' : ℤ) = e' - r')
    (q q' : ℚ) :
    haveI := isClosedImmersion_tensorEmbedding sX sX' sY sY' a a' hqA hqA'
    tensorBlock k sX sX' sY sY' (canonicalDiagonalClassFamily k) hX hX' hY hY' r r'
        (q ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sY) a ((e : ℤ) - r)))
        (q' ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX' sY') a' ((e' : ℤ) - r'))) =
      (q * q') ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (tensorBase sX sX' sY sY') (tensorEmbedding sX sX' sY sY' a a' hqA hqA')
        (((e + e' : ℕ) : ℤ) - (r + r'))) := by
  rw [tensorBlock_tmul, tensorInt_closedSubscheme k sX sX' sY sY' hX hX' hY hY' r r' a a' hqA hqA'
    hA hA' hnA hnA']

end Formula

end Stacks.WeilCohomology

end
