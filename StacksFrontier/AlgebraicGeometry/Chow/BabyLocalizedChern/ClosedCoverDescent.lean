module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentLift
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.ClosedCoverExactSequence

/-!
# Descent of operations along the Chow groups of a closed cover

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `T` be locally of
finite type over `S` and let `a : A ⟶ T`, `b : B ⟶ T` be closed immersions whose images cover `T`.
Stacks 0F94 says that

  `A_k(A ×_T B) ⟶ A_k(A) ⊕ A_k(B) ⟶ A_k(T) ⟶ 0`

is exact. In the library that statement is made for two ideal sheaves on `T`; this file reads it
for two arbitrary closed immersions, through the isomorphisms of their sources with their
scheme-theoretic images.

The consequence used for Stacks 0F9H is a descent principle: an additive map
`φ : A_k(B) ⟶ M` which kills every class `y` with `a_* x + b_* y = 0` induces an additive map
`A_k(T) ⟶ M` sending `a_* x + b_* y` to `φ y`.

## Main results

* `Stacks.Chow.exists_chowPush_add_chowPush_eq` — every class on `T` is `a_* x + b_* y`.
* `Stacks.Chow.exists_eq_neg_chowPush_of_chowPush_add_chowPush_eq_zero` — if `a_* x + b_* y = 0`
  then `y` is minus the pushforward of a class on a closed subscheme `W` of `B` whose inclusion
  into `T` factors through `A`.
* `Stacks.Chow.closedCoverDescent` — the descended map, with its defining formula
  `Stacks.Chow.closedCoverDescent_apply`.
* `Stacks.Chow.closedCover_addMonoidHom_ext` — two additive maps out of `A_k(T)` agreeing on the
  classes pushed forward from `A` and from `B` are equal.

## References

* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Proper pushforward around a commutative square: `v_* u_* x = v'_* u'_* x` when
`u ≫ v = u' ≫ v'`. -/
theorem chowPush_comm_square (C : ChowSituation.{u}) {A B B' D : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sB' : B' ⟶ C.S)
    [LocallyOfFiniteType sB'] (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (u : A ⟶ B) [IsProper u]
    (v : B ⟶ D) [IsProper v] (u' : A ⟶ B') [IsProper u'] (v' : B' ⟶ D) [IsProper v']
    (hsq : u ≫ v = u' ≫ v') (hu : u ≫ sB = sA) (hv : v ≫ sD = sB) (hu' : u' ≫ sB' = sA)
    (hv' : v' ≫ sD = sB') (k : ℤ) (x : chowGroup C sA k) :
    chowPush C sB sD v hv k (chowPush C sA sB u hu k x) =
      chowPush C sB' sD v' hv' k (chowPush C sA sB' u' hu' k x) := by
  rw [chowPush_comp C sA sB sD u v (u ≫ v) rfl hu hv (by rw [Category.assoc, hv, hu]) k x,
    chowPush_comp C sA sB' sD u' v' (u' ≫ v') rfl hu' hv' (by rw [Category.assoc, hv', hu']) k x]
  exact chowPush_congr C sA sD hsq _ _ k x

section ClosedCover

variable (C : ChowSituation.{u}) {T A B : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT]
  (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
  (a : A ⟶ T) [IsClosedImmersion a] (ha : a ≫ sT = sA)
  (b : B ⟶ T) [IsClosedImmersion b] (hb : b ≫ sT = sB)

/-- The scheme-theoretic images of two closed immersions whose images cover `T` cover `T`. -/
theorem support_ker_sup_support_ker_eq_top
    (hcover : Set.range a.base ∪ Set.range b.base = Set.univ) :
    a.ker.support ⊔ b.ker.support = ⊤ := by
  refine SetLike.coe_injective ?_
  rw [TopologicalSpace.Closeds.coe_sup, Scheme.Hom.support_ker, Scheme.Hom.support_ker,
    a.isClosedEmbedding.isClosed_range.closure_eq, b.isClosedEmbedding.isClosed_range.closure_eq,
    hcover, TopologicalSpace.Closeds.coe_top]

/-- The inverse of `A ≅ a.image` followed by `a` is the inclusion of the image. -/
private theorem inv_toImage_comp_hom : inv a.toImage ≫ a = a.ker.subschemeι := by
  rw [IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]

omit [LocallyOfFiniteType sA] in
include ha in
/-- The structure morphism of the scheme-theoretic image of `a`, read through the inverse of the
isomorphism `A ≅ a.image`. -/
theorem inv_toImage_comp_structureMorphism :
    inv a.toImage ≫ sA = a.ker.subschemeι ≫ sT := by
  rw [← ha, ← Category.assoc, inv_toImage_comp_hom]

omit [LocallyOfFiniteType sA] in
include ha in
/-- The structure morphism of `A`, read through the isomorphism `A ≅ a.image`. -/
theorem toImage_comp_structureMorphism :
    a.toImage ≫ a.ker.subschemeι ≫ sT = sA := by
  rw [Scheme.Hom.toImage_imageι_assoc, ha]

/-- Pushing forward to the image and then into `T` is pushing forward along `a`. -/
theorem chowPush_imageι_chowPush_toImage (k : ℤ) (x : chowGroup C sA k) :
    chowPush C (a.ker.subschemeι ≫ sT) sT a.ker.subschemeι rfl k
        (chowPush C sA (a.ker.subschemeι ≫ sT) a.toImage
          (toImage_comp_structureMorphism C sT sA a ha) k x) =
      chowPush C sA sT a ha k x :=
  chowPush_comp C sA _ sT a.toImage a.ker.subschemeι a (Scheme.Hom.toImage_imageι a) _ rfl ha k x

/-- Pushing forward along `a` the class transported from the image is pushing forward along the
inclusion of the image. -/
theorem chowPush_chowPush_inv_toImage (k : ℤ) (x : chowGroup C (a.ker.subschemeι ≫ sT) k) :
    chowPush C sA sT a ha k
        (chowPush C (a.ker.subschemeι ≫ sT) sA (inv a.toImage)
          (inv_toImage_comp_structureMorphism C sT sA a ha) k x) =
      chowPush C (a.ker.subschemeι ≫ sT) sT a.ker.subschemeι rfl k x :=
  chowPush_comp C _ sA sT (inv a.toImage) a a.ker.subschemeι
    (inv_toImage_comp_hom a) _ ha rfl k x

/-- **Stacks 0F94, surjectivity, for two closed immersions.** If the images of `a` and `b` cover
`T`, every class on `T` is `a_* x + b_* y`. -/
theorem exists_chowPush_add_chowPush_eq
    (hcover : Set.range a.base ∪ Set.range b.base = Set.univ) (k : ℤ) (α : chowGroup C sT k) :
    ∃ (x : chowGroup C sA k) (y : chowGroup C sB k),
      chowPush C sA sT a ha k x + chowPush C sB sT b hb k y = α := by
  obtain ⟨⟨x, y⟩, hxy⟩ := surjective_summandsToUnionChow C sT a.ker b.ker k
    (support_ker_sup_support_ker_eq_top a b hcover) α
  refine ⟨chowPush C _ sA (inv a.toImage) (inv_toImage_comp_structureMorphism C sT sA a ha) k x,
    chowPush C _ sB (inv b.toImage) (inv_toImage_comp_structureMorphism C sT sB b hb) k y, ?_⟩
  rw [chowPush_chowPush_inv_toImage, chowPush_chowPush_inv_toImage]
  exact hxy

/-- **Stacks 0F94, exactness in the middle, for two closed immersions.** If `a_* x + b_* y = 0`,
then `y` is minus the pushforward of a class on a scheme `W` with a closed immersion `w_b` into
`B` and a morphism `w_a` into `A` such that `w_a ≫ a = w_b ≫ b`: the scheme-theoretic
intersection. -/
theorem exists_eq_neg_chowPush_of_chowPush_add_chowPush_eq_zero
    (hcover : Set.range a.base ∪ Set.range b.base = Set.univ) (k : ℤ) (x : chowGroup C sA k)
    (y : chowGroup C sB k)
    (hxy : chowPush C sA sT a ha k x + chowPush C sB sT b hb k y = 0) :
    ∃ (W : Scheme.{u}) (wa : W ⟶ A) (wb : W ⟶ B) (_ : IsClosedImmersion wb),
      wa ≫ a = wb ≫ b ∧
        ∃ γ : chowGroup C (wb ≫ sB) k, y = -chowPush C (wb ≫ sB) sB wb rfl k γ := by
  set I := a.ker
  set J := b.ker
  set x' := chowPush C sA (I.subschemeι ≫ sT) a.toImage
    (toImage_comp_structureMorphism C sT sA a ha) k x
  set y' := chowPush C sB (J.subschemeι ≫ sT) b.toImage
    (toImage_comp_structureMorphism C sT sB b hb) k y
  have hsum : summandsToUnionChow C sT I J k (x', y') = 0 := by
    show chowPush C (I.subschemeι ≫ sT) sT I.subschemeι rfl k x' +
      chowPush C (J.subschemeι ≫ sT) sT J.subschemeι rfl k y' = 0
    rwa [chowPush_imageι_chowPush_toImage, chowPush_imageι_chowPush_toImage]
  obtain ⟨γ, hγ⟩ := (exact_intersectionToSummandsChow_summandsToUnionChow C sT I J k
    (support_ker_sup_support_ker_eq_top a b hcover) (x', y')).mp hsum
  have hy' : y' = -chowPush C ((I ⊔ J).subschemeι ≫ sT) (J.subschemeι ≫ sT)
      (Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J))
      (Scheme.IdealSheafData.inclusion_subschemeι_assoc (le_sup_right : J ≤ I ⊔ J) sT) k γ :=
    (congrArg Prod.snd hγ).symm
  let wb : (I ⊔ J).subscheme ⟶ B :=
    Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J) ≫ inv b.toImage
  let wa : (I ⊔ J).subscheme ⟶ A :=
    Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J) ≫ inv a.toImage
  have hwb : wb ≫ sB = (I ⊔ J).subschemeι ≫ sT := by
    simp only [wb, Category.assoc, ← hb, reassoc_of% (inv_toImage_comp_hom b)]
    exact Scheme.IdealSheafData.inclusion_subschemeι_assoc _ _
  refine ⟨(I ⊔ J).subscheme, wa, wb, inferInstance, ?_,
    chowPush C ((I ⊔ J).subschemeι ≫ sT) (wb ≫ sB) (𝟙 _) (by rw [Category.id_comp, hwb]) k γ,
    ?_⟩
  · simp only [wa, wb, I, J, Category.assoc, inv_toImage_comp_hom a, inv_toImage_comp_hom b,
      Scheme.IdealSheafData.inclusion_subschemeι]
  · have hy : y = chowPush C (J.subschemeι ≫ sT) sB (inv b.toImage)
        (inv_toImage_comp_structureMorphism C sT sB b hb) k y' := by
      rw [chowPush_comp C sB _ sB b.toImage (inv b.toImage) (𝟙 B) (IsIso.hom_inv_id _) _ _
        (Category.id_comp sB) k y, chowPush_id]
    rw [hy, hy', map_neg, chowPush_comp C _ _ sB (𝟙 _) wb wb (Category.id_comp wb) _ rfl hwb,
      chowPush_comp C _ _ sB _ (inv b.toImage) wb rfl _ _ hwb]

/-- The sum of the two pushforwards, `A_k(A) ⊕ A_k(B) ⟶ A_k(T)`. -/
abbrev closedCoverSum (k : ℤ) : chowGroup C sA k × chowGroup C sB k →+ chowGroup C sT k :=
  (chowPush C sA sT a ha k).coprod (chowPush C sB sT b hb k)

/-- If the images of `a` and `b` cover `T`, then `A_k(A) ⊕ A_k(B) ⟶ A_k(T)`,
`(x, y) ↦ a_* x + b_* y`, is surjective. -/
theorem surjective_closedCoverSum (hcover : Set.range a.base ∪ Set.range b.base = Set.univ)
    (k : ℤ) : Function.Surjective (closedCoverSum C sT sA sB a ha b hb k) := by
  intro α
  obtain ⟨x, y, h⟩ := exists_chowPush_add_chowPush_eq C sT sA sB a ha b hb hcover k α
  exact ⟨(x, y), h⟩

/-- **The descent principle of Stacks 0F94.** An additive map `φ : A_k(B) ⟶ M` killing every `y`
with `a_* x + b_* y = 0` descends to an additive map `A_k(T) ⟶ M`, which sends `a_* x + b_* y` to
`φ y` (`Stacks.Chow.closedCoverDescent_apply`). -/
def closedCoverDescent {M : Type*} [AddCommGroup M]
    (hcover : Set.range a.base ∪ Set.range b.base = Set.univ) (k : ℤ)
    (φ : chowGroup C sB k →+ M)
    (hφ : ∀ (x : chowGroup C sA k) (y : chowGroup C sB k),
      chowPush C sA sT a ha k x + chowPush C sB sT b hb k y = 0 → φ y = 0) :
    chowGroup C sT k →+ M :=
  (QuotientAddGroup.lift (closedCoverSum C sT sA sB a ha b hb k).ker
      (φ.comp (AddMonoidHom.snd _ _)) fun z hz ↦ hφ z.1 z.2 hz).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective (closedCoverSum C sT sA sB a ha b hb k)
      (surjective_closedCoverSum C sT sA sB a ha b hb hcover k)).symm.toAddMonoidHom

/-- **The defining formula of the descended map**: on `a_* x + b_* y` it is `φ y`. -/
theorem closedCoverDescent_apply {M : Type*} [AddCommGroup M]
    (hcover : Set.range a.base ∪ Set.range b.base = Set.univ) (k : ℤ)
    (φ : chowGroup C sB k →+ M)
    (hφ : ∀ (x : chowGroup C sA k) (y : chowGroup C sB k),
      chowPush C sA sT a ha k x + chowPush C sB sT b hb k y = 0 → φ y = 0)
    (x : chowGroup C sA k) (y : chowGroup C sB k) :
    closedCoverDescent C sT sA sB a ha b hb hcover k φ hφ
        (chowPush C sA sT a ha k x + chowPush C sB sT b hb k y) = φ y := by
  have hsymm : (QuotientAddGroup.quotientKerEquivOfSurjective
      (closedCoverSum C sT sA sB a ha b hb k)
      (surjective_closedCoverSum C sT sA sB a ha b hb hcover k)).symm
        (chowPush C sA sT a ha k x + chowPush C sB sT b hb k y) =
      QuotientAddGroup.mk' (closedCoverSum C sT sA sB a ha b hb k).ker (x, y) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  unfold closedCoverDescent
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hsymm]
  rfl

/-- **Uniqueness from Stacks 0F94.** Two additive maps out of `A_k(T)` that agree on the classes
pushed forward from `A` and on those pushed forward from `B` are equal. -/
theorem closedCover_addMonoidHom_ext {M : Type*} [AddCommGroup M]
    (hcover : Set.range a.base ∪ Set.range b.base = Set.univ) (k : ℤ)
    (F G : chowGroup C sT k →+ M)
    (hA : ∀ x : chowGroup C sA k, F (chowPush C sA sT a ha k x) = G (chowPush C sA sT a ha k x))
    (hB : ∀ y : chowGroup C sB k, F (chowPush C sB sT b hb k y) = G (chowPush C sB sT b hb k y)) :
    F = G := by
  refine AddMonoidHom.ext fun α ↦ ?_
  obtain ⟨x, y, rfl⟩ := exists_chowPush_add_chowPush_eq C sT sA sB a ha b hb hcover k α
  rw [map_add, map_add, hA, hB]

end ClosedCover

end Stacks.Chow

end
