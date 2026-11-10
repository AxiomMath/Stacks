module

public import StacksFrontier.AlgebraicGeometry.Chow.TripleIntersectionProductExterior
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Associativity
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonal

/-!
# Associativity of the canonical intersection product

Let `k` be a field and `W` a scheme smooth over `k` of constant dimension `N`. The
intersection product on `CH_*(W)` formed with the Gysin class `Δ^!` of the diagonal of Stacks
0FBR, `Stacks.Chow.selfIntersectionProduct`, is the product `α · β = Δ^!(α × β)` of Stacks 0FC0
for `Y = Z = W` over `X = W`, read on `W` through the projection `W ×_W W ≅ W`. Stacks 0FC1
asserts that the product of Stacks 0FC0 is associative,

  `(α · β) · γ = α · (β · γ)`   in   `CH_*(Y ×_X Z ×_X W)`,

and this file deduces that the product on `W` is associative, which is the property
`Stacks.WeilCohomology.DiagonalClassFamily.IntersectionAssoc` of the canonical family of diagonal
classes.

The deduction compares the iterated products on `W` with the two sides of Stacks 0FC1 on the
triple fibre product `W ×_W W ×_W W`. Feeding `α · β ∈ CH_*(W)` back into the product means
pushing the class on `W ×_W W` forward along `W ×_W W ≅ W` first; the intersection product is
natural with respect to isomorphisms of its factors over `X`, so this pushforward can be moved
outside, and both bracketings become pushforwards to `W` of the two sides of Stacks 0FC1 along
projections that agree through the associator of the triple fibre product.

## Main results

* `Stacks.Chow.intersectionProduct_chowPushforwardOfIso_tmul`: the intersection product of
  Stacks 0FC0 is natural with respect to isomorphisms of its factors over `X`.
* `Stacks.Chow.selfIntersectionProduct_selfIntersectionProduct_left` and
  `Stacks.Chow.selfIntersectionProduct_selfIntersectionProduct_right`: the two bracketings of the
  product on `W` are pushforwards to `W` of the two sides of Stacks 0FC1.
* `Stacks.Chow.selfIntersectionProduct_assoc_of_isAssociativeIntersectionProduct`: Stacks 0FC1
  for `Y = Z = W = X` gives associativity of the product on `W`.
* `Stacks.WeilCohomology.canonicalDiagonalClassFamily_intersectionAssoc`: the canonical family of
  diagonal classes has associative intersection products.

## Implementation notes

The two sides of Stacks 0FC1 live on `(W ×_W W) ×_W W` and `W ×_W (W ×_W W)` in the degrees
`(n + m - N) + l - N` and `n + (m + l - N) - N`, and the left factor of the outer product is
presented on the structure morphism `(pr₁ ≫ 𝟙) ≫ s_W` of `W ×_W W`
(`Stacks.Chow.intersectionProductReassoc`). The comparisons are made up to heterogeneous
equality and closed by pushforward along isomorphisms over the base,
`Stacks.Chow.chowPushforwardOfIso`, and its functoriality.

## References

* [Stacks Project, Tag 0FC1](https://stacks.math.columbia.edu/tag/0FC1)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Naturality of the intersection product under isomorphisms of the factors -/

section Naturality

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
  {X Y Z Y' Z' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b]
  (a' : Y' ⟶ X) [LocallyOfFiniteType a'] (b' : Z' ⟶ X) [LocallyOfFiniteType b']
  (φ₁ : Y' ⟶ Y) [IsIso φ₁] (φ₂ : Z' ⟶ Z) [IsIso φ₂] (h₁ : φ₁ ≫ a = a') (h₂ : φ₂ ≫ b = b')
  (d : ℤ)
  (c : BivariantClass C G sX (selfProductStructure C sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX) d)

include h₁ h₂ in
/-- **The intersection product is natural with respect to isomorphisms of the factors.** Let
`φ₁ : Y' ⟶ Y` and `φ₂ : Z' ⟶ Z` be isomorphisms over `X`, so that `a' = φ₁ ≫ a` and
`b' = φ₂ ≫ b`. For `x ∈ CH_n(Y')` and `y ∈ CH_m(Z')`,

  `φ₁_* x · φ₂_* y = (φ₁ ×_X φ₂)_*(x · y)`   in   `CH_{n+m-d}(Y ×_X Z)`.

The isomorphism `φ₁ ×_k φ₂` carries `x × y` to `φ₁_* x × φ₂_* y` (Stacks 0FBV), the cap of the
diagonal class commutes with pushforward along an isomorphism of test schemes (Stacks 0B76 (1)),
and `φ₁ ×_X φ₂` is the induced isomorphism of the pullbacks of the diagonal. -/
theorem intersectionProduct_chowPushforwardOfIso_tmul (n m : ℤ)
    (x : chowGroup C (a' ≫ sX) n) (y : chowGroup C (b' ≫ sX) m) :
    intersectionProduct C hδ G sX a b d c n m
        (chowPushforwardOfIso C (a' ≫ sX) (a ≫ sX) φ₁ (by rw [← h₁, Category.assoc]) n x ⊗ₜ[ℤ]
          chowPushforwardOfIso C (b' ≫ sX) (b ≫ sX) φ₂ (by rw [← h₂, Category.assoc]) m y) =
      chowPushforwardOfIso C (pullback.fst a' b' ≫ (a' ≫ sX)) (pullback.fst a b ≫ (a ≫ sX))
        (pullback.map a' b' a b φ₁ φ₂ (𝟙 X) (by simp [h₁]) (by simp [h₂]))
        (by simp [← h₁]) (n + m - d)
        (intersectionProduct C hδ G sX a' b' d c n m (x ⊗ₜ[ℤ] y)) := by
  subst h₁ h₂
  set Ψ := pullback.map ((φ₁ ≫ a) ≫ sX) ((φ₂ ≫ b) ≫ sX) (a ≫ sX) (b ≫ sX) φ₁ φ₂ (𝟙 C.S)
    (by simp) (by simp) with hΨ
  have hm : Ψ ≫ exteriorToSelfProduct C sX a b =
      exteriorToSelfProduct C sX (φ₁ ≫ a) (φ₂ ≫ b) := by
    ext <;> simp [hΨ, exteriorToSelfProduct, exteriorToSelfProductMap]
  rw [intersectionProduct_apply, intersectionProduct_apply,
    ← chowPushforwardOfIso_pullbackMap_chowExteriorProduct_tmul C (a ≫ sX) ((φ₁ ≫ a) ≫ sX)
      (b ≫ sX) ((φ₂ ≫ b) ≫ sX) φ₁ φ₂ (by simp) (by simp) hδ n m x y]
  have hE := BivariantClass.cap_heq_chowPushforwardOfIso c (exteriorToSelfProduct C sX a b) Ψ
    (exteriorToSelfProduct C sX (φ₁ ≫ a) (φ₂ ≫ b)) hm rfl
    (chowExteriorProduct C hδ ((φ₁ ≫ a) ≫ sX) ((φ₂ ≫ b) ≫ sX) n m (x ⊗ₜ[ℤ] y))
    (chowGroupCongr C (exteriorToSelfProduct_comp_selfProductStructure C sX a b).symm (n + m)
      (chowPushforwardOfIso C (pullback.fst ((φ₁ ≫ a) ≫ sX) ((φ₂ ≫ b) ≫ sX) ≫ (φ₁ ≫ a) ≫ sX)
        (pullback.fst (a ≫ sX) (b ≫ sX) ≫ a ≫ sX) Ψ (by simp [hΨ]) (n + m)
        (chowExteriorProduct C hδ ((φ₁ ≫ a) ≫ sX) ((φ₂ ≫ b) ≫ sX) n m (x ⊗ₜ[ℤ] y))))
    (by rw [exteriorToSelfProduct_comp_selfProductStructure]; simp [hΨ])
    ((chowGroupCongr_heq _ _ _ _).trans (chowPushforwardOfIso_heq _ _ _ rfl
      (exteriorToSelfProduct_comp_selfProductStructure C sX a b).symm rfl HEq.rfl))
    (chowGroupCongr C
      (exteriorToSelfProduct_comp_selfProductStructure C sX (φ₁ ≫ a) (φ₂ ≫ b)).symm (n + m)
      (chowExteriorProduct C hδ ((φ₁ ≫ a) ≫ sX) ((φ₂ ≫ b) ≫ sX) n m (x ⊗ₜ[ℤ] y)))
    (chowGroupCongr_heq _ _ _ _)
  refine eq_of_heq
    ((chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl rfl _ _ hE).trans
      (HEq.trans ?_
        (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl rfl _ _ HEq.rfl).symm))
  refine heq_of_eq (chowPushforwardOfIso_congr_apply _ _ _ _ _ ?_ _ _ _ _)
  apply pullback.hom_ext <;> simp [hΨ]

end Naturality

/-! ### The two bracketings of the product on a single scheme -/

section SelfIntersection

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
  {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (D : ℤ)
  (Dc : BivariantClass C G sW (selfProductStructure C sW) (pullback.diagonal sW)
    (diagonal_comp_selfProductStructure C sW) D)

/-- The self-intersection product, read on `W` through `W ×_W W ≅ W`, is the pushforward of the
reassociated product. -/
private theorem chowGroupCongr_selfIntersectionProduct (n m : ℤ) (x : chowGroup C sW n)
    (y : chowGroup C sW m) :
    chowGroupCongr C (Category.id_comp sW).symm (n + m - D)
      (selfIntersectionProduct C hδ G sW D Dc n m x y) =
      chowPushforwardOfIso C ((pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) ≫ sW) (𝟙 W ≫ sW)
        (pullback.fst (𝟙 W) (𝟙 W)) (by simp) (n + m - D)
        (intersectionProductReassoc C hδ G sW (𝟙 W) (𝟙 W) D Dc n m
          (chowGroupCongr C (Category.id_comp sW).symm n x)
          (chowGroupCongr C (Category.id_comp sW).symm m y)) :=
  eq_of_heq ((chowGroupCongr_heq _ _ _ _).trans (chowPushforwardOfIso_heq _ _ _
    (Category.assoc _ _ _) (Category.id_comp sW) rfl (chowGroupCongr_heq _ _ _ _)).symm)

/-- **The left-bracketed self-intersection product.** On a scheme `W` whose diagonal carries the
class `Dc`, `(x · y) · z` is the intersection product of Stacks 0FC0 over `X = W` of `x · y`,
read on `W ×_W W`, with `z`, carried to `W` along the projection `(W ×_W W) ×_W W ⟶ W`. -/
theorem selfIntersectionProduct_selfIntersectionProduct_left (n m l : ℤ) (x : chowGroup C sW n)
    (y : chowGroup C sW m) (z : chowGroup C sW l) :
    selfIntersectionProduct C hδ G sW D Dc (n + m - D) l
        (selfIntersectionProduct C hδ G sW D Dc n m x y) z =
      chowPushforwardOfIso C
        (pullback.fst (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) (𝟙 W) ≫
          ((pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) ≫ sW)) sW
        (pullback.fst (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) (𝟙 W) ≫ pullback.fst (𝟙 W) (𝟙 W))
        (by simp) (n + m - D + l - D)
        (intersectionProduct C hδ G sW (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) (𝟙 W) D Dc (n + m - D) l
          (intersectionProductReassoc C hδ G sW (𝟙 W) (𝟙 W) D Dc n m
              (chowGroupCongr C (Category.id_comp sW).symm n x)
              (chowGroupCongr C (Category.id_comp sW).symm m y) ⊗ₜ[ℤ]
            chowGroupCongr C (Category.id_comp sW).symm l z)) := by
  have h₁ := chowGroupCongr_selfIntersectionProduct C hδ G sW D Dc n m x y
  have h₂ : chowGroupCongr C (Category.id_comp sW).symm l z =
      chowPushforwardOfIso C (𝟙 W ≫ sW) (𝟙 W ≫ sW) (𝟙 W) (Category.id_comp _) l
        (chowGroupCongr C (Category.id_comp sW).symm l z) :=
    (chowPushforwardOfIso_id C _ l _).symm
  change chowPushforwardOfIso C (pullback.fst (𝟙 W) (𝟙 W) ≫ (𝟙 W ≫ sW)) sW
    (pullback.fst (𝟙 W) (𝟙 W)) (by simp) _
    (intersectionProduct C hδ G sW (𝟙 W) (𝟙 W) D Dc (n + m - D) l
      (chowGroupCongr C (Category.id_comp sW).symm (n + m - D)
          (selfIntersectionProduct C hδ G sW D Dc n m x y) ⊗ₜ[ℤ]
        chowGroupCongr C (Category.id_comp sW).symm l z)) = _
  rw [h₁]
  conv_lhs => rw [h₂]
  rw [intersectionProduct_chowPushforwardOfIso_tmul C hδ G sW (𝟙 W) (𝟙 W)
      (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) (𝟙 W) (pullback.fst (𝟙 W) (𝟙 W)) (𝟙 W) rfl
      (Category.id_comp _), chowPushforwardOfIso_comp_apply]
  exact chowPushforwardOfIso_congr_apply _ _ _ _ _ (by simp) _ _ _ _

/-- **The right-bracketed self-intersection product.** On a scheme `W` whose diagonal carries
the class `Dc`, `x · (y · z)` is the intersection product of Stacks 0FC0 over `X = W` of `x` with
`y · z`, read on `W ×_W W`, carried to `W` along the projection `W ×_W (W ×_W W) ⟶ W`. -/
theorem selfIntersectionProduct_selfIntersectionProduct_right (n m l : ℤ)
    (x : chowGroup C sW n) (y : chowGroup C sW m) (z : chowGroup C sW l) :
    selfIntersectionProduct C hδ G sW D Dc n (m + l - D) x
        (selfIntersectionProduct C hδ G sW D Dc m l y z) =
      chowPushforwardOfIso C
        (pullback.fst (𝟙 W) (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) ≫ (𝟙 W ≫ sW)) sW
        (pullback.fst (𝟙 W) (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W)) (by simp)
        (n + (m + l - D) - D)
        (intersectionProduct C hδ G sW (𝟙 W) (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) D Dc n (m + l - D)
          (chowGroupCongr C (Category.id_comp sW).symm n x ⊗ₜ[ℤ]
            intersectionProductReassoc C hδ G sW (𝟙 W) (𝟙 W) D Dc m l
              (chowGroupCongr C (Category.id_comp sW).symm m y)
              (chowGroupCongr C (Category.id_comp sW).symm l z))) := by
  have h₁ := chowGroupCongr_selfIntersectionProduct C hδ G sW D Dc m l y z
  have h₂ : chowGroupCongr C (Category.id_comp sW).symm n x =
      chowPushforwardOfIso C (𝟙 W ≫ sW) (𝟙 W ≫ sW) (𝟙 W) (Category.id_comp _) n
        (chowGroupCongr C (Category.id_comp sW).symm n x) :=
    (chowPushforwardOfIso_id C _ n _).symm
  change chowPushforwardOfIso C (pullback.fst (𝟙 W) (𝟙 W) ≫ (𝟙 W ≫ sW)) sW
    (pullback.fst (𝟙 W) (𝟙 W)) (by simp) _
    (intersectionProduct C hδ G sW (𝟙 W) (𝟙 W) D Dc n (m + l - D)
      (chowGroupCongr C (Category.id_comp sW).symm n x ⊗ₜ[ℤ]
        chowGroupCongr C (Category.id_comp sW).symm (m + l - D)
          (selfIntersectionProduct C hδ G sW D Dc m l y z))) = _
  rw [h₁]
  conv_lhs => rw [h₂]
  rw [intersectionProduct_chowPushforwardOfIso_tmul C hδ G sW (𝟙 W) (𝟙 W) (𝟙 W)
      (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) (𝟙 W) (pullback.fst (𝟙 W) (𝟙 W))
      (Category.id_comp _) rfl, chowPushforwardOfIso_comp_apply]
  exact chowPushforwardOfIso_congr_apply _ _ _ _ _ (by simp) _ _ _ _

/-- **Associativity of the self-intersection product from Stacks 0FC1.** If the intersection
product of Stacks 0FC0 formed with the class `Dc` of the diagonal of `W` is associative for
`Y = Z = W` over `X = W` (`Stacks.Chow.IsAssociativeIntersectionProduct`), then so is the
product `Stacks.Chow.selfIntersectionProduct` on `W`:

  `(x · y) · z = x · (y · z)`   in   `CH_{n+m+l-2D}(W)`. -/
theorem selfIntersectionProduct_assoc_of_isAssociativeIntersectionProduct (n m l : ℤ)
    (hpp : ProperPushforwardDescends C)
    (h : IsAssociativeIntersectionProduct C hδ G sW (𝟙 W) (𝟙 W) (𝟙 W) D Dc n m l hpp)
    (x : chowGroup C sW n) (y : chowGroup C sW m) (z : chowGroup C sW l) :
    chowGroupDegreeEquiv C sW (intersectionProductAssocDegree n m l D)
        (selfIntersectionProduct C hδ G sW D Dc (n + m - D) l
          (selfIntersectionProduct C hδ G sW D Dc n m x y) z) =
      selfIntersectionProduct C hδ G sW D Dc n (m + l - D) x
        (selfIntersectionProduct C hδ G sW D Dc m l y z) := by
  have key : ∀ Q : chowGroup C (pullback.fst (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) (𝟙 W) ≫
      ((pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) ≫ sW)) (n + m - D + l - D),
      chowGroupDegreeEquiv C sW (intersectionProductAssocDegree n m l D)
          (chowPushforwardOfIso C _ sW
            (pullback.fst (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) (𝟙 W) ≫ pullback.fst (𝟙 W) (𝟙 W))
            (by simp) _ Q) =
        chowPushforwardOfIso C
          (pullback.fst (𝟙 W) (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) ≫ (𝟙 W ≫ sW)) sW
          (pullback.fst (𝟙 W) (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W)) (by simp) _
          (chowGroupDegreeEquiv C _ (intersectionProductAssocDegree n m l D)
            (properChowPushforward C _ _ (tripleProductAssoc (𝟙 W) (𝟙 W) (𝟙 W)).hom
              (tripleProductAssoc_hom_comp_structureMorphism C sW _ _ _) _ (hpp _ _ _ _ _) Q)) := by
    intro Q
    refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans (HEq.symm ?_))
    exact chowPushforwardOfIso_heq_comp_of_comp_eq (tripleProductAssoc (𝟙 W) (𝟙 W) (𝟙 W)).hom
      (pullback.fst (𝟙 W) (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W))
      (pullback.fst (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W) (𝟙 W) ≫ pullback.fst (𝟙 W) (𝟙 W))
      (tripleProductAssoc_hom_fst _ _ _) (tripleProductAssoc_hom_comp_structureMorphism C sW _ _ _)
      _ rfl rfl (intersectionProductAssocDegree n m l D) Q _
      (chowGroupDegreeEquiv_heq _ _ _ _)
  rw [selfIntersectionProduct_selfIntersectionProduct_left,
    selfIntersectionProduct_selfIntersectionProduct_right, ← h]
  exact key _

end SelfIntersection

end Stacks.Chow

namespace Stacks.WeilCohomology

open Stacks.Chow

/-- **Associativity of the canonical intersection product** (Stacks 0FC1 with
`Y = Z = W = X`): on a scheme `W` smooth over `k` of constant dimension `N`, the
intersection products formed with the Gysin class of the diagonal satisfy
`(a · b) · c = a · (b · c)` in `CH_{n+m+l-2N}(W)`. This is
`Stacks.Chow.isAssociativeIntersectionProduct_canonical_of_relativeDimension` for
`a = b = g = 𝟙 W`, read on `W` through
`Stacks.Chow.selfIntersectionProduct_assoc_of_isAssociativeIntersectionProduct`. -/
theorem canonicalDiagonalClassFamily_intersectionAssoc (k : Type u) [Field k] :
    DiagonalClassFamily.IntersectionAssoc (canonicalDiagonalClassFamily k) := by
  intro W sW _ _ N hN n m l a b c
  exact selfIntersectionProduct_assoc_of_isAssociativeIntersectionProduct _ _ _ sW _ _ n m l _
    (isAssociativeIntersectionProduct_canonical_of_relativeDimension k sW hN (𝟙 W) (𝟙 W) (𝟙 W)
      n m l) a b c

end Stacks.WeilCohomology

end
