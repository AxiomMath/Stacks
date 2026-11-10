module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassBivariant
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClopenDecompositionCapGluing

/-!
# Chern classes of a finite locally free module of non-constant rank

In Situation 0EDT let `X/B` be good and let `ℰ` be a finite locally free `𝒪_X`-module whose rank
need not be constant. Stacks 0ES2 writes

`X = X_0 ⨿ X_1 ⨿ X_2 ⨿ …`,

`X_r ⊆ X` the open and closed subspace where `ℰ` has rank `r`
(`AlgebraicGeometry.Space.isClopenSubspaceDecomposition_rankSubspace`). A morphism `g : X' ⟶ X` of
good algebraic spaces over `B` pulls this back to the decomposition `X' = ∐_r X'_r`,
`X'_r = g^{-1}(X_r)` (`AlgebraicGeometry.Space.IsClopenSubspaceDecomposition.preimage`), and
`CH_*(X') = ∏_r CH_*(X'_r)` (`AlgebraicGeometry.Space.chowGroupCanonicalDecompositionEquiv`). The
Chern class `c_i(ℰ)` is then the bivariant class which preserves these product decompositions and
acts on the factor of `X'_r` by `c_i(ℰ|_{X_r}) ∩ -`, the Chern class of Stacks 0ERZ of the module
`ℰ|_{X_r}` of constant rank `r` (zero when `i > r`, following the convention of Stacks 0ERZ that
`c_i = 0` for `i` above the rank).

## Main definitions

* `AlgebraicGeometry.Space.rankPieceChernCap`: `c_i(ℰ|_{X_r}) ∩ -` on the test spaces of `X_r`.
* `AlgebraicGeometry.Space.chernCapOfFiniteLocallyFree`: `c_i(ℰ) ∩ -` on a good test space
  `X' ⟶ X`, glued from the `c_i(ℰ|_{X_r}) ∩ -` along `CH_*(X') = ∏_r CH_*(X'_r)`.
* `AlgebraicGeometry.Space.chernClassOfFiniteLocallyFree`: **Stacks 0ES2**, the bivariant class
  `c_i(ℰ) ∈ A^i(X)`.

## Main results

* `AlgebraicGeometry.Space.chowGroupCanonicalPieceRestrict_chernCapOfFiniteLocallyFree`: the
  operation `c_i(ℰ) ∩ -` acts by `c_i(ℰ|_{X_r}) ∩ -` on the factor of `X'_r`.
* `AlgebraicGeometry.Space.chernClassOfFiniteLocallyFree_cap`: the cap operation of the bivariant
  class `c_i(ℰ)` is `c_i(ℰ) ∩ -`, read on `X ×_X X' ≅ X'`.
* `AlgebraicGeometry.Space.rankDecomposition_chowGroup_chernClassOfFiniteLocallyFree`:
  **Stacks 0ES2**, the whole remark: the rank decomposition of `X`, its pullback to every good
  `X' ⟶ X`, the product decomposition of the Chow groups of `X'`, and `c_i(ℰ)` as the unique
  bivariant class preserving these decompositions and acting by `c_i(ℰ|_{X_r}) ∩ -` on the
  factors.

## Implementation notes

The Chow groups are those of Stacks 0EQ6 at the canonical embeddings
(`AlgebraicGeometry.Space.chowGroupCanonical`) and the bivariant classes those of Stacks 0ERJ over
them, as for the Chern classes of constant rank (`AlgebraicGeometry.Space.chernClass`). The rank
decomposition is indexed by `ULift ℕ`, as in
`AlgebraicGeometry.Space.isClopenSubspaceDecomposition_rankSubspace`. The restriction `ℰ|_{X_r}`
is the inverse image along the inclusion of `X_r`
(`AlgebraicGeometry.Space.pullbackSheaf`), which is finite locally free of rank `r`
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_modulePullback_rankSubspace`).

## References

* [Stacks Project, Tag 0ES2](https://stacks.math.columbia.edu/tag/0ES2)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The two degree identifications `CH_a(Y) = CH_b(Y)` along `a = b`, of the projective bundle
relation and of the Chow cohomology algebra, agree. -/
theorem degreeCast_eq_chowGroupCanonicalDegreeCongr {D : BaseSpaceDimensionSituation.{u}}
    {Y : D.Ambient} (sY : Y ⟶ D.space) (hY : D.IsGood sY) {a b : ℤ} (h : a = b)
    (x : chowGroupCanonical.{u + 1} D sY hY a) :
    ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D sY hY m) h x =
      chowGroupCanonicalDegreeCongr D sY hY h x := by
  subst h
  rfl

section NonConstantRank

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- **`c_i(ℰ|_{X_r}) ∩ -` on the test spaces of `X_r`**: for `i ≤ r` the cap operation of the
`i`-th Chern class (Stacks 0ERY, 0ERZ) of the restriction `ℰ|_{X_r}`, which is finite locally
free of rank `r`; for `i > r` the zero map, Stacks setting `c_i(ℰ|_{X_r}) = 0` above the rank. -/
def rankPieceChernCap (i : ℕ) (r : ULift.{u} ℕ) {Y : D.Ambient}
    (g : Y ⟶ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).toFunctor)
    (hY : D.IsGood (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX)) (k : ℤ) :
    chowGroupCanonical.{u + 1} D (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX) hY k →+
      chowGroupCanonical.{u + 1} D (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX) hY
        (k - (i : ℤ)) :=
  if hi : i ≤ r.down then
    chernCap D ((rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX)
      (isGood_rankSubspace D sX hX E r.down)
      (pullbackSheaf D sX hX ((rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX)
        (isGood_rankSubspace D sX hX E r.down)
        (ObjectProperty.homMk (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι) E) r.down
      (isFiniteLocallyFreeOfRank_modulePullback_rankSubspace (Y := ⟨X, hX.1⟩) E hE r.down
        (isGood_rankSubspace D sX hX E r.down).1) g hY ⟨i, Nat.lt_succ_of_le hi⟩ k
  else 0

/-- For `i ≤ r`, `c_i(ℰ|_{X_r}) ∩ -` is the cap operation of the `i`-th Chern class of
`ℰ|_{X_r}`. -/
theorem rankPieceChernCap_of_le (i : ℕ) (r : ULift.{u} ℕ) (hi : i ≤ r.down) {Y : D.Ambient}
    (g : Y ⟶ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).toFunctor)
    (hY : D.IsGood (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX)) (k : ℤ) :
    rankPieceChernCap D sX hX E hE i r g hY k =
      chernCap D ((rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX)
        (isGood_rankSubspace D sX hX E r.down)
        (pullbackSheaf D sX hX ((rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX)
          (isGood_rankSubspace D sX hX E r.down)
          (ObjectProperty.homMk (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι) E) r.down
        (isFiniteLocallyFreeOfRank_modulePullback_rankSubspace (Y := ⟨X, hX.1⟩) E hE r.down
          (isGood_rankSubspace D sX hX E r.down).1) g hY ⟨i, Nat.lt_succ_of_le hi⟩ k :=
  dite_eq_left hi

/-- For `i > r`, `c_i(ℰ|_{X_r}) ∩ -` is zero. -/
theorem rankPieceChernCap_of_lt (i : ℕ) (r : ULift.{u} ℕ) (hi : r.down < i) {Y : D.Ambient}
    (g : Y ⟶ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).toFunctor)
    (hY : D.IsGood (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX)) (k : ℤ) :
    rankPieceChernCap D sX hX E hE i r g hY k = 0 :=
  dite_eq_right (Nat.not_le.2 hi)

/-- `c_i(ℰ|_{X_r}) ∩ -` commutes with proper pushforward. -/
theorem rankPieceChernCap_properPushforward (i : ℕ) (r : ULift.{u} ℕ) {Y₁ Y₂ : D.Ambient}
    (g : Y₁ ⟶ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).toFunctor)
    (hY₁ : D.IsGood (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX)) (h : Y₂ ⟶ Y₁)
    (hY₂ : D.IsGood ((h ≫ g) ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX))
    (hh : IsProper D.site D.base D.base_mem h) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D
      ((h ≫ g) ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX) hY₂ k) :
    rankPieceChernCap D sX hX E hE i r g hY₁ k
        (chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁
          (Category.assoc h g _).symm hh k α) =
      chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g _).symm hh
        _ (rankPieceChernCap D sX hX E hE i r (h ≫ g) hY₂ k α) := by
  rcases le_or_gt i r.down with hi | hi
  · simp only [rankPieceChernCap_of_le D sX hX E hE i r hi]
    exact chernCap_properPushforward D _ _ _ r.down _ ⟨i, Nat.lt_succ_of_le hi⟩ g hY₁ h hY₂ hh k α
  · simp only [rankPieceChernCap_of_lt D sX hX E hE i r hi, AddMonoidHom.zero_apply, map_zero]

/-- `c_i(ℰ|_{X_r}) ∩ -` commutes with flat pullback. -/
theorem rankPieceChernCap_flatPullback (i : ℕ) (r : ULift.{u} ℕ) {Y₁ Y₂ : D.Ambient}
    (g : Y₁ ⟶ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).toFunctor)
    (hY₁ : D.IsGood (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX)) (h : Y₂ ⟶ Y₁)
    (hY₂ : D.IsGood ((h ≫ g) ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX)) (m : ℕ)
    (hhf : IsFlat D.site D.base D.base_mem h)
    (hhr : HasRelativeDimension m D.site D.base D.base_mem h) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D
      (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX) hY₁ k) :
    rankPieceChernCap D sX hX E hE i r (h ≫ g) hY₂ (k + m)
        (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h
          (Category.assoc h g _).symm m hhf hhr k (k + m) rfl α) =
      flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g _).symm m hhf
        hhr (k - (i : ℤ)) (k + m - (i : ℤ)) (by ring)
        (rankPieceChernCap D sX hX E hE i r g hY₁ k α) := by
  rcases le_or_gt i r.down with hi | hi
  · simp only [rankPieceChernCap_of_le D sX hX E hE i r hi]
    exact chernCap_flatPullback D _ _ _ r.down _ ⟨i, Nat.lt_succ_of_le hi⟩ g hY₁ h hY₂ m hhf hhr
      k α
  · simp only [rankPieceChernCap_of_lt D sX hX E hE i r hi, AddMonoidHom.zero_apply, map_zero]

/-- `c_i(ℰ|_{X_r}) ∩ -` commutes with the Gysin maps of sections of invertible modules. -/
theorem rankPieceChernCap_sectionGysinChowGroupMap (i : ℕ) (r : ULift.{u} ℕ) {Y : D.Ambient}
    (g : Y ⟶ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).toFunctor)
    (hY : D.IsGood (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX))
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (t : M.sections)
    (hM : IsInvertibleSheaf D (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX) hY M)
    (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D
      (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX) hY (k + 1)) :
    rankPieceChernCap D sX hX E hE i r
        ((vanishingLocus D (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX) hY M t).1.ι ≫ g)
        (isGood_vanishingLocus_comp D ((rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX) g hY
          M t) k
        (sectionGysinChowGroupMap D (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX) hY M t
          hM k α) =
      sectionGysinChowGroupMap D (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX) hY M t hM
        (k - (i : ℤ))
        (chowGroupCanonicalDegreeCongr D (g ≫ (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι ≫ sX)
          hY (by ring) (rankPieceChernCap D sX hX E hE i r g hY (k + 1) α)) := by
  rcases le_or_gt i r.down with hi | hi
  · simp only [rankPieceChernCap_of_le D sX hX E hE i r hi,
      ← degreeCast_eq_chowGroupCanonicalDegreeCongr]
    exact chernCap_gysin D _ _ _ r.down _ ⟨i, Nat.lt_succ_of_le hi⟩ g hY M t hM k α
  · simp only [rankPieceChernCap_of_lt D sX hX E hE i r hi, AddMonoidHom.zero_apply, map_zero]

/-- **`c_i(ℰ) ∩ - : CH_k(X') ⟶ CH_{k-i}(X')`** on a good test space `g : X' ⟶ X`, for `ℰ` finite
locally free of possibly non-constant rank: the map which preserves the product decomposition
`CH_*(X') = ∏_r CH_*(X'_r)`, `X'_r = g^{-1}(X_r)`, and acts by `c_i(ℰ|_{X_r}) ∩ -` on the factor
of `X'_r` (`AlgebraicGeometry.Space.clopenGluedCap`). -/
def chernCapOfFiniteLocallyFree (i : ℕ) {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (k : ℤ) :
    chowGroupCanonical.{u + 1} D (g ≫ sX) hY k →+
      chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - (i : ℤ)) :=
  clopenGluedCap (isClopenSubspaceDecomposition_rankSubspace D sX hX E hE) (i : ℤ)
    (rankPieceChernCap D sX hX E hE i) g hY k

/-- **`c_i(ℰ) ∩ -` acts by `c_i(ℰ|_{X_r}) ∩ -` on the factor of `X'_r`.** -/
theorem chowGroupCanonicalPieceRestrict_chernCapOfFiniteLocallyFree (i : ℕ) {Y : D.Ambient}
    (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) (r : ULift.{u} ℕ) :
    chowGroupCanonicalPieceRestrict
        ((isClopenSubspaceDecomposition_rankSubspace D sX hX E hE).preimage g hY) r (k - (i : ℤ))
        (chernCapOfFiniteLocallyFree D sX hX E hE i g hY k α) =
      rankPieceChernCap D sX hX E hE i r
        ((rankSubspace (Y := ⟨X, hX.1⟩) E r.down).fromPreimage g)
        (((isClopenSubspaceDecomposition_rankSubspace D sX hX E hE).preimage g hY).isGoodPiece r)
        k (chowGroupCanonicalPieceRestrict
          ((isClopenSubspaceDecomposition_rankSubspace D sX hX E hE).preimage g hY) r k α) :=
  chowGroupCanonicalPieceRestrict_clopenGluedCap _ _ _ g hY k α r

/-- `c_i(ℰ) ∩ -` commutes with proper pushforward. -/
theorem chernCapOfFiniteLocallyFree_properPushforward (i : ℕ) {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X)
    (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁) (hY₂ : D.IsGood ((h ≫ g) ≫ sX))
    (hh : IsProper D.site D.base D.base_mem h) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY₂ k) :
    chernCapOfFiniteLocallyFree D sX hX E hE i g hY₁ k
        (chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g sX).symm hh
          k α) =
      chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g sX).symm hh _
        (chernCapOfFiniteLocallyFree D sX hX E hE i (h ≫ g) hY₂ k α) :=
  clopenGluedCap_properPushforward _ _ _
    (fun r _ _ g hY₁ h hY₂ hh k α =>
      rankPieceChernCap_properPushforward D sX hX E hE i r g hY₁ h hY₂ hh k α)
    g hY₁ h hY₂ hh k α

/-- `c_i(ℰ) ∩ -` commutes with flat pullback. -/
theorem chernCapOfFiniteLocallyFree_flatPullback (i : ℕ) {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X)
    (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁) (hY₂ : D.IsGood ((h ≫ g) ≫ sX)) (m : ℕ)
    (hhf : IsFlat D.site D.base D.base_mem h)
    (hhr : HasRelativeDimension m D.site D.base D.base_mem h) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY₁ k) :
    chernCapOfFiniteLocallyFree D sX hX E hE i (h ≫ g) hY₂ (k + m)
        (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g sX).symm m hhf
          hhr k (k + m) rfl α) =
      flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g sX).symm m hhf hhr
        (k - (i : ℤ)) (k + m - (i : ℤ)) (chernDegree_sub_add k m _)
        (chernCapOfFiniteLocallyFree D sX hX E hE i g hY₁ k α) :=
  clopenGluedCap_flatPullback _ _ _
    (fun r _ _ g hY₁ h hY₂ m hhf hhr k α =>
      rankPieceChernCap_flatPullback D sX hX E hE i r g hY₁ h hY₂ m hhf hhr k α)
    g hY₁ h hY₂ m hhf hhr k α

/-- `c_i(ℰ) ∩ -` commutes with the Gysin maps of sections of invertible modules. -/
theorem chernCapOfFiniteLocallyFree_sectionGysinChowGroupMap (i : ℕ) {Y : D.Ambient}
    (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (t : M.sections) (hM : IsInvertibleSheaf D (g ≫ sX) hY M) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k + 1)) :
    chernCapOfFiniteLocallyFree D sX hX E hE i ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g)
        (isGood_vanishingLocus D (g ≫ sX) hY M t) k
        (sectionGysinChowGroupMap D (g ≫ sX) hY M t hM k α) =
      sectionGysinChowGroupMap D (g ≫ sX) hY M t hM (k - (i : ℤ))
        (ProjectiveBundleRelation.degreeCast
          (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (chernDegree_add_one_sub k _)
          (chernCapOfFiniteLocallyFree D sX hX E hE i g hY (k + 1) α)) := by
  rw [degreeCast_eq_chowGroupCanonicalDegreeCongr]
  exact clopenGluedCap_sectionGysinChowGroupMap _ _ _
    (fun r _ _ g hY₁ h hY₂ m hhf hhr k α =>
      rankPieceChernCap_flatPullback D sX hX E hE i r g hY₁ h hY₂ m hhf hhr k α)
    (fun r _ g hY M t hM k α =>
      rankPieceChernCap_sectionGysinChowGroupMap D sX hX E hE i r g hY M t hM k α)
    g hY M t hM k α

/-- **Stacks 0ES2: the `i`-th Chern class `c_i(ℰ) ∈ A^i(X)` of a finite locally free module `ℰ`
of possibly non-constant rank** on a good algebraic space `X/B`: the bivariant class of degree `i`
whose cap operation on a good test space `g : X' ⟶ X` preserves the product decomposition
`CH_*(X') = ∏_r CH_*(X'_r)` along the pullback `X'_r = g^{-1}(X_r)` of the rank decomposition
`X = ∐_r X_r` of `ℰ` and acts on the factor of `X'_r` by `c_i(ℰ|_{X_r}) ∩ -`, the Chern class of
Stacks 0ERZ of the module `ℰ|_{X_r}` of constant rank `r` (zero for `i > r`)
(`AlgebraicGeometry.Space.chernCapOfFiniteLocallyFree`); the cap operation is read on
`X ×_X X' ≅ X'` (`AlgebraicGeometry.Space.chernClassOfFiniteLocallyFree_cap`). -/
@[stacks 0ES2 "the definition: c_i(E) ∈ A^i(X) for E finite locally free of non-constant rank, \
the bivariant class preserving CH_*(X') = ∏_r CH_*(X'_r) and acting by c_i(E|_{X_r}) ∩ - on the \
factors"]
def chernClassOfFiniteLocallyFree (i : ℕ) :
    chowCohomologyComponentCanonical.{u + 1} D sX hX (i : ℤ) :=
  bivariantClassOfTestCaps D sX hX (i : ℤ)
    (fun g hY k => chernCapOfFiniteLocallyFree D sX hX E hE i g hY k)
    (fun g hY₁ h hY₂ hh k α =>
      chernCapOfFiniteLocallyFree_properPushforward D sX hX E hE i g hY₁ h hY₂ hh k α)
    (fun g hY₁ h hY₂ m hhf hhr k α =>
      chernCapOfFiniteLocallyFree_flatPullback D sX hX E hE i g hY₁ h hY₂ m hhf hhr k α)
    (fun g hY M t hM k α =>
      chernCapOfFiniteLocallyFree_sectionGysinChowGroupMap D sX hX E hE i g hY M t hM k α)

/-- The cap operation of `c_i(ℰ)` on a test space `g : X' ⟶ X` is `c_i(ℰ) ∩ -` on `X'`, read on
`X ×_X X' ≅ X'`. -/
theorem chernClassOfFiniteLocallyFree_cap (i : ℕ) {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (hXg : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    (chernClassOfFiniteLocallyFree D sX hX E hE i).cap g hY hXg k α =
      testSpacePullbackChowMap D sX hX g hY hXg _
        (chernCapOfFiniteLocallyFree D sX hX E hE i g hY k α) :=
  rfl

/-- **Stacks 0ES2.** In Situation 0EDT let `X/B` be good and let `ℰ` be a finite locally free
`𝒪_X`-module, of possibly non-constant rank.

1. `X = X_0 ⨿ X_1 ⨿ X_2 ⨿ …`, where `X_r ⊆ X` is the open and closed subspace where `ℰ` has
   rank `r`.
2. For every morphism `g : X' ⟶ X` of good algebraic spaces over `B`, the inverse images
   `X'_r = g^{-1}(X_r)` form the corresponding decomposition of `X'`, and
3. the restrictions to the pieces identify `CH_k(X')` with `∏_r CH_k(X'_r)` for every `k`.
4. For every `i`, `c_i(ℰ) ∈ A^i(X)` (`AlgebraicGeometry.Space.chernClassOfFiniteLocallyFree`)
   is a bivariant class which preserves these direct product decompositions and acts by
   `c_i(ℰ|_{X_r}) ∩ -` on the factors (`AlgebraicGeometry.Space.rankPieceChernCap`: the Chern class
   of Stacks 0ERZ of `ℰ|_{X_r}`, of constant rank `r`, and `0` for `i > r`), and it is the only
   bivariant class of degree `i` with this property.

The cap operation of a class `C ∈ A^i(X)` on `X'` lands in `CH_{k-i}(X ×_X X')`, which is read on
`X'` along the flat pullback by the isomorphism `X ×_X X' ≅ X'`
(`AlgebraicGeometry.Space.testSpacePullbackChowMap`). -/
@[stacks 0ES2 "the whole remark: X = ∐_r X_r by the rank of E (open and closed), its pullback to \
every morphism X' → X of good spaces over B, CH_k(X') = ∏_r CH_k(X'_r) on Chow groups, and c_i(E) \
∈ A^i(X) as the unique bivariant class preserving these decompositions and acting by \
c_i(E|_{X_r}) ∩ - on the factors"]
theorem rankDecomposition_chowGroup_chernClassOfFiniteLocallyFree :
    IsClopenSubspaceDecomposition D sX
        (fun r : ULift.{u} ℕ => (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι) ∧
      (∀ {Y : D.Ambient} (g : Y ⟶ X), D.IsGood (g ≫ sX) →
        ∃ hdec : IsClopenSubspaceDecomposition D (g ≫ sX)
            (fun r : ULift.{u} ℕ => ((rankSubspace (Y := ⟨X, hX.1⟩) E r.down).preimage g).ι),
          ∀ k : ℤ, Function.Bijective (chowGroupCanonicalDecompositionRestrict hdec k)) ∧
      ∀ i : ℕ,
        let P : chowCohomologyComponentCanonical.{u + 1} D sX hX (i : ℤ) → Prop := fun C =>
          ∀ {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
            (hXg : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) (k : ℤ)
            (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k),
            ∃ β : chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - (i : ℤ)),
              C.cap g hY hXg k α = testSpacePullbackChowMap D sX hX g hY hXg _ β ∧
                ∀ r : ULift.{u} ℕ,
                  chowGroupCanonicalPieceRestrict
                      ((isClopenSubspaceDecomposition_rankSubspace D sX hX E hE).preimage g hY) r
                      (k - (i : ℤ)) β =
                    rankPieceChernCap D sX hX E hE i r
                      ((rankSubspace (Y := ⟨X, hX.1⟩) E r.down).fromPreimage g)
                      (((isClopenSubspaceDecomposition_rankSubspace D sX hX E hE).preimage g
                        hY).isGoodPiece r) k
                      (chowGroupCanonicalPieceRestrict
                        ((isClopenSubspaceDecomposition_rankSubspace D sX hX E hE).preimage g hY)
                        r k α)
        P (chernClassOfFiniteLocallyFree D sX hX E hE i) ∧
          ∀ C, P C → C = chernClassOfFiniteLocallyFree D sX hX E hE i := by
  refine ⟨isClopenSubspaceDecomposition_rankSubspace D sX hX E hE, fun g hY =>
    ⟨(isClopenSubspaceDecomposition_rankSubspace D sX hX E hE).preimage g hY, fun k =>
      bijective_chowGroupCanonicalDecompositionRestrict _ k⟩, fun i => ?_⟩
  refine ⟨fun g hY hXg k α => ⟨chernCapOfFiniteLocallyFree D sX hX E hE i g hY k α, rfl,
    chowGroupCanonicalPieceRestrict_chernCapOfFiniteLocallyFree D sX hX E hE i g hY k α⟩,
    fun C hC => ?_⟩
  apply BivariantClassCanonical.ext
  intro Y g hY hXg k α
  obtain ⟨β, hβ, hβr⟩ := hC g hY hXg k α
  rw [hβ, chernClassOfFiniteLocallyFree_cap]
  congr 1
  exact chowGroupCanonical_ext_of_decomposition
    ((isClopenSubspaceDecomposition_rankSubspace D sX hX E hE).preimage g hY) fun r => by
      rw [hβr, chowGroupCanonicalPieceRestrict_chernCapOfFiniteLocallyFree]

end NonConstantRank

end AlgebraicGeometry.Space
