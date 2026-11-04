module

public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorCounitDevissage

/-!
# Inverse systems of triangulated functors and vanishing of derived limits

Let `C` and `D` be pre-triangulated categories, `D` with countable products, and let
`⋯ ⟶ F₂ ⟶ F₁ ⟶ F₀` be an inverse system of triangulated functors `Fₙ : C ⥤ D` whose transition
maps `τₙ : Fₙ₊₁ ⟶ Fₙ` commute with the shift. Every object `X` of `C` then gives an inverse system
`n ↦ Fₙ(X)` of `D`. This file shows that **the objects `X` for which this inverse system has
derived limit `0` form a triangulated subcategory of `C`**.

The derived limit `R lim Fₙ(X)` vanishes exactly when the difference map
`1 - shift : ∏ Fₙ(X) ⟶ ∏ Fₙ(X)` is invertible (it is the second map of the defining triangle of
Tag 08TC). A distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` of `C` is carried by each `Fₙ` to a
distinguished triangle of `D`, the transitions `τₙ` assemble these into an inverse system of
distinguished triangles, and the product of that system is again a distinguished triangle. The
three difference maps are the components of an endomorphism of that product triangle, so if two
of them are invertible so is the third.

## Main definitions

* `CategoryTheory.Pretriangulated.familyDifference`: the difference map `1 - shift` of a family of
  objects with transition maps.
* `CategoryTheory.Pretriangulated.productTriangleDifference`: the endomorphism of the product of
  an inverse system of triangles whose components are the three difference maps.
* `CategoryTheory.Pretriangulated.TriangulatedTower.tower`: the inverse system `n ↦ Fₙ(X)`.
* `CategoryTheory.Pretriangulated.TriangulatedTower.rlimZero`: the objects `X` for which the
  difference map of `n ↦ Fₙ(X)` is invertible.

## Main results

* `CategoryTheory.Pretriangulated.IsDerivedLimit.isZero_iff_isIso_difference`: a derived limit
  vanishes exactly when the difference map is invertible.
* `CategoryTheory.Pretriangulated.TriangulatedTower.rlimZero_isTriangulated`: the objects
  `X` for which `R lim Fₙ(X) = 0` form a triangulated subcategory.
* `CategoryTheory.Pretriangulated.TriangulatedTower.isZero_of_isDerivedLimit`: for such an `X`,
  every derived limit of `n ↦ Fₙ(X)` is zero.

## References

* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC) is the derived limit.
* [Stacks Project, Tag 0GZK](https://stacks.math.columbia.edu/tag/0GZK), whose proof uses that
  `R lim (M_n ⊗^𝐋_R K_t) = 0` when `R lim M_n = 0`, the Koszul complex `K_t` being built out of
  `R` by finitely many triangles.
-/

@[expose] public noncomputable section

open CategoryTheory Limits ZeroObject

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Pretriangulated

section Difference

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- The difference map `(yₙ) ↦ (yₙ - tₙ(yₙ₊₁))` of a family of objects `Yₙ` with maps
`tₙ : Yₙ₊₁ ⟶ Yₙ`. -/
def familyDifference (Y : ℕ → D) [HasProduct Y] (t : ∀ n : ℕ, Y (n + 1) ⟶ Y n) :
    ∏ᶜ Y ⟶ ∏ᶜ Y :=
  Pi.lift fun n => Pi.π Y n - Pi.π Y (n + 1) ≫ t n

/-- The `n`-th component of the difference map is `yₙ - tₙ(yₙ₊₁)`. -/
@[reassoc (attr := simp)]
theorem familyDifference_π (Y : ℕ → D) [HasProduct Y] (t : ∀ n : ℕ, Y (n + 1) ⟶ Y n)
    (n : ℕ) : familyDifference Y t ≫ Pi.π Y n = Pi.π Y n - Pi.π Y (n + 1) ≫ t n :=
  Pi.lift_π _ _

/-- The difference maps commute with a map of families compatible with the transition maps. -/
@[reassoc]
theorem piMap_familyDifference {Y Y' : ℕ → D} [HasProduct Y] [HasProduct Y']
    {t : ∀ n : ℕ, Y (n + 1) ⟶ Y n} {t' : ∀ n : ℕ, Y' (n + 1) ⟶ Y' n} (f : ∀ n, Y n ⟶ Y' n)
    (hf : ∀ n, f (n + 1) ≫ t' n = t n ≫ f n) :
    Limits.Pi.map f ≫ familyDifference Y' t' = familyDifference Y t ≫ Limits.Pi.map f := by
  refine Pi.hom_ext _ _ fun n => ?_
  simp only [Category.assoc, familyDifference_π, Preadditive.comp_sub, Pi.map_π,
    familyDifference_π_assoc, Preadditive.sub_comp, Pi.map_π_assoc, hf]

/-- The difference map commutes with a functor preserving the product, read through the
comparison map of the product. -/
@[reassoc]
theorem map_familyDifference_piComparison {E : Type*} [Category E] [Preadditive E]
    (G : D ⥤ E) [G.Additive] (Y : ℕ → D) [HasProduct Y] [HasProduct fun n => G.obj (Y n)]
    (t : ∀ n : ℕ, Y (n + 1) ⟶ Y n) :
    G.map (familyDifference Y t) ≫ piComparison G Y =
      piComparison G Y ≫ familyDifference (fun n => G.obj (Y n)) fun n => G.map (t n) := by
  refine Pi.hom_ext _ _ fun n => ?_
  simp only [Category.assoc, piComparison_comp_π, familyDifference_π, Preadditive.comp_sub,
    piComparison_comp_π_assoc, ← G.map_comp, G.map_sub]

/-- A family of isomorphisms induces an isomorphism of products. -/
private def piMapIso {Y Y' : ℕ → D} [HasProduct Y] [HasProduct Y'] (e : ∀ n, Y n ≅ Y' n) :
    ∏ᶜ Y ≅ ∏ᶜ Y' where
  hom := Limits.Pi.map fun n => (e n).hom
  inv := Limits.Pi.map fun n => (e n).inv
  hom_inv_id := Pi.hom_ext _ _ fun n => by simp
  inv_hom_id := Pi.hom_ext _ _ fun n => by simp

/-- **An isomorphism of families compatible with the transition maps carries an invertible
difference map to an invertible difference map.** -/
theorem isIso_familyDifference_of_iso {Y Y' : ℕ → D} [HasProduct Y] [HasProduct Y']
    {t : ∀ n : ℕ, Y (n + 1) ⟶ Y n} {t' : ∀ n : ℕ, Y' (n + 1) ⟶ Y' n} (e : ∀ n, Y n ≅ Y' n)
    (he : ∀ n, (e (n + 1)).hom ≫ t' n = t n ≫ (e n).hom)
    (h : IsIso (familyDifference Y' t')) : IsIso (familyDifference Y t) := by
  have : IsIso (Limits.Pi.map fun n => (e n).hom) :=
    inferInstanceAs (IsIso (piMapIso e).hom)
  have : IsIso (familyDifference Y t ≫ Limits.Pi.map fun n => (e n).hom) := by
    rw [← piMap_familyDifference (fun n => (e n).hom) he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (Limits.Pi.map fun n => (e n).hom)

end Difference

section ProductTriangle

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]

variable (T : ℕ → Triangle D) (φ : ∀ n : ℕ, T (n + 1) ⟶ T n)
  [HasProduct fun n => (T n).obj₁] [HasProduct fun n => (T n).obj₂]
  [HasProduct fun n => (T n).obj₃] [HasProduct fun n => ((T n).obj₁)⟦(1 : ℤ)⟧]

/-- **The difference endomorphism of the product of an inverse system of triangles.** Its three
components are the difference maps of the three inverse systems of vertices. -/
def productTriangleDifference : productTriangle T ⟶ productTriangle T where
  hom₁ := familyDifference (fun n => (T n).obj₁) fun n => (φ n).hom₁
  hom₂ := familyDifference (fun n => (T n).obj₂) fun n => (φ n).hom₂
  hom₃ := familyDifference (fun n => (T n).obj₃) fun n => (φ n).hom₃
  comm₁ := piMap_familyDifference (fun n => (T n).mor₁) fun n => (φ n).comm₁
  comm₂ := piMap_familyDifference (fun n => (T n).mor₂) fun n => (φ n).comm₂
  comm₃ := by
    have h := map_familyDifference_piComparison (shiftFunctor D (1 : ℤ))
      (fun n => (T n).obj₁) fun n => (φ n).hom₁
    have h' : inv (piComparison (shiftFunctor D (1 : ℤ)) fun n => (T n).obj₁) ≫
        (shiftFunctor D (1 : ℤ)).map
          (familyDifference (fun n => (T n).obj₁) fun n => (φ n).hom₁) =
        familyDifference (fun n => ((T n).obj₁)⟦(1 : ℤ)⟧)
            (fun n => ((φ n).hom₁)⟦(1 : ℤ)⟧') ≫
          inv (piComparison (shiftFunctor D (1 : ℤ)) fun n => (T n).obj₁) := by
      rw [IsIso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    simp only [productTriangle, Triangle.mk_mor₃, Category.assoc]
    rw [h', piMap_familyDifference_assoc (fun n => (T n).mor₃) fun n => (φ n).comm₃]

end ProductTriangle

variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A derived limit vanishes exactly when the difference map is invertible.** The difference map
is the second map of the defining triangle of Tag 08TC. -/
theorem IsDerivedLimit.isZero_iff_isIso_difference {F : ℕᵒᵖ ⥤ D}
    [HasProduct fun n : ℕ => F.obj ⟨n⟩] {K : D} (hK : IsDerivedLimit F K) :
    IsZero K ↔ IsIso (familyDifference (fun n : ℕ => F.obj ⟨n⟩)
      fun n => F.map (homOfLE (Nat.le_succ n)).op) := by
  obtain ⟨p, δ, hT⟩ := hK
  exact Triangle.isZero₁_iff_isIso₂ _ hT

/-- An inverse system whose difference map is invertible has every derived limit zero. -/
theorem IsDerivedLimit.isZero_of_isIso_difference {F : ℕᵒᵖ ⥤ D}
    [HasProduct fun n : ℕ => F.obj ⟨n⟩] {K : D} (hK : IsDerivedLimit F K)
    (h : IsIso (familyDifference (fun n : ℕ => F.obj ⟨n⟩)
      fun n => F.map (homOfLE (Nat.le_succ n)).op)) : IsZero K :=
  hK.isZero_iff_isIso_difference.2 h

/-- An inverse system with a zero derived limit has invertible difference map. -/
theorem IsDerivedLimit.isIso_difference_of_isZero {F : ℕᵒᵖ ⥤ D}
    [HasProduct fun n : ℕ => F.obj ⟨n⟩] {K : D} (hK : IsDerivedLimit F K) (h : IsZero K) :
    IsIso (familyDifference (fun n : ℕ => F.obj ⟨n⟩)
      fun n => F.map (homOfLE (Nat.le_succ n)).op) :=
  hK.isZero_iff_isIso_difference.1 h

/-- **Being a derived limit is invariant under isomorphism of inverse systems.** -/
theorem IsDerivedLimit.of_iso {F G : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    [HasProduct fun n : ℕ => G.obj ⟨n⟩] (c : F ≅ G) {K : D} (hK : IsDerivedLimit F K) :
    IsDerivedLimit G K := by
  obtain ⟨p, δ, hT⟩ := hK
  let e := piMapIso fun n : ℕ => c.app ⟨n⟩
  have he : e.hom ≫ familyDifference (fun n : ℕ => G.obj ⟨n⟩)
      (fun n => G.map (homOfLE (Nat.le_succ n)).op) = familyDifference (fun n : ℕ => F.obj ⟨n⟩)
      (fun n => F.map (homOfLE (Nat.le_succ n)).op) ≫ e.hom :=
    piMap_familyDifference (fun n => c.hom.app ⟨n⟩) fun n => (c.hom.naturality _).symm
  refine ⟨p ≫ e.hom, e.inv ≫ δ, isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _)
    e.symm e.symm ?_ ?_ ?_)⟩
  · show (p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ p
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · show familyDifference _ _ ≫ e.inv = e.inv ≫ familyDifference _ _
    rw [Iso.comp_inv_eq, Category.assoc, ← he, Iso.inv_hom_id_assoc]
  · show (e.inv ≫ δ) ≫ (𝟙 K)⟦(1 : ℤ)⟧' = e.inv ≫ δ
    rw [Functor.map_id, Category.comp_id]

namespace TriangulatedTower

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasProductsOfShape ℕ D]
  (F : ℕ → C ⥤ D) [∀ n, (F n).CommShift ℤ] [∀ n, (F n).IsTriangulated]
  (τ : ∀ n : ℕ, F (n + 1) ⟶ F n) [∀ n, NatTrans.CommShift (τ n) ℤ]

/-- The inverse system `n ↦ Fₙ(X)` of `D`, with transition maps `τₙ` at `X`. -/
def tower (X : C) : ℕᵒᵖ ⥤ D :=
  Functor.ofOpSequence (X := fun n => (F n).obj X) fun n => (τ n).app X

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasProductsOfShape ℕ D]
  [∀ n, (F n).CommShift ℤ] [∀ n, (F n).IsTriangulated] [∀ n, NatTrans.CommShift (τ n) ℤ] in
/-- The `n`-th object of the inverse system `n ↦ Fₙ(X)` is `Fₙ(X)`. -/
@[simp] theorem tower_obj (X : C) (n : ℕ) : (tower F τ X).obj ⟨n⟩ = (F n).obj X := rfl

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasProductsOfShape ℕ D]
  [∀ n, (F n).CommShift ℤ] [∀ n, (F n).IsTriangulated] [∀ n, NatTrans.CommShift (τ n) ℤ] in
/-- The one-step transition maps of `n ↦ Fₙ(X)` are the components of the `τₙ` at `X`. -/
@[simp] theorem tower_map_succ (X : C) (n : ℕ) :
    (tower F τ X).map (homOfLE (Nat.le_succ n)).op = (τ n).app X :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [∀ n, (F n).CommShift ℤ] [∀ n, (F n).IsTriangulated]
  [∀ n, NatTrans.CommShift (τ n) ℤ] in
/-- The difference map of `n ↦ Fₙ(X)` is the difference map of the components of the `τₙ`. -/
theorem tower_familyDifference (X : C) :
    familyDifference (fun n : ℕ => (tower F τ X).obj ⟨n⟩)
        (fun n => (tower F τ X).map (homOfLE (Nat.le_succ n)).op) =
      familyDifference (fun n => (F n).obj X) fun n => (τ n).app X := by
  show familyDifference (fun n => (F n).obj X) _ = _
  congr 1
  funext n
  exact tower_map_succ F τ X n

/-- The objects `X` of `C` for which the difference map of `n ↦ Fₙ(X)` is invertible, that is,
for which `R lim Fₙ(X) = 0`. -/
def rlimZero : ObjectProperty C := fun X =>
  IsIso (familyDifference (fun n => (F n).obj X) fun n => (τ n).app X)

variable {F τ}

/-- The two-out-of-three property along a distinguished triangle, in the three positions. -/
theorem rlimZero_of_distTriang (Δ : Triangle C) (hΔ : Δ ∈ distTriang C) :
    (rlimZero F τ Δ.obj₁ → rlimZero F τ Δ.obj₂ → rlimZero F τ Δ.obj₃) ∧
      (rlimZero F τ Δ.obj₁ → rlimZero F τ Δ.obj₃ → rlimZero F τ Δ.obj₂) ∧
      (rlimZero F τ Δ.obj₂ → rlimZero F τ Δ.obj₃ → rlimZero F τ Δ.obj₁) := by
  let T : ℕ → Triangle D := fun n => (F n).mapTriangle.obj Δ
  let φ : ∀ n, T (n + 1) ⟶ T n := fun n => StacksDraft.NatTransDevissage.mapTriangleHom (τ n) Δ
  have hT : productTriangle T ∈ distTriang D :=
    productTriangle_distinguished T fun n => (F n).map_distinguished Δ hΔ
  let ψ := productTriangleDifference T φ
  exact ⟨fun h₁ h₂ => isIso₃_of_isIso₁₂ ψ hT hT h₁ h₂,
    fun h₁ h₃ => isIso₂_of_isIso₁₃ ψ hT hT h₁ h₃,
    fun h₂ h₃ => isIso₁_of_isIso₂₃ ψ hT hT h₂ h₃⟩

omit [∀ n, NatTrans.CommShift (τ n) ℤ] in
/-- The zero object has `R lim Fₙ(0) = 0`. -/
theorem rlimZero_of_isZero {X : C} (hX : IsZero X) : rlimZero F τ X := by
  have hP : IsZero (∏ᶜ fun n => (F n).obj X) :=
    (IsZero.iff_id_eq_zero _).2 (Pi.hom_ext _ _ fun n => ((F n).map_isZero hX).eq_of_tgt _ _)
  exact ⟨⟨0, hP.eq_of_src _ _, hP.eq_of_src _ _⟩⟩

/-- `R lim Fₙ(-) = 0` is invariant under isomorphism. -/
theorem rlimZero_of_iso {X Y : C} (e : X ≅ Y) (hX : rlimZero F τ X) : rlimZero F τ Y := by
  have hΔ : Triangle.mk e.hom (0 : Y ⟶ 0) (0 : (0 : C) ⟶ X⟦(1 : ℤ)⟧) ∈ distTriang C :=
    (Triangle.distinguished_iff_of_isZero₃ _ (isZero_zero _)).2 e.isIso_hom
  exact (rlimZero_of_distTriang _ hΔ).2.1 hX (rlimZero_of_isZero (isZero_zero C))

/-- The objects `X` with `R lim Fₙ(X) = 0` are closed under isomorphism. -/
instance : (rlimZero F τ).IsClosedUnderIsomorphisms where
  of_iso e hX := rlimZero_of_iso e hX

/-- `R lim Fₙ(-) = 0` is stable under the shift by `1`. -/
theorem rlimZero_shift_one {X : C} (hX : rlimZero F τ X) : rlimZero F τ (X⟦(1 : ℤ)⟧) :=
  (rlimZero_of_distTriang _ (contractible_distinguished₂ X)).1 hX
    (rlimZero_of_isZero (isZero_zero C))

/-- `R lim Fₙ(-) = 0` is stable under the shift by `-1`. -/
theorem rlimZero_shift_neg_one {X : C} (hX : rlimZero F τ X) :
    rlimZero F τ (X⟦(-1 : ℤ)⟧) := by
  have h : rlimZero F τ (X⟦(-1 : ℤ)⟧⟦(1 : ℤ)⟧) :=
    rlimZero_of_iso ((shiftEquiv C (1 : ℤ)).counitIso.app X).symm hX
  exact (rlimZero_of_distTriang _ (contractible_distinguished₂ (X⟦(-1 : ℤ)⟧))).2.2
    (rlimZero_of_isZero (isZero_zero C)) h

/-- `R lim Fₙ(-) = 0` is stable under every shift. -/
theorem rlimZero_shift {X : C} (hX : rlimZero F τ X) (a : ℤ) : rlimZero F τ (X⟦a⟧) := by
  induction a using Int.induction_on with
  | zero => exact rlimZero_of_iso ((shiftFunctorZero C ℤ).app X).symm hX
  | succ k ih =>
      exact rlimZero_of_iso ((shiftFunctorAdd' C (k : ℤ) 1 (k + 1) rfl).app X).symm
        (rlimZero_shift_one ih)
  | pred k ih =>
      exact rlimZero_of_iso ((shiftFunctorAdd' C (-(k : ℤ)) (-1) (-(k : ℤ) - 1)
        (by omega)).app X).symm (rlimZero_shift_neg_one ih)

/-- **The objects `X` with `R lim Fₙ(X) = 0` form a triangulated subcategory.** -/
theorem rlimZero_isTriangulated : (rlimZero F τ).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, rlimZero_of_isZero (isZero_zero C)⟩
  isStableUnderShiftBy a := ⟨fun _ hX => rlimZero_shift hX a⟩
  ext₂' Δ hΔ h₁ h₃ := (rlimZero F τ).le_isoClosure _ ((rlimZero_of_distTriang Δ hΔ).2.1 h₁ h₃)

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [∀ n, (F n).CommShift ℤ] [∀ n, (F n).IsTriangulated]
  [∀ n, NatTrans.CommShift (τ n) ℤ] in
/-- **For `X` with `R lim Fₙ(X) = 0`, every derived limit of `n ↦ Fₙ(X)` is zero.** -/
theorem isZero_of_isDerivedLimit {X : C} (hX : rlimZero F τ X) {K : D}
    (hK : IsDerivedLimit (tower F τ X) K) : IsZero K :=
  hK.isZero_of_isIso_difference (by rwa [tower_familyDifference])

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [∀ n, (F n).CommShift ℤ] [∀ n, (F n).IsTriangulated]
  [∀ n, NatTrans.CommShift (τ n) ℤ] in
/-- An object `X` such that `n ↦ Fₙ(X)` has a zero derived limit has `R lim Fₙ(X) = 0`. -/
theorem rlimZero_of_isDerivedLimit {X : C} {K : D} (hK : IsDerivedLimit (tower F τ X) K)
    (hz : IsZero K) : rlimZero F τ X := by
  have h := hK.isIso_difference_of_isZero hz
  rwa [tower_familyDifference] at h

end TriangulatedTower

end CategoryTheory.Pretriangulated

end
