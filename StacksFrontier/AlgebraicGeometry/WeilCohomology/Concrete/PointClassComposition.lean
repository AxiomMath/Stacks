module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalGradedCategory

/-!
# Composing the class of a rational point with the fundamental class

Let `k` be a field, let `X` be smooth and proper over `k` of constant dimension `d`, and let
`x : Spec k ⟶ X` be a rational point. The proof of Stacks 0FGD (2) uses two correspondences:

* `a' ∈ Corr^d(Spec k, X) = CH^d(X)`, the class of the point `x`;
* `b' ∈ Corr^{-d}(X, Spec k) = CH_d(X)`, the fundamental class `[X]`.

It computes their two compositions by intersecting cycles:

* `b' ∘ a' = 1`, because `[x] · [X] = [x]` on `Spec k × X × Spec k`;
* `a' ∘ b' = [X × x]`, because `pr₁₂^* b' · pr₂₃^* a'` is the cycle `X × Spec k × x` on
  `X × Spec k × X`.

In each case the two cycles meet properly with Cohen–Macaulay local rings along the
intersection, so both computations are instances of the proper-intersection formula of Stacks
0FFD, in the form `DiagonalClassFamily.ProperIntersectionFormula.compositionInt_closedSubscheme`
(namespace `Stacks.WeilCohomology`). Both are proved here on Chow groups, with the composition
`c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')` of Section 0FFZ, for any family of diagonal classes
satisfying the formula, such as the canonical one
(`Stacks.WeilCohomology.canonicalDiagonalClassFamily_properIntersectionFormula`).

The point is a scheme `P` with an isomorphism `P ≅ Spec k` over `k`.

## Main definitions

* `Stacks.WeilCohomology.pointSectionEmbedding`: the point `x`, as the closed subscheme
  `(𝟙, x) : P ⟶ P ×_k X`.
* `Stacks.WeilCohomology.unitSectionEmbedding`: `X`, as the closed subscheme `X ⟶ X ×_k P`.
* `Stacks.WeilCohomology.constantFibreEmbedding`: the fibre `X × x`, as the closed subscheme
  `y ↦ (y, x)` of `X ×_k X`.

## Main results

In the namespace `Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula`:

* `compositionInt_pointSection_unitSection`: `[X] ∘ [x] = [Δ_P]`, i.e. `b' ∘ a' = 1`.
* `compositionInt_unitSection_pointSection`: `[x] ∘ [X] = [X × x]`, i.e. `a' ∘ b' = c₂`.

## References

* [Stacks Project, Tag 0FGD](https://stacks.math.columbia.edu/tag/0FGD)
* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k] {X P : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sP : P ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [IsIso sP]
  (x : P ⟶ X) (hx : x ≫ sX = sP)

/-! ### The three closed subschemes -/

/-- The point `x : P ⟶ X`, as the closed subscheme `(𝟙, x) : P ⟶ P ×_k X`. Its class is the
correspondence `a' ∈ Corr^d(P, X)` of Stacks 0FGD (2). -/
abbrev pointSectionEmbedding : P ⟶ Limits.pullback sP sX :=
  pullback.lift (𝟙 P) x (by rw [Category.id_comp, hx])

/-- `X`, as the closed subscheme `(𝟙, s) : X ⟶ X ×_k P` of `X ×_k P` for `P ≅ Spec k`. Its class
is the correspondence `b' ∈ Corr^{-d}(X, P)` of Stacks 0FGD (2). -/
abbrev unitSectionEmbedding : X ⟶ Limits.pullback sX sP :=
  pullback.lift (𝟙 X) (sX ≫ inv sP) (by simp)

/-- The fibre `X × x`, as the closed subscheme `y ↦ (y, x)` of `X ×_k X`. Its class is the
correspondence `c₂ = [X × x]` of Example 0FG6. -/
abbrev constantFibreEmbedding : X ⟶ Limits.pullback sX sX :=
  pullback.lift (𝟙 X) (sX ≫ inv sP ≫ x) (by simp [hx])

omit [Smooth sX] [IsIso sP] in
include hx in
/-- The point `(𝟙, x) : P ⟶ P ×_k X` is a closed immersion. -/
theorem isClosedImmersion_pointSectionEmbedding :
    IsClosedImmersion (pointSectionEmbedding k sX sP x hx) := by
  have : IsClosedImmersion (pointSectionEmbedding k sX sP x hx ≫ pullback.fst sP sX) := by
    rw [pullback.lift_fst]; infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst sP sX)

omit [Smooth sX] [IsSeparated sX] in
/-- `X ⟶ X ×_k P` is a closed immersion. -/
theorem isClosedImmersion_unitSectionEmbedding :
    IsClosedImmersion (unitSectionEmbedding k sX sP) := by
  have : IsClosedImmersion (unitSectionEmbedding k sX sP ≫ pullback.fst sX sP) := by
    rw [pullback.lift_fst]; infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst sX sP)

omit [Smooth sX] in
include hx in
/-- `y ↦ (y, x)` is a closed immersion `X ⟶ X ×_k X`. -/
theorem isClosedImmersion_constantFibreEmbedding :
    IsClosedImmersion (constantFibreEmbedding k sX sP x hx) := by
  have : IsClosedImmersion (constantFibreEmbedding k sX sP x hx ≫ pullback.fst sX sX) := by
    rw [pullback.lift_fst]; infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst sX sX)

attribute [local instance] isClosedImmersion_pointSectionEmbedding
  isClosedImmersion_unitSectionEmbedding isClosedImmersion_constantFibreEmbedding
  isClosedImmersion_graphMorphism

/-! ### The two fibre products over the middle factor -/

omit [Smooth sX] [IsSeparated sX] in
/-- The fibre product `x ×_X X` of the point and of `X` over the middle factor `X` maps to
`P ×_k P` through the diagonal of `P`. -/
theorem toProduct_pointSection_unitSection :
    compositionFibre.toProduct (pointSectionEmbedding k sX sP x hx) (unitSectionEmbedding k sX sP) =
      pullback.fst _ _ ≫ graphMorphism sP sP (𝟙 P) (Category.id_comp sP) := by
  have h := pullback.condition (f := pointSectionEmbedding k sX sP x hx ≫ pullback.snd sP sX)
    (g := unitSectionEmbedding k sX sP ≫ pullback.fst sX sP)
  simp only [pointSectionEmbedding, unitSectionEmbedding, pullback.lift_snd, pullback.lift_fst,
    Category.comp_id] at h
  apply pullback.hom_ext
  · rw [compositionFibre.toProduct, pullback.lift_fst, Category.assoc]
    congr 1
    rw [pullback.lift_fst, graphMorphism_fst]
  · simp only [compositionFibre.toProduct, unitSectionEmbedding, pullback.lift_snd,
      Category.assoc, Category.comp_id]
    rw [← reassoc_of% h, reassoc_of% hx, IsIso.hom_inv_id, Category.comp_id]

omit [Smooth sX] [IsSeparated sX] in
/-- The fibre product `X ×_P x` of `X` and of the point over the middle factor `P` maps to
`X ×_k X` onto the fibre `X × x`. -/
theorem toProduct_unitSection_pointSection :
    compositionFibre.toProduct (unitSectionEmbedding k sX sP) (pointSectionEmbedding k sX sP x hx) =
      pullback.fst _ _ ≫ constantFibreEmbedding k sX sP x hx := by
  have h := pullback.condition (f := unitSectionEmbedding k sX sP ≫ pullback.snd sX sP)
    (g := pointSectionEmbedding k sX sP x hx ≫ pullback.fst sP sX)
  simp only [pointSectionEmbedding, unitSectionEmbedding, pullback.lift_snd, pullback.lift_fst,
    Category.comp_id] at h
  apply pullback.hom_ext
  · rw [compositionFibre.toProduct, pullback.lift_fst, Category.assoc]
    congr 1
    rw [pullback.lift_fst, pullback.lift_fst]
  · simp only [compositionFibre.toProduct, pointSectionEmbedding, constantFibreEmbedding,
      pullback.lift_snd, Category.assoc]
    rw [← reassoc_of% h]

/-! ### The two compositions -/

variable {k} {Δ : DiagonalClassFamily k}

/-- **`b' ∘ a' = 1` (Stacks 0FGD (2)).** For `X` smooth and proper over `k` of constant
dimension `d` and a point `x : P ⟶ X` with `P ≅ Spec k`, compose the class
`a' = [x] ∈ CH_0(P × X)` with the fundamental class `b' = [X] ∈ CH_d(X × P)`. The result is the
class of the diagonal of `P`, that is the identity correspondence of `P`. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.compositionInt_pointSection_unitSection
    [IsProper sX] (hΔ : Δ.ProperIntersectionFormula) {d : ℕ} (hX : RelativeDimension sX d)
    (hP : RelativeDimension sP 0) :
    compositionInt k sP sX sP Δ hP hX hP d (-d)
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sP sX) (pointSectionEmbedding k sX sP x hx) ((d : ℤ) - d)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sP) (unitSectionEmbedding k sX sP) (((0 : ℕ) : ℤ) - -d))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sP sP) (graphMorphism sP sP (𝟙 P) (Category.id_comp sP))
        (((0 : ℕ) : ℤ) - (d + -d))) := by
  have hκ := toProduct_pointSection_unitSection k sX sP x hx
  have : IsIso (pullback.fst (pointSectionEmbedding k sX sP x hx ≫ pullback.snd sP sX)
      (unitSectionEmbedding k sX sP ≫ pullback.fst sX sP)) := by
    rw [pullback.lift_fst]
    infer_instance
  have : IsClosedImmersion (compositionFibre.toProduct (pointSectionEmbedding k sX sP x hx)
      (unitSectionEmbedding k sX sP)) := by rw [hκ]; infer_instance
  rw [hΔ.compositionInt_closedSubscheme k sP sX sP hP hX hP d (-d) _ _ ?_ ?_ ?_ ?_]
  · exact congrArg _ (cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _
      (asIso (pullback.fst _ _)) hκ.symm _)
  · intro T
    rw [deltaDimension_congr (g := sP) (by rw [prodBase, pullback.lift_fst_assoc,
      Category.id_comp]), sub_self]
    exact_mod_cast deltaDimension_irreducibleComponent_of_relativeDimension k sP 0 hP T
  · intro T
    rw [deltaDimension_congr (g := sX) (by rw [prodBase, pullback.lift_fst_assoc,
      Category.id_comp])]
    push_cast
    rw [zero_sub, neg_neg]
    exact deltaDimension_irreducibleComponent_of_relativeDimension k sX d hX T
  · rw [schemeDeltaDimension_congr _ (show compositionFibre.toProduct
        (pointSectionEmbedding k sX sP x hx) (unitSectionEmbedding k sX sP) ≫ prodBase sP sP =
          (asIso (pullback.fst _ _)).hom ≫ sP by
        rw [hκ, asIso_hom, Category.assoc, prodBase, pullback.lift_fst_assoc, Category.id_comp]),
      schemeDeltaDimension_comp_iso]
    simpa using schemeDeltaDimension_le_of_relativeDimension sP hP
  · intro z _
    exact ⟨isCohenMacaulayLocalRing_stalk_of_smooth k sP _,
      isCohenMacaulayLocalRing_stalk_of_smooth k sX _⟩

/-- **`a' ∘ b' = c₂` (Stacks 0FGD (2)).** For `X` smooth over `k` of constant dimension `d` and a
point `x : P ⟶ X` with `P ≅ Spec k`, compose the fundamental class `b' = [X] ∈ CH_d(X × P)`
with the class `a' = [x] ∈ CH_0(P × X)`. The result is the class of the fibre `X × x` in
`CH_d(X × X)`. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.compositionInt_unitSection_pointSection
    (hΔ : Δ.ProperIntersectionFormula) {d : ℕ} (hX : RelativeDimension sX d)
    (hP : RelativeDimension sP 0) :
    compositionInt k sX sP sX Δ hX hP hX (-d) d
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sP) (unitSectionEmbedding k sX sP) (((0 : ℕ) : ℤ) - -d)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sP sX) (pointSectionEmbedding k sX sP x hx) ((d : ℤ) - d))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sX sX) (constantFibreEmbedding k sX sP x hx) ((d : ℤ) - (-d + d))) := by
  have hκ := toProduct_unitSection_pointSection k sX sP x hx
  have : IsIso (pullback.fst (unitSectionEmbedding k sX sP ≫ pullback.snd sX sP)
      (pointSectionEmbedding k sX sP x hx ≫ pullback.fst sP sX)) := by
    rw [pullback.lift_fst]
    infer_instance
  have : IsClosedImmersion (compositionFibre.toProduct (unitSectionEmbedding k sX sP)
      (pointSectionEmbedding k sX sP x hx)) := by rw [hκ]; infer_instance
  rw [hΔ.compositionInt_closedSubscheme k sX sP sX hX hP hX (-d) d _ _ ?_ ?_ ?_ ?_]
  · exact congrArg _ (cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _
      (asIso (pullback.fst _ _)) hκ.symm _)
  · intro T
    rw [deltaDimension_congr (g := sX) (by rw [prodBase, pullback.lift_fst_assoc,
      Category.id_comp])]
    push_cast
    rw [zero_sub, neg_neg]
    exact deltaDimension_irreducibleComponent_of_relativeDimension k sX d hX T
  · intro T
    rw [deltaDimension_congr (g := sP) (by rw [prodBase, pullback.lift_fst_assoc,
      Category.id_comp]), sub_self]
    exact_mod_cast deltaDimension_irreducibleComponent_of_relativeDimension k sP 0 hP T
  · rw [schemeDeltaDimension_congr _ (show compositionFibre.toProduct
        (unitSectionEmbedding k sX sP) (pointSectionEmbedding k sX sP x hx) ≫ prodBase sX sX =
          (asIso (pullback.fst _ _)).hom ≫ sX by
        rw [hκ, asIso_hom, Category.assoc, prodBase, pullback.lift_fst_assoc, Category.id_comp]),
      schemeDeltaDimension_comp_iso]
    simpa using schemeDeltaDimension_le_of_relativeDimension sX hX
  · intro z _
    exact ⟨isCohenMacaulayLocalRing_stalk_of_smooth k sX _,
      isCohenMacaulayLocalRing_stalk_of_smooth k sP _⟩

end Stacks.WeilCohomology

end
