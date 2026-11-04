module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ChowGroupsOfMotives
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveMonoidDuality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TateRealization
public import StacksFrontier.CategoryTheory.GradedObject.MonoidalFunctorDuality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The cycle class map of a realization of Chow motives

Let `G : M_k ⥤ graded F-vector spaces` be an additive monoidal functor and `eₙ ∈ G(𝟏(n))^{-2n}`
elements. A cycle `α ∈ CH^i(X)` on a smooth projective scheme `X` over `k` is, by Stacks 0FG0,
a correspondence `a_α ∈ Corr^i(Spec k, X)`, i.e. a morphism of motives `a_α : 𝟏(-i) ⟶ h(X)`; the
cycle class of `α` is `γ(α) = G(a_α)(e_{-i}) ∈ G(h(X))^{2i}` (Stacks 0FH1, datum (D2)). This file
constructs `γ` and proves its compatibility with pullbacks (axiom (C)(a)): for `f : X ⟶ Y` the
correspondence of `f^!β` is `a_β ∘ [Γ_f]` (Stacks 0FG5 (1)), so that `γ(f^!β) = G(h(f))(γ(β))`.

## Main definitions

* `Stacks.WeilCohomology.pointCorrHom`: `α ↦ a_α ∈ Corr^i(Spec k, X)`, as a morphism of the
  category of correspondences.
* `Stacks.WeilCohomology.ChowMotiveCat.pointMotiveHom`: `a_α : 𝟏(-i) ⟶ h(X)`.
* `Stacks.WeilCohomology.ChowMotiveCat.cycleClassMotive`: `γ : CH^i(X) → G(h(X))^{2i}`.

## Main results

* `Stacks.WeilCohomology.pointCorrHom_comp_graphHom`: `a_β ∘ [Γ_f] = a_{f^!β}`.
* `Stacks.WeilCohomology.ChowMotiveCat.cycleClassMotive_gysin`: `γ(f^!β) = G(h(f))(γ(β))`.
* `Stacks.WeilCohomology.pointCorrHom_comp_transposeGraphHom`: `a_α ∘ [Γ_f]ᵗ = a_{f_*α}`, and
  `Stacks.WeilCohomology.tensorHom_graphHom_pointCorrHom_comp_fundamentalClassHom`: the identity
  of correspondences behind (C)(b), from Stacks 0FG8.

## References

* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Tag 0FG5](https://stacks.math.columbia.edu/tag/0FG5)
* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

open CorrespondenceCategory ChowMotiveCat SmoothProjectiveScheme

variable {k : Type u} [Field k]

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
    CorrespondenceCategory _)

/-- **The correspondence of a cycle** (Stacks 0FG0): `α ∈ CH^i(X)` read as the correspondence
`a_α ∈ Corr^i(Spec k, X)` of `1 ⊗ α ∈ CH^i(X) ⊗ ℚ`, as a morphism `Spec k ⟶ X` of the category
of correspondences. -/
def pointCorrHom (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ) :
    codimensionChowGroup k X.obj.hom i →+
      ((𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) :
          (canonicalCorrespondenceCompositionData k).Obj) ⟶ 𝐎 X) :=
  haveI : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  ((homOf i).toAddMonoidHom.comp (pointCorrEquiv X i).toLinearMap.toAddMonoidHom).comp
    (codimensionToCodimChow k X.obj.hom i)

/-- `pointCorrHom X i α` is `homOf i` of the correspondence attached to the class of `α` in
`CodimChow`. -/
theorem pointCorrHom_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) :
    haveI : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
    pointCorrHom X i α = homOf i (pointCorrEquiv X i (codimensionToCodimChow k X.obj.hom i α)) :=
  rfl

/-- The correspondence `a_α` of `α ∈ CH^i(X)` is homogeneous of degree `i`. -/
theorem pointCorrHom_mem_grade (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) :
    pointCorrHom X i α ∈ GradedCategory.grade (R := ℚ) _ _ i :=
  homOf_mem_grade _

/-- An equation `x' ≫ y' = z'` between morphisms with other spellings `A', B', C'` of the same
objects gives the equation between the same morphisms read at `A, B, C`. -/
theorem comp_eq_of_heq {𝒞 : Type*} [Category 𝒞] {A' B' C' : 𝒞} {x' : A' ⟶ B'} {y' : B' ⟶ C'}
    {z' : A' ⟶ C'} (h : x' ≫ y' = z') {A B C : 𝒞} (hA : A = A') (hB : B = B') (hC : C = C')
    {x : A ⟶ B} {y : B ⟶ C} {z : A ⟶ C} (hx : x ≍ x') (hy : y ≍ y') (hz : z ≍ z') :
    x ≫ y = z := by
  subst hA hB hC
  cases hx
  cases hy
  cases hz
  exact h

/-- Transport of a correspondence from the point along an equality of codimensions. -/
theorem homOf_pointCorrEquiv_codimChowCongr (X : (SmoothProjectiveScheme k).FullSubcategory)
    {r r' : ℤ} (h : r = r') (x : CodimChow k X.obj.hom r) :
    homOf r' (pointCorrEquiv X r' (codimChowCongr k X.obj.hom h x)) =
      homOf r (pointCorrEquiv X r x) := by
  subst h
  rw [codimChowCongr_self]

/-- **Stacks 0FH1, proof of (C)(a)**: for `f : X ⟶ Y` and `β ∈ CH^i(Y)`, the correspondence of
`f^!β` is `a_β ∘ [Γ_f]`: pushforward by `[Γ_f]` is the Gysin map (Stacks 0FG5 (1)) and
composition with a correspondence from the point is pushforward (Stacks 0FG0). -/
theorem pointCorrHom_comp_graphHom {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (i : ℤ) (β : codimensionChowGroup k Y.obj.hom i) :
    pointCorrHom Y i β ≫ (graphHom f : 𝐎 Y ⟶ 𝐎 X) =
      pointCorrHom X i (codimensionGysin X.obj.hom Y.obj.hom (Over.w f.hom) i β) := by
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  have : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
  have h₀ := LinearMap.congr_fun (pushforward_graphCorrespondenceSP f i) ((1 : ℚ) ⊗ₜ[ℤ] β)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
    rationalCodimensionToCodimChow_tmul, one_smul] at h₀
  rw [pointCorrHom_apply, pointCorrHom_apply, ← homOf_graphCorrespondenceSP, homOf_comp_homOf,
    ← pointCorrEquiv_pushforward, h₀]
  exact homOf_pointCorrEquiv_codimChowCongr X (add_zero i).symm _

/-- The transposed graph `[Γ_f]ᵗ` as a homogeneous morphism of correspondences. -/
theorem transposeGraphHom_eq_homOf {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (d e : ℕ) :
    transposeGraphHom f e d = homOf ((e : ℤ) - d) (transposeGraphCorrespondenceSP f e d) := by
  rw [transposeGraphHom, homOf, DirectSum.lof_eq_of]

/-- **Stacks 0FH1, proof of (C)(b)**: for `f : X ⟶ Y` with `X`, `Y` equidimensional of
dimensions `d`, `e` and `α ∈ CH^p(X)`, the correspondence of `f_*α` is `a_α ∘ [Γ_f]ᵗ`
(Stacks 0FG5 (3)(a) and 0FG0). -/
theorem pointCorrHom_comp_transposeGraphHom {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) {d e : ℕ} (hX : RelativeDimension X.obj.hom d)
    (hY : RelativeDimension Y.obj.hom e) (p : ℤ)
    (α : codimensionChowGroup k X.obj.hom p) :
    pointCorrHom X p α ≫ transposeGraphHom f e d =
      pointCorrHom Y (p + ((e : ℤ) - d))
        (equidimensionalPushforward f d e p (p + ((e : ℤ) - d)) (by ring) α) := by
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  have : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
  rw [pointCorrHom_apply, pointCorrHom_apply, transposeGraphHom_eq_homOf, homOf_comp_homOf,
    ← pointCorrEquiv_pushforward,
    pushforward_transposeGraphCorrespondenceSP_codimensionToCodimChow f hY hX p α]

/-- **Stacks 0FH1, proof of (C)(b), on correspondences**: for `f : X ⟶ Y` with `X`, `Y`
equidimensional of dimensions `d`, `e` and `α ∈ CH^p(X)`, the two morphisms
`Y ⊗ Spec k ⟶ Spec k`

  `([Γ_f] ⊗ a_α) ≫ η_X ≫ [X]` and `(1 ⊗ a_{f_*α}) ≫ η_Y ≫ [Y]`

agree, by Stacks 0FG8 precomposed with `1 ⊗ a_α`. -/
theorem tensorHom_graphHom_pointCorrHom_comp_fundamentalClassHom
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) {d e : ℕ}
    (hX : RelativeDimension X.obj.hom d)
    (hY : RelativeDimension Y.obj.hom e) (p : ℤ) (α : codimensionChowGroup k X.obj.hom p) :
    CorrespondenceCategory.tensorHom (graphHom f : 𝐎 Y ⟶ 𝐎 X) (pointCorrHom X p α) ≫
        diagonalGraphHom X ≫ fundamentalClassHom hX =
      CorrespondenceCategory.tensorHom (𝟙 (𝐎 Y))
          (pointCorrHom Y (p + ((e : ℤ) - d))
            (equidimensionalPushforward f d e p (p + ((e : ℤ) - d)) (by ring) α)) ≫
        diagonalGraphHom Y ≫ fundamentalClassHom hY := by
  rw [← pointCorrHom_comp_transposeGraphHom f hX hY p α]
  have e₁ : CorrespondenceCategory.tensorHom (graphHom f : 𝐎 Y ⟶ 𝐎 X) (pointCorrHom X p α) =
      CorrespondenceCategory.tensorHom (𝟙 (𝐎 Y)) (pointCorrHom X p α) ≫
        CorrespondenceCategory.tensorHom (graphHom f : 𝐎 Y ⟶ 𝐎 X) (𝟙 (𝐎 X)) := by
    rw [CorrespondenceCategory.tensorHom_comp_tensorHom', Category.id_comp, Category.comp_id]
  have e₂ : CorrespondenceCategory.tensorHom (𝟙 (𝐎 Y))
        (pointCorrHom X p α ≫ transposeGraphHom f e d) =
      CorrespondenceCategory.tensorHom (𝟙 (𝐎 Y)) (pointCorrHom X p α) ≫
        CorrespondenceCategory.tensorHom (𝟙 (𝐎 Y)) (transposeGraphHom f e d) := by
    rw [CorrespondenceCategory.tensorHom_comp_tensorHom', Category.id_comp]
  rw [e₁, e₂, Category.assoc, Category.assoc, graph_tensor_diagonal_fundamental_comm hY hX f]

namespace ChowMotiveCat

open CategoryTheory.GradedCategory

/- As in `StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveMonoid`, the monoidal
structure of `M_k` is taken through the generic instances in this section. -/
attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct

/-- **The morphism of motives of a cycle** (Stacks 0FG0): `α ∈ CH^i(X)` read as
`a_α : 𝟏(-i) ⟶ h(X)`. -/
def pointMotiveHom (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) :=
  TwistedKaroubi.Hom.mk (R := ℚ) (M := tate k (-i)) (N := TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
    (pointCorrHom X i α)
    ⟨TwistedKaroubi.grade_cast (pointCorrHom_mem_grade X i α) (by simp), Category.id_comp _,
      Category.comp_id _⟩

/-- The underlying correspondence of `pointMotiveHom X i α` is `pointCorrHom X i α`. -/
theorem pointMotiveHom_val (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) :
    (pointMotiveHom X i α).val = pointCorrHom X i α :=
  rfl

/-- The morphism of motives of a cycle is additive in the cycle: `a_{α + β} = a_α + a_β`. -/
theorem pointMotiveHom_add (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α β : codimensionChowGroup k X.obj.hom i) :
    pointMotiveHom X i (α + β) = pointMotiveHom X i α + pointMotiveHom X i β :=
  TwistedKaroubi.hom_ext (map_add (pointCorrHom X i) α β)

/-- The morphism of motives of the zero cycle is zero. -/
theorem pointMotiveHom_zero (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ) :
    pointMotiveHom X i 0 = 0 :=
  TwistedKaroubi.hom_ext (map_zero (pointCorrHom X i))

/-- **Stacks 0FH1, proof of (C)(a), on motives**: `a_β ≫ h(f) = a_{f^!β}`. -/
theorem pointMotiveHom_comp_motMap {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (i : ℤ) (β : codimensionChowGroup k Y.obj.hom i) :
    pointMotiveHom Y i β ≫ motMap f =
      pointMotiveHom X i (codimensionGysin X.obj.hom Y.obj.hom (Over.w f.hom) i β) :=
  TwistedKaroubi.hom_ext <| comp_eq_of_heq (pointCorrHom_comp_graphHom f i β)
    (A := (tate k (-i)).X) (B := (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y)).X)
    (C := (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)).X) rfl rfl rfl
    (x := (pointMotiveHom Y i β).val) (y := (motMap f).val)
    (z := (pointMotiveHom X i (codimensionGysin X.obj.hom Y.obj.hom (Over.w f.hom) i β)).val)
    HEq.rfl HEq.rfl HEq.rfl

section Realization

variable {F : Type w} [Field F] (G : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{w} F))
  [G.Additive] (e : ∀ n : ℤ, (G.obj (tate k n)) (-2 * n))

/-- `e_{-i} ∈ G(𝟏(-i))^{2i}`. -/
def tateGenNeg (i : ℤ) : (G.obj (tate k (-i))) (2 * i) :=
  (eqToHom (congrArg (G.obj (tate k (-i))) (show -2 * -i = 2 * i by ring))).hom (e (-i))

/-- **The cycle class map of a realization** (Stacks 0FH1, datum (D2)): `γ(α) = G(a_α)(e_{-i})`
for `α ∈ CH^i(X)`, with `a_α : 𝟏(-i) ⟶ h(X)` the correspondence of `α` (Stacks 0FG0) and
`e_{-i} ∈ G(𝟏(-i))^{2i}`. -/
def cycleClassMotive (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ) :
    codimensionChowGroup k X.obj.hom i →+
      (G.obj (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))) (2 * i) where
  toFun α := (G.map (pointMotiveHom X i α) (2 * i)).hom (tateGenNeg G e i)
  map_zero' := by rw [pointMotiveHom_zero, G.map_zero]; rfl
  map_add' α β := by rw [pointMotiveHom_add, G.map_add]; rfl

/-- The cycle class of `α ∈ CH^i(X)` is `G(a_α)(e_{-i})`. -/
theorem cycleClassMotive_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) :
    cycleClassMotive G e X i α = (G.map (pointMotiveHom X i α) (2 * i)).hom (tateGenNeg G e i) :=
  rfl

/-- **Axiom (C)(a)** (Stacks 0FH1): the cycle class map is compatible with pullbacks,
`γ(f^!β) = G(h(f))(γ(β))` for `f : X ⟶ Y` and `β ∈ CH^i(Y)`. -/
theorem cycleClassMotive_gysin {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (i : ℤ) (β : codimensionChowGroup k Y.obj.hom i) :
    (G.map (motMap f) (2 * i)).hom (cycleClassMotive G e Y i β) =
      cycleClassMotive G e X i (codimensionGysin X.obj.hom Y.obj.hom (Over.w f.hom) i β) := by
  rw [cycleClassMotive_apply, cycleClassMotive_apply, ← ModuleCat.comp_apply,
    ← GradedObject.categoryOfGradedObjects_comp, ← G.map_comp, pointMotiveHom_comp_motMap]

end Realization

end ChowMotiveCat

end Stacks.WeilCohomology

end
