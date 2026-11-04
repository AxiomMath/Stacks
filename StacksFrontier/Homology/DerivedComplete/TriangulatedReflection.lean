module

public import StacksFrontier.Homology.DerivedComplete.CompleteIdeal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GlobalSectionsCompletionComparison

/-!
# Derived completion in a linear pretriangulated category

Let `A` be a commutative ring and let `𝒟` be an `A`-linear pretriangulated category with
countable products whose shift functors are `A`-linear. For `f ∈ A` the derived complete objects
at `f` (`T(K, f) = 0`, i.e. `IsDerivedCompleteAt K f`) are exactly the objects admitting no
nonzero map from an object on which `f` acts invertibly; and every `K` has a derived completion
at `f`: the cone `K^∧` of the map `T(K, f) ⟶ K` from the derived limit of `⋯ →f K →f K`. For a
finitely generated ideal `I ⊆ A` iterating over generators gives the derived completion along `I`,
so the inclusion of the derived `I`-complete objects into `𝒟` has a left adjoint (the shape of
Stacks 099F and 091V).

## Main definitions

* `DerivedCompletionReflection.fiberObj`: `T(K, f)`, the fiber of `1 - f·shift` on `∏ K`.
* `DerivedCompletionReflection.coneObj`, `DerivedCompletionReflection.coneπ`: the derived
  completion `K^∧` at `f`, the cone of `T(K, f) ⟶ K`, and the map `K ⟶ K^∧`.

## Main results

* `DerivedCompletionReflection.isIso_smul_fiber`: `f` acts invertibly on `T(K, f)`.
* `DerivedCompletionReflection.isDerivedCompleteAt_iff_forall_eq_zero`: `K` is derived complete
  at `f` iff every map into `K` from an object on which `f` acts invertibly vanishes.
* `DerivedCompletionReflection.isDerivedCompleteAt_coneObj`,
  `DerivedCompletionReflection.bijective_precomp_coneπ`: `K^∧` is derived complete at `f` and
  `K ⟶ K^∧` is universal among maps to objects derived complete at `f`.
* `DerivedCompletionReflection.isRightAdjoint_ι_isDerivedComplete`: for a finitely generated
  ideal `I`, the inclusion of the derived `I`-complete objects has a left adjoint.

## Implementation notes

The one non-formal input is that `f` acts invertibly on `T(K, f)`. A fill-in `a` of the shift
`s` on `∏ K` (which commutes with `1 - f·s`) gives a fill-in `f·a` of `f·s = 1 - (1 - f·s)`; any
fill-in `α` of `1 - φ` on a distinguished triangle `X ⟶ P ⟶φ P ⟶ X⟦1⟧` satisfies
`(α - 1)² = 0`, because `α - 1` kills the first map and its shift is killed by the third. So
`f·a` is invertible, and so is `f`, which commutes with `a`.

## References

* [Stacks Project, Tag 091V](https://stacks.math.columbia.edu/tag/091V)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 091S](https://stacks.math.columbia.edu/tag/091S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCompletionReflection

section Basic

variable {A : Type*} [CommRing A] {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] [Linear A 𝒟]
  [HasProductsOfShape ℕ 𝒟]

/-- The shift `(xₙ) ↦ (xₙ₊₁)` of `∏ₙ K`. -/
def piShift (K : 𝒟) : (∏ᶜ fun _ : ℕ => K) ⟶ (∏ᶜ fun _ : ℕ => K) :=
  Pi.lift fun n => Pi.π (fun _ : ℕ => K) (n + 1)

omit [Preadditive 𝒟] in
/-- The `n`-th component of `piShift K` is the projection onto the `(n + 1)`-st factor. -/
@[reassoc (attr := simp)]
theorem piShift_π (K : 𝒟) (n : ℕ) :
    piShift K ≫ Pi.π (fun _ : ℕ => K) n = Pi.π (fun _ : ℕ => K) (n + 1) := by
  simp [piShift]

/-- `oneSubSmulShift K f` is `1 - f • piShift K`. -/
theorem oneSubSmulShift_eq (K : 𝒟) (f : A) :
    oneSubSmulShift K f = 𝟙 _ - f • piShift K := by
  refine Pi.hom_ext _ _ fun n => ?_
  rw [oneSubSmulShift_π, Preadditive.sub_comp, Category.id_comp, Linear.smul_comp, piShift_π]

/-- `oneSubSmulShift K f` commutes with `piShift K`. -/
theorem oneSubSmulShift_comp_piShift (K : 𝒟) (f : A) :
    oneSubSmulShift K f ≫ piShift K = piShift K ≫ oneSubSmulShift K f := by
  refine Pi.hom_ext _ _ fun n => ?_
  rw [Category.assoc, piShift_π, oneSubSmulShift_π, Category.assoc, oneSubSmulShift_π,
    Preadditive.comp_sub, Linear.comp_smul, piShift_π, piShift_π]

/-- The components of a map killed by `1 - f·shift` satisfy `gₙ = f·gₙ₊₁`. -/
theorem comp_π_eq_smul_of_comp_oneSubSmulShift {N K : 𝒟} {f : A}
    (G : N ⟶ ∏ᶜ fun _ : ℕ => K) (hG : G ≫ oneSubSmulShift K f = 0) (m : ℕ) :
    G ≫ Pi.π (fun _ : ℕ => K) m = f • (G ≫ Pi.π (fun _ : ℕ => K) (m + 1)) := by
  have := congrArg (· ≫ Pi.π (fun _ : ℕ => K) m) hG
  simp only [Category.assoc, oneSubSmulShift_π, Preadditive.comp_sub, Linear.comp_smul,
    zero_comp] at this
  exact sub_eq_zero.1 this

variable {f : A} {N : 𝒟} [IsIso (f • 𝟙 N)]

omit [HasProductsOfShape ℕ 𝒟] in
/-- If `f` acts invertibly on `N`, then `f • (f • 𝟙 N)⁻¹ = 𝟙 N`. -/
theorem smul_inv_eq_id : f • inv (f • 𝟙 N) = 𝟙 N := by
  rw [← Category.id_comp (inv (f • 𝟙 N)), ← Linear.smul_comp, IsIso.hom_inv_id]

omit [HasProductsOfShape ℕ 𝒟] in
/-- If `f` acts invertibly on `N`, then `f • ((f • 𝟙 N)⁻¹ ≫ y) = y`. -/
theorem smul_comp_inv_smul {X : 𝒟} (y : N ⟶ X) : f • (inv (f • 𝟙 N) ≫ y) = y := by
  rw [← Linear.smul_comp, smul_inv_eq_id, Category.id_comp]

omit [HasProductsOfShape ℕ 𝒟] in
/-- If `f` acts invertibly on `N`, then `(f • 𝟙 N)⁻¹ ≫ (f • y) = y`. -/
theorem inv_smul_comp_smul {X : 𝒟} (y : N ⟶ X) : inv (f • 𝟙 N) ≫ (f • y) = y := by
  rw [Linear.comp_smul, ← Linear.smul_comp, smul_inv_eq_id, Category.id_comp]

/-- `1 - f·shift` is surjective on maps from an object on which `f` acts invertibly. -/
theorem exists_comp_oneSubSmulShift (K : 𝒟) (h : N ⟶ ∏ᶜ fun _ : ℕ => K) :
    ∃ G : N ⟶ ∏ᶜ fun _ : ℕ => K, G ≫ oneSubSmulShift K f = h := by
  let g : ℕ → (N ⟶ K) := fun n => Nat.rec 0
    (fun m q => inv (f • 𝟙 N) ≫ (q - h ≫ Pi.π (fun _ : ℕ => K) m)) n
  refine ⟨Pi.lift g, Pi.hom_ext _ _ fun n => ?_⟩
  rw [Category.assoc, oneSubSmulShift_π, Preadditive.comp_sub, Linear.comp_smul, Pi.lift_π,
    Pi.lift_π]
  show g n - f • (inv (f • 𝟙 N) ≫ (g n - h ≫ Pi.π (fun _ : ℕ => K) n)) = _
  rw [smul_comp_inv_smul, sub_sub_cancel]

/-- If `f` acts invertibly on `N`, every map `N ⟶ K` extends to a map `N ⟶ ∏ K` killed by
`1 - f·shift`. -/
theorem exists_comp_oneSubSmulShift_eq_zero (K : 𝒟) (g : N ⟶ K) :
    ∃ G : N ⟶ ∏ᶜ fun _ : ℕ => K,
      G ≫ oneSubSmulShift K f = 0 ∧ G ≫ Pi.π (fun _ : ℕ => K) 0 = g := by
  let p : ℕ → (N ⟶ N) := fun n => Nat.rec (𝟙 N) (fun _ q => inv (f • 𝟙 N) ≫ q) n
  refine ⟨Pi.lift fun n => p n ≫ g, Pi.hom_ext _ _ fun n => ?_, ?_⟩
  · rw [Category.assoc, oneSubSmulShift_π, Preadditive.comp_sub, Linear.comp_smul, Pi.lift_π,
      Pi.lift_π, zero_comp]
    show p n ≫ g - f • ((inv (f • 𝟙 N) ≫ p n) ≫ g) = 0
    rw [Category.assoc, smul_comp_inv_smul, sub_self]
  · rw [Pi.lift_π]
    exact Category.id_comp g

omit [IsIso (f • 𝟙 N)] in
/-- Derived completeness along `Ideal.span s` is derived completeness at every element of `s`. -/
theorem isDerivedComplete_span_iff (s : Set A) (M : 𝒟) :
    IsDerivedComplete (Ideal.span s) M ↔ ∀ a ∈ s, IsDerivedCompleteAt M a := by
  refine ⟨fun h a ha => h a (Ideal.subset_span ha), fun h a ha => ?_⟩
  have hle : Ideal.span s ≤ derivedCompleteIdeal (A := A) M :=
    Ideal.span_le.2 fun c hc => mem_derivedCompleteIdeal_iff.2 (h c hc)
  exact mem_derivedCompleteIdeal_iff.1 (hle ha)

end Basic

section Shift

variable {A : Type*} [CommRing A] {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟]
  [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]

/-- Exactness of `Hom(W, -)` at the middle vertex of a distinguished triangle. -/
theorem coyoneda_exact₂' {X Y Z W : 𝒟} {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ X⟦(1 : ℤ)⟧}
    (h : Triangle.mk a b c ∈ distTriang 𝒟) (u : W ⟶ Y) (hu : u ≫ b = 0) :
    ∃ v : W ⟶ X, u = v ≫ a :=
  Triangle.coyoneda_exact₂ _ h u hu

/-- Exactness of `Hom(W, -)` at the third vertex of a distinguished triangle. -/
theorem coyoneda_exact₃' {X Y Z W : 𝒟} {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ X⟦(1 : ℤ)⟧}
    (h : Triangle.mk a b c ∈ distTriang 𝒟) (u : W ⟶ Z) (hu : u ≫ c = 0) :
    ∃ v : W ⟶ Y, u = v ≫ b :=
  Triangle.coyoneda_exact₃ _ h u hu

/-- Exactness of `Hom(W, -)` at the shifted first vertex of a distinguished triangle. -/
theorem coyoneda_exact₁' {X Y Z W : 𝒟} {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ X⟦(1 : ℤ)⟧}
    (h : Triangle.mk a b c ∈ distTriang 𝒟) (u : W ⟶ X⟦(1 : ℤ)⟧) (hu : u ≫ a⟦(1 : ℤ)⟧' = 0) :
    ∃ v : W ⟶ Z, u = v ≫ c :=
  Triangle.coyoneda_exact₁ _ h u hu

/-- Exactness of `Hom(-, W)` at the shifted first vertex of a distinguished triangle. -/
theorem yoneda_exact₁' {X Y Z W : 𝒟} {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ X⟦(1 : ℤ)⟧}
    (h : Triangle.mk a b c ∈ distTriang 𝒟) (u : X⟦(1 : ℤ)⟧ ⟶ W) (hu : c ≫ u = 0) :
    ∃ v : Y⟦(1 : ℤ)⟧ ⟶ W, u = a⟦(1 : ℤ)⟧' ≫ v := by
  obtain ⟨v, hv⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ h) u hu
  refine ⟨-v, ?_⟩
  have hv' : u = (-(a⟦(1 : ℤ)⟧')) ≫ (v : Y⟦(1 : ℤ)⟧ ⟶ W) := hv
  rw [hv']
  exact (Preadditive.neg_comp _ _).trans (Preadditive.comp_neg _ _).symm

/-- **A fill-in of `1 - φ` is invertible.** Let `X ⟶ P ⟶ P ⟶ X⟦1⟧` be a distinguished triangle
with middle map `φ`, and let `α` be an endomorphism of `X` completing `(1 - φ, 1 - φ)` to an
endomorphism of the triangle. Then `(α - 1)² = 0`, so `α` is invertible. -/
theorem isIso_of_fillIn_one_sub {X P : 𝒟} (ι : X ⟶ P) (φ : P ⟶ P) (δ : P ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ι φ δ ∈ distTriang 𝒟) (α : X ⟶ X) (h₁ : ι ≫ (𝟙 P - φ) = α ≫ ι)
    (h₃ : δ ≫ α⟦(1 : ℤ)⟧' = (𝟙 P - φ) ≫ δ) : IsIso α := by
  have hιφ : ι ≫ φ = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have hφδ : φ ≫ δ = 0 := comp_distTriang_mor_zero₂₃ _ hT
  obtain ⟨n, hn⟩ : ∃ n : X ⟶ X, n = α - 𝟙 X := ⟨_, rfl⟩
  have hα : α = 𝟙 X + n := by
    rw [hn]
    abel
  have hn₁ : n ≫ ι = 0 := by
    rw [hn, Preadditive.sub_comp, ← h₁, Category.id_comp, Preadditive.comp_sub,
      Category.comp_id, hιφ, sub_zero, sub_self]
  have hn₃ : δ ≫ n⟦(1 : ℤ)⟧' = 0 := by
    rw [hn, Functor.map_sub, CategoryTheory.Functor.map_id, Preadditive.comp_sub, h₃,
      Category.comp_id, Preadditive.sub_comp, Category.id_comp, hφδ, sub_zero, sub_self]
  obtain ⟨g, hg⟩ := yoneda_exact₁' hT (n⟦(1 : ℤ)⟧') hn₃
  have hnn : n ≫ n = 0 := by
    apply (shiftFunctor 𝒟 (1 : ℤ)).map_injective
    rw [Functor.map_comp, Functor.map_zero]
    nth_rw 2 [hg]
    rw [← Category.assoc, ← Functor.map_comp, hn₁, Functor.map_zero, zero_comp]
  refine ⟨𝟙 X - n, ?_, ?_⟩
  · rw [hα]
    simp only [Preadditive.add_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
      hnn]
    abel
  · rw [hα]
    simp only [Preadditive.sub_comp, Preadditive.comp_add, Category.id_comp, Category.comp_id,
      hnn]
    abel

omit [HasZeroObject 𝒟] [Pretriangulated 𝒟] in
  /-- A map `c : N ⟶ X⟦1⟧` vanishes once its `⟦-1⟧` shift, composed with the canonical iso, does. -/
  private theorem eq_zero_of_shift_neg_one_comp_eq_zero {N X : 𝒟} (c : N ⟶ X⟦(1 : ℤ)⟧)
      (h : c⟦(-1 : ℤ)⟧' ≫ (shiftFunctorCompIsoId 𝒟 (1 : ℤ) (-1) (by omega)).hom.app X = 0) :
      c = 0 := by
    apply (shiftFunctor 𝒟 (-1 : ℤ)).map_injective
    rw [Functor.map_zero,
      ← cancel_mono ((shiftFunctorCompIsoId 𝒟 (1 : ℤ) (-1) (by omega)).hom.app X), h, zero_comp]

omit [HasZeroObject 𝒟] [Pretriangulated 𝒟] in
/-- A map into `X⟦1⟧` vanishes once every map from `N⟦-1⟧` to `X` vanishes. -/
theorem eq_zero_of_shift_neg_one {N X : 𝒟} (h : ∀ x : N⟦(-1 : ℤ)⟧ ⟶ X, x = 0)
    (c : N ⟶ X⟦(1 : ℤ)⟧) : c = 0 :=
  eq_zero_of_shift_neg_one_comp_eq_zero c (h _)

omit [HasZeroObject 𝒟] [Pretriangulated 𝒟] in
/-- If `x ↦ x ≫ p` is injective on maps from `N⟦-1⟧`, then `c ↦ c ≫ p⟦1⟧'` is injective on maps
from `N`. -/
theorem eq_zero_of_comp_shift_eq_zero {N X Y : 𝒟} (p : X ⟶ Y)
    (h : ∀ x : N⟦(-1 : ℤ)⟧ ⟶ X, x ≫ p = 0 → x = 0) (c : N ⟶ X⟦(1 : ℤ)⟧)
    (hc : c ≫ p⟦(1 : ℤ)⟧' = 0) : c = 0 := by
  have hnat := (shiftFunctorCompIsoId 𝒟 (1 : ℤ) (-1) (by omega)).hom.naturality p
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hnat
  have hx : (c⟦(-1 : ℤ)⟧' ≫ (shiftFunctorCompIsoId 𝒟 (1 : ℤ) (-1) (by omega)).hom.app X) ≫
      p = 0 := by
    rw [Category.assoc, ← hnat, ← Category.assoc, ← Functor.map_comp, hc, Functor.map_zero,
      zero_comp]
  exact eq_zero_of_shift_neg_one_comp_eq_zero c (h _ hx)

variable {A : Type*} [CommRing A] [Linear A 𝒟] [∀ n : ℤ, (shiftFunctor 𝒟 n).Linear A]

omit [HasZeroObject 𝒟] [∀ (n : ℤ), (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] in
/-- If `f` acts invertibly on `N`, it acts invertibly on every shift of `N`. -/
theorem isIso_smul_shift {N : 𝒟} {f : A} [IsIso (f • 𝟙 N)] (n : ℤ) :
    IsIso (f • 𝟙 (N⟦n⟧)) := by
  have : (shiftFunctor 𝒟 n).map (f • 𝟙 N) = f • 𝟙 (N⟦n⟧) := by
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  rw [← this]
  infer_instance

end Shift

section Triangulated

variable {A : Type*} [CommRing A] {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟]
  [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] [Linear A 𝒟]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Linear A] [HasProductsOfShape ℕ 𝒟]

/-- The object `T(K, f)`: the fiber of `1 - f·shift` on `∏ₙ K`. -/
def fiberObj (K : 𝒟) (f : A) : 𝒟 :=
  (distinguished_cocone_triangle₁ (oneSubSmulShift K f)).choose

/-- The map `T(K, f) ⟶ ∏ₙ K`. -/
def fiberι (K : 𝒟) (f : A) : fiberObj K f ⟶ ∏ᶜ fun _ : ℕ => K :=
  (distinguished_cocone_triangle₁ (oneSubSmulShift K f)).choose_spec.choose

/-- The connecting map `∏ₙ K ⟶ T(K, f)⟦1⟧`. -/
def fiberδ (K : 𝒟) (f : A) : (∏ᶜ fun _ : ℕ => K) ⟶ (fiberObj K f)⟦(1 : ℤ)⟧ :=
  (distinguished_cocone_triangle₁ (oneSubSmulShift K f)).choose_spec.choose_spec.choose

omit [∀ (n : ℤ), Functor.Linear A (shiftFunctor 𝒟 n)] in
/-- The fiber triangle `T(K, f) ⟶ ∏ K ⟶ ∏ K ⟶ T(K, f)⟦1⟧` of `1 - f·shift` is distinguished. -/
theorem fiber_distinguished (K : 𝒟) (f : A) :
    Triangle.mk (fiberι K f) (oneSubSmulShift K f) (fiberδ K f) ∈ distTriang 𝒟 :=
  (distinguished_cocone_triangle₁ (oneSubSmulShift K f)).choose_spec.choose_spec.choose_spec

omit [∀ (n : ℤ), Functor.Linear A (shiftFunctor 𝒟 n)] in
/-- The composite `T(K, f) ⟶ ∏ K ⟶ ∏ K` of `fiberι K f` and `1 - f·shift` is zero. -/
theorem fiberι_comp (K : 𝒟) (f : A) : fiberι K f ≫ oneSubSmulShift K f = 0 :=
  comp_distTriang_mor_zero₁₂ _ (fiber_distinguished K f)

omit [∀ (n : ℤ), Functor.Linear A (shiftFunctor 𝒟 n)] in
/-- The composite of `1 - f·shift` and `fiberδ K f` is zero. -/
theorem comp_fiberδ (K : 𝒟) (f : A) : oneSubSmulShift K f ≫ fiberδ K f = 0 :=
  comp_distTriang_mor_zero₂₃ _ (fiber_distinguished K f)

/-- **`f` acts invertibly on `T(K, f)`.** -/
theorem isIso_smul_fiber (K : 𝒟) (f : A) : IsIso (f • 𝟙 (fiberObj K f)) := by
  have hT := fiber_distinguished K f
  obtain ⟨a, ha₁, ha₃⟩ : ∃ a : fiberObj K f ⟶ fiberObj K f,
      fiberι K f ≫ piShift K = a ≫ fiberι K f ∧
        fiberδ K f ≫ a⟦(1 : ℤ)⟧' = piShift K ≫ fiberδ K f :=
    complete_distinguished_triangle_morphism₁ _ _ hT hT (piShift K) (piShift K)
      (oneSubSmulShift_comp_piShift K f)
  have e : 𝟙 (∏ᶜ fun _ : ℕ => K) - oneSubSmulShift K f = f • piShift K := by
    rw [oneSubSmulShift_eq, sub_sub_cancel]
  have hfa : IsIso (f • a) := by
    refine isIso_of_fillIn_one_sub (fiberι K f) (oneSubSmulShift K f) (fiberδ K f) hT
      (f • a) ?_ ?_
    · rw [e, Linear.comp_smul, Linear.smul_comp, ha₁]
    · rw [e, Functor.Linear.map_smul, Linear.comp_smul, Linear.smul_comp, ha₃]
  have h₁ : (f • 𝟙 (fiberObj K f)) ≫ a = f • a := by rw [Linear.smul_comp, Category.id_comp]
  have h₂ : a ≫ (f • 𝟙 (fiberObj K f)) = f • a := by rw [Linear.comp_smul, Category.comp_id]
  have : IsSplitEpi (f • 𝟙 (fiberObj K f)) :=
    ⟨⟨{ section_ := inv (f • a) ≫ a, id := by rw [Category.assoc, h₂, IsIso.inv_hom_id] }⟩⟩
  have : Mono (f • 𝟙 (fiberObj K f)) := by
    have : Mono ((f • 𝟙 (fiberObj K f)) ≫ a) := by
      rw [h₁]
      infer_instance
    exact mono_of_mono _ a
  exact isIso_of_mono_of_isSplitEpi _

/-- The map `T(K, f) ⟶ ∏ K ⟶ K`. -/
def fiberProj (K : 𝒟) (f : A) : fiberObj K f ⟶ K :=
  fiberι K f ≫ Pi.π (fun _ : ℕ => K) 0

section Invertible

variable {f : A} {N : 𝒟} [IsIso (f • 𝟙 N)]

/-- Maps from `N` to `T(K, f)` are detected by their composite with `T(K, f) ⟶ K`. -/
theorem fiber_hom_ext (K : 𝒟) (x : N ⟶ fiberObj K f) (hx : x ≫ fiberProj K f = 0) :
    x = 0 := by
  have hG : (x ≫ fiberι K f) ≫ oneSubSmulShift K f = 0 := by
    rw [Category.assoc, fiberι_comp, comp_zero]
  have hcomp : ∀ n, (x ≫ fiberι K f) ≫ Pi.π (fun _ : ℕ => K) n = 0 := by
    intro n
    induction n with
    | zero => exact (Category.assoc _ _ _).trans hx
    | succ m ih =>
      have hm := comp_π_eq_smul_of_comp_oneSubSmulShift _ hG m
      rw [ih] at hm
      rw [← inv_smul_comp_smul (f := f) ((x ≫ fiberι K f) ≫ Pi.π (fun _ : ℕ => K) (m + 1)),
        ← hm, comp_zero]
  have hG0 : x ≫ fiberι K f = 0 :=
    Pi.hom_ext _ _ fun n => (hcomp n).trans zero_comp.symm
  have hx1 : x⟦(1 : ℤ)⟧' ≫ (fiberι K f)⟦(1 : ℤ)⟧' = 0 := by
    rw [← Functor.map_comp, hG0, Functor.map_zero]
  obtain ⟨y, hy⟩ := coyoneda_exact₁' (fiber_distinguished K f) (x⟦(1 : ℤ)⟧') hx1
  have := isIso_smul_shift (A := A) (N := N) (f := f) (1 : ℤ)
  obtain ⟨z, hz⟩ := exists_comp_oneSubSmulShift (f := f) (N := N⟦(1 : ℤ)⟧) K y
  apply (shiftFunctor 𝒟 (1 : ℤ)).map_injective
  rw [Functor.map_zero, hy, ← hz, Category.assoc, comp_fiberδ, comp_zero]

omit [∀ (n : ℤ), Functor.Linear A (shiftFunctor 𝒟 n)] in
/-- Every map `N ⟶ K` lifts along `T(K, f) ⟶ K`. -/
theorem exists_fiber_lift (K : 𝒟) (g : N ⟶ K) : ∃ x : N ⟶ fiberObj K f, x ≫ fiberProj K f = g := by
  obtain ⟨G, hG, hG0⟩ := exists_comp_oneSubSmulShift_eq_zero (f := f) (N := N) K g
  obtain ⟨x, hx⟩ := coyoneda_exact₂' (fiber_distinguished K f) G hG
  exact ⟨x, by rw [fiberProj, ← Category.assoc, ← hx, hG0]⟩

end Invertible

/-- **Derived completeness at `f` is right orthogonality to the `f`-invertible objects.** -/
theorem isDerivedCompleteAt_iff_forall_eq_zero (M : 𝒟) (f : A) :
    IsDerivedCompleteAt M f ↔
      ∀ (N : 𝒟) [IsIso (f • 𝟙 N)] (g : N ⟶ M), g = 0 := by
  refine ⟨fun hM N _ g => hM.eq_zero_of_isIso_smul g, fun h => ?_⟩
  have hT := fiber_distinguished M f
  have := isIso_smul_fiber M f
  have h₁ : ∀ (N : 𝒟) [IsIso (f • 𝟙 N)] (g : N ⟶ ∏ᶜ fun _ : ℕ => M), g = 0 :=
    fun N _ g => Pi.hom_ext _ _ fun n => (h N (g ≫ Pi.π _ n)).trans zero_comp.symm
  have hmor₁ : fiberι M f = 0 := h₁ _ _
  have hid : 𝟙 ((fiberObj M f)⟦(1 : ℤ)⟧) = 0 := by
    have h0 : 𝟙 ((fiberObj M f)⟦(1 : ℤ)⟧) ≫ (fiberι M f)⟦(1 : ℤ)⟧' = 0 := by
      rw [hmor₁, Functor.map_zero, comp_zero]
    obtain ⟨y, hy⟩ := coyoneda_exact₁' hT _ h0
    have := isIso_smul_shift (A := A) (N := fiberObj M f) (f := f) (1 : ℤ)
    rw [hy, h₁ _ y, zero_comp]
  have hz : IsZero (fiberObj M f) := by
    have hz1 : IsZero ((fiberObj M f)⟦(1 : ℤ)⟧) := (IsZero.iff_id_eq_zero _).2 hid
    exact IsZero.of_iso ((shiftFunctor 𝒟 (-1 : ℤ)).map_isZero hz1)
      ((shiftFunctorCompIsoId 𝒟 (1 : ℤ) (-1) (by omega)).symm.app (fiberObj M f))
  rw [isDerivedCompleteAt_iff_isIso]
  exact (Triangle.isZero₁_iff_isIso₂ _ hT).1 hz

/-! ### The derived completion at a single element -/

/-- The derived completion `K^∧` of `K` at `f`: the cone of `T(K, f) ⟶ K`. -/
def coneObj (K : 𝒟) (f : A) : 𝒟 :=
  (distinguished_cocone_triangle (fiberProj K f)).choose

/-- The completion map `K ⟶ K^∧`. -/
def coneπ (K : 𝒟) (f : A) : K ⟶ coneObj K f :=
  (distinguished_cocone_triangle (fiberProj K f)).choose_spec.choose

/-- The connecting map `K^∧ ⟶ T(K, f)⟦1⟧`. -/
def coneδ (K : 𝒟) (f : A) : coneObj K f ⟶ (fiberObj K f)⟦(1 : ℤ)⟧ :=
  (distinguished_cocone_triangle (fiberProj K f)).choose_spec.choose_spec.choose

omit [∀ (n : ℤ), Functor.Linear A (shiftFunctor 𝒟 n)] in
/-- The triangle `T(K, f) ⟶ K ⟶ K^∧ ⟶ T(K, f)⟦1⟧` is distinguished. -/
theorem cone_distinguished (K : 𝒟) (f : A) :
    Triangle.mk (fiberProj K f) (coneπ K f) (coneδ K f) ∈ distTriang 𝒟 :=
  (distinguished_cocone_triangle (fiberProj K f)).choose_spec.choose_spec.choose_spec

omit [∀ (n : ℤ), Functor.Linear A (shiftFunctor 𝒟 n)] in
/-- The composite `T(K, f) ⟶ K ⟶ K^∧` is zero. -/
theorem fiberProj_comp_coneπ (K : 𝒟) (f : A) : fiberProj K f ≫ coneπ K f = 0 :=
  comp_distTriang_mor_zero₁₂ _ (cone_distinguished K f)

omit [∀ (n : ℤ), Functor.Linear A (shiftFunctor 𝒟 n)] in
/-- The composite of `coneδ K f` and the shift of `fiberProj K f` is zero. -/
theorem coneδ_comp (K : 𝒟) (f : A) : coneδ K f ≫ (fiberProj K f)⟦(1 : ℤ)⟧' = 0 :=
  comp_distTriang_mor_zero₃₁ _ (cone_distinguished K f)

/-- **The derived completion of `K` at `f` is derived complete at `f`.** -/
theorem isDerivedCompleteAt_coneObj (K : 𝒟) (f : A) : IsDerivedCompleteAt (coneObj K f) f := by
  rw [isDerivedCompleteAt_iff_forall_eq_zero]
  intro N _ c
  have hc : c ≫ coneδ K f = 0 := by
    refine eq_zero_of_comp_shift_eq_zero (fiberProj K f) (fun x hx => ?_) _ ?_
    · have := isIso_smul_shift (A := A) (N := N) (f := f) (-1 : ℤ)
      exact fiber_hom_ext K x hx
    · rw [Category.assoc, coneδ_comp, comp_zero]
  obtain ⟨y, hy⟩ := coyoneda_exact₃' (cone_distinguished K f) c hc
  obtain ⟨x, hx⟩ := exists_fiber_lift (f := f) (N := N) K y
  rw [hy, ← hx, Category.assoc, fiberProj_comp_coneπ, comp_zero]

/-- **The universal property of the derived completion at `f`.** For `M` derived complete at
`f`, precomposition with `K ⟶ K^∧` is a bijection `(K^∧ ⟶ M) ≃ (K ⟶ M)`. -/
theorem bijective_precomp_coneπ (K : 𝒟) (f : A) {M : 𝒟} (hM : IsDerivedCompleteAt M f) :
    Function.Bijective fun g : coneObj K f ⟶ M => coneπ K f ≫ g := by
  have hC := cone_distinguished K f
  have := isIso_smul_fiber K f
  refine ⟨fun g g' hgg' => ?_, fun g => ?_⟩
  · rw [← sub_eq_zero]
    have h0 : coneπ K f ≫ (g - g') = 0 := by
      rw [Preadditive.comp_sub, sub_eq_zero.2 hgg']
    obtain ⟨b, hb⟩ : ∃ v : (fiberObj K f)⟦(1 : ℤ)⟧ ⟶ M, g - g' = coneδ K f ≫ v :=
      CategoryTheory.Pretriangulated.Triangle.yoneda_exact₃ _ hC _ h0
    have := isIso_smul_shift (A := A) (N := fiberObj K f) (f := f) (1 : ℤ)
    rw [hb, hM.eq_zero_of_isIso_smul b, comp_zero]
  · obtain ⟨a, ha⟩ := CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂ _ hC g
      (hM.eq_zero_of_isIso_smul (fiberProj K f ≫ g))
    exact ⟨a, ha.symm⟩

/-- **Derived completion at `f` preserves derived completeness at every other scalar.** -/
theorem isDerivedCompleteAt_coneObj_of_isDerivedCompleteAt (K : 𝒟) (f : A) {b : A}
    (hK : IsDerivedCompleteAt K b) : IsDerivedCompleteAt (coneObj K f) b := by
  rw [isDerivedCompleteAt_iff_forall_eq_zero]
  intro N _ c
  have hP : IsDerivedCompleteAt (∏ᶜ fun _ : ℕ => K) b := isDerivedCompleteAt_pi fun _ => hK
  have hw : ∀ (N' : 𝒟) [IsIso (b • 𝟙 N')] (w : N' ⟶ (fiberObj K f)⟦(1 : ℤ)⟧), w = 0 := by
    intro N' _ w
    have hw3 : w ≫ (fiberι K f)⟦(1 : ℤ)⟧' = 0 :=
      eq_zero_of_shift_neg_one (fun x => by
        have := isIso_smul_shift (A := A) (N := N') (f := b) (-1 : ℤ)
        exact hP.eq_zero_of_isIso_smul x) _
    obtain ⟨y, hy⟩ := coyoneda_exact₁' (fiber_distinguished K f) w hw3
    rw [hy, hP.eq_zero_of_isIso_smul y, zero_comp]
  obtain ⟨y, hy⟩ := coyoneda_exact₃' (cone_distinguished K f) c (hw N _)
  rw [hy, hK.eq_zero_of_isIso_smul y, zero_comp]

/-! ### Derived completion along a finite family -/

/-- **Derived completion along a finite list of scalars.** For every `K` there is a map
`η : K ⟶ R` with `R` derived complete at every member of the list, universal among maps to such
objects, and with `R` derived complete at every scalar at which `K` is. -/
theorem exists_reflection_list (l : List A) (K : 𝒟) :
    ∃ (R : 𝒟) (η : K ⟶ R), (∀ a ∈ l, IsDerivedCompleteAt R a) ∧
      (∀ M : 𝒟, (∀ a ∈ l, IsDerivedCompleteAt M a) →
        Function.Bijective fun g : R ⟶ M => η ≫ g) ∧
      (∀ b : A, IsDerivedCompleteAt K b → IsDerivedCompleteAt R b) := by
  induction l with
  | nil =>
    refine ⟨K, 𝟙 K, by simp, fun M _ => ?_, fun _ h => h⟩
    have : (fun g : K ⟶ M => 𝟙 K ≫ g) = id := funext fun g => Category.id_comp g
    rw [this]
    exact Function.bijective_id
  | cons a l ih =>
    obtain ⟨R, η, hR, huniv, hpres⟩ := ih
    refine ⟨coneObj R a, η ≫ coneπ R a, ?_, ?_,
      fun b hb => isDerivedCompleteAt_coneObj_of_isDerivedCompleteAt R a (hpres b hb)⟩
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact isDerivedCompleteAt_coneObj R c
      · exact isDerivedCompleteAt_coneObj_of_isDerivedCompleteAt R a (hR c hc)
    · intro M hM
      have h1 := bijective_precomp_coneπ R a (hM a List.mem_cons_self)
      have h2 := huniv M fun c hc => hM c (List.mem_cons_of_mem a hc)
      have : (fun g : coneObj R a ⟶ M => (η ≫ coneπ R a) ≫ g) =
          (fun g : R ⟶ M => η ≫ g) ∘ fun g => coneπ R a ≫ g :=
        funext fun g => Category.assoc _ _ _
      rw [this]
      exact h2.comp h1

/-- **Derived completion along a finitely generated ideal exists.** For every `K` there is a map
`η : K ⟶ R` to a derived `I`-complete object, universal among maps to derived `I`-complete
objects. -/
theorem exists_reflection (I : Ideal A) (hI : I.FG) (K : 𝒟) :
    ∃ (R : 𝒟) (η : K ⟶ R), IsDerivedComplete I R ∧
      ∀ M : 𝒟, IsDerivedComplete I M → Function.Bijective fun g : R ⟶ M => η ≫ g := by
  obtain ⟨s, rfl⟩ := hI
  obtain ⟨R, η, hR, huniv, -⟩ := exists_reflection_list s.toList K
  exact ⟨R, η, (isDerivedComplete_span_iff _ R).2 fun a ha => hR a (by simpa using ha),
    fun M hM => huniv M fun a ha => ((isDerivedComplete_span_iff _ M).1 hM) a (by simpa using ha)⟩

/-- **The inclusion of the derived `I`-complete objects has a left adjoint** for a finitely
generated ideal `I`: derived completion (Stacks 099F, 091V). -/
theorem isRightAdjoint_ι_isDerivedComplete (I : Ideal A) (hI : I.FG) :
    (ObjectProperty.ι (IsDerivedComplete I : ObjectProperty 𝒟)).IsRightAdjoint := by
  choose R η hR huniv using exists_reflection (𝒟 := 𝒟) I hI
  let P : ObjectProperty 𝒟 := IsDerivedComplete I
  let e : ∀ (K : 𝒟) (M : P.FullSubcategory),
      ((⟨R K, hR K⟩ : P.FullSubcategory) ⟶ M) ≃ (K ⟶ P.ι.obj M) := fun K M =>
    P.fullyFaithfulι.homEquiv.trans (Equiv.ofBijective _ (huniv K M.obj M.property))
  have he : ∀ K M M' (g : M ⟶ M') h, e K M' (h ≫ g) = e K M h ≫ P.ι.map g := by
    intro K M M' g h
    simp only [e, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply, Functor.map_comp,
      Equiv.ofBijective_apply, Category.assoc]
  exact (Adjunction.adjunctionOfEquivLeft e he).isRightAdjoint

end Triangulated

end DerivedCompletionReflection
