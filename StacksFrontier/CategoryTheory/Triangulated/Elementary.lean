module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.CategoryTheory.Idempotents.Countable
public import StacksFrontier.CategoryTheory.Triangulated.Functor

/-!
# Elementary results on triangulated categories

This file collects the elementary consequences of the axioms of a pre-triangulated category:
what a distinguished triangle on a given morphism is determined by, when a morphism of
triangles is unique, when a triangle splits, which morphisms have kernels and cokernels, how
distinguished triangles interact with products and coproducts, and the two constructions —
the nine diagram and the long exact sequence of a `δ`-functor — that a triangulated category
and a homological functor produce out of them.

Throughout, `C` (or `D`, `𝒟`) is a pre-triangulated category: an additive category with an
additive shift by `ℤ` and a class `distTriang C` of distinguished triangles satisfying the
axioms TR1, TR2 and TR3. The octahedron axiom TR4, `CategoryTheory.IsTriangulated`, is assumed
only where it is used, namely for the nine diagram.

## Main results

* `CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism₂_idempotent`: a
  commutative square between the morphism `mor₃` of a distinguished triangle and itself, with
  both vertical maps idempotent, extends to an *idempotent* endomorphism of that triangle.
* `CategoryTheory.Pretriangulated.isIso_biprod_desc_of_distTriang`: for a distinguished
  triangle `T` and any right inverse `s` of `T.mor₂`, the map `biprod.desc T.mor₁ s` is an
  isomorphism, so `s` splits the triangle.
* `CategoryTheory.Pretriangulated.isIdempotentComplete_of_hasCountableProducts_or_coproducts`:
  a pre-triangulated category with countable powers of every object is Karoubian, and so is
  one with countable copowers.
* `shiftFunctor_preservesProductsCoproducts_and_productCoproductTriangle_distinguished`, in the
  `CategoryTheory.Pretriangulated` namespace: the shift preserves products and coproducts, and a
  product or coproduct of distinguished triangles is distinguished.
* `CategoryTheory.Pretriangulated.Triangle.hom_ext_of_hom₁_eq_of_hom₃_eq`: a morphism of
  distinguished triangles is determined by its two outer components, under any one of five
  `Hom`-vanishing conditions.
* `CategoryTheory.Triangulated.exists_nine_diagram`: a commutative square in a triangulated
  category extends to a `4 × 4` diagram whose rows and columns are distinguished triangles,
  all of whose squares commute except the lower right one, which anticommutes.
* Mathlib's `CategoryTheory.Functor.map_distinguished_iff`: a fully faithful exact
  functor of pre-triangulated categories reflects distinguished triangles (Stacks 05SQ).
* `CategoryTheory.Functor.DeltaFunctorStructure.isCohomologicalDeltaFunctor_comp_shift`: a
  homological functor composed with a `δ`-functor is a cohomological `δ`-functor.
* `comp_middle_zero_of_endomorphisms`: if `(0, b, 0)` and `(0, b', 0)` are endomorphisms of a
  distinguished triangle, then `b ∘ b' = 0`.
* `productTriangle_distinguished_iff`: the direct sum of two triangles is distinguished if and
  only if both summands are.
* `hasKernel_iff_hasCokernel_iff_split`: a morphism has a kernel if and only if it has a
  cokernel, if and only if it is isomorphic to `biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q`.

## References

* [Stacks, Tag 014B](https://stacks.math.columbia.edu/tag/014B)
* [Stacks, Tag 05QP](https://stacks.math.columbia.edu/tag/05QP)
* [Stacks, Tag 05QQ](https://stacks.math.columbia.edu/tag/05QQ)
* [Stacks, Tag 05QR](https://stacks.math.columbia.edu/tag/05QR)
* [Stacks, Tag 05QS](https://stacks.math.columbia.edu/tag/05QS)
* [Stacks, Tag 05QT](https://stacks.math.columbia.edu/tag/05QT)
* [Stacks, Tag 05QU](https://stacks.math.columbia.edu/tag/05QU)
* [Stacks, Tag 05QW](https://stacks.math.columbia.edu/tag/05QW)
* [Stacks, Tag 05R0](https://stacks.math.columbia.edu/tag/05R0)
* [Stacks, Tag 05SQ](https://stacks.math.columbia.edu/tag/05SQ)
* [Stacks, Tag 05SR](https://stacks.math.columbia.edu/tag/05SR)
* [Stacks, Tag 0CRG](https://stacks.math.columbia.edu/tag/0CRG)
* [Stacks, Tag 0FWZ](https://stacks.math.columbia.edu/tag/0FWZ)
-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Category Limits Preadditive Pretriangulated

add_to_stacks 05SQ CategoryTheory.Functor.map_distinguished_iff

namespace CategoryTheory.Pretriangulated

/-! ### Uniqueness of the cone on a morphism -/

add_to_stacks 014B "existence of a distinguished triangle on a morphism"
  CategoryTheory.Pretriangulated.distinguished_cocone_triangle
add_to_stacks 014B "uniqueness up to a (nonunique) isomorphism of triangles"
  CategoryTheory.Pretriangulated.exists_iso_of_arrow_iso

/-! ### Idempotent endomorphisms of a distinguished triangle -/

section Idempotent

/-- The idempotent correction of a ring element whose error term `x * x - x`
squares to zero: `1 - (1 - x * x) * (1 - x * x)` is idempotent. -/
private lemma isIdempotentElem_one_sub_one_sub_mul_self_mul_self {R : Type*} [Ring R] {x : R}
    (hx : (x * x - x) * (x * x - x) = 0) :
    IsIdempotentElem (1 - (1 - x * x) * (1 - x * x)) := by
  have h : (x - x ^ 2) ^ 2 = 0 := by
    rw [show x - x ^ 2 = -(x * x - x) from by rw [pow_two]; abel, neg_sq]
    simpa [pow_two] using hx
  simpa [pow_two] using isIdempotentElem_one_sub_one_sub_pow_pow x 2 h

section

variable {C : Type u} [Category.{v} C]

/-- If `f` intertwines an idempotent `a` with `b`, then post-composition with `b`
fixes `f ≫ b`. -/
private lemma comp_comp_self {X Y : C} {f : X ⟶ Y} {a : X ⟶ X} {b : Y ⟶ Y}
    (hf : f ≫ b = a ≫ f) (ha : a ≫ a = a) : (f ≫ b) ≫ b = f ≫ b := by
  rw [hf, Category.assoc, hf, ← Category.assoc, ha]

/-- If `g` intertwines `b` with an idempotent `c`, then pre-composition with `b`
fixes `b ≫ g`. -/
private lemma self_comp_comp {Y Z : C} {g : Y ⟶ Z} {b : Y ⟶ Y} {c : Z ⟶ Z}
    (hg : g ≫ c = b ≫ g) (hc : c ≫ c = c) : b ≫ b ≫ g = b ≫ g := by
  rw [← hg, ← Category.assoc, ← hg, Category.assoc, hc]

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Let `a`, `b`, `c` be endomorphisms of `X`, `Y`, `Z` with `a` and `c` idempotent,
intertwined by `f : X ⟶ Y` and `g : Y ⟶ Z` in the sense that `f ≫ b = a ≫ f` and
`g ≫ c = b ≫ g`. If the error term `b ≫ b - b` of `b` squares to zero, then there is an
*idempotent* `q` satisfying the same two relations. -/
private lemma exists_comp_self_eq_self_of_error_comp_self_eq_zero {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) {a : X ⟶ X} {b : Y ⟶ Y} {c : Z ⟶ Z} (hf : f ≫ b = a ≫ f)
    (hg : g ≫ c = b ≫ g) (ha : a ≫ a = a) (hc : c ≫ c = c)
    (he : (b ≫ b - b) ≫ (b ≫ b - b) = 0) :
    ∃ q : Y ⟶ Y, q ≫ q = q ∧ f ≫ q = a ≫ f ∧ g ≫ c = q ≫ g := by
  have hq : (𝟙 Y - (𝟙 Y - b ≫ b) ≫ (𝟙 Y - b ≫ b)) ≫ (𝟙 Y - (𝟙 Y - b ≫ b) ≫ (𝟙 Y - b ≫ b)) =
      𝟙 Y - (𝟙 Y - b ≫ b) ≫ (𝟙 Y - b ≫ b) := by
    have h := isIdempotentElem_one_sub_one_sub_mul_self_mul_self (R := End Y) (x := End.of b)
      (by ext; simpa using he)
    simpa using congr(($h).asHom)
  refine ⟨𝟙 Y - (𝟙 Y - b ≫ b) ≫ (𝟙 Y - b ≫ b), hq, ?_, ?_⟩
  · simp only [comp_sub, sub_comp, Category.comp_id, Category.id_comp, ← Category.assoc,
      comp_comp_self hf ha]
    rw [hf]
    abel
  · simp only [comp_sub, sub_comp, Category.comp_id, Category.id_comp, Category.assoc,
      self_comp_comp hg hc]
    rw [← hg]
    abel

end

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- If `e` and `e'` are endomorphisms of the middle
object of a distinguished triangle `T` such that `(0, e, 0)` and `(0, e', 0)` are
endomorphisms of `T`, i.e. `T.mor₁ ≫ e = 0` and `e' ≫ T.mor₂ = 0`, then
`e' ≫ e = 0`. -/
private lemma comp_eq_zero_of_mor₁_comp_eq_zero_of_comp_mor₂_eq_zero (T : Triangle C)
    (hT : T ∈ distTriang C) {e e' : T.obj₂ ⟶ T.obj₂} (he : T.mor₁ ≫ e = 0)
    (he' : e' ≫ T.mor₂ = 0) : e' ≫ e = 0 := by
  obtain ⟨β, hβ⟩ := Triangle.yoneda_exact₂ T hT e he
  obtain ⟨α, hα⟩ := Triangle.coyoneda_exact₂ T hT e' he'
  rw [hα, hβ, Category.assoc, ← Category.assoc T.mor₁,
    comp_distTriang_mor_zero₁₂ T hT, zero_comp, comp_zero]

/-- The error term of an endomorphism `(a, b, c)` of a distinguished triangle
whose outer components are idempotent squares to zero. -/
private lemma error_comp_self_eq_zero (T : Triangle C) (hT : T ∈ distTriang C)
    {a : T.obj₁ ⟶ T.obj₁} {b : T.obj₂ ⟶ T.obj₂} {c : T.obj₃ ⟶ T.obj₃}
    (hb₁ : T.mor₁ ≫ b = a ≫ T.mor₁) (hb₂ : T.mor₂ ≫ c = b ≫ T.mor₂) (ha : a ≫ a = a)
    (hc : c ≫ c = c) : (b ≫ b - b) ≫ (b ≫ b - b) = 0 := by
  refine comp_eq_zero_of_mor₁_comp_eq_zero_of_comp_mor₂_eq_zero T hT ?_ ?_
  · simp only [comp_sub, ← Category.assoc, comp_comp_self hb₁ ha, sub_self]
  · simp only [sub_comp, Category.assoc, self_comp_comp hb₂ hc, sub_self]

/-- Let `T = (X, Y, Z, f, g, h)` be a distinguished triangle in
a pre-triangulated category, and let `a : X ⟶ X`, `c : Z ⟶ Z` be idempotents
such that `h ≫ a⟦1⟧' = c ≫ h`. Then `(a, c)` extends to an *idempotent*
endomorphism `φ : T ⟶ T` of the triangle, i.e. there is `b : Y ⟶ Y` with
`b ≫ b = b` making `(a, b, c)` an endomorphism of `T`. -/
@[stacks 05QQ]
theorem complete_distinguished_triangle_morphism₂_idempotent (T : Triangle C)
    (hT : T ∈ distTriang C) (a : T.obj₁ ⟶ T.obj₁) (c : T.obj₃ ⟶ T.obj₃)
    (comm : T.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T.mor₃) (ha : a ≫ a = a) (hc : c ≫ c = c) :
    ∃ φ : T ⟶ T, φ ≫ φ = φ ∧ φ.hom₁ = a ∧ φ.hom₃ = c := by
  obtain ⟨b, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism₂ T T hT hT a c comm
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_comp_self_eq_self_of_error_comp_self_eq_zero
    T.mor₁ T.mor₂ hb₁ hb₂ ha hc (error_comp_self_eq_zero T hT hb₁ hb₂ ha hc)
  refine ⟨⟨a, q, c, hq₁, hq₂, comm⟩, ?_, rfl, rfl⟩
  ext
  · simpa using ha
  · simpa using hq
  · simpa using hc

end

end Idempotent

/-! ### A morphism is an isomorphism iff its cone vanishes -/

add_to_stacks 05QR "(1) ⟺ (2)"
  CategoryTheory.Pretriangulated.Triangle.distinguished_iff_of_isZero₃
add_to_stacks 05QR "(1) ⟺ (3)"
  CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁
add_to_stacks 05QR "(1) ⟹ (3)"
  CategoryTheory.Pretriangulated.Triangle.isZero₃_of_isIso₁

/-! ### A right inverse splits a distinguished triangle -/

section Split

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- Let `T = (X, Y, Z, f, g, h)` be a distinguished triangle. A morphism `φ : X ⊕ Z ⟶ Y`
restricting to `f` on `X` and satisfying `φ ≫ g = pr₂` is an isomorphism. -/
private lemma isIso_of_comp_mor₂_eq_snd (T : Triangle C) (hT : T ∈ distTriang C)
    (φ : T.obj₁ ⊞ T.obj₃ ⟶ T.obj₂) (h₁ : biprod.inl ≫ φ = T.mor₁)
    (h₂ : φ ≫ T.mor₂ = biprod.snd) : IsIso φ :=
  have : IsSplitEpi T.mor₂ := IsSplitEpi.mk' ⟨biprod.inr ≫ φ, by simp [h₂]⟩
  isIso₂_of_isIso₁₃
    (Triangle.homMk (binaryBiproductTriangle T.obj₁ T.obj₃) T (𝟙 _) φ (𝟙 _)
      (by simpa [binaryBiproductTriangle] using h₁)
      (by simp [binaryBiproductTriangle, h₂])
      (by simp [binaryBiproductTriangle, T.mor₃_eq_zero_of_epi₂ hT inferInstance]))
    (binaryBiproductTriangle_distinguished _ _) hT (IsIso.id _) (IsIso.id _)

/-- Let `T = (X, Y, Z, f, g, h)` be a distinguished triangle in a
pre-triangulated category. For any right inverse `s : Z ⟶ Y` of `g`, the map
`f ⊕ s : X ⊕ Z ⟶ Y` is an isomorphism. -/
@[stacks 05QT]
theorem isIso_biprod_desc_of_distTriang (T : Triangle C) (hT : T ∈ distTriang C)
    (s : T.obj₃ ⟶ T.obj₂) (hs : s ≫ T.mor₂ = 𝟙 T.obj₃) :
    IsIso (biprod.desc T.mor₁ s) :=
  isIso_of_comp_mor₂_eq_snd T hT _ (by simp)
    (by ext <;> simp [hs, comp_distTriang_mor_zero₁₂ _ hT])

end Split

/-! ### Countable (co)products make a pre-triangulated category Karoubian -/

section Karoubian

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- In a pre-triangulated category a split epimorphism has a kernel. -/
private lemma hasKernel_of_isSplitEpi {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] : HasKernel f := by
  obtain ⟨W, i, h, hT⟩ := distinguished_cocone_triangle₁ f
  have hif : i ≫ f = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have hh : h = 0 := by simpa using section_ f ≫= comp_distTriang_mor_zero₂₃ _ hT
  have : Mono i := (Triangle.mor₃_eq_zero_iff_mono₁ _ hT).1 hh
  have fac : ∀ {W' : C} (g' : W' ⟶ X), g' ≫ f = 0 → ∃ m : W' ⟶ W, g' = m ≫ i :=
    fun g' hg' => Triangle.coyoneda_exact₂ _ hT g' hg'
  exact HasLimit.mk ⟨KernelFork.ofι i hif, KernelFork.IsLimit.ofι i hif
    (fun {_} g' hg' => (fac g' hg').choose)
    (fun {_} g' hg' => (fac g' hg').choose_spec.symm)
    (fun {_} g' hg' m hm => (cancel_mono i).1 (by rw [hm]; exact (fac g' hg').choose_spec))⟩

/-- In a pre-triangulated category a split monomorphism has a cokernel. -/
private lemma hasCokernel_of_isSplitMono {X Y : C} (f : X ⟶ Y) [IsSplitMono f] :
    HasCokernel f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  have hfg : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have hh : h = 0 := by
    have h₀ : h ≫ (CategoryTheory.shiftFunctor C 1).map f = 0 :=
      comp_distTriang_mor_zero₃₁ _ hT
    calc h = h ≫ (CategoryTheory.shiftFunctor C 1).map (f ≫ retraction f) := by simp
      _ = 0 := by rw [Functor.map_comp, ← Category.assoc, h₀, zero_comp]
  have : Epi g := (Triangle.mor₃_eq_zero_iff_epi₂ _ hT).1 hh
  have fac : ∀ {Z' : C} (g' : Y ⟶ Z'), f ≫ g' = 0 → ∃ m : Z ⟶ Z', g' = g ≫ m :=
    fun g' hg' => Triangle.yoneda_exact₂ _ hT g' hg'
  exact HasColimit.mk ⟨CokernelCofork.ofπ g hfg, CokernelCofork.IsColimit.ofπ g hfg
    (fun {_} g' hg' => (fac g' hg').choose)
    (fun {_} g' hg' => (fac g' hg').choose_spec.symm)
    (fun {_} g' hg' m hm => (cancel_epi g).1 (by rw [hm]; exact (fac g' hg').choose_spec))⟩

end

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- A pre-triangulated category in which every object has a countable power
`∏_{n : ℕ} Z` is Karoubian, i.e. idempotent complete; and so is one in which every object has a
countable copower `∐_{n : ℕ} Z`. In particular a pre-triangulated category with countable
products, or with countable coproducts, is Karoubian. -/
@[stacks 05QW]
theorem isIdempotentComplete_of_hasCountableProducts_or_coproducts :
    (∀ [∀ Z : C, HasProduct fun _ : ℕ => Z], IsIdempotentComplete C) ∧
      (∀ [∀ Z : C, HasCoproduct fun _ : ℕ => Z], IsIdempotentComplete C) := by
  refine ⟨?_, ?_⟩
  · intro _
    exact isIdempotentComplete_of_hasCountableProducts fun f _ => hasKernel_of_isSplitEpi f
  · intro _
    exact isIdempotentComplete_of_hasCountableCoproducts fun f _ => hasCokernel_of_isSplitMono f

end Karoubian

/-! ### Products and coproducts of distinguished triangles -/

section Products

section

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]

/-- The shifted coprojections exhibit `(∐ X)⟦n⟧` as a coproduct of the `(X i)⟦n⟧`. -/
private noncomputable def isColimitCofanShift {I : Type w} (X : I → C) [HasCoproduct X] (n : ℤ) :
    IsColimit (Cofan.mk ((∐ X)⟦n⟧) fun i => (Sigma.ι X i)⟦n⟧') :=
  isColimitOfHasCoproductOfPreservesColimit (CategoryTheory.shiftFunctor C n) X

/-- A family of morphisms out of the shifted summands descends to `(∐ X)⟦n⟧`. -/
private lemma exists_shift_desc {I : Type w} (X : I → C) [HasCoproduct X] (n : ℤ) {A : C}
    (β : ∀ i, (X i)⟦n⟧ ⟶ A) : ∃ d : (∐ X)⟦n⟧ ⟶ A, ∀ i, (Sigma.ι X i)⟦n⟧' ≫ d = β i :=
  ⟨Cofan.IsColimit.desc (isColimitCofanShift X n) β,
    fun i => Cofan.IsColimit.fac (isColimitCofanShift X n) β i⟩

/-- Two morphisms out of `(∐ X)⟦n⟧` agreeing on the shifted coprojections are equal. -/
private lemma shift_sigma_hom_ext {I : Type w} (X : I → C) [HasCoproduct X] (n : ℤ) {A : C}
    {u v : (∐ X)⟦n⟧ ⟶ A} (h : ∀ i, (Sigma.ι X i)⟦n⟧' ≫ u = (Sigma.ι X i)⟦n⟧' ≫ v) : u = v :=
  Cofan.IsColimit.hom_ext (isColimitCofanShift X n) u v h

end

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- A morphism `f : X⟦1⟧ ⟶ A` out of the shifted first object of a distinguished triangle
`(X, Y, Z, f₁, g, h)` with `h ≫ f = 0` factors through `f₁⟦1⟧'`. -/
private lemma yoneda_exact₁' (T : Triangle C) (hT : T ∈ distTriang C) {A : C}
    (f : T.obj₁⟦(1 : ℤ)⟧ ⟶ A) (hf : T.mor₃ ≫ f = 0) :
    ∃ g : T.obj₂⟦(1 : ℤ)⟧ ⟶ A, f = T.mor₁⟦(1 : ℤ)⟧' ≫ g := by
  obtain ⟨g₀, hg₀⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ hT) f hf
  obtain ⟨g, hg⟩ : ∃ g : T.obj₂⟦(1 : ℤ)⟧ ⟶ A, f = (-(T.mor₁⟦(1 : ℤ)⟧')) ≫ g := ⟨g₀, hg₀⟩
  exact ⟨-g, by rw [hg, Preadditive.neg_comp, Preadditive.comp_neg]⟩

/-- A coproduct of distinguished triangles is distinguished. -/
private lemma coproductTriangle_distinguished {I : Type w} (T : I → Triangle C)
    (hT : ∀ i, T i ∈ distTriang C)
    [HasCoproduct fun i => (T i).obj₁] [HasCoproduct fun i => (T i).obj₂]
    [HasCoproduct fun i => (T i).obj₃] :
    Triangle.mk (Limits.Sigma.map fun i => (T i).mor₁) (Limits.Sigma.map fun i => (T i).mor₂)
        (Limits.Sigma.desc fun i =>
          (T i).mor₃ ≫ (Sigma.ι (fun i => (T i).obj₁) i)⟦(1 : ℤ)⟧') ∈ distTriang C := by
  set f₁ : (∐ fun i => (T i).obj₁) ⟶ (∐ fun i => (T i).obj₂) :=
    Limits.Sigma.map fun i => (T i).mor₁ with hf₁
  obtain ⟨Z, f₂, f₃, hT'⟩ := distinguished_cocone_triangle f₁
  let T' : Triangle C := Triangle.mk f₁ f₂ f₃
  change T' ∈ distTriang C at hT'
  let Φ : ∀ i, T i ⟶ T' := fun i => completeDistinguishedTriangleMorphism (T i) T' (hT i) hT'
    (Sigma.ι (fun i => (T i).obj₁) i) (Sigma.ι (fun i => (T i).obj₂) i) (by simp [T', hf₁])
  have hcomm₂ : ∀ i, (T i).mor₂ ≫ (Φ i).hom₃ = Sigma.ι (fun i => (T i).obj₂) i ≫ f₂ :=
    fun i => (Φ i).comm₂
  have hcomm₃ : ∀ i, (T i).mor₃ ≫ (Sigma.ι (fun i => (T i).obj₁) i)⟦(1 : ℤ)⟧'
      = (Φ i).hom₃ ≫ f₃ := fun i => (Φ i).comm₃
  set ψ : (∐ fun i => (T i).obj₃) ⟶ Z := Limits.Sigma.desc fun i => (Φ i).hom₃ with hψ
  have hι : ∀ i, Sigma.ι (fun i => (T i).obj₃) i ≫ ψ = (Φ i).hom₃ := fun i => by simp [hψ]
  have hψ₂ : (Limits.Sigma.map fun i => (T i).mor₂) ≫ ψ = f₂ := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, Sigma.ι_map, Category.assoc, hι, hcomm₂]
  have hψ₃ : (Limits.Sigma.desc fun i =>
      (T i).mor₃ ≫ (Sigma.ι (fun i => (T i).obj₁) i)⟦(1 : ℤ)⟧') = ψ ≫ f₃ := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Sigma.ι_desc, ← Category.assoc, hι, hcomm₃]
  set S : Triangle C := Triangle.mk (Limits.Sigma.map fun i => (T i).mor₁)
    (Limits.Sigma.map fun i => (T i).mor₂)
    (Limits.Sigma.desc fun i =>
      (T i).mor₃ ≫ (Sigma.ι (fun i => (T i).obj₁) i)⟦(1 : ℤ)⟧') with hS
  let Ψ : S ⟶ T' := Triangle.homMk S T' (𝟙 _) (𝟙 _) ψ (by simp [S, T', hf₁])
    (by simpa [S, T'] using hψ₂) (by simpa [S, T'] using hψ₃)
  suffices h : IsIso ψ by
    have : IsIso Ψ := Triangle.isIso_of_isIsos Ψ (inferInstanceAs (IsIso (𝟙 S.obj₁)))
      (inferInstanceAs (IsIso (𝟙 S.obj₂))) h
    exact isomorphic_distinguished _ hT' _ (asIso Ψ)
  refine isIso_of_coyoneda_map_bijective ψ (fun A => ⟨?_, ?_⟩)
  · suffices hepi : Epi ψ by
      intro a₁ a₂ ha
      simpa only [← cancel_epi ψ] using ha
    rw [Preadditive.epi_iff_cancel_zero]
    intro B u hu
    have hu₂ : f₂ ≫ u = 0 := by rw [← hψ₂, Category.assoc, hu, comp_zero]
    obtain ⟨g, hg₀⟩ := Triangle.yoneda_exact₃ T' hT' u hu₂
    have hg : u = f₃ ≫ g := hg₀
    have hg' : ∀ i, (T i).mor₃ ≫ ((Sigma.ι (fun i => (T i).obj₁) i)⟦(1 : ℤ)⟧' ≫ g) = 0 := by
      intro i
      rw [← Category.assoc, hcomm₃, Category.assoc, ← hg, ← hι, Category.assoc, hu, comp_zero]
    choose β hβ using fun i => yoneda_exact₁' (T i) (hT i) _ (hg' i)
    obtain ⟨d, hd⟩ := exists_shift_desc (fun i => (T i).obj₂) (1 : ℤ) β
    have hgd : g = f₁⟦(1 : ℤ)⟧' ≫ d := by
      refine shift_sigma_hom_ext (fun i => (T i).obj₁) (1 : ℤ) fun i => ?_
      have h₁ : (Sigma.ι (fun i => (T i).obj₁) i)⟦(1 : ℤ)⟧' ≫ f₁⟦(1 : ℤ)⟧'
          = (T i).mor₁⟦(1 : ℤ)⟧' ≫ (Sigma.ι (fun i => (T i).obj₂) i)⟦(1 : ℤ)⟧' := by
        rw [← Functor.map_comp, ← Functor.map_comp, hf₁, Sigma.ι_map]
      rw [hβ i, ← Category.assoc, h₁, Category.assoc, hd i]
    have hzero : f₃ ≫ f₁⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ T' hT'
    rw [hg, hgd, ← Category.assoc, hzero, zero_comp]
  · intro a
    have hz : f₁ ≫ (Limits.Sigma.map fun i => (T i).mor₂) = 0 := by
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [comp_zero, ← Category.assoc, hf₁, Sigma.ι_map, Category.assoc, Sigma.ι_map,
        ← Category.assoc, comp_distTriang_mor_zero₁₂ _ (hT i), zero_comp]
    have hz₂ : f₁ ≫ ((Limits.Sigma.map fun i => (T i).mor₂) ≫ a) = 0 := by
      rw [← Category.assoc, hz, zero_comp]
    obtain ⟨a'₀, ha'₀⟩ := Triangle.yoneda_exact₂ T' hT'
      ((Limits.Sigma.map fun i => (T i).mor₂) ≫ a) hz₂
    obtain ⟨a', ha'⟩ : ∃ a' : Z ⟶ A,
        (Limits.Sigma.map fun i => (T i).mor₂) ≫ a = f₂ ≫ a' := ⟨a'₀, ha'₀⟩
    have key : ∀ i, (T i).mor₂ ≫ (Sigma.ι (fun i => (T i).obj₃) i ≫ (a - ψ ≫ a')) = 0 := by
      intro i
      rw [← Category.assoc, ← Sigma.ι_map (fun i => (T i).mor₂) i, Category.assoc,
        Preadditive.comp_sub, ha', ← Category.assoc, hψ₂, sub_self, comp_zero]
    choose b hb using fun i => Triangle.yoneda_exact₃ (T i) (hT i) _ (key i)
    obtain ⟨e, he⟩ := exists_shift_desc (fun i => (T i).obj₁) (1 : ℤ) b
    refine ⟨a' + f₃ ≫ e, ?_⟩
    have hsub : a - ψ ≫ a' = (Limits.Sigma.desc fun i =>
        (T i).mor₃ ≫ (Sigma.ι (fun i => (T i).obj₁) i)⟦(1 : ℤ)⟧') ≫ e := by
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [← Category.assoc, Sigma.ι_desc, Category.assoc, he i]
      exact hb i
    change ψ ≫ (a' + f₃ ≫ e) = a
    rw [Preadditive.comp_add, ← Category.assoc, ← hψ₃, ← hsub]
    abel

/-- Let `C` be a pre-triangulated category and `I` an index type.
(1)(a) The shift functors preserve `I`-indexed products, i.e. if `∏ Xᵢ` exists then
`(∏ Xᵢ)⟦n⟧` together with the shifted projections is a product of the `Xᵢ⟦n⟧`;
(1)(b) dually, they preserve `I`-indexed coproducts.
(2)(a) If `Xᵢ → Yᵢ → Zᵢ → Xᵢ⟦1⟧` is a family of distinguished triangles whose products
exist, then `∏ Xᵢ → ∏ Yᵢ → ∏ Zᵢ → (∏ Xᵢ)⟦1⟧` is distinguished;
(2)(b) if their coproducts exist, then `∐ Xᵢ → ∐ Yᵢ → ∐ Zᵢ → (∐ Xᵢ)⟦1⟧` is distinguished. -/
@[stacks 0CRG]
theorem
    shiftFunctor_preservesProductsCoproducts_and_productCoproductTriangle_distinguished
    (I : Type w) :
    (∀ n : ℤ, PreservesLimitsOfShape (Discrete I) (CategoryTheory.shiftFunctor C n)) ∧
    (∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (CategoryTheory.shiftFunctor C n)) ∧
    (∀ T : I → Triangle C, (∀ i, T i ∈ distTriang C) →
      ∀ [HasProduct fun i => (T i).obj₁] [HasProduct fun i => (T i).obj₂]
        [HasProduct fun i => (T i).obj₃] [HasProduct fun i => (T i).obj₁⟦(1 : ℤ)⟧],
        productTriangle T ∈ distTriang C) ∧
    (∀ T : I → Triangle C, (∀ i, T i ∈ distTriang C) →
      ∀ [HasCoproduct fun i => (T i).obj₁] [HasCoproduct fun i => (T i).obj₂]
        [HasCoproduct fun i => (T i).obj₃],
        Triangle.mk (Limits.Sigma.map fun i => (T i).mor₁)
            (Limits.Sigma.map fun i => (T i).mor₂)
            (Limits.Sigma.desc fun i =>
              (T i).mor₃ ≫ (Limits.Sigma.ι (fun i => (T i).obj₁) i)⟦(1 : ℤ)⟧') ∈
          distTriang C) :=
  ⟨fun _ => inferInstance, fun _ => inferInstance,
    fun T hT => productTriangle_distinguished T hT,
    fun T hT => coproductTriangle_distinguished T hT⟩

end Products

/-! ### Uniqueness of a morphism of distinguished triangles -/

section HomExt

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- A morphism `b : A ⟶ Y'` into the second object of a distinguished triangle
`(X', Y', Z', f', g', h')` with `b ≫ g' = 0` vanishes as soon as `Hom(A, X') = 0`. -/
private lemma eq_zero_of_comp_mor₂_eq_zero {T' : Triangle C} (hT' : T' ∈ distTriang C)
    {A : C} (b : A ⟶ T'.obj₂) (hb : b ≫ T'.mor₂ = 0)
    (H : ∀ u : A ⟶ T'.obj₁, u = 0) : b = 0 := by
  obtain ⟨γ, rfl⟩ := Triangle.coyoneda_exact₂ T' hT' b hb
  rw [H γ, zero_comp]

/-- A morphism `b : Y ⟶ A` out of the second object of a distinguished triangle
`(X, Y, Z, f, g, h)` with `f ≫ b = 0` vanishes as soon as `Hom(Z, A) = 0`. -/
private lemma eq_zero_of_mor₁_comp_eq_zero {T : Triangle C} (hT : T ∈ distTriang C)
    {A : C} (b : T.obj₂ ⟶ A) (hb : T.mor₁ ≫ b = 0)
    (H : ∀ u : T.obj₃ ⟶ A, u = 0) : b = 0 := by
  obtain ⟨ε, rfl⟩ := Triangle.yoneda_exact₂ T hT b hb
  rw [H ε, comp_zero]

/-- Exactness of `Hom(-, A)` on a distinguished triangle `(X, Y, Z)`: if
`Hom(X, A) = 0` and `Hom(Z, A) = 0` then `Hom(Y, A) = 0`. -/
private lemma hom_from_obj₂_eq_zero {T : Triangle C} (hT : T ∈ distTriang C) {A : C}
    (h₁ : ∀ u : T.obj₁ ⟶ A, u = 0) (h₃ : ∀ u : T.obj₃ ⟶ A, u = 0) (u : T.obj₂ ⟶ A) :
    u = 0 :=
  eq_zero_of_mor₁_comp_eq_zero hT u (h₁ _) h₃

/-- Exactness of `Hom(A, -)` on a distinguished triangle `(X', Y', Z')`: if
`Hom(A, X') = 0` and `Hom(A, Z') = 0` then `Hom(A, Y') = 0`. -/
private lemma hom_to_obj₂_eq_zero {T' : Triangle C} (hT' : T' ∈ distTriang C) {A : C}
    (h₁ : ∀ u : A ⟶ T'.obj₁, u = 0) (h₃ : ∀ u : A ⟶ T'.obj₃, u = 0) (u : A ⟶ T'.obj₂) :
    u = 0 :=
  eq_zero_of_comp_mor₂_eq_zero hT' u (h₃ _) h₁

/-- Let `(X, Y, Z, f, g, h)` and `(X', Y', Z', f', g', h')` be distinguished triangles. If
`Hom(X[1], Z') = 0` and `Hom(Z, X') = 0`, the only `b : Y ⟶ Y'` with `f ≫ b = 0` and
`b ≫ g' = 0` is `b = 0`. -/
private lemma eq_zero_of_hom_shift_obj₁_obj₃_eq_zero {T T' : Triangle C}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) (b : T.obj₂ ⟶ T'.obj₂)
    (hb₁ : T.mor₁ ≫ b = 0) (hb₂ : b ≫ T'.mor₂ = 0)
    (H₁ : ∀ u : T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃, u = 0)
    (H₂ : ∀ u : T.obj₃ ⟶ T'.obj₁, u = 0) : b = 0 := by
  obtain ⟨ε, rfl⟩ := Triangle.yoneda_exact₂ T hT b hb₁
  have hε : ε ≫ T'.mor₂ = 0 := by
    obtain ⟨δ, hδ⟩ := Triangle.yoneda_exact₃ T hT (ε ≫ T'.mor₂) (by
      rw [← Category.assoc, hb₂])
    rw [hδ, H₁ δ, comp_zero]
  rw [eq_zero_of_comp_mor₂_eq_zero hT' ε hε H₂, comp_zero]

/-- Let `(X, Y, Z, f, g, h)` and `(X', Y', Z', f', g', h')` be distinguished triangles. A
morphism `b : Y ⟶ Y'` with `f ≫ b = 0` and `b ≫ g' = 0` vanishes as soon as one of the
five vanishing conditions of `Triangle.hom_ext_of_hom₁_eq_of_hom₃_eq` holds. -/
private lemma eq_zero_of_mor₁_comp_eq_zero_of_comp_mor₂_eq_zero {T T' : Triangle C}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) (b : T.obj₂ ⟶ T'.obj₂)
    (hb₁ : T.mor₁ ≫ b = 0) (hb₂ : b ≫ T'.mor₂ = 0)
    (H : (∀ u : T.obj₂ ⟶ T'.obj₁, u = 0) ∨
      (∀ u : T.obj₃ ⟶ T'.obj₂, u = 0) ∨
      ((∀ u : T.obj₁ ⟶ T'.obj₁, u = 0) ∧ ∀ u : T.obj₃ ⟶ T'.obj₁, u = 0) ∨
      ((∀ u : T.obj₃ ⟶ T'.obj₁, u = 0) ∧ ∀ u : T.obj₃ ⟶ T'.obj₃, u = 0) ∨
      ((∀ u : T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃, u = 0) ∧ ∀ u : T.obj₃ ⟶ T'.obj₁, u = 0)) :
    b = 0 := by
  obtain H | H | ⟨H, H'⟩ | ⟨H, H'⟩ | ⟨H, H'⟩ := H
  · exact eq_zero_of_comp_mor₂_eq_zero hT' b hb₂ H
  · exact eq_zero_of_mor₁_comp_eq_zero hT b hb₁ H
  · exact eq_zero_of_comp_mor₂_eq_zero hT' b hb₂ (hom_from_obj₂_eq_zero hT H H')
  · exact eq_zero_of_mor₁_comp_eq_zero hT b hb₁ (hom_to_obj₂_eq_zero hT' H H')
  · exact eq_zero_of_hom_shift_obj₁_obj₃_eq_zero hT hT' b hb₁ hb₂ H H'

/-- A morphism of distinguished triangles is determined by its outer two components, as
soon as one of the following five vanishing conditions holds:
`Hom(Y, X') = 0`, or `Hom(Z, Y') = 0`, or `Hom(X, X') = Hom(Z, X') = 0`, or
`Hom(Z, X') = Hom(Z, Z') = 0`, or `Hom(X[1], Z') = Hom(Z, X') = 0`. -/
@[stacks 0FWZ]
theorem Triangle.hom_ext_of_hom₁_eq_of_hom₃_eq {T T' : Triangle C}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) (φ ψ : T ⟶ T')
    (h₁ : φ.hom₁ = ψ.hom₁) (h₃ : φ.hom₃ = ψ.hom₃)
    (H : (∀ u : T.obj₂ ⟶ T'.obj₁, u = 0) ∨
      (∀ u : T.obj₃ ⟶ T'.obj₂, u = 0) ∨
      ((∀ u : T.obj₁ ⟶ T'.obj₁, u = 0) ∧ ∀ u : T.obj₃ ⟶ T'.obj₁, u = 0) ∨
      ((∀ u : T.obj₃ ⟶ T'.obj₁, u = 0) ∧ ∀ u : T.obj₃ ⟶ T'.obj₃, u = 0) ∨
      ((∀ u : T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃, u = 0) ∧ ∀ u : T.obj₃ ⟶ T'.obj₁, u = 0)) :
    φ = ψ := by
  have hb₁ : T.mor₁ ≫ (φ.hom₂ - ψ.hom₂) = 0 := by
    rw [comp_sub, φ.comm₁, ψ.comm₁, h₁, sub_self]
  have hb₂ : (φ.hom₂ - ψ.hom₂) ≫ T'.mor₂ = 0 := by
    rw [sub_comp, ← φ.comm₂, ← ψ.comm₂, h₃, sub_self]
  refine Triangle.hom_ext _ _ h₁ ?_ h₃
  rw [← sub_eq_zero]
  exact eq_zero_of_mor₁_comp_eq_zero_of_comp_mor₂_eq_zero hT hT' _ hb₁ hb₂ H

end HomExt

end CategoryTheory.Pretriangulated

/-! ### The nine diagram -/

namespace CategoryTheory.Triangulated

open Triangulated

section NineDiagram

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A triangle `(f, g, h)` whose rotation `(g, h, -f⟦1⟧')` is distinguished is
distinguished. -/
private lemma distTriang_of_rot {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧}
    (H : Triangle.mk g h (-(f⟦(1 : ℤ)⟧')) ∈ distTriang C) :
    Triangle.mk f g h ∈ distTriang C :=
  (Pretriangulated.rotate_distinguished_triangle _).mpr H

end NineDiagram

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- Let `u₁₂ : X₁ ⟶ X₂` and `u₂₃ : X₂ ⟶ X₃`, let `(u₁₂, v₁₂, w₁₂)` and `(u₁₂ ≫ u₂₃, v₁₃, w₁₃)` be
distinguished, and let the triangle on `u₂₃` be given as `(k, u₂₃, v₂₃)` with `k : Z ⟶ X₂`, that
is, with `u₂₃` in second position. Then there are `m₁ : Z₁₂ ⟶ Z₁₃` and `m₃ : Z₁₃ ⟶ Z⟦1⟧` such
that `(k ≫ v₁₂, m₁, m₃)` is distinguished — again with `Z` in first position — three of whose
faces commute as in `CategoryTheory.Triangulated.Octahedron` and whose fourth face
`w₁₃ ≫ u₁₂⟦1⟧' = -(m₃ ≫ k⟦1⟧')` anticommutes. -/
private lemma exists_octahedron_of_rot {X₁ X₂ X₃ Z Z₁₂ Z₁₃ : C}
    {u₁₂ : X₁ ⟶ X₂} {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧}
    (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C)
    {k : Z ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {v₂₃ : X₃ ⟶ Z⟦(1 : ℤ)⟧}
    (h₂₃ : Triangle.mk k u₂₃ v₂₃ ∈ distTriang C)
    {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧}
    (h₁₃ : Triangle.mk (u₁₂ ≫ u₂₃) v₁₃ w₁₃ ∈ distTriang C) :
    ∃ (m₁ : Z₁₂ ⟶ Z₁₃) (m₃ : Z₁₃ ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk (k ≫ v₁₂) m₁ m₃ ∈ distTriang C ∧
      v₁₂ ≫ m₁ = u₂₃ ≫ v₁₃ ∧ m₁ ≫ w₁₃ = w₁₂ ∧ v₁₃ ≫ m₃ = v₂₃ ∧
      w₁₃ ≫ u₁₂⟦(1 : ℤ)⟧' = -(m₃ ≫ k⟦(1 : ℤ)⟧') := by
  let o := someOctahedron (u₁₂ := u₁₂) (u₂₃ := u₂₃) rfl h₁₂ (rot_of_distTriang _ h₂₃) h₁₃
  exact ⟨o.m₁, o.m₃, distTriang_of_rot (by simpa using o.mem), o.comm₁, o.comm₂, o.comm₃,
    by simpa using o.comm₄⟩

/-- Let `C` be a triangulated category. Given a commutative square
`u₁ ≫ b₁ = a₁ ≫ v₁` and distinguished triangles `(u₁, u₂, u₃)`, `(v₁, v₂, v₃)` on its two
horizontal morphisms and `(a₁, a₂, a₃)`, `(b₁, b₂, b₃)` on its two vertical ones, there are an
object `Z''`, a third row `(w₁, w₂, w₃)` and a third column `(c₁, c₂, c₃)`, both distinguished
triangles, such that the resulting `4 × 4` diagram — whose fourth row and fourth column are the
first row and the first column shifted by `1` — has all its squares commutative, except the
lower right one, which anticommutes. -/
@[stacks 05R0]
theorem exists_nine_diagram {X Y Z X' Y' Z' X'' Y'' : C}
    {u₁ : X ⟶ Y} {u₂ : Y ⟶ Z} {u₃ : Z ⟶ X⟦(1 : ℤ)⟧}
    (hu : Triangle.mk u₁ u₂ u₃ ∈ distTriang C)
    {v₁ : X' ⟶ Y'} {v₂ : Y' ⟶ Z'} {v₃ : Z' ⟶ X'⟦(1 : ℤ)⟧}
    (hv : Triangle.mk v₁ v₂ v₃ ∈ distTriang C)
    {a₁ : X ⟶ X'} {a₂ : X' ⟶ X''} {a₃ : X'' ⟶ X⟦(1 : ℤ)⟧}
    (ha : Triangle.mk a₁ a₂ a₃ ∈ distTriang C)
    {b₁ : Y ⟶ Y'} {b₂ : Y' ⟶ Y''} {b₃ : Y'' ⟶ Y⟦(1 : ℤ)⟧}
    (hb : Triangle.mk b₁ b₂ b₃ ∈ distTriang C)
    (comm : u₁ ≫ b₁ = a₁ ≫ v₁) :
    ∃ (Z'' : C) (w₁ : X'' ⟶ Y'') (w₂ : Y'' ⟶ Z'') (w₃ : Z'' ⟶ X''⟦(1 : ℤ)⟧)
      (c₁ : Z ⟶ Z') (c₂ : Z' ⟶ Z'') (c₃ : Z'' ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk w₁ w₂ w₃ ∈ distTriang C ∧ Triangle.mk c₁ c₂ c₃ ∈ distTriang C ∧
      u₂ ≫ c₁ = b₁ ≫ v₂ ∧ u₃ ≫ a₁⟦(1 : ℤ)⟧' = c₁ ≫ v₃ ∧
      v₁ ≫ b₂ = a₂ ≫ w₁ ∧ v₂ ≫ c₂ = b₂ ≫ w₂ ∧ v₃ ≫ a₂⟦(1 : ℤ)⟧' = c₂ ≫ w₃ ∧
      w₁ ≫ b₃ = a₃ ≫ u₁⟦(1 : ℤ)⟧' ∧ w₂ ≫ c₃ = b₃ ≫ u₂⟦(1 : ℤ)⟧' ∧
      w₃ ≫ a₃⟦(1 : ℤ)⟧' = -(c₃ ≫ u₃⟦(1 : ℤ)⟧') := by
  obtain ⟨A, p, q, hA⟩ := distinguished_cocone_triangle (u₁ ≫ b₁)
  let o₁ := someOctahedron (u₁₂ := u₁) (u₂₃ := b₁) rfl hu hb hA
  let o₂ := someOctahedron (u₁₂ := a₁) (u₂₃ := v₁) comm.symm ha hv hA
  obtain ⟨Z'', w₂, w₃, hw⟩ := distinguished_cocone_triangle (o₂.m₁ ≫ o₁.m₃)
  obtain ⟨c₂, c₃, hc, hm₁, hm₂, hm₃, hm₄⟩ := exists_octahedron_of_rot o₂.mem o₁.mem hw
  refine ⟨Z'', o₂.m₁ ≫ o₁.m₃, w₂, w₃, o₁.m₁ ≫ o₂.m₃, c₂, c₃, hw, hc,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← assoc, o₁.comm₁, assoc, o₂.comm₃]
  · rw [assoc, ← o₂.comm₄, o₁.comm₂_assoc]
  · rw [o₂.comm₁_assoc, o₁.comm₃]
  · rw [← o₂.comm₃_assoc, hm₁, o₁.comm₃_assoc]
  · exact hm₂.symm
  · rw [assoc, ← o₁.comm₄, o₂.comm₂_assoc]
  · exact hm₃
  · rw [← o₂.comm₂, ← o₁.comm₂, Functor.map_comp, Functor.map_comp, ← assoc, hm₄]
    simp

end

end CategoryTheory.Triangulated

namespace CategoryTheory.Functor

/-! ### A homological functor composed with a `δ`-functor -/

namespace DeltaFunctorStructure

section Biproducts

variable {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]
  {ℬ : Type*} [Category ℬ] [Preadditive ℬ] [HasBinaryBiproducts ℬ] [Balanced ℬ]

/-- If `0 ⟶ F(X₁) ⟶ F(X₁ ⊞ X₂) ⟶ F(X₂)` is exact, then `F` preserves the biproduct
`X₁ ⊞ X₂`. -/
private lemma preservesBinaryBiproduct_of_exact_map_biprod (F : 𝒜 ⥤ ℬ)
    [F.PreservesZeroMorphisms] {X₁ X₂ : 𝒜}
    (ex : (ShortComplex.mk (F.map (biprod.inl : X₁ ⟶ X₁ ⊞ X₂))
      (F.map (biprod.snd : X₁ ⊞ X₂ ⟶ X₂))
      (by rw [← F.map_comp, biprod.inl_snd, F.map_zero])).Exact) :
    PreservesBinaryBiproduct X₁ X₂ F := by
  have : Mono (F.biprodComparison X₁ X₂) := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro Z f hf
    obtain ⟨g, rfl⟩ := ex.lift' f (by simpa using hf =≫ biprod.snd)
    rw [show g = 0 from by simpa [← F.map_comp] using hf =≫ biprod.fst, zero_comp]
  exact preservesBinaryBiproduct_of_mono_biprodComparison _

end Biproducts

section

open ZeroObject

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {ℬ : Type*} [Category ℬ] [Abelian ℬ]
  {𝒟 : Type*} [Category 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ] [Preadditive 𝒟]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] {G : 𝒜 ⥤ 𝒟}

/-- A `δ`-functor sends the zero object to a zero object. -/
private lemma isZero_obj_zero (h : DeltaFunctorStructure 𝒜 𝒟 G) :
    IsZero (G.obj (0 : 𝒜)) := by
  have hS : (ShortComplex.mk (𝟙 (0 : 𝒜)) (0 : (0 : 𝒜) ⟶ (0 : 𝒜)) (by simp)).ShortExact :=
    (ShortComplex.Splitting.ofIsIsoOfIsZero _ (by dsimp; infer_instance)
      (isZero_zero 𝒜)).shortExact
  refine Triangle.isZero₃_of_isIso₁ _ (h.distinguished hS) ?_
  dsimp
  rw [G.map_id]
  infer_instance

/-- The exactness of `H ⁿ(G(A)) ⟶ H ⁿ(G(B)) ⟶ H ⁿ(G(C))` in the middle, for a short exact
sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜`. -/
private lemma exact_comp_shift (h : DeltaFunctorStructure 𝒜 𝒟 G) (H : 𝒟 ⥤ ℬ)
    [H.IsHomological] [H.ShiftSequence ℤ] {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℤ) :
    (ShortComplex.mk ((G ⋙ H.shift n).map S.f) ((G ⋙ H.shift n).map S.g)
      (H.homologySequence_comp _ (h.distinguished hS) n)).Exact :=
  H.homologySequence_exact₂ _ (h.distinguished hS) n

/-- The functors `H ⁿ ∘ G` are additive. -/
private lemma additive_comp_shift (h : DeltaFunctorStructure 𝒜 𝒟 G) (H : 𝒟 ⥤ ℬ)
    [H.IsHomological] [H.ShiftSequence ℤ] (n : ℤ) : (G ⋙ H.shift n).Additive := by
  have : G.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_map_zero_object (isZero_obj_zero h).isoZero
  have : PreservesBinaryBiproducts (G ⋙ H.shift n) :=
    ⟨fun {X₁ X₂} => preservesBinaryBiproduct_of_exact_map_biprod _
      (exact_comp_shift h H (ShortComplex.Splitting.ofHasBinaryBiproduct X₁ X₂).shortExact n)⟩
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The morphism of distinguished triangles that a `δ`-functor attaches to a morphism `φ` of
short exact sequences, with components `G.map φ.τ₁`, `G.map φ.τ₂` and `G.map φ.τ₃`. -/
private def mapTriangleHom (h : DeltaFunctorStructure 𝒜 𝒟 G) {S S' : ShortComplex 𝒜}
    (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') :
    Triangle.mk (G.map S.f) (G.map S.g) (h.δ hS) ⟶
      Triangle.mk (G.map S'.f) (G.map S'.g) (h.δ hS') :=
  Triangle.homMk _ _ (G.map φ.τ₁) (G.map φ.τ₂) (G.map φ.τ₃)
    (by simpa using (congrArg G.map φ.comm₁₂).symm)
    (by simpa using (congrArg G.map φ.comm₂₃).symm)
    (h.δ_naturality hS hS' φ)

/-- A homological functor composed with a `δ`-functor is a cohomological `δ`-functor. Let
`G : 𝒜 ⥤ 𝒟` be a `δ`-functor from an abelian category to a pre-triangulated category, with
`δ`-functor structure `h`, let `H : 𝒟 ⥤ ℬ` be a homological functor into an abelian category, and
assume `H ⁻¹(G(A)) = 0` for every `A` in `𝒜`. Let `δ` be the connecting
morphism `H ⁿ(G(C)) ⟶ H ⁿ⁺¹(G(A))` that the long exact homology sequence of `H` attaches to the
image under `G` of a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜`. Then
`{H ⁿ ∘ G, δ}_{n ≥ 0}` is a cohomological `δ`-functor from `𝒜` to `ℬ`: the functors `H ⁿ ∘ G`
are additive, the sequence
`0 ⟶ H ⁰(G(A)) ⟶ H ⁰(G(B)) ⟶ H ⁰(G(C)) ⟶ H ¹(G(A)) ⟶ H ¹(G(B)) ⟶ ⋯` is exact, and `δ` is
natural in the short exact sequence. -/
@[stacks 05SR]
theorem isCohomologicalDeltaFunctor_comp_shift (h : DeltaFunctorStructure 𝒜 𝒟 G)
    (H : 𝒟 ⥤ ℬ) [H.IsHomological] [H.ShiftSequence ℤ]
    (hH : ∀ A : 𝒜, IsZero ((H.shift (-1 : ℤ)).obj (G.obj A)))
    (δ : ∀ {S : ShortComplex 𝒜}, S.ShortExact → ∀ n : ℕ,
      (G ⋙ H.shift (n : ℤ)).obj S.X₃ ⟶ (G ⋙ H.shift ((n : ℤ) + 1)).obj S.X₁)
    (hδ : ∀ {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ), δ hS n =
      H.homologySequenceδ (Triangle.mk (G.map S.f) (G.map S.g) (h.δ hS)) n ((n : ℤ) + 1) rfl) :
    (∀ n : ℕ, (G ⋙ H.shift (n : ℤ)).Additive) ∧
    (∀ {S : ShortComplex 𝒜}, S.ShortExact → Mono ((G ⋙ H.shift (0 : ℤ)).map S.f)) ∧
    (∀ {S : ShortComplex 𝒜} (_ : S.ShortExact) (n : ℕ),
      ∃ hz : (G ⋙ H.shift (n : ℤ)).map S.f ≫ (G ⋙ H.shift (n : ℤ)).map S.g = 0,
        (ShortComplex.mk _ _ hz).Exact) ∧
    (∀ {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ),
      ∃ hz : (G ⋙ H.shift (n : ℤ)).map S.g ≫ δ hS n = 0,
        (ShortComplex.mk _ _ hz).Exact) ∧
    (∀ {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ),
      ∃ hz : δ hS n ≫ (G ⋙ H.shift ((n : ℤ) + 1)).map S.f = 0,
        (ShortComplex.mk _ _ hz).Exact) ∧
    (∀ {S S' : ShortComplex 𝒜} (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') (n : ℕ),
      (G ⋙ H.shift (n : ℤ)).map φ.τ₃ ≫ δ hS' n =
        δ hS n ≫ (G ⋙ H.shift ((n : ℤ) + 1)).map φ.τ₁) := by
  simp only [hδ]
  refine ⟨fun n => additive_comp_shift h H n, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun hS => (H.homologySequence_mono_shift_map_mor₁_iff _ (h.distinguished hS) (-1) 0
      (by ring)).2 ((hH _).eq_of_src _ _)
  · exact fun hS n => ⟨_, exact_comp_shift h H hS n⟩
  · exact fun hS n => ⟨H.comp_homologySequenceδ _ (h.distinguished hS) n _ rfl,
      H.homologySequence_exact₃ _ (h.distinguished hS) n _ rfl⟩
  · exact fun hS n => ⟨H.homologySequenceδ_comp _ (h.distinguished hS) n _ rfl,
      H.homologySequence_exact₁ _ (h.distinguished hS) n _ rfl⟩
  · exact fun hS hS' φ n => H.homologySequenceδ_naturality (mapTriangleHom h hS hS' φ) n _ rfl

end

end DeltaFunctorStructure

end CategoryTheory.Functor

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- If `(0, b, 0)` and `(0, b', 0)` are endomorphisms of a distinguished triangle
`T = (X, Y, Z, f, g, h)`, then the composite of their middle components vanishes,
i.e. `b ∘ b' = 0` (written `ψ.hom₂ ≫ φ.hom₂ = 0` in Lean's diagrammatic order
with `b = φ.hom₂`, `b' = ψ.hom₂`). -/
@[stacks 05QP]
theorem comp_middle_zero_of_endomorphisms (T : Triangle C)
    (hT : T ∈ distinguishedTriangles)
    (φ ψ : TriangleMorphism T T)
    (hφ₁ : φ.hom₁ = 0)
    (hψ₃ : ψ.hom₃ = 0) :
    ψ.hom₂ ≫ φ.hom₂ = 0 :=
  comp_eq_zero_of_mor₁_comp_eq_zero_of_comp_mor₂_eq_zero T hT (by simp [hφ₁])
    (by simpa [hψ₃] using ψ.comm₂.symm)

end

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits

/-- If `(f, g)` is a retract of a pair `(f', g')` in which every `w` with `w ≫ g' = 0` factors
through `f'`, then every `x` with `x ≫ g = 0` factors through `f`. -/
private lemma exists_comp_eq_of_retract {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B Z A' B' Z' : C} {f : A ⟶ B} {g : B ⟶ Z} {f' : A' ⟶ B'} {g' : B' ⟶ Z'}
    {rA : A' ⟶ A} {iB : B ⟶ B'} {rB : B' ⟶ B} {iZ : Z ⟶ Z'}
    (hi : g ≫ iZ = iB ≫ g') (hr : f' ≫ rB = rA ≫ f) (hB : iB ≫ rB = 𝟙 B)
    (ex : ∀ {W : C} (w : W ⟶ B'), w ≫ g' = 0 → ∃ z, w = z ≫ f') {W : C} (x : W ⟶ B)
    (hx : x ≫ g = 0) : ∃ z, x = z ≫ f := by
  obtain ⟨z, hz⟩ := ex (x ≫ iB) (by rw [Category.assoc, ← hi, ← Category.assoc, hx, zero_comp])
  exact ⟨z ≫ rA, by rw [Category.assoc, ← hr, ← Category.assoc, ← hz, Category.assoc, hB,
    Category.comp_id]⟩

/-- A retract, in the category `Triangle C`, of a distinguished triangle is distinguished. -/
theorem retract_distinguished
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [CategoryTheory.Pretriangulated C]
    {S D : Triangle C} (hD : D ∈ distTriang C) (ρ : Retract S D) :
    S ∈ distTriang C := by
  have e1 : ρ.i.hom₁ ≫ ρ.r.hom₁ = 𝟙 S.obj₁ := by
    rw [← comp_hom₁, ρ.retract, id_hom₁]
  have e2 : ρ.i.hom₂ ≫ ρ.r.hom₂ = 𝟙 S.obj₂ := by
    rw [← comp_hom₂, ρ.retract, id_hom₂]
  have e3 : ρ.i.hom₃ ≫ ρ.r.hom₃ = 𝟙 S.obj₃ := by
    rw [← comp_hom₃, ρ.retract, id_hom₃]
  have Sexact₂ : ∀ {W : C} (f : W ⟶ S.obj₂), f ≫ S.mor₂ = 0 → ∃ z, f = z ≫ S.mor₁ :=
    fun f hf => exists_comp_eq_of_retract ρ.i.comm₂ ρ.r.comm₁ e2
      (fun w hw => Triangle.coyoneda_exact₂ D hD w hw) f hf
  have Sexact₃ : ∀ {W : C} (f : W ⟶ S.obj₃), f ≫ S.mor₃ = 0 → ∃ w, f = w ≫ S.mor₂ :=
    fun f hf => exists_comp_eq_of_retract ρ.i.comm₃ ρ.r.comm₂ e3
      (fun w hw => Triangle.coyoneda_exact₃ D hD w hw) f hf
  have Szero₃₁ : S.mor₃ ≫ (shiftFunctor C 1).map S.mor₁ = 0 := by
    have rc3 : D.mor₃ ≫ (shiftFunctor C 1).map ρ.r.hom₁ = ρ.r.hom₃ ≫ S.mor₃ := ρ.r.comm₃
    have rc1 : D.mor₁ ≫ ρ.r.hom₂ = ρ.r.hom₁ ≫ S.mor₁ := ρ.r.comm₁
    have hS3 : S.mor₃ = ρ.i.hom₃ ≫ D.mor₃ ≫ (shiftFunctor C 1).map ρ.r.hom₁ := by
      rw [rc3, ← Category.assoc, e3, Category.id_comp]
    rw [hS3, Category.assoc, Category.assoc, ← Functor.map_comp, ← rc1, Functor.map_comp,
      reassoc_of% (comp_distTriang_mor_zero₃₁ D hD), zero_comp, comp_zero]
  obtain ⟨Z, g, h, hE⟩ := distinguished_cocone_triangle S.mor₁
  set E : Triangle C := Triangle.mk S.mor₁ g h with hEdef
  have comm : E.mor₁ ≫ ρ.i.hom₂ = ρ.i.hom₁ ≫ D.mor₁ := ρ.i.comm₁
  set α : E ⟶ D := completeDistinguishedTriangleMorphism E D hE hD ρ.i.hom₁ ρ.i.hom₂ comm with hαdef
  have hα₁ : α.hom₁ = ρ.i.hom₁ := completeDistinguishedTriangleMorphism_hom₁ E D hE hD _ _ comm
  have hα₂ : α.hom₂ = ρ.i.hom₂ := completeDistinguishedTriangleMorphism_hom₂ E D hE hD _ _ comm
  set φ : E ⟶ S := α ≫ ρ.r with hφdef
  have hφ₁ : φ.hom₁ = 𝟙 S.obj₁ := by rw [hφdef, comp_hom₁, hα₁, e1]
  have hφ₂ : φ.hom₂ = 𝟙 S.obj₂ := by rw [hφdef, comp_hom₂, hα₂, e2]
  have hsq2 : E.mor₂ ≫ φ.hom₃ = S.mor₂ := by rw [φ.comm₂, hφ₂]; exact Category.id_comp _
  have hmapid : (shiftFunctor C (1 : ℤ)).map (𝟙 S.obj₁) = 𝟙 ((shiftFunctor C (1 : ℤ)).obj S.obj₁) :=
    CategoryTheory.Functor.map_id _ _
  have hsq3 : E.mor₃ = φ.hom₃ ≫ S.mor₃ := by
    rw [← φ.comm₃, hφ₁, hmapid]
    exact (Category.comp_id E.mor₃).symm
  have hiso : IsIso φ.hom₃ := by
    refine isIso_of_yoneda_map_bijective _ fun W => ⟨fun x₁ x₂ hx => ?_, fun y => ?_⟩
    · simp only at hx
      have hx' : (x₁ - x₂) ≫ φ.hom₃ = 0 := by rw [Preadditive.sub_comp, hx, sub_self]
      obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₃ E hE (x₁ - x₂) (by
        rw [hsq3, ← Category.assoc, hx', zero_comp])
      obtain ⟨z, hz⟩ := Sexact₂ y (by rw [← hsq2, ← Category.assoc, ← hy, hx'])
      rw [← sub_eq_zero, hy, hz, Category.assoc,
        show S.mor₁ ≫ E.mor₂ = 0 from comp_distTriang_mor_zero₁₂ E hE, comp_zero]
    · obtain ⟨x₀, hx₀⟩ := Triangle.coyoneda_exact₁ E hE (y ≫ S.mor₃) (by
        change (y ≫ S.mor₃) ≫ (shiftFunctor C 1).map S.mor₁ = 0
        rw [Category.assoc, Szero₃₁, comp_zero])
      obtain ⟨w, hw⟩ := Sexact₃ (y - x₀ ≫ φ.hom₃) (by
        rw [Preadditive.sub_comp, Category.assoc, ← hsq3, ← hx₀, sub_self])
      refine ⟨x₀ + w ≫ E.mor₂, ?_⟩
      change (x₀ + w ≫ E.mor₂) ≫ φ.hom₃ = y
      rw [Preadditive.add_comp, Category.assoc, hsq2, ← hw]
      abel
  have : IsIso φ :=
    Triangle.isIso_of_isIsos φ (by rw [hφ₁]; exact IsIso.id _) (by rw [hφ₂]; exact IsIso.id _) hiso
  exact isomorphic_distinguished E hE S (asIso φ).symm

/-- The summand `T p` is a retract of the direct-sum (product) triangle `productTriangle T`, with
section `productTriangle.lift T (fun j => if j = p then eqToHom else 0)` and retraction the
projection `productTriangle.π T p`. -/
noncomputable def productTriangle_retract
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [CategoryTheory.Pretriangulated C]
    [HasBinaryBiproducts C] (T : WalkingPair → Triangle C) (p : WalkingPair) :
    Retract (T p) (productTriangle T) where
  i := productTriangle.lift T (fun j => if h : j = p then eqToHom (by rw [h]) else 0)
  r := productTriangle.π T p
  retract := by
    apply Triangle.hom_ext <;>
    · simp only [comp_hom₁, comp_hom₂, comp_hom₃, id_hom₁, id_hom₂, id_hom₃,
        productTriangle.lift_hom₁, productTriangle.lift_hom₂, productTriangle.lift_hom₃,
        productTriangle.π_hom₁, productTriangle.π_hom₂, productTriangle.π_hom₃]
      rw [Pi.lift_comp_π, dite_eq_left rfl]
      simp

/-- The direct sum of two triangles is distinguished if and only if both summand triangles are
distinguished. Here `T : WalkingPair → Triangle C` packages the pair `(T₁, T₂)`, and
`productTriangle T` is the direct-sum triangle `T₁ ⊕ T₂`. -/
@[stacks 05QS]
theorem productTriangle_distinguished_iff
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [CategoryTheory.Pretriangulated C]
    [HasBinaryBiproducts C] (T : WalkingPair → Triangle C) :
    (productTriangle T ∈ distTriang C) ↔
      (∀ p : WalkingPair, T p ∈ distTriang C) :=
  ⟨fun hD p => retract_distinguished hD (productTriangle_retract T p),
    fun h => productTriangle_distinguished T h⟩

end

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

section Sketch

variable {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- If a distinguished triangle `T = (X, Y, Z, f, g, h)` has zero connecting morphism
`h = T.mor₃ = 0`, then `g = T.mor₂` admits a section `s : Z ⟶ Y` (i.e. `s ≫ g = 𝟙 Z`) and the
induced map `f ⊕ s : X ⊞ Z ⟶ Y` (`biprod.desc T.mor₁ s`) is an isomorphism; in other words the
triangle splits as `Y ≅ X ⊞ Z`. -/
theorem Stacks05QT_split (T : Triangle C) (hT : T ∈ distinguishedTriangles)
    (h0 : T.mor₃ = 0) :
    ∃ s : T.obj₃ ⟶ T.obj₂, s ≫ T.mor₂ = 𝟙 T.obj₃ ∧
      IsIso (biprod.desc T.mor₁ s : T.obj₁ ⊞ T.obj₃ ⟶ T.obj₂) := by
  obtain ⟨s, hs⟩ := Triangle.coyoneda_exact₃ T hT (𝟙 T.obj₃) (by rw [h0, comp_zero])
  exact ⟨s, hs.symm, isIso_biprod_desc_of_distTriang T hT s hs.symm⟩

/-- A monomorphism `f : X ⟶ Y` in a pretriangulated category is isomorphic, in the arrow
category, to a coprojection `biprod.inl : X ⟶ X ⊞ Z`. -/
theorem mono_arrow_iso_inl {X Y : C} (f : X ⟶ Y) [Mono f] :
    ∃ Z : C, Nonempty (Arrow.mk f ≅ Arrow.mk (biprod.inl : X ⟶ X ⊞ Z)) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  obtain ⟨s, -, hiso⟩ :=
    Stacks05QT_split _ hT ((Triangle.mor₃_eq_zero_iff_mono₁ _ hT).2 (inferInstance : Mono f))
  have : IsIso (biprod.desc f s) := hiso
  exact ⟨Z, ⟨Arrow.isoMk' f biprod.inl (Iso.refl _) (asIso (biprod.desc f s)).symm
    (by simp [IsIso.eq_comp_inv])⟩⟩

/-- If `f : X ⟶ Y` has a kernel, then `f` is isomorphic in the arrow category to
`biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q` for some `K, Z, Q`. -/
theorem hasKernel_imp_split {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    ∃ (K Z Q : C),
      Nonempty (Arrow.mk f ≅ Arrow.mk (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q)) := by
  obtain ⟨X', ⟨e₁⟩⟩ := mono_arrow_iso_inl (kernel.ι f)
  set K := kernel f with hK
  have hinvw : (biprod.inl : K ⟶ K ⊞ X') ≫ e₁.inv.right = e₁.inv.left ≫ kernel.ι f :=
    (Arrow.w e₁.inv).symm
  set g : K ⊞ X' ⟶ Y := e₁.inv.right ≫ f with hg
  have hinl_g : (biprod.inl : K ⟶ K ⊞ X') ≫ g = 0 := by
    rw [hg, ← Category.assoc, hinvw, Category.assoc, kernel.condition, comp_zero]
  set f' : X' ⟶ Y := biprod.inr ≫ g with hf'
  have hgfact : g = biprod.snd ≫ f' :=
    biprod.hom_ext' _ _ (by simp [hinl_g]) (by simp [hf'])
  have hw_hom : e₁.hom.left ≫ (biprod.inl : K ⟶ K ⊞ X') = kernel.ι f ≫ e₁.hom.right :=
    Arrow.w e₁.hom
  have hrr : e₁.inv.right ≫ e₁.hom.right = 𝟙 (K ⊞ X') := congrArg Arrow.Hom.right e₁.inv_hom_id
  have hmono_f' : Mono f' := by
    refine Preadditive.mono_of_cancel_zero _ fun {W} t ht => ?_
    have h₁ : (t ≫ biprod.inr ≫ e₁.inv.right) ≫ f = 0 := by simpa [hf', hg] using ht
    have h₂ : t ≫ biprod.inr ≫ e₁.inv.right ≫ e₁.hom.right =
        kernel.lift f _ h₁ ≫ kernel.ι f ≫ e₁.hom.right := by
      simp
    rw [hrr, Category.comp_id, ← hw_hom] at h₂
    have h4 := congrArg (· ≫ (biprod.snd : K ⊞ X' ⟶ X')) h₂
    simp only [Category.assoc] at h4
    erw [biprod.inr_snd, biprod.inl_snd] at h4
    simpa using h4
  obtain ⟨Q, ⟨e₂⟩⟩ := mono_arrow_iso_inl f'
  refine ⟨K, X', Q, ⟨?_⟩⟩
  have hr1 : IsIso e₁.hom.right := (Arrow.rightFunc.mapIso e₁).isIso_hom
  have hr2 : IsIso e₂.hom.right := (Arrow.rightFunc.mapIso e₂).isIso_hom
  have hl2 : IsIso e₂.hom.left := (Arrow.leftFunc.mapIso e₂).isIso_hom
  have hri : e₁.hom.right ≫ e₁.inv.right = 𝟙 X := congrArg Arrow.Hom.right e₁.hom_inv_id
  have hef : e₁.hom.right ≫ biprod.snd ≫ f' = f := by
    rw [← hgfact, hg, ← Category.assoc, hri]
    simp
  have hw2 : e₂.hom.left ≫ (biprod.inl : X' ⟶ X' ⊞ Q) = f' ≫ e₂.hom.right := Arrow.w e₂.hom
  let lIso : X ≅ K ⊞ X' :=
    (asIso e₁.hom.right) ≪≫ biprod.mapIso (Iso.refl K) (asIso e₂.hom.left)
  refine Arrow.isoMk lIso (asIso e₂.hom.right) ?_
  change (e₁.hom.right ≫ biprod.map (𝟙 K) e₂.hom.left) ≫ (biprod.snd ≫ biprod.inl)
      = f ≫ e₂.hom.right
  simp only [Category.assoc, biprod.map_snd_assoc]
  calc _ = e₁.hom.right ≫ biprod.snd ≫ f' ≫ e₂.hom.right := by congr 1; congr 1
    _ = f ≫ e₂.hom.right := by rw [reassoc_of% hef]

open CategoryTheory.Pretriangulated.Opposite in
/-- If `f : X ⟶ Y` has a cokernel, then `f` is isomorphic in the arrow category to
`biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q` for some `K, Z, Q`. -/
theorem hasCokernel_imp_split {X Y : C} (f : X ⟶ Y) [HasCokernel f] :
    ∃ (K Z Q : C),
      Nonempty (Arrow.mk f ≅ Arrow.mk (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q)) := by
  have : HasKernel f.op := by
    have hcolim : IsColimit (CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)) :=
      cokernelIsCokernel f
    have hlim := CokernelCofork.IsColimit.ofπOp (cokernel.π f) (cokernel.condition f) hcolim
    exact ⟨⟨⟨_, hlim⟩⟩⟩
  obtain ⟨K', Z', Q', ⟨e⟩⟩ := hasKernel_imp_split (f.op)
  refine ⟨Q'.unop, Z'.unop, K'.unop, ⟨?_⟩⟩
  set g : K' ⊞ Z' ⟶ Z' ⊞ Q' := biprod.snd ≫ biprod.inl with hgdef
  have arrowUnop : Arrow.mk g.unop ≅ Arrow.mk f := by
    refine Arrow.isoMk ⟨(e.hom.right).unop, (e.inv.right).unop, ?_, ?_⟩
      ⟨(e.hom.left).unop, (e.inv.left).unop, ?_, ?_⟩ ?_
    · rw [← unop_comp]; simp [← Arrow.comp_right]
    · rw [← unop_comp]; simp [← Arrow.comp_right]
    · rw [← unop_comp]; simp [← Arrow.comp_left]
    · rw [← unop_comp]; simp [← Arrow.comp_left]
    · have hw := Arrow.w e.hom
      dsimp at hw ⊢
      have := congrArg Quiver.Hom.unop hw
      simp only [unop_comp] at this
      exact this.symm
  let L : (Z' ⊞ Q').unop ≅ Z'.unop ⊞ Q'.unop := (biprod.opIso Z'.unop Q'.unop).unop
  let R : (K' ⊞ Z').unop ≅ K'.unop ⊞ Z'.unop := (biprod.opIso K'.unop Z'.unop).unop
  have conj : L.inv ≫ g.unop ≫ R.hom
      = (biprod.fst ≫ biprod.inr : Z'.unop ⊞ Q'.unop ⟶ K'.unop ⊞ Z'.unop) := by
    have e1 : L.inv ≫ (biprod.inl : Z' ⟶ Z' ⊞ Q').unop = biprod.fst := by
      change ((biprod.opIso _ _).unop).inv ≫ _ = _
      rw [Iso.unop_inv, ← unop_comp, biprod.inl_opIso_inv]; rfl
    have e2 : (biprod.snd : K' ⊞ Z' ⟶ Z').unop ≫ R.hom = biprod.inr := by
      change _ ≫ ((biprod.opIso _ _).unop).hom = _
      rw [Iso.unop_hom, ← unop_comp, biprod.opIso_hom_snd]; rfl
    rw [hgdef, unop_comp, ← Category.assoc, ← Category.assoc, e1, Category.assoc, e2]
  have conjIso : Arrow.mk (biprod.fst ≫ biprod.inr : Z'.unop ⊞ Q'.unop ⟶ K'.unop ⊞ Z'.unop)
      ≅ Arrow.mk g.unop := by
    refine Arrow.isoMk L.symm R.symm ?_
    change L.inv ≫ g.unop = (biprod.fst ≫ biprod.inr) ≫ R.inv
    rw [← conj]
    simp
  have braidedIso : Arrow.mk (biprod.snd ≫ biprod.inl : Q'.unop ⊞ Z'.unop ⟶ Z'.unop ⊞ K'.unop)
      ≅ Arrow.mk (biprod.fst ≫ biprod.inr : Z'.unop ⊞ Q'.unop ⟶ K'.unop ⊞ Z'.unop) := by
    refine Arrow.isoMk (biprod.braiding Q'.unop Z'.unop) (biprod.braiding Z'.unop K'.unop) ?_
    change (biprod.braiding Q'.unop Z'.unop).hom ≫ (biprod.fst ≫ biprod.inr)
        = (biprod.snd ≫ biprod.inl) ≫ (biprod.braiding Z'.unop K'.unop).hom
    ext <;> simp
  exact (braidedIso ≪≫ conjIso ≪≫ arrowUnop).symm

end Sketch

/-- In a pre-triangulated category `C`, for a
morphism `f : X ⟶ Y` the following are equivalent:

1. `f` has a kernel;
2. `f` has a cokernel;
3. there are objects `K, Z, Q` with `f` isomorphic, in the arrow category, to the
   composite of the second projection `K ⊞ Z ⟶ Z` with the first coprojection
   `Z ⟶ Z ⊞ Q`, namely `biprod.snd ≫ biprod.inl`. -/
@[stacks 05QU]
theorem hasKernel_iff_hasCokernel_iff_split (C : Type*) [Category C] [HasZeroObject C]
    [Preadditive C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {X Y : C} (f : X ⟶ Y) :
    [HasKernel f,
     HasCokernel f,
     ∃ (K Z Q : C),
       Nonempty (Arrow.mk f ≅ Arrow.mk (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q))].TFAE := by
  tfae_have 3 → 1 := by
    rintro ⟨K, Z, Q, ⟨e⟩⟩
    have hk : HasKernel (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q) :=
      hasKernel_comp_mono biprod.snd biprod.inl
    rw [Arrow.iso_w' e.symm]
    exact hasKernel_iso_comp _ _
  tfae_have 3 → 2 := by
    rintro ⟨K, Z, Q, ⟨e⟩⟩
    rw [Arrow.iso_w' e.symm]
    exact hasCokernel_epi_comp _ _
  tfae_have 1 → 3 := fun _ => hasKernel_imp_split f
  tfae_have 2 → 3 := fun _ => hasCokernel_imp_split f
  tfae_finish

end

end
