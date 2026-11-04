module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
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
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroup
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Defs

/-!
# `K`-groups of bounded derived categories

Let `A` be an abelian category with a derived category `D(A)`. Its zeroth `K`-group `K₀(A)` is the
free abelian group on the objects of `A` modulo `[X₂] - [X₁] - [X₃]` for every short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, and the zeroth `K`-group of a pretriangulated category is
`CategoryTheory.Pretriangulated.K0`, the same construction with the relations indexed by the
distinguished triangles. This file identifies the two for a bounded derived category:
`K₀(A) ≃+ K₀(D^b(A))`, and, for a weak Serre subcategory `B` of `A`,
`K₀(B) ≃+ K₀(D^b_B(A))`, where `D^b_B(A) ⊆ D(A)` is the full subcategory of bounded objects all of
whose homology objects lie in `B`. Both isomorphisms send the class of an object to the class of
that object viewed as a complex in degree `0`, and this property determines them, the classes of
objects generating the source.

In one direction: a short exact sequence of `A` gives a distinguished triangle
`X₁[0] ⟶ X₂[0] ⟶ X₃[0] ⟶ X₁[0]⟦1⟧` of `D(A)` whose three vertices are bounded, so `X ↦ [X[0]]`
is additive and induces a homomorphism. For a weak Serre subcategory the same works because the
inclusion `B ⥤ A` is exact, so a short exact sequence of `B` is one of `A`, and the vertices of the
resulting triangle have all their homology in `B`.

In the other: the Euler characteristic `[X] ↦ ∑ᶠ i, (-1)ⁱ [Hⁱ(X)]`, a finite sum because `X` is
bounded. Its additivity along a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` is the long exact
sequence of homology plus a telescoping: writing `uᵢ`, `vᵢ`, `δᵢ` for the maps
`Hⁱ(X) ⟶ Hⁱ(Y) ⟶ Hⁱ(Z) ⟶ Hⁱ⁺¹(X)` and `kᵢ = [ker uᵢ]`, exactness gives
`[Hⁱ(X)] = kᵢ + [im uᵢ]`, `[Hⁱ(Y)] = [im uᵢ] + [im vᵢ]` and `[Hⁱ(Z)] = [im vᵢ] + kᵢ₊₁`, so the
`i`-th defect `[Hⁱ(Y)] - [Hⁱ(X)] - [Hⁱ(Z)]` is `-kᵢ - kᵢ₊₁`, whose alternating sum over an interval
`[a, b]` is the difference of the two boundary terms `(-1)ᵃ kₐ` and `(-1)^(b+1) k_{b+1}`; both
vanish when the interval contains the support of the homology of all three objects. For a weak
Serre subcategory this computation takes place in `B`: the inclusion is exact and faithful, so
`ShortComplex.exact_map_iff_of_faithful` transports the long exact sequence of `D(A)` into `B`,
where the kernels and images above are then formed.

That the two homomorphisms are mutually inverse needs only one of the two composites, together with
surjectivity, which is an induction on the length of an interval containing the support of the
homology: the truncation triangle `τ_{≤a} X ⟶ X ⟶ τ_{>a} X ⟶ (τ_{≤a} X)⟦1⟧` of the canonical
t-structure has all three vertices in the subcategory — for `D^b_B(A)` because the homology of a
truncation is either zero or the homology of `X` — its first vertex has homology concentrated in
the single degree `a`, hence is isomorphic to `Y[0]⟦-a⟧` for an object `Y`, whose class is
`(-1)ᵃ [Y[0]]` because `[W⟦1⟧] = -[W]` in `K₀` of any pretriangulated category, and its third
vertex has homology in `[a + 1, b]`.

## Main results

* `DerivedCategory.Bounded.exists_addEquiv_K0`: `K₀(A) ≃+ K₀(D^b(A))`, characterised by
  `[X] ↦ [X[0]]`.
* `DerivedCategory.exists_addEquiv_K0_of_isWeakSerreClass`: `K₀(B) ≃+ K₀(D^b_B(A))` for a weak
  Serre subcategory `B` of `A`, characterised by `[X] ↦ [X[0]]`.

## Implementation notes

Both statements are for bounded objects only, as in the source: for the unbounded derived category
of a category with countable coproducts the Eilenberg swindle kills `K₀`.

`K₀` of an abelian category is `KZero`, with its classes `KZero.mk` and its universal property
`KZero.lift`. `K₀` of a pretriangulated category is `CategoryTheory.Pretriangulated.K0`, a quotient
of a free abelian group by relations of the shape `[x₂] - [x₁] - [x₃]`; the relation itself and
the value on a generator of a homomorphism lifted from a function killing the relations are
proved for an arbitrary such quotient, in `quot_eq_add` and `liftCls`.

The relations of `K₀` of a triangulated category are indexed by distinguished triangles, and the
triangles available here are triangles of `D(A)` whose three vertices happen to lie in the
subcategory. They are transported once and for all in `clsT_eq_add_of_distTriang_ι` and its
counterpart for `D^b_B(A)`: a morphism of the subcategory is completed to a distinguished triangle
*inside* the subcategory and the resulting cone is identified with the expected object through the
uniqueness of cones, `Pretriangulated.isoTriangleOfIso₁₂`.

The description of `D^b_B(A)` is taken as a hypothesis `hP` on an object property `P` rather than
as a definition, so that a caller may use its own spelling of the subcategory; the hypothesis is
substituted at the start of the proof, which then runs for the property `Db B` prescribed by it.
Its triangulatedness is likewise a hypothesis: it is what makes `K₀(D^b_B(A))` a `K`-group of a
pretriangulated category at all.

## References

* [Stacks project, Tag 0FCP](https://stacks.math.columbia.edu/tag/0FCP)
* [Stacks project, Tag 0FCS](https://stacks.math.columbia.edu/tag/0FCS)
* [Stacks project, Tag 0FCN](https://stacks.math.columbia.edu/tag/0FCN)
-/

@[expose] public section

open CategoryTheory Limits ObjectProperty Pretriangulated Triangulated ZeroObject

universe w v u

/-! ### Quotients of a free abelian group by relations `[x₂] - [x₁] - [x₃]` -/

section Quot

variable {X : Type*} {s : Set (FreeAbelianGroup X)}

/-- The relation `[x₂] = [x₁] + [x₃]` holds in `FreeAbelianGroup X ⧸ AddSubgroup.closure s`
as soon as `[x₂] - [x₁] - [x₃]` belongs to `s`. -/
private lemma quot_eq_add {x₁ x₂ x₃ : X}
    (h : FreeAbelianGroup.of x₂ - FreeAbelianGroup.of x₁ - FreeAbelianGroup.of x₃ ∈ s) :
    (QuotientAddGroup.mk (FreeAbelianGroup.of x₂) :
        FreeAbelianGroup X ⧸ AddSubgroup.closure s) =
      QuotientAddGroup.mk (FreeAbelianGroup.of x₁) +
        QuotientAddGroup.mk (FreeAbelianGroup.of x₃) := by
  have h0 : (QuotientAddGroup.mk' (AddSubgroup.closure s))
      (FreeAbelianGroup.of x₂ - FreeAbelianGroup.of x₁ - FreeAbelianGroup.of x₃) = 0 := by
    rw [QuotientAddGroup.mk'_apply]
    exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.subset_closure h)
  rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h0
  simpa only [QuotientAddGroup.mk'_apply] using h0

/-- A function `f` which kills every relation of `s` induces a homomorphism on the quotient
`FreeAbelianGroup X ⧸ AddSubgroup.closure s`. -/
private def liftCls {M : Type*} [AddCommGroup M] (s : Set (FreeAbelianGroup X)) (f : X → M)
    (hf : ∀ x ∈ s, FreeAbelianGroup.lift f x = 0) :
    (FreeAbelianGroup X ⧸ AddSubgroup.closure s) →+ M :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift f) (fun x hx => by
    have h : AddSubgroup.closure s ≤ (FreeAbelianGroup.lift f).ker := by
      rw [AddSubgroup.closure_le]
      intro y hy
      exact AddMonoidHom.mem_ker.mpr (hf y hy)
    exact AddMonoidHom.mem_ker.mp (h hx))

private lemma liftCls_cls {M : Type*} [AddCommGroup M] (s : Set (FreeAbelianGroup X)) (f : X → M)
    (hf : ∀ x ∈ s, FreeAbelianGroup.lift f x = 0) (x : X) :
    liftCls s f hf (QuotientAddGroup.mk (FreeAbelianGroup.of x)) = f x := by
  show FreeAbelianGroup.lift f (FreeAbelianGroup.of x) = f x
  simp

/-- The value of `FreeAbelianGroup.lift f` on a generator. -/
private lemma lift_of {M : Type*} [AddCommGroup M] (f : X → M) (x : X) :
    FreeAbelianGroup.lift f (FreeAbelianGroup.of x) = f x := by
  simp

end Quot

/-! ### The zeroth `K`-group of an abelian category -/

section Abelian

variable {E : Type u} [Category.{v} E] [Abelian E]

private lemma mk_kernel_eq_mk_image_of_exact {W₁ W₂ W₃ : E} {f : W₁ ⟶ W₂} {g : W₂ ⟶ W₃}
    {w : f ≫ g = 0} (h : (ShortComplex.mk f g w).Exact) :
    KZero.mk _ (kernel g) = KZero.mk _ (Abelian.image f) :=
  (KZero.mk_eq_of_iso (IsLimit.conePointUniqueUpToIso h.isLimitImage (kernelIsKernel g))).symm

/-- If `W₁ ⟶ W₂ ⟶ W₃` is exact at `W₂`, the class of `W₂` in `K₀(E)` is the sum of the classes of
the images of the two maps. -/
private lemma mk_eq_add_image_image_of_exact {W₁ W₂ W₃ : E} {f : W₁ ⟶ W₂} {g : W₂ ⟶ W₃}
    {w : f ≫ g = 0} (h : (ShortComplex.mk f g w).Exact) :
    KZero.mk _ W₂ = KZero.mk _ (Abelian.image f) + KZero.mk _ (Abelian.image g) := by
  rw [KZero.mk_eq_kernel_add_image g, mk_kernel_eq_mk_image_of_exact h]

/-- **The defect of additivity of a class along a four-term exact sequence**: for
`W₁ ⟶ W₂ ⟶ W₃ ⟶ W₄` exact at `W₂` and at `W₃`, the defect `[W₂] - [W₁] - [W₃]` is measured by
the kernel of the first map and the image of the last. -/
private lemma mk_sub_sub_eq {W₁ W₂ W₃ W₄ : E} {f : W₁ ⟶ W₂} {g : W₂ ⟶ W₃} {h : W₃ ⟶ W₄}
    {w₁ : f ≫ g = 0} {w₂ : g ≫ h = 0} (hf : (ShortComplex.mk f g w₁).Exact)
    (hg : (ShortComplex.mk g h w₂).Exact) :
    KZero.mk _ W₂ - KZero.mk _ W₁ - KZero.mk _ W₃ =
      -KZero.mk _ (kernel f) - KZero.mk _ (Abelian.image h) := by
  rw [mk_eq_add_image_image_of_exact hf, KZero.mk_eq_kernel_add_image f,
    mk_eq_add_image_image_of_exact hg]
  abel

private lemma mk_image_eq_zero {X Y : E} (f : X ⟶ Y) (hX : IsZero X) :
    KZero.mk _ (Abelian.image f) = 0 :=
  KZero.mk_eq_zero_of_isZero (IsZero.of_epi (Abelian.factorThruImage f) hX)

private lemma mk_kernel_eq_zero {X Y : E} (f : X ⟶ Y) (hX : IsZero X) :
    KZero.mk _ (kernel f) = 0 :=
  KZero.mk_eq_zero_of_isZero (IsZero.of_mono (kernel.ι f) hX)

end Abelian

/-! ### The zeroth `K`-group of a pretriangulated category -/


section Pretriang

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- The class of an object in `K₀(C)`, for `C` pretriangulated. -/
private abbrev clsT (X : C) : Pretriangulated.K0 C := QuotientAddGroup.mk (FreeAbelianGroup.of X)

private lemma clsT_eq_add {T : Triangle C} (hT : T ∈ distTriang C) :
    clsT T.obj₂ = clsT T.obj₁ + clsT T.obj₃ :=
  quot_eq_add ⟨T, hT, rfl⟩

private lemma clsT_zero_eq_zero : clsT (0 : C) = 0 := by
  have h : clsT (0 : C) = clsT (0 : C) + clsT (0 : C) :=
    clsT_eq_add (contractible_distinguished (0 : C))
  exact left_eq_add.mp h

private lemma clsT_eq_of_iso {X Y : C} (e : X ≅ Y) : clsT X = clsT Y := by
  have h : clsT Y = clsT X + clsT (0 : C) :=
    clsT_eq_add (T := Triangle.mk e.hom (0 : Y ⟶ 0) 0)
      ((Triangle.distinguished_iff_of_isZero₃ _ (isZero_zero C)).2 (by dsimp; infer_instance))
  rw [h, clsT_zero_eq_zero, add_zero]

private lemma clsT_eq_zero_of_isZero {X : C} (hX : IsZero X) : clsT X = 0 := by
  rw [clsT_eq_of_iso hX.isoZero, clsT_zero_eq_zero]

/-- Shifting by `1` negates the class in `K₀(C)`: the triangle `X ⟶ 0 ⟶ X⟦1⟧` is
distinguished. -/
private lemma clsT_shift_one (X : C) : clsT (X⟦(1 : ℤ)⟧) = -clsT X := by
  have h : clsT (0 : C) = clsT X + clsT (X⟦(1 : ℤ)⟧) :=
    clsT_eq_add (contractible_distinguished₂ X)
  rw [clsT_zero_eq_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- `[X⟦n⟧] = (-1)ⁿ [X]` in `K₀(C)`. -/
private lemma clsT_shift (X : C) (n : ℤ) : clsT (X⟦n⟧) = (n.negOnePow : ℤ) • clsT X := by
  induction n using Int.induction_on with
  | zero =>
    rw [Int.negOnePow_zero, Units.val_one, one_smul]
    exact clsT_eq_of_iso ((shiftFunctorZero C ℤ).app X)
  | succ n ih =>
    rw [clsT_eq_of_iso ((shiftFunctorAdd C (n : ℤ) 1).app X), Functor.comp_obj,
      clsT_shift_one, ih, Int.negOnePow_succ, Units.val_neg, neg_smul]
  | pred n ih =>
    rw [clsT_eq_of_iso ((shiftFunctorAdd' C (-(n : ℤ) - 1) 1 (-(n : ℤ)) (by omega)).app X),
      Functor.comp_obj, clsT_shift_one, neg_eq_iff_eq_neg] at ih
    rw [ih, Int.negOnePow_sub, Int.negOnePow_one, Units.val_mul, Units.val_neg, Units.val_one,
      mul_neg_one, neg_smul]

/-- A homomorphism to `K₀(C)` whose range contains every class `[X]` is surjective. -/
private lemma surjective_of_clsT_mem_range {M : Type*} [AddCommGroup M] (f : M →+ K0 C)
    (h : ∀ X : C, clsT X ∈ AddMonoidHom.range f) : Function.Surjective f := by
  intro z
  rw [← AddMonoidHom.mem_range]
  induction z using QuotientAddGroup.induction_on with
  | H w =>
    induction w using FreeAbelianGroup.induction_on with
    | zero => exact zero_mem _
    | of X => exact h X
    | neg X => exact neg_mem (h X)
    | add x y hx hy => exact add_mem hx hy

end Pretriang

/-! ### A telescoping sum over an interval of integers -/

/-- If `F i = g (i + 1) - g i` and `g` vanishes at both ends of `[a, b + 1]`, the sum of `F` over
`Finset.Icc a b` vanishes. -/
private lemma sum_Icc_eq_zero_of_telescope {M : Type*} [AddCommGroup M] (F g : ℤ → M) (a b : ℤ)
    (hab : a ≤ b + 1) (h : ∀ i : ℤ, F i = g (i + 1) - g i) (ha : g a = 0) (hb : g (b + 1) = 0) :
    ∑ i ∈ Finset.Icc a b, F i = 0 := by
  suffices hsum : ∀ c : ℤ, a - 1 ≤ c → ∑ i ∈ Finset.Icc a c, F i = g (c + 1) - g a by
    rw [hsum b (by omega), ha, hb, sub_zero]
  intro c hc
  induction c, hc using Int.leInduction with
  | base =>
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, show a - 1 + 1 = a from by omega,
      sub_self]
  | succ c hc ih =>
    have hins : Finset.Icc a (c + 1) = insert (c + 1) (Finset.Icc a c) := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih, h (c + 1)]
    abel

/-- If `F₂ i - F₁ i - F₃ i = g (i + 1) - g i` and `g` vanishes at both ends of `[a, b + 1]`, then
the sum of `F₂` over `Finset.Icc a b` is the sum of those of `F₁` and `F₃`. -/
private lemma sum_Icc_eq_add_of_telescope {M : Type*} [AddCommGroup M] (F₁ F₂ F₃ g : ℤ → M)
    (a b : ℤ) (hab : a ≤ b + 1) (h : ∀ i : ℤ, F₂ i - F₁ i - F₃ i = g (i + 1) - g i)
    (ha : g a = 0) (hb : g (b + 1) = 0) :
    ∑ i ∈ Finset.Icc a b, F₂ i = ∑ i ∈ Finset.Icc a b, F₁ i + ∑ i ∈ Finset.Icc a b, F₃ i := by
  have H := sum_Icc_eq_zero_of_telescope _ g a b hab h ha hb
  simp only [Finset.sum_sub_distrib] at H
  rwa [sub_sub, sub_eq_zero] at H

/-! ### Homology of the derived category -/

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

open DerivedCategory

/-- The `i`-th homology object of an object of the derived category. -/
private noncomputable abbrev Hobj (i : ℤ) (X : DerivedCategory A) : A :=
  (DerivedCategory.homologyFunctor A i).obj X

private lemma isZero_Hobj_of_bounds {X : DerivedCategory A} {n m : ℤ}
    (hn : TStructure.t.IsGE X n) (hm : TStructure.t.IsLE X m) (i : ℤ) (hi : i < n ∨ m < i) :
    IsZero (Hobj i X) := by
  have := hn
  have := hm
  rcases hi with hi | hi
  · exact DerivedCategory.isZero_of_isGE X n i hi
  · exact DerivedCategory.isZero_of_isLE X m i hi

/-- Three bounded objects of `D(A)` have no homology outside a common interval `[a, b]`. -/
private lemma exists_interval_isZero_Hobj {X₁ X₂ X₃ : DerivedCategory A}
    (h₁ : TStructure.t.bounded X₁) (h₂ : TStructure.t.bounded X₂) (h₃ : TStructure.t.bounded X₃) :
    ∃ a b : ℤ, a ≤ b + 1 ∧ (∀ i : ℤ, (i < a ∨ b < i) → IsZero (Hobj i X₁)) ∧
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero (Hobj i X₂)) ∧
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero (Hobj i X₃)) := by
  obtain ⟨⟨a₁, h₁⟩, ⟨b₁, h₁'⟩⟩ := h₁
  obtain ⟨⟨a₂, h₂⟩, ⟨b₂, h₂'⟩⟩ := h₂
  obtain ⟨⟨a₃, h₃⟩, ⟨b₃, h₃'⟩⟩ := h₃
  obtain ⟨a, ha₁, ha₂, ha₃⟩ : ∃ a : ℤ, a ≤ a₁ ∧ a ≤ a₂ ∧ a ≤ a₃ :=
    ⟨min a₁ (min a₂ a₃), by omega, by omega, by omega⟩
  obtain ⟨b, hb₁, hb₂, hb₃, hab⟩ : ∃ b : ℤ, b₁ ≤ b ∧ b₂ ≤ b ∧ b₃ ≤ b ∧ a ≤ b + 1 :=
    ⟨max (max b₁ (max b₂ b₃)) a, by omega, by omega, by omega, by omega⟩
  exact ⟨a, b, hab,
    fun i hi => isZero_Hobj_of_bounds (TStructure.t.isGE_of_ge _ a a₁ ha₁)
      (TStructure.t.isLE_of_le _ b₁ b hb₁) i hi,
    fun i hi => isZero_Hobj_of_bounds (TStructure.t.isGE_of_ge _ a a₂ ha₂)
      (TStructure.t.isLE_of_le _ b₂ b hb₂) i hi,
    fun i hi => isZero_Hobj_of_bounds (TStructure.t.isGE_of_ge _ a a₃ ha₃)
      (TStructure.t.isLE_of_le _ b₃ b hb₃) i hi⟩

/-- In a distinguished triangle `W ⟶ X ⟶ V ⟶ W⟦1⟧` of `D(A)` whose third vertex has no homology
in degrees `≤ a`, the map `Hⁱ(W) ⟶ Hⁱ(X)` is an isomorphism for every `i ≤ a`. -/
private lemma isIso_homologyMap_mor₁ {T : Triangle (DerivedCategory A)}
    (hT : T ∈ distTriang (DerivedCategory A)) (a i : ℤ) (hi : i ≤ a)
    (hV : ∀ j : ℤ, j ≤ a → IsZero (Hobj j T.obj₃)) :
    IsIso ((DerivedCategory.homologyFunctor A i).map T.mor₁) := by
  have hmono : Mono ((DerivedCategory.homologyFunctor A i).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i]
    exact (hV (i - 1) (by omega)).eq_of_src _ _
  have hepi : Epi ((DerivedCategory.homologyFunctor A i).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i]
    exact (hV i hi).eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

/-- In a distinguished triangle `W ⟶ X ⟶ V ⟶ W⟦1⟧` of `D(A)` whose first vertex has no homology
in degrees `> a`, the map `Hⁱ(X) ⟶ Hⁱ(V)` is an isomorphism for every `i > a`. -/
private lemma isIso_homologyMap_mor₂ {T : Triangle (DerivedCategory A)}
    (hT : T ∈ distTriang (DerivedCategory A)) (a i : ℤ) (hi : a < i)
    (hW : ∀ j : ℤ, a < j → IsZero (Hobj j T.obj₁)) :
    IsIso ((DerivedCategory.homologyFunctor A i).map T.mor₂) := by
  have hmono : Mono ((DerivedCategory.homologyFunctor A i).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i]
    exact (hW i hi).eq_of_src _ _
  have hepi : Epi ((DerivedCategory.homologyFunctor A i).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1)]
    exact (hW (i + 1) (by omega)).eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

end Derived

/-! ### A weak Serre subcategory as an abelian category -/

section WeakSerre

variable {A : Type u} [Category.{v} A] [Abelian A] (B : ObjectProperty A) [B.IsWeakSerreClass]

/-- Exactness of a short complex of a weak Serre subcategory `B` is exactness of its image in the
ambient category: the inclusion of `B` is exact and faithful. -/
private lemma exact_of_exact_map_ι (S : ShortComplex B.FullSubcategory) (h : (S.map B.ι).Exact) :
    S.Exact := by
  have := B.preservesFiniteLimits_ι_of_isWeakSerreClass
  have := B.preservesFiniteColimits_ι_of_isWeakSerreClass
  rwa [← ShortComplex.exact_map_iff_of_faithful S B.ι]

/-- Exactness in `B` of a short complex given by morphisms of the ambient category. -/
private lemma exact_of_exact_hom {X Y Z : B.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : f ≫ g = 0)
    (h : (ShortComplex.mk f.hom g.hom (by rw [← FullSubcategory.comp_hom, w]; rfl)).Exact) :
    (ShortComplex.mk f g w).Exact :=
  exact_of_exact_map_ι B _ h

/-- A short exact sequence of a weak Serre subcategory is short exact in the ambient category. -/
private lemma shortExact_map_ι {S : ShortComplex B.FullSubcategory} (hS : S.ShortExact) :
    (S.map B.ι).ShortExact := by
  have := B.preservesFiniteLimits_ι_of_isWeakSerreClass
  have := B.preservesFiniteColimits_ι_of_isWeakSerreClass
  exact hS.map_of_exact B.ι

omit [B.IsWeakSerreClass] in
private lemma isZero_of_isZero_obj {X : B.FullSubcategory} (h : IsZero X.obj) : IsZero X :=
  (IsZero.iff_id_eq_zero X).2 (B.ι.map_injective (h.eq_of_src _ _))

end WeakSerre
/-! ### The Euler characteristic on the bounded derived category -/


section Euler

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The Euler characteristic `∑ᶠ i, (-1)ⁱ [Hⁱ(X)]` of an object of the derived category, an
element of `K₀(A)`. It is the interesting sum only when `X` is bounded. -/
private noncomputable def eulerChar (X : DerivedCategory A) : KZero A :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • KZero.mk _ (Hobj i X)

/-- The sum over `ℤ` of `(-1)ⁱ • f i` is the sum over `[a, b]` when `f` vanishes outside it. -/
private lemma finsum_negOnePow_smul_eq_sum {M : Type*} [AddCommGroup M] (f : ℤ → M) (a b : ℤ)
    (h : ∀ i : ℤ, (i < a ∨ b < i) → f i = 0) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • f i = ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • f i := by
  refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
  simp only [Function.mem_support] at hi
  simp only [Finset.coe_Icc, Set.mem_Icc]
  by_contra hia
  exact hi (by rw [h i (by lia), smul_zero])

private lemma eulerChar_eq_sum (X : DerivedCategory A) (a b : ℤ)
    (h : ∀ i : ℤ, (i < a ∨ b < i) → IsZero (Hobj i X)) :
    eulerChar X = ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • KZero.mk _ (Hobj i X) :=
  finsum_negOnePow_smul_eq_sum _ a b fun i hi => KZero.mk_eq_zero_of_isZero (h i hi)

variable {T : Triangle (DerivedCategory A)}

/-- The alternating sum of the classes of the homology objects of a distinguished triangle of
`D(A)` over an interval `[a, b]` is additive, provided the homology of `T.obj₁` vanishes in
degree `b + 1` and that of `T.obj₃` in degree `a - 1`. -/
private lemma sum_Icc_eq_of_distTriang (hT : T ∈ distTriang (DerivedCategory A)) (a b : ℤ)
    (hab : a ≤ b + 1) (h₁ : IsZero (Hobj (b + 1) T.obj₁)) (h₃ : IsZero (Hobj (a - 1) T.obj₃)) :
    ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • KZero.mk _ (Hobj i T.obj₂) =
      (∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • KZero.mk _ (Hobj i T.obj₁)) +
        ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • KZero.mk _ (Hobj i T.obj₃) := by
  set k : ℤ → KZero A := fun i =>
    KZero.mk _ (kernel ((DerivedCategory.homologyFunctor A i).map T.mor₁)) with hk
  have key : ∀ i : ℤ, (i.negOnePow : ℤ) • KZero.mk _ (Hobj i T.obj₂) -
      (i.negOnePow : ℤ) • KZero.mk _ (Hobj i T.obj₁) -
      (i.negOnePow : ℤ) • KZero.mk _ (Hobj i T.obj₃) =
      (((i + 1).negOnePow : ℤ) • k (i + 1) - (i.negOnePow : ℤ) • k i) := by
    intro i
    have e1 : KZero.mk _ (Hobj i T.obj₁) = k i +
        KZero.mk _ (Abelian.image ((DerivedCategory.homologyFunctor A i).map T.mor₁)) :=
      KZero.mk_eq_kernel_add_image _
    have e2 : KZero.mk _ (Hobj i T.obj₂) =
        KZero.mk _ (Abelian.image ((DerivedCategory.homologyFunctor A i).map T.mor₁)) +
          KZero.mk _ (Abelian.image ((DerivedCategory.homologyFunctor A i).map T.mor₂)) :=
      mk_eq_add_image_image_of_exact
        (DerivedCategory.HomologySequence.exact₂ T hT i)
    have e4 : k (i + 1) =
        KZero.mk _ (Abelian.image (DerivedCategory.HomologySequence.δ T i (i + 1) rfl)) :=
      mk_kernel_eq_mk_image_of_exact
        (DerivedCategory.HomologySequence.exact₁ T hT i (i + 1) rfl)
    have e3 : KZero.mk _ (Hobj i T.obj₃) =
        KZero.mk _ (Abelian.image ((DerivedCategory.homologyFunctor A i).map T.mor₂)) +
          k (i + 1) := by
      rw [e4]
      exact mk_eq_add_image_image_of_exact
        (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl)
    rw [e1, e2, e3]
    simp only [Int.negOnePow_succ, Units.val_neg, neg_smul, smul_add]
    abel
  have hga : ((a.negOnePow : ℤ) • k a) = 0 := by
    have h' : k a = KZero.mk _ (Abelian.image (DerivedCategory.HomologySequence.δ T (a - 1) a
        (by omega))) :=
      mk_kernel_eq_mk_image_of_exact
        (DerivedCategory.HomologySequence.exact₁ T hT (a - 1) a (by omega))
    rw [h', mk_image_eq_zero _ h₃, smul_zero]
  have hgb : (((b + 1).negOnePow : ℤ) • k (b + 1)) = 0 := by
    have h' : k (b + 1) = 0 := mk_kernel_eq_zero _ h₁
    rw [h', smul_zero]
  exact sum_Icc_eq_add_of_telescope _ _ _ (fun i => (i.negOnePow : ℤ) • k i) a b hab key hga hgb


end Euler

/-! ### The bounded derived category -/

section Bounded

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

open DerivedCategory


/-- The object `X[0]` of `D^b(A)` attached to an object `X` of `A`. -/
private noncomputable abbrev sng (X : A) : DerivedCategory.Bounded A :=
  ⟨(DerivedCategory.singleFunctor A 0).obj X, ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩⟩

/-- The class of an object of a triangulated subcategory of `D(A)` whose underlying object is zero
lies in the range of every homomorphism to `K₀`. -/
private lemma clsT_mem_range_of_isZero_obj {P : ObjectProperty (DerivedCategory A)}
    [P.IsTriangulated] {M : Type*} [AddCommGroup M] {f : M →+ K0 P.FullSubcategory}
    {X : P.FullSubcategory} (h : IsZero X.obj) : clsT X ∈ AddMonoidHom.range f :=
  ⟨0, by rw [map_zero, clsT_eq_zero_of_isZero ((IsZero.iff_id_eq_zero X).2
    (P.ι.map_injective (h.eq_of_src _ _)))]⟩

/-- Additivity of the class in `K₀(P)`, read off a distinguished triangle of `D(A)` whose three
vertices are objects of a triangulated subcategory `P`. -/
private lemma clsT_eq_add_of_distTriang_ι {P : ObjectProperty (DerivedCategory A)}
    [P.IsTriangulated] {X Y Z : P.FullSubcategory} (u : X.obj ⟶ Y.obj) (v : Y.obj ⟶ Z.obj)
    (w : Z.obj ⟶ (X.obj)⟦(1 : ℤ)⟧) (hT : Triangle.mk u v w ∈ distTriang (DerivedCategory A)) :
    clsT Y = clsT X + clsT Z := by
  obtain ⟨Z', p, q, hZ'⟩ :=
    Pretriangulated.distinguished_cocone_triangle (ObjectProperty.homMk u : X ⟶ Y)
  have hadd : clsT Y = clsT X + clsT Z' := clsT_eq_add hZ'
  rw [hadd]
  refine congrArg _ (clsT_eq_of_iso (ObjectProperty.isoMk _ ?_))
  have hdist : P.ι.mapTriangle.obj (Triangle.mk (ObjectProperty.homMk u) p q) ∈
      distTriang (DerivedCategory A) := hZ'
  exact Triangle.π₃.mapIso (Pretriangulated.isoTriangleOfIso₁₂ _ _ hdist hT
    (Iso.refl _) (Iso.refl _) ((Category.comp_id _).trans (Category.id_comp u).symm))

private lemma clsT_sng_eq_add {S : ShortComplex A} (hS : S.ShortExact) :
    clsT (sng S.X₂) = clsT (sng S.X₁) + clsT (sng S.X₃) :=
  clsT_eq_add_of_distTriang_ι ((DerivedCategory.singleFunctor A 0).map S.f)
    ((DerivedCategory.singleFunctor A 0).map S.g) hS.singleδ hS.singleTriangle_distinguished

/-- The canonical homomorphism `K₀(A) ⟶ K₀(D^b(A))`, sending `[X]` to `[X[0]]`. -/
private noncomputable def toK0 : KZero A →+ Pretriangulated.K0 (DerivedCategory.Bounded A) :=
  KZero.lift (fun X => clsT (sng X)) fun _ hS => clsT_sng_eq_add hS

private lemma toK0_mk (X : A) : toK0 (KZero.mk _ X) = clsT (sng X) := KZero.lift_mk _ _ _

/-- The Euler characteristic of `X[0]` is `[X]`: the homology of `X[0]` is `X` in degree `0`
and zero elsewhere. -/
private lemma eulerChar_sng (X : A) : eulerChar (sng X).obj = KZero.mk _ X := by
  have hge : TStructure.t.IsGE (sng X).obj 0 := inferInstance
  have hle : TStructure.t.IsLE (sng X).obj 0 := inferInstance
  have h : ∀ i : ℤ, (i < 0 ∨ 0 < i) → IsZero (Hobj i (sng X).obj) := fun i hi =>
    isZero_Hobj_of_bounds hge hle i hi
  rw [eulerChar_eq_sum _ 0 0 h]
  simp only [Finset.Icc_self, Finset.sum_singleton, Int.negOnePow_zero, Units.val_one, one_smul]
  exact KZero.mk_eq_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app X)

/-- An object of `D^b(A)` whose homology is concentrated in the single degree `a` has, up to the
sign `(-1)ᵃ`, the class of an object of `A` placed in degree `0`. -/
private lemma clsT_mem_range_of_isGE_of_isLE (X : DerivedCategory.Bounded A) (a : ℤ)
    (hge : TStructure.t.IsGE X.obj a) (hle : TStructure.t.IsLE X.obj a) :
    clsT X ∈ AddMonoidHom.range (toK0 (A := A)) := by
  have h1 : TStructure.t.IsGE ((X.obj)⟦a⟧) 0 := TStructure.t.isGE_shift X.obj a a 0 (by omega)
  have h2 : TStructure.t.IsLE ((X.obj)⟦a⟧) 0 := TStructure.t.isLE_shift X.obj a a 0 (by omega)
  obtain ⟨Y, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE ((X.obj)⟦a⟧) 0
  have e' : (X⟦a⟧ : DerivedCategory.Bounded A) ≅ sng Y :=
    ObjectProperty.isoMk _ ((Bounded.ι.commShiftIso a).app X ≪≫ e)
  refine AddMonoidHom.mem_range.2 ⟨(a.negOnePow : ℤ) • KZero.mk _ Y, ?_⟩
  rw [map_zsmul, toK0_mk, ← clsT_eq_of_iso e', clsT_shift, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul]

/-- Every class of `K₀(D^b(A))` comes from `K₀(A)`: induction on the length of an interval
containing the support of the homology, peeling off the truncation triangle. -/
private lemma clsT_mem_range_aux (n : ℕ) : ∀ (X : DerivedCategory.Bounded A) (a b : ℤ),
    TStructure.t.IsGE X.obj a → TStructure.t.IsLE X.obj b → b < a + n →
    clsT X ∈ AddMonoidHom.range (toK0 (A := A)) := by
  induction n with
  | zero =>
    intro X a b hge hle hn
    exact clsT_mem_range_of_isZero_obj (TStructure.t.isZero X.obj b a (by omega))
  | succ n ih =>
    intro X a b hge hle hn
    by_cases hab : a ≤ b
    · have hge' := hge
      have hle' := hle
      have hLge : TStructure.t.IsGE ((TStructure.t.truncLE a).obj X.obj) a :=
        TStructure.t.isGE_of_iso
          ((TStructure.t.truncLEIsoTruncLT a (a + 1) rfl).app X.obj).symm a
      have hRle : TStructure.t.IsLE ((TStructure.t.truncGT a).obj X.obj) b :=
        TStructure.t.isLE_of_iso
          ((TStructure.t.truncGTIsoTruncGE a (a + 1) rfl).app X.obj).symm b
      have hsum : clsT X =
          clsT (⟨(TStructure.t.truncLE a).obj X.obj, ⟨⟨a, hLge⟩, ⟨a, inferInstance⟩⟩⟩ :
            DerivedCategory.Bounded A) +
          clsT (⟨(TStructure.t.truncGT a).obj X.obj, ⟨⟨a + 1, inferInstance⟩, ⟨b, hRle⟩⟩⟩ :
            DerivedCategory.Bounded A) :=
        clsT_eq_add_of_distTriang_ι ((TStructure.t.truncLEι a).app X.obj)
          ((TStructure.t.truncGTπ a).app X.obj) ((TStructure.t.truncGTδLE a).app X.obj)
          (TStructure.t.triangleLEGT_distinguished a X.obj)
      rw [hsum]
      exact add_mem (clsT_mem_range_of_isGE_of_isLE _ a hLge inferInstance)
        (ih _ (a + 1) b inferInstance hRle (by omega))
    · have hge' := hge
      have hle' := hle
      exact clsT_mem_range_of_isZero_obj (TStructure.t.isZero X.obj b a (by omega))

private lemma clsT_mem_range (X : DerivedCategory.Bounded A) :
    clsT X ∈ AddMonoidHom.range (toK0 (A := A)) := by
  obtain ⟨a, ha⟩ := X.property.1
  obtain ⟨b, hb⟩ := X.property.2
  exact clsT_mem_range_aux (b + 1 - a).toNat X a b ha hb (by omega)

private lemma surjective_toK0 : Function.Surjective ⇑(toK0 (A := A)) :=
  surjective_of_clsT_mem_range _ clsT_mem_range

/-- The additivity of the alternating sum of the classes of the homology objects, for a
distinguished triangle of `D^b(A)`. -/
private lemma sum_Icc_eq_of_distTriang_bounded (T : Triangle (DerivedCategory.Bounded A))
    (hT : T ∈ distTriang (DerivedCategory.Bounded A)) (a b : ℤ) (hab : a ≤ b + 1)
    (h₁ : IsZero (Hobj (b + 1) T.obj₁.obj)) (h₃ : IsZero (Hobj (a - 1) T.obj₃.obj)) :
    ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • KZero.mk _ (Hobj i T.obj₂.obj) =
      (∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • KZero.mk _ (Hobj i T.obj₁.obj)) +
        ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • KZero.mk _ (Hobj i T.obj₃.obj) :=
  sum_Icc_eq_of_distTriang (T := Bounded.ι.mapTriangle.obj T) hT a b hab h₁ h₃

/-- The Euler characteristic as a homomorphism `K₀(D^b(A)) ⟶ K₀(A)`. -/
private noncomputable def ofK0 :
    Pretriangulated.K0 (DerivedCategory.Bounded A) →+ KZero A :=
  liftCls _ (fun X => eulerChar X.obj) (by
    rintro x ⟨T, hT, rfl⟩
    simp only [map_sub, lift_of]
    obtain ⟨a, b, hab, H₁, H₂, H₃⟩ :=
      exists_interval_isZero_Hobj T.obj₁.property T.obj₂.property T.obj₃.property
    rw [eulerChar_eq_sum _ a b H₂, eulerChar_eq_sum _ a b H₁, eulerChar_eq_sum _ a b H₃,
      sum_Icc_eq_of_distTriang_bounded T hT a b hab (H₁ (b + 1) (Or.inr (by lia)))
        (H₃ (a - 1) (Or.inl (by lia)))]
    abel)

private lemma ofK0_clsT (X : DerivedCategory.Bounded A) : ofK0 (clsT X) = eulerChar X.obj :=
  liftCls_cls _ _ _ _

private lemma ofK0_comp_toK0 (y : KZero A) : ofK0 (toK0 y) = y :=
  DFunLike.congr_fun (KZero.hom_ext (F := ofK0.comp toK0) (F' := AddMonoidHom.id _)
    fun X => by rw [AddMonoidHom.comp_apply, toK0_mk, ofK0_clsT, eulerChar_sng,
      AddMonoidHom.id_apply]) y

end Bounded
open DerivedCategory in
/-- **The zeroth `K`-group of `D^b(A)` is that of `A`**: for an abelian category `A` there is a
group isomorphism from the zeroth `K`-group of `A` (the free abelian group on the objects of `A`
modulo `[X₂] - [X₁] - [X₃]` for every short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`) to the zeroth
`K`-group of the bounded derived category of `A`, sending the class of `X` to the class of `X`
viewed as a complex in degree `0`. Such an isomorphism is unique, since the classes of objects
generate `K₀(A)`. -/
@[stacks 0FCP]
theorem DerivedCategory.Bounded.exists_addEquiv_K0 {A : Type u} [Category.{v} A]
    [Abelian A] [HasDerivedCategory.{w} A] :
    ∃ e : KZero A ≃+ Pretriangulated.K0 (DerivedCategory.Bounded A),
      ∀ X : A, e (KZero.mk A X) =
        QuotientAddGroup.mk (FreeAbelianGroup.of
          (⟨(DerivedCategory.singleFunctor A 0).obj X,
            ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩⟩ : DerivedCategory.Bounded A)) := by
  refine ⟨AddEquiv.ofBijective (toK0 (A := A))
    ⟨Function.LeftInverse.injective ofK0_comp_toK0, surjective_toK0⟩,
    fun X => ?_⟩
  exact toK0_mk X

/-! ### The bounded derived category with homology in `B` -/

section Db

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (B : ObjectProperty A) [B.IsWeakSerreClass]

open DerivedCategory

/-- The object property cutting `D^b_B(A)` out of `D(A)`: the bounded objects all of whose
homology objects lie in `B`. -/
private abbrev Db : ObjectProperty (DerivedCategory A) :=
  (DerivedCategory.TStructure.t (C := A)).bounded ⊓ fun X ↦ ∀ n : ℤ, B (Hobj n X)

variable [hDb : ObjectProperty.IsTriangulated
  ((DerivedCategory.TStructure.t (C := A)).bounded ⊓
    fun X ↦ ∀ n : ℤ, B ((DerivedCategory.homologyFunctor A n).obj X))]

/-- The `i`-th homology functor `D^b_B(A) ⥤ B`. -/
private noncomputable abbrev homologyFunctorB (i : ℤ) :
    (Db B).FullSubcategory ⥤ B.FullSubcategory :=
  B.lift ((Db B).ι ⋙ DerivedCategory.homologyFunctor A i) (fun X ↦ X.property.2 i)

omit [B.IsWeakSerreClass] hDb in
private lemma isZero_homologyFunctorB_obj {i : ℤ} {X : (Db B).FullSubcategory}
    (h : IsZero (Hobj i X.obj)) : IsZero ((homologyFunctorB B i).obj X) :=
  isZero_of_isZero_obj B h

/-- The Euler characteristic `∑ᶠ i, (-1)ⁱ [Hⁱ(X)]` of an object of `D^b_B(A)`, an element of
`K₀(B)`. -/
private noncomputable def eulerCharB (X : (Db B).FullSubcategory) : KZero B.FullSubcategory :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • KZero.mk _ ((homologyFunctorB B i).obj X)

omit hDb in
private lemma eulerCharB_eq_sum (X : (Db B).FullSubcategory) (a b : ℤ)
    (h : ∀ i : ℤ, (i < a ∨ b < i) → IsZero (Hobj i X.obj)) :
    eulerCharB B X =
      ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • KZero.mk _ ((homologyFunctorB B i).obj X) := by
  exact finsum_negOnePow_smul_eq_sum _ a b fun i hi =>
    KZero.mk_eq_zero_of_isZero (isZero_homologyFunctorB_obj B (h i hi))

/-- The alternating sum of the classes of the homology objects of a distinguished triangle of
`D^b_B(A)` over an interval `[a, b]` is additive, provided the homology of `T.obj₁` vanishes in
degree `b + 1` and that of `T.obj₃` in degree `a - 1`. -/
private lemma sum_Icc_eq_of_distTriangB {T : Triangle (Db B).FullSubcategory}
    (hT : T ∈ distTriang (Db B).FullSubcategory) (a b : ℤ) (hab : a ≤ b + 1)
    (h₁ : IsZero (Hobj (b + 1) T.obj₁.obj)) (h₃ : IsZero (Hobj (a - 1) T.obj₃.obj)) :
    ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • KZero.mk _ ((homologyFunctorB B i).obj T.obj₂) =
      (∑ i ∈ Finset.Icc a b,
          (i.negOnePow : ℤ) • KZero.mk _ ((homologyFunctorB B i).obj T.obj₁)) +
        ∑ i ∈ Finset.Icc a b,
          (i.negOnePow : ℤ) • KZero.mk _ ((homologyFunctorB B i).obj T.obj₃) := by
  have hT' : (Db B).ι.mapTriangle.obj T ∈ distTriang (DerivedCategory A) := hT
  -- the maps of the long exact sequence of homology, as morphisms of `B`
  have hu : ∀ i : ℤ, (homologyFunctorB B i).map T.mor₁ ≫ (homologyFunctorB B i).map T.mor₂ = 0 :=
    fun i => by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero]
  have hvd : ∀ (i j : ℤ) (h : i + 1 = j), (homologyFunctorB B i).map T.mor₂ ≫
      (ObjectProperty.homMk (DerivedCategory.HomologySequence.δ
        ((Db B).ι.mapTriangle.obj T) i j h) :
        (homologyFunctorB B i).obj T.obj₃ ⟶ (homologyFunctorB B j).obj T.obj₁) = 0 :=
    fun i j h => ObjectProperty.hom_ext B
      (DerivedCategory.HomologySequence.comp_δ _ hT' i j h)
  have hdu : ∀ (i j : ℤ) (h : i + 1 = j),
      (ObjectProperty.homMk (DerivedCategory.HomologySequence.δ
        ((Db B).ι.mapTriangle.obj T) i j h) :
        (homologyFunctorB B i).obj T.obj₃ ⟶ (homologyFunctorB B j).obj T.obj₁) ≫
        (homologyFunctorB B j).map T.mor₁ = 0 :=
    fun i j h => ObjectProperty.hom_ext B
      (DerivedCategory.HomologySequence.δ_comp _ hT' i j h)
  have exu : ∀ i : ℤ, (ShortComplex.mk _ _ (hu i)).Exact := fun i =>
    exact_of_exact_hom B _ _ (hu i) (DerivedCategory.HomologySequence.exact₂ _ hT' i)
  have exv : ∀ (i j : ℤ) (h : i + 1 = j), (ShortComplex.mk _ _ (hvd i j h)).Exact :=
    fun i j h => exact_of_exact_hom B _ _ (hvd i j h)
      (DerivedCategory.HomologySequence.exact₃ _ hT' i j h)
  have exd : ∀ (i j : ℤ) (h : i + 1 = j), (ShortComplex.mk _ _ (hdu i j h)).Exact :=
    fun i j h => exact_of_exact_hom B _ _ (hdu i j h)
      (DerivedCategory.HomologySequence.exact₁ _ hT' i j h)
  set k : ℤ → KZero B.FullSubcategory :=
    fun i => KZero.mk _ (kernel ((homologyFunctorB B i).map T.mor₁)) with hk
  have hkd : ∀ (i j : ℤ) (h : i + 1 = j), k j =
      KZero.mk _ (Abelian.image (ObjectProperty.homMk (DerivedCategory.HomologySequence.δ
        ((Db B).ι.mapTriangle.obj T) i j h) :
        (homologyFunctorB B i).obj T.obj₃ ⟶ (homologyFunctorB B j).obj T.obj₁)) :=
    fun i j h => mk_kernel_eq_mk_image_of_exact (exd i j h)
  have key : ∀ i : ℤ, (i.negOnePow : ℤ) • KZero.mk _ ((homologyFunctorB B i).obj T.obj₂) -
      (i.negOnePow : ℤ) • KZero.mk _ ((homologyFunctorB B i).obj T.obj₁) -
      (i.negOnePow : ℤ) • KZero.mk _ ((homologyFunctorB B i).obj T.obj₃) =
      (((i + 1).negOnePow : ℤ) • k (i + 1) - (i.negOnePow : ℤ) • k i) := by
    intro i
    have hdefect := mk_sub_sub_eq (exu i) (exv i (i + 1) rfl)
    rw [← hkd i (i + 1) rfl] at hdefect
    rw [← smul_sub, ← smul_sub, hdefect]
    simp only [Int.negOnePow_succ, Units.val_neg, neg_smul, smul_neg, smul_sub, hk]
    abel
  have hga : ((a.negOnePow : ℤ) • k a) = 0 := by
    rw [hkd (a - 1) a (by omega),
      mk_image_eq_zero _ (isZero_homologyFunctorB_obj B h₃), smul_zero]
  have hgb : (((b + 1).negOnePow : ℤ) • k (b + 1)) = 0 := by
    have hkb : k (b + 1) = KZero.mk _ (kernel ((homologyFunctorB B (b + 1)).map T.mor₁)) := by
      rw [hk]
    rw [hkb, mk_kernel_eq_zero _ (isZero_homologyFunctorB_obj B h₁), smul_zero]
  exact sum_Icc_eq_add_of_telescope _ _ _ (fun i => (i.negOnePow : ℤ) • k i) a b hab key hga hgb

/-- The object `X[0]` of `D^b_B(A)` attached to an object `X` of `B`. -/
private noncomputable abbrev sngB (X : B.FullSubcategory) : (Db B).FullSubcategory :=
  ⟨(DerivedCategory.singleFunctor A 0).obj X.obj,
    ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ by
      rcases eq_or_ne n 0 with rfl | hn
      · exact B.prop_of_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app X.obj).symm X.property
      · refine B.prop_of_isZero (isZero_Hobj_of_bounds (n := 0) (m := 0) inferInstance
          inferInstance n ?_)
        rcases hn.lt_or_gt with h | h
        · exact Or.inl h
        · exact Or.inr h⟩

omit [B.IsWeakSerreClass] in
/-- The class of an object of `D^b_B(A)` whose underlying object is zero lies in the range of every
homomorphism to `K₀(D^b_B(A))`. -/
private lemma clsT_mem_rangeB_of_isZero_obj {M : Type*} [AddCommGroup M]
    {f : M →+ K0 (Db B).FullSubcategory} {X : (Db B).FullSubcategory} (h : IsZero X.obj) :
    clsT X ∈ AddMonoidHom.range f :=
  clsT_mem_range_of_isZero_obj h

omit [B.IsWeakSerreClass] in
/-- Additivity of the class in `K₀(D^b_B(A))`, read off a distinguished triangle of `D(A)` whose
three vertices are objects of `D^b_B(A)`. -/
private lemma clsT_eq_add_of_distTriang_ιB {X Y Z : (Db B).FullSubcategory} (u : X.obj ⟶ Y.obj)
    (v : Y.obj ⟶ Z.obj) (w : Z.obj ⟶ (X.obj)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u v w ∈ distTriang (DerivedCategory A)) :
    clsT Y = clsT X + clsT Z :=
  clsT_eq_add_of_distTriang_ι u v w hT

private lemma clsT_sngB_eq_add {S : ShortComplex B.FullSubcategory} (hS : S.ShortExact) :
    clsT (sngB B S.X₂) = clsT (sngB B S.X₁) + clsT (sngB B S.X₃) :=
  clsT_eq_add_of_distTriang_ιB B ((DerivedCategory.singleFunctor A 0).map S.f.hom)
    ((DerivedCategory.singleFunctor A 0).map S.g.hom) (shortExact_map_ι B hS).singleδ
    (shortExact_map_ι B hS).singleTriangle_distinguished

/-- The canonical homomorphism `K₀(B) ⟶ K₀(D^b_B(A))`, sending `[X]` to `[X[0]]`. -/
private noncomputable def toK0B :
    KZero B.FullSubcategory →+ Pretriangulated.K0 (Db B).FullSubcategory :=
  KZero.lift (fun X => clsT (sngB B X)) fun _ hS => clsT_sngB_eq_add B hS

private lemma toK0B_mk (X : B.FullSubcategory) : toK0B B (KZero.mk _ X) = clsT (sngB B X) :=
  KZero.lift_mk _ _ _

omit hDb in
/-- The Euler characteristic of `X[0]` is `[X]`: the homology of `X[0]` is `X` in degree `0`
and zero elsewhere. -/
private lemma eulerCharB_sng (X : B.FullSubcategory) : eulerCharB B (sngB B X) = KZero.mk _ X := by
  have hge : TStructure.t.IsGE (sngB B X).obj 0 := inferInstance
  have hle : TStructure.t.IsLE (sngB B X).obj 0 := inferInstance
  rw [eulerCharB_eq_sum B _ 0 0 (fun i hi => isZero_Hobj_of_bounds hge hle i hi)]
  simp only [Finset.Icc_self, Finset.sum_singleton, Int.negOnePow_zero, Units.val_one, one_smul]
  exact KZero.mk_eq_of_iso (ObjectProperty.isoMk _
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app X.obj))

/-- The Euler characteristic as a homomorphism `K₀(D^b_B(A)) ⟶ K₀(B)`. -/
private noncomputable def ofK0B :
    Pretriangulated.K0 (Db B).FullSubcategory →+ KZero B.FullSubcategory :=
  liftCls _ (fun X => eulerCharB B X) (by
    rintro x ⟨T, hT, rfl⟩
    simp only [map_sub, lift_of]
    obtain ⟨a, b, hab, H₁, H₂, H₃⟩ :=
      exists_interval_isZero_Hobj T.obj₁.property.1 T.obj₂.property.1 T.obj₃.property.1
    rw [eulerCharB_eq_sum B _ a b H₂, eulerCharB_eq_sum B _ a b H₁, eulerCharB_eq_sum B _ a b H₃,
      sum_Icc_eq_of_distTriangB B hT a b hab (H₁ (b + 1) (Or.inr (by lia)))
        (H₃ (a - 1) (Or.inl (by lia)))]
    abel)

private lemma ofK0B_clsT (X : (Db B).FullSubcategory) : ofK0B B (clsT X) = eulerCharB B X :=
  liftCls_cls _ _ _ _

private lemma ofK0B_comp_toK0B (y : KZero B.FullSubcategory) : ofK0B B (toK0B B y) = y :=
  DFunLike.congr_fun (KZero.hom_ext (F := (ofK0B B).comp (toK0B B)) (F' := AddMonoidHom.id _)
    fun X => by rw [AddMonoidHom.comp_apply, toK0B_mk, ofK0B_clsT, eulerCharB_sng,
      AddMonoidHom.id_apply]) y

/-- An object of `D^b_B(A)` whose homology is concentrated in the single degree `a` has, up to the
sign `(-1)ᵃ`, the class of an object of `B` placed in degree `0`. -/
private lemma clsT_mem_rangeB_of_isGE_of_isLE (X : (Db B).FullSubcategory) (a : ℤ)
    (hge : TStructure.t.IsGE X.obj a) (hle : TStructure.t.IsLE X.obj a) :
    clsT X ∈ AddMonoidHom.range (toK0B B) := by
  have h1 : TStructure.t.IsGE ((X.obj)⟦a⟧) 0 := TStructure.t.isGE_shift X.obj a a 0 (by omega)
  have h2 : TStructure.t.IsLE ((X.obj)⟦a⟧) 0 := TStructure.t.isLE_shift X.obj a a 0 (by omega)
  obtain ⟨Y, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE ((X.obj)⟦a⟧) 0
  have hY : B Y := B.prop_of_iso
    ((((DerivedCategory.homologyFunctor A 0).shiftIso a 0 a (by omega)).app X.obj).symm ≪≫
      (DerivedCategory.homologyFunctor A 0).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app Y) (X.property.2 a)
  have e' : (X⟦a⟧ : (Db B).FullSubcategory) ≅ sngB B ⟨Y, hY⟩ :=
    ObjectProperty.isoMk _ (((Db B).ι.commShiftIso a).app X ≪≫ e)
  refine AddMonoidHom.mem_range.2 ⟨(a.negOnePow : ℤ) • KZero.mk _ (⟨Y, hY⟩ : B.FullSubcategory), ?_⟩
  rw [map_zsmul, toK0B_mk, ← clsT_eq_of_iso e', clsT_shift, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul]

omit hDb in
/-- Every homology object of the `≤ a`-truncation of an object of `D^b_B(A)` lies in `B`: it
vanishes in degrees `> a`, and in degrees `≤ a` it is the homology of the object itself. -/
private lemma prop_homology_truncLE (X : (Db B).FullSubcategory) (a n : ℤ) :
    B (Hobj n ((TStructure.t.truncLE a).obj X.obj)) := by
  rcases le_or_gt n a with hn | hn
  · have hiso : IsIso ((DerivedCategory.homologyFunctor A n).map
        ((TStructure.t.truncLEι a).app X.obj)) :=
      isIso_homologyMap_mor₁
        (T := Triangle.mk ((TStructure.t.truncLEι a).app X.obj)
          ((TStructure.t.truncGTπ a).app X.obj) ((TStructure.t.truncGTδLE a).app X.obj))
        (TStructure.t.triangleLEGT_distinguished a X.obj) a n hn
        (fun j hj => DerivedCategory.isZero_of_isGE
          ((TStructure.t.truncGT a).obj X.obj) (a + 1) j (by omega))
    exact B.prop_of_iso (asIso ((DerivedCategory.homologyFunctor A n).map
      ((TStructure.t.truncLEι a).app X.obj))).symm (X.property.2 n)
  · exact B.prop_of_isZero (DerivedCategory.isZero_of_isLE _ a n hn)

omit hDb in
/-- Every homology object of the `> a`-truncation of an object of `D^b_B(A)` lies in `B`: it
vanishes in degrees `≤ a`, and in degrees `> a` it is the homology of the object itself. -/
private lemma prop_homology_truncGT (X : (Db B).FullSubcategory) (a n : ℤ) :
    B (Hobj n ((TStructure.t.truncGT a).obj X.obj)) := by
  rcases le_or_gt n a with hn | hn
  · exact B.prop_of_isZero (DerivedCategory.isZero_of_isGE _ (a + 1) n (by omega))
  · have hiso : IsIso ((DerivedCategory.homologyFunctor A n).map
        ((TStructure.t.truncGTπ a).app X.obj)) :=
      isIso_homologyMap_mor₂
        (T := Triangle.mk ((TStructure.t.truncLEι a).app X.obj)
          ((TStructure.t.truncGTπ a).app X.obj) ((TStructure.t.truncGTδLE a).app X.obj))
        (TStructure.t.triangleLEGT_distinguished a X.obj) a n hn
        (fun j hj => DerivedCategory.isZero_of_isLE
          ((TStructure.t.truncLE a).obj X.obj) a j hj)
    exact B.prop_of_iso (asIso ((DerivedCategory.homologyFunctor A n).map
      ((TStructure.t.truncGTπ a).app X.obj))) (X.property.2 n)

/-- Every class of `K₀(D^b_B(A))` comes from `K₀(B)`: induction on the length of an interval
containing the support of the homology, peeling off the truncation triangle. -/
private lemma clsT_mem_rangeB_aux (n : ℕ) : ∀ (X : (Db B).FullSubcategory) (a b : ℤ),
    TStructure.t.IsGE X.obj a → TStructure.t.IsLE X.obj b → b < a + n →
    clsT X ∈ AddMonoidHom.range (toK0B B) := by
  induction n with
  | zero =>
    intro X a b hge hle hn
    exact clsT_mem_rangeB_of_isZero_obj B (TStructure.t.isZero X.obj b a (by omega))
  | succ n ih =>
    intro X a b hge hle hn
    by_cases hab : a ≤ b
    · have hge' := hge
      have hle' := hle
      have hLge : TStructure.t.IsGE ((TStructure.t.truncLE a).obj X.obj) a :=
        TStructure.t.isGE_of_iso
          ((TStructure.t.truncLEIsoTruncLT a (a + 1) rfl).app X.obj).symm a
      have hRle : TStructure.t.IsLE ((TStructure.t.truncGT a).obj X.obj) b :=
        TStructure.t.isLE_of_iso
          ((TStructure.t.truncGTIsoTruncGE a (a + 1) rfl).app X.obj).symm b
      have hsum : clsT X =
          clsT (⟨(TStructure.t.truncLE a).obj X.obj, ⟨⟨a, hLge⟩, ⟨a, inferInstance⟩⟩,
            prop_homology_truncLE B X a⟩ : (Db B).FullSubcategory) +
          clsT (⟨(TStructure.t.truncGT a).obj X.obj, ⟨⟨a + 1, inferInstance⟩, ⟨b, hRle⟩⟩,
            prop_homology_truncGT B X a⟩ : (Db B).FullSubcategory) :=
        clsT_eq_add_of_distTriang_ιB B ((TStructure.t.truncLEι a).app X.obj)
          ((TStructure.t.truncGTπ a).app X.obj) ((TStructure.t.truncGTδLE a).app X.obj)
          (TStructure.t.triangleLEGT_distinguished a X.obj)
      rw [hsum]
      exact add_mem (clsT_mem_rangeB_of_isGE_of_isLE B _ a hLge inferInstance)
        (ih _ (a + 1) b inferInstance hRle (by omega))
    · have hge' := hge
      have hle' := hle
      exact clsT_mem_rangeB_of_isZero_obj B (TStructure.t.isZero X.obj b a (by omega))

private lemma surjective_toK0B : Function.Surjective ⇑(toK0B B) :=
  surjective_of_clsT_mem_range _ fun X => by
    obtain ⟨a, ha⟩ := X.property.1.1
    obtain ⟨b, hb⟩ := X.property.1.2
    exact clsT_mem_rangeB_aux B (b + 1 - a).toNat X a b ha hb (by omega)

end Db
open DerivedCategory in
/-- **The zeroth `K`-group of `D^b_B(A)` is that of `B`**: for a weak Serre subcategory `B` of an
abelian category `A` there is a group isomorphism from the zeroth `K`-group of `B` (the free
abelian group on the objects of `B` modulo `[X₂] - [X₁] - [X₃]` for every short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `B`) to the zeroth `K`-group of the triangulated subcategory
`D^b_B(A) ⊆ D(A)` of bounded objects with all cohomology objects in `B`, sending the class of `X`
to the class of `X` viewed as a complex in degree `0`. Such an isomorphism is unique, since the
classes of objects generate `K₀(B)`. -/
@[stacks 0FCS]
theorem DerivedCategory.exists_addEquiv_K0_of_isWeakSerreClass
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (B : ObjectProperty A) [B.IsWeakSerreClass]
    {P : ObjectProperty (DerivedCategory A)}
    (hP : P = (DerivedCategory.TStructure.t (C := A)).bounded ⊓
      fun X ↦ ∀ n : ℤ, B ((DerivedCategory.homologyFunctor A n).obj X))
    [P.IsTriangulated] :
    ∃ e : KZero B.FullSubcategory ≃+ Pretriangulated.K0 P.FullSubcategory,
      (∀ X : B.FullSubcategory, ∃ Y : P.FullSubcategory,
          Nonempty (P.ι.obj Y ≅ (DerivedCategory.singleFunctor A 0).obj (B.ι.obj X))) ∧
        ∀ (X : B.FullSubcategory) (Y : P.FullSubcategory),
          (P.ι.obj Y ≅ (DerivedCategory.singleFunctor A 0).obj (B.ι.obj X)) →
            e (KZero.mk B.FullSubcategory X) =
              QuotientAddGroup.mk (FreeAbelianGroup.of Y) := by
  subst hP
  refine ⟨AddEquiv.ofBijective (toK0B B)
    ⟨Function.LeftInverse.injective (ofK0B_comp_toK0B B), surjective_toK0B B⟩,
    fun X => ⟨sngB B X, ⟨Iso.refl _⟩⟩, fun X Y e => ?_⟩
  exact (toK0B_mk B X).trans (clsT_eq_of_iso (ObjectProperty.isoMk _ e)).symm

end
