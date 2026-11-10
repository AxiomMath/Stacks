module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Triangulated.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus

import StacksCore.Tactic.StacksAttribute

/-!
# Distinguished triangles in the homotopy category

This file collects the formalizations of [Stacks, Tag 014Q], [Stacks, Tag 014X], [Stacks, Tag
05RQ], [Stacks, Tag 0G6C], [Stacks, Tag 014R].

## References

* [Stacks, Tag 014Q](https://stacks.math.columbia.edu/tag/014Q)
* [Stacks, Tag 014X](https://stacks.math.columbia.edu/tag/014X)
* [Stacks, Tag 05RQ](https://stacks.math.columbia.edu/tag/05RQ)
* [Stacks, Tag 0G6C](https://stacks.math.columbia.edu/tag/0G6C)
* [Stacks, Tag 014R](https://stacks.math.columbia.edu/tag/014R)
-/

section

/-!
# Distinguished triangles in the homotopy category

Let `C` be an additive category and let `K(C)` be the homotopy category of cochain complexes of
`C`. A termwise split exact sequence of complexes is a short complex `0 → X^• → Y^• → Z^• → 0`
of cochain complexes together with, in each degree, a splitting `Y^n = X^n ⊕ Z^n` compatible
with its two maps; the connecting morphism `δ : Z^• ⟶ X^•[1]`, `δ^n = π^{n+1} ∘ d_Y^n ∘ s^n`,
makes `X^• → Y^• → Z^• → X^•[1]` a triangle of `K(C)`, the triangle associated to the sequence.
A triangle of `K(C)` is *distinguished* when it is isomorphic to one of these. The sign-free
connecting morphism is the point of the definition: it is the boundary map of the snake lemma, so
the long exact cohomology sequence of a distinguished triangle carries no signs.

The class of triangles so defined is the class of distinguished triangles of the pretriangulated
category `K(C)`, which is presented instead by mapping cones: there a triangle is distinguished
when it is isomorphic to `X^• → Y^• → cone(φ)^• → X^•[1]` for some morphism `φ : X^• ⟶ Y^•`.
Mathlib records the coincidence of the two classes, which is what identifies the definition
above with `distTriang (HomotopyCategory C (ComplexShape.up ℤ))`.

## Implementation notes

The class of triangles is not given a name of its own: `distTriang (HomotopyCategory C
(ComplexShape.up ℤ))` already denotes it, and a second name would only invite lemmas stated
against the wrong one. The membership criterion is
`HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`. The source records the same
coincidence one paragraph later, as tag 014L.

A termwise split exact sequence is a `CategoryTheory.ShortComplex (CochainComplex C ℤ)` together
with a `CategoryTheory.ShortComplex.Splitting` of each of its degreewise evaluations: the
splittings, not a separate exactness hypothesis, are what make the sequence exact, which is how
the source words it too. Its associated triangle is `CochainComplex.trianglehOfDegreewiseSplit`,
whose third map is `CochainComplex.homOfDegreewiseSplit` — the morphism `δ` of tag 011J, with
degree-`n` component `s^n ≫ d_Y^n ≫ π^{n+1}`, the source's `δ^n = π^{n+1} ∘ d_Y^n ∘ s^n` read in
diagrammatic order and with no sign.

The source's "additive" is `Preadditive C`, `HasZeroObject C` and `HasBinaryBiproducts C`; the
zero object and the biproducts are what make `K(C)` pretriangulated.

The source's `K^{+}(C)`, `K^{-}(C)` and `K^b(C)` need no separate definition: each is a full
subcategory of `K(C)` stable under the operations of a triangulated category, and the
distinguished triangles of a full subcategory are the triangles whose image in `K(C)` is
distinguished (tag 05RQ).

## References

* [Stacks project, Tag 014Q](https://stacks.math.columbia.edu/tag/014Q)
-/

@[expose] public section

-- The distinguished triangles of `K(C)` are exactly the triangles isomorphic to the triangle
-- of a termwise split exact sequence of complexes.
add_to_stacks 014Q "the distinguished triangles of the homotopy category"
  HomotopyCategory.Pretriangulated.distinguishedTriangles
add_to_sga "4½ Etat_0 1.2.2" HomotopyCategory.Pretriangulated.distinguishedTriangles
add_to_sga "6 I 1.1.5" "partial" HomotopyCategory.Pretriangulated.distinguishedTriangles
add_to_sga "4 XVII 1.1.1" "distinguished triangles"
  HomotopyCategory.Pretriangulated.distinguishedTriangles
add_to_stacks 014Q "a triangle is distinguished iff it is isomorphic to the triangle of a \
termwise split exact sequence" HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit
add_to_stacks 014Q "the triangle associated to a termwise split exact sequence"
  CochainComplex.trianglehOfDegreewiseSplit
add_to_sga "7 XIII 1.4.2" "partial" CochainComplex.trianglehOfDegreewiseSplit
add_to_sga "4½ Etat_0 1.2.4" "triangle from semi-split" CochainComplex.trianglehOfDegreewiseSplit
add_to_sga "4 XVII 1.1.1" "triangle of split seq" CochainComplex.trianglehOfDegreewiseSplit

end

end

section

/-!
# Distinguished triangles in bounded homotopy categories

For an additive functor between additive categories, this file constructs the
induced exact functors on the unbounded, bounded-below, bounded-above, and
bounded homotopy categories of cochain complexes indexed by `ℤ` (Stacks
Project, Tag 014X).

Mathlib already provides the unbounded and bounded-below constructions. The
bounded-above and bounded constructions here follow the same full-subcategory
pattern and expose their object properties, inclusions, and induced functors for
reuse.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject Pretriangulated HomotopicalAlgebra

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- The property of bounded cochain complexes. -/
def bounded (C : Type*) [Category* C] [Preadditive C] : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ a b, K.IsStrictlyGE a ∧ K.IsStrictlyLE b

omit [HasBinaryBiproducts C] in
/-- Unfolding lemma for `CochainComplex.bounded`. -/
lemma bounded_iff (K : CochainComplex C ℤ) :
    CochainComplex.bounded C K ↔ ∃ a b, K.IsStrictlyGE a ∧ K.IsStrictlyLE b := by
  unfold CochainComplex.bounded
  exact Iff.rfl

end CochainComplex

namespace HomotopyCategory

variable (C D : Type*) [Category* C] [Category* D] [Preadditive C] [Preadditive D]

variable {C} in
/-- A property of complexes holds for a complex `K` if and only if its strict image in the
homotopy category holds for the image of `K`: the quotient functor is injective on objects. -/
lemma strictMap_quotient_obj_iff {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty (HomologicalComplex C c)) (K : HomologicalComplex C c) :
    P.strictMap (quotient C c) ((quotient C c).obj K) ↔ P K := by
  refine ⟨?_, fun h ↦ ⟨_, h⟩⟩
  rw [ObjectProperty.strictMap_iff]
  rintro ⟨L, h, hL⟩
  obtain rfl : L = K := congr_arg Quotient.as hL
  exact h

variable {C} in
/-- The strict image along `HomotopyCategory.quotient` of a property of cochain
complexes that is closed under mapping cones is closed under the third object of
distinguished triangles. -/
lemma isTriangulatedClosed₃_strictMap_quotient [HasZeroObject C] [HasBinaryBiproducts C]
    (P : ObjectProperty (CochainComplex C ℤ))
    (hP : ∀ ⦃K L : CochainComplex C ℤ⦄ (f : K ⟶ L),
      P K → P L → P (CochainComplex.mappingCone f)) :
    (P.strictMap (quotient C (.up ℤ))).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨X₁, X₂, X₃, mor₁, mor₂, mor₃⟩ := T
    obtain ⟨K, rfl⟩ := X₁.quotient_obj_surjective
    obtain ⟨L, rfl⟩ := X₂.quotient_obj_surjective
    obtain ⟨f, rfl⟩ := (quotient _ _).map_surjective mor₁
    have hT' := mappingCone_triangleh_distinguished f
    unfold CochainComplex.mappingCone.triangleh CochainComplex.mappingCone.triangle at hT'
    rw [Functor.mapTriangle_obj] at hT'
    refine ObjectProperty.prop_isoClosure ?_
      (isoTriangleOfIso₁₂ _ _ hT hT' (Iso.refl _) (Iso.refl _) ?_).inv.hom₃
    · rw [Triangle.mk_obj₃, strictMap_quotient_obj_iff]
      exact hP f ((strictMap_quotient_obj_iff P K).1 h₁) ((strictMap_quotient_obj_iff P L).1 h₂)
    · simp

/-- The property of objects in the homotopy category represented by bounded-above
cochain complexes. -/
@[sga "4 XVII 2.2.10" "partial"]
def minus : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (CochainComplex.minus C).strictMap (quotient _ _)

variable {C} in
/-- The image of a cochain complex in the homotopy category is bounded above if and only if the
complex is bounded above. -/
@[simp]
lemma minus_quotient_obj_iff (K : CochainComplex C ℤ) :
    minus C ((quotient _ _).obj K) ↔ CochainComplex.minus C K := by
  unfold minus
  exact strictMap_quotient_obj_iff _ K

/-- The property `minus C` contains a zero object. -/
instance [HasZeroObject C] : (minus C).ContainsZero where
  exists_zero :=
    ⟨(quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _), by
      simp only [minus_quotient_obj_iff, CochainComplex.minus_iff]
      exact ⟨0, inferInstance⟩⟩

/-- The property `minus C` is stable under the shifts by all integers. -/
instance : (minus C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        simp only [minus_quotient_obj_iff, CochainComplex.minus_iff] at hK
        obtain ⟨q, _⟩ := hK
        rw [ObjectProperty.prop_shift_iff, shift_quotient_obj,
          minus_quotient_obj_iff, CochainComplex.minus_iff]
        exact ⟨q - n, K.isStrictlyLE_shift q n (q - n) (by lia)⟩ }

/-- The property `minus C` is closed under the third object of distinguished triangles. -/
instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (minus C).IsTriangulatedClosed₃ := by
  unfold minus
  refine isTriangulatedClosed₃_strictMap_quotient _ fun K L f hK hL ↦ ?_
  rw [CochainComplex.minus_iff] at hK hL ⊢
  obtain ⟨n₁, _⟩ := hK
  obtain ⟨n₂, _⟩ := hL
  exact ⟨max n₁ n₂, CochainComplex.isStrictlyLE_mappingCone f n₁ n₂ _⟩

/-- The property `minus C` is a triangulated subcategory. -/
instance [HasZeroObject C] [HasBinaryBiproducts C] : (minus C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- The homotopy category of bounded-above cochain complexes. -/
@[sga "4 XVII 2.2.10" "special case"]
abbrev Minus := (minus C).FullSubcategory

namespace Minus

/-- The inclusion of the bounded-above homotopy category in the unbounded one. -/
abbrev ι : Minus C ⥤ HomotopyCategory C (.up ℤ) := (minus C).ι

end Minus

/-- The property of objects in the homotopy category represented by bounded
cochain complexes. -/
@[sga "4 XVII 2.2.10" "partial"]
def bounded : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (CochainComplex.bounded C).strictMap (quotient _ _)

variable {C} in
/-- The image of a cochain complex in the homotopy category is bounded if and only if the complex
is bounded. -/
@[simp]
lemma bounded_quotient_obj_iff (K : CochainComplex C ℤ) :
    bounded C ((quotient _ _).obj K) ↔ CochainComplex.bounded C K := by
  unfold bounded
  exact strictMap_quotient_obj_iff _ K

/-- The property `bounded C` contains a zero object. -/
instance [HasZeroObject C] : (bounded C).ContainsZero where
  exists_zero :=
    ⟨(quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _), by
      simp only [bounded_quotient_obj_iff, CochainComplex.bounded_iff]
      exact ⟨0, 0, inferInstance, inferInstance⟩⟩

/-- The property `bounded C` is stable under the shifts by all integers. -/
instance : (bounded C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        simp only [bounded_quotient_obj_iff, CochainComplex.bounded_iff] at hK
        obtain ⟨a, b, _, _⟩ := hK
        rw [ObjectProperty.prop_shift_iff, shift_quotient_obj,
          bounded_quotient_obj_iff, CochainComplex.bounded_iff]
        exact ⟨a - n, b - n, K.isStrictlyGE_shift a n (a - n) (by lia),
          K.isStrictlyLE_shift b n (b - n) (by lia)⟩ }

/-- The property `bounded C` is closed under the third object of distinguished triangles. -/
instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (bounded C).IsTriangulatedClosed₃ := by
  unfold bounded
  refine isTriangulatedClosed₃_strictMap_quotient _ fun K L f hK hL ↦ ?_
  rw [CochainComplex.bounded_iff] at hK hL ⊢
  obtain ⟨a₁, b₁, _, _⟩ := hK
  obtain ⟨a₂, b₂, _, _⟩ := hL
  exact ⟨min (a₁ - 1) a₂, max b₁ b₂, CochainComplex.isStrictlyGE_mappingCone f a₁ a₂ _,
    CochainComplex.isStrictlyLE_mappingCone f b₁ b₂ _⟩

/-- The property `bounded C` is a triangulated subcategory. -/
instance [HasZeroObject C] [HasBinaryBiproducts C] : (bounded C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- The homotopy category of bounded cochain complexes. -/
@[sga "4 XVII 2.2.10" "special case"]
abbrev Bounded := (bounded C).FullSubcategory

namespace Bounded

/-- The inclusion of the bounded homotopy category in the unbounded one. -/
abbrev ι : Bounded C ⥤ HomotopyCategory C (.up ℤ) := (bounded C).ι

end Bounded

end HomotopyCategory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]

/-- An additive functor sends bounded-above cochain complexes to bounded-above cochain
complexes. -/
lemma map_minus_obj (K : CochainComplex C ℤ) (hK : CochainComplex.minus C K) :
    CochainComplex.minus D ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨n, _⟩ := hK
  exact ⟨n, inferInstance⟩

/-- An additive functor sends bounded cochain complexes to bounded cochain complexes. -/
lemma map_bounded_obj (K : CochainComplex C ℤ) (hK : CochainComplex.bounded C K) :
    CochainComplex.bounded D ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨a, b, _, _⟩ := hK
  exact ⟨a, b, inferInstance, inferInstance⟩

/-- If `F` sends complexes satisfying `P` to complexes satisfying `Q`, then `F.mapHomotopyCategory`
sends the strict image of `P` in the homotopy category into that of `Q`. -/
private lemma strictMap_quotient_mapHomotopyCategory_obj
    (P : ObjectProperty (CochainComplex C ℤ)) (Q : ObjectProperty (CochainComplex D ℤ))
    (h : ∀ K, P K → Q ((F.mapHomologicalComplex (.up ℤ)).obj K))
    (X : HomotopyCategory C (.up ℤ)) (hX : P.strictMap (HomotopyCategory.quotient C _) X) :
    Q.strictMap (HomotopyCategory.quotient D _) ((F.mapHomotopyCategory (.up ℤ)).obj X) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  rw [HomotopyCategory.strictMap_quotient_obj_iff] at hX
  exact (HomotopyCategory.strictMap_quotient_obj_iff Q _).2 (h K hX)

/-- The functor induced by `F` on homotopy categories sends bounded-above objects to
bounded-above objects. -/
lemma mapHomotopyCategoryMinus_obj (X : HomotopyCategory.Minus C) :
    HomotopyCategory.minus D
      ((HomotopyCategory.Minus.ι C ⋙ F.mapHomotopyCategory (.up ℤ)).obj X) :=
  strictMap_quotient_mapHomotopyCategory_obj F _ _ (map_minus_obj F) _ X.2

/-- The functor induced by `F` on homotopy categories sends bounded objects to bounded
objects. -/
lemma mapHomotopyCategoryBounded_obj (X : HomotopyCategory.Bounded C) :
    HomotopyCategory.bounded D
      ((HomotopyCategory.Bounded.ι C ⋙ F.mapHomotopyCategory (.up ℤ)).obj X) :=
  strictMap_quotient_mapHomotopyCategory_obj F _ _ (map_bounded_obj F) _ X.2

/-- The functor on bounded-above homotopy categories induced by an additive functor. -/
@[implicit_reducible]
def mapHomotopyCategoryMinus : HomotopyCategory.Minus C ⥤ HomotopyCategory.Minus D :=
  (HomotopyCategory.minus D).lift
    (HomotopyCategory.Minus.ι C ⋙ F.mapHomotopyCategory (.up ℤ))
    (mapHomotopyCategoryMinus_obj F)

/-- The functor `F.mapHomotopyCategoryMinus` commutes with the shifts. -/
noncomputable instance : F.mapHomotopyCategoryMinus.CommShift ℤ :=
  inferInstanceAs (((HomotopyCategory.minus D).lift
    (HomotopyCategory.Minus.ι C ⋙ F.mapHomotopyCategory (.up ℤ))
    (mapHomotopyCategoryMinus_obj F)).CommShift ℤ)

/-- **Stacks 014X (bounded above).** An additive functor induces an exact
functor on bounded-above homotopy categories of cochain complexes. -/
@[stacks 014X "bounded-above homotopy categories"]
instance isTriangulated_mapHomotopyCategoryMinus [HasZeroObject C] [HasBinaryBiproducts C]
    [HasZeroObject D] [HasBinaryBiproducts D] :
    F.mapHomotopyCategoryMinus.IsTriangulated :=
  ObjectProperty.isTriangulated_lift (HomotopyCategory.minus D)
    (HomotopyCategory.Minus.ι C ⋙ F.mapHomotopyCategory (.up ℤ))
    (mapHomotopyCategoryMinus_obj F)

/-- The functor on bounded homotopy categories induced by an additive functor. -/
@[implicit_reducible]
def mapHomotopyCategoryBounded : HomotopyCategory.Bounded C ⥤ HomotopyCategory.Bounded D :=
  (HomotopyCategory.bounded D).lift
    (HomotopyCategory.Bounded.ι C ⋙ F.mapHomotopyCategory (.up ℤ))
    (mapHomotopyCategoryBounded_obj F)

/-- The functor `F.mapHomotopyCategoryBounded` commutes with the shifts. -/
noncomputable instance : F.mapHomotopyCategoryBounded.CommShift ℤ :=
  inferInstanceAs (((HomotopyCategory.bounded D).lift
    (HomotopyCategory.Bounded.ι C ⋙ F.mapHomotopyCategory (.up ℤ))
    (mapHomotopyCategoryBounded_obj F)).CommShift ℤ)

/-- **Stacks 014X (bounded).** An additive functor induces an exact functor on
bounded homotopy categories of cochain complexes. -/
@[stacks 014X "bounded homotopy categories"]
instance isTriangulated_mapHomotopyCategoryBounded [HasZeroObject C] [HasBinaryBiproducts C]
    [HasZeroObject D] [HasBinaryBiproducts D] :
    F.mapHomotopyCategoryBounded.IsTriangulated :=
  ObjectProperty.isTriangulated_lift (HomotopyCategory.bounded D)
    (HomotopyCategory.Bounded.ι C ⋙ F.mapHomotopyCategory (.up ℤ))
    (mapHomotopyCategoryBounded_obj F)

end CategoryTheory.Functor

/-- **Stacks 014X (unbounded).** An additive functor induces an exact functor
on homotopy categories of cochain complexes. -/
@[stacks 014X "unbounded homotopy categories",
  sga "4 Vbis 2.5.1" "more general",
  sga "4 XVII 7.3.3" "special case",
  sga "6 I 1.1.5" "partial"]
theorem mapHomotopyCategory_isTriangulated
    (𝒜 𝓑 : Type*) [Category 𝒜] [Category 𝓑]
    [Preadditive 𝒜] [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜]
    [Preadditive 𝓑] [HasZeroObject 𝓑] [HasBinaryBiproducts 𝓑]
    (F : 𝒜 ⥤ 𝓑) [F.Additive] :
    (F.mapHomotopyCategory (ComplexShape.up ℤ)).IsTriangulated :=
  HomotopyCategory.instIsTriangulatedIntUpMapHomotopyCategory F

/-- **Stacks 014X (bounded below).** An additive functor induces an exact
functor on bounded-below homotopy categories of cochain complexes. -/
@[stacks 014X "bounded-below homotopy categories"]
theorem mapHomotopyCategoryPlus_isTriangulated
    (𝒜 𝓑 : Type*) [Category 𝒜] [Category 𝓑]
    [Preadditive 𝒜] [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜]
    [Preadditive 𝓑] [HasZeroObject 𝓑] [HasBinaryBiproducts 𝓑]
    (F : 𝒜 ⥤ 𝓑) [F.Additive] :
    F.mapHomotopyCategoryPlus.IsTriangulated := inferInstance

end

end

section

/-!
# Distinguished triangles in the homotopy category

Let `A` be an additive category. Inside the homotopy category `K(A)` of cochain complexes
one has the full subcategories `K⁺(A)`, `K⁻(A)` and `K^b(A)` of complexes that are bounded
below, bounded above, and bounded. Each of them contains a zero object, is stable under the
shift functors, and is closed under extensions in distinguished triangles: the cone of a
morphism between complexes that are bounded below (above, on both sides) is again bounded
below (above, on both sides). Hence all three are triangulated subcategories of `K(A)`.

A distinguished triangle of `K(A)` is, up to isomorphism, the triangle of a termwise split short
exact sequence of complexes ([Stacks, Tag 014L]); the isomorphism may moreover be taken to be the
identity on the outer terms, so that one may always *assume* the middle term of a distinguished
triangle to be an actual complex sitting in a termwise split short exact sequence between the
outer two.

## Main results

* `HomotopyCategory.isTriangulated_minus_bounded`: the object properties of
  `K(A) = HomotopyCategory A (.up ℤ)` cutting out `K⁻(A)` and `K^b(A)` are triangulated
  subcategories, in the sense of `CategoryTheory.ObjectProperty.IsTriangulated`.

* `HomotopyCategory.exists_trianglehOfDegreewiseSplit_of_distinguished`: for a distinguished
  triangle `(A^•, B, C^•, a, b, c)` of `K(A)` whose outer terms are complexes, a complex `(B')^•`
  in a termwise split short exact sequence `0 → A^n → (B')^n → C^n → 0` with connecting morphism
  `c`, together with an isomorphism `B ≅ (B')^•` carrying `a` and `b` to the two maps of that
  sequence.

For `K⁺(A)`, which is `HomotopyCategory.plus A`, this is Mathlib's
`(HomotopyCategory.plus A).IsTriangulated`; the three statements together are the content of
the source.

## Implementation notes

A subcategory given by an `ObjectProperty` is full by construction
(`ObjectProperty.FullSubcategory`, whose inclusion `ObjectProperty.ι` is fully faithful), so
"full triangulated subcategory" is `ObjectProperty.IsTriangulated`: a zero object, stability
under shift by `ℤ`, and closure under extensions, which is exactly the criterion of tag 05QX.
Closure under extensions is verified in the form `IsTriangulatedClosed₃` — the cone of a
morphism of the subcategory lies in it — which is the source's own argument,
`IsTriangulatedClosed₂` being then formal; the route through [Stacks, Tag 013N], replacing a
morphism by a termwise split injection, is the source's alternative and is not needed. Boundedness
above is inherited by cones because `(C(f))ⁿ = Kⁿ⁺¹ ⊕ Lⁿ`, so `C(f)` is bounded above by
`max (n₁ - 1) n₂` as soon as `K` is bounded above by `n₁` and `L` by `n₂`; the mirror statement for
boundedness below is Mathlib's `CochainComplex.isStrictlyGE_mappingCone`.

The properties of complexes pushed forward to `K(A)` are the ones already named:
`CochainComplex.minus A` for bounded above ([Stacks, Tag 013H]) and
`CochainComplex.plus A ⊓ CochainComplex.minus A` for bounded, the image along the quotient
functor being taken with `ObjectProperty.strictMap`, exactly as `HomotopyCategory.plus` is
defined. As for `plus`, none of the three properties is closed under isomorphisms — a complex
isomorphic in `K(A)` to a bounded one need not be bounded — which is why
`ObjectProperty.IsTriangulated` does not assume this, and it is also why `K^b(A)` is a
statement of its own rather than a consequence of `K⁺(A)` and `K⁻(A)`: the general instance
`(P ⊓ Q).IsTriangulated` asks that `Q` be closed under isomorphisms. The criterion is applied
to the conjunction directly instead, the two bounds being produced independently. Both
conclusions are class statements, and a user who wants either as an instance introduces it with
`haveI` from the corresponding conjunct.

On faithfulness to the source. (1) `Preadditive A`, `HasZeroObject A` and
`HasBinaryBiproducts A` say that `A` is additive, and they are used, not decoration: they are
what makes `K(A)` pretriangulated, hence what makes the conclusion meaningful. (2) The ambient
category is the source's: `ℤ`-indexed cochain complexes in `A` itself, up to homotopy, with its
`ℤ`-shift. (3) The source names no map, and the subcategories, rather than merely existing,
are pinned by their defining boundedness properties; the inclusions are the fully faithful
`ObjectProperty.ι`. (4) The instantiation is not degenerate: for `A = ModuleCat R` all three
properties are proper, e.g. no complex with nonzero terms in all degrees is bounded above.

On the shape of the last result. The outer terms are given as complexes `A^•`, `C^•` and the
triangle as `Triangle.mk a b c`, rather than as an abstract `T : Triangle (K A)`; this is no loss
of generality, objects of `K(A)` being complexes, and it is what lets the statement say that the
new triangle has *the same* first and third term and *the same* third map instead of only up to a
transport along an equality of objects. The conclusion is spelled as the middle isomorphism
`e : B ≅ (B')^•` together with the three equations saying that `(𝟙, e, 𝟙)` is an isomorphism of
triangles, rather than as a `Triangle` isomorphism two of whose components are asserted to be
identities: in the second form the two identities agree only definitionally, so rewriting them
away costs an unfolding of `Functor.mapTriangle`, while the three equations are stated where their
two sides are literally composable. That the new triangle is distinguished needs no separate
conjunct, being `CochainComplex.trianglehOfDegreewiseSplit_distinguished`. Two clauses are
stronger than the bare existence of an isomorphic degreewise split triangle, and both are what the
proof produces: the sequence has the given `c` as its connecting morphism
`CochainComplex.homOfDegreewiseSplit`, and the splitting is given as data rather than asserted,
which is how a termwise split sequence is packaged — the splittings, not a separate exactness
hypothesis, are what make the sequence exact. The middle term is `CochainComplex.twist φ`, the
twist of `A^•` by `C^•` along a lift `φ : C^• ⟶ A^•⟦1⟧` of `c`: the complex with `A^n ⊞ C^n` in
degree `n` and differential `(a, x) ↦ (d a + φ^n x, d x)`, the shift by `-1` of the cone on `φ`.
Both triangles being distinguished with the same outer terms and third morphism, TR3 produces a
morphism between them which is the identity on the outer terms, and the five lemma for
triangulated categories makes its middle component an isomorphism.

## References

* [Stacks project, Tag 05RQ](https://stacks.math.columbia.edu/tag/05RQ)
* [Stacks project, Tag 05QX](https://stacks.math.columbia.edu/tag/05QX)
* [Stacks project, Tag 0G6C](https://stacks.math.columbia.edu/tag/0G6C)
* [Stacks project, Tag 014L](https://stacks.math.columbia.edu/tag/014L)
-/

open CategoryTheory Limits ZeroObject Pretriangulated

@[expose] public section

namespace HomotopyCategory

section

variable {C : Type*} [Category* C] [Preadditive C]

variable [HasZeroObject C] [HasBinaryBiproducts C]

/-- **The criterion of [Stacks, Tag 05QX] for the strict image in `K(C)` of a property of
cochain complexes.** If a property `P` of `ℤ`-indexed cochain complexes holds for the zero
complex, is stable under the shifts, and holds for the mapping cone of a morphism between
complexes satisfying it, then the full subcategory of `K(C)` it cuts out is a triangulated
subcategory. -/
lemma isTriangulated_strictMap_quotient (P : ObjectProperty (CochainComplex C ℤ))
    (hzero : P 0) (hshift : ∀ (K : CochainComplex C ℤ) (n : ℤ), P K → P (K⟦n⟧))
    (hcone : ∀ {K L : CochainComplex C ℤ} (f : K ⟶ L), P K → P L →
      P (CochainComplex.mappingCone f)) :
    (P.strictMap (quotient C (ComplexShape.up ℤ))).IsTriangulated := by
  have hiff := strictMap_quotient_obj_iff (c := ComplexShape.up ℤ) P
  have : (P.strictMap (quotient C (ComplexShape.up ℤ))).ContainsZero :=
    ⟨⟨(quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _), (hiff 0).2 hzero⟩⟩
  have : (P.strictMap (quotient C (ComplexShape.up ℤ))).IsStableUnderShift ℤ :=
    ⟨fun n ↦ ⟨fun X hX ↦ by
      obtain ⟨K : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
      rw [hiff] at hX
      rw [ObjectProperty.prop_shift_iff, shift_quotient_obj, hiff]
      exact hshift _ _ hX⟩⟩
  have : (P.strictMap (quotient C (ComplexShape.up ℤ))).IsTriangulatedClosed₃ :=
    isTriangulatedClosed₃_strictMap_quotient P fun _ _ f ↦ hcone f
  exact { toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃ }

end

/-- **Stacks 05RQ.** Let `A` be an additive category. The categories `K⁻(A)` of complexes
bounded above and `K^b(A)` of bounded complexes are full triangulated subcategories of `K(A)`.
For `K⁺(A)` this is `(HomotopyCategory.plus A).IsTriangulated`. -/
@[stacks 05RQ "K⁻(A) and K^b(A); K⁺(A) is (HomotopyCategory.plus A).IsTriangulated",
  sga "6 I 1.1.5" "K^-, K^b triangulated",
  sga "4 XVII 2.2.10" "(A), special case",
  sga "4½ Etat_0 1.2.3" "(A)"]
public theorem isTriangulated_minus_bounded
    (A : Type*) [Category* A] [Preadditive A] [HasZeroObject A] [HasBinaryBiproducts A] :
    ((CochainComplex.minus A).strictMap (quotient A (ComplexShape.up ℤ))).IsTriangulated ∧
      ((CochainComplex.plus A ⊓ CochainComplex.minus A).strictMap
        (quotient A (ComplexShape.up ℤ))).IsTriangulated := by
  refine ⟨inferInstanceAs (minus A).IsTriangulated,
    isTriangulated_strictMap_quotient _ ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩ ?_ ?_⟩
  · rintro K n ⟨⟨k, _⟩, ⟨l, _⟩⟩
    exact ⟨⟨k - n, K.isStrictlyGE_shift k n _ (by lia)⟩,
      ⟨l - n, K.isStrictlyLE_shift l n _ (by lia)⟩⟩
  · rintro K L f ⟨⟨n₁, _⟩, ⟨m₁, _⟩⟩ ⟨⟨n₂, _⟩, ⟨m₂, _⟩⟩
    exact ⟨⟨min (n₁ - 1) n₂, CochainComplex.isStrictlyGE_mappingCone f n₁ n₂ _⟩,
      ⟨max (m₁ - 1) m₂, CochainComplex.isStrictlyLE_mappingCone f m₁ m₂ _⟩⟩

/-! ### Every distinguished triangle comes from a degreewise split sequence -/

section Twist

open Category CochainComplex HomologicalComplex

universe v u

/-- **A distinguished triangle of `K(𝒜)` is the triangle of a degreewise split short exact
sequence of complexes, after changing its middle term.** Let `𝒜` be an additive category and
let `(A^•, B, C^•, a, b, c)` be a distinguished triangle of `K(𝒜)` whose outer terms are the
complexes `A^•` and `C^•`. Then there are a complex `(B')^•` and maps `f : A^• ⟶ (B')^•`,
`g : (B')^• ⟶ C^•` with `f ≫ g = 0` whose degreewise evaluations
`0 → A^n → (B')^n → C^n → 0` are split short exact sequences, and an isomorphism
`e : B ≅ (B')^•` in `K(𝒜)` with `a ≫ e = f`, `e ≫ g = b` and such that `c` is the connecting
morphism of the sequence, i.e. `(𝟙, e, 𝟙)` is an isomorphism of distinguished triangles from
`(A^•, B, C^•, a, b, c)` to `(A^•, (B')^•, C^•, f, g, c)`. -/
@[stacks 0G6C,
  sga "4 XVII 1.1.1" "every antidist. arises",
  sga "4½ Etat_0 1.2.4" "ρ ess. surjective"]
public theorem exists_trianglehOfDegreewiseSplit_of_distinguished
    {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜]
    {A C : CochainComplex 𝒜 ℤ} {B : HomotopyCategory 𝒜 (ComplexShape.up ℤ)}
    (a : (quotient 𝒜 (ComplexShape.up ℤ)).obj A ⟶ B)
    (b : B ⟶ (quotient 𝒜 (ComplexShape.up ℤ)).obj C)
    (c : (quotient 𝒜 (ComplexShape.up ℤ)).obj C ⟶
      ((quotient 𝒜 (ComplexShape.up ℤ)).obj A)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a b c ∈ distTriang (HomotopyCategory 𝒜 (ComplexShape.up ℤ))) :
    ∃ (B' : CochainComplex 𝒜 ℤ) (f : A ⟶ B') (g : B' ⟶ C) (w : f ≫ g = 0)
      (σ : ∀ n, ((ShortComplex.mk f g w).map (eval 𝒜 (ComplexShape.up ℤ) n)).Splitting)
      (e : B ≅ (quotient 𝒜 (ComplexShape.up ℤ)).obj B'),
      a ≫ e.hom = (quotient 𝒜 (ComplexShape.up ℤ)).map f ∧
        e.hom ≫ (quotient 𝒜 (ComplexShape.up ℤ)).map g = b ∧
        c = (trianglehOfDegreewiseSplit (.mk f g w) σ).mor₃ := by
  -- lift `c` to a morphism of complexes `φ : C ⟶ A⟦1⟧`
  obtain ⟨φ, hφ⟩ : ∃ φ : C ⟶ A⟦(1 : ℤ)⟧,
      (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map φ ≫
        ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app A = c :=
    ⟨(HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).preimage
      (c ≫ ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).inv.app A),
      by rw [Functor.map_preimage]; simp⟩
  refine ⟨twist φ, twistι φ, twistπ φ, twistι_comp_twistπ φ, twistSplitting φ, ?_⟩
  have hmor₃ :
      (trianglehOfDegreewiseSplit (twistShortComplex φ) (twistSplitting φ)).mor₃ = c := by
    change (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map
        (homOfDegreewiseSplit (twistShortComplex φ) (twistSplitting φ)) ≫
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app A = c
    rw [homOfDegreewiseSplit_twistSplitting, hφ]
  have hT' := trianglehOfDegreewiseSplit_distinguished (twistShortComplex φ) (twistSplitting φ)
  -- the same triangle, written so that its outer terms and its third morphism are literally
  -- those of `Triangle.mk a b c`
  have heq : Triangle.mk ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map (twistι φ))
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map (twistπ φ)) c =
      trianglehOfDegreewiseSplit (twistShortComplex φ) (twistSplitting φ) := by
    rw [← hmor₃]
    rfl
  rw [heq.symm] at hT'
  obtain ⟨β, h₁, h₂⟩ := complete_distinguished_triangle_morphism₂ (Triangle.mk a b c) _ hT hT'
    (𝟙 ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj A))
    (𝟙 ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj C)) (by simp)
  have : IsIso β :=
    isIso₂_of_isIso₁₃ (T := Triangle.mk a b c)
      (T' := Triangle.mk ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map (twistι φ))
        ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map (twistπ φ)) c)
      ⟨𝟙 _, β, 𝟙 _, h₁, h₂, by simp⟩ hT hT' (by exact IsIso.id _) (by exact IsIso.id _)
  exact ⟨asIso β, by simpa using h₁, by simpa using h₂.symm, hmor₃.symm⟩

end Twist

end HomotopyCategory

end

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks Project, Tag 014R (Lemma 13.10.2), Chapter 13 "Derived Categories", Section 13.10
"Distinguished triangles in the homotopy category".

Throughout, `A` is a fixed additive category. We write `Comp(A)` for the category of cochain
complexes of `A` and `K(A)` for the homotopy category of complexes (objects: cochain complexes
of `A`; morphisms: morphisms of complexes modulo chain homotopy).

The theorem states: if `α : A → B` and `β : B → C` are termwise split injections of complexes,
then there exist complexes `Q₁, Q₂, Q₃`, morphisms `p₁ : B → Q₁`, `p₂ : C → Q₂`, `p₃ : C → Q₃`
and `d₁ : Q₁ → A[1]`, `d₂ : Q₂ → A[1]`, `d₃ : Q₃ → B[1]` in `K(A)`, such that the three triangles
`(A, B, Q₁, α, p₁, d₁)`, `(A, C, Q₂, β∘α, p₂, d₂)`, `(B, C, Q₃, β, p₃, d₃)` are distinguished
triangles of `K(A)`, and such that axiom TR4 holds for these three distinguished triangles with
respect to the composable morphisms `α` and `β`.

Supporting Stacks tags: 0144 (triangles and their morphisms), 0145 (TR4), 014Q (distinguished
triangles), 014I/011J (termwise split exact sequences and their associated triangle), 014G
(termwise split injections), 011G (shift functor).
-/

open CategoryTheory CategoryTheory.Pretriangulated

universe v u

/-- The category of cochain complexes of `A` (indexed by `ℤ`). -/
@[sga "4 XVII 0.4" "special case",
  sga "4 XVII 2.2.7" "special case",
  sga "4½ Etat_0 1.2.1",
  sga "6 I 1.1.5" "partial"]
abbrev Cpx (A : Type u) [Category.{v} A] [Preadditive A] := CochainComplex A ℤ

/-- The homotopy category `K(A)` of cochain complexes of `A`. -/
@[ega "0 20.6.26",
  sga "4 Vbis 2.5.1",
  sga "4 XVII 2.2.8" "absolute case of K(A/B)",
  sga "4½ Etat_0 1.2.2",
  sga "6 I 1.1.5" "the fiber K(C_X)"]
abbrev HoCat (A : Type u) [Category.{v} A] [Preadditive A] :=
  HomotopyCategory A (ComplexShape.up ℤ)

/-- The quotient functor `Comp(A) → K(A)`. -/
@[sga "4 XVII 2.2.8" "special case"]
noncomputable abbrev Qfun (A : Type u) [Category.{v} A] [Preadditive A] :
    Cpx A ⥤ HoCat A := HomotopyCategory.quotient A (ComplexShape.up ℤ)

-- An *additive category* is a preadditive category with all finite biproducts (this provides a
-- zero object and binary biproducts, so that "inclusion of a direct summand" makes sense). We work
-- under `[Preadditive A] [HasFiniteBiproducts A]` throughout, matching the Mathlib convention for
-- additive categories.
variable {A : Type u} [Category.{v} A] [Preadditive A] [Limits.HasFiniteBiproducts A]

-- Finite biproducts give binary biproducts, needed to build the complementary summand of a
-- composite split injection as a binary biproduct `α.compl n ⊞ β.compl n`.
/-- An additive category has binary biproducts. -/
instance : Limits.HasBinaryBiproducts A := Limits.hasBinaryBiproducts_of_finite_biproducts A

/-! ## Definition 1 (Shift functor, Stacks Tag 011G)

The shift functor `[k]` on cochain complexes is `Mathlib`'s `CochainComplex.shiftFunctor A k`,
with `A[k]^n = A^{n+k}` and `d_{A[k]}^n = (-1)^k d_A^{n+k}`. On the homotopy category `K(A)` the
induced shift is the standard `HasShift (HoCat A) ℤ` instance, written `X⟦k⟧`. These satisfy the
sign and shift conventions of Tag 011G; in particular for `k = 1` one has `d_{A[1]}^n = -
d_A^{n+1}`.
-/

/-! ## Definition 3 (Termwise split injection, Stacks Tag 014G). -/

/-- **Definition 3 (Termwise split injection, Stacks Tag 014G).**
A morphism of complexes `α : X → Y` is a (termwise) split injection if for every degree `n` the map
`α^n : X^n → Y^n` is isomorphic to the inclusion of a direct summand. In an additive category this
is genuine direct-summand data: we record, in each degree `n`, the complementary summand object
`compl n`, the retraction `retr n : Y^n → X^n` of `α^n`, the complementary inclusion
`incl n : (compl n) → Y^n` and the complementary projection `proj n : Y^n → (compl n)`, together
with the biproduct relations exhibiting `Y^n ≅ X^n ⊕ (compl n)` with `α^n : X^n → Y^n` as the first
inclusion and `retr n` as the first projection. (Equivalently, `α^n` is split mono with a chosen
direct complement.) -/
structure TermwiseSplitInj (X Y : Cpx A) where
  /-- The underlying morphism of complexes. -/
  hom : X ⟶ Y
  /-- The complementary direct summand object in degree `n`. -/
  compl : ℤ → A
  /-- A chosen degreewise retraction of `α^n`. -/
  retr : ∀ n, (Y.X n) ⟶ (X.X n)
  /-- The inclusion of the complementary summand in degree `n`. -/
  incl : ∀ n, (compl n) ⟶ (Y.X n)
  /-- The projection onto the complementary summand in degree `n`. -/
  proj : ∀ n, (Y.X n) ⟶ (compl n)
  /-- `retr` is a retraction of `α` in each degree. -/
  retr_hom : ∀ n, hom.f n ≫ retr n = 𝟙 (X.X n)
  /-- `proj` is a retraction of `incl` in each degree. -/
  proj_incl : ∀ n, incl n ≫ proj n = 𝟙 (compl n)
  /-- The two summands are orthogonal (mixed relation). -/
  retr_incl : ∀ n, incl n ≫ retr n = 0
  /-- The two summands are orthogonal (mixed relation). -/
  proj_hom : ∀ n, hom.f n ≫ proj n = 0
  /-- Completeness: `id_{Y^n} = α^n ∘ retr^n + incl^n ∘ proj^n`. -/
  total : ∀ n, retr n ≫ hom.f n + proj n ≫ incl n = 𝟙 (Y.X n)

/-! ## Definition 4 (Termwise split exact sequence and its associated triangle, Tags 014I, 011J).
-/

/-- **Definition 4 (Termwise split exact sequence of complexes, Stacks Tags 014I and 011J).**
A short complex `0 → X → Y → Z → 0` of complexes (so `β ∘ α = 0`) together with chosen direct sum
decompositions `Y^n = X^n ⊕ Z^n` compatible with `α^n` and `β^n`. The decomposition is encoded by
the section `s n : Z^n → Y^n` of `β` and the retraction `π n : Y^n → X^n` of `α`, satisfying the
biproduct relations. -/
structure TSES (A : Type u) [Category.{v} A] [Preadditive A] where
  /-- The first complex `X`. -/
  X : Cpx A
  /-- The middle complex `Y`. -/
  Y : Cpx A
  /-- The last complex `Z`. -/
  Z : Cpx A
  /-- The injection `α : X → Y`. -/
  α : X ⟶ Y
  /-- The surjection `β : Y → Z`. -/
  β : Y ⟶ Z
  /-- Degreewise section `s n : Z^n → Y^n` of `β`. -/
  s : ∀ n, (Z.X n) ⟶ (Y.X n)
  /-- Degreewise retraction `π n : Y^n → X^n` of `α`. -/
  π : ∀ n, (Y.X n) ⟶ (X.X n)
  /-- `π` is a retraction of `α` in each degree. -/
  retraction : ∀ n, α.f n ≫ π n = 𝟙 (X.X n)
  /-- `s` is a section of `β` in each degree. -/
  section_ : ∀ n, s n ≫ β.f n = 𝟙 (Z.X n)
  /-- The decomposition `id_{Y^n} = α^n π^n + β^n s^n` (i.e. `Y^n = X^n ⊕ Z^n`). -/
  decomp : ∀ n, π n ≫ α.f n + β.f n ≫ s n = 𝟙 (Y.X n)
  /-- The two summands are orthogonal: `s n ∘ π n = 0`. -/
  πs : ∀ n, s n ≫ π n = 0
  /-- `β ∘ α = 0` in each degree. -/
  βα : ∀ n, α.f n ≫ β.f n = 0

namespace TSES

/-- The associated connecting morphism `δ : Z → X[1]` of a termwise split exact sequence
(Definition 4). Its degree-`n` component is `δ^n = π^{n+1} ∘ d_Y^n ∘ s^n : Z^n → X^{n+1} = X[1]^n`.
-/
@[sga "4½ Etat_0 1.2.4"]
noncomputable def delta (T : TSES A) : T.Z ⟶ (CochainComplex.shiftFunctor A 1).obj T.X where
  f n := T.s n ≫ T.Y.d n (n + 1) ≫ T.π (n + 1)
  comm' := by
    rintro n m (rfl : n + 1 = m)
    have hT1 : T.α.f (n + 1) ≫ T.Y.d (n + 1) (n + 1 + 1) ≫ T.π (n + 1 + 1)
        = T.X.d (n + 1) (n + 1 + 1) := by
      rw [← Category.assoc, T.α.comm (n + 1) (n + 1 + 1), Category.assoc, T.retraction (n + 1 + 1),
        Category.comp_id]
    have hT2 : T.s n ≫ T.Y.d n (n + 1) ≫ T.β.f (n + 1) = T.Z.d n (n + 1) := by
      rw [← T.β.comm n (n + 1), ← Category.assoc, T.section_ n, Category.id_comp]
    have hd2 : T.Y.d n (n + 1) ≫ T.Y.d (n + 1) (n + 1 + 1) = 0 := T.Y.d_comp_d n (n + 1) (n + 1 + 1)
    have e : T.s n ≫ T.Y.d n (n + 1) ≫
        (T.π (n + 1) ≫ T.α.f (n + 1) + T.β.f (n + 1) ≫ T.s (n + 1)) ≫
          T.Y.d (n + 1) (n + 1 + 1) ≫ T.π (n + 1 + 1) = 0 := by
      rw [T.decomp (n + 1), Category.id_comp, ← Category.assoc (T.Y.d n (n + 1)), hd2]
      simp
    rw [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_add] at e
    have eq1 : T.s n ≫ T.Y.d n (n + 1) ≫ (T.π (n + 1) ≫ T.α.f (n + 1)) ≫
        T.Y.d (n + 1) (n + 1 + 1) ≫ T.π (n + 1 + 1)
        = (T.s n ≫ T.Y.d n (n + 1) ≫ T.π (n + 1)) ≫ T.X.d (n + 1) (n + 1 + 1) := by
      simp only [Category.assoc]; rw [hT1]
    have eq2 : T.s n ≫ T.Y.d n (n + 1) ≫ (T.β.f (n + 1) ≫ T.s (n + 1)) ≫
        T.Y.d (n + 1) (n + 1 + 1) ≫ T.π (n + 1 + 1)
        = T.Z.d n (n + 1) ≫ (T.s (n + 1) ≫ T.Y.d (n + 1) (n + 1 + 1) ≫ T.π (n + 1 + 1)) := by
      simp only [Category.assoc]
      rw [← Category.assoc (T.Y.d n (n + 1)), ← Category.assoc (T.s n), hT2]
    rw [eq1, eq2] at e
    have goalEq : (T.s n ≫ T.Y.d n (n + 1) ≫ T.π (n + 1)) ≫ (- T.X.d (n + 1) (n + 1 + 1))
        = T.Z.d n (n + 1) ≫ (T.s (n + 1) ≫ T.Y.d (n + 1) (n + 1 + 1) ≫ T.π (n + 1 + 1)) := by
      rw [Preadditive.comp_neg, eq_neg_of_add_eq_zero_left e, neg_neg]
    rw [CochainComplex.shiftFunctor_obj_d]
    simp only [Int.negOnePow_one, Units.neg_smul, one_smul]
    simpa only [Category.assoc] using goalEq

/-- The triangle in `K(A)` associated to a termwise split exact sequence (Definition 4):
`(X, Y, Z, α, β, δ)`, where the connecting morphism `δ : Z → X[1]` is transported across the
canonical isomorphism `Q(X[1]) ≅ Q(X)[1]` (`commShiftIso`) so that it becomes a morphism
`Q(Z) → Q(X)⟦1⟧` in `K(A)`. -/
@[sga "4½ Etat_0 1.2.4" "object assignment of ρ", sga "7 XIII 1.4.2" "partial"]
noncomputable def triangle (T : TSES A) : Triangle (HoCat A) :=
  Triangle.mk ((Qfun A).map T.α) ((Qfun A).map T.β)
    ((Qfun A).map T.delta ≫ ((Qfun A).commShiftIso (1 : ℤ)).hom.app T.X)

end TSES

/-! ## Building blocks: complementary complex and TSES from a termwise split injection.

These are the standard "kernel of the chosen retraction" constructions of Stacks Tag 014R. From a
termwise split injection `α : X → Y` (with chosen degreewise complement `α.compl n`, inclusion
`α.incl n`, projection `α.proj n`, retraction `α.retr n`) we build the complementary cochain
complex `complComplex α` (whose `n`-th object is `α.compl n` and whose differential is
`d_Q n m = incl n ≫ d_Y n m ≫ proj m`), the surjection `projHom α : Y → complComplex α`, and the
termwise split exact sequence `0 → X → Y → complComplex α → 0` as a `TSES`. -/

/-- The complementary cochain complex of a termwise split injection `α : X → Y`: in degree `n` its
object is the chosen complement `α.compl n`, and its differential is the differential of `Y`
sandwiched between the complementary inclusion and projection,
`d_Q n m = α.incl n ≫ Y.d n m ≫ α.proj m`. The `d ∘ d = 0` identity holds because the cross terms
involving `α.retr ≫ α.hom` vanish (chain-map property of `α.hom` plus `α.hom ≫ α.proj = 0`). -/
noncomputable def complComplex {X Y : Cpx A} (α : TermwiseSplitInj X Y) : Cpx A where
  X n := α.compl n
  d n m := α.incl n ≫ Y.d n m ≫ α.proj m
  shape n m h := by simp [Y.shape n m h]
  d_comp_d' i j k _ _ := by
    have key : α.proj j ≫ α.incl j = 𝟙 (Y.X j) - α.retr j ≫ α.hom.f j :=
      eq_sub_of_add_eq' (α.total j)
    simp only [Category.assoc]
    rw [reassoc_of% key]
    simp [reassoc_of% α.hom.comm j k, α.proj_hom k]

/-- The complementary projection `α.proj` assembles into a chain map `Y → complComplex α`.
The chain-map identity `proj n ≫ d_Q n m = d_Y n m ≫ proj m` reduces, via
`proj n ≫ incl n = id − retr n ≫ hom n`, to the vanishing of the `retr ≫ hom` term (again by the
chain-map property of `α.hom` and `α.hom ≫ α.proj = 0`). -/
noncomputable def projHom {X Y : Cpx A} (α : TermwiseSplitInj X Y) : Y ⟶ complComplex α where
  f n := α.proj n
  comm' n m _ := by
    have key : α.proj n ≫ α.incl n = 𝟙 (Y.X n) - α.retr n ≫ α.hom.f n :=
      eq_sub_of_add_eq' (α.total n)
    change α.proj n ≫ α.incl n ≫ Y.d n m ≫ α.proj m = Y.d n m ≫ α.proj m
    rw [reassoc_of% key]
    simp [reassoc_of% α.hom.comm n m, α.proj_hom m]

/-- The termwise split exact sequence `0 → X → Y → complComplex α → 0` associated to a termwise
split injection `α : X → Y`. All five `TSES` axioms are immediate from the `TermwiseSplitInj`
biproduct relations (`retr_hom`, `proj_incl`, `total`, `retr_incl`, `proj_hom`). -/
noncomputable def tsesOfSplitInj {X Y : Cpx A} (α : TermwiseSplitInj X Y) : TSES A where
  X := X
  Y := Y
  Z := complComplex α
  α := α.hom
  β := projHom α
  s := α.incl
  π := α.retr
  retraction := α.retr_hom
  section_ := α.proj_incl
  decomp := α.total
  πs := α.retr_incl
  βα := α.proj_hom

/-- The composite of two termwise split injections `α : X → Y` and `β : Y → Z` is again a termwise
split injection `X → Z`. The complement in degree `n` is the biproduct `α.compl n ⊞ β.compl n`;
the retraction is `β.retr n ≫ α.retr n`; the complementary inclusion sends the first summand via
`α.incl n ≫ β.hom n` and the second via `β.incl n`; the complementary projection is
`biprod.lift (β.retr n ≫ α.proj n) (β.proj n)`. The biproduct identities follow from the biproduct
relations of `α` and `β` (using `s ≫ π = 0`, `hom ≫ proj = 0`, `proj ≫ incl = id`, completeness).
-/
noncomputable def splitInj_comp {X Y Z : Cpx A}
    (α : TermwiseSplitInj X Y) (β : TermwiseSplitInj Y Z) :
    TermwiseSplitInj X Z where
  hom := α.hom ≫ β.hom
  compl n := α.compl n ⊞ β.compl n
  retr n := β.retr n ≫ α.retr n
  incl n := Limits.biprod.desc (α.incl n ≫ β.hom.f n) (β.incl n)
  proj n := Limits.biprod.lift (β.retr n ≫ α.proj n) (β.proj n)
  retr_hom n := by
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [reassoc_of% (β.retr_hom n), α.retr_hom n]
  proj_incl n := by
    refine Limits.biprod.hom_ext' _ _ (Limits.biprod.hom_ext _ _ ?_ ?_)
      (Limits.biprod.hom_ext _ _ ?_ ?_) <;>
      simp only [Limits.biprod.inl_desc_assoc, Limits.biprod.inr_desc_assoc, Category.assoc,
        Limits.biprod.lift_fst, Limits.biprod.lift_snd, Limits.biprod.inl_fst,
        Limits.biprod.inl_snd, Limits.biprod.inr_fst, Limits.biprod.inr_snd, Category.comp_id]
    · rw [reassoc_of% (β.retr_hom n), α.proj_incl n]
    · rw [β.proj_hom n, Limits.comp_zero]
    · rw [← Category.assoc, β.retr_incl n, Limits.zero_comp]
    · rw [β.proj_incl n]
  retr_incl n := by
    refine Limits.biprod.hom_ext' _ _ ?_ ?_ <;>
      simp only [Limits.biprod.inl_desc_assoc, Limits.biprod.inr_desc_assoc, Category.assoc,
        Limits.comp_zero]
    · rw [reassoc_of% (β.retr_hom n), α.retr_incl n]
    · rw [← Category.assoc, β.retr_incl n, Limits.zero_comp]
  proj_hom n := by
    simp only [HomologicalComplex.comp_f]
    refine Limits.biprod.hom_ext _ _ ?_ ?_ <;>
      simp only [Category.assoc, Limits.biprod.lift_fst, Limits.biprod.lift_snd, Limits.zero_comp]
    · rw [reassoc_of% (β.retr_hom n), α.proj_hom n]
    · rw [β.proj_hom n, Limits.comp_zero]
  total n := by
    have hα := α.total n
    have hβ := β.total n
    simp only [HomologicalComplex.comp_f]
    rw [Limits.biprod.lift_desc]
    have e1 : (β.retr n ≫ α.retr n) ≫ (α.hom.f n ≫ β.hom.f n)
        = (β.retr n ≫ (α.retr n ≫ α.hom.f n)) ≫ β.hom.f n := by simp only [Category.assoc]
    have e2 : (β.retr n ≫ α.proj n) ≫ (α.incl n ≫ β.hom.f n)
        = (β.retr n ≫ (α.proj n ≫ α.incl n)) ≫ β.hom.f n := by simp only [Category.assoc]
    rw [e1, ← add_assoc, e2, ← Preadditive.add_comp, ← Preadditive.comp_add, hα,
      Category.comp_id]
    exact hβ

/-! ## Definition 5 (Distinguished triangle in `K(A)`, Stacks Tag 014Q). -/

/-- **Definition 5 (Distinguished triangle in `K(A)`, Stacks Tag 014Q).**
A triangle of `K(A)` is distinguished if it is isomorphic, as a triangle in `K(A)`, to the triangle
associated to some termwise split exact sequence of complexes (Definition 4). -/
@[sga "4½ Etat_0 1.2.2"]
def IsDistinguished (T : Triangle (HoCat A)) : Prop :=
  ∃ S : TSES A, Nonempty (T ≅ S.triangle)

/-! ## Definition 2 (Triangle and morphism of triangles, Stacks Tag 0144).

A triangle in `K(A)` is `Mathlib`'s `Pretriangulated.Triangle (HoCat A)` (a sextuple
`(X, Y, Z, f, g, h)` with `f : X → Y`, `g : Y → Z`, `h : Z → X⟦1⟧`). A morphism of triangles is
`Mathlib`'s `Pretriangulated.TriangleMorphism`, a triple `(a, b, c)` with the commutativity
conditions `b ∘ f = f' ∘ a`, `c ∘ g = g' ∘ b`, `a⟦1⟧ ∘ h = h' ∘ c`. -/

/-! ## Definition 6 (Axiom TR4, Stacks Tag 0145), as a standalone predicate. -/

/-- **Definition 6 (Axiom TR4, Stacks Tag 0145).**
Given composable morphisms `f : X → Y` and `g : Y → Z` of `K(A)` and three distinguished triangles
`Tf = (X, Y, Q₁, f, p₁, d₁)`, `Tgf = (X, Z, Q₂, g ∘ f, p₂, d₂)`, `Tg = (Y, Z, Q₃, g, p₃, d₃)`,
the predicate `TR4Holds f g Tf Tgf Tg` asserts the existence of morphisms `a : Q₁ → Q₂` and
`b : Q₂ → Q₃` such that:

* (i) `(Q₁, Q₂, Q₃, a, b, p₁⟦1⟧ ∘ d₃)` is a distinguished triangle (closing morphism `p₁⟦1⟧ ∘ d₃`,
  as in Tag 0145);
* (ii) `(id_X, g, a)` is a morphism of triangles `Tf → Tgf`;
* (iii) `(f, id_Z, b)` is a morphism of triangles `Tgf → Tg`.

Here `f = Tf.mor₁ : X → Y` and `g = Tg.mor₁ : Y → Z` are the composable morphisms underlying the
construction (so `X = Tf.obj₁ = Tgf.obj₁`, `Y = Tf.obj₂ = Tg.obj₁`, `Z = Tgf.obj₂ = Tg.obj₂`),
passed explicitly. The triangles are passed via their three distinguished-triangle data: `Tf`,
`Tgf`, `Tg` are the `Triangle (HoCat A)` whose first/second morphisms are `f, p₁`, `g ∘ f, p₂`,
`g, p₃` respectively (with closing morphisms `d₁, d₂, d₃`). -/
def TR4Holds {X Y Z : HoCat A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (Tf Tgf Tg : Triangle (HoCat A))
    (hTf₁ : Tf.obj₁ = X) (hTf₂ : Tf.obj₂ = Y)
    (hTgf₁ : Tgf.obj₁ = X) (hTgf₂ : Tgf.obj₂ = Z)
    (hTg₁ : Tg.obj₁ = Y) (hTg₂ : Tg.obj₂ = Z) : Prop :=
  ∃ (a : Tf.obj₃ ⟶ Tgf.obj₃) (b : Tgf.obj₃ ⟶ Tg.obj₃),
    -- (i) the octahedron triangle, closing morphism `p₁⟦1⟧ ∘ d₃ = d₃ ≫ p₁⟦1⟧`.
    -- `Tg.mor₃ : Q₃ → Y⟦1⟧`, transported (`Y = Tg.obj₁ = Tf.obj₂`) and composed with
    -- `(p₁ = Tf.mor₂)⟦1⟧ : Y⟦1⟧ → Q₁⟦1⟧`.
    IsDistinguished
      (Triangle.mk a b
        (Tg.mor₃ ≫ (shiftFunctor (HoCat A) (1 : ℤ)).map
          (eqToHom hTg₁ ≫ eqToHom hTf₂.symm ≫ Tf.mor₂))) ∧
    -- (ii) `(id_X, g, a)` is a morphism of triangles `Tf → Tgf`.
    (∃ φ : Tf ⟶ Tgf,
      φ.hom₁ = (eqToHom hTf₁ ≫ eqToHom hTgf₁.symm) ∧
      φ.hom₂ = (eqToHom hTf₂ ≫ g ≫ eqToHom hTgf₂.symm) ∧ φ.hom₃ = a) ∧
    -- (iii) `(f, id_Z, b)` is a morphism of triangles `Tgf → Tg`.
    (∃ ψ : Tgf ⟶ Tg,
      ψ.hom₁ = (eqToHom hTgf₁ ≫ f ≫ eqToHom hTg₁.symm) ∧
      ψ.hom₂ = (eqToHom hTgf₂ ≫ eqToHom hTg₂.symm) ∧ ψ.hom₃ = b)

/-! ## Octahedron building blocks: the chain maps `â`, `b̂` and the octahedron `TSES`. -/

/-- The chain map `â : complComplex α → complComplex (splitInj_comp α β)`, degreewise the biproduct
inclusion `biprod.inl : α.compl n → α.compl n ⊞ β.compl n`. -/
noncomputable def octInj {Acx Bcx Ccx : Cpx A}
    (α : TermwiseSplitInj Acx Bcx) (β : TermwiseSplitInj Bcx Ccx) :
    complComplex α ⟶ complComplex (splitInj_comp α β) where
  f n := Limits.biprod.inl
  comm' := by
    intro n m _
    change Limits.biprod.inl ≫ ((splitInj_comp α β).incl n ≫ Ccx.d n m ≫ (splitInj_comp α β).proj m)
      = (α.incl n ≫ Bcx.d n m ≫ α.proj m) ≫ Limits.biprod.inl
    refine Limits.biprod.hom_ext _ _ ?_ ?_
    · simp only [splitInj_comp, Category.assoc, Limits.biprod.inl_desc_assoc,
        Limits.biprod.lift_fst, Limits.biprod.inl_fst, Category.comp_id]
      rw [reassoc_of% (β.hom.comm n m), reassoc_of% (β.retr_hom m)]
    · simp only [splitInj_comp, Category.assoc, Limits.biprod.inl_desc_assoc,
        Limits.biprod.lift_snd, Limits.biprod.inl_snd, Limits.comp_zero]
      rw [reassoc_of% (β.hom.comm n m), β.proj_hom m, Limits.comp_zero, Limits.comp_zero]

/-- The chain map `b̂ : complComplex (splitInj_comp α β) → complComplex β`, degreewise the
biproduct projection `biprod.snd : α.compl n ⊞ β.compl n → β.compl n`. -/
noncomputable def octProj {Acx Bcx Ccx : Cpx A}
    (α : TermwiseSplitInj Acx Bcx) (β : TermwiseSplitInj Bcx Ccx) :
    complComplex (splitInj_comp α β) ⟶ complComplex β where
  f n := Limits.biprod.snd
  comm' := by
    intro n m _
    change Limits.biprod.snd ≫ (β.incl n ≫ Ccx.d n m ≫ β.proj m)
      = ((splitInj_comp α β).incl n ≫ Ccx.d n m ≫ (splitInj_comp α β).proj m) ≫ Limits.biprod.snd
    refine Limits.biprod.hom_ext' _ _ ?_ ?_
    · simp only [splitInj_comp, Category.assoc, Limits.biprod.inl_snd_assoc, Limits.zero_comp,
        Limits.biprod.inl_desc_assoc, Limits.biprod.lift_snd]
      rw [reassoc_of% (β.hom.comm n m), β.proj_hom m, Limits.comp_zero, Limits.comp_zero]
    · simp only [splitInj_comp, Category.assoc, Limits.biprod.inr_snd_assoc,
        Limits.biprod.inr_desc_assoc, Limits.biprod.lift_snd]

/-- The octahedron termwise split exact sequence `0 → Q₁ → Q₂ → Q₃ → 0`, where
`Q₁ = complComplex α`, `Q₂ = complComplex (splitInj_comp α β)`, `Q₃ = complComplex β`,
with `α = octInj`, `β = octProj`, section `biprod.inr` and retraction `biprod.fst`. -/
noncomputable def octTSES {Acx Bcx Ccx : Cpx A}
    (α : TermwiseSplitInj Acx Bcx) (β : TermwiseSplitInj Bcx Ccx) : TSES A where
  X := complComplex α
  Y := complComplex (splitInj_comp α β)
  Z := complComplex β
  α := octInj α β
  β := octProj α β
  s _ := Limits.biprod.inr
  π _ := Limits.biprod.fst
  retraction n := by
    change (octInj α β).f n ≫ Limits.biprod.fst = 𝟙 _
    simp only [octInj]
    exact Limits.biprod.inl_fst
  section_ n := by
    change Limits.biprod.inr ≫ (octProj α β).f n = 𝟙 _
    simp only [octProj]
    exact Limits.biprod.inr_snd
  decomp n := by
    simp only [octInj, octProj]
    exact Limits.biprod.total
  πs n := by
    change Limits.biprod.inr ≫ Limits.biprod.fst = 0
    exact Limits.biprod.inr_fst
  βα n := by
    simp only [octInj, octProj]
    exact Limits.biprod.inl_snd

/-- Strict chain identity (TR4(ii), third square): `delta_α = octInj ≫ delta_{αβ}`. -/
theorem octInj_delta {Acx Bcx Ccx : Cpx A}
    (α : TermwiseSplitInj Acx Bcx) (β : TermwiseSplitInj Bcx Ccx) :
    (tsesOfSplitInj α).delta = octInj α β ≫ (tsesOfSplitInj (splitInj_comp α β)).delta := by
  ext n
  change α.incl n ≫ Bcx.d n (n + 1) ≫ α.retr (n + 1)
    = Limits.biprod.inl ≫ ((splitInj_comp α β).incl n ≫ Ccx.d n (n + 1) ≫
        (β.retr (n + 1) ≫ α.retr (n + 1)))
  simp only [splitInj_comp, Limits.biprod.inl_desc_assoc, Category.assoc]
  rw [reassoc_of% (β.hom.comm n (n + 1)), reassoc_of% (β.retr_hom (n + 1))]

/-- Strict chain identity (TR4(ii), second square): `projHom α ≫ octInj = β.hom ≫ projHom (αβ)`. -/
theorem projHom_octInj {Acx Bcx Ccx : Cpx A}
    (α : TermwiseSplitInj Acx Bcx) (β : TermwiseSplitInj Bcx Ccx) :
    projHom α ≫ octInj α β = β.hom ≫ projHom (splitInj_comp α β) := by
  ext n
  change α.proj n ≫ Limits.biprod.inl
    = β.hom.f n ≫ Limits.biprod.lift (β.retr n ≫ α.proj n) (β.proj n)
  refine Limits.biprod.hom_ext _ _ ?_ ?_
  · simp only [Category.assoc, Limits.biprod.inl_fst, Category.comp_id, Limits.biprod.lift_fst]
    rw [reassoc_of% (β.retr_hom n)]
  · simp only [Category.assoc, Limits.biprod.inl_snd, Limits.comp_zero, Limits.biprod.lift_snd,
      β.proj_hom n]

/-- Strict chain identity (TR4(iii), second square): `projHom (αβ) ≫ octProj = projHom β`. -/
theorem projHom_octProj {Acx Bcx Ccx : Cpx A}
    (α : TermwiseSplitInj Acx Bcx) (β : TermwiseSplitInj Bcx Ccx) :
    projHom (splitInj_comp α β) ≫ octProj α β = projHom β := by
  ext n
  change Limits.biprod.lift (β.retr n ≫ α.proj n) (β.proj n) ≫ Limits.biprod.snd = β.proj n
  simp only [Limits.biprod.lift_snd]

/-- Strict chain identity (TR4(i)): `octTSES.delta = delta_β ≫ shift (projHom α)`. -/
theorem octTSES_delta {Acx Bcx Ccx : Cpx A}
    (α : TermwiseSplitInj Acx Bcx) (β : TermwiseSplitInj Bcx Ccx) :
    (octTSES α β).delta
      = (tsesOfSplitInj β).delta ≫ (CochainComplex.shiftFunctor A 1).map (projHom α) := by
  ext n
  change Limits.biprod.inr ≫ ((splitInj_comp α β).incl n ≫ Ccx.d n (n + 1) ≫
      (splitInj_comp α β).proj (n + 1)) ≫ Limits.biprod.fst
    = (β.incl n ≫ Ccx.d n (n + 1) ≫ β.retr (n + 1)) ≫ α.proj (n + 1)
  simp only [splitInj_comp, Limits.biprod.inr_desc_assoc, Category.assoc,
    Limits.biprod.lift_fst]

/-- The chain homotopy witnessing the (homotopy-category) equality of connecting maps needed for
TR4(iii)'s third square: `octProj ≫ delta_β ≃ delta_{αβ} ≫ shift(α.hom)`.  The homotopy in degree
`i` is `biprod.fst ≫ α.incl i : Q₂^i → B^i = (B[1])^{i-1}`. -/
noncomputable def octProjDeltaHomotopy {Acx Bcx Ccx : Cpx A}
    (α : TermwiseSplitInj Acx Bcx) (β : TermwiseSplitInj Bcx Ccx) :
    Homotopy (octProj α β ≫ (tsesOfSplitInj β).delta)
      ((tsesOfSplitInj (splitInj_comp α β)).delta ≫
        (CochainComplex.shiftFunctor A 1).map α.hom) where
  hom i j :=
    if h : j + 1 = i then
      Limits.biprod.fst ≫ eqToHom (show α.compl i = α.compl (j + 1) by rw [h]) ≫ α.incl (j + 1) ≫
        eqToHom (show Bcx.X (j + 1) = ((CochainComplex.shiftFunctor A 1).obj Bcx).X j from rfl)
    else 0
  zero i j hij := by
    rw [dite_eq_right]
    intro h
    exact hij (by rw [ComplexShape.up_Rel]; exact h)
  comm i := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (k + 1) (k + 1 + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel k (k + 1) from rfl)]
    rw [dite_eq_left (show (k + 1) + 1 = k + 1 + 1 from rfl),
        dite_eq_left (show k + 1 = k + 1 from rfl)]
    rw [CochainComplex.shiftFunctor_obj_d]
    simp only [Int.negOnePow_one, Units.neg_smul, one_smul, eqToHom_refl, Category.id_comp,
      Category.comp_id, Preadditive.comp_neg]
    refine Limits.biprod.hom_ext' _ _ ?_ ?_
    · simp only [octProj, TSES.delta, tsesOfSplitInj, complComplex, splitInj_comp,
        HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f,
        Limits.biprod.inl_desc_assoc, Limits.biprod.inl_fst_assoc,
        Limits.biprod.inl_snd_assoc, Limits.zero_comp, Category.assoc, Limits.biprod.lift_fst_assoc,
        Preadditive.comp_add, Preadditive.comp_neg]
      rw [reassoc_of% (β.hom.comm (k + 1) (k + 1 + 1)), reassoc_of% (β.retr_hom (k + 1 + 1))]
      have hcr : β.hom.f (k + 1) ≫ Ccx.d (k + 1) (k + 1 + 1) ≫ β.retr (k + 1 + 1)
          = Bcx.d (k + 1) (k + 1 + 1) := by
        rw [reassoc_of% (β.hom.comm (k + 1) (k + 1 + 1)), β.retr_hom (k + 1 + 1),
          Category.comp_id]
      rw [show α.incl (k + 1) ≫ β.hom.f (k + 1) ≫ Ccx.d (k + 1) (k + 1 + 1) ≫
              β.retr (k + 1 + 1) ≫ α.retr (k + 1 + 1) ≫ α.hom.f (k + 1 + 1)
          = α.incl (k + 1) ≫ (β.hom.f (k + 1) ≫ Ccx.d (k + 1) (k + 1 + 1) ≫ β.retr (k + 1 + 1)) ≫
              α.retr (k + 1 + 1) ≫ α.hom.f (k + 1 + 1) from by simp only [Category.assoc]]
      rw [hcr]
      have htot := α.total (k + 1 + 1)
      rw [show α.incl (k + 1) ≫ Bcx.d (k + 1) (k + 1 + 1) ≫ α.retr (k + 1 + 1) ≫ α.hom.f (k + 1 + 1)
          = α.incl (k + 1) ≫ Bcx.d (k + 1) (k + 1 + 1) ≫
              (α.retr (k + 1 + 1) ≫ α.hom.f (k + 1 + 1)) from by simp only []]
      rw [show α.incl (k + 1) ≫ Bcx.d (k + 1) (k + 1 + 1) ≫
              α.proj (k + 1 + 1) ≫ α.incl (k + 1 + 1)
          = α.incl (k + 1) ≫ Bcx.d (k + 1) (k + 1 + 1) ≫
              (α.proj (k + 1 + 1) ≫ α.incl (k + 1 + 1)) from by simp only []]
      rw [show α.retr (k + 1 + 1) ≫ α.hom.f (k + 1 + 1)
          = 𝟙 _ - α.proj (k + 1 + 1) ≫ α.incl (k + 1 + 1) from by
        rw [eq_sub_iff_add_eq]; exact htot]
      simp only [Preadditive.comp_sub, Category.comp_id]
      abel
    · simp only [octProj, TSES.delta, tsesOfSplitInj, complComplex, splitInj_comp,
        HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f,
        Limits.biprod.inr_desc_assoc, Limits.biprod.inr_fst_assoc,
        Limits.biprod.inr_snd_assoc, Category.assoc, Limits.biprod.lift_fst_assoc,
        Preadditive.comp_add, Preadditive.comp_neg, Limits.zero_comp,
        ]
      have htot := α.total (k + 1 + 1)
      rw [show β.incl (k + 1) ≫ Ccx.d (k + 1) (k + 1 + 1) ≫
              β.retr (k + 1 + 1) ≫ α.proj (k + 1 + 1) ≫ α.incl (k + 1 + 1)
          = β.incl (k + 1) ≫ Ccx.d (k + 1) (k + 1 + 1) ≫ β.retr (k + 1 + 1) ≫
              (α.proj (k + 1 + 1) ≫ α.incl (k + 1 + 1)) from by simp only []]
      rw [show β.incl (k + 1) ≫ Ccx.d (k + 1) (k + 1 + 1) ≫
              β.retr (k + 1 + 1) ≫ α.retr (k + 1 + 1) ≫ α.hom.f (k + 1 + 1)
          = β.incl (k + 1) ≫ Ccx.d (k + 1) (k + 1 + 1) ≫ β.retr (k + 1 + 1) ≫
              (α.retr (k + 1 + 1) ≫ α.hom.f (k + 1 + 1)) from by simp only []]
      rw [show α.retr (k + 1 + 1) ≫ α.hom.f (k + 1 + 1)
          = 𝟙 _ - α.proj (k + 1 + 1) ≫ α.incl (k + 1 + 1) from by
        rw [eq_sub_iff_add_eq]; exact htot]
      simp only [Preadditive.comp_sub, Category.comp_id]
      abel

/-- The required octahedron triangle (TR4(i)) coincides with `(octTSES α β).triangle`.  This is
the equality of closing morphisms `(Q(delta_β) ≫ ε_B) ≫ (Q(projHom α))⟦1⟧ = Q(octTSES.delta) ≫
ε_{Q₁}`,
which follows from the strict identity `octTSES_delta` and naturality of `commShiftIso`. -/
theorem octClosing {Acx Bcx Ccx : Cpx A}
    (α : TermwiseSplitInj Acx Bcx) (β : TermwiseSplitInj Bcx Ccx) :
    ((Qfun A).map (tsesOfSplitInj β).delta ≫ ((Qfun A).commShiftIso (1 : ℤ)).hom.app Bcx) ≫
        (shiftFunctor (HoCat A) (1 : ℤ)).map ((Qfun A).map (projHom α))
      = (Qfun A).map (octTSES α β).delta ≫ ((Qfun A).commShiftIso (1 : ℤ)).hom.app (complComplex
          α) := by
  rw [octTSES_delta α β, Functor.map_comp, Category.assoc,
    ← Functor.commShiftIso_hom_naturality (Qfun A) (projHom α) (1 : ℤ), ← Category.assoc]
  rfl

/-! ## TR4 sub-lemma (the octahedron verification, Stacks Tag 014R / 0145).

This is the substantive computational content of Tag 014R, isolated as a named sub-lemma to be
discharged in the formal phase. With the canonical witnesses built above
(`Q₁ = complComplex α`, `Q₂ = complComplex (splitInj_comp α β)`, `Q₃ = complComplex β`,
`pᵢ = Q(projHom …)`, `dᵢ = Q(delta …) ≫ commShiftIso`), TR4 requires:

* **The maps `a : Q(Q₁) → Q(Q₂)` and `b : Q(Q₂) → Q(Q₃)`.** Degreewise, with the identifications
  `B^n = A^n ⊕ Q₁^n`, `C^n = B^n ⊕ Q₃^n = A^n ⊕ Q₁^n ⊕ Q₃^n` and `Q₂^n = Q₁^n ⊕ Q₃^n` (the latter
  is the chosen biproduct in `splitInj_comp`), `a^n : Q₁^n → Q₂^n` is the biproduct inclusion
  `biprod.inl` of the first summand and `b^n : Q₂^n → Q₃^n` is the biproduct projection
  `biprod.snd` onto the second summand. Both are chain maps (they commute with the differentials
  induced by `d_B`, `d_C` on the complementary summands — a direct biproduct computation using the
  block form of the differentials) and we take `a := Q(â)`, `b := Q(b̂)` for these complex maps
  `â : Q₁ → Q₂`, `b̂ : Q₂ → Q₃`.

* **TR4(i): the triangle `(Q₁, Q₂, Q₃, a, b, p₁⟦1⟧ ∘ d₃)` is distinguished.** The sequence
  `0 → Q₁ →(â) Q₂ →(b̂) Q₃ → 0` is termwise split exact: in each degree it is the split biproduct
  `Q₂^n = Q₁^n ⊕ Q₃^n` with section `Q₃^n → Q₂^n = biprod.inr` and retraction
  `Q₂^n → Q₁^n = biprod.fst`. Assemble these into a `TSES` `Soct` (a routine biproduct check, like
  `tsesOfSplitInj`). Its associated triangle `Soct.triangle` has closing morphism `Q(Soct.delta) ≫
  commShiftIso`. The required closing morphism is `d₃ ≫ p₁⟦1⟧` (i.e. `p₁⟦1⟧ ∘ d₃`), the composite
  `Q₃ →(d₃) B⟦1⟧ →(p₁⟦1⟧ = Q(projHom α)⟦1⟧) Q₁⟦1⟧`. The key identity to verify is the equality (in
  `K(A)`, i.e. up to homotopy — here even on the nose) of the two connecting maps:
  `Soct.delta = projHom α ∘ (delta of the C-row restricted to Q₃) ∘ (section)`, which unwinds to
  the degreewise computation `biprod.fst ∘ d_{Q₂} ∘ biprod.inr = α.proj ∘ d_C ∘ (Q₃ section)` after
  transport across `commShiftIso`. This is the equality of connecting morphisms of the bottom row
  of the 3×3 diagram of Tag 014R. Then TR4(i) is `⟨Soct, ⟨e⟩⟩` where `e` is the triangle
  isomorphism identifying the closing maps (identity on `Q₁, Q₂, Q₃`, using the connecting-map
  identity for the third square).

* **TR4(ii): `(id_{Q(A)}, Q(β), a)` is a morphism of triangles `T₁ → T₂`.** The three squares:
  `Q(β) ∘ Q(α) = Q(β∘α) ∘ id` (functoriality), `a ∘ p₁ = p₂ ∘ Q(β)` (degreewise:
  `biprod.inl ∘ α.proj = (splitInj_comp).proj ∘ β.hom` — i.e. the first component is `α.proj` and
  the second `β.proj ∘ β.hom = 0`-after-projection; holds by the block form), and
  `id⟦1⟧ ∘ d₁ = d₂ ∘ a` (the connecting maps agree, top two rows of the 3×3 diagram). Build the
  `TriangleMorphism` with `hom₁ = id`, `hom₂ = Q(β)`, `hom₃ = a` and discharge the three `comm`
  fields by `Q`-functoriality and the degreewise biproduct identities.

* **TR4(iii): `(Q(α), id_{Q(C)}, b)` is a morphism of triangles `T₂ → T₃`.** Symmetric to (ii):
  `id ∘ Q(β∘α) = Q(β) ∘ Q(α)`, `b ∘ p₂ = p₃ ∘ id` (degreewise `biprod.snd ∘ (splitInj_comp).proj =
  β.proj`), and `Q(α)⟦1⟧ ∘ d₂ = d₃ ∘ b` (connecting maps, bottom two rows). Build the
  `TriangleMorphism` with `hom₁ = Q(α)`, `hom₂ = id`, `hom₃ = b`.

All three reduce to (a) chain-map / biproduct identities in `A` and (b) functoriality of `Q` and
naturality of `commShiftIso`; no homotopies beyond equalities of complex maps are needed because
the construction is strict (the 3×3 diagram commutes on the nose). The lemma is left unproved for
the formal phase. -/
/-- For termwise split injections `α : Acx → Bcx` and `β : Bcx → Ccx`, axiom TR4 holds for the
distinguished triangles of `K(A)` attached to `α`, to `splitInj_comp α β` and to `β`, with respect
to the composable morphisms `Q(α)` and `Q(β)`. -/
theorem tr4Holds_of_termwiseSplitInj
    {Acx Bcx Ccx : Cpx A}
    (α : TermwiseSplitInj Acx Bcx) (β : TermwiseSplitInj Bcx Ccx) :
    TR4Holds ((Qfun A).map α.hom) ((Qfun A).map β.hom)
      (Triangle.mk ((Qfun A).map α.hom) ((Qfun A).map (projHom α))
        ((Qfun A).map (tsesOfSplitInj α).delta ≫ ((Qfun A).commShiftIso (1 : ℤ)).hom.app Acx))
      (Triangle.mk ((Qfun A).map (α.hom ≫ β.hom)) ((Qfun A).map (projHom (splitInj_comp α β)))
        ((Qfun A).map (tsesOfSplitInj (splitInj_comp α β)).delta ≫
          ((Qfun A).commShiftIso (1 : ℤ)).hom.app Acx))
      (Triangle.mk ((Qfun A).map β.hom) ((Qfun A).map (projHom β))
        ((Qfun A).map (tsesOfSplitInj β).delta ≫ ((Qfun A).commShiftIso (1 : ℤ)).hom.app Bcx))
      rfl rfl rfl rfl rfl rfl := by
  refine ⟨(Qfun A).map (octInj α β), (Qfun A).map (octProj α β), ?_, ?_, ?_⟩
  · -- TR4(i): the octahedron triangle is `(octTSES α β).triangle`, up to the closing-map identity.
    refine ⟨octTSES α β, ⟨?_⟩⟩
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp [TSES.triangle, octTSES]
    · simp [TSES.triangle, octTSES]
    · -- closing-map square
      simp only [Triangle.mk, TSES.triangle, Iso.refl_hom, CategoryTheory.Functor.map_id,
        Category.comp_id, Category.id_comp, eqToHom_refl]
      exact octClosing α β
  · -- TR4(ii): (id, Q(β), a) is a morphism of triangles.
    refine ⟨TriangleMorphism.mk (𝟙 _) ((Qfun A).map β.hom) ((Qfun A).map (octInj α β)) ?_ ?_ ?_,
      ?_, ?_, ?_⟩
    · -- comm₁: Q(α.hom) ≫ Q(β.hom) = id ≫ Q(α.hom ≫ β.hom)
      simp only [Triangle.mk_mor₁, Category.id_comp, ← Functor.map_comp]
    · -- comm₂: Q(projHom α) ≫ Q(octInj) = Q(β.hom) ≫ Q(projHom (αβ))
      simp only [Triangle.mk_mor₂, ← Functor.map_comp, projHom_octInj]
    · -- comm₃: (Q(delta_α) ≫ ε_A) ≫ id⟦1⟧ = Q(octInj) ≫ (Q(delta_{αβ}) ≫ ε_A)
      simp only [Triangle.mk_mor₃, CategoryTheory.Functor.map_id,
        Category.comp_id]
      rw [← Category.assoc, ← Functor.map_comp, ← octInj_delta]
    · simp only [eqToHom_refl, Category.comp_id]
    · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    · rfl
  · -- TR4(iii): (Q(α), id, b) is a morphism of triangles.
    refine ⟨TriangleMorphism.mk ((Qfun A).map α.hom) (𝟙 _) ((Qfun A).map (octProj α β)) ?_ ?_ ?_,
      ?_, ?_, ?_⟩
    · -- comm₁: Q(α.hom ≫ β.hom) ≫ id = Q(α.hom) ≫ Q(β.hom)
      simp only [Triangle.mk_mor₁, Category.comp_id, ← Functor.map_comp]
    · -- comm₂: Q(projHom (αβ)) ≫ Q(octProj) = id ≫ Q(projHom β)
      simp only [Triangle.mk_mor₂, Category.id_comp, ← Functor.map_comp, projHom_octProj]
    · -- comm₃: (Q(delta_{αβ}) ≫ ε_A) ≫ Q(α)⟦1⟧ = Q(octProj) ≫ (Q(delta_β) ≫ ε_B)
      have hH : (Qfun A).map (octProj α β ≫ (tsesOfSplitInj β).delta)
          = (Qfun A).map ((tsesOfSplitInj (splitInj_comp α β)).delta ≫
              (CochainComplex.shiftFunctor A 1).map α.hom) :=
        HomotopyCategory.eq_of_homotopy _ _ (octProjDeltaHomotopy α β)
      simp only [Triangle.mk_mor₃]
      rw [Category.assoc, ← Functor.commShiftIso_hom_naturality (Qfun A) α.hom (1 : ℤ),
        ← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
      congr 1
      exact hH.symm
    · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    · simp only [eqToHom_refl, Category.comp_id]
    · rfl

/-! ## Main Statement (Stacks Tag 014R, Lemma 13.10.2). -/

/-- **Theorem (Stacks Tag 014R, Lemma 13.10.2).**
Let `A` be an additive category and let `α : Acx → Bcx` and `β : Bcx → Ccx` be termwise split
injections of complexes. Then there exist complexes `Q₁ Q₂ Q₃` of `A`, morphisms
`p₁ : Q(Bcx) → Q(Q₁)`, `p₂ : Q(Ccx) → Q(Q₂)`, `p₃ : Q(Ccx) → Q(Q₃)` and connecting morphisms
`d₁ : Q(Q₁) → Q(Acx)⟦1⟧`, `d₂ : Q(Q₂) → Q(Acx)⟦1⟧`, `d₃ : Q(Q₃) → Q(Bcx)⟦1⟧` in `K(A)` such that:

* the three triangles
  `(Q(Acx), Q(Bcx), Q(Q₁), Q(α), p₁, d₁)`,
  `(Q(Acx), Q(Ccx), Q(Q₂), Q(β ∘ α), p₂, d₂)`,
  `(Q(Bcx), Q(Ccx), Q(Q₃), Q(β), p₃, d₃)`
  are distinguished triangles of `K(A)`; and

* axiom TR4 (Definition 6) holds for these three distinguished triangles with respect to the
  composable morphisms `Q(α)` and `Q(β)`. -/
@[stacks 014R]
theorem exists_octahedron_of_termwiseSplitInj
    {Acx Bcx Ccx : Cpx A}
    (α : TermwiseSplitInj Acx Bcx) (β : TermwiseSplitInj Bcx Ccx) :
    ∃ (Q₁ Q₂ Q₃ : Cpx A)
      (p₁ : (Qfun A).obj Bcx ⟶ (Qfun A).obj Q₁)
      (p₂ : (Qfun A).obj Ccx ⟶ (Qfun A).obj Q₂)
      (p₃ : (Qfun A).obj Ccx ⟶ (Qfun A).obj Q₃)
      (d₁ : (Qfun A).obj Q₁ ⟶ ((Qfun A).obj Acx)⟦(1 : ℤ)⟧)
      (d₂ : (Qfun A).obj Q₂ ⟶ ((Qfun A).obj Acx)⟦(1 : ℤ)⟧)
      (d₃ : (Qfun A).obj Q₃ ⟶ ((Qfun A).obj Bcx)⟦(1 : ℤ)⟧),
      -- The three distinguished triangles `(X, Y, Q(Q_i), f, p_i, d_i)`.
      letI T₁ : Triangle (HoCat A) := Triangle.mk ((Qfun A).map α.hom) p₁ d₁
      letI T₂ : Triangle (HoCat A) := Triangle.mk ((Qfun A).map (α.hom ≫ β.hom)) p₂ d₂
      letI T₃ : Triangle (HoCat A) := Triangle.mk ((Qfun A).map β.hom) p₃ d₃
      IsDistinguished T₁ ∧ IsDistinguished T₂ ∧ IsDistinguished T₃ ∧
      -- Axiom TR4 (Definition 6) for these three distinguished triangles, with respect to the
      -- composable morphisms `f = Q(α) : Q(Acx) → Q(Bcx)` and `g = Q(β) : Q(Bcx) → Q(Ccx)`.
      TR4Holds ((Qfun A).map α.hom) ((Qfun A).map β.hom) T₁ T₂ T₃
        rfl rfl rfl rfl rfl rfl := by
  refine ⟨complComplex α, complComplex (splitInj_comp α β), complComplex β,
    (Qfun A).map (projHom α), (Qfun A).map (projHom (splitInj_comp α β)),
    (Qfun A).map (projHom β),
    (Qfun A).map (tsesOfSplitInj α).delta ≫ ((Qfun A).commShiftIso (1 : ℤ)).hom.app Acx,
    (Qfun A).map (tsesOfSplitInj (splitInj_comp α β)).delta ≫
      ((Qfun A).commShiftIso (1 : ℤ)).hom.app Acx,
    (Qfun A).map (tsesOfSplitInj β).delta ≫ ((Qfun A).commShiftIso (1 : ℤ)).hom.app Bcx,
    ?_, ?_, ?_, ?_⟩
  · -- T₁ is distinguished: it is definitionally `(tsesOfSplitInj α).triangle`.
    exact ⟨tsesOfSplitInj α, ⟨Iso.refl _⟩⟩
  · -- T₂ is distinguished: it is `(tsesOfSplitInj (splitInj_comp α β)).triangle`.
    exact ⟨tsesOfSplitInj (splitInj_comp α β), ⟨Iso.refl _⟩⟩
  · -- T₃ is distinguished: it is `(tsesOfSplitInj β).triangle`.
    exact ⟨tsesOfSplitInj β, ⟨Iso.refl _⟩⟩
  · -- Axiom TR4 for the three triangles built above (Stacks Tag 014R octahedron); see
    -- `tr4Holds_of_termwiseSplitInj` for the detailed construction of `a`, `b`, the octahedron
    -- `TSES`, and the
    -- two triangle morphisms.
    exact tr4Holds_of_termwiseSplitInj α β

end

end

add_to_sga "4 XVII 1.1.1" "distinguished <=> split"
  HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit

add_to_sga "4½ Etat_0 1.2.4" "ρ essentially surjective"
  HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit
