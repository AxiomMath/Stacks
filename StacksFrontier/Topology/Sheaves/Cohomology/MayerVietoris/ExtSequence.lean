module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.MayerVietorisTriangle
import StacksCore.Tactic.StacksAttribute

/-!
# The unbounded Mayer--Vietoris sequence of Ext groups

Let `X` be a ringed space which is the union of two open subspaces `U` and `V`, and let `E`
and `F` be objects of the unbounded derived category `D(𝒪_X)`. Stacks 08BW is the
Mayer--Vietoris long exact sequence

`⋯ ⟶ Ext⁻¹(E|_{U∩V}, F|_{U∩V}) ⟶ Hom(E, F) ⟶ Hom(E|_U, F|_U) ⊕ Hom(E|_V, F|_V) ⟶
  Hom(E|_{U∩V}, F|_{U∩V}) ⟶ ⋯`

running in every integer degree. It is obtained by applying the cohomological functor
`Hom(-, F⟦n⟧)` to the Mayer--Vietoris distinguished triangle of Stacks 08BU.

## Main definitions

* `CategoryTheory.Pretriangulated.triangleShiftedHomδ` and
  `CategoryTheory.Pretriangulated.biprodTriangleShiftedHomδ`: the connecting homomorphism
  `Ext^{n₀}(T.obj₁, F) ⟶ Ext^{n₁}(T.obj₃, F)` of the contravariant long exact sequence of a
  triangle `T`, in general and for a triangle with binary biproduct middle term.
* `Stacks.ExtensionByZero.derivedRestriction` and
  `Stacks.ExtensionByZero.derivedExtensionRestriction`: restriction to an open subspace, and
  extension by zero of that restriction, on the unbounded derived categories.
* `Stacks.ExtensionByZero.extensionRestrictionExtEquiv`: the identification of
  `Ext^n_X(j_{U!}(E|_U), F)` with `Ext^n_U(E|_U, F|_U)` coming from Stacks 08BT.

## Main results

* In `CategoryTheory.Pretriangulated`, the three lemmas
  `exact_restriction_difference_of_distTriang`,
  `exact_difference_biprodTriangleShiftedHomδ_of_distTriang` and
  `exact_biprodTriangleShiftedHomδ_restriction_of_distTriang`: exactness at the three spots
  of the contravariant sequence of shifted morphism groups attached to a distinguished
  triangle whose middle term is a binary biproduct.
* `Stacks.ExtensionByZero.distinguished_derivedExtensionRestriction_triangle`: **Stacks
  08BU** at the presentation of the three derived functors built here, so with no derived
  functor and no comparison supplied from outside.
* `Stacks.ExtensionByZero.exists_mayerVietoris_ext_longExactSequence`: **Stacks 08BW**, the
  Mayer--Vietoris long exact sequence whose terms are the Ext groups of the restrictions in
  the derived categories of the two opens and of their intersection.
* `Stacks.ExtensionByZero.exists_mayerVietoris_hom_longExactSequence`: **Stacks 08BW** in the
  form the triangle of Stacks 08BU produces it, with the terms the groups of morphisms in
  `D(𝒪_X)` out of the extensions by zero, and with the maps of the sequence given explicitly
  by the canonical derived adjunction counits and the comparison maps of Stacks 08BU.
* `Stacks.ExtensionByZero.exists_mayerVietoris_ext_longExactSequence_restrictions`, in
  `StacksFrontier/Topology/Sheaves/Cohomology/MayerVietoris/ExtSequenceRestrictions.lean`:
  **Stacks 08BW** with every map of the sequence described -- the first map is the pair of the
  restrictions to the two opens and the second is a difference of two restrictions to their
  intersection.

## Implementation notes

For an object `F` of a pretriangulated category, `Hom(-, F⟦n⟧)` is the shift sequence of the
homological functor `CategoryTheory.preadditiveYoneda.obj F` on the opposite category, so the
three exactness statements are the three exactness lemmas of a homological functor applied to
the opposite of the triangle. The middle term of the Mayer--Vietoris triangle is a binary
biproduct, and `Hom(A ⊞ B, Z)` is transported to `Hom(A, Z) × Hom(B, Z)`; under that
transport the first map of the sequence becomes the pair of the two restrictions and the
second becomes their difference, which is the shape displayed in the source.

The triangle of Stacks 08BU produces the three terms as groups of morphisms in `D(𝒪_X)` out
of the extensions by zero of the restrictions of `E`. Those are turned into the Ext groups of
the source by the derived adjunction `D(j_!) ⊣ D(j^*)` of Stacks 08BT, which gives
`Ext^n_X(j_{U!}(E|_U), F) ≃ Ext^n_U(E|_U, F|_U)` once the shift is moved through `D(j^*)` by
its commutation isomorphism. For that the triangle is taken at the concrete functors
`D(j_!) ∘ D(j^*)`, which are right derived functors of the degreewise `j_! j^*` because
`j^*` and `j_!` are exact and each induced functor on the derived category is induced by the
degreewise one on the homotopy category.

In `exists_mayerVietoris_hom_longExactSequence` the three derived functors and their units
are quantified over rather than fixed, as in Stacks 08BU, so that statement applies to every
choice of them; its restriction and difference maps are given explicitly, in terms of the
canonical derived adjunction counits of Stacks 08BT and of the two comparison maps out of the
intersection term, which carry the Mayer--Vietoris sign. In
`exists_mayerVietoris_ext_longExactSequence` the three maps are existentially quantified
without being described: they are the maps of the former statement conjugated by the
identifications of Stacks 08BT. Recording that in the statement needs the counit used by
Stacks 08BU to be the counit of the derived adjunction of Stacks 08BT, which is
`Stacks.ExtensionByZero.derivedExtensionRestrictionCanonicalCounit_eq` in
`StacksFrontier/Topology/Sheaves/Cohomology/MayerVietoris/ExtSequenceRestrictions.lean`; the
sequence with all of its maps described is
`Stacks.ExtensionByZero.exists_mayerVietoris_ext_longExactSequence_restrictions` there.

## References

* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
* [Stacks Project, Tag 08BU](https://stacks.math.columbia.edu/tag/08BU)
* [Stacks Project, Tag 08BT](https://stacks.math.columbia.edu/tag/08BT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open ExtensionByZeroModules

universe u

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ]

/-- Precomposition with `f : X ⟶ Y`, as a homomorphism of the groups of morphisms into a
shift of `F`: the map `Ext^n(Y, F) ⟶ Ext^n(X, F)` induced by `f`. -/
public def shiftedHomPrecomp {X Y : C} (f : X ⟶ Y) (F : C) (n : ℤ) :
    (Y ⟶ F⟦n⟧) →+ (X ⟶ F⟦n⟧) :=
  AddMonoidHom.mk' (fun x => f ≫ x) fun _ _ => by simp

/-- `shiftedHomPrecomp f F n` sends `x` to `f ≫ x`. -/
@[simp]
public lemma shiftedHomPrecomp_apply {X Y : C} (f : X ⟶ Y) (F : C) (n : ℤ) (x : Y ⟶ F⟦n⟧) :
    shiftedHomPrecomp f F n x = f ≫ x := rfl

/-- The group of morphisms out of a binary biproduct is the product of the groups of
morphisms out of the two summands. -/
public def shiftedHomBiprodEquiv (A B Z : C) [HasBinaryBiproduct A B] :
    (A ⊞ B ⟶ Z) ≃+ ((A ⟶ Z) × (B ⟶ Z)) where
  toFun z := (biprod.inl ≫ z, biprod.inr ≫ z)
  invFun w := biprod.desc w.1 w.2
  left_inv _ := by apply biprod.hom_ext' <;> simp
  right_inv _ := by simp
  map_add' _ _ := by simp

/-- The pair of the two restrictions `Ext^n(Z, F) ⟶ Ext^n(A, F) × Ext^n(B, F)` along
`r : A ⟶ Z` and `s : B ⟶ Z`. -/
public def shiftedHomRestriction {A B Z : C} (r : A ⟶ Z) (s : B ⟶ Z) (F : C) (n : ℤ) :
    (Z ⟶ F⟦n⟧) →+ ((A ⟶ F⟦n⟧) × (B ⟶ F⟦n⟧)) :=
  AddMonoidHom.mk' (fun x => (r ≫ x, s ≫ x)) fun _ _ => by simp

/-- `shiftedHomRestriction r s F n` sends `x` to the pair `(r ≫ x, s ≫ x)`. -/
@[simp]
public lemma shiftedHomRestriction_apply {A B Z : C} (r : A ⟶ Z) (s : B ⟶ Z) (F : C) (n : ℤ)
    (x : Z ⟶ F⟦n⟧) : shiftedHomRestriction r s F n x = (r ≫ x, s ≫ x) := rfl

/-- The sum `Ext^n(A, F) × Ext^n(B, F) ⟶ Ext^n(Y, F)` of the maps induced by `p : Y ⟶ A` and
`q : Y ⟶ B`; it is a difference when `q` carries the Mayer--Vietoris sign. -/
public def shiftedHomDifference {A B Y : C} (p : Y ⟶ A) (q : Y ⟶ B) (F : C) (n : ℤ) :
    ((A ⟶ F⟦n⟧) × (B ⟶ F⟦n⟧)) →+ (Y ⟶ F⟦n⟧) :=
  AddMonoidHom.mk' (fun w => p ≫ w.1 + q ≫ w.2) fun _ _ => by
    simp only [Prod.fst_add, Prod.snd_add, Preadditive.comp_add]
    abel

/-- `shiftedHomDifference p q F n` sends a pair `w` to `p ≫ w.1 + q ≫ w.2`. -/
@[simp]
public lemma shiftedHomDifference_apply {A B Y : C} (p : Y ⟶ A) (q : Y ⟶ B) (F : C) (n : ℤ)
    (w : (A ⟶ F⟦n⟧) × (B ⟶ F⟦n⟧)) :
    shiftedHomDifference p q F n w = p ≫ w.1 + q ≫ w.2 := rfl

private lemma shiftedHomRestriction_ladder {A B Z : C} [HasBinaryBiproduct A B]
    (r : A ⟶ Z) (s : B ⟶ Z) (F : C) (n : ℤ) :
    (shiftedHomPrecomp (biprod.desc r s) F n).comp (AddEquiv.refl (Z ⟶ F⟦n⟧)) =
      ((shiftedHomBiprodEquiv A B (F⟦n⟧)).symm : _ →+ _).comp (shiftedHomRestriction r s F n) := by
  refine AddMonoidHom.ext fun _ => ?_
  apply biprod.hom_ext' <;> simp [shiftedHomRestriction, shiftedHomBiprodEquiv]

private lemma shiftedHomDifference_ladder {A B Y : C} [HasBinaryBiproduct A B]
    (p : Y ⟶ A) (q : Y ⟶ B) (F : C) (n : ℤ) :
    (shiftedHomPrecomp (biprod.lift p q) F n).comp
        ((shiftedHomBiprodEquiv A B (F⟦n⟧)).symm : _ →+ _) =
      (AddEquiv.refl (Y ⟶ F⟦n⟧) : _ →+ _).comp (shiftedHomDifference p q F n) := by
  refine AddMonoidHom.ext fun _ => ?_
  simp [shiftedHomDifference, shiftedHomBiprodEquiv]

section

variable [∀ n : ℤ, (shiftFunctor C n).Additive]

/-- The connecting homomorphism `Ext^{n₀}(T.obj₁, F) ⟶ Ext^{n₁}(T.obj₃, F)` of the
contravariant long exact sequence of shifted morphism groups attached to a triangle `T`. -/
public def triangleShiftedHomδ (T : Triangle C) (F : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (T.obj₁ ⟶ F⟦n₀⟧) →+ (T.obj₃ ⟶ F⟦n₁⟧) :=
  ((preadditiveYoneda.obj F).homologySequenceδ
    ((triangleOpEquivalence C).functor.obj (op T)) n₀ n₁ h).hom

/-- The connecting homomorphism is given by composition with the third map of the triangle. -/
public lemma triangleShiftedHomδ_apply (T : Triangle C) (F : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (x : T.obj₁ ⟶ F⟦n₀⟧) :
    triangleShiftedHomδ T F n₀ n₁ h x =
      T.mor₃ ≫ x⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C n₀ 1 n₁ h).inv.app F :=
  preadditiveYoneda_homologySequenceδ_apply T n₀ n₁ h x

/-- The connecting homomorphism `Ext^{n₀}(Y, F) ⟶ Ext^{n₁}(Z, F)` of the contravariant
sequence attached to a triangle `Y ⟶ A ⊞ B ⟶ Z ⟶ Y⟦1⟧` whose middle term is a binary
biproduct and whose first two maps are a lift and a description. -/
public def biprodTriangleShiftedHomδ {A B Y Z : C} [HasBinaryBiproduct A B]
    (p : Y ⟶ A) (q : Y ⟶ B) (r : A ⟶ Z) (s : B ⟶ Z) (d : Z ⟶ Y⟦(1 : ℤ)⟧)
    (F : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : (Y ⟶ F⟦n₀⟧) →+ (Z ⟶ F⟦n₁⟧) :=
  triangleShiftedHomδ (Triangle.mk (biprod.lift p q) (biprod.desc r s) d) F n₀ n₁ h

/-- The connecting homomorphism of a biproduct triangle is given by composition with the
third map of the triangle. -/
public lemma biprodTriangleShiftedHomδ_apply {A B Y Z : C} [HasBinaryBiproduct A B]
    (p : Y ⟶ A) (q : Y ⟶ B) (r : A ⟶ Z) (s : B ⟶ Z) (d : Z ⟶ Y⟦(1 : ℤ)⟧)
    (F : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (x : Y ⟶ F⟦n₀⟧) :
    biprodTriangleShiftedHomδ p q r s d F n₀ n₁ h x =
      d ≫ x⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C n₀ 1 n₁ h).inv.app F :=
  triangleShiftedHomδ_apply (Triangle.mk (biprod.lift p q) (biprod.desc r s) d) F n₀ n₁ h x

variable [HasZeroObject C] [Pretriangulated C]

/-- Exactness of the contravariant sequence of shifted morphism groups attached to a
distinguished triangle with biproduct middle term, at the product term: a pair of morphisms
out of the two summands whose combination vanishes consists of the two restrictions of a
morphism out of the third term of the triangle. -/
public lemma exact_restriction_difference_of_distTriang {A B Y Z : C} [HasBinaryBiproduct A B]
    (p : Y ⟶ A) (q : Y ⟶ B) (r : A ⟶ Z) (s : B ⟶ Z) (d : Z ⟶ Y⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift p q) (biprod.desc r s) d ∈ distTriang C)
    (F : C) (n : ℤ) :
    Function.Exact (fun x : Z ⟶ F⟦n⟧ => (r ≫ x, s ≫ x))
      (fun w : (A ⟶ F⟦n⟧) × (B ⟶ F⟦n⟧) => p ≫ w.1 + q ≫ w.2) := by
  have h := (preadditiveYoneda.obj F).homologySequence_exact₂
    ((triangleOpEquivalence C).functor.obj (op _)) (op_distinguished _ hT) n
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact Function.Exact.of_ladder_addEquiv_of_exact' (AddEquiv.refl _)
    (shiftedHomBiprodEquiv A B (F⟦n⟧)).symm (AddEquiv.refl _)
    (f₁₂ := shiftedHomRestriction r s F n) (f₂₃ := shiftedHomDifference p q F n)
    (shiftedHomRestriction_ladder r s F n) (shiftedHomDifference_ladder p q F n) h

/-- Exactness of the contravariant sequence of shifted morphism groups attached to a
distinguished triangle with biproduct middle term, at the term of the first vertex. -/
public lemma exact_difference_biprodTriangleShiftedHomδ_of_distTriang {A B Y Z : C}
    [HasBinaryBiproduct A B] (p : Y ⟶ A) (q : Y ⟶ B) (r : A ⟶ Z) (s : B ⟶ Z)
    (d : Z ⟶ Y⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift p q) (biprod.desc r s) d ∈ distTriang C)
    (F : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    Function.Exact (fun w : (A ⟶ F⟦n₀⟧) × (B ⟶ F⟦n₀⟧) => p ≫ w.1 + q ≫ w.2)
      (biprodTriangleShiftedHomδ p q r s d F n₀ n₁ h) := by
  have hh := (preadditiveYoneda.obj F).homologySequence_exact₃
    ((triangleOpEquivalence C).functor.obj (op _)) (op_distinguished _ hT) n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at hh
  exact Function.Exact.of_ladder_addEquiv_of_exact'
    (shiftedHomBiprodEquiv A B (F⟦n₀⟧)).symm (AddEquiv.refl _) (AddEquiv.refl _)
    (f₁₂ := shiftedHomDifference p q F n₀)
    (f₂₃ := biprodTriangleShiftedHomδ p q r s d F n₀ n₁ h)
    (shiftedHomDifference_ladder p q F n₀) rfl hh

/-- Exactness of the contravariant sequence of shifted morphism groups attached to a
distinguished triangle with biproduct middle term, at the term of the third vertex. -/
public lemma exact_biprodTriangleShiftedHomδ_restriction_of_distTriang {A B Y Z : C}
    [HasBinaryBiproduct A B] (p : Y ⟶ A) (q : Y ⟶ B) (r : A ⟶ Z) (s : B ⟶ Z)
    (d : Z ⟶ Y⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift p q) (biprod.desc r s) d ∈ distTriang C)
    (F : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    Function.Exact (biprodTriangleShiftedHomδ p q r s d F n₀ n₁ h)
      (fun x : Z ⟶ F⟦n₁⟧ => (r ≫ x, s ≫ x)) := by
  have hh := (preadditiveYoneda.obj F).homologySequence_exact₁
    ((triangleOpEquivalence C).functor.obj (op _)) (op_distinguished _ hT) n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at hh
  exact Function.Exact.of_ladder_addEquiv_of_exact' (AddEquiv.refl _) (AddEquiv.refl _)
    (shiftedHomBiprodEquiv A B (F⟦n₁⟧)).symm
    (f₁₂ := biprodTriangleShiftedHomδ p q r s d F n₀ n₁ h)
    (f₂₃ := shiftedHomRestriction r s F n₁) rfl (shiftedHomRestriction_ladder r s F n₁) hh

section Hom

variable {A B Y Z : C} [HasBinaryBiproduct A B] (p : Y ⟶ A) (q : Y ⟶ B) (r : A ⟶ Z)
  (s : B ⟶ Z) (d : Z ⟶ Y⟦(1 : ℤ)⟧)
  (hT : Triangle.mk (biprod.lift p q) (biprod.desc r s) d ∈ distTriang C) (F : C)

include hT

/-- `exact_restriction_difference_of_distTriang`, with the two maps as group
homomorphisms. -/
public lemma exact_shiftedHomRestriction_shiftedHomDifference (n : ℤ) :
    Function.Exact (shiftedHomRestriction r s F n) (shiftedHomDifference p q F n) :=
  exact_restriction_difference_of_distTriang p q r s d hT F n

/-- `exact_difference_biprodTriangleShiftedHomδ_of_distTriang`, with the first map as a group
homomorphism. -/
public lemma exact_shiftedHomDifference_biprodTriangleShiftedHomδ (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) :
    Function.Exact (shiftedHomDifference p q F n₀)
      (biprodTriangleShiftedHomδ p q r s d F n₀ n₁ h) :=
  exact_difference_biprodTriangleShiftedHomδ_of_distTriang p q r s d hT F n₀ n₁ h

/-- `exact_biprodTriangleShiftedHomδ_restriction_of_distTriang`, with the second map as a
group homomorphism. -/
public lemma exact_biprodTriangleShiftedHomδ_shiftedHomRestriction (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) :
    Function.Exact (biprodTriangleShiftedHomδ p q r s d F n₀ n₁ h)
      (shiftedHomRestriction r s F n₁) :=
  exact_biprodTriangleShiftedHomδ_restriction_of_distTriang p q r s d hT F n₀ n₁ h

end Hom

end

end CategoryTheory.Pretriangulated

namespace Stacks.ExtensionByZero

attribute [local instance] HasDerivedCategory.standard jShriek_additive

/-- Postcomposition with an isomorphism, as an additive equivalence of morphism groups. -/
public def postcompAddEquiv {C : Type*} [Category* C] [Preadditive C] {A B : C} (Z : C)
    (i : A ≅ B) : (Z ⟶ A) ≃+ (Z ⟶ B) where
  toFun f := f ≫ i.hom
  invFun g := g ≫ i.inv
  left_inv _ := by simp
  right_inv _ := by simp
  map_add' _ _ := by simp

section Restriction

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)

/-- Restriction of unbounded derived modules to an open subspace, `D(j^*)`. -/
public abbrev derivedRestriction : DerivedCategory (SheafOfModules.{u} O) ⥤
    DerivedCategory (SheafOfModules.{u} (resRing U O)) :=
  (jStar U O).mapDerivedCategory

/-- Extension by zero of the restriction to an open subspace, `D(j_!) ∘ D(j^*)`, on the
unbounded derived category. -/
public abbrev derivedExtensionRestriction : DerivedCategory (SheafOfModules.{u} O) ⥤
    DerivedCategory (SheafOfModules.{u} O) :=
  derivedRestriction O U ⋙ (jShriek U O).mapDerivedCategory

/-- **Stacks 08BT at the level of Ext groups.** Morphisms in `D(𝒪_X)` from the extension by
zero of the restriction of `E` to `U` into the `n`-th shift of `F` are the same as morphisms
in `D(𝒪_U)` from the restriction of `E` into the `n`-th shift of the restriction of `F`, so
`Ext^n_X(j_{U!}(E|_U), F)` and `Ext^n_U(E|_U, F|_U)` are identified. -/
public def extensionRestrictionExtEquiv
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) :
    ((derivedExtensionRestriction O U).obj E ⟶ F⟦n⟧) ≃+
      ((derivedRestriction O U).obj E ⟶ ((derivedRestriction O U).obj F)⟦n⟧) :=
  ((jShriekAdjunction U O).mapDerivedCategory.homAddEquiv
      ((derivedRestriction O U).obj E) (F⟦n⟧)).trans
    (postcompAddEquiv _ (((derivedRestriction O U).commShiftIso n).app F))

/-- The functor `D(j_!) ∘ D(j^*)` on the derived category is the one induced by the
degreewise functor `j_! j^*` on the homotopy category, so it is a right derived functor of
the latter along the quasi-isomorphisms. -/
public def derivedExtensionRestrictionFactorsh :
    DerivedCategory.Qh ⋙ derivedExtensionRestriction O U ≅
      homotopyExtensionRestriction O U :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (jStar U O).mapDerivedCategoryFactorsh
      (jShriek U O).mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((jStar U O).mapHomotopyCategory (ComplexShape.up ℤ))
      (jShriek U O).mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (jStar U O ⋙ jShriek U O))
        (ComplexShape.up ℤ)) DerivedCategory.Qh

/-- The functor `D(j_!) ∘ D(j^*)` is a right derived functor of the degreewise functor `j_! j^*`
on the homotopy category along the quasi-isomorphisms. -/
instance derivedExtensionRestriction_isRightDerivedFunctor :
    (derivedExtensionRestriction O U).IsRightDerivedFunctor
      (derivedExtensionRestrictionFactorsh O U).inv
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ (derivedExtensionRestrictionFactorsh O U)

/-- The canonical derived adjunction counit `D(j_!) D(j^*) ⟶ ᵀ` of Stacks 08BT, taken at the
concrete derived functor `derivedExtensionRestriction`. -/
public def derivedExtensionRestrictionCanonicalCounit :
    derivedExtensionRestriction O U ⟶ 𝟭 (DerivedCategory (SheafOfModules.{u} O)) :=
  derivedExtensionRestrictionCounit O U (derivedExtensionRestriction O U)
    (derivedExtensionRestrictionFactorsh O U).inv

end Restriction

/-- Let `X` be a ringed space which is the union of two open subspaces `U` and `V`. Then there
are comparison maps out of `D(j_!)D(j^*)` for `U ∩ V` into the ones for `U` and for `V`, and a
connecting transformation, such that for every object of `D(𝒪_X)` the resulting triangle is
distinguished. The three derived functors are `derivedExtensionRestriction`, the maps to the
identity functor are the canonical derived adjunction counits
`derivedExtensionRestrictionCanonicalCounit`, and the two comparison maps are determined by
composing them with those counits, the second with a sign. -/
@[stacks 08BU "the whole statement at the presentation built in this file: the three clauses of
`distinguished_extensionRestriction_triangle` for `derivedExtensionRestriction`,
`derivedExtensionRestrictionFactorsh` and the instance
`derivedExtensionRestriction_isRightDerivedFunctor`, with the maps to the identity functor the
canonical derived adjunction counits of Stacks 08BT and the two maps out of the intersection term
pinned by composing them with those counits, the second with the Mayer--Vietoris sign"]
public theorem distinguished_derivedExtensionRestriction_triangle {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U V : Opens X)
    (hUV : U ⊔ V = ⊤) :
    ∃ (iU : derivedExtensionRestriction O (U ⊓ V) ⟶ derivedExtensionRestriction O U)
      (iV : derivedExtensionRestriction O (U ⊓ V) ⟶ derivedExtensionRestriction O V)
      (δ : 𝟭 (DerivedCategory (SheafOfModules.{u} O)) ⟶
        derivedExtensionRestriction O (U ⊓ V) ⋙
          shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)),
      (iU ≫ derivedExtensionRestrictionCanonicalCounit O U =
          derivedExtensionRestrictionCanonicalCounit O (U ⊓ V)) ∧
      (iV ≫ derivedExtensionRestrictionCanonicalCounit O V =
          -derivedExtensionRestrictionCanonicalCounit O (U ⊓ V)) ∧
      (∀ E, Triangle.mk (biprod.lift (iU.app E) (iV.app E))
        (biprod.desc ((derivedExtensionRestrictionCanonicalCounit O U).app E)
          ((derivedExtensionRestrictionCanonicalCounit O V).app E)) (δ.app E) ∈
          distTriang (DerivedCategory (SheafOfModules.{u} O))) :=
  distinguished_extensionRestriction_triangle O U V hUV
    (derivedExtensionRestriction O U) (derivedExtensionRestriction O V)
    (derivedExtensionRestriction O (U ⊓ V))
    (derivedExtensionRestrictionFactorsh O U).inv
    (derivedExtensionRestrictionFactorsh O V).inv
    (derivedExtensionRestrictionFactorsh O (U ⊓ V)).inv

/-- The two identifications of Stacks 08BT for `U` and for `V`, taken together. -/
private def extensionRestrictionExtPairEquiv {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U V : Opens X)
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) :
    (((derivedExtensionRestriction O U).obj E ⟶ F⟦n⟧) ×
        ((derivedExtensionRestriction O V).obj E ⟶ F⟦n⟧)) ≃+
      (((derivedRestriction O U).obj E ⟶ ((derivedRestriction O U).obj F)⟦n⟧) ×
        ((derivedRestriction O V).obj E ⟶ ((derivedRestriction O V).obj F)⟦n⟧)) :=
  (extensionRestrictionExtEquiv O U E F n).prodCongr (extensionRestrictionExtEquiv O V E F n)

/-- Let `X` be a ringed space covered by two open subspaces `U` and `V`, and let `E` and `F` be
objects of `D(𝒪_X)`. There are restriction, difference and connecting homomorphisms making the
Mayer--Vietoris sequence

`⋯ ⟶ Ext^{n-1}(E|_{U∩V}, F|_{U∩V}) ⟶ Ext^n(E, F) ⟶
  Ext^n(E|_U, F|_U) × Ext^n(E|_V, F|_V) ⟶ Ext^n(E|_{U∩V}, F|_{U∩V}) ⟶ ⋯`

exact at each of its three kinds of spot and in every integer degree, the Ext groups of the
restrictions being taken in the derived categories of the open subspaces. -/
@[stacks 08BW "long exact sequence of the Ext groups on the two opens and their intersection"]
public theorem exists_mayerVietoris_ext_longExactSequence {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (E F : DerivedCategory (SheafOfModules.{u} O)) :
    ∃ (restriction : ∀ n : ℤ, (E ⟶ F⟦n⟧) →+
          (((derivedRestriction O U).obj E ⟶ ((derivedRestriction O U).obj F)⟦n⟧) ×
            ((derivedRestriction O V).obj E ⟶ ((derivedRestriction O V).obj F)⟦n⟧)))
      (difference : ∀ n : ℤ,
        (((derivedRestriction O U).obj E ⟶ ((derivedRestriction O U).obj F)⟦n⟧) ×
            ((derivedRestriction O V).obj E ⟶ ((derivedRestriction O V).obj F)⟦n⟧)) →+
          ((derivedRestriction O (U ⊓ V)).obj E ⟶
            ((derivedRestriction O (U ⊓ V)).obj F)⟦n⟧))
      (boundary : ∀ n : ℤ,
        ((derivedRestriction O (U ⊓ V)).obj E ⟶
          ((derivedRestriction O (U ⊓ V)).obj F)⟦n⟧) →+ (E ⟶ F⟦n + 1⟧)),
      ∀ n : ℤ, Function.Exact (restriction n) (difference n) ∧
        Function.Exact (difference n) (boundary n) ∧
        Function.Exact (boundary n) (restriction (n + 1)) :=
  (distinguished_extensionRestriction_triangle O U V hUV
      (derivedExtensionRestriction O U) (derivedExtensionRestriction O V)
      (derivedExtensionRestriction O (U ⊓ V))
      (derivedExtensionRestrictionFactorsh O U).inv
      (derivedExtensionRestrictionFactorsh O V).inv
      (derivedExtensionRestrictionFactorsh O (U ⊓ V)).inv).elim
    fun iU hiU => hiU.elim fun iV hiV => hiV.elim fun δ h => by
      refine ⟨fun n => (extensionRestrictionExtPairEquiv O U V E F n : _ →+ _).comp
          (shiftedHomRestriction (derivedExtensionRestrictionCanonicalCounit O U |>.app E)
            (derivedExtensionRestrictionCanonicalCounit O V |>.app E) F n),
        fun n => (extensionRestrictionExtEquiv O (U ⊓ V) E F n : _ →+ _).comp
          ((shiftedHomDifference (iU.app E) (iV.app E) F n).comp
            ((extensionRestrictionExtPairEquiv O U V E F n).symm : _ →+ _)),
        fun n => (biprodTriangleShiftedHomδ (iU.app E) (iV.app E)
            (derivedExtensionRestrictionCanonicalCounit O U |>.app E)
            (derivedExtensionRestrictionCanonicalCounit O V |>.app E) (δ.app E)
            F n (n + 1) rfl).comp
          ((extensionRestrictionExtEquiv O (U ⊓ V) E F n).symm : _ →+ _),
        fun n => ⟨?_, ?_, ?_⟩⟩
      · refine Function.Exact.of_ladder_addEquiv_of_exact' (AddEquiv.refl _)
          (extensionRestrictionExtPairEquiv O U V E F n).symm
          (extensionRestrictionExtEquiv O (U ⊓ V) E F n).symm ?_ ?_
          (exact_shiftedHomRestriction_shiftedHomDifference _ _ _ _ _ (h.2.2 E) F n) <;>
        exact AddMonoidHom.ext fun _ => by simp [derivedExtensionRestrictionCanonicalCounit]
      · refine Function.Exact.of_ladder_addEquiv_of_exact'
          (extensionRestrictionExtPairEquiv O U V E F n).symm
          (extensionRestrictionExtEquiv O (U ⊓ V) E F n).symm (AddEquiv.refl _) ?_ ?_
          (exact_shiftedHomDifference_biprodTriangleShiftedHomδ _ _ _ _ _ (h.2.2 E) F n
            (n + 1) rfl) <;>
        exact AddMonoidHom.ext fun _ => by simp [derivedExtensionRestrictionCanonicalCounit]
      · refine Function.Exact.of_ladder_addEquiv_of_exact'
          (extensionRestrictionExtEquiv O (U ⊓ V) E F n).symm (AddEquiv.refl _)
          (extensionRestrictionExtPairEquiv O U V E F (n + 1)).symm ?_ ?_
          (exact_biprodTriangleShiftedHomδ_shiftedHomRestriction _ _ _ _ _ (h.2.2 E) F n
            (n + 1) rfl) <;>
        exact AddMonoidHom.ext fun _ => by simp [derivedExtensionRestrictionCanonicalCounit]

/-- Let `X` be a ringed space covered by two open subspaces `U` and `V`, and let `E` and `F` be
objects of `D(𝒪_X)`. For every choice of the three derived functors of extension by zero of the
restrictions there are comparison maps `iU` and `iV` out of the functor attached to `U ∩ V`,
compatible with the canonical derived adjunction counits and carrying the Mayer--Vietoris sign,
and connecting homomorphisms, such that the Mayer--Vietoris sequence

`⋯ ⟶ Ext^{n-1}(j_{U∩V,!}E|_{U∩V}, F) ⟶ Ext^n(E, F) ⟶
  Ext^n(j_{U!}E|_U, F) × Ext^n(j_{V!}E|_V, F) ⟶ Ext^n(j_{U∩V,!}E|_{U∩V}, F) ⟶ ⋯`

is exact at each of its three kinds of spot and in every integer degree. -/
@[stacks 08BW "long exact sequence, extension-by-zero form of the Ext groups"]
public theorem exists_mayerVietoris_hom_longExactSequence {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (DU DV DUV : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aU : homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh ⋙ DU)
    (aV : homotopyExtensionRestriction O V ⟶ DerivedCategory.Qh ⋙ DV)
    (aUV : homotopyExtensionRestriction O (U ⊓ V) ⟶ DerivedCategory.Qh ⋙ DUV)
    [DU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [DV.IsRightDerivedFunctor aV
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [DUV.IsRightDerivedFunctor aUV
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    ∃ (iU : DUV ⟶ DU) (iV : DUV ⟶ DV)
      (boundary : ∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ),
        (DUV.obj E ⟶ F⟦n⟧) →+ (E ⟶ F⟦n + 1⟧)),
      (iU ≫ derivedExtensionRestrictionCounit O U DU aU =
          derivedExtensionRestrictionCounit O (U ⊓ V) DUV aUV) ∧
      (iV ≫ derivedExtensionRestrictionCounit O V DV aV =
          -derivedExtensionRestrictionCounit O (U ⊓ V) DUV aUV) ∧
      ∀ (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ),
        Function.Exact
            (fun x : E ⟶ F⟦n⟧ =>
              ((derivedExtensionRestrictionCounit O U DU aU).app E ≫ x,
                (derivedExtensionRestrictionCounit O V DV aV).app E ≫ x))
            (fun w : (DU.obj E ⟶ F⟦n⟧) × (DV.obj E ⟶ F⟦n⟧) =>
              iU.app E ≫ w.1 + iV.app E ≫ w.2) ∧
          Function.Exact
            (fun w : (DU.obj E ⟶ F⟦n⟧) × (DV.obj E ⟶ F⟦n⟧) =>
              iU.app E ≫ w.1 + iV.app E ≫ w.2)
            (boundary E F n) ∧
          Function.Exact (boundary E F n)
            (fun x : E ⟶ F⟦n + 1⟧ =>
              ((derivedExtensionRestrictionCounit O U DU aU).app E ≫ x,
                (derivedExtensionRestrictionCounit O V DV aV).app E ≫ x)) :=
  (distinguished_extensionRestriction_triangle O U V hUV DU DV DUV aU aV aUV).elim
    fun iU hiU => hiU.elim fun iV hiV => hiV.elim fun δ h =>
      ⟨iU, iV, fun E F n => biprodTriangleShiftedHomδ (iU.app E) (iV.app E)
          ((derivedExtensionRestrictionCounit O U DU aU).app E)
          ((derivedExtensionRestrictionCounit O V DV aV).app E) (δ.app E) F n (n + 1) rfl,
        h.1, h.2.1, fun E F n =>
          ⟨exact_restriction_difference_of_distTriang _ _ _ _ _ (h.2.2 E) F n,
            exact_difference_biprodTriangleShiftedHomδ_of_distTriang _ _ _ _ _ (h.2.2 E) F n
              (n + 1) rfl,
            exact_biprodTriangleShiftedHomδ_restriction_of_distTriang _ _ _ _ _ (h.2.2 E) F n
              (n + 1) rfl⟩⟩

end Stacks.ExtensionByZero

end
