module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedCategoryBIsoClosedInstance
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakSerreClassInf
public import StacksFrontier.CategoryTheory.Triangulated.AdmissibleSubcategories

/-!
# Colocalizing `D_𝓛(A)` at the kernel of a functor with a fully faithful left adjoint

Let `A` be an abelian category, let `𝓛` be a weak Serre class and `𝓟` a weak Serre class in `A`,
and let `G : D(A) ⥤ D'` be a triangulated functor whose kernel is the complexes with cohomology
in `𝓟`. Suppose `G` has a left adjoint `L` with `G L = id` (the unit is invertible) and that
`L G` preserves `D_𝓛(A)`. Then for every `K` in `D_𝓛(A)` the counit `L G K ⟶ K` extends to a
distinguished triangle

`L G K ⟶ K ⟶ P ⟶ (L G K)[1]`

of `D_𝓛(A)` with `P` in `D_{𝓟 ∩ 𝓛}(A)` and `L G K` left orthogonal to `D_{𝓟 ∩ 𝓛}(A)`. By
[Stacks, Tag 0H0P] the parasitic part `D_{𝓟 ∩ 𝓛}(A) ⊂ D_𝓛(A)` is therefore left admissible,
its left orthogonal `𝒜` is right admissible, `𝒜` maps isomorphically onto the Verdier quotient
`D_𝓛(A) / D_{𝓟 ∩ 𝓛}(A)`, and `𝒜` is a strictly full saturated triangulated subcategory of
`D_𝓛(A)` and of `D(A)`.

This is the formal content of **Stacks 07BA** and **Stacks 0H11**, where `A = Mod(𝒪_𝒳)`,
`𝓛 = LQCoh^fbc(𝒪_𝒳)`, `𝓟` the parasitic modules and `G = g^*` restriction to the flat-fppf site.
It is stated here with no reference to the geometry, so that it can be instantiated at any
module universe and at any reading of `LQCoh^fbc(𝒪_𝒳)`.

## Main definitions

In the namespace `DerivedCategory.KernelColocalization`:

* `derivedInter 𝓟 𝓛`: the subcategory `D_{𝓟 ∩ 𝓛}(A)` of `D(A)`.
* `interIn 𝓟 𝓛` and `interLeftOrthogonalIn 𝓟 𝓛`: `D_{𝓟 ∩ 𝓛}(A)` and its left orthogonal `𝒜`,
  as subcategories of `D_𝓛(A)`.
* `interLeftOrthogonal 𝓟 𝓛`: the subcategory `𝒜` read inside `D(A)`.
* `quotientW 𝓟 𝓛`, `quotient 𝓟 𝓛` and `toQuotient 𝓟 𝓛`: the morphisms of `D_𝓛(A)` with cone in
  `D_{𝓟 ∩ 𝓛}(A)`, the Verdier quotient `D_𝓛(A) / D_{𝓟 ∩ 𝓛}(A)`, and the quotient functor.
* `interLeftOrthogonalToClass 𝓟 𝓛`: the inclusion of `interLeftOrthogonal 𝓟 𝓛` into `D_𝓛(A)`.

## Main results

* `quotientW_eq_trW`: the inverted class is the class attached to `interIn 𝓟 𝓛`.
* `leftOrthogonal_obj_counit`, `derivedInter_obj₃_of_distTriang`, `extensionProduct_eq_top`:
  the canonical triangle.
* `isLeftAdmissible_interIn`, `isRightAdmissible_interLeftOrthogonalIn`,
  `isEquivalence_interLeftOrthogonalIn_ι_comp`, `isSaturated_interLeftOrthogonalIn`,
  `isSaturated_interLeftOrthogonal`, `isEquivalence_interLeftOrthogonalToClass_comp`: the
  admissibility statements.

## References

* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
* [Stacks Project, Tag 0CQP](https://stacks.math.columbia.edu/tag/0CQP)
* [Stacks Project, Tag 0H0P](https://stacks.math.columbia.edu/tag/0H0P)
* [Stacks Project, Tag 0H11](https://stacks.math.columbia.edu/tag/0H11)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

namespace DerivedCategory.KernelColocalization

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A] (𝓟 𝓛 : ObjectProperty A)

/-! ### The subcategories and the Verdier quotient -/

/-- The subcategory `D_{𝓟 ∩ 𝓛}(A)` of `D(A)`. -/
abbrev derivedInter : ObjectProperty (DerivedCategory A) :=
  DerivedCategoryB.derivedCategoryB (𝓟 ⊓ 𝓛)

/-- `D_{𝓟 ∩ 𝓛}(A)` as a subcategory of `D_𝓛(A)`. -/
abbrev interIn : ObjectProperty (DerivedCategoryB.derivedCategoryB 𝓛).FullSubcategory :=
  (derivedInter 𝓟 𝓛).inverseImage (DerivedCategoryB.derivedCategoryB 𝓛).ι

/-- The left orthogonal `𝒜` of `D_{𝓟 ∩ 𝓛}(A)` inside `D_𝓛(A)`. -/
abbrev interLeftOrthogonalIn :
    ObjectProperty (DerivedCategoryB.derivedCategoryB 𝓛).FullSubcategory :=
  (interIn 𝓟 𝓛).leftOrthogonal

/-- The subcategory `𝒜` read inside `D(A)`: the objects of `D_𝓛(A)` admitting no nonzero
morphism to `D_{𝓟 ∩ 𝓛}(A)`. -/
abbrev interLeftOrthogonal : ObjectProperty (DerivedCategory A) :=
  (derivedInter 𝓟 𝓛).leftOrthogonal ⊓ DerivedCategoryB.derivedCategoryB 𝓛

/-- The morphisms of `D_𝓛(A)` whose cone, taken in `D(A)`, lies in `D_{𝓟 ∩ 𝓛}(A)`. -/
abbrev quotientW : MorphismProperty (DerivedCategoryB.derivedCategoryB 𝓛).FullSubcategory :=
  MorphismProperty.inverseImage (derivedInter 𝓟 𝓛).trW (DerivedCategoryB.derivedCategoryB 𝓛).ι

/-- The Verdier quotient `D_𝓛(A) / D_{𝓟 ∩ 𝓛}(A)`, the localization at `quotientW 𝓟 𝓛`. -/
abbrev quotient := (quotientW 𝓟 𝓛).Localization

/-- The quotient functor `D_𝓛(A) ⥤ D_𝓛(A) / D_{𝓟 ∩ 𝓛}(A)`. -/
abbrev toQuotient : (DerivedCategoryB.derivedCategoryB 𝓛).FullSubcategory ⥤ quotient 𝓟 𝓛 :=
  (quotientW 𝓟 𝓛).Q

/-- The inclusion of `interLeftOrthogonal 𝓟 𝓛` into `D_𝓛(A)`. -/
abbrev interLeftOrthogonalToClass :
    (interLeftOrthogonal 𝓟 𝓛).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB 𝓛).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryB 𝓛).lift (interLeftOrthogonal 𝓟 𝓛).ι
    (fun X => X.property.2)

/-- `D_{𝓟 ∩ 𝓛}(A) ⊆ D_𝓛(A)`. -/
lemma derivedInter_le : derivedInter 𝓟 𝓛 ≤ DerivedCategoryB.derivedCategoryB 𝓛 :=
  fun _ hX n => (hX n).2

/-- The two readings of `𝒜` agree, because `D_{𝓟 ∩ 𝓛}(A) ⊆ D_𝓛(A)`. -/
theorem interLeftOrthogonalIn_eq_inverseImage :
    interLeftOrthogonalIn 𝓟 𝓛 =
      (interLeftOrthogonal 𝓟 𝓛).inverseImage (DerivedCategoryB.derivedCategoryB 𝓛).ι := by
  ext X
  constructor
  · refine fun hX => ⟨fun {Y} f hY => ?_, X.property⟩
    have := (DerivedCategoryB.derivedCategoryB 𝓛).ι.congr_map
      (hX (Y := ⟨Y, derivedInter_le 𝓟 𝓛 Y hY⟩) (homMk f) hY)
    simpa using this
  · exact fun hX _ f hY => ObjectProperty.hom_ext _ (hX.1 f.hom hY)

section WeakSerre

variable [𝓟.IsWeakSerreClass] [𝓛.IsWeakSerreClass]

/-- The quotient is the Verdier quotient by `interIn 𝓟 𝓛`. -/
theorem quotientW_eq_trW : quotientW 𝓟 𝓛 = (interIn 𝓟 𝓛).trW := by
  ext X Y f
  exact ((derivedInter 𝓟 𝓛).inverseImage_trW_iff (DerivedCategoryB.derivedCategoryB 𝓛).ι f).symm

/-! ### The canonical triangle -/

variable {D' : Type*} [Category D'] [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  {G : DerivedCategory A ⥤ D'} [G.CommShift ℤ] [G.IsTriangulated]
  {Lsh : D' ⥤ DerivedCategory A} (adj : Lsh ⊣ G)

omit [𝓟.IsWeakSerreClass] [𝓛.IsWeakSerreClass] [HasZeroObject D'] [HasShift D' ℤ]
  [Preadditive D'] [∀ (n : ℤ), (shiftFunctor D' n).Additive] [Pretriangulated D']
  [G.CommShift ℤ] [G.IsTriangulated] in
include 𝓛 adj in
/-- The first term `L G K` of the canonical triangle is left orthogonal to `D_{𝓟 ∩ 𝓛}(A)`:
`Hom(L G K, P') = Hom(G K, G P') = 0`, as `G` kills `D_{𝓟 ∩ 𝓛}(A)`. -/
theorem leftOrthogonal_obj_counit
    (hG : ∀ K, IsZero (G.obj K) ↔ ∀ n : ℤ, 𝓟 ((homologyFunctor A n).obj K))
    (K : DerivedCategory A) : (derivedInter 𝓟 𝓛).leftOrthogonal (Lsh.obj (G.obj K)) := by
  intro P' f hP'
  have hz : IsZero (G.obj P') := (hG P').2 (fun n => (hP' n).1)
  exact (adj.homEquiv _ P').injective (hz.eq_of_tgt _ _)

omit [𝓟.IsWeakSerreClass] [𝓛.IsWeakSerreClass] [HasZeroObject D'] [HasShift D' ℤ]
  [Preadditive D'] [∀ (n : ℤ), (shiftFunctor D' n).Additive] [Pretriangulated D']
  [G.CommShift ℤ] [G.IsTriangulated] in
/-- `G` inverts the counit `L G K ⟶ K` when the unit is invertible, by a triangle identity. -/
theorem isIso_map_counit_app (hunit : IsIso adj.unit) (K : DerivedCategory A) :
    IsIso (G.map (adj.counit.app K)) := by
  have h₂ : adj.unit.app (G.obj K) ≫ G.map (adj.counit.app K) = 𝟙 _ :=
    adj.right_triangle_components K
  have h₃ : IsIso (adj.unit.app (G.obj K) ≫ G.map (adj.counit.app K)) := by
    rw [h₂]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_left (adj.unit.app (G.obj K)) _

omit [𝓟.IsWeakSerreClass] in
/-- The third term of the canonical triangle: if `K` and `L G K` lie in `D_𝓛(A)`, every cone on
the counit `L G K ⟶ K` lies in `D_{𝓟 ∩ 𝓛}(A)`. -/
theorem derivedInter_obj₃_of_distTriang
    (hG : ∀ K, IsZero (G.obj K) ↔ ∀ n : ℤ, 𝓟 ((homologyFunctor A n).obj K))
    (hunit : IsIso adj.unit)
    (K : DerivedCategory A) (hK : DerivedCategoryB.derivedCategoryB 𝓛 K)
    (hK' : DerivedCategoryB.derivedCategoryB 𝓛 (Lsh.obj (G.obj K)))
    (P : DerivedCategory A) (b : K ⟶ P) (c : P ⟶ (Lsh.obj (G.obj K))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (adj.counit.app K) b c ∈ distTriang (DerivedCategory A)) :
    derivedInter 𝓟 𝓛 P := by
  have hP : DerivedCategoryB.derivedCategoryB 𝓛 P :=
    (DerivedCategoryB.derivedCategoryB 𝓛).ext_of_isTriangulatedClosed₃ _ hT hK' hK
  have hz : IsZero (G.obj P) := by
    refine (Triangle.isZero₃_iff_isIso₁ _ (G.map_distinguished _ hT)).2 ?_
    exact isIso_map_counit_app adj hunit K
  exact fun n => ⟨(hG P).1 hz n, hP n⟩

omit [𝓟.IsWeakSerreClass] in
/-- **The semiorthogonal decomposition** `D_𝓛(A) = ⟨D_{𝓟 ∩ 𝓛}(A), 𝒜⟩`: every object of
`D_𝓛(A)` is an extension of an object of `D_{𝓟 ∩ 𝓛}(A)` by an object of `𝒜`, namely the
canonical one on the counit, provided `L G` preserves `D_𝓛(A)`. -/
theorem extensionProduct_eq_top
    (hG : ∀ K, IsZero (G.obj K) ↔ ∀ n : ℤ, 𝓟 ((homologyFunctor A n).obj K))
    (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (Lsh.obj (G.obj K))) :
    (interLeftOrthogonalIn 𝓟 𝓛).extensionProduct (interIn 𝓟 𝓛) = ⊤ := by
  rw [eq_top_iff]
  intro X _
  obtain ⟨P, b, c, hT⟩ := distinguished_cocone_triangle (adj.counit.app X.obj)
  have hK' := hshriek X.obj X.property
  have hP := derivedInter_obj₃_of_distTriang 𝓟 𝓛 adj hG hunit X.obj X.property hK' P b c hT
  refine ⟨⟨_, hK'⟩, ⟨P, derivedInter_le 𝓟 𝓛 P hP⟩, homMk (adj.counit.app X.obj), homMk b,
    homMk (c ≫ ((DerivedCategoryB.derivedCategoryB 𝓛).ι.commShiftIso (1 : ℤ)).inv.app ⟨_, hK'⟩),
    ?_, ?_, hP⟩
  · -- the triangle of `D(A)` is the image of a triangle of the full subcategory
    rw [← (DerivedCategoryB.derivedCategoryB 𝓛).ι.map_distinguished_iff]
    refine isomorphic_distinguished _ hT _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_) <;>
      simp [Functor.mapTriangle]
  · rw [interLeftOrthogonalIn_eq_inverseImage]
    exact ⟨leftOrthogonal_obj_counit 𝓟 𝓛 adj hG X.obj, hK'⟩

/-! ### Admissibility -/

/-- [Stacks, Tag 0H0P] applied to `extensionProduct_eq_top`. -/
private lemma admissibility
    (hG : ∀ K, IsZero (G.obj K) ↔ ∀ n : ℤ, 𝓟 ((homologyFunctor A n).obj K))
    (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (Lsh.obj (G.obj K))) :
    (interIn 𝓟 𝓛).IsLeftAdmissible ∧
      ((interLeftOrthogonalIn 𝓟 𝓛).IsRightAdmissible ∧
        interIn 𝓟 𝓛 = (interLeftOrthogonalIn 𝓟 𝓛).rightOrthogonal) ∧
      ((interLeftOrthogonalIn 𝓟 𝓛).ι ⋙ toQuotient 𝓟 𝓛).IsEquivalence := by
  have hloc : (toQuotient 𝓟 𝓛).IsLocalization (interIn 𝓟 𝓛).trW := by
    rw [← quotientW_eq_trW 𝓟 𝓛]
    infer_instance
  have hsemi : interLeftOrthogonalIn 𝓟 𝓛 ≤ (interIn 𝓟 𝓛).leftOrthogonal ∧
      (interLeftOrthogonalIn 𝓟 𝓛).extensionProduct (interIn 𝓟 𝓛) = ⊤ :=
    ⟨le_rfl, extensionProduct_eq_top 𝓟 𝓛 adj hG hunit hshriek⟩
  have hmain := tfae_isRightAdmissible_isLeftAdmissible_extensionProduct_and_isEquivalence_ι_comp
    (interLeftOrthogonalIn 𝓟 𝓛) (interIn 𝓟 𝓛)
  have h₂ : (interIn 𝓟 𝓛).IsLeftAdmissible ∧
      interLeftOrthogonalIn 𝓟 𝓛 = (interIn 𝓟 𝓛).leftOrthogonal :=
    (hmain.1.out 3 2).mp hsemi
  have h₁ : (interLeftOrthogonalIn 𝓟 𝓛).IsRightAdmissible ∧
      interIn 𝓟 𝓛 = (interLeftOrthogonalIn 𝓟 𝓛).rightOrthogonal :=
    (hmain.1.out 3 1).mp hsemi
  exact ⟨h₂.1, h₁, ((hmain.2 hsemi.1 hsemi.2).1 (toQuotient 𝓟 𝓛)).1⟩

/-- `D_{𝓟 ∩ 𝓛}(A) ⊂ D_𝓛(A)` is left admissible. -/
theorem isLeftAdmissible_interIn
    (hG : ∀ K, IsZero (G.obj K) ↔ ∀ n : ℤ, 𝓟 ((homologyFunctor A n).obj K))
    (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (Lsh.obj (G.obj K))) :
    (interIn 𝓟 𝓛).IsLeftAdmissible :=
  (admissibility 𝓟 𝓛 adj hG hunit hshriek).1

/-- The left orthogonal `𝒜` of `D_{𝓟 ∩ 𝓛}(A)` is right admissible in `D_𝓛(A)`, and
`D_{𝓟 ∩ 𝓛}(A)` is the right orthogonal of `𝒜`. -/
theorem isRightAdmissible_interLeftOrthogonalIn
    (hG : ∀ K, IsZero (G.obj K) ↔ ∀ n : ℤ, 𝓟 ((homologyFunctor A n).obj K))
    (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (Lsh.obj (G.obj K))) :
    (interLeftOrthogonalIn 𝓟 𝓛).IsRightAdmissible ∧
      interIn 𝓟 𝓛 = (interLeftOrthogonalIn 𝓟 𝓛).rightOrthogonal :=
  (admissibility 𝓟 𝓛 adj hG hunit hshriek).2.1

/-- `𝒜 ⟶ D_𝓛(A) ⟶ D_𝓛(A) / D_{𝓟 ∩ 𝓛}(A)` is an equivalence. -/
theorem isEquivalence_interLeftOrthogonalIn_ι_comp
    (hG : ∀ K, IsZero (G.obj K) ↔ ∀ n : ℤ, 𝓟 ((homologyFunctor A n).obj K))
    (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (Lsh.obj (G.obj K))) :
    ((interLeftOrthogonalIn 𝓟 𝓛).ι ⋙ toQuotient 𝓟 𝓛).IsEquivalence :=
  (admissibility 𝓟 𝓛 adj hG hunit hshriek).2.2

/-- `𝒜` is a strictly full saturated triangulated subcategory of `D_𝓛(A)`. -/
theorem isSaturated_interLeftOrthogonalIn
    (hG : ∀ K, IsZero (G.obj K) ↔ ∀ n : ℤ, 𝓟 ((homologyFunctor A n).obj K))
    (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (Lsh.obj (G.obj K))) :
    (interLeftOrthogonalIn 𝓟 𝓛).IsClosedUnderIsomorphisms ∧
      (interLeftOrthogonalIn 𝓟 𝓛).IsSaturated ∧ (interLeftOrthogonalIn 𝓟 𝓛).IsTriangulated := by
  have hadm := (isRightAdmissible_interLeftOrthogonalIn 𝓟 𝓛 adj hG hunit hshriek).1
  have key := isLeftAdjoint_ι_iff_extensionProduct_rightOrthogonal_eq_top_and_isSaturated
    (interLeftOrthogonalIn 𝓟 𝓛)
  exact ⟨inferInstance, (key.2 (key.1.1 inferInstance)).1, inferInstance⟩

/-- `𝒜` read inside `D(A)` is a strictly full saturated triangulated subcategory of `D(A)`:
it is a left orthogonal, which is stable under retracts, intersected with `D_𝓛(A)`, which is
stable under retracts because `𝓛` is weak Serre. -/
theorem isSaturated_interLeftOrthogonal :
    (interLeftOrthogonal 𝓟 𝓛).IsClosedUnderIsomorphisms ∧
      (interLeftOrthogonal 𝓟 𝓛).IsSaturated ∧ (interLeftOrthogonal 𝓟 𝓛).IsTriangulated := by
  have hortho := (isStableUnderRetracts_rightOrthogonal_and_leftOrthogonal
    (derivedInter 𝓟 𝓛)).2
  have hL : (DerivedCategoryB.derivedCategoryB 𝓛).IsStableUnderRetracts :=
    DerivedCategoryB.derivedCategoryB_isStableUnderRetracts 𝓛
      (WeakSerre.isWeakSerre_of_isWeakSerreClass 𝓛)
  have hiso : (interLeftOrthogonal 𝓟 𝓛).IsClosedUnderIsomorphisms :=
    ⟨fun e hX => ⟨prop_of_iso _ e hX.1, prop_of_iso _ e hX.2⟩⟩
  have hretract : (interLeftOrthogonal 𝓟 𝓛).IsStableUnderRetracts :=
    ⟨fun r hY => ⟨hortho.of_retract r hY.1, hL.of_retract r hY.2⟩⟩
  exact ⟨hiso, IsSaturated.of_isStableUnderRetracts _, inferInstance⟩

/-- With `𝒜` presented inside `D(A)`, its composition with the quotient functor is still an
equivalence. -/
theorem isEquivalence_interLeftOrthogonalToClass_comp
    (hG : ∀ K, IsZero (G.obj K) ↔ ∀ n : ℤ, 𝓟 ((homologyFunctor A n).obj K))
    (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (Lsh.obj (G.obj K))) :
    (interLeftOrthogonalToClass 𝓟 𝓛 ⋙ toQuotient 𝓟 𝓛).IsEquivalence := by
  have hmem : ∀ X : (interLeftOrthogonal 𝓟 𝓛).FullSubcategory,
      interLeftOrthogonalIn 𝓟 𝓛 ((interLeftOrthogonalToClass 𝓟 𝓛).obj X) := by
    intro X
    rw [interLeftOrthogonalIn_eq_inverseImage]
    exact X.property
  have := isEquivalence_interLeftOrthogonalIn_ι_comp 𝓟 𝓛 adj hG hunit hshriek
  have hlift : ((interLeftOrthogonalIn 𝓟 𝓛).lift
      (interLeftOrthogonalToClass 𝓟 𝓛) hmem).EssSurj :=
    ⟨fun Y => ⟨⟨Y.obj.obj, (interLeftOrthogonalIn_eq_inverseImage 𝓟 𝓛).le
      Y.obj Y.property⟩, ⟨Iso.refl _⟩⟩⟩
  have : ((interLeftOrthogonalIn 𝓟 𝓛).lift
      (interLeftOrthogonalToClass 𝓟 𝓛) hmem).IsEquivalence :=
    ⟨inferInstance, inferInstance, hlift⟩
  exact inferInstanceAs (((interLeftOrthogonalIn 𝓟 𝓛).lift
    (interLeftOrthogonalToClass 𝓟 𝓛) hmem) ⋙
      ((interLeftOrthogonalIn 𝓟 𝓛).ι ⋙ toQuotient 𝓟 𝓛)).IsEquivalence

end WeakSerre

end DerivedCategory.KernelColocalization
