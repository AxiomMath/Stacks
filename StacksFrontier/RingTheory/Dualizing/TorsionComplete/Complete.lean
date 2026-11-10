module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence
public import StacksFrontier.RingTheory.Dualizing.DerivedTorsion

/-!
# Derived complete objects as a triangulated subcategory

Let `I` be an ideal of a commutative ring `A`. An object of `D(A)` is derived `I`-complete when
the derived limit of the tower `⋯ → K → K` given by multiplication by `a` vanishes for every
`a ∈ I`. This file packages those objects as an `ObjectProperty` of `D(A)` and shows that the
property is triangulated: it contains zero, is closed under isomorphism and shift, and is stable
under extensions. It also shows that a map from an object on which some `a ∈ I` acts invertibly
into a derived `I`-complete object is zero, and that any reflection of `D(A)` onto the derived
`I`-complete objects annihilates such an object.

The module universe is independent of the ring universe throughout. Countable products exist in
`D(A)` because countable products of modules are exact, so the statements are unconditional.

## Main definitions

* `Dualizing.derivedCompleteProperty` — the property of being derived `I`-complete.
* `Dualizing.DerivedCompleteDerivedCategory` — the full subcategory `D_comp(A, I)` it cuts out.

## Main results

* `Dualizing.isDerivedCompleteAt_map` — an exact linear functor preserving the relevant countable
  product preserves derived completeness at an element.
* `Dualizing.derivedCompleteProperty_isTriangulated` — the derived `I`-complete objects form a
  triangulated subcategory of `D(A)`.
* `Dualizing.subsingleton_hom_of_isIso_smul_of_isDerivedCompleteAt` — there are no nonzero maps
  from an object on which `a` acts invertibly to an object derived complete at `a`.
* `Dualizing.isZero_reflector_obj_of_isIso_smul` — a reflection onto the derived `I`-complete
  objects kills every object on which some element of `I` acts invertibly.

## References

* [Stacks Project, Tag 091S](https://stacks.math.columbia.edu/tag/091S)
* [Stacks Project, Tag 0A6W](https://stacks.math.columbia.edu/tag/0A6W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace Dualizing

section Transfer

variable {A : Type u} [CommSemiring A]

/-- An additive `A`-linear functor preserving the countable power of `K` also preserves derived
completeness of `K` at an element. -/
theorem isDerivedCompleteAt_map {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear A C] [Linear A D]
    [HasProductsOfShape ℕ C] [HasProductsOfShape ℕ D]
    (F : C ⥤ D) [F.Additive] [F.Linear A] (K : C) (a : A)
    [PreservesLimit (Discrete.functor fun _ : ℕ => K) F]
    (hK : IsDerivedCompleteAt K a) : IsDerivedCompleteAt (F.obj K) a := by
  rw [isDerivedCompleteAt_iff_isIso] at hK ⊢
  let e := piComparison F fun _ : ℕ => K
  have he : e ≫ oneSubSmulShift (F.obj K) a = F.map (oneSubSmulShift K a) ≫ e := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, oneSubSmulShift_π, Preadditive.comp_sub, Linear.comp_smul,
      piComparison_comp_π, piComparison_comp_π, Category.assoc, piComparison_comp_π,
      ← F.map_comp, oneSubSmulShift_π, F.map_sub, Functor.Linear.map_smul]
  have h1 : IsIso (e ≫ oneSubSmulShift (F.obj K) a) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left e _

/-- There is at most one map from an object on which `a` acts invertibly into an object that is
derived complete at `a`. -/
theorem subsingleton_hom_of_isIso_smul_of_isDerivedCompleteAt
    {D : Type*} [Category D] [Preadditive D] [Linear A D] [HasProductsOfShape ℕ D]
    (K E : D) (x : A) [IsIso (x • 𝟙 K)] (hE : IsDerivedCompleteAt E x) :
    Subsingleton (K ⟶ E) := by
  let d := oneSubSmulShift E x
  have hd : IsIso d := hE
  let a : K ⟶ K := x • 𝟙 K
  refine ⟨fun f g => ?_⟩
  suffices f - g = 0 by simpa [sub_eq_zero] using this
  let q : ℕ → (K ⟶ E) := fun n => Nat.rec (f - g) (fun _ z => inv a ≫ z) n
  let s : K ⟶ (∏ᶜ fun _ : ℕ => E) := Pi.lift q
  have hs : s ≫ d = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [d, s, Category.assoc, oneSubSmulShift_π, Pi.lift_comp_π, Preadditive.comp_sub,
      Linear.comp_smul, zero_comp]
    rw [← Category.id_comp (q (n + 1)), ← Linear.smul_comp]
    change q n - a ≫ q (n + 1) = 0
    rw [show q (n + 1) = inv a ≫ q n by simp [q], IsIso.hom_inv_id_assoc]
    simp
  simpa [s, q] using congrArg (fun t => t ≫ Pi.π (fun _ : ℕ => E) 0)
    ((cancel_mono d).mp (show s ≫ d = 0 ≫ d by simpa using hs))

end Transfer

section Property

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- Countable products exist in `D(A)`, because countable products of `A`-modules are exact. -/
theorem hasProductsOfShape_nat_derivedCategory :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

attribute [local instance] hasProductsOfShape_nat_derivedCategory

/-- The property of an object of `D(A)` of being derived `I`-complete. -/
def derivedCompleteProperty : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
  fun K ↦ IsDerivedComplete I K

/-- The full subcategory `D_comp(A, I)` of derived `I`-complete objects of `D(A)`. -/
abbrev DerivedCompleteDerivedCategory := (derivedCompleteProperty.{u, v} A I).FullSubcategory

/-- Derived `I`-completeness is invariant under isomorphism in `D(A)`. -/
instance derivedCompleteProperty_isClosedUnderIsomorphisms :
    (derivedCompleteProperty.{u, v} A I).IsClosedUnderIsomorphisms where
  of_iso e h := DerivedCompleteRecurrence.isDerivedComplete_of_iso e h

/-- The zero object of `D(A)` is derived `I`-complete. -/
instance derivedCompleteProperty_containsZero :
    (derivedCompleteProperty.{u, v} A I).ContainsZero :=
  ⟨⟨0, isZero_zero _, fun a _ =>
    isDerivedCompleteAt_of_isNilpotent ⟨1, by
      rw [pow_one]
      ext⟩⟩⟩

variable {A I}

/-- Derived `I`-completeness is stable under shifts. -/
theorem isDerivedComplete_shift {K : DerivedCategory (ModuleCat.{v} A)}
    (hK : IsDerivedComplete I K) (n : ℤ) : IsDerivedComplete I (K⟦n⟧) := fun a ha =>
  isDerivedCompleteAt_map (shiftFunctor (DerivedCategory (ModuleCat.{v} A)) n) K a (hK a ha)

variable (A I)

/-- The derived `I`-complete objects of `D(A)` are stable under all shifts `K ↦ K⟦n⟧`. -/
instance derivedCompleteProperty_isStableUnderShift :
    (derivedCompleteProperty.{u, v} A I).IsStableUnderShift ℤ :=
  ⟨fun n => ⟨fun _ hX => isDerivedComplete_shift hX n⟩⟩

/-- In a distinguished triangle of `D(A)` whose first and third objects are derived
`I`-complete, the second object is derived `I`-complete. -/
instance derivedCompleteProperty_isTriangulatedClosed₂ :
    (derivedCompleteProperty.{u, v} A I).IsTriangulatedClosed₂ :=
  .mk' fun T hT h₁ h₃ a ha =>
    isDerivedCompleteAt_of_distTriang (rot_of_distTriang T hT) (h₃ a ha)
      (isDerivedComplete_shift h₁ 1 a ha)

/-- The derived `I`-complete objects form a triangulated subcategory of `D(A)`. -/
instance derivedCompleteProperty_isTriangulated :
    (derivedCompleteProperty.{u, v} A I).IsTriangulated := {}

/-- Any reflection of `D(A)` onto a full subcategory of derived `I`-complete objects annihilates
every object on which some element of `I` acts invertibly. -/
theorem isZero_reflector_obj_of_isIso_smul
    (P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)))
    (C : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory) (hC : C ⊣ P.ι)
    (K : DerivedCategory (ModuleCat.{v} A)) (x : A) (hx : x ∈ I) [IsIso (x • 𝟙 K)]
    (hP : ∀ E : P.FullSubcategory, IsDerivedComplete I (P.ι.obj E)) : IsZero (C.obj K) :=
  (IsZero.iff_id_eq_zero (C.obj K)).2 <| (hC.homEquiv K (C.obj K)).injective <|
    (subsingleton_hom_of_isIso_smul_of_isDerivedCompleteAt K (P.ι.obj (C.obj K)) x
      (hP (C.obj K) x hx)).elim _ _

end Property

end Dualizing

end
