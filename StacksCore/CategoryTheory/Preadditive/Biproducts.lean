module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksCore.CategoryTheory.Limits.Shapes.BinaryBiproducts
import StacksCore.Tactic.StacksAttribute

/-! ## Biproducts in preadditive categories.

Besides the Stacks attributions, `Limits.isPullback_biprod_desc_id_iff`: in a preadditive category
with the relevant binary biproducts, the fold square `𝟙 ⊕ 𝟙` over `m` is a pullback if and only if
`m` is an isomorphism. -/

add_to_stacks 0101 CategoryTheory.Limits.HasBinaryBiproduct.of_hasBinaryProduct
add_to_stacks 0101 CategoryTheory.Limits.HasBinaryBiproduct.of_hasBinaryCoproduct
add_to_stacks 0103 CategoryTheory.Limits.isBinaryBilimitOfTotal

@[expose] public section

open CategoryTheory Limits

/-- Two complementary split idempotents on `Z` — split monos `iX`, `iY` with retractions `rX`, `rY`
whose associated projections sum to the identity — assemble into a binary bicone with apex `Z`. -/
@[implicit_reducible, simps]
def CategoryTheory.Limits.BinaryBicone.mk' {C : Type*} [Category* C] [Preadditive C] {X Y Z : C}
    {iX : X ⟶ Z} {rX : Z ⟶ X} {iY : Y ⟶ Z} {rY : Z ⟶ Y} (hiX : iX ≫ rX = 𝟙 X)
    (hiY : iY ≫ rY = 𝟙 Y) (htot : rX ≫ iX + rY ≫ iY = 𝟙 Z) : BinaryBicone X Y where
  pt := Z
  fst := rX
  snd := rY
  inl := iX
  inr := iY
  inl_snd := by
    have h : (iX ≫ rY) ≫ iY = 0 := by
      simpa [Preadditive.comp_add, ← Category.assoc, hiX] using congrArg (iX ≫ ·) htot
    rw [← Category.comp_id (iX ≫ rY), ← hiY, ← Category.assoc, h, zero_comp]
  inr_fst := by
    have h : (iY ≫ rX) ≫ iX = 0 := by
      simpa [Preadditive.comp_add, ← Category.assoc, hiY] using congrArg (iY ≫ ·) htot
    rw [← Category.comp_id (iY ≫ rX), ← hiX, ← Category.assoc, h, zero_comp]

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C]

/-- In a preadditive category with the two biproducts, the square of the fold map `𝟙 ⊕ 𝟙` over
`m` is a pullback if and only if `m` is an isomorphism: the antidiagonal `(x, -x)` lies over `0`,
so the pullback property splits `m`, and `(k, -k)` and `0` agree on both legs whenever
`k ≫ m = 0`, so `m` is a monomorphism. -/
lemma isPullback_biprod_desc_id_iff {S X : C} [HasBinaryBiproduct S S]
    [HasBinaryBiproduct X X] (m : S ⟶ X) :
    IsPullback (biprod.desc (𝟙 S) (𝟙 S)) (biprod.map m m) m (biprod.desc (𝟙 X) (𝟙 X)) ↔
      IsIso m := by
  refine ⟨fun hP => ?_, fun _ => ?_⟩
  · have : Mono m := by
      rw [Preadditive.mono_iff_cancel_zero]
      intro T k hk
      have h := hP.hom_ext (k := biprod.lift k (-k)) (l := 0)
        (by simp [biprod.lift_desc]) (by ext <;> simp [hk])
      simpa using h =≫ biprod.fst
    have w : (0 : X ⟶ S) ≫ m = biprod.lift (𝟙 X) (-𝟙 X) ≫ biprod.desc (𝟙 X) (𝟙 X) := by simp
    have hsec : (hP.lift 0 (biprod.lift (𝟙 X) (-𝟙 X)) w ≫ biprod.fst) ≫ m = 𝟙 X := by
      rw [Category.assoc, ← biprod.map_fst m m, hP.lift_snd_assoc, biprod.lift_fst]
    have : IsSplitEpi m := IsSplitEpi.mk' ⟨_, hsec⟩
    exact isIso_of_mono_of_isSplitEpi m
  · have : IsIso (biprod.map m m) :=
      inferInstanceAs (IsIso (biprod.mapIso (asIso m) (asIso m)).hom)
    exact IsPullback.of_vert_isIso ⟨by simp [biprod.map_desc]⟩

end CategoryTheory.Limits
