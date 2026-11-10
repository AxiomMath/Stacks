module

public import StacksFrontier.CategoryTheory.Monoidal.MateAsInternalHomPre
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import StacksCore.CategoryTheory.Monoidal.Rigid.Biproducts

/-!
# The mate of a map between finite products of the unit object

Let `C` be a monoidal preadditive category and let `A`, `B` be finite types. A morphism
`g : ∏_A 𝟙 ⟶ ∏_B 𝟙` between finite products of copies of the unit object is a matrix
`c_{ab} = ι_a ≫ g ≫ π_b` of endomorphisms of `𝟙`. If `∏_A 𝟙` and `∏_B 𝟙` are paired with
products `∏_{A'} 𝟙`, `∏_{B'} 𝟙` over reindexings `A ≃ A'`, `B ≃ B'` by the *standard* pairings,
whose evaluation is the sum over `a` of the products of the `a`-th projections, then the mate of
`g` is the map with the transposed matrix:

`mate g ≫ π_{a'} = ∑_b π_{b'} ≫ c_{ab}`.

No mate of an entry appears: the entries are endomorphisms of the unit, and an endomorphism of
the unit commutes past both unitors of `𝟙 ⊗ 𝟙`.

## Main definitions

* `CategoryTheory.ExactPairing.unitPiι`: the inclusion of the `a`-th factor into `∏_A 𝟙`.

## Main results

* `CategoryTheory.ExactPairing.mate_comp_π_of_evaluation`: the matrix of the mate is the
  transposed matrix.

## Implementation notes

The reindexings `A ≃ A'` are there because in the application the dual of the degree-`n` term of
a complex is its degree-`-(-n)` term, whose index type is propositionally but not definitionally
the index type of the degree-`n` term. The mate is pinned down by
`CategoryTheory.ExactPairing.eq_mate` from the evaluations alone, so only the evaluations of the
two pairings are assumed.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace CategoryTheory.ExactPairing

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

/-- The inclusion of the `a`-th factor into a finite product of copies of the unit. -/
def unitPiι {A : Type*} [DecidableEq A] [HasProduct fun _ : A => 𝟙_ C] (a : A) :
    𝟙_ C ⟶ ∏ᶜ fun _ : A => 𝟙_ C :=
  Pi.lift fun a' => if a' = a then 𝟙 _ else 0

omit [MonoidalPreadditive C] in
/-- The `a'`-th component of the inclusion of the `a`-th factor of a finite product of copies of
the unit is the identity if `a' = a` and zero otherwise. -/
@[reassoc (attr := simp)]
theorem unitPiι_π {A : Type*} [DecidableEq A] [HasProduct fun _ : A => 𝟙_ C] (a a' : A) :
    unitPiι (C := C) a ≫ Pi.π _ a' = if a' = a then 𝟙 _ else 0 :=
  Pi.lift_comp_π _ _

omit [MonoidalPreadditive C] in
/-- The sum over `a` of the `a`-th projection followed by the `a`-th inclusion is the identity of
a finite product of copies of the unit. -/
theorem sum_π_unitPiι {A : Type*} [Fintype A] [DecidableEq A] [HasProduct fun _ : A => 𝟙_ C] :
    ∑ a, Pi.π (fun _ : A => 𝟙_ C) a ≫ unitPiι a = 𝟙 _ := by
  refine Pi.hom_ext _ _ fun a' => ?_
  simp only [Preadditive.sum_comp, Category.assoc, unitPiι_π, Category.id_comp]
  rw [Finset.sum_eq_single a' (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

omit [Preadditive C] [MonoidalPreadditive C] in
/-- An endomorphism of the unit moves from the left to the right factor of a tensor product of
two maps into the unit, after the unitor. -/
theorem tensorHom_comp_leftUnitor_swap {Z W : C} (x : Z ⟶ 𝟙_ C) (y : W ⟶ 𝟙_ C)
    (c : 𝟙_ C ⟶ 𝟙_ C) :
    ((x ≫ c) ⊗ₘ y) ≫ (λ_ (𝟙_ C)).hom = (x ⊗ₘ (y ≫ c)) ≫ (λ_ (𝟙_ C)).hom := by
  have h₁ := tensorHom_comp_tensorHom x y c (𝟙 _)
  have h₂ := tensorHom_comp_tensorHom x y (𝟙 _) c
  simp only [Category.comp_id] at h₁ h₂
  rw [← h₁, ← h₂, Category.assoc, Category.assoc, tensorHom_id, id_tensorHom, unitors_equal,
    rightUnitor_naturality, ← unitors_equal, leftUnitor_naturality]

variable {A A' B B' : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [HasProduct fun _ : A => 𝟙_ C] [HasProduct fun _ : A' => 𝟙_ C]
  [HasProduct fun _ : B => 𝟙_ C] [HasProduct fun _ : B' => 𝟙_ C]

omit [DecidableEq B] in
/-- **The matrix of the mate of a map between products of the unit is the transposed matrix.**
For pairings of `∏_A 𝟙` with `∏_{A'} 𝟙` and of `∏_B 𝟙` with `∏_{B'} 𝟙` whose evaluations are the
standard ones along `ea : A ≃ A'` and `eb : B ≃ B'`, the `ea a`-th component of the mate of `g` is
the sum over `b` of the `eb b`-th projection followed by the `(a, b)` entry of `g`. -/
theorem mate_comp_π_of_evaluation (ea : A ≃ A') (eb : B ≃ B')
    (P : ExactPairing (∏ᶜ fun _ : A => 𝟙_ C) (∏ᶜ fun _ : A' => 𝟙_ C))
    (hP : P.evaluation' =
      ∑ a, (Pi.π (fun _ : A' => 𝟙_ C) (ea a) ⊗ₘ Pi.π (fun _ : A => 𝟙_ C) a) ≫ (λ_ (𝟙_ C)).hom)
    (Q : ExactPairing (∏ᶜ fun _ : B => 𝟙_ C) (∏ᶜ fun _ : B' => 𝟙_ C))
    (hQ : Q.evaluation' =
      ∑ b, (Pi.π (fun _ : B' => 𝟙_ C) (eb b) ⊗ₘ Pi.π (fun _ : B => 𝟙_ C) b) ≫ (λ_ (𝟙_ C)).hom)
    (g : (∏ᶜ fun _ : A => 𝟙_ C) ⟶ ∏ᶜ fun _ : B => 𝟙_ C) (a : A) :
    mate P Q g ≫ Pi.π _ (ea a) =
      ∑ b, Pi.π (fun _ : B' => 𝟙_ C) (eb b) ≫ (unitPiι a ≫ g ≫ Pi.π _ b) := by
  let h : (∏ᶜ fun _ : B' => 𝟙_ C) ⟶ ∏ᶜ fun _ : A' => 𝟙_ C := Pi.lift fun a' =>
    ∑ b, Pi.π (fun _ : B' => 𝟙_ C) (eb b) ≫ (unitPiι (ea.symm a') ≫ g ≫ Pi.π _ b)
  have hh : h = mate P Q g := by
    refine eq_mate P Q g h ?_
    rw [hP, hQ, Preadditive.comp_sum, Preadditive.comp_sum]
    have hL : ∀ a : A, h ▷ _ ≫ (Pi.π (fun _ : A' => 𝟙_ C) (ea a) ⊗ₘ
          Pi.π (fun _ : A => 𝟙_ C) a) ≫ (λ_ (𝟙_ C)).hom =
        ∑ b, ((Pi.π (fun _ : B' => 𝟙_ C) (eb b) ≫ (unitPiι a ≫ g ≫ Pi.π _ b)) ⊗ₘ
          Pi.π (fun _ : A => 𝟙_ C) a) ≫ (λ_ (𝟙_ C)).hom := by
      intro a
      rw [← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp,
        Pi.lift_comp_π, Equiv.symm_apply_apply, sum_tensor, Preadditive.sum_comp]
    have hR : ∀ b : B, _ ◁ g ≫ (Pi.π (fun _ : B' => 𝟙_ C) (eb b) ⊗ₘ
          Pi.π (fun _ : B => 𝟙_ C) b) ≫ (λ_ (𝟙_ C)).hom =
        ∑ a, (Pi.π (fun _ : B' => 𝟙_ C) (eb b) ⊗ₘ
          (Pi.π (fun _ : A => 𝟙_ C) a ≫ (unitPiι a ≫ g ≫ Pi.π _ b))) ≫
            (λ_ (𝟙_ C)).hom := by
      intro b
      rw [← Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
      conv_lhs => rw [← Category.id_comp (g ≫ Pi.π _ b), ← sum_π_unitPiι, Preadditive.sum_comp]
      rw [tensor_sum, Preadditive.sum_comp]
      exact Finset.sum_congr rfl fun a _ => by rw [Category.assoc]
    rw [Finset.sum_congr rfl fun a _ => hL a, Finset.sum_congr rfl fun b _ => hR b,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
      tensorHom_comp_leftUnitor_swap _ _ _
  rw [← hh, Pi.lift_comp_π, Equiv.symm_apply_apply]

section Biproduct

variable {A : Type} [Fintype A] [HasFiniteBiproducts C]

/-- **The standard pairing of a finite product of the unit with itself**: the biproduct pairing of
[Stacks, Tag 0FFT] of copies of `CategoryTheory.exactPairingUnit`, transported to the product,
evaluates as the sum of the products of the projections. -/
theorem evaluation_exactPairingCongr_biproduct_unit :
    (@exactPairingCongr C _ _ (∏ᶜ fun _ : A => 𝟙_ C) (⨁ fun _ : A => 𝟙_ C)
        (∏ᶜ fun _ : A => 𝟙_ C) (⨁ fun _ : A => 𝟙_ C)
        (letI : ∀ _ : A, ExactPairing (𝟙_ C) (𝟙_ C) := fun _ => exactPairingUnit
         ExactPairing.biproduct)
        (biproduct.isoProduct _).symm (biproduct.isoProduct _).symm).evaluation' =
      ∑ a, (Pi.π (fun _ : A => 𝟙_ C) a ⊗ₘ Pi.π (fun _ : A => 𝟙_ C) a) ≫ (λ_ (𝟙_ C)).hom := by
  change (∏ᶜ fun _ : A => 𝟙_ C) ◁ (biproduct.isoProduct _).inv ≫
      (biproduct.isoProduct _).inv ▷ _ ≫
        ∑ a, (biproduct.π (fun _ : A => 𝟙_ C) a ⊗ₘ biproduct.π (fun _ : A => 𝟙_ C) a) ≫
          (ρ_ (𝟙_ C)).hom = _
  rw [Preadditive.comp_sum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Category.assoc, ← Category.assoc, ← id_tensorHom, ← tensorHom_id,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    biproduct.isoProduct_inv, biproduct.lift_π, unitors_equal]

end Biproduct

end CategoryTheory.ExactPairing

end

end
