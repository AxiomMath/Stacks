module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# A Mayer–Vietoris short complex with an invertible edge is split

A *Mayer–Vietoris short complex* is a short complex of the shape

`M --(a, -b)--> N ⊞ V --(g, d)--> A`

in a preadditive category with binary biproducts.  Two degenerate cases of such a complex are
short exact for purely formal reasons, and they are the two cases the Mayer–Vietoris sequence
of an elementary distinguished square falls into at a geometric point:

* `b` and `g` are invertible.  Then `-b⁻¹` composed with the projection to `V` retracts the
  first map, `g⁻¹` composed with the inclusion of `N` sections the second, and the two are
  complementary idempotents because the complex condition `a ≫ g = b ≫ d` says exactly that
  `b⁻¹ ≫ a` and `d ≫ g⁻¹` agree.
* `M` and `N` are zero and `d` is invertible.  Then the complex is the identity of `V` read
  through the biproduct.

## Main definitions

* `CategoryTheory.ShortComplex.mayerVietoris` is the short complex above.
* `CategoryTheory.ShortComplex.mayerVietorisSplittingOfIsIso` and
  `CategoryTheory.ShortComplex.mayerVietorisSplittingOfIsZero` are its splittings in the two
  cases.

## Main results

* `CategoryTheory.ShortComplex.mayerVietoris_shortExact_of_isIso` and
  `CategoryTheory.ShortComplex.mayerVietoris_shortExact_of_isZero`: in the two cases the
  complex is short exact.

## Implementation notes

Both cases are proved by exhibiting a `CategoryTheory.ShortComplex.Splitting`, which is
stronger than short exactness and needs no hypothesis on the category beyond a zero object:
no kernel, image or homology is computed.  The invertibility of one of the two maps out of the
biproduct is what makes the splitting available, and no hypothesis is placed on the remaining
maps `a` and `d` other than the complex condition — which is as it must be, since at a
geometric point lying on the open subspace of an elementary distinguished square the map `a`
really is arbitrary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {M N V A : C} (a : M ⟶ N) (b : M ⟶ V) (g : N ⟶ A) (d : V ⟶ A)
  (h : biprod.lift a (-b) ≫ biprod.desc g d = 0)

/-- The **Mayer–Vietoris short complex** `M ⟶ N ⊞ V ⟶ A` attached to four maps whose
alternating composite vanishes. -/
def mayerVietoris : ShortComplex C :=
  ShortComplex.mk (biprod.lift a (-b)) (biprod.desc g d) h

/-- The complex condition of a Mayer–Vietoris short complex, read as the commutativity of the
square of its four maps. -/
theorem comp_eq_comp_of_mayerVietoris
    (h₀ : biprod.lift a (-b) ≫ biprod.desc g d = 0) : a ≫ g = b ≫ d := by
  have h' := h₀
  rw [biprod.lift_desc] at h'
  rw [Preadditive.neg_comp] at h'
  exact eq_of_sub_eq_zero (by rw [← sub_eq_add_neg] at h'; exact h')

/-- Minus the projection to `V` followed by `b⁻¹` retracts the first map of a Mayer–Vietoris
short complex whose edge to `V` is invertible. -/
theorem mv_f_r [IsIso b] :
    biprod.lift a (-b) ≫ (-(biprod.snd ≫ inv b) : N ⊞ V ⟶ M) = 𝟙 M := by
  simp

/-- `g⁻¹` followed by the inclusion of `N` sections the second map of a Mayer–Vietoris short
complex whose map out of `N` is invertible. -/
theorem mv_s_g [IsIso g] :
    (inv g ≫ biprod.inl : A ⟶ N ⊞ V) ≫ biprod.desc g d = 𝟙 A := by
  simp

/-- That retraction and that section are complementary, which is where the complex condition of
a Mayer–Vietoris short complex is used. -/
theorem mv_id [IsIso b] [IsIso g]
    (h₀ : biprod.lift a (-b) ≫ biprod.desc g d = 0) :
    (-(biprod.snd ≫ inv b) : N ⊞ V ⟶ M) ≫ biprod.lift a (-b) +
      biprod.desc g d ≫ (inv g ≫ biprod.inl : A ⟶ N ⊞ V) = 𝟙 (N ⊞ V) := by
  have hab : a ≫ g = b ≫ d := comp_eq_comp_of_mayerVietoris a b g d h₀
  have key : inv b ≫ a = d ≫ inv g := by
    refine (cancel_mono g).1 ?_
    rw [Category.assoc, hab, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine biprod.hom_ext' _ _ ?_ ?_
  · refine biprod.hom_ext _ _ ?_ ?_ <;> simp
  · refine biprod.hom_ext _ _ ?_ ?_ <;> simp [key]

/-- **A Mayer–Vietoris short complex whose edge to `V` and whose map out of `N` are invertible
is split.**  The retraction of the first map is minus the projection to `V` followed by `b⁻¹`,
the section of the second is `g⁻¹` followed by the inclusion of `N`, and the complex condition
makes the two complementary. -/
def mayerVietorisSplittingOfIsIso [IsIso b] [IsIso g] :
    (mayerVietoris a b g d h).Splitting where
  r := (-(biprod.snd ≫ inv b) : N ⊞ V ⟶ M)
  s := (inv g ≫ biprod.inl : A ⟶ N ⊞ V)
  f_r := mv_f_r a b
  s_g := mv_s_g g d
  id := mv_id a b g d h

/-- `d⁻¹` followed by the inclusion of `V` sections the second map of a Mayer–Vietoris short
complex whose edge `d` is invertible. -/
theorem mvz_s_g [IsIso d] :
    (inv d ≫ biprod.inr : A ⟶ N ⊞ V) ≫ biprod.desc g d = 𝟙 A := by
  simp

/-- With `N` zero that section is complementary to the zero retraction. -/
theorem mvz_id (hN : IsZero N) [IsIso d] :
    (0 : N ⊞ V ⟶ M) ≫ biprod.lift a (-b) +
      biprod.desc g d ≫ (inv d ≫ biprod.inr : A ⟶ N ⊞ V) = 𝟙 (N ⊞ V) := by
  rw [Limits.zero_comp, zero_add]
  refine biprod.hom_ext' _ _ ?_ ?_
  · exact hN.eq_of_src _ _
  · simp

/-- **A Mayer–Vietoris short complex whose outer source and whose summand `N` are zero and
whose edge `d` is invertible is split.** -/
def mayerVietorisSplittingOfIsZero (hM : IsZero M) (hN : IsZero N) [IsIso d] :
    (mayerVietoris a b g d h).Splitting where
  r := (0 : N ⊞ V ⟶ M)
  s := (inv d ≫ biprod.inr : A ⟶ N ⊞ V)
  f_r := hM.eq_of_src _ _
  s_g := mvz_s_g g d
  id := mvz_id a b g d hN

variable [HasZeroObject C]

/-- **A Mayer–Vietoris short complex whose edge to `V` and whose map out of `N` are invertible
is short exact.** -/
theorem mayerVietoris_shortExact_of_isIso [IsIso b] [IsIso g] :
    (mayerVietoris a b g d h).ShortExact :=
  (mayerVietorisSplittingOfIsIso a b g d h).shortExact

/-- **A Mayer–Vietoris short complex whose outer source and whose summand `N` are zero and
whose edge `d` is invertible is short exact.** -/
theorem mayerVietoris_shortExact_of_isZero (hM : IsZero M) (hN : IsZero N) [IsIso d] :
    (mayerVietoris a b g d h).ShortExact :=
  (mayerVietorisSplittingOfIsZero a b g d h hM hN).shortExact

end CategoryTheory.ShortComplex

end
