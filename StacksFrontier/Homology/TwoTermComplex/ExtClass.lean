module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.TwoTermComplex.Representative

/-!
# The `Ext¹` class of a map out of the degree `-1` term of a two-term complex

Let `L` be a cochain complex of `R`-modules vanishing in degrees `≤ -2` and in degrees `> 0`,
with `L⁰` projective, and let `N` be an `R`-module. Stacks 0ALN part (1) identifies
`Hom_{K(R)}(L, N[1])` with `Hom_{D(R)}(L, N[1]) = Ext¹_R(L, N)`, and a morphism `L → N[1]` in
the homotopy category is nothing but a map `a : L^{-1} → N` taken modulo those of the form
`h ∘ d_L^{-1}`. This file turns that identification into an explicit map

`extClass : (L^{-1} ⟶ N) → Ext¹_R(L, N)`

together with the two facts that make it the cokernel description used by Stacks 0GAP:
`extClass a = 0` exactly when `a = h ∘ d_L^{-1}` for some `h : L⁰ → N`, and every class is
`extClass a` for some `a`. In other words

`Ext¹_R(L, N) = Coker (Hom_R(L⁰, N) → Hom_R(L^{-1}, N))`.

The existing API of `StacksFrontier/Homology/TwoTermComplex/Ext.lean` and
`StacksFrontier/Homology/TwoTermComplex/Representative.lean` only answers the question for *all*
classes at once — `TwoTermComplexExt.forall_Q_map_comp_eq_zero_iff` (Stacks 0ALN part (2)) and
`TwoTermComplex.ext_one_annihilated_iff_twoTerm_factorization` (Stacks 0G9F) are about an ideal
annihilating every element of every `Ext¹`. Naming one class and asking whether it vanishes is
what an obstruction class needs, and that is what is added here. Nothing in the annihilation
lemmas is touched.

## Main definitions

* `TwoTermComplexExt.toShiftSingle`: the chain map `L → N[1]` whose only nonzero component is
  the given `a : L^{-1} ⟶ N`, in degree `-1`.
* `TwoTermComplexExt.extClass`: its class in `Ext¹_R(L, N) = Hom_{D(R)}(L, N[1])`.
* `TwoTermComplexExt.extClassShifted`: the same class read in
  `DerivedCategory.Ext (Q.obj L) (N[0]) 1`, which is the shape the Ext groups of the completed
  naive cotangent complex are stated in.

## Main results

* `TwoTermComplexExt.extClass_eq_zero_iff`: `extClass a = 0 ↔ ∃ h : L⁰ ⟶ N, d_L^{-1} ≫ h = a`.
* `TwoTermComplexExt.extClass_surjective`: every class of `Ext¹_R(L, N)` is an `extClass`.
* `TwoTermComplexExt.extClass_add`: `extClass` is additive.
* `TwoTermComplexExt.extClassShifted_eq_zero_iff` and
  `TwoTermComplexExt.extClassShifted_surjective`: the same two facts for the shifted form.

Together these say that `extClass` presents `Ext¹_R(L, N)` as the cokernel of
`Hom_R(L⁰, N) → Hom_R(L^{-1}, N)`, which is the identification Stacks 0GAP invokes.

## Implementation notes

`N[1]` is `TwoTermComplexExt.shiftSingle N 1`, the shift of the complex concentrated in degree
`0`; it is concentrated in degree `-1` and all its differentials vanish, so a chain map out of
`L` is a single map in degree `-1` and the chain-map condition only constrains the incoming
differential `L^{-2} → L^{-1}`, which is zero by hypothesis. The vanishing criterion is the
bijectivity of `TwoTermComplexExt.toHomD` (Stacks 0ALN part (1)) together with the explicit
form of a null-homotopy in degree `-1`.

## References

* [Stacks Project, Tag 0ALN](https://stacks.math.columbia.edu/tag/0ALN)
* [Stacks Project, Tag 0GAP](https://stacks.math.columbia.edu/tag/0GAP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace TwoTermComplexExt

universe u v

variable {R : Type u} [Ring R] [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)]

section Construction

variable (L : CochainComplex (ModuleCat.{v} R) ℤ) (N : ModuleCat.{v} R)

omit [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)] in
/-- Every term of `N[1]` in degree at most `-2` vanishes, `N[1]` being concentrated in degree
`-1`. -/
public theorem isZero_shiftSingle_one_X_of_le (i : ℤ) (hi : i ≤ -2) :
    IsZero ((shiftSingle N 1).X i) :=
  isZero_shiftSingle_X (by omega)

/-- The chain map `L → N[1]` whose only nonzero component is `a : L^{-1} ⟶ N`, placed in degree
`-1`. The chain-map condition holds because all differentials of `N[1]` vanish and `L^{-2}` is
zero. -/
public noncomputable def toShiftSingle (hL : ∀ i ≤ (-2 : ℤ), IsZero (L.X i))
    (a : L.X (-1) ⟶ N) : L ⟶ shiftSingle N 1 where
  f i := if hi : i = -1 then
      eqToHom (show L.X i = L.X (-1) by rw [hi]) ≫ a ≫ (shiftSingleXSelf N 1).inv ≫
        eqToHom (show (shiftSingle N 1).X (-1) = (shiftSingle N 1).X i by rw [hi])
    else 0
  comm' i j hij := by
    rw [shiftSingle_d_eq_zero, comp_zero]
    by_cases hj : j = -1
    · have hi : i = -2 := by
        simp only [ComplexShape.up_Rel] at hij
        omega
      rw [(hL i (by omega)).eq_zero_of_src (L.d i j), zero_comp]
    · rw [dite_eq_right hj, comp_zero]

omit [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)] in
@[simp]
public theorem toShiftSingle_f_neg_one (hL : ∀ i ≤ (-2 : ℤ), IsZero (L.X i))
    (a : L.X (-1) ⟶ N) :
    (toShiftSingle L N hL a).f (-1) = a ≫ (shiftSingleXSelf N 1).inv := by
  change (if hi : (-1 : ℤ) = -1 then
      eqToHom (show L.X (-1) = L.X (-1) by rw [hi]) ≫ a ≫ (shiftSingleXSelf N 1).inv ≫
        eqToHom (show (shiftSingle N 1).X (-1) = (shiftSingle N 1).X (-1) by rw [hi])
    else 0) = _
  rw [dite_eq_left rfl]
  simp

omit [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)] in
@[simp]
public theorem toShiftSingle_f_of_ne (hL : ∀ i ≤ (-2 : ℤ), IsZero (L.X i))
    (a : L.X (-1) ⟶ N) (i : ℤ) (hi : i ≠ -1) : (toShiftSingle L N hL a).f i = 0 :=
  dite_eq_right hi

/-- The class in `Ext¹_R(L, N) = Hom_{D(R)}(L, N[1])` of a map `a : L^{-1} ⟶ N`. -/
public noncomputable def extClass (hL : ∀ i ≤ (-2 : ℤ), IsZero (L.X i)) (a : L.X (-1) ⟶ N) :
    ExtMod L N 1 :=
  toHomD ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map
    (toShiftSingle L N hL a))

end Construction

section Vanishing

variable (L : CochainComplex (ModuleCat.{v} R) ℤ) (N : ModuleCat.{v} R)
  (hL : ∀ i ≤ (-2 : ℤ), IsZero (L.X i))

/-- The candidate null-homotopy attached to a factorisation `h : L⁰ ⟶ N`: it is `h` in the only
slot a homotopy `L → N[1]` can occupy, namely from degree `0` to degree `-1`. -/
private noncomputable def nullHomotopyHom (h : L.X 0 ⟶ N) :
    ∀ i j : ℤ, L.X i ⟶ (shiftSingle N 1).X j := fun i j =>
  if hij : i = 0 ∧ j = -1 then
    eqToHom (show L.X i = L.X 0 by rw [hij.1]) ≫ h ≫ (shiftSingleXSelf N 1).inv ≫
      eqToHom (show (shiftSingle N 1).X (-1) = (shiftSingle N 1).X j by rw [hij.2])
  else 0

omit [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)] in
private theorem nullHomotopyHom_zero_neg_one (h : L.X 0 ⟶ N) :
    nullHomotopyHom L N h 0 (-1) = h ≫ (shiftSingleXSelf N 1).inv := by
  rw [nullHomotopyHom, dite_eq_left ⟨rfl, rfl⟩]
  simp

omit [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)] in
private theorem nullHomotopyHom_eq_zero (h : L.X 0 ⟶ N) (i j : ℤ) (hi : i ≠ 0) :
    nullHomotopyHom L N h i j = 0 := by
  rw [nullHomotopyHom, dite_eq_right (fun hij : i = 0 ∧ j = -1 => hi hij.1)]

omit [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)] in
private theorem nullHomotopyHom_eq_zero' (h : L.X 0 ⟶ N) (i j : ℤ)
    (hij : ¬ (ComplexShape.up ℤ).Rel j i) : nullHomotopyHom L N h i j = 0 := by
  have hc : ¬ (i = 0 ∧ j = -1) := by
    rintro ⟨hi, hj⟩
    subst hi
    subst hj
    exact hij (by norm_num [ComplexShape.up_Rel])
  rw [nullHomotopyHom, dite_eq_right hc]

omit [Small.{v} R] in
/-- A map out of `L^{-1}` which factors through the differential has vanishing class: the
factorisation is a null-homotopy of the corresponding chain map `L → N[1]`. -/
public theorem extClass_eq_zero_of_factors (a : L.X (-1) ⟶ N) (h : L.X 0 ⟶ N)
    (hh : L.d (-1) 0 ≫ h = a) : extClass L N hL a = 0 := by
  classical
  have hprev : ∀ j : ℤ, prevD j (nullHomotopyHom L N h) = 0 := by
    intro j
    rw [prevD_eq (nullHomotopyHom L N h)
        (show (ComplexShape.up ℤ).Rel (j - 1) j by simp [ComplexShape.up_Rel]),
      shiftSingle_d_eq_zero, comp_zero]
  have hdnext : ∀ j : ℤ, dNext j (nullHomotopyHom L N h)
      = L.d j (j + 1) ≫ nullHomotopyHom L N h (j + 1) j := fun j =>
    dNext_eq (nullHomotopyHom L N h)
      (show (ComplexShape.up ℤ).Rel j (j + 1) by simp [ComplexShape.up_Rel])
  let H : Homotopy (toShiftSingle L N hL a) 0 :=
    { hom := nullHomotopyHom L N h
      zero := fun i j hij => nullHomotopyHom_eq_zero' L N h i j hij
      comm := by
        intro i
        rw [hdnext i, hprev i]
        simp only [add_zero, HomologicalComplex.zero_f]
        by_cases hi : i = -1
        · subst hi
          rw [show ((-1 : ℤ) + 1) = 0 from by norm_num, toShiftSingle_f_neg_one,
            nullHomotopyHom_zero_neg_one, ← Category.assoc, hh]
        · rw [toShiftSingle_f_of_ne L N hL a i hi,
            nullHomotopyHom_eq_zero L N h (i + 1) i (by omega), comp_zero] }
  rw [extClass, HomotopyCategory.eq_of_homotopy _ _ H, Functor.map_zero, toHomD_zero]


omit [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)] in
/-- Every term of `N[1]` outside degree `-1` vanishes. -/
public theorem isZero_shiftSingle_one_X_of_ne (i : ℤ) (hi : i ≠ -1) :
    IsZero ((shiftSingle N 1).X i) :=
  isZero_shiftSingle_X (by omega)

/-- The comparison `Hom_{K(R)}(L, N[1]) → Hom_{D(R)}(L, N[1])` is bijective: this is Stacks
0ALN part (1) applied to `N[1]`, whose terms vanish in degrees at most `-2`. -/
public theorem toHomD_shiftSingle_bijective
    (hLpos : ∀ i : ℤ, 0 < i → IsZero (L.X i)) (hL0 : Projective (L.X 0)) :
    Function.Bijective
      (fun f : HomK L (shiftSingle N 1) => (toHomD f : HomD L (shiftSingle N 1))) :=
  toHomD_bijective L (shiftSingle N 1) hLpos hL0
    (fun i hi => isZero_shiftSingle_one_X_of_le N i hi)

/-- A map out of `L^{-1}` with vanishing class factors through the differential. -/
public theorem exists_factors_of_extClass_eq_zero
    (hLpos : ∀ i : ℤ, 0 < i → IsZero (L.X i)) (hL0 : Projective (L.X 0))
    (a : L.X (-1) ⟶ N) (ha : extClass L N hL a = 0) :
    ∃ h : L.X 0 ⟶ N, L.d (-1) 0 ≫ h = a := by
  have hzero : (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map
      (toShiftSingle L N hL a) = 0 := by
    refine (toHomD_shiftSingle_bijective L N hLpos hL0).injective ?_
    change toHomD _ = toHomD (0 : HomK L (shiftSingle N 1))
    rw [toHomD_zero]
    exact ha
  obtain ⟨H⟩ : Nonempty (Homotopy (toShiftSingle L N hL a) 0) :=
    ⟨HomotopyCategory.homotopyOfEq _ _ (by rw [hzero, Functor.map_zero])⟩
  refine ⟨H.hom 0 (-1) ≫ (shiftSingleXSelf N 1).hom, ?_⟩
  have hcomm := H.comm (-1)
  rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel (-1 : ℤ) 0 by simp [ComplexShape.up_Rel]),
    prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (-2 : ℤ) (-1) by simp [ComplexShape.up_Rel]),
    shiftSingle_d_eq_zero] at hcomm
  simp only [comp_zero, add_zero, HomologicalComplex.zero_f] at hcomm
  rw [toShiftSingle_f_neg_one] at hcomm
  rw [← Category.assoc, ← hcomm, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The cokernel presentation of `Ext¹`, derived from Stacks 0ALN(1).
The class of `a : L^{-1} ⟶ N` in `Ext¹_R(L, N)`
vanishes exactly when `a` factors through the differential `d_L^{-1} : L^{-1} → L⁰`. This is the
kernel half of the identification
`Ext¹_R(L, N) = Coker (Hom_R(L⁰, N) → Hom_R(L^{-1}, N))`. -/
public theorem extClass_eq_zero_iff
    (hLpos : ∀ i : ℤ, 0 < i → IsZero (L.X i)) (hL0 : Projective (L.X 0))
    (a : L.X (-1) ⟶ N) :
    extClass L N hL a = 0 ↔ ∃ h : L.X 0 ⟶ N, L.d (-1) 0 ≫ h = a :=
  ⟨exists_factors_of_extClass_eq_zero L N hL hLpos hL0 a,
   fun ⟨h, hh⟩ => extClass_eq_zero_of_factors L N hL a h hh⟩

omit [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)] in
/-- Two chain maps `L → N[1]` are equal when their degree `-1` components are. -/
private theorem hom_ext_shiftSingle_one {f g : L ⟶ shiftSingle N 1}
    (h : f.f (-1) = g.f (-1)) : f = g := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases hi : i = -1
  · subst hi
    exact h
  · exact (isZero_shiftSingle_one_X_of_ne N i hi).eq_of_tgt _ _

/-- The cokernel presentation of `Ext¹`, derived from Stacks 0ALN(1).
Every class of `Ext¹_R(L, N)` is the class of a
map `L^{-1} ⟶ N`: the surjectivity half of the identification. -/
public theorem extClass_surjective
    (hLpos : ∀ i : ℤ, 0 < i → IsZero (L.X i)) (hL0 : Projective (L.X 0))
    (ξ : ExtMod L N 1) : ∃ a : L.X (-1) ⟶ N, extClass L N hL a = ξ := by
  obtain ⟨c, hc⟩ := (toHomD_shiftSingle_bijective L N hLpos hL0).surjective ξ
  obtain ⟨f, hf⟩ := (HomotopyCategory.quotient (ModuleCat.{v} R)
    (ComplexShape.up ℤ)).map_surjective c
  have heq : toShiftSingle L N hL (f.f (-1) ≫ (shiftSingleXSelf N 1).hom) = f :=
    hom_ext_shiftSingle_one L N (by
      rw [toShiftSingle_f_neg_one, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  exact ⟨f.f (-1) ≫ (shiftSingleXSelf N 1).hom, by rw [extClass, heq, hf]; exact hc⟩

omit [Small.{v} R] [HasDerivedCategory (ModuleCat.{v} R)] in
public theorem toShiftSingle_add (a b : L.X (-1) ⟶ N) :
    toShiftSingle L N hL (a + b) = toShiftSingle L N hL a + toShiftSingle L N hL b := by
  exact hom_ext_shiftSingle_one L N (by simp [Preadditive.add_comp])

omit [Small.{v} R] in
public theorem toHomD_add {M K : CochainComplex (ModuleCat.{v} R) ℤ} (f g : HomK M K) :
    (toHomD (f + g) : HomD M K) = toHomD f + toHomD g := by
  simp only [toHomD_eq, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

omit [Small.{v} R] in
/-- `extClass` is additive. With `extClass_eq_zero_iff` and `extClass_surjective` this exhibits
`Ext¹_R(L, N)` as the cokernel of `Hom_R(L⁰, N) → Hom_R(L^{-1}, N)`, the identification Stacks
0GAP invokes. -/
public theorem extClass_add (a b : L.X (-1) ⟶ N) :
    extClass L N hL (a + b) = extClass L N hL a + extClass L N hL b := by
  rw [extClass, extClass, extClass, toShiftSingle_add, Functor.map_add, toHomD_add]

end Vanishing

section Shifted

variable (L : CochainComplex (ModuleCat.{v} R) ℤ) (N : ModuleCat.{v} R)
  (hL : ∀ i ≤ (-2 : ℤ), IsZero (L.X i))

/-- `Q(N[1])` is the shift of the image of the complex concentrated in degree `0`: the
comparison that turns `Hom_{D(R)}(L, N[1])` into `DerivedCategory.Ext (Q L) (N[0]) 1`. -/
public noncomputable def shiftSingleTargetIso :
    DerivedCategory.Q.obj (shiftSingle N 1) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)⟦(1 : ℤ)⟧ :=
  ((DerivedCategory.Q (C := ModuleCat.{v} R)).commShiftIso (1 : ℤ)).app
    ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj N)

/-- The class of `a : L^{-1} ⟶ N` as an element of
`DerivedCategory.Ext (Q.obj L) ((singleFunctor _ 0).obj N) 1`. -/
public noncomputable def extClassShifted (a : L.X (-1) ⟶ N) :
    DerivedCategory.Ext (DerivedCategory.Q.obj L)
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1 :=
  extClass L N hL a ≫ (shiftSingleTargetIso N).hom

omit [Small.{v} R] in
public theorem extClassShifted_eq (a : L.X (-1) ⟶ N) :
    extClassShifted L N hL a = extClass L N hL a ≫ (shiftSingleTargetIso N).hom := rfl

/-- The cokernel presentation of `Ext¹`, derived from Stacks 0ALN(1),
in shifted form. -/
public theorem extClassShifted_eq_zero_iff
    (hLpos : ∀ i : ℤ, 0 < i → IsZero (L.X i)) (hL0 : Projective (L.X 0))
    (a : L.X (-1) ⟶ N) :
    extClassShifted L N hL a = 0 ↔ ∃ h : L.X 0 ⟶ N, L.d (-1) 0 ≫ h = a := by
  rw [← extClass_eq_zero_iff L N hL hLpos hL0 a, extClassShifted_eq]
  refine ⟨fun hz => ?_, fun hz => by rw [hz, zero_comp]⟩
  exact (cancel_mono (shiftSingleTargetIso N).hom).mp (by rw [hz, zero_comp])

/-- The cokernel presentation of `Ext¹`, derived from Stacks 0ALN(1),
in shifted form. -/
public theorem extClassShifted_surjective
    (hLpos : ∀ i : ℤ, 0 < i → IsZero (L.X i)) (hL0 : Projective (L.X 0))
    (ξ : DerivedCategory.Ext (DerivedCategory.Q.obj L)
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1) :
    ∃ a : L.X (-1) ⟶ N, extClassShifted L N hL a = ξ := by
  obtain ⟨a, ha⟩ := extClass_surjective L N hL hLpos hL0 (ξ ≫ (shiftSingleTargetIso N).inv)
  exact ⟨a, by rw [extClassShifted_eq, ha, Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩

omit [Small.{v} R] in
public theorem extClassShifted_add (a b : L.X (-1) ⟶ N) :
    extClassShifted L N hL (a + b) = extClassShifted L N hL a + extClassShifted L N hL b := by
  rw [extClassShifted_eq, extClassShifted_eq, extClassShifted_eq, extClass_add,
    Preadditive.add_comp]

end Shifted

end TwoTermComplexExt

end
