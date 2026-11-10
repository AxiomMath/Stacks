module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic

/-!
# Dévissage for bijectivity on `Ext`

Let `F` be an exact functor between abelian categories and `X` an object of its source. This file
proves closure properties of the class of objects `Y` such that `F` is bijective on `Ext` from `X`
into `Y`, stated directly and through `Stacks.EtaleCohomology.IsBijectiveOnExt`. For the inverse
image along a morphism of schemes these are closure steps of the dévissage proving part (7) of
[Stacks, Tag 03SC]; closure under extensions is the corresponding case of [Stacks, Tag 0A5C].

## Main results

* `Stacks.EtaleCohomology.mapExt_bijective_of_shortExact`: if an exact functor is bijective on
  `Ext` out of a fixed object into the outer two terms of a short exact sequence in every degree,
  then it is bijective on `Ext` into the middle term in every degree.
* `Stacks.EtaleCohomology.mapExt_bijective_of_retract`: bijectivity on `Ext` in a given degree
  passes to a retract in the second variable.
* `Stacks.EtaleCohomology.isBijectiveOnExt_of_shortExact`: the first statement phrased through
  `IsBijectiveOnExt`.
* `Stacks.EtaleCohomology.isBijectiveOnExt_biprod`: closure under binary biproducts.
* `Stacks.EtaleCohomology.isBijectiveOnExt_of_retract`: closure under retracts in the second
  variable.

## Implementation notes

In degree `0`, injectivity in `mapExt_bijective_of_shortExact` comes from the four lemma with a
zero map on the left, since the covariant long exact sequence of `Ext`, indexed by `ℕ`, has no term
to the left of `Ext X S.X₁ 0`.

## References

* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian

namespace Stacks.EtaleCohomology

universe w w' w₃ v₁ v₂ v₃ u₁ u₂ u₃

section Devissage

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- If `i ≫ p = 𝟙 Y'` then postcomposition with `i` followed by postcomposition with `p` is the
identity of `Ext X Y' n`. -/
private lemma comp_mk₀_comp_mk₀_of_comp_eq_id {E : Type u₃} [Category.{v₃} E] [Abelian E]
    [HasExt.{w₃} E] {X Y Y' : E} (i : Y' ⟶ Y) (p : Y ⟶ Y') (hip : i ≫ p = 𝟙 Y') {n : ℕ}
    (z : Ext.{w₃} X Y' n) :
    (z.comp (Ext.mk₀ i) (add_zero n)).comp (Ext.mk₀ p) (add_zero n) = z := by
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hip, Ext.comp_mk₀_id]

/-- A short complex of abelian groups beginning with the zero map is exact exactly when its second
map is injective. -/
private lemma exact_zero_left {A : Type*} {B : Type*} [AddCommGroup A] [AddCommGroup B]
    (g : A →+ B) (hg : Function.Injective g) : Function.Exact (0 : A →+ A) g := by
  intro b
  refine ⟨fun h => ⟨0, ?_⟩, ?_⟩
  · simpa using (hg (h.trans (map_zero g).symm)).symm
  · rintro ⟨a, ha⟩
    simp [← ha]

/-- Exactness of a short complex in `AddCommGrpCat` gives exactness of the underlying functions. -/
private lemma function_exact_of_exact {S : ShortComplex AddCommGrpCat} (h : S.Exact) :
    Function.Exact S.f S.g :=
  (ShortComplex.ab_exact_iff_function_exact _).1 h

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀
  Ext.mapExactFunctor_extClass

/-- **Dévissage for bijectivity on `Ext`.** Let `F` be an exact functor between abelian categories,
`X` an object of the source and `S` a short exact sequence there. If `F` is bijective on `Ext` from
`X` into the outer terms `S.X₁` and `S.X₃` in every degree, then it is bijective on `Ext` from `X`
into the middle term `S.X₂` in every degree. -/
theorem mapExt_bijective_of_shortExact [HasExt.{w} C] [HasExt.{w'} D] (X : C)
    {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : ∀ n, Function.Bijective (F.mapExtAddHom X S.X₁ n))
    (h₃ : ∀ n, Function.Bijective (F.mapExtAddHom X S.X₃ n)) (n : ℕ) :
    Function.Bijective (F.mapExtAddHom X S.X₂ n) := by
  have hS' := hS.map_of_exact F
  have := hS.mono_f
  have := hS'.mono_f
  refine ⟨?_, ?_⟩
  · obtain _ | m := n
    · exact AddMonoidHom.injective_of_surjective_of_injective_of_injective
        (0 : Ext.{w} X S.X₁ 0 →+ Ext.{w} X S.X₁ 0)
        ((Ext.mk₀ S.f).postcomp X (add_zero 0))
        ((Ext.mk₀ S.g).postcomp X (add_zero 0))
        (0 : Ext.{w'} (F.obj X) (S.map F).X₁ 0 →+ Ext.{w'} (F.obj X) (S.map F).X₁ 0)
        ((Ext.mk₀ (S.map F).f).postcomp (F.obj X) (add_zero 0))
        ((Ext.mk₀ (S.map F).g).postcomp (F.obj X) (add_zero 0))
        (F.mapExtAddHom X S.X₁ 0) (F.mapExtAddHom X S.X₁ 0) (F.mapExtAddHom X S.X₂ 0)
        (F.mapExtAddHom X S.X₃ 0)
        (by ext x; simp) (by cat_disch) (by cat_disch)
        (exact_zero_left _ (Ext.postcomp_mk₀_injective_of_mono X S.f))
        (function_exact_of_exact (Ext.covariant_sequence_exact₂' X hS 0))
        (exact_zero_left _ (Ext.postcomp_mk₀_injective_of_mono (F.obj X) (S.map F).f))
        (h₁ 0).surjective (h₁ 0).injective (h₃ 0).injective
    · exact AddMonoidHom.injective_of_surjective_of_injective_of_injective
        (hS.extClass.postcomp X rfl)
        ((Ext.mk₀ S.f).postcomp X (add_zero (m + 1)))
        ((Ext.mk₀ S.g).postcomp X (add_zero (m + 1)))
        (hS'.extClass.postcomp (F.obj X) rfl)
        ((Ext.mk₀ (S.map F).f).postcomp (F.obj X) (add_zero (m + 1)))
        ((Ext.mk₀ (S.map F).g).postcomp (F.obj X) (add_zero (m + 1)))
        (F.mapExtAddHom X S.X₃ m) (F.mapExtAddHom X S.X₁ (m + 1))
        (F.mapExtAddHom X S.X₂ (m + 1)) (F.mapExtAddHom X S.X₃ (m + 1))
        (by cat_disch) (by cat_disch) (by cat_disch)
        (function_exact_of_exact (Ext.covariant_sequence_exact₁' X hS m (m + 1) rfl))
        (function_exact_of_exact (Ext.covariant_sequence_exact₂' X hS (m + 1)))
        (function_exact_of_exact (Ext.covariant_sequence_exact₁' (F.obj X) hS' m (m + 1) rfl))
        (h₃ m).surjective (h₁ (m + 1)).injective (h₃ (m + 1)).injective
  · exact AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
      ((Ext.mk₀ S.f).postcomp X (add_zero n))
      ((Ext.mk₀ S.g).postcomp X (add_zero n))
      (hS.extClass.postcomp X rfl)
      ((Ext.mk₀ (S.map F).f).postcomp (F.obj X) (add_zero n))
      ((Ext.mk₀ (S.map F).g).postcomp (F.obj X) (add_zero n))
      (hS'.extClass.postcomp (F.obj X) rfl)
      (F.mapExtAddHom X S.X₁ n) (F.mapExtAddHom X S.X₂ n) (F.mapExtAddHom X S.X₃ n)
      (F.mapExtAddHom X S.X₁ (n + 1))
      (by cat_disch) (by cat_disch) (by cat_disch)
      (function_exact_of_exact (Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl))
      (function_exact_of_exact (Ext.covariant_sequence_exact₂' (F.obj X) hS' n))
      (function_exact_of_exact (Ext.covariant_sequence_exact₃' (F.obj X) hS' n (n + 1) rfl))
      (h₁ n).surjective (h₃ n).surjective (h₁ (n + 1)).injective

/-- **Dévissage along a retract.** Bijectivity on `Ext` passes to a retract in the second variable:
if `i : Y' ⟶ Y` and `p : Y ⟶ Y'` satisfy `i ≫ p = 𝟙 Y'` and the exact functor `F` is bijective on
`Ext` from `X` into `Y` in degree `n`, then it is bijective on `Ext` from `X` into `Y'` in degree
`n`. -/
theorem mapExt_bijective_of_retract [HasExt.{w} C] [HasExt.{w'} D] (X : C) {Y Y' : C}
    (i : Y' ⟶ Y) (p : Y ⟶ Y') (hip : i ≫ p = 𝟙 Y') {n : ℕ}
    (h : Function.Bijective (F.mapExtAddHom X Y n)) :
    Function.Bijective (F.mapExtAddHom X Y' n) := by
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have hx : (x.comp (Ext.mk₀ i) (add_zero n)).mapExactFunctor F =
        (y.comp (Ext.mk₀ i) (add_zero n)).mapExactFunctor F := by
      simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
      exact congrArg (fun z => Ext.comp z (Ext.mk₀ (F.map i)) (add_zero n)) hxy
    have hxy' := h.injective hx
    calc x = (x.comp (Ext.mk₀ i) (add_zero n)).comp (Ext.mk₀ p) (add_zero n) :=
            (comp_mk₀_comp_mk₀_of_comp_eq_id i p hip x).symm
      _ = (y.comp (Ext.mk₀ i) (add_zero n)).comp (Ext.mk₀ p) (add_zero n) := by rw [hxy']
      _ = y := comp_mk₀_comp_mk₀_of_comp_eq_id i p hip y
  · obtain ⟨x, hx⟩ := h.surjective (y.comp (Ext.mk₀ (F.map i)) (add_zero n))
    refine ⟨x.comp (Ext.mk₀ p) (add_zero n), ?_⟩
    have hmap : (x.comp (Ext.mk₀ p) (add_zero n)).mapExactFunctor F =
        (x.mapExactFunctor F).comp (Ext.mk₀ (F.map p)) (add_zero n) := by
      simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    rw [F.mapExtAddHom_apply, hmap]
    change (F.mapExtAddHom X Y n x).comp (Ext.mk₀ (F.map p)) (add_zero n) = y
    rw [hx]
    exact comp_mk₀_comp_mk₀_of_comp_eq_id (F.map i) (F.map p)
      (by rw [← F.map_comp, hip, F.map_id]) y

section IsBijectiveOnExt

attribute [local instance] HasDerivedCategory.standard

/-- **Dévissage for `IsBijectiveOnExt`.** The class of objects `Y` such that an exact functor is
bijective on `Ext` from a fixed `X` into `Y` in every degree is closed under extensions. -/
theorem isBijectiveOnExt_of_shortExact (X : C) {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : ∀ n, IsBijectiveOnExt F X S.X₁ n) (h₃ : ∀ n, IsBijectiveOnExt F X S.X₃ n) (n : ℕ) :
    IsBijectiveOnExt F X S.X₂ n := by
  have hC := HasExt.standard C
  have hD := HasExt.standard D
  refine (mapExt_bijective_iff_mapDerivedCategory F X S.X₂ n).mp
    (mapExt_bijective_of_shortExact F X hS (fun m => ?_) (fun m => ?_) n)
  · exact (mapExt_bijective_iff_mapDerivedCategory F X S.X₁ m).mpr (h₁ m)
  · exact (mapExt_bijective_iff_mapDerivedCategory F X S.X₃ m).mpr (h₃ m)

/-- Bijectivity on `Ext` into a binary biproduct follows from bijectivity on `Ext` into each
factor. -/
theorem isBijectiveOnExt_biprod (X A B : C)
    (hA : ∀ n, IsBijectiveOnExt F X A n) (hB : ∀ n, IsBijectiveOnExt F X B n) (n : ℕ) :
    IsBijectiveOnExt F X (A ⊞ B) n :=
  isBijectiveOnExt_of_shortExact F X
    (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact hA hB n

/-- `IsBijectiveOnExt` passes to a retract in the second variable. -/
theorem isBijectiveOnExt_of_retract (X : C) {Y Y' : C} (i : Y' ⟶ Y) (p : Y ⟶ Y')
    (hip : i ≫ p = 𝟙 Y') {n : ℕ} (h : IsBijectiveOnExt F X Y n) :
    IsBijectiveOnExt F X Y' n := by
  have := HasExt.standard C
  have := HasExt.standard D
  exact (mapExt_bijective_iff_mapDerivedCategory F X Y' n).mp
    (mapExt_bijective_of_retract F X i p hip
      ((mapExt_bijective_iff_mapDerivedCategory F X Y n).mpr h))

end IsBijectiveOnExt

end Devissage

end Stacks.EtaleCohomology

end
