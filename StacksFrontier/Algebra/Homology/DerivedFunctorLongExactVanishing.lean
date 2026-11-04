module

public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact

/-!
# Vanishing and isomorphism criteria from the long exact sequence of right derived functors

Let `0 → K → F → H → 0` be a sequence of additive functors which is short exact on injective
objects. Its long exact sequence of right derived functors
(`CategoryTheory.longExact_rightDerived_of_shortExact_on_injectives`) gives, at a fixed object
`X`:

* if all `Rⁿ K (X)` vanish, every `Rⁿ q : Rⁿ F (X) ⟶ Rⁿ H (X)` is an isomorphism;
* if all `Rⁿ F (X)` and all `Rⁿ H (X)` vanish, so do all `Rⁿ K (X)`.

## Main results

* `CategoryTheory.isIso_rightDerived_app_of_isZero` and
  `CategoryTheory.isZero_rightDerived_of_isZero` — the two criteria.

In a single degree, for a short complex `F ⟶ G ⟶ H` short exact on injective objects:

* `CategoryTheory.isZero_rightDerived_succ_of_epi`: `Rⁿ⁺¹F(X) = 0` when `Rⁿ⁺¹G(X) = 0` and
  `RⁿG(X) ⟶ RⁿH(X)` is an epimorphism.
* `CategoryTheory.isZero_rightDerived_succ_of_isZero`: `Rⁿ⁺¹F(X) = 0` when `Rⁿ⁺¹G(X) = 0` and
  `RⁿH(X) = 0`.
* `CategoryTheory.isZero_rightDerived_of_isZero_of_isZero`: `RⁿG(X) = 0` when
  `RⁿF(X) = 0 = RⁿH(X)`.

These degreewise forms are what dimension-shifting and Mayer–Vietoris arguments read off, the
typical instance being the Mayer–Vietoris sequence of global sections of an elementary
distinguished square, which is short exact on injective modules (Stacks 08GW).

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0CRS](https://stacks.math.columbia.edu/tag/0CRS)
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasInjectiveResolutions A] {K F H : A ⥤ B}
  [K.Additive] [F.Additive] [H.Additive]
  (i : K ⟶ F) (q : F ⟶ H) (hiq : i ≫ q = 0)
  (hinj : ∀ X : A, Injective X → (NatTrans.appShortComplex i q hiq X).ShortExact)

include hinj in
/-- If all right derived functors of the kernel term vanish at `X`, the right derived functors of
`q` are isomorphisms at `X`. -/
theorem isIso_rightDerived_app_of_isZero (X : A) (hK : ∀ n : ℕ, IsZero ((K.rightDerived n).obj X))
    (p : ℕ) : IsIso ((NatTrans.rightDerived q p).app X) := by
  obtain ⟨delta, -, hex⟩ := longExact_rightDerived_of_shortExact_on_injectives i q hiq hinj
  have hmono : Mono ((NatTrans.rightDerived q p).app X) :=
    ((hex p X).exact' 0 1 2).mono_g ((hK p).eq_of_src _ _)
  have hepi : Epi ((NatTrans.rightDerived q p).app X) :=
    ((hex p X).exact' 1 2 3).epi_f ((hK (p + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

include hinj in
/-- If all right derived functors of the middle and of the last term vanish at `X`, so do all
right derived functors of the kernel term. -/
theorem isZero_rightDerived_of_isZero (X : A) (hF : ∀ n : ℕ, IsZero ((F.rightDerived n).obj X))
    (hH : ∀ n : ℕ, IsZero ((H.rightDerived n).obj X)) (n : ℕ) :
    IsZero ((K.rightDerived n).obj X) := by
  obtain ⟨delta, hmono, hex⟩ := longExact_rightDerived_of_shortExact_on_injectives i q hiq hinj
  cases n with
  | zero =>
    have := hmono X
    exact (hF 0).of_mono ((NatTrans.rightDerived i 0).app X)
  | succ m =>
    exact ((hex m X).exact' 2 3 4).isZero_X₂ ((hH m).eq_of_src _ _)
      ((hF (m + 1)).eq_of_tgt _ _)

end CategoryTheory

namespace CategoryTheory

open Limits

section Abstract

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasInjectiveResolutions A] {F G H : A ⥤ B}
  [F.Additive] [G.Additive] [H.Additive]
  (i : F ⟶ G) (q : G ⟶ H) (hiq : i ≫ q = 0)
  (hinj : ∀ X : A, Injective X → (NatTrans.appShortComplex i q hiq X).ShortExact)

include hinj

/-- **Dimension shifting along a short complex of functors.**  Let `F ⟶ G ⟶ H` be a short
complex of additive functors which is short exact on injective objects.  If `Rⁿ⁺¹G(X) = 0` and
`RⁿG(X) ⟶ RⁿH(X)` is an epimorphism, then `Rⁿ⁺¹F(X) = 0`: in the long exact sequence the
connecting map `RⁿH(X) ⟶ Rⁿ⁺¹F(X)` is then both zero and onto. -/
theorem isZero_rightDerived_succ_of_epi (X : A) (n : ℕ)
    (hG : IsZero ((G.rightDerived (n + 1)).obj X))
    (hq : Epi ((NatTrans.rightDerived q n).app X)) :
    IsZero ((F.rightDerived (n + 1)).obj X) := by
  have hE := exact_rightDerived_composableArrows₅ i q hiq hinj (injectiveResolution X) n
  have h3 := hE.exact 2
  have hδ : InjectiveResolution.rightDerivedDelta i q hiq hinj (injectiveResolution X) n = 0 :=
    (cancel_epi ((NatTrans.rightDerived q n).app X)).1 (by
      rw [comp_zero]
      exact hE.toIsComplex.zero 1)
  exact h3.isZero_X₂ hδ (hG.eq_of_tgt _ _)

/-- **Dimension shifting along a short complex of functors, vanishing form.**  If `F ⟶ G ⟶ H`
is short exact on injective objects, `Rⁿ⁺¹G(X) = 0` and `RⁿH(X) = 0`, then `Rⁿ⁺¹F(X) = 0`. -/
theorem isZero_rightDerived_succ_of_isZero (X : A) (n : ℕ)
    (hG : IsZero ((G.rightDerived (n + 1)).obj X)) (hH : IsZero ((H.rightDerived n).obj X)) :
    IsZero ((F.rightDerived (n + 1)).obj X) :=
  isZero_rightDerived_succ_of_epi i q hiq hinj X n hG
    ⟨fun _ _ _ => hH.eq_of_src _ _⟩

/-- **The middle term of a short complex of functors.**  If `F ⟶ G ⟶ H` is short exact on
injective objects and `RⁿF(X) = 0 = RⁿH(X)`, then `RⁿG(X) = 0`. -/
theorem isZero_rightDerived_of_isZero_of_isZero (X : A) (n : ℕ)
    (hF : IsZero ((F.rightDerived n).obj X)) (hH : IsZero ((H.rightDerived n).obj X)) :
    IsZero ((G.rightDerived n).obj X) := by
  have hE := exact_rightDerived_composableArrows₅ i q hiq hinj (injectiveResolution X) n
  exact (hE.exact 0).isZero_X₂ (hF.eq_of_src _ _) (hH.eq_of_tgt _ _)

end Abstract

end CategoryTheory

end
