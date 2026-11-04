module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeExt

/-!
# The localization map between single complexes

Let `𝒜` be an abelian category and `P`, `Q` two of its objects. The localization functor
`Qh : K(𝒜) ⥤ D(𝒜)` induces a map from the homotopy classes of morphisms of cochain complexes
from `P` placed in degree `0` to `Q` placed in degree `q` to the morphisms of `D(𝒜)` between the
same objects. This file proves it bijective for every `q` as soon as `Ext^i(P, Q)` vanishes for
every `i ≥ 1`.

In degree `q = 0` both sides are `Hom_𝒜(P, Q)`, the single functors being fully faithful. In
every other degree the homotopy classes vanish, a morphism of single complexes in different
degrees being zero; the morphisms of `D(𝒜)` vanish for `q > 0` because they go from `D^{≤ 0}` to
`D^{≥ q}`, and for `q < 0` they are `Ext^{-q}(P, Q)`, which vanishes by hypothesis.

## Main results

* `CochainComplex.isKInjective_single_obj_of_injective`: an injective object placed in one
  degree is a K-injective complex.
* `DerivedCategory.qh_map_bijective_single_of_ext_eq_zero`: the localization map between single
  complexes is bijective when the higher `Ext`-groups vanish.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits CategoryTheory.Abelian

universe w w' v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **An injective object placed in one degree is a K-injective complex**: the complex is
strictly bounded below and degreewise injective, its terms away from the given degree being zero
objects. -/
lemma isKInjective_single_obj_of_injective (E : C) [Injective E] (q : ℤ) :
    ((singleFunctor C q).obj E).IsKInjective := by
  have : ∀ n : ℤ, Injective (((singleFunctor C q).obj E).X n) := by
    intro n
    by_cases hn : n = q
    · subst hn
      exact Injective.of_iso ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n E).symm)
        inferInstance
    · exact Injective.of_iso
        ((HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) q E n hn).isoZero).symm
        inferInstance
  have : CochainComplex.IsStrictlyGE ((singleFunctor C q).obj E) q :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      ((HomologicalComplex.single C (ComplexShape.up ℤ) q).obj E) q)
  exact isKInjective_of_injective _ q

end CochainComplex

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w'} C]

/-- The localization of a single complex, read as the image of the object under the single
functor of the derived category. -/
def qhSingleIso (P : C) (q : ℤ) :
    Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor C q).obj P)) ≅ (singleFunctor C q).obj P :=
  (quotientCompQhIso C).app _ ≪≫ ((singleFunctorIsoCompQ C q).app P).symm

omit [HasDerivedCategory C] in
/-- A morphism of cochain complexes from an object placed in degree `0` to an object placed in a
different degree is zero, and hence so is its homotopy class. -/
lemma subsingleton_hom_quotient_single_of_ne (P Q : C) {q : ℤ} (hq : q ≠ 0) :
    Subsingleton ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor C 0).obj P) ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor C q).obj Q)) := by
  have hz : ∀ h : (CochainComplex.singleFunctor C 0).obj P ⟶
      (CochainComplex.singleFunctor C q).obj Q, h = 0 := by
    intro h
    ext n
    by_cases hn : n = 0
    · subst hn
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) q Q 0
        (Ne.symm hq)).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 P n hn).eq_of_src _ _
  refine subsingleton_of_forall_eq 0 fun a => ?_
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective a
  rw [hz f, Functor.map_zero]

/-- Bijectivity of the localization map on morphisms out of an object of the homotopy category
transfers along an isomorphism of that object. -/
lemma qh_map_bijective_of_iso_source {X X' Y : HomotopyCategory C (ComplexShape.up ℤ)}
    (e : X ≅ X') (h : Function.Bijective (DerivedCategory.Qh.map : (X' ⟶ Y) → _)) :
    Function.Bijective (DerivedCategory.Qh.map : (X ⟶ Y) → _) := by
  refine ⟨fun a b hab => ?_, fun d => ?_⟩
  · have : e.inv ≫ a = e.inv ≫ b := h.1 (by simp [hab])
    simpa using congrArg (e.hom ≫ ·) this
  · obtain ⟨c, hc⟩ := h.2 (DerivedCategory.Qh.map e.inv ≫ d)
    exact ⟨e.hom ≫ c, by simp [hc]⟩

variable [HasExt.{w} C]

/-- **The localization map between single complexes is bijective when the higher `Ext`-groups
vanish.** For objects `P`, `Q` of `𝒜` with `Ext^i(P, Q) = 0` for every `i ≥ 1` and every
`q : ℤ`, the localization functor induces a bijection from the homotopy classes of morphisms from
`P` placed in degree `0` to `Q` placed in degree `q` to the morphisms of `D(𝒜)` between them. -/
theorem qh_map_bijective_single_of_ext_eq_zero (P Q : C)
    (hext : ∀ (n : ℕ) (a : Ext.{w} P Q (n + 1)), a = 0) (q : ℤ) :
    Function.Bijective (Qh.map :
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj P) ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor C q).obj Q)) → _) := by
  by_cases hq : q = 0
  · subst hq
    let s : (P ⟶ Q) → ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor C 0).obj P) ⟶
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor C 0).obj Q)) := fun f =>
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((CochainComplex.singleFunctor C 0).map f)
    have hs : Function.Surjective s := by
      intro a
      obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective a
      obtain ⟨f, rfl⟩ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map_surjective g
      exact ⟨f, rfl⟩
    have hcomp : ∀ f : P ⟶ Q, Qh.map (s f) =
        (qhSingleIso P 0).hom ≫ (singleFunctor C 0).map f ≫ (qhSingleIso Q 0).inv := by
      intro f
      simp only [s, qhSingleIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
        Iso.app_hom, Iso.app_inv, assoc]
      rw [← (singleFunctorIsoCompQ C 0).inv.naturality_assoc f]
      simp only [Functor.comp_map, Iso.inv_hom_id_app_assoc]
      rw [← assoc, ← (quotientCompQhIso C).hom.naturality, assoc, Iso.hom_inv_id_app, comp_id]
      rfl
    refine ⟨fun a b hab => ?_, fun d => ?_⟩
    · obtain ⟨f, rfl⟩ := hs a
      obtain ⟨g, rfl⟩ := hs b
      rw [hcomp, hcomp, cancel_epi, cancel_mono] at hab
      rw [(singleFunctor C 0).map_injective hab]
    · obtain ⟨f, hf⟩ := (singleFunctor C 0).map_surjective
        ((qhSingleIso P 0).inv ≫ d ≫ (qhSingleIso Q 0).hom)
      refine ⟨s f, ?_⟩
      rw [hcomp, hf]
      simp only [assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, comp_id]
  · have := subsingleton_hom_quotient_single_of_ne P Q hq
    have htgt : Subsingleton (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj P)) ⟶
        Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor C q).obj Q))) := by
      suffices h : Subsingleton ((singleFunctor C 0).obj P ⟶ (singleFunctor C q).obj Q) from
        (Iso.homCongr (qhSingleIso P 0) (qhSingleIso Q q)).subsingleton
      rcases lt_or_gt_of_ne hq with hlt | hgt
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, q + ((n + 1 : ℕ) : ℤ) = 0 := ⟨(-q - 1).toNat, by lia⟩
        have := subsingleton_of_forall_eq (0 : Ext.{w} P Q (n + 1)) (hext n)
        exact (singleHomEquivExt.{w} P Q 0 q (n + 1) hn).injective.subsingleton
      · exact subsingleton_of_forall_eq 0 (hom_singleFunctor_obj_eq_zero P Q 0 q hgt)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun d => ⟨0, Subsingleton.elim _ _⟩⟩

end DerivedCategory
