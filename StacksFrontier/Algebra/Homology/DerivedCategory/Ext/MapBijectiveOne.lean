module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# `Ext¹` along a fully faithful exact functor whose image is closed under extensions

Let `F : C ⥤ D` be an exact, fully faithful functor between abelian categories. If every
extension in `D` of an object `F B` by an object `F A` has its middle term in the essential
image of `F`, then `F` induces a bijection `Ext¹_C(B, A) → Ext¹_D(F B, F A)`.

Unlike `CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`, this needs no
injective or projective objects anywhere: `Ext¹` is the group of extensions
(`CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum`), so both
surjectivity and injectivity are statements about short exact sequences, which `F` reflects.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.extClass_eq_zero_of_comp_eq_id`: the class of a short
  exact sequence whose second map has a section vanishes.
* `CategoryTheory.Functor.mapExtAddHom_one_bijective`: the bijectivity on `Ext¹`.
-/

@[expose] public section

universe w w' u u' v v'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The class of a short exact sequence `0 → X₁ → X₂ → X₃ → 0` whose second map has a section
`s : X₃ → X₂` vanishes. -/
theorem ShortComplex.ShortExact.extClass_eq_zero_of_comp_eq_id [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 S.X₃) :
    hS.extClass = 0 := by
  calc hS.extClass = (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) := by simp
    _ = ((Ext.mk₀ s).comp (Ext.mk₀ S.g) (zero_add 0)).comp hS.extClass (zero_add 1) := by
        rw [Ext.mk₀_comp_mk₀, hs]
    _ = 0 := by
        rw [Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1), hS.comp_extClass,
          Ext.comp_zero]

variable {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Full] [F.Faithful] [HasExt.{w} C] [HasExt.{w'} D]

/-- An exact, fully faithful functor is injective on `Ext¹`. -/
theorem Functor.mapExtAddHom_one_injective (A B : C) :
    Function.Injective (F.mapExtAddHom B A 1) := by
  obtain ⟨hsurjC, -, -⟩ := Ext.extClass_surjective_and_eq_iff_iso_and_baerSum.{w} C B A
  obtain ⟨-, heqD, -⟩ :=
    Ext.extClass_surjective_and_eq_iff_iso_and_baerSum.{w'} D (F.obj B) (F.obj A)
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨E, i, p, w, h, rfl⟩ := hsurjC x
  rw [Functor.mapExtAddHom_apply, Abelian.Ext.mapExactFunctor_extClass] at hx
  -- the split extension of `F B` by `F A`
  let Sp := ShortComplex.mk (biprod.inl : F.obj A ⟶ F.obj A ⊞ F.obj B) biprod.snd (by simp)
  have hSp : Sp.ShortExact := (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact
  have hSp0 : hSp.extClass = 0 :=
    hSp.extClass_eq_zero_of_comp_eq_id biprod.inr (by simp [Sp])
  obtain ⟨φ, hφ₁, hφ₂⟩ := (heqD _ _ _ _ _ _ _ _ (h.map_of_exact F) hSp).1 (hx.trans hSp0.symm)
  have hsec : (biprod.inr ≫ φ.inv) ≫ F.map p = 𝟙 (F.obj B) := by
    have : φ.inv ≫ F.map p = biprod.snd := by
      rw [Iso.inv_comp_eq, ← hφ₂]
    rw [Category.assoc, this, biprod.inr_snd]
  exact h.extClass_eq_zero_of_comp_eq_id (F.preimage (biprod.inr ≫ φ.inv))
    (F.map_injective (by simpa using hsec))

/-- If the middle term of every extension of `F B` by `F A` is isomorphic to the image under `F`
of an object of `C`, then `F` is surjective on `Ext¹(B, A)`. -/
theorem Functor.mapExtAddHom_one_surjective (A B : C)
    (hext : ∀ (E : D) (i : F.obj A ⟶ E) (p : E ⟶ F.obj B) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact → ∃ E' : C, Nonempty (F.obj E' ≅ E)) :
    Function.Surjective (F.mapExtAddHom B A 1) := by
  obtain ⟨hsurjD, heqD, -⟩ :=
    Ext.extClass_surjective_and_eq_iff_iso_and_baerSum.{w'} D (F.obj B) (F.obj A)
  intro y
  obtain ⟨E, i, p, w, h, rfl⟩ := hsurjD y
  obtain ⟨E', ⟨e⟩⟩ := hext E i p w h
  let i' : A ⟶ E' := F.preimage (i ≫ e.inv)
  let p' : E' ⟶ B := F.preimage (e.hom ≫ p)
  have hi' : F.map i' = i ≫ e.inv := F.map_preimage _
  have hp' : F.map p' = e.hom ≫ p := F.map_preimage _
  have w' : i' ≫ p' = 0 := F.map_injective (by simp [hi', hp', w])
  have hmap : ((ShortComplex.mk i' p' w').map F).ShortExact := by
    refine ShortComplex.shortExact_of_iso ?_ h
    exact ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) (by simp [hi']) (by simp [hp'])
  have h' := ShortExact.reflects_shortExact_of_faithful F hmap
  refine ⟨h'.extClass, ?_⟩
  rw [Functor.mapExtAddHom_apply, Abelian.Ext.mapExactFunctor_extClass]
  exact (heqD _ _ _ _ _ _ _ _ (h'.map_of_exact F) h).2 ⟨e, by simp [hi'], by simp [hp']⟩

/-- **`Ext¹` along a fully faithful exact functor whose essential image is closed under
extensions.** If the middle term of every extension of `F B` by `F A` is isomorphic to the image
under `F` of an object of `C`, then `F` induces a bijection `Ext¹(B, A) ≃ Ext¹(F B, F A)`. -/
theorem Functor.mapExtAddHom_one_bijective (A B : C)
    (hext : ∀ (E : D) (i : F.obj A ⟶ E) (p : E ⟶ F.obj B) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact → ∃ E' : C, Nonempty (F.obj E' ≅ E)) :
    Function.Bijective (F.mapExtAddHom B A 1) :=
  ⟨F.mapExtAddHom_one_injective A B, F.mapExtAddHom_one_surjective A B hext⟩

end CategoryTheory
