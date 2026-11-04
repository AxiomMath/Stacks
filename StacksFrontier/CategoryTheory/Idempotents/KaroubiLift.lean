module

public import StacksFrontier.CategoryTheory.Idempotents.KaroubiMonoidalExtension
public import StacksFrontier.CategoryTheory.Monoidal.BraidedEquivalenceInverse
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleTransport
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a symmetric monoidal functor to the Karoubi envelope

A functor `F : A ⥤ 𝒞` into an idempotent complete category extends to the Karoubi envelope of `A`:
the formal direct factor `(X, p)` is sent to the image of the idempotent `F(p)`. This file records
that the extension `Karoubi.mapFunctor F ⋙ (toKaroubiEquivalence 𝒞).inverse` is braided monoidal
when `F` is, additive when `F` is, that its restriction to `A` is `F` by a monoidal isomorphism,
and that it sends `(X, p)` to an invertible object as soon as some, equivalently any, image of
`F(p)` is invertible.

## Main definitions

* `CategoryTheory.Idempotents.Karoubi.lift`: the extension of `F` to the Karoubi envelope.
* `CategoryTheory.Idempotents.Karoubi.toKaroubiCompLiftIso`: its restriction to `A` is `F`.

## Main results

* `CategoryTheory.Idempotents.Karoubi.isInvertible_lift_obj`: the extension sends `(X, p)` to an
  invertible object if an image of `F(p)` is invertible.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category Limits

namespace CategoryTheory.Idempotents.Karoubi

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] {𝒞 : Type u₂} [Category.{v₂} 𝒞] [IsIdempotentComplete 𝒞]

/-- The extension of a functor `F : A ⥤ 𝒞` into an idempotent complete category to the Karoubi
envelope of `A`: `(X, p)` is sent to the image of `F(p)`. -/
@[sga "4 I 8.7.8"]
noncomputable abbrev lift (F : A ⥤ 𝒞) : Karoubi A ⥤ 𝒞 :=
  mapFunctor F ⋙ (toKaroubiEquivalence 𝒞).inverse

/-- The extension restricts to `F` along `toKaroubi A`. -/
noncomputable def toKaroubiCompLiftIso (F : A ⥤ 𝒞) : toKaroubi A ⋙ lift F ≅ F :=
  (Functor.associator (toKaroubi A) (mapFunctor F) (toKaroubiEquivalence 𝒞).inverse).symm ≪≫
    Functor.isoWhiskerRight (toKaroubiCompMapFunctorIso F :
      toKaroubi A ⋙ mapFunctor F ≅ F ⋙ (toKaroubiEquivalence 𝒞).functor)
      (toKaroubiEquivalence 𝒞).inverse ≪≫
      Functor.associator F (toKaroubiEquivalence 𝒞).functor (toKaroubiEquivalence 𝒞).inverse ≪≫
        (Functor.isoWhiskerLeft F (toKaroubiEquivalence 𝒞).unitIso).symm ≪≫ F.rightUnitor

section Additive

variable [Preadditive A] [Preadditive 𝒞]

/-- The functor induced on Karoubi envelopes by an additive functor is additive. -/
instance (F : A ⥤ 𝒞) [F.Additive] : (mapFunctor F).Additive where
  map_add {_ _ f g} := Karoubi.hom_ext _ _ (F.map_add (f := f.f) (g := g.f))

/-- The extension of an additive functor to the Karoubi envelope is additive. -/
instance (F : A ⥤ 𝒞) [F.Additive] : (lift F).Additive :=
  inferInstanceAs (mapFunctor F ⋙ (toKaroubiEquivalence 𝒞).inverse).Additive

end Additive

section Monoidal

variable [MonoidalCategory A] [MonoidalCategory 𝒞] (F : A ⥤ 𝒞) [F.Monoidal]

/-- The restriction of the extension of a monoidal functor is monoidally isomorphic to it. -/
instance toKaroubiCompLiftIso_isMonoidal :
    NatTrans.IsMonoidal (toKaroubiCompLiftIso F).hom := by
  let e := toKaroubiEquivalence 𝒞
  let φ₀ : toKaroubi A ⋙ mapFunctor F ≅ F ⋙ e.functor := toKaroubiCompMapFunctorIso F
  have h₀ : NatTrans.IsMonoidal φ₀.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (toKaroubiCompMapFunctorIso F).hom)
  have h₁ : NatTrans.IsMonoidal (Functor.associator (toKaroubi A) (mapFunctor F) e.inverse).inv :=
    inferInstance
  have h₁' : NatTrans.IsMonoidal
      (Functor.associator (toKaroubi A) (mapFunctor F) e.inverse).symm.hom := h₁
  have h₂ : NatTrans.IsMonoidal (Functor.whiskerRight φ₀.hom e.inverse) := inferInstance
  have h₃ : NatTrans.IsMonoidal (Functor.associator F e.functor e.inverse).hom := inferInstance
  have h₄ : NatTrans.IsMonoidal (Functor.whiskerLeft F e.unitIso.inv) := inferInstance
  have h₅ : NatTrans.IsMonoidal F.rightUnitor.hom := inferInstance
  exact NatTrans.IsMonoidal.comp _ (Functor.whiskerRight φ₀.hom e.inverse ≫
    (Functor.associator F e.functor e.inverse).hom ≫ Functor.whiskerLeft F e.unitIso.inv ≫
      F.rightUnitor.hom)

omit [IsIdempotentComplete 𝒞] in
/-- **A natural transformation between lax monoidal functors out of a Karoubi envelope is monoidal
as soon as its restriction along `toKaroubi` is**: every formal direct factor `(X, p)` is a
retract of `(X, 1)`, and both sides of the compatibility with the tensorators are natural. -/
theorem isMonoidal_of_whiskerLeft_toKaroubi {A₁ A₂ : Karoubi A ⥤ 𝒞} [A₁.LaxMonoidal]
    [A₂.LaxMonoidal] (ψ : A₁ ⟶ A₂)
    [h : NatTrans.IsMonoidal (Functor.whiskerLeft (toKaroubi A) ψ)] : NatTrans.IsMonoidal ψ := by
  have hε : Functor.LaxMonoidal.ε (toKaroubi A) = 𝟙 _ := Karoubi.hom_ext _ _ (by simp)
  have key₀ : ∀ X Y : A,
      Functor.LaxMonoidal.μ A₁ ((toKaroubi A).obj X) ((toKaroubi A).obj Y) ≫
          ψ.app ((toKaroubi A).obj X ⊗ (toKaroubi A).obj Y) =
        (ψ.app ((toKaroubi A).obj X) ⊗ₘ ψ.app ((toKaroubi A).obj Y)) ≫
          Functor.LaxMonoidal.μ A₂ ((toKaroubi A).obj X) ((toKaroubi A).obj Y) := by
    intro X Y
    have h₀ := NatTrans.IsMonoidal.tensor (τ := Functor.whiskerLeft (toKaroubi A) ψ) X Y
    rw [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.comp_μ] at h₀
    have h₁ := congrArg (· ≫ A₂.map (Functor.OplaxMonoidal.δ (toKaroubi A) X Y)) h₀
    simp only [Functor.whiskerLeft_app, assoc, ← A₂.map_comp, Functor.Monoidal.μ_δ, A₂.map_id,
      comp_id] at h₁
    rw [← h₁, ψ.naturality_assoc, ← A₂.map_comp, Functor.Monoidal.μ_δ, A₂.map_id, comp_id]
  have key : ∀ X Y : A,
      Functor.LaxMonoidal.μ A₁ (X : Karoubi A) (Y : Karoubi A) ≫ ψ.app ((X : Karoubi A) ⊗ Y) =
        (ψ.app (X : Karoubi A) ⊗ₘ ψ.app (Y : Karoubi A)) ≫
          Functor.LaxMonoidal.μ A₂ (X : Karoubi A) (Y : Karoubi A) :=
    key₀
  refine ⟨?_, fun P Q ↦ ?_⟩
  · have h₀ := NatTrans.IsMonoidal.unit (τ := Functor.whiskerLeft (toKaroubi A) ψ)
    simp only [Functor.LaxMonoidal.comp_ε, hε, Functor.map_id, comp_id,
      Functor.whiskerLeft_app] at h₀
    exact h₀
  · have hP := Karoubi.decompId P
    have hQ := Karoubi.decompId Q
    calc Functor.LaxMonoidal.μ A₁ P Q ≫ ψ.app (P ⊗ Q)
        = (A₁.map (Karoubi.decompId_i P) ⊗ₘ A₁.map (Karoubi.decompId_i Q)) ≫
            (Functor.LaxMonoidal.μ A₁ (P.X : Karoubi A) (Q.X : Karoubi A) ≫
              ψ.app ((P.X : Karoubi A) ⊗ (Q.X : Karoubi A))) ≫
              A₂.map (Karoubi.decompId_p P ⊗ₘ Karoubi.decompId_p Q) := by
          symm
          simp only [assoc]
          rw [← ψ.naturality, Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp_assoc,
            tensorHom_comp_tensorHom, ← hP, ← hQ, id_tensorHom_id, A₁.map_id, id_comp]
      _ = (A₁.map (Karoubi.decompId_i P) ⊗ₘ A₁.map (Karoubi.decompId_i Q)) ≫
            ((ψ.app (P.X : Karoubi A) ⊗ₘ ψ.app (Q.X : Karoubi A)) ≫
              Functor.LaxMonoidal.μ A₂ (P.X : Karoubi A) (Q.X : Karoubi A)) ≫
              A₂.map (Karoubi.decompId_p P ⊗ₘ Karoubi.decompId_p Q) := by
          rw [key]
      _ = (ψ.app P ⊗ₘ ψ.app Q) ≫ Functor.LaxMonoidal.μ A₂ P Q := by
          simp only [assoc]
          rw [← Functor.LaxMonoidal.μ_natural, tensorHom_comp_tensorHom_assoc,
            tensorHom_comp_tensorHom_assoc, ψ.naturality, ψ.naturality, assoc, assoc,
            ← A₂.map_comp, ← A₂.map_comp, ← hP, ← hQ, A₂.map_id, A₂.map_id, comp_id, comp_id]

end Monoidal

section Braided

variable [MonoidalCategory A] [MonoidalCategory 𝒞] [BraidedCategory A] [BraidedCategory 𝒞]
  (F : A ⥤ 𝒞) [F.Braided]

/-- The extension of a braided monoidal functor is braided. -/
noncomputable instance liftBraided : (lift F).Braided :=
  letI : (toKaroubiEquivalence 𝒞).functor.Braided := inferInstanceAs (toKaroubi 𝒞).Braided
  letI : (toKaroubiEquivalence 𝒞).inverse.Braided := (toKaroubiEquivalence 𝒞).inverseBraided
  inferInstanceAs (mapFunctor F ⋙ (toKaroubiEquivalence 𝒞).inverse).Braided

end Braided

/-- An image of the idempotent `F(p)`, that is an object `U` with `i : U ⟶ F(X)`,
`e : F(X) ⟶ U`, `i ≫ e = 1` and `e ≫ i = F(p)`, is isomorphic to the value of the extension at
`(X, p)`. -/
noncomputable def liftObjIsoOfSplit (F : A ⥤ 𝒞) (P : Karoubi A) {U : 𝒞} (i : U ⟶ F.obj P.X)
    (e : F.obj P.X ⟶ U) (hie : i ≫ e = 𝟙 U) (hei : e ≫ i = F.map P.p) : (lift F).obj P ≅ U :=
  (toKaroubiEquivalence 𝒞).inverse.mapIso
      { hom := ⟨e, by
          change F.map P.p ≫ e ≫ 𝟙 U = e
          rw [comp_id, ← hei, assoc, hie, comp_id]⟩
        inv := ⟨i, by
          change 𝟙 U ≫ i ≫ F.map P.p = i
          rw [id_comp, ← hei, ← assoc, hie, id_comp]⟩
        hom_inv_id := Karoubi.hom_ext _ _ hei
        inv_hom_id := Karoubi.hom_ext _ _ hie } ≪≫
    ((toKaroubiEquivalence 𝒞).unitIso.app U).symm

/-- **The extension sends `(X, p)` to an invertible object as soon as an image of `F(p)` is
invertible.** -/
theorem isInvertible_lift_obj [MonoidalCategory 𝒞] (F : A ⥤ 𝒞) (P : Karoubi A)
    (h : ∃ (U : 𝒞) (i : U ⟶ F.obj P.X) (e : F.obj P.X ⟶ U),
      i ≫ e = 𝟙 U ∧ e ≫ i = F.map P.p ∧ IsInvertible U) :
    IsInvertible ((lift F).obj P) := by
  obtain ⟨U, i, e, hie, hei, hU⟩ := h
  exact MonoidalCategory.isInvertible_of_iso (liftObjIsoOfSplit F P i e hie hei).symm hU

end CategoryTheory.Idempotents.Karoubi
