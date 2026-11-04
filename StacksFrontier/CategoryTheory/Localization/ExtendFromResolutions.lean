module

public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Extending an isomorphism of localized functors from a class of resolutions

Let `Q : C ⥤ D` be a localization of `C` at a class `W` of morphisms, and let `R : C ⥤ C` be a
functorial resolution: a functor together with `η : 𝟭 C ⟶ R` whose components become invertible
in `D`, and whose values all satisfy a property `P`. Two functors `F, G : D ⥤ E` are then
isomorphic as soon as they are isomorphic at the image of every object satisfying `P`,
naturally in the morphisms between such objects, and the isomorphism is uniquely determined by
its components there.

This is the mechanism by which an identification of two constructions on resolutions — in
practice, on K-injective complexes — becomes an isomorphism of functors on the whole localized
category, and the uniqueness clause is what makes such an isomorphism canonical rather than
chosen.

## Main results

* `CategoryTheory.exists_natIso_of_isoOnResolutions`: the isomorphism of functors, together
  with the formula for its components at objects satisfying `P`.
* `CategoryTheory.natTrans_ext_of_resolutions`: two natural transformations which agree at the
  image of every object satisfying `P` are equal.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/-- Two natural transformations between functors out of a localized category are equal as soon
as they agree at the image of every object carrying a functorial resolution: the resolution
exhibits an arbitrary object as isomorphic, in the localized category, to one where the two
agree. -/
theorem natTrans_ext_of_resolutions
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (R : C ⥤ C) (η : 𝟭 C ⟶ R) [∀ c, IsIso (Q.map (η.app c))]
    (P : C → Prop) (hR : ∀ c, P (R.obj c))
    {F G : D ⥤ E} (α β : F ⟶ G)
    (h : ∀ c, P c → α.app (Q.obj c) = β.app (Q.obj c)) :
    α = β := by
  have hQ : ∀ c : C, α.app (Q.obj c) = β.app (Q.obj c) := by
    intro c
    have hα := α.naturality (Q.map (η.app c))
    have hβ := β.naturality (Q.map (η.app c))
    simp only [Functor.id_obj] at hα hβ
    have key : α.app (Q.obj c) ≫ G.map (Q.map (η.app c)) =
        β.app (Q.obj c) ≫ G.map (Q.map (η.app c)) := by
      rw [← hα, ← hβ, h (R.obj c) (hR c)]
    exact (cancel_mono (G.map (Q.map (η.app c)))).mp key
  exact Localization.natTrans_ext Q W hQ

/-- An isomorphism between two functors out of a localized category, extended from an
isomorphism at the image of every object satisfying `P`. The components at such objects are the
given ones, which determines the isomorphism. -/
theorem exists_natIso_of_isoOnResolutions
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (R : C ⥤ C) (η : 𝟭 C ⟶ R) [∀ c, IsIso (Q.map (η.app c))]
    (P : C → Prop) (hR : ∀ c, P (R.obj c))
    (F G : D ⥤ E) (e : ∀ c, P c → (F.obj (Q.obj c) ≅ G.obj (Q.obj c)))
    (he : ∀ {c c'} (hc : P c) (hc' : P c') (f : c ⟶ c'),
      F.map (Q.map f) ≫ (e c' hc').hom = (e c hc).hom ≫ G.map (Q.map f)) :
    ∃ e' : F ≅ G, ∀ c (hc : P c), e'.hom.app (Q.obj c) = (e c hc).hom := by
  let t : Q ⋙ F ≅ Q ⋙ G := NatIso.ofComponents
    (fun c => F.mapIso (asIso (Q.map (η.app c))) ≪≫ e (R.obj c) (hR c) ≪≫
      (G.mapIso (asIso (Q.map (η.app c)))).symm)
    (by
      intro c c' f
      dsimp
      have hn := congrArg (fun k => Q.map k) (η.naturality f)
      dsimp at hn
      simp only [Functor.map_comp] at hn
      have hF := congrArg (fun k => F.map k) hn
      have hG := congrArg (fun k => G.map k) hn
      simp only [Functor.map_comp] at hF hG
      simp only [Category.assoc]
      rw [reassoc_of% hF, reassoc_of% (he (hR c) (hR c') (R.map f))]
      congr 2
      apply (cancel_mono (G.map (Q.map (η.app c')))).mp
      simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id, Category.comp_id]
      rw [Q.map_comp, hn]
      simp)
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W E
  refine ⟨ff.preimageIso t, ?_⟩
  intro c hc
  have ht := congrArg (fun k => k.app c) (ff.map_preimage t.hom)
  change (ff.preimageIso t).hom.app (Q.obj c) = _ at ht
  rw [ht]
  dsimp [t]
  rw [reassoc_of% (he hc (hR c) (η.app c))]
  simp

end CategoryTheory

end
