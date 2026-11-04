module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import Mathlib.CategoryTheory.Limits.VanKampen

/-!
# Fibre products over a universal coproduct

A fibre product over the vertex of a universal cofan decomposes as the coproduct of the
fibre products over its summands: if `c` is a universal cofan on a family `X` and
`u : c.pt ⟶ S` restricts to `f i` on the summand `i`, then base change along `v : B ⟶ S`
identifies `∐ (B ×_S X i)` with `B ×_S c.pt`.

## Main definitions

* `CategoryTheory.Limits.coproductPullbackIso` is that decomposition.
* `CategoryTheory.Limits.pullbackRightIdIso` identifies `Y` with `Y ×_X X`, the fibre
  product of a morphism against an identity.

## Main results

* `CategoryTheory.Limits.coproductPullbackIso_ι_fst` and
  `CategoryTheory.Limits.coproductPullbackIso_ι_snd`: the decomposition is compatible with
  the two projections.
* `CategoryTheory.Limits.pullbackRightIdIso_inv`: that identification inverts the first
  projection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {I : Type v} [HasCoproductsOfShape I C] [HasPullbacks C]
  {S B : C}

/-- A fibre product over the vertex of a universal cofan is the coproduct of the fibre
products over its summands. -/
noncomputable def coproductPullbackIso (X : I → C) (f : ∀ i, X i ⟶ S) (c : Cofan X)
    (hu : IsUniversalColimit c) (u : c.pt ⟶ S) (huι : ∀ i, c.inj i ≫ u = f i) (v : B ⟶ S) :
    (∐ fun i ↦ pullback v (f i)) ≅ pullback v u :=
  (hu.isPullback_of_isColimit_left (f := f) (u := u) (v := v)
    (q₁ := fun i ↦ pullback.fst v (f i)) (q₂ := fun i ↦ pullback.snd v (f i))
    (hP := fun i ↦ IsPullback.of_hasPullback v (f i))
    (coproductIsCoproduct fun i ↦ pullback v (f i)) huι).isoPullback

/-- The fibre product of a morphism against an identity is its own source. -/
noncomputable def pullbackRightIdIso {X Y : C} (f : Y ⟶ X) : Y ≅ pullback f (𝟙 X) :=
  (IsPullback.of_id_fst (f := f)).isoPullback

/-- The inverse of the identification of a morphism with its fibre product against an
identity is the first projection. -/
theorem pullbackRightIdIso_inv {X Y : C} (f : Y ⟶ X) :
    (pullbackRightIdIso f).inv = pullback.fst f (𝟙 X) := by
  rw [pullbackRightIdIso]
  simpa using (IsPullback.of_id_fst (f := f)).isoPullback_inv_fst

/-- The square exhibiting `B ×_S c.pt` as the coproduct of the `B ×_S X i`. -/
private theorem isPullback_coproductPullback (X : I → C) (f : ∀ i, X i ⟶ S) (c : Cofan X)
    (hu : IsUniversalColimit c) (u : c.pt ⟶ S) (huι : ∀ i, c.inj i ≫ u = f i) (v : B ⟶ S) :
    IsPullback
      (Cofan.IsColimit.desc (coproductIsCoproduct fun i ↦ pullback v (f i))
        fun i ↦ pullback.fst v (f i))
      (Cofan.IsColimit.desc (coproductIsCoproduct fun i ↦ pullback v (f i))
        fun i ↦ pullback.snd v (f i) ≫ c.inj i) v u :=
  hu.isPullback_of_isColimit_left (f := f) (u := u) (v := v)
    (q₁ := fun i ↦ pullback.fst v (f i)) (q₂ := fun i ↦ pullback.snd v (f i))
    (hP := fun i ↦ IsPullback.of_hasPullback v (f i))
    (coproductIsCoproduct fun i ↦ pullback v (f i)) huι

/-- The decomposition of a fibre product over a universal coproduct is compatible with the
first projections. -/
theorem coproductPullbackIso_ι_fst (X : I → C) (f : ∀ i, X i ⟶ S) (c : Cofan X)
    (hu : IsUniversalColimit c) (u : c.pt ⟶ S) (huι : ∀ i, c.inj i ≫ u = f i) (v : B ⟶ S)
    (i : I) :
    Sigma.ι (fun i ↦ pullback v (f i)) i ≫
      (coproductPullbackIso X f c hu u huι v).hom ≫ pullback.fst v u =
        pullback.fst v (f i) := by
  rw [coproductPullbackIso, (isPullback_coproductPullback X f c hu u huι v).isoPullback_hom_fst]
  exact Cofan.IsColimit.fac (coproductIsCoproduct fun i ↦ pullback v (f i))
    (fun i ↦ pullback.fst v (f i)) i

/-- The decomposition of a fibre product over a universal coproduct is compatible with the
second projections. -/
theorem coproductPullbackIso_ι_snd (X : I → C) (f : ∀ i, X i ⟶ S) (c : Cofan X)
    (hu : IsUniversalColimit c) (u : c.pt ⟶ S) (huι : ∀ i, c.inj i ≫ u = f i) (v : B ⟶ S)
    (i : I) :
    Sigma.ι (fun i ↦ pullback v (f i)) i ≫
      (coproductPullbackIso X f c hu u huι v).hom ≫ pullback.snd v u =
        pullback.snd v (f i) ≫ c.inj i := by
  rw [coproductPullbackIso, (isPullback_coproductPullback X f c hu u huι v).isoPullback_hom_snd]
  exact Cofan.IsColimit.fac (coproductIsCoproduct fun i ↦ pullback v (f i))
    (fun i ↦ pullback.snd v (f i) ≫ c.inj i) i

end CategoryTheory.Limits

end
