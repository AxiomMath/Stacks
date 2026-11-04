module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutAbstractSquares
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditional
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.RingTheory.MilnorPatching.BaseChangeGlueing

/-!
# Global sections over a flat base change of a pushout along a thickening

Let `Y' = Y ⨿_Z Z'` be a pushout of schemes along a thickening `i : Z ⟶ Z'` and an affine
morphism `f : Z ⟶ Y` ([Stacks Project, Tag 07RT]).  The fourth assertion of that tag says that
`𝒪_{Y'} = 𝒪_Y ×_{f_*𝒪_Z} g_*𝒪_{Z'}`.  This file records the two consequences of it which a
chartwise argument needs:

* for an arbitrary cocartesian square presenting `Y'`, the global sections of `Y'` are the fibre
  product of those of `Y` and `Z'` over those of `Z`;
* if `T ⟶ Y'` is flat and `T_Y`, `T_{Z'}`, `T_Z` are its base changes, then the global sections
  of `T` are the fibre product of those of `T_Y` and `T_{Z'}` over those of `T_Z`; when `T_{Z'}`
  is affine the map to `T_Z` is moreover surjective, so the four rings form the fibre square of
  Milnor patching, `MilnorPatching.IsFibreSquare`.

The second statement is the first one applied to the square of the four base changes, which is
again a pushout along a thickening and an affine morphism by the closing paragraph of
[Stacks Project, Tag 07RX] (`Stacks.Pushout.isPushout_restrictions_of_flat`).

## Main results

* `Stacks.Pushout.isPullback_appTop_of_isPushout`: global sections of a pushout along a
  thickening and an affine morphism.
* `Stacks.Pushout.isFibreSquare_appTop_of_flat`: the fibre square of global sections over a flat
  base change of such a pushout.

## References

* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

variable {Z Z' Y Y' : Scheme.{u}} {i : Z ⟶ Z'} {f : Z ⟶ Y} {g : Z' ⟶ Y'} {h : Y ⟶ Y'}

/-- **The global sections of a pushout along a thickening and an affine morphism are the fibre
product of the global sections of the two pieces** (the fourth assertion of
[Stacks Project, Tag 07RT] over the whole space), for an arbitrary cocartesian square. -/
theorem isPullback_appTop_of_isPushout (hpo : IsPushout i f g h) (hi : IsThickening i)
    [IsAffineHom f] :
    IsPullback h.appTop g.appTop f.appTop i.appTop := by
  let := hpo.hasPushout
  refine (pushout_structureSheaf_isPullback' i f hi ⊤).of_iso (Scheme.Γ.mapIso hpo.isoPushout.op)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · show (pushout.inr i f).appTop ≫ 𝟙 _ = hpo.isoPushout.hom.appTop ≫ h.appTop
    rw [Category.comp_id, ← Scheme.Hom.comp_appTop, hpo.inr_isoPushout_hom]
  · show (pushout.inl i f).appTop ≫ 𝟙 _ = hpo.isoPushout.hom.appTop ≫ g.appTop
    rw [Category.comp_id, ← Scheme.Hom.comp_appTop, hpo.inl_isoPushout_hom]
  · rfl
  · simp only [Iso.refl_hom]
    rfl

/-- A cartesian square of commutative rings whose bottom map is surjective is a fibre square in
the sense of Milnor patching. -/
theorem isFibreSquare_of_isPullback {R P Q W : CommRingCat.{u}} {σ : R ⟶ P} {σ' : R ⟶ Q}
    {τ : P ⟶ W} {π : Q ⟶ W} (H : IsPullback σ σ' τ π) (hπ : Function.Surjective π) :
    MilnorPatching.IsFibreSquare σ.hom σ'.hom τ.hom π.hom := by
  have hcan := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit τ π)
  let e := H.isoIsPullback _ _ hcan
  have h₁ : ∀ x : R, ((e.hom x).1 : P × Q).1 = σ x := fun x =>
    congrArg (fun k : R ⟶ P => k x) (H.isoIsPullback_hom_fst _ _ hcan)
  have h₂ : ∀ x : R, ((e.hom x).1 : P × Q).2 = σ' x := fun x =>
    congrArg (fun k : R ⟶ Q => k x) (H.isoIsPullback_hom_snd _ _ hcan)
  refine ⟨congrArg CommRingCat.Hom.hom H.w, fun x y hσ hσ' => ?_, fun b a hba => ?_, hπ⟩
  · apply (ConcreteCategory.bijective_of_isIso e.hom).1
    exact Subtype.ext (Prod.ext ((h₁ x).trans (hσ.trans (h₁ y).symm))
      ((h₂ x).trans (hσ'.trans (h₂ y).symm)))
  · let z : (CommRingCat.pullbackCone τ π).pt := ⟨(b, a), hba⟩
    refine ⟨e.inv z, ?_, ?_⟩
    · rw [← h₁, ← ConcreteCategory.comp_apply, e.inv_hom_id, ConcreteCategory.id_apply]
    · rw [← h₂, ← ConcreteCategory.comp_apply, e.inv_hom_id, ConcreteCategory.id_apply]

/-- **Over a flat base change of a pushout along a thickening and an affine morphism, global
sections form a fibre square.** Let `t : T ⟶ Y'` be flat and let `T_Y`, `T_{Z'}` and
`T_Z = T_Y ×_Y Z` be its base changes, with `T_{Z'}` affine. Then
`Γ(T) = Γ(T_Y) ×_{Γ(T_Z)} Γ(T_{Z'})` with `Γ(T_{Z'}) ⟶ Γ(T_Z)` surjective: by the closing
paragraph of [Stacks Project, Tag 07RX] the square of the four base changes is again a pushout
along a thickening and an affine morphism, and `Stacks.Pushout.isPullback_appTop_of_isPushout`
applies to it. -/
theorem isFibreSquare_appTop_of_flat (hpo : IsPushout i f g h) (hi : IsThickening i)
    [IsAffineHom f] {T TY TZ' TZ : Scheme.{u}} {t : T ⟶ Y'} {tY : TY ⟶ Y} {tZ' : TZ' ⟶ Z'}
    {tZ : TZ ⟶ Z} {eY : TY ⟶ T} {eZ' : TZ' ⟶ T} {dY : TZ ⟶ TY} {dZ' : TZ ⟶ TZ'}
    (ht : Flat t) (hcomm : dZ' ≫ eZ' = dY ≫ eY)
    (heY : IsPullback eY tY t h) (heZ' : IsPullback eZ' tZ' t g)
    (hdY : IsPullback dY tZ tY f) (hdZ' : IsPullback dZ' tZ tZ' i) (hTZ' : IsAffine TZ') :
    MilnorPatching.IsFibreSquare eY.appTop.hom eZ'.appTop.hom dY.appTop.hom dZ'.appTop.hom := by
  have := hTZ'
  have hi' : IsThickening dZ' := isThickening_of_isPullback hdZ' hi
  have : IsAffineHom dY := MorphismProperty.of_isPullback hdY.flip ‹IsAffineHom f›
  have : IsClosedImmersion dZ' := hi'.1
  exact isFibreSquare_of_isPullback
    (isPullback_appTop_of_isPushout
      (isPushout_restrictions_of_flat hi hpo ht hcomm heY heZ' hdY hdZ') hi')
    (dZ'.app_surjective ⊤ (isAffineOpen_top TZ'))

end Stacks.Pushout

end
