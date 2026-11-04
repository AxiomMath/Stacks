module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FormallyEtaleScheme
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Thickenings.Existence

/-!
# Formally étale lifting without affineness hypotheses

Formal étaleness of a morphism of schemes, `AlgebraicGeometry.FormallyEtale`, is a unique lifting
property stated only for first-order thickenings of *affine* schemes. This file shows that the
same unique lifting property then holds for a first-order thickening of arbitrary schemes.

## Main results

* `AlgebraicGeometry.FormallyEtale.existsUnique_lift`: a formally étale morphism admits a unique
  lift across any first-order thickening of schemes over its target.

## References

* [Stacks Project, Tag 04FD](https://stacks.math.columbia.edu/tag/04FD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry

private theorem pullback_fst_comp_eq_of_comp_eq {T T' U V X : Scheme.{u}} {i : T ⟶ T'}
    {e : U ⟶ T'} {g : T ⟶ X} {h : U ⟶ X} (hh : pullback.fst e i ≫ h = pullback.snd e i ≫ g)
    (w : V ⟶ U) {b : V ⟶ T'} (hb : w ≫ e = b) :
    pullback.fst b i ≫ w ≫ h = pullback.snd b i ≫ g := by
  have hw : (pullback.fst b i ≫ w) ≫ e = pullback.snd b i ≫ i := by
    rw [Category.assoc, hb, pullback.condition]
  rw [← Category.assoc, ← pullback.lift_fst_assoc _ _ hw, hh, pullback.lift_snd_assoc]

/-- A formally étale morphism admits a unique lift across the restriction of a first-order
thickening to an affine scheme `U` openly immersed in its ambient scheme. -/
private theorem FormallyEtale.existsUnique_lift_of_isOpenImmersion
    {X S T T' U : Scheme.{u}} {f : X ⟶ S} (hf : FormallyEtale f)
    {i : T ⟶ T'} (hi : IsFirstOrderThickening i) {p : T' ⟶ S} {g : T ⟶ X}
    (hg : g ≫ f = i ≫ p) (e : U ⟶ T') [IsOpenImmersion e] [IsAffine U] :
    ∃! h : U ⟶ X, pullback.fst e i ≫ h = pullback.snd e i ≫ g ∧ h ≫ f = e ≫ p := by
  have : IsClosedImmersion i := hi.1
  have : IsAffine (pullback e i) := isAffine_of_isAffineHom (pullback.fst e i)
  refine hf _ ⟨inferInstance, ?_⟩ (e ≫ p) (pullback.snd e i ≫ g) (by
    rw [Category.assoc, hg, pullback.condition_assoc])
  rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  exact comap_sq_eq_bot_of_isOpenImmersion i.ker e hi.2

/-- For a formally étale morphism, two lifts across the restriction of a first-order thickening
to a scheme `U` openly immersed in its ambient scheme coincide. -/
private theorem FormallyEtale.eq_of_isOpenImmersion
    {X S T T' U : Scheme.{u}} {f : X ⟶ S} (hf : FormallyEtale f)
    {i : T ⟶ T'} (hi : IsFirstOrderThickening i) {p : T' ⟶ S} {g : T ⟶ X}
    (hg : g ≫ f = i ≫ p) (e : U ⟶ T') [IsOpenImmersion e] {h₁ h₂ : U ⟶ X}
    (hg₁ : pullback.fst e i ≫ h₁ = pullback.snd e i ≫ g) (hf₁ : h₁ ≫ f = e ≫ p)
    (hg₂ : pullback.fst e i ≫ h₂ = pullback.snd e i ≫ g) (hf₂ : h₂ ≫ f = e ≫ p) :
    h₁ = h₂ := by
  refine U.affineCover.hom_ext _ _ fun l => ?_
  obtain ⟨_, _, hu⟩ :=
    FormallyEtale.existsUnique_lift_of_isOpenImmersion hf hi hg (U.affineCover.f l ≫ e)
  exact (hu (U.affineCover.f l ≫ h₁) ⟨pullback_fst_comp_eq_of_comp_eq hg₁ _ rfl,
    by simp [hf₁]⟩).trans (hu (U.affineCover.f l ≫ h₂)
      ⟨pullback_fst_comp_eq_of_comp_eq hg₂ _ rfl, by simp [hf₂]⟩).symm

/-- A formally étale morphism admits a unique lift across any first-order
thickening of schemes over its base, without affineness assumptions. -/
@[stacks 04FD]
theorem FormallyEtale.existsUnique_lift
    {X S T T' : Scheme.{u}} (f : X ⟶ S) (hf : FormallyEtale f)
    (i : T ⟶ T') (hi : IsFirstOrderThickening i)
    (p : T' ⟶ S) (g : T ⟶ X) (hg : g ≫ f = i ≫ p) :
    ∃! h : T' ⟶ X, i ≫ h = g ∧ h ≫ f = p := by
  classical
  let 𝒰 := T'.affineCover
  have localLift (j : 𝒰.I₀) :=
    FormallyEtale.existsUnique_lift_of_isOpenImmersion hf hi hg (𝒰.f j)
  let lift (j : 𝒰.I₀) : 𝒰.X j ⟶ X := Classical.choose (localLift j)
  have lift_spec (j : 𝒰.I₀) :
      pullback.fst (𝒰.f j) i ≫ lift j = pullback.snd (𝒰.f j) i ≫ g ∧
        lift j ≫ f = 𝒰.f j ≫ p := (Classical.choose_spec (localLift j)).1
  have compatible (j k : 𝒰.I₀) :
      pullback.fst (𝒰.f j) (𝒰.f k) ≫ lift j = pullback.snd (𝒰.f j) (𝒰.f k) ≫ lift k :=
    FormallyEtale.eq_of_isOpenImmersion hf hi hg (pullback.fst (𝒰.f j) (𝒰.f k) ≫ 𝒰.f j)
      (pullback_fst_comp_eq_of_comp_eq (lift_spec j).1 _ rfl) (by simp [(lift_spec j).2])
      (pullback_fst_comp_eq_of_comp_eq (lift_spec k).1 _ pullback.condition.symm)
      (by simp [(lift_spec k).2, pullback.condition_assoc])
  let h := 𝒰.glueMorphisms lift compatible
  let 𝒯 : T.OpenCover := Scheme.Cover.mkOfCovers 𝒰.I₀
      (fun j => pullback i (𝒰.f j)) (fun j => pullback.fst i (𝒰.f j)) (by
        intro t
        obtain ⟨j, y, hy⟩ := 𝒰.exists_eq (i t)
        obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback t y hy.symm
        exact ⟨j, z, hz⟩)
  have hi' : i ≫ h = g := by
    refine 𝒯.hom_ext _ _ fun (j : 𝒰.I₀) => ?_
    change pullback.fst i (𝒰.f j) ≫ i ≫ h = pullback.fst i (𝒰.f j) ≫ g
    rw [pullback.condition_assoc, 𝒰.ι_glueMorphisms, ← pullbackSymmetry_hom_comp_fst,
      Category.assoc, (lift_spec j).1, pullbackSymmetry_hom_comp_snd_assoc]
  have hp' : h ≫ f = p := 𝒰.hom_ext _ _ fun j => by
    rw [𝒰.ι_glueMorphisms_assoc lift compatible j, (lift_spec j).2]
  refine ⟨h, ⟨hi', hp'⟩, fun h' hh' => 𝒰.hom_ext _ _ fun j => ?_⟩
  exact ((Classical.choose_spec (localLift j)).2 _ ⟨by rw [pullback.condition_assoc, hh'.1],
    by rw [Category.assoc, hh'.2]⟩).trans (𝒰.ι_glueMorphisms lift compatible j).symm

end AlgebraicGeometry

end
