module

public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceRigidity
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Specialization of invertible modules on projective space over a scheme

For a scheme `S` write `𝒪(d)` on `ℙᵐ_S` for the pullback of the twisting sheaf of the integral
model `ℙᵐ_ℤ`. Its class `τ_S(d) ∈ Pic(ℙᵐ_S)` is natural in `S` on the nose, and for `S = Spec A`
with `A` a unique factorization domain and `0 < m` it is the isomorphism `ℤ ≃ Pic(ℙᵐ_A)` of
Stacks 0BXJ. Consequently, for **any** morphism `Spec B ⟶ Spec A` between spectra of unique
factorization domains the pullback `Pic(ℙᵐ_A) ⟶ Pic(ℙᵐ_B)` is injective.

Applied to the local rings of a scheme `T` this gives the rigidity statement used in the last
paragraph of the proof of Stacks 0FH9 in place of Euler characteristics: if `p` and `q` are
points of `T` with factorial local rings and a common generization `η` with factorial local
ring (for instance the generic point of an integral scheme), then an invertible module on `ℙᵐ_T`
trivial on the fibre over `p` is trivial on the fibre over `q`.

## Main definitions

* `Stacks.PicardUFD.projectiveTwistClassHom`: `τ_S : ℤ →+ Pic(ℙᵐ_S)`.

## Main results

* `Stacks.PicardUFD.pullbackPicardHom_projectiveTwistClassHom`: naturality of `τ`.
* `Stacks.PicardUFD.projectiveTwistClassHom_eq`: over a unique factorization domain `τ` is the
  isomorphism of Stacks 0BXJ.
* `Stacks.PicardUFD.injective_pullbackPicardHom_projectiveSpaceOverMap_spec`: injectivity of the
  pullback along any morphism of spectra of unique factorization domains.
* `Stacks.PicardUFD.pullbackPicardHom_eq_zero_of_specializes`: **the rigidity statement** over a
  scheme with factorial local rings at two points and at a common generization.

## References

* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.PicardUFD

open Stacks.SheafOfModules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The twisting classes `d ↦ [𝒪(d)]` of the integral model `ℙᵐ_ℤ`. -/
def integralTwistClassHom (m : ℕ) : ℤ →+ (projectiveSpaceAtUniverse.{u} m).picardGroup :=
  twistPicardHom (ULift.{u} ℤ) m

/-- **The twisting classes of `ℙᵐ_S`**: `d ↦ [𝒪(d)]`, where `𝒪(d)` is the pullback of the
twisting sheaf of the integral model `ℙᵐ_ℤ` along the projection `ℙᵐ_S ⟶ ℙᵐ_ℤ`. -/
def projectiveTwistClassHom (m : ℕ) (S : Scheme.{u}) :
    ℤ →+ (projectiveSpaceOver m S).picardGroup :=
  (pullbackPicardHom (projectiveSpaceOver.toIntegralAtUniverse m S)).comp
    (integralTwistClassHom m)

/-- The class `τ_S(d)` is the pullback of the integral twisting class `[𝒪(d)]` along the
projection `ℙᵐ_S ⟶ ℙᵐ_ℤ`. -/
theorem projectiveTwistClassHom_apply (m : ℕ) (S : Scheme.{u}) (d : ℤ) :
    projectiveTwistClassHom m S d =
      pullbackPicardHom (projectiveSpaceOver.toIntegralAtUniverse m S)
        (integralTwistClassHom m d) :=
  rfl

/-- **The twisting classes are natural in the base**: pulling back along `ℙᵐ_{S'} ⟶ ℙᵐ_S`
carries `[𝒪(d)]` to `[𝒪(d)]`. -/
theorem pullbackPicardHom_projectiveTwistClassHom (m : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S)
    (d : ℤ) :
    pullbackPicardHom (projectiveSpaceOverMap m g) (projectiveTwistClassHom m S d) =
      projectiveTwistClassHom m S' d :=
  (pullbackPicardHom_comp_apply _ _ _).symm.trans
    (congrArg (fun φ => pullbackPicardHom φ (integralTwistClassHom m d))
      (projectiveSpaceOverMap_snd m g))

variable (A : Type u) [CommRing A]

/-- The twisting classes on `ℙᵐ_A`, pulled back to `Proj A[T₀, …, Tₘ]` along the comparison of
models, are the classes of the twisting sheaves of the polynomial grading. This is the twist
transport of Tag 01N2 for polynomial rings,
`Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport`. -/
theorem pullbackPicardHom_projModelIso_hom_projectiveTwistClassHom (m : ℕ) (d : ℤ) :
    pullbackPicardHom (Stacks.ProjectiveCohomology.projModelIso A m).hom
        (projectiveTwistClassHom m (Spec (CommRingCat.of A)) d) =
      twistPicardHom A m d := by
  refine (pullbackPicardHom_comp_apply _ _ _).symm.trans ?_
  refine (congrArg (fun φ => pullbackPicardHom φ (integralTwistClassHom m d))
    (Stacks.ProjectiveCohomology.projModelIso_hom_toIntegralAtUniverse A m)).trans ?_
  refine (congrArg (pullbackPicardHom (Stacks.ProjectiveCohomology.projModelMap m
    (Stacks.ProjectiveCohomology.fromULiftInt A))) (twistPicardHom_apply (ULift.{u} ℤ) m d)).trans
    ?_
  refine (pullbackPicardHom_picardClass _ _ _).trans ((twistPicardHom_apply A m d) ▸ ?_)
  obtain ⟨e⟩ := Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport A m d
  exact (Scheme.picardClass_eq_iff _ _ _ _ _).mpr ⟨e⟩

variable [IsDomain A] [UniqueFactorizationMonoid A]

/-- **Over a unique factorization domain the twisting classes are the isomorphism of Stacks
0BXJ.** -/
theorem projectiveTwistClassHom_eq (m : ℕ) (hm : 0 < m) (d : ℤ) :
    projectiveTwistClassHom m (Spec (CommRingCat.of A)) d =
      projectiveSpaceOverRingPicardAddEquiv A m hm d := by
  let e := Stacks.ProjectiveCohomology.projModelIso A m
  apply (picardGroupAddEquivOfIso e).symm.injective
  show pullbackPicardHom e.hom _ = pullbackPicardHom e.hom
    (pullbackPicardHom e.inv (twistPicardHom A m d))
  rw [← pullbackPicardHom_comp_apply, e.hom_inv_id, pullbackPicardHom_id,
    pullbackPicardHom_projModelIso_hom_projectiveTwistClassHom]
  rfl

/-- Over a unique factorization domain the twisting classes exhaust the Picard group, injectively,
for `0 < m`. -/
theorem bijective_projectiveTwistClassHom (m : ℕ) (hm : 0 < m) :
    Function.Bijective (projectiveTwistClassHom m (Spec (CommRingCat.of A))) := by
  have h : ⇑(projectiveTwistClassHom m (Spec (CommRingCat.of A))) =
      ⇑(projectiveSpaceOverRingPicardAddEquiv A m hm) :=
    funext (projectiveTwistClassHom_eq A m hm)
  rw [h]
  exact (projectiveSpaceOverRingPicardAddEquiv A m hm).bijective

/-- **Pullback along any morphism of spectra of unique factorization domains is injective on the
Picard groups of projective space.** -/
theorem injective_pullbackPicardHom_projectiveSpaceOverMap_spec (m : ℕ) {A B : CommRingCat.{u}}
    [IsDomain A] [UniqueFactorizationMonoid A] [IsDomain B] [UniqueFactorizationMonoid B]
    (g : Spec B ⟶ Spec A) :
    Function.Injective (pullbackPicardHom (projectiveSpaceOverMap m g)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have := subsingleton_picardGroup_projectiveSpaceOverRing_zero A
    exact fun x y _ => Subsingleton.elim x y
  have hA : Function.Bijective (projectiveTwistClassHom m (Spec A)) :=
    bijective_projectiveTwistClassHom A m hm
  have hB : Function.Bijective (projectiveTwistClassHom m (Spec B)) :=
    bijective_projectiveTwistClassHom B m hm
  intro x y hxy
  obtain ⟨a, rfl⟩ := hA.2 x
  obtain ⟨b, rfl⟩ := hA.2 y
  rw [pullbackPicardHom_projectiveTwistClassHom, pullbackPicardHom_projectiveTwistClassHom] at hxy
  rw [hB.1 hxy]

end Stacks.PicardUFD

namespace Stacks.PicardUFD

open Stacks.SheafOfModules

/-- The fibre of `ℙᵐ_T` over the local scheme at `t`, as a morphism of projective spaces. -/
abbrev projectiveSpaceStalkMap (m : ℕ) {T : Scheme.{u}} (t : T) :
    projectiveSpaceOver m (Spec (T.presheaf.stalk t)) ⟶ projectiveSpaceOver m T :=
  projectiveSpaceOverMap m (T.fromSpecStalk t)

/-- Pulling back along `ℙᵐ_g` and then `ℙᵐ_h` is pulling back along `ℙᵐ_{g ≫ h}`. -/
private theorem pullbackPicardHom_projectiveSpaceOverMap_comp_apply (m : ℕ) {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (h : Y ⟶ Z) (x : (projectiveSpaceOver m Z).picardGroup) :
    pullbackPicardHom (projectiveSpaceOverMap m g)
        (pullbackPicardHom (projectiveSpaceOverMap m h) x) =
      pullbackPicardHom (projectiveSpaceOverMap m (g ≫ h)) x := by
  rw [← pullbackPicardHom_comp_apply, projectiveSpaceOverMap_comp]

/-- A morphism from the spectrum of a local ring factors through the local scheme at the image of
its closed point, so its fibre factors through the fibre over that local scheme. -/
theorem pullbackPicardHom_projectiveSpaceOverMap_eq_comp_stalk (m : ℕ) {T : Scheme.{u}}
    {R : CommRingCat.{u}} [IsLocalRing R] (f : Spec R ⟶ T)
    (x : (projectiveSpaceOver m T).picardGroup) :
    pullbackPicardHom (projectiveSpaceOverMap m f) x =
      pullbackPicardHom (projectiveSpaceOverMap m (Spec.map (Scheme.stalkClosedPointTo f)))
        (pullbackPicardHom (projectiveSpaceStalkMap m (f (IsLocalRing.closedPoint R))) x) := by
  rw [projectiveSpaceStalkMap, pullbackPicardHom_projectiveSpaceOverMap_comp_apply,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

/-- **Rigidity of invertible modules on `ℙᵐ_T` along specializations.** Let `R`, `R'` be local
unique factorization domains and `p : Spec R ⟶ T`, `q : Spec R' ⟶ T` morphisms whose closed
points go to `t_p`, `t_q`. Suppose the local rings of `T` at `t_p`, `t_q` and at a common
generization `η` of both are unique factorization domains. Then a class on `ℙᵐ_T` whose pullback
to the fibre over `p` vanishes has vanishing pullback to the fibre over `q`. -/
theorem pullbackPicardHom_eq_zero_of_specializes (m : ℕ) {T : Scheme.{u}}
    {R R' : CommRingCat.{u}} [IsLocalRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [IsLocalRing R'] [IsDomain R'] [UniqueFactorizationMonoid R']
    (p : Spec R ⟶ T) (q : Spec R' ⟶ T) (η : T)
    (hp : η ⤳ p (IsLocalRing.closedPoint R)) (hq : η ⤳ q (IsLocalRing.closedPoint R'))
    [IsDomain (T.presheaf.stalk (p (IsLocalRing.closedPoint R)))]
    [UniqueFactorizationMonoid (T.presheaf.stalk (p (IsLocalRing.closedPoint R)))]
    [IsDomain (T.presheaf.stalk (q (IsLocalRing.closedPoint R')))]
    [UniqueFactorizationMonoid (T.presheaf.stalk (q (IsLocalRing.closedPoint R')))]
    [IsDomain (T.presheaf.stalk η)] [UniqueFactorizationMonoid (T.presheaf.stalk η)]
    (x : (projectiveSpaceOver m T).picardGroup)
    (hx : pullbackPicardHom (projectiveSpaceOverMap m p) x = 0) :
    pullbackPicardHom (projectiveSpaceOverMap m q) x = 0 := by
  set tp := p (IsLocalRing.closedPoint R)
  set tq := q (IsLocalRing.closedPoint R')
  -- the class vanishes on the local scheme at `tp`
  have hxp : pullbackPicardHom (projectiveSpaceStalkMap m tp) x = 0 := by
    rw [pullbackPicardHom_projectiveSpaceOverMap_eq_comp_stalk m p x] at hx
    exact injective_pullbackPicardHom_projectiveSpaceOverMap_spec m
      (Spec.map (Scheme.stalkClosedPointTo p)) (hx.trans (map_zero _).symm)
  -- hence at the common generization
  have hxη : pullbackPicardHom (projectiveSpaceStalkMap m η) x = 0 := by
    rw [projectiveSpaceStalkMap, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hp,
      ← pullbackPicardHom_projectiveSpaceOverMap_comp_apply, hxp, map_zero]
  -- hence at `tq`, by injectivity of the pullback from `tq` to `η`
  have hxq : pullbackPicardHom (projectiveSpaceStalkMap m tq) x = 0 := by
    refine injective_pullbackPicardHom_projectiveSpaceOverMap_spec m
      (Spec.map (T.presheaf.stalkSpecializes hq)) ?_
    rw [pullbackPicardHom_projectiveSpaceOverMap_comp_apply,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, map_zero]
    exact hxη
  rw [pullbackPicardHom_projectiveSpaceOverMap_eq_comp_stalk m q x, hxq, map_zero]

end Stacks.PicardUFD

end
