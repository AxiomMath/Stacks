module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.SpaceLiftCover
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource

/-!
# A smooth morphism of algebraic spaces is formally smooth

This is the implication (1) ⇒ (2) of Stacks 04AM in full generality, without the descent
hypothesis `AlgebraicGeometry.Space.FormallySmoothEtaleDescent` that
`AlgebraicGeometry.Space.formallySmooth_of_isSmooth` carries.

Base changing along the given section `y : T' ⟶ Y` of the target (Stacks 02X2 and 03ZE), the
lifting problem becomes that of extending a point of an algebraic space smooth over the affine
`T'` across the thickening `T ⟶ T'`, which is
`AlgebraicGeometry.Stack.GroupoidLift.exists_lift_of_isSmooth`.

## Main results

* `AlgebraicGeometry.Space.formallySmooth_of_isSmooth_unconditional`.
-/

@[expose] public section

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A smooth morphism of algebraic spaces is formally smooth** (Stacks 04AM, (1) ⇒ (2), the
formal smoothness). -/
theorem formallySmooth_of_isSmooth_unconditional {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsSmooth B S hS f) : FormallySmooth f := by
  intro T T' hT hT' i hi x y hxy
  let y' : yoneda.obj T' ⟶ Y := yonedaEquiv.symm y
  let fA : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩ := ObjectProperty.homMk f
  let yA : (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨Y, hY⟩ := ObjectProperty.homMk y'
  have hπ : IsSmooth B S hS (pullback.snd f y') :=
    (isSmooth_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS fA yA) hf
  have hP : IsAlgebraicSpace B S hS (pullback f y') :=
    (AlgebraicSpaces.fiberProduct B S hS fA yA).property
  have hw : yonedaEquiv.symm x ≫ f = yoneda.map i ≫ y' := by
    simp only [y']
    rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_left, hxy]
  let xr : (pullback f y').obj (op T) := yonedaEquiv (pullback.lift _ _ hw)
  have hxr : (pullback.snd f y').app (op T) xr = i := by
    simp only [xr]
    rw [← yonedaEquiv_comp, pullback.lift_snd, yonedaEquiv_yoneda_map]
  obtain ⟨z, hz, hzπ⟩ := Stack.GroupoidLift.exists_lift_of_isSmooth (pullback.snd f y') hP hπ i
    hi xr hxr
  refine ⟨(pullback.fst f y').app (op T') z, ?_, ?_⟩
  · rw [← NatTrans.naturality_apply, hz]
    simp only [xr]
    rw [← yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]
  · rw [← NatTrans.comp_app_apply, pullback.condition, NatTrans.comp_app_apply, hzπ]
    exact yonedaEquiv.apply_symm_apply y

end AlgebraicGeometry.Space

end
