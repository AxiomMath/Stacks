module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal

/-!
# Integral birational morphisms to normal schemes

An integral birational morphism between integral schemes is an isomorphism when its target is
normal. In particular, this applies to finite birational morphisms.

The point is local on the target: on an affine open `U` of the normal target, the ring of
sections of the source over the preimage of `U` is integral over `Γ(X, U)` and sits inside the
common function field, so integral closedness of `Γ(X, U)` forces the two to agree.

## Main results

* `AlgebraicGeometry.isIso_of_isIntegralHom_of_isBirational_of_isNormal`: an integral birational
  morphism of integral schemes with normal target is an isomorphism.

## Implementation notes

The result is stated for integral morphisms, the stronger form in the source. Since finite
morphisms are integral, it includes the finite case.

## References

* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- At the generic point of an integral scheme, the stalk is a fraction field of the sections
over any nonempty affine open containing it. -/
private theorem isFractionRing_stalk_of_eq_genericPoint
    (Y : Scheme.{u}) [IsIntegral Y] (U : Y.Opens) (hU : IsAffineOpen U)
    [Nonempty U] (x : Y) (hxU : x ∈ U) (hx : x = genericPoint Y) :
    letI : Algebra Γ(Y, U) (Y.presheaf.stalk x) :=
      (Y.presheaf.germ U x hxU).hom.toAlgebra
    IsFractionRing Γ(Y, U) (Y.presheaf.stalk x) := by
  subst x
  exact functionField_isFractionRing_of_isAffineOpen Y U hU

/-- The map on sections of an integral birational morphism of integral schemes with normal
target over a nonempty affine open is an isomorphism. -/
private theorem isIso_app_of_isIntegralHom_of_isBirational_of_isNormal
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsIntegralHom f] [IsNormal Y] (hf : IsBirational f)
    (U : Y.affineOpens) [Nonempty U.1] : IsIso (f.app U.1) := by
  have hηX : genericPoint X ∈ genericPoints X := by simp [genericPoints_eq_singleton]
  have heq : f (genericPoint X) = genericPoint Y := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hf.bijOn.1 hηX
  have hfxU : f (genericPoint X) ∈ U.1 := by
    rw [heq]
    exact ((genericPoint_spec Y).mem_open_set_iff U.1.isOpen).2 (by simpa using ‹Nonempty U.1›)
  let : Nonempty (f ⁻¹ᵁ U.1) := ⟨⟨genericPoint X, hfxU⟩⟩
  have : IsIso (f.stalkMap (genericPoint X)) := hf.isIso_stalkMap _ hηX
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro a b hab
    apply germ_injective_of_isIntegral Y (f (genericPoint X)) hfxU
    apply (ConcreteCategory.bijective_of_isIso (f.stalkMap (genericPoint X))).1
    rw [f.germ_stalkMap_apply, f.germ_stalkMap_apply, hab]
  · intro b
    let A := Γ(Y, U.1)
    let B := Γ(X, f ⁻¹ᵁ U.1)
    let KY := Y.presheaf.stalk (f (genericPoint X))
    let KX := X.functionField
    let : Algebra A B := (f.app U.1).hom.toAlgebra
    let : Algebra A KX := ((f.app U.1) ≫ X.germToFunctionField (f ⁻¹ᵁ U.1)).hom.toAlgebra
    let : Algebra A KY :=
      (Y.presheaf.germ U.1 (f (genericPoint X)) hfxU).hom.toAlgebra
    let : IsFractionRing A KY :=
      isFractionRing_stalk_of_eq_genericPoint Y U.1 U.2 _ hfxU heq
    let e : KY ≃ₐ[A] KX :=
      { (asIso (f.stalkMap (genericPoint X))).commRingCatIsoToRingEquiv with
        commutes' := fun a ↦ by
          show f.stalkMap (genericPoint X)
              (Y.presheaf.germ U.1 (f (genericPoint X)) hfxU a) =
            X.germToFunctionField (f ⁻¹ᵁ U.1) (f.app U.1 a)
          exact f.germ_stalkMap_apply U.1 (genericPoint X) hfxU a }
    let : IsFractionRing A KX := IsFractionRing.of_algEquiv e
    let : IsScalarTower A B KX := IsScalarTower.of_algebraMap_eq' rfl
    have hb : _root_.IsIntegral A b := f.isIntegral_app U.1 U.2 b
    obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff KX).mp
      ((isNormal_iff_forall_affineOpen_normal Y).mp inferInstance U ‹_›)
      (x := X.germToFunctionField (f ⁻¹ᵁ U.1) b) (hb.map (IsScalarTower.toAlgHom A B KX))
    exact ⟨a, X.germToFunctionField_injective (f ⁻¹ᵁ U.1) ha⟩

/-- **Stacks Project, Tag 0AB1.** An integral birational morphism of integral schemes whose
target is normal is an isomorphism. -/
@[stacks 0AB1,
  ega "IV 8.12.10.1" "more general",
  ega "II 6.1.15",
  ega "II 8.11.2" "special case",
  ega "IV 17.15.14.1" "(i), special case",
  ega "IV 8.12.10" "special case"]
public theorem isIso_of_isIntegralHom_of_isBirational_of_isNormal
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsIntegralHom f] [IsNormal Y] (hf : IsBirational f) :
    IsIso f := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    Y.affineCover).mpr fun i ↦ ?_
  let U : Y.affineOpens := ⟨_, isAffineOpen_opensRange (Y.affineCover.f i)⟩
  have : Nonempty U.1 := by
    let V := (Y.local_affine i).choose
    let e := Classical.choice (Y.local_affine i).choose_spec.choose_spec
    let z := e.hom.base ⟨i, V.2⟩
    exact ⟨⟨(Y.affineCover.f i).base z, Set.mem_range_self _⟩⟩
  have := isIso_app_of_isIntegralHom_of_isBirational_of_isNormal f hf U
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (morphismRestrictOpensRange f (Y.affineCover.f i))).mp
    ((isIso_morphismRestrict_iff_isIso_app f U.2).2 this)

end AlgebraicGeometry
