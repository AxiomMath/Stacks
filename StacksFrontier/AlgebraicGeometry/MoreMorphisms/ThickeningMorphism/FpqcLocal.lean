module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.FpqcLocal

/-!
# Thickenings are fpqc local on the target

Let `f : X ⟶ Y` be a morphism of schemes and `{Yᵢ ⟶ Y}` an fpqc covering. Then `f` is a
thickening if and only if every base change `Yᵢ ×_Y X ⟶ Yᵢ` is a thickening, and the same
holds for first-order thickenings.

## Main results

* `Stacks.Thickenings.isThickening_isLocalAtTarget_fpqc`: being a thickening is fpqc local on
  the target.
* `Stacks.Thickenings.isFirstOrderThickening_isLocalAtTarget_fpqc`: being a first-order
  thickening is fpqc local on the target.

## Implementation notes

A thickening is a surjective closed immersion, and both halves are already known to be fpqc
local on the target, so the first statement is the infimum of those two.

The first-order condition is not an infimum of properties that are separately fpqc local, so
it goes through the criterion `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage`: being a
first-order thickening is Zariski local on the target and stable under arbitrary base change,
and it descends along a surjective flat quasi-compact morphism. Only the descent needs an
argument, and `AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact`
reduces it to the case of a faithfully flat map of affine schemes `Spec S ⟶ Spec R` and a
morphism `g : Y ⟶ Spec R` whose base change is a first-order thickening. There `g` is a closed
immersion because closed immersions descend, hence `Y` is affine. Writing `I` for the kernel of
`Γ(Spec R) ⟶ Γ(Y)`, commutativity of the pullback square on global sections puts the extension
of `I` inside the kernel of `Γ(Spec S) ⟶ Γ(Spec S ×_{Spec R} Y)`, whose square vanishes; so the
extension of `I ^ 2` vanishes, and lifting ideals along a faithfully flat ring map is injective.

## References

* [Stacks Project, Tag 0BPF](https://stacks.math.columbia.edu/tag/0BPF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MorphismProperty

namespace Stacks.Thickenings

universe u

/-- A thickening is exactly a morphism which is both a closed immersion and surjective. -/
private theorem isThickening_eq_inf :
    (@IsThickening : MorphismProperty Scheme.{u}) =
      (@IsClosedImmersion ⊓ @Surjective : MorphismProperty Scheme.{u}) := by
  ext X Y f
  exact ⟨fun h ↦ ⟨h.1, ⟨h.2⟩⟩, fun h ↦ ⟨h.1, h.2.surj⟩⟩

/-- **Stacks Project, Tag 0BPF.** Being a thickening is fpqc local on the target: a morphism
whose base changes along the members of an fpqc covering of the target are all thickenings is
itself a thickening. -/
@[stacks 0BPF "thickenings"]
instance isThickening_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@IsThickening : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := by
  rw [isThickening_eq_inf]
  exact .inf _ _

/-- A surjective local isomorphism is surjective and flat. -/
private alias isLocalIso_inf_surjective_le_surjective_inf_flat :=
  Stacks.Descent.isLocalIso_inf_surjective_le_surjective_inf_flat

/-- Surjective flat morphisms are stable under base change. -/
private alias isStableUnderBaseChange_surjective_inf_flat :=
  Stacks.Descent.isStableUnderBaseChange_surjective_inf_flat

/-- Surjective flat morphisms are stable under composition. -/
private alias isStableUnderComposition_surjective_inf_flat :=
  Stacks.Descent.isStableUnderComposition_surjective_inf_flat

/-- For a morphism to an affine scheme, the kernel ideal sheaf is square-zero exactly when the
kernel of the induced map of global sections is. -/
private theorem ker_sq_eq_bot_iff_of_isAffine {X Z : Scheme.{u}} [IsAffine Z] (h : X ⟶ Z)
    [QuasiCompact h] :
    h.ker ^ 2 = (⊥ : Z.IdealSheafData) ↔ RingHom.ker h.appTop.hom ^ 2 = ⊥ := by
  refine ⟨fun hh ↦ ?_, fun hh ↦ ?_⟩
  · have h2 : h.ker.ideal ⟨⊤, isAffineOpen_top Z⟩ ^ 2 = ⊥ :=
      congrArg (fun I : Z.IdealSheafData ↦ I.ideal ⟨⊤, isAffineOpen_top Z⟩) hh
    rwa [Scheme.Hom.ker_apply] at h2
  · refine Scheme.IdealSheafData.ext_of_isAffine ?_
    change h.ker.ideal ⟨⊤, isAffineOpen_top Z⟩ ^ 2 = ⊥
    rwa [Scheme.Hom.ker_apply]

/-- **The descent step for Tag 0BPF.** Let `Spec S ⟶ Spec R` be a surjective flat morphism of
affine schemes and `g : Y ⟶ Spec R` a morphism whose base change along it is a first-order
thickening. Then `g` is a first-order thickening. -/
private theorem firstOrderThickening_of_affine_descent {R S : CommRingCat.{u}} {Y : Scheme.{u}}
    (φ : R ⟶ S) (g : Y ⟶ Spec R)
    (hφ : (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}) (Spec.map φ))
    (hfst : IsFirstOrderThickening (pullback.fst (Spec.map φ) g)) :
    IsFirstOrderThickening g := by
  have hci : IsClosedImmersion g :=
    MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @IsClosedImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨hφ, inferInstance⟩ hfst.1
  have : IsClosedImmersion (pullback.fst (Spec.map φ) g) := hfst.1
  have : IsAffine Y := (IsClosedImmersion.isAffine_surjective_of_isAffine g).1
  let : Algebra Γ(Spec R, ⊤) Γ(Spec S, ⊤) := (Spec.map φ).appTop.hom.toAlgebra
  have : Module.FaithfullyFlat Γ(Spec R, ⊤) Γ(Spec S, ⊤) :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (Spec.map φ)).mp ⟨hφ.2, hφ.1⟩
  set K : Ideal Γ(Spec S, ⊤) := RingHom.ker (pullback.fst (Spec.map φ) g).appTop.hom
  refine ⟨hci, (ker_sq_eq_bot_iff_of_isAffine g).mpr ?_⟩
  -- The ideal of `g` extends into the ideal of its base change, by commutativity of the square.
  have hle : (RingHom.ker g.appTop.hom).map (algebraMap Γ(Spec R, ⊤) Γ(Spec S, ⊤)) ≤ K := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hw := congrArg (fun k : pullback (Spec.map φ) g ⟶ Spec R ↦ k.appTop.hom a)
      (pullback.condition (f := Spec.map φ) (g := g))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hw
    change (pullback.fst (Spec.map φ) g).appTop.hom (algebraMap _ _ a) = 0
    rw [RingHom.algebraMap_toAlgebra, hw, show g.appTop.hom a = 0 from ha, map_zero]
  -- Hence the extension of its square vanishes, and faithful flatness removes the extension.
  refine Ideal.map_injective_of_faithfullyFlat (A := Γ(Spec R, ⊤)) (B := Γ(Spec S, ⊤)) ?_
  rw [Ideal.map_bot, Ideal.map_pow]
  exact le_bot_iff.mp ((Ideal.pow_right_mono hle 2).trans
    ((ker_sq_eq_bot_iff_of_isAffine _).mp hfst.2).le)

/-- **Stacks Project, Tag 0BPF.** First-order thickenings satisfy fpqc descent: a morphism
whose base change along a surjective flat quasi-compact morphism is a first-order thickening is
itself a first-order thickening. -/
private theorem isFirstOrderThickening_descendsAlong :
    MorphismProperty.DescendsAlong (@IsFirstOrderThickening : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := isFirstOrderThickening_isZariskiLocalAtTarget.{u}
  have := isStableUnderBaseChange_surjective_inf_flat.{u}
  have := isStableUnderComposition_surjective_inf_flat.{u}
  exact IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact @IsFirstOrderThickening
    (@Surjective ⊓ @Flat) isLocalIso_inf_surjective_le_surjective_inf_flat
    firstOrderThickening_of_affine_descent

/-- **Stacks Project, Tag 0BPF.** Being a first-order thickening is fpqc local on the target: a
morphism whose base changes along the members of an fpqc covering of the target are all
first-order thickenings is itself a first-order thickening. -/
@[stacks 0BPF "first-order thickenings"]
instance isFirstOrderThickening_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@IsFirstOrderThickening : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := isFirstOrderThickening_isZariskiLocalAtTarget.{u}
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@IsFirstOrderThickening : MorphismProperty Scheme.{u})
  have := isFirstOrderThickening_descendsAlong.{u}
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

end Stacks.Thickenings

end
