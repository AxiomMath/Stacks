module

public import StacksFrontier.AlgebraicGeometry.AmplePositivePower.Basic
public import StacksFrontier.AlgebraicGeometry.BasisRoute.Basic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleImplications.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative ampleness and the integer tensor powers

For `f : X ⟶ S` and an invertible `𝒪_X`-module `L`, and a predicate `VA` on the tensor powers of
`L`, consider the conditions

1. `L` is ample relative to `f`;
2. `VA` holds for some positive tensor power of `L`;
3. `VA` holds for every sufficiently high tensor power of `L`.

The integer tensor powers `Stacks.AmpleProjectiveImmersion.tensorPowerModule X L d` are invertible
in the sense of `Stacks.Ample.IsInvertibleModule`, relative ampleness passes to positive tensor
powers, and the two biconditionals (1) ↔ (2) and (1) ↔ (3) follow from the implications
(2) ⟹ (1) and (1) ⟹ (3). For `VA` either of `Stacks.RelativeVeryAmple.HasRelativeTwistImmersion`
and `Stacks.RelativeAmpleBasisRoute.HasRelativeBasisImmersion`, both biconditionals hold for every
quasi-compact `f`.

## Main results

* `Stacks.Tag01VUReduction.isInvertibleModule_tensorPowerModule`: every integer tensor power of an
  invertible module is invertible.
* `Stacks.Tag01VUReduction.isRelativelyAmple_iff_isRelativelyAmple_tensorPowModule`: for `d ≥ 1`,
  `L` is ample relative to `f` exactly when `L ^⊗ d` is.
* `Stacks.Tag01VUReduction.iff_exists_and_iff_eventually`: the two biconditionals follow from
  (2) ⟹ (1) and (1) ⟹ (3), for any predicate on the degree.
* `Stacks.Tag01VUReduction.iff_exists_and_iff_eventually_hasRelativeBasisImmersion` and
  `Stacks.Tag01VUReduction.iff_exists_and_iff_eventually_hasRelativeTwistImmersion`: both
  biconditionals hold for the two weakened hypotheses, for quasi-compact `f`.

## References

* [Stacks Project, Tag 01VU](https://stacks.math.columbia.edu/tag/01VU)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01VR](https://stacks.math.columbia.edu/tag/01VR)
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AmpleProjectiveImmersion
open Stacks.RelativeAmpleBasisRoute
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.Tag01VUReduction

/-! ### Invertibility of the integer tensor powers -/

/-- Every integer tensor power `tensorPowerModule X L d` of an invertible `𝒪_X`-module is
invertible. -/
instance isInvertibleModule_tensorPowerModule (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (d : ℤ) : IsInvertibleModule X (tensorPowerModule X L d) := by
  have hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L).mpr inferInstance
  exact (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _).mp
    (Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L d)

/-! ### Relative ampleness of tensor powers -/

/-- If `L` is ample relative to `f`, then so is `L ^⊗ d` for every `d ≥ 1`. -/
@[ega "II 4.6.9" "Clause (i)"]
theorem isRelativelyAmple_tensorPowModule_of_isRelativelyAmple {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (d : ℕ) (hd : 1 ≤ d)
    (h : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f (tensorPowModule X L (d : ℤ)) := by
  exact ⟨h.1, fun V hV ↦ (isAmple_congr _ _ (hN' := isInvertibleModule_tensorPowModule _ _ (d : ℤ))
    (pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι L d)).mpr
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple _ d hd (h.2 V hV))⟩

/-- For `d ≥ 1`, a module is ample relative to `f` exactly when its `d`-th tensor power is. -/
@[ega "II 4.6.9"]
theorem isRelativelyAmple_iff_isRelativelyAmple_tensorPowModule {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (d : ℕ) (hd : 1 ≤ d) :
    Stacks.RelativeAmple.IsRelativelyAmple f L ↔
      Stacks.RelativeAmple.IsRelativelyAmple f (tensorPowModule X L (d : ℤ)) :=
  ⟨isRelativelyAmple_tensorPowModule_of_isRelativelyAmple f L d hd,
    isRelativelyAmple_of_isRelativelyAmple_tensorPowModule f L d hd⟩

/-! ### The hypothesis of the basis route is an invariant of the isomorphism class -/

/-- `Stacks.RelativeAmpleBasisRoute.HasRelativeBasisImmersion` depends only on the isomorphism
class of the module. -/
theorem hasRelativeBasisImmersion_congr {X S : Scheme.{u}} (f : X ⟶ S) (M M' : X.Modules)
    [IsInvertibleModule X M] [IsInvertibleModule X M'] (e : M ≅ M') :
    HasRelativeBasisImmersion f M ↔ HasRelativeBasisImmersion f M' := by
  constructor
  · rintro ⟨P, p, N, hN, i, him, hover, hbasis, ⟨j⟩⟩
    exact ⟨P, p, N, hN, i, him, hover, hbasis, ⟨e.symm ≪≫ j⟩⟩
  · rintro ⟨P, p, N, hN, i, him, hover, hbasis, ⟨j⟩⟩
    exact ⟨P, p, N, hN, i, him, hover, hbasis, ⟨e ≪≫ j⟩⟩

/-! ### Relative ampleness from the weakened hypotheses on tensor powers -/

/-- For quasi-compact `f`, if `HasRelativeBasisImmersion f (tensorPowerModule X L d)` holds for
some `d ≥ 1`, then `L` is ample relative to `f`. -/
theorem isRelativelyAmple_of_exists_hasRelativeBasisImmersion_tensorPowerModule
    {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : ∃ d : ℕ, 1 ≤ d ∧ HasRelativeBasisImmersion f (tensorPowerModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  obtain ⟨d, hd, hVA⟩ := h
  exact isRelativelyAmple_of_exists_hasRelativeBasisImmersion_tensorPowModule f L hf
    ⟨d, hd, (hasRelativeBasisImmersion_congr f _ _
      (Stacks.PowerFamilyBridge.tensorPowerModuleIso X L (d : ℤ))).mp hVA⟩

/-- For quasi-compact `f`, if `HasRelativeBasisImmersion f (tensorPowerModule X L d)` holds for all
sufficiently large `d`, then `L` is ample relative to `f`. -/
theorem isRelativelyAmple_of_eventually_hasRelativeBasisImmersion_tensorPowerModule
    {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      HasRelativeBasisImmersion f (tensorPowerModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  isRelativelyAmple_of_exists_hasRelativeBasisImmersion_tensorPowerModule f L hf
    (exists_one_le_and_of_eventually h)

/-- For quasi-compact `f`, if `HasRelativeTwistImmersion f (tensorPowerModule X L d)` holds for
some `d ≥ 1`, then `L` is ample relative to `f`. -/
theorem isRelativelyAmple_of_exists_hasRelativeTwistImmersion_tensorPowerModule
    {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : ∃ d : ℕ, 1 ≤ d ∧ HasRelativeTwistImmersion f (tensorPowerModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  obtain ⟨d, hd, hVA⟩ := h
  exact Stacks.RelativeAmpleImplications.isRelativelyAmple_of_exists_hasRelativeTwistImmersion
    f L hf ⟨d, hd, (Stacks.RelativeAmpleImplications.hasRelativeTwistImmersion_congr f _ _
      (Stacks.PowerFamilyBridge.tensorPowerModuleIso X L (d : ℤ))).mp hVA⟩

/-- For quasi-compact `f`, if `HasRelativeTwistImmersion f (tensorPowerModule X L d)` holds for all
sufficiently large `d`, then `L` is ample relative to `f`. -/
theorem isRelativelyAmple_of_eventually_hasRelativeTwistImmersion_tensorPowerModule
    {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      HasRelativeTwistImmersion f (tensorPowerModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  isRelativelyAmple_of_exists_hasRelativeTwistImmersion_tensorPowerModule f L hf
    (exists_one_le_and_of_eventually h)

/-! ### The biconditionals from the forward implication -/

/-- Let `P` be a proposition and `VA` a predicate on degrees such that `VA d` implies `P` for every
`d ≥ 1`, and `P` implies `VA d` for all sufficiently large `d`. Then `P` is equivalent to `VA d`
holding for some `d ≥ 1`, and to `VA d` holding for all sufficiently large `d`. -/
theorem iff_exists_and_iff_eventually {P : Prop} {VA : ℕ → Prop}
    (hbwd : ∀ d : ℕ, 1 ≤ d → VA d → P) (hfwd : P → ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → VA d) :
    (P ↔ ∃ d : ℕ, 1 ≤ d ∧ VA d) ∧ (P ↔ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → VA d) := by
  have bwd : (∃ d : ℕ, 1 ≤ d ∧ VA d) → P := fun ⟨d, hd, hVA⟩ ↦ hbwd d hd hVA
  exact ⟨⟨fun hp ↦ exists_one_le_and_of_eventually (hfwd hp), bwd⟩,
    ⟨hfwd, fun h ↦ bwd (exists_one_le_and_of_eventually h)⟩⟩

/-- For quasi-compact `f`, if relative ampleness of `L` implies
`HasRelativeBasisImmersion f (tensorPowerModule X L d)` for all sufficiently large `d`, then
relative ampleness of `L` is equivalent to that hypothesis for some `d ≥ 1`, and to it for all
sufficiently large `d`. -/
theorem iff_exists_and_iff_eventually_hasRelativeBasisImmersion_of_forward {X S : Scheme.{u}}
    (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (hfwd : Stacks.RelativeAmple.IsRelativelyAmple f L →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → HasRelativeBasisImmersion f (tensorPowerModule X L (d : ℤ))) :
    (Stacks.RelativeAmple.IsRelativelyAmple f L ↔
        ∃ d : ℕ, 1 ≤ d ∧ HasRelativeBasisImmersion f (tensorPowerModule X L (d : ℤ))) ∧
      (Stacks.RelativeAmple.IsRelativelyAmple f L ↔
        ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
          HasRelativeBasisImmersion f (tensorPowerModule X L (d : ℤ))) :=
  iff_exists_and_iff_eventually
    (fun d hd h => isRelativelyAmple_of_exists_hasRelativeBasisImmersion_tensorPowerModule f L hf
      ⟨d, hd, h⟩) hfwd

/-- For quasi-compact `f`, if relative ampleness of `L` implies
`HasRelativeTwistImmersion f (tensorPowerModule X L d)` for all sufficiently large `d`, then
relative ampleness of `L` is equivalent to that hypothesis for some `d ≥ 1`, and to it for all
sufficiently large `d`. -/
theorem iff_exists_and_iff_eventually_hasRelativeTwistImmersion_of_forward {X S : Scheme.{u}}
    (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (hfwd : Stacks.RelativeAmple.IsRelativelyAmple f L →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → HasRelativeTwistImmersion f (tensorPowerModule X L (d : ℤ))) :
    (Stacks.RelativeAmple.IsRelativelyAmple f L ↔
        ∃ d : ℕ, 1 ≤ d ∧ HasRelativeTwistImmersion f (tensorPowerModule X L (d : ℤ))) ∧
      (Stacks.RelativeAmple.IsRelativelyAmple f L ↔
        ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
          HasRelativeTwistImmersion f (tensorPowerModule X L (d : ℤ))) :=
  iff_exists_and_iff_eventually
    (fun d hd h => isRelativelyAmple_of_exists_hasRelativeTwistImmersion_tensorPowerModule f L hf
      ⟨d, hd, h⟩) hfwd

/-! ### The biconditionals for the weakened hypotheses -/

/-- If `L` is ample relative to `f`, then `HasRelativeTwistImmersion f (tensorPowerModule X L d)`
holds for every `d ≥ 1`. -/
private theorem hasRelativeTwistImmersion_tensorPowerModule_of_isRelativelyAmple
    {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] (d : ℕ) (hd : 1 ≤ d)
    (h : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    HasRelativeTwistImmersion f (tensorPowerModule X L (d : ℤ)) :=
  hasRelativeTwistImmersion_self f _
    ((isRelativelyAmple_congr f _ _ (Stacks.PowerFamilyBridge.tensorPowerModuleIso X L (d : ℤ))).mpr
      (isRelativelyAmple_tensorPowModule_of_isRelativelyAmple f L d hd h))

/-- If `L` is ample relative to `f`, then `HasRelativeBasisImmersion f (tensorPowerModule X L d)`
holds for every `d ≥ 1`. -/
theorem hasRelativeBasisImmersion_tensorPowerModule_of_isRelativelyAmple {X S : Scheme.{u}}
    (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] (d : ℕ) (hd : 1 ≤ d)
    (h : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    HasRelativeBasisImmersion f (tensorPowerModule X L (d : ℤ)) :=
  hasRelativeBasisImmersion_of_hasRelativeTwistImmersion f _
    (hasRelativeTwistImmersion_tensorPowerModule_of_isRelativelyAmple f L d hd h)

/-- For quasi-compact `f`, `L` is ample relative to `f` exactly when
`HasRelativeBasisImmersion f (tensorPowerModule X L d)` holds for some `d ≥ 1`, and exactly when it
holds for all sufficiently large `d`. -/
theorem iff_exists_and_iff_eventually_hasRelativeBasisImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f) :
    (Stacks.RelativeAmple.IsRelativelyAmple f L ↔
        ∃ d : ℕ, 1 ≤ d ∧ HasRelativeBasisImmersion f (tensorPowerModule X L (d : ℤ))) ∧
      (Stacks.RelativeAmple.IsRelativelyAmple f L ↔
        ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
          HasRelativeBasisImmersion f (tensorPowerModule X L (d : ℤ))) :=
  iff_exists_and_iff_eventually_hasRelativeBasisImmersion_of_forward f L hf fun h =>
    ⟨1, fun d hd => hasRelativeBasisImmersion_tensorPowerModule_of_isRelativelyAmple f L d hd h⟩

/-- For quasi-compact `f`, `L` is ample relative to `f` exactly when
`HasRelativeTwistImmersion f (tensorPowerModule X L d)` holds for some `d ≥ 1`, and exactly when it
holds for all sufficiently large `d`. -/
theorem iff_exists_and_iff_eventually_hasRelativeTwistImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f) :
    (Stacks.RelativeAmple.IsRelativelyAmple f L ↔
        ∃ d : ℕ, 1 ≤ d ∧ HasRelativeTwistImmersion f (tensorPowerModule X L (d : ℤ))) ∧
      (Stacks.RelativeAmple.IsRelativelyAmple f L ↔
        ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
          HasRelativeTwistImmersion f (tensorPowerModule X L (d : ℤ))) :=
  iff_exists_and_iff_eventually_hasRelativeTwistImmersion_of_forward f L hf fun h =>
    ⟨1, fun d hd =>
      hasRelativeTwistImmersion_tensorPowerModule_of_isRelativelyAmple f L d hd h⟩

end Stacks.Tag01VUReduction

end
