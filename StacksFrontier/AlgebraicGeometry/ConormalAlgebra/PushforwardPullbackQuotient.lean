module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerIterate

/-!
# `ℐ ^ m (ℐ ^ n 𝓖) = ℐ ^ (n + m) 𝓖`, the Artin–Rees identity for the ideal-power filtration

Let `X` be a scheme, `ℐ` a quasi-coherent sheaf of ideals and `𝓖` a quasi-coherent
`𝒪_X`-module. The member `ℐ ^ n 𝓖` of the ideal-power filtration of `𝓖` carries a filtration of
its own, and its `m`-th member is the `(n + m)`-th member of the filtration of `𝓖`:

`ℐ ^ m (ℐ ^ n 𝓖) = ℐ ^ (n + m) 𝓖`   as subsheaves of `ℐ ^ n 𝓖`.

`StacksFrontier/AlgebraicGeometry/Duality/ExtensionZeroCoherent/IdealPowerIterate.lean` constructs
the inclusion `ℐ ^ (n + m) 𝓖 ⊆ ℐ ^ m (ℐ ^ n 𝓖)` — the half which splits a power of the ideal into
two factors — and its implementation note explicitly declines the reverse inclusion. This file
supplies that reverse inclusion and states the equality.

At `m = 1` this is `ℐ · (ℐ ^ n 𝓖) = ℐ ^ (n + 1) 𝓖`, the step that identifies the degree-`n` piece
of the associated graded module of the filtration.

## Main definitions

None: both sides of the equality already exist. The subsheaf `ℐ ^ m (ℐ ^ n 𝓖)` of `ℐ ^ n 𝓖` is
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` at the module
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul`, and `ℐ ^ (n + m) 𝓖` is read inside
`ℐ ^ n 𝓖` as the preimage `AlgebraicGeometry.sheafSubmoduleComap` of the filtration member along
the inclusion `ℐ ^ n 𝓖 ⟶ 𝓖`.

## Main results

All names below are in the namespace `Stacks.AlgebraicGeometry.IdealPowerColimit`.

* `smul_mem_secs_idealPowerMultiple_add`: a section of `ℐ ^ n 𝓖` over an affine open,
  multiplied by an element of `ℐ(U) ^ m`, lies in the sections of `ℐ ^ (n + m) 𝓖`.
* `idealPowerMultiple_le_sheafSubmoduleComap_submoduleι`: the inclusion
  `ℐ ^ m (ℐ ^ n 𝓖) ⊆ ℐ ^ (n + m) 𝓖`.
* `sheafSubmoduleComap_submoduleι_le_idealPowerMultiple`: the reverse inclusion
  `ℐ ^ (n + m) 𝓖 ⊆ ℐ ^ m (ℐ ^ n 𝓖)`, read off
  `top_le_sheafSubmoduleComap_idealPowerMultiple`.
* `idealPowerMultiple_idealPowSmul_eq`: the equality `ℐ ^ m (ℐ ^ n 𝓖) = ℐ ^ (n + m) 𝓖`.
* `idealSmul_idealPowSmul_eq`: the case `m = 1`, `ℐ · (ℐ ^ n 𝓖) = ℐ ^ (n + 1) 𝓖`.

## Implementation notes

The two subsheaves live in `ℐ ^ n 𝓖`, not in `𝓖`: `ℐ ^ m (ℐ ^ n 𝓖)` is a subsheaf of `ℐ ^ n 𝓖`
by construction, while `ℐ ^ (n + m) 𝓖` is a subsheaf of `𝓖`, so the equality is stated after
pulling the latter back along the inclusion `ℐ ^ n 𝓖 ⟶ 𝓖`. Pulling back rather than pushing
forward is forced: `SheafOfModules.Submodule` has a preimage
(`AlgebraicGeometry.sheafSubmoduleComap`) and no image, and the inclusion is a monomorphism, so
no information is lost.

The new inclusion is the defining affine-local lower bound of `ℐ ^ m` applied to a module whose
affine sections are known: over an affine open the sections of `ℐ ^ n 𝓖` are `ℐ(U) ^ n Γ(𝓖, U)`
by `Stacks.AlgebraicGeometry.IdealPowerComparison.obj_idealPowerMultiple`, and multiplying by
`ℐ(U) ^ m` gives `ℐ(U) ^ (n + m) Γ(𝓖, U)`, which is the affine sections of `ℐ ^ (n + m) 𝓖`.
This is the same computation as in
`Stacks.AlgebraicGeometry.IdealPowerColimit.val_mem_smul_secs_idealPowerMultiple`, run in the
other direction; what differs is that here the scalar is quantified rather than read off a
section, so the universal property `idealPowerMultiple_le_iff` applies and no affine-local image
is needed.

Scalars on `Γ(𝓖, U)` are declared over `X.ringCatSheaf.obj.obj (op U)`, which instance search
does not recognise as `Γ(X, U)`; `AlgebraicGeometry.secs` and the local instance
`AlgebraicGeometry.sectionsModuleΓSheaf` are the spelling
`StacksFrontier/AlgebraicGeometry/Duality/ExtensionZeroCoherent/IdealPowerIterate.lean` fixed for
that, and they are used here so that the two files' statements compose without a conversion.

Converting the inclusion of
`StacksFrontier/AlgebraicGeometry/Duality/ExtensionZeroCoherent/IdealPowerIterate.lean` from its
"the preimage is everything" shape
to an inclusion of subsheaves of `ℐ ^ n 𝓖` has to build a section of `ℐ ^ (n + m) 𝓖` out of a
section of `ℐ ^ n 𝓖` and a membership proof. Done at the concrete subsheaf that is a kernel
**deterministic timeout**: the anonymous constructor makes the kernel reduce the type
`Γ(ℐ ^ (n + m) 𝓖, U)` to a `Subtype`, which unfolds the infimum defining
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`. The private lemma
`sheafSubmoduleComap_le_of_top_le` therefore keeps both submodules as variables, which is the
same device, for the same reason, as
`AlgebraicGeometry.mem_idealPowerMultiple_of_subInclusion`.

No declaration here carries a `@[stacks]` attribute: this is a comparison internal to the
development between two of its own constructions, in the same way as
`Stacks.Blowup.reesMultiple_eq_idealPowerMultiple`.

The isomorphism `v_* v^* 𝓖 ≅ 𝓖 / ℐ 𝓖` of [Stacks, Tag 0EL1] is not restated here: for an
arbitrary closed immersion `v` with `v.ker = ℐ ^ n` it is
`Stacks.Algebraization.idealQuotientPushforwardIso`, whose case `n = 1` is exactly it.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerComparison

universe u

attribute [local instance] AlgebraicGeometry.sectionsModuleΓSheaf

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

/-- Every section of a module on a scheme lies in its largest subsheaf. -/
private theorem mem_top_toSubmodule_obj {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf}
    (U : (Opens X)ᵒᵖ) (z : M.val.obj U) : z ∈ (⊤ : M.Submodule).toSubmodule.obj U := by
  rw [SheafOfModules.Submodule.toSubmodule_top]
  exact Submodule.mem_top

/-- **The preimage of a subsheaf under an inclusion of subsheaves, read in the ambient module.**
If the preimage of `T ⊆ A'` under the inclusion `A ⟶ A'` is everything, then every section of
`A'` whose value lies in `A` lies in `T`.

The two submodules `A` and `A'` are kept as variables, as in
`AlgebraicGeometry.mem_idealPowerMultiple_of_subInclusion`: at a concrete
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` the anonymous constructor below asks the
kernel to unfold the infimum defining it, and the proof does not terminate. -/
private theorem sheafSubmoduleComap_le_of_top_le {X : Scheme.{u}} {M : X.Modules}
    {A A' : M.Submodule} (hle : A ≤ A') (T : (subMod A').Submodule)
    (h : (⊤ : (subMod A).Submodule) ≤ sheafSubmoduleComap (subInclusion hle) T) :
    sheafSubmoduleComap (submoduleι A') A ≤ T := by
  refine SheafOfModules.Submodule.le_iff.mpr fun U x hx => ?_
  exact SheafOfModules.Submodule.le_iff.mp h U
    (mem_top_toSubmodule_obj U (⟨x.1, hx⟩ : Γ(subMod A, U.unop)))

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n m : ℕ) (G : X.Modules) [G.IsQuasicoherent]

/-- **The affine-local step.** Over an affine open `U`, an element of `ℐ(U) ^ m` carries the
sections of `ℐ ^ n 𝓖` into the sections of `ℐ ^ (n + m) 𝓖`, because both are the corresponding
products (`Stacks.AlgebraicGeometry.IdealPowerComparison.obj_idealPowerMultiple`) and
`ℐ(U) ^ m ℐ(U) ^ n = ℐ(U) ^ (n + m)`. -/
public theorem smul_mem_secs_idealPowerMultiple_add (U : X.affineOpens) {a : Γ(X, U.1)}
    (ha : a ∈ I.ideal U ^ m) {z : Γ(G, U.1)}
    (hz : z ∈ secs (idealPowerMultiple I n G) U.1) :
    a • z ∈ secs (idealPowerMultiple I (n + m) G) U.1 := by
  have hsecs : secs (idealPowerMultiple I n G) U.1 =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1)) := obj_idealPowerMultiple I n G U
  have hsum : secs (idealPowerMultiple I (n + m) G) U.1 =
      I.ideal U ^ (n + m) • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1)) :=
    obj_idealPowerMultiple I (n + m) G U
  have hpow : I.ideal U ^ m • (I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1))) =
      I.ideal U ^ (n + m) • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1)) := by
    rw [← mul_smul, ← pow_add, Nat.add_comm m n]
  rw [hsecs] at hz
  rw [hsum, ← hpow]
  exact Submodule.smul_mem_smul ha hz

/-- **`ℐ ^ m (ℐ ^ n 𝓖)` lands in `ℐ ^ (n + m) 𝓖`.** This is the inclusion
`StacksFrontier/AlgebraicGeometry/Duality/ExtensionZeroCoherent/IdealPowerIterate.lean` left out:
`Stacks.AlgebraicGeometry.IdealPowerColimit.top_le_sheafSubmoduleComap_idealPowerMultiple` is the
other one.

It is the affine-local universal property
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_le_iff` of `ℐ ^ m (ℐ ^ n 𝓖)` applied to
the preimage of `ℐ ^ (n + m) 𝓖`, where the affine-local containment is
`Stacks.AlgebraicGeometry.IdealPowerColimit.smul_mem_secs_idealPowerMultiple_add`. -/
public theorem idealPowerMultiple_le_sheafSubmoduleComap_submoduleι :
    idealPowerMultiple I m (idealPowSmul I n G) ≤
      sheafSubmoduleComap (submoduleι (idealPowerMultiple I n G))
        (idealPowerMultiple I (n + m) G) := by
  rw [idealPowerMultiple_le_iff]
  intro U
  refine Submodule.smul_le.2 fun a ha x _ => ?_
  exact mem_sheafSubmoduleComap _ _ _
    (smul_mem_secs_idealPowerMultiple_add I n m G U ha x.2)

/-- **`ℐ ^ (n + m) 𝓖` lands in `ℐ ^ m (ℐ ^ n 𝓖)`**, read as an inclusion of subsheaves of
`ℐ ^ n 𝓖`. This is
`Stacks.AlgebraicGeometry.IdealPowerColimit.top_le_sheafSubmoduleComap_idealPowerMultiple`: a
section of `ℐ ^ n 𝓖` whose value lies in `ℐ ^ (n + m) 𝓖` *is* a section of `ℐ ^ (n + m) 𝓖`, and
the inclusion `ℐ ^ (n + m) 𝓖 ⟶ ℐ ^ n 𝓖` does not change the value of a section. -/
public theorem sheafSubmoduleComap_submoduleι_le_idealPowerMultiple :
    sheafSubmoduleComap (submoduleι (idealPowerMultiple I n G))
        (idealPowerMultiple I (n + m) G) ≤
      idealPowerMultiple I m (idealPowSmul I n G) :=
  sheafSubmoduleComap_le_of_top_le
    (IdealPower.idealPowerMultiple_antitone I G (Nat.le_add_right n m)) _
    (top_le_sheafSubmoduleComap_idealPowerMultiple I n m G)

/-- **`ℐ ^ m (ℐ ^ n 𝓖) = ℐ ^ (n + m) 𝓖`**, as subsheaves of `ℐ ^ n 𝓖`: the filtration of a member
of the ideal-power filtration is the tail of the filtration of the module itself. -/
public theorem idealPowerMultiple_idealPowSmul_eq :
    idealPowerMultiple I m (idealPowSmul I n G) =
      sheafSubmoduleComap (submoduleι (idealPowerMultiple I n G))
        (idealPowerMultiple I (n + m) G) :=
  le_antisymm (idealPowerMultiple_le_sheafSubmoduleComap_submoduleι I n m G)
    (sheafSubmoduleComap_submoduleι_le_idealPowerMultiple I n m G)

/-- **`ℐ · (ℐ ^ n 𝓖) = ℐ ^ (n + 1) 𝓖`**, as subsheaves of `ℐ ^ n 𝓖`. This is the case `m = 1` of
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerMultiple_idealPowSmul_eq`, the step which
identifies the degree-`n` piece of the associated graded module of the filtration. -/
public theorem idealSmul_idealPowSmul_eq :
    idealPowerMultiple I 1 (idealPowSmul I n G) =
      sheafSubmoduleComap (submoduleι (idealPowerMultiple I n G))
        (idealPowerMultiple I (n + 1) G) :=
  idealPowerMultiple_idealPowSmul_eq I n 1 G

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
