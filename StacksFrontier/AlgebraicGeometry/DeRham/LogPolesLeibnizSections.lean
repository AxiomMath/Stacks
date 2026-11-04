module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelationsKernel
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.FormsInclusion

/-!
# The ideal inclusion on sections, and the identity the Leibniz form needs

Let `f : X ⟶ S` be a morphism of schemes and let `I` cut out a closed subscheme `Y ⊆ X` with
ideal sheaf `ℐ`. `AlgebraicGeometry.SheafOfModules.logLeibnizFormBilin`
(`StacksFrontier/AlgebraicGeometry/DeRham/SheafLogLeibniz.lean`) makes the Leibniz form

`Λ(a, b) = ι a · d(ψ b) − d(ι b) ∧ ψ a`

bilinear for a module `N` of sections with an `𝒪_X(V)`-linear map `ι : N ⟶ 𝒪_X(V)`, given the
identity `ι a · ψ b = ι b · ψ a`. This file supplies `ι` and that identity for `N` the local
sections of `ℐ`, which is the case the de Rham complex of log poles is about.

The identity reduces to `ι a · b = ι b · a` in `ℐ(V)`, that is to `ι` being injective on
sections. The ideal sheaf is a kernel and `Stacks.Divisors.idealInclusion` is that kernel's
inclusion, which is injective on sections over every open set by
`Stacks.SheafOfModules.injective_app_kernel_ι`: evaluation at an object preserves
monomorphisms.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.negativeTwistInclusion`: the ideal inclusion `ℐ(V) ⟶ 𝒪_X(V)` on
  sections, as an `𝒪_X(V)`-linear map. The underlying function is
  `AlgebraicGeometry.Scheme.Hom.negativeTwistSection`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.injective_negativeTwistInclusion`: the ideal inclusion is
  injective on sections.
* `AlgebraicGeometry.Scheme.Hom.negativeTwistInclusion_smul_comm`: `(ι a) · b = (ι b) · a` for
  local sections of the ideal sheaf.
* `AlgebraicGeometry.Scheme.Hom.smul_apply_comm_negativeTwist`: **the hypothesis of
  `AlgebraicGeometry.SheafOfModules.logLeibnizFormBilin`, for the ideal sheaf** —
  `ι a · ψ b = ι b · ψ a` for every `𝒪_X(V)`-linear `ψ` out of `ℐ(V)`.

## Implementation notes

Everything is stated at the ring-sheaf spelling `structureSheafRing X.toRingedSpace`, which is
the one the sections of `Stacks.Divisors.negativeTwist` carry their module structure for. It is
equal to `AlgebraicGeometry.Scheme.ringCatSheaf` by `rfl`, but instance search does not cross:
`Module ↑(X.ringCatSheaf.obj.obj (op V)) ↑((Stacks.Divisors.negativeTwist I).val.obj (op V))`
fails to synthesise while the same statement at `structureSheafRing X.toRingedSpace` succeeds.
This is the device the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/LogPoles/FormsInclusionHom.lean` describe, used for the
same reason.

`AlgebraicGeometry.Scheme.Hom.negativeTwistInclusion` differs from
`AlgebraicGeometry.Scheme.Hom.negativeTwistSection` only in being bundled as a `LinearMap` and
in the spelling of its target, and the two agree by `rfl`: `negativeTwistSection` names the
target `X.ringCatSheaf.obj.obj (op V)`, which is not a spelling the ideal sheaf's own scalars
are found at, so a bundled map with that target cannot be applied to a section of `ℐ`.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The sections of the structure sheaf commute, read at the ring-sheaf spelling. The
`RingCat`-valued `structureSheafRing` carries only a `Ring` instance, so `mul_comm` is not found
on it; the same carrier at the `CommRingCat`-valued `RingedSpace.presheaf` does carry one, and
the two multiplications are the same. -/
private theorem mul_comm_structureSheafRing (V : X.Opens)
    (r s : (structureSheafRing X.toRingedSpace).obj.obj (op V)) : r * s = s * r :=
  mul_comm (show X.toRingedSpace.presheaf.obj (op V) from r)
    (show X.toRingedSpace.presheaf.obj (op V) from s)

/-- **The ideal inclusion on sections, as a linear map.** The inclusion of the sections of the
ideal sheaf over `V` into the sections of the structure sheaf over `V`, linear over the latter;
its underlying function is `AlgebraicGeometry.Scheme.Hom.negativeTwistSection`. -/
def negativeTwistInclusion (V : X.Opens) :
    (Stacks.Divisors.negativeTwist I).val.obj (op V) →ₗ[(structureSheafRing
        X.toRingedSpace).obj.obj (op V)]
      (structureSheafRing X.toRingedSpace).obj.obj (op V) :=
  ((Stacks.Divisors.idealInclusion I).val.app (op V)).hom

/-- The ideal inclusion on sections sends a section `a` of the ideal sheaf over `V` to
`AlgebraicGeometry.Scheme.Hom.negativeTwistSection I V a`. -/
@[simp]
theorem negativeTwistInclusion_apply (V : X.Opens)
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op V)) :
    negativeTwistInclusion I V a = negativeTwistSection I V a := rfl

/-- **The ideal inclusion is injective on sections.** The ideal sheaf is the kernel of
`𝒪_X ⟶ i_*𝒪_Y` and `Stacks.Divisors.idealInclusion` is that kernel's inclusion, which is
injective on sections over every open set. -/
theorem injective_negativeTwistInclusion (V : X.Opens) :
    Function.Injective (negativeTwistInclusion I V) :=
  Stacks.SheafOfModules.injective_app_kernel_ι
    (_root_.SheafOfModules.unitToPushforwardObjUnit
      (RingedSpaceModuleAdjunction.structureSheafHom I.subschemeι.toLRSHom.toShHom)) (op V)

/-- **`(ι a) · b = (ι b) · a` for local sections of the ideal sheaf.** Both sides have the image
`ι a * ι b` under the inclusion, which is injective. -/
theorem negativeTwistInclusion_smul_comm (V : X.Opens)
    (a b : (Stacks.Divisors.negativeTwist I).val.obj (op V)) :
    negativeTwistInclusion I V a • b = negativeTwistInclusion I V b • a :=
  injective_negativeTwistInclusion I V
    (((negativeTwistInclusion I V).map_smul (negativeTwistInclusion I V a) b).trans
      ((mul_comm_structureSheafRing V (negativeTwistInclusion I V a)
          (negativeTwistInclusion I V b)).trans
        ((negativeTwistInclusion I V).map_smul (negativeTwistInclusion I V b) a).symm))

/-- **The hypothesis of `AlgebraicGeometry.SheafOfModules.logLeibnizFormBilin`, for the ideal
sheaf.** For every `𝒪_X(V)`-linear map `ψ` out of the local sections of `ℐ`,
`ι a · ψ b = ι b · ψ a`: both sides are `ψ ((ι a) · b)`, by
`AlgebraicGeometry.Scheme.Hom.negativeTwistInclusion_smul_comm`. This is what makes the Leibniz
form of `ψ` bilinear, and so what makes it a candidate for the value of `Λ_p`. -/
theorem smul_apply_comm_negativeTwist (V : X.Opens) {M : Type u} [AddCommGroup M]
    [Module ((structureSheafRing X.toRingedSpace).obj.obj (op V)) M]
    (ψ : (Stacks.Divisors.negativeTwist I).val.obj (op V) →ₗ[(structureSheafRing
        X.toRingedSpace).obj.obj (op V)] M)
    (a b : (Stacks.Divisors.negativeTwist I).val.obj (op V)) :
    negativeTwistInclusion I V a • ψ b = negativeTwistInclusion I V b • ψ a :=
  ((ψ.map_smul (negativeTwistInclusion I V a) b).symm.trans
    (congrArg ψ (negativeTwistInclusion_smul_comm I V a b))).trans
    (ψ.map_smul (negativeTwistInclusion I V b) a)

end AlgebraicGeometry.Scheme.Hom
