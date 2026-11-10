module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequenceMultiplication
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafGradedPieceQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistFamily
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence

/-!
# The multiplication of restricted ideal sheaves on an exceptional curve, through the unit

Let `D` be an effective Cartier divisor on a scheme `X`, let `i : E ⟶ X` be the closed immersion
it cuts out, and write

* `ℐ_{Dᵈ} = Stacks.Divisors.negativeTwist (D ^ d)` for the ideal sheaves of the powers of `D`,
  assembled into `Stacks.Divisors.negativeTwistPowerSystem D`, whose successor comparison is the
  canonical multiplication `Stacks.Divisors.idealTensorMul`;
* `i^*ℐ_{Dᵈ}` for the same sheaves restricted to `E`, assembled into
  `Stacks.PullbackSheafTensor.pullbackPowerSystem` of that system — the `E`-side of
  `AlgebraicGeometry.Scheme.IdealSheafData.curvePowerSystem`, whose successor comparison is the
  comparison of [Stacks, Tag 01CD] followed by `i^*` of the multiplication;
* `K_d = Stacks.Divisors.thickeningKernelMap D d : i_* i^* ℐ_{Dᵈ⁺¹} ⟶ 𝒪_{Dᵈ⁺²}` for the kernel
  inclusion of [Stacks, Tag 0C4T] at the thickenings.

This file links the two multiplications through the unit `η` of `i^* ⊣ i_*`:

`η_{ℐ_{Dᵈ} ⊗ ℐ_D} ≫ i_*(comparison ≫ succIso) = succIso ≫ η_{ℐ_{Dᵈ⁺¹}}`,

and supplies the affine-local surjectivity of `η` that passing this to sections needs.

## Why this is the shape of the step, and what is still missing

The multiplicativity of the symbol of
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.formalNeighborhoodSymbol`
in bidegree `(d, 1)` — the one bidegree a monomial induction consumes, and the whole remaining
content of [Stacks, Tag 0C2K] — factors into two halves:

* the **`X`-side half**, carried here and in
  `StacksFrontier/AlgebraicGeometry/Divisors/EffectiveCartier/SumSequenceMultiplication.lean`:
  the `E`-side multiplication `i^*ℐ_{Dᵈ} ⊗ i^*ℐ_D ⟶ i^*ℐ_{Dᵈ⁺¹}`, followed by `K_d`, is
  multiplication of functions on the thickening;
* the **`𝐏¹`-side half**: `AlgebraicGeometry.Scheme.IdealSheafData`
  `.IsExceptionalCurveOfFirstKind.curveSections` of that multiplication is the product of forms.

The first is reachable by covering `X` by affine opens and gluing, because over an affine open the
unit *is* surjective on sections — `Stacks.Divisors.surjective_unit_app_negativeTwist` below,
which is the ingredient the implementation notes of
`StacksFrontier/AlgebraicGeometry/Divisors/EffectiveCartier/SumSequenceMultiplication.lean`
call for,
and which is a two-line consequence of
`Stacks.ClosedImmersion.epi_unit_app`,
`Stacks.Divisors.isQuasicoherent_pushforward_pullback_negativeTwist` and
`Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen`. Both quasi-coherence instances need
bridging by an explicit application: instance search does not cross the `𝟭 X.Modules` of the unit's
source nor the functor composition of its target, and reports `synthInstanceFailed` on each.

The second is **not** reachable with what the tree has, and that is the gap this file does not
close. `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.curveTwistIso_tensorHom_comp_succIso` and
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveTwistIso_mul` are
equalities of *morphisms*, and
`AlgebraicGeometry.Scheme.IdealSheafData.mulSection_gradedPieceFormEquiv` is the multiplicativity
of the identification of forms with `H⁰(𝐏¹_k, 𝒪(d))` — but it is stated against
`Stacks.AlgebraicGeometry.TwistTensor.mulSection`, not against
`AlgebraicGeometry.projectiveLineTwistPowerSystem`'s `succIso`, and no declaration anywhere
evaluates any `Stacks.Monoidal.PowerSystem.mulIso` or `succIso` on `curveSections` or on
`Stacks.Cohomology.sectionsFunctor`. The four clauses
`curveSections_add`, `curveSections_zero`, `curveSections_bijective` and `curveSections_smul` are
the only facts about `curveSections`, and each is about a single degree.

## Implementation notes

Every step below is a term, and every repeated `rfl` identity has its own name. Both are forced,
and the two failures are worth recording because each looks like a fixable syntax error and is not:

* `rw` cannot be used across the two spellings of the module category. The power system is typed at
  `SheafOfModules (structureSheafRing _)` and `Stacks.Divisors.thickeningKernelMap` at
  `AlgebraicGeometry.Scheme.Modules`; the two are definitionally equal, so composites elaborate,
  but a rewrite whose motive crosses them is not type-correct at `implicit` transparency and fails
  with an application type mismatch naming `negativeTwist (D ^ d)` at one index and the other.
  `congrArg` with an explicitly written function does cross it. The same is recorded for the same
  reason in the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Divisors/EffectiveCartier/SumSequenceMultiplication.lean`.
* Reassociating *after* crossing to sections exhausts the kernel. Evaluating the composite below on
  a local pure tensor and matching it against
  `Stacks.Divisors.app_idealTensorMul_comp_unit_comp_thickeningKernelMap_tmul_mul` by definitional
  unfolding — the association differs, and `Stacks.Divisors.thickeningKernelMap` is a
  `CategoryTheory.Limits.kernel.lift` over a sheafification — is a `(kernel) deterministic
  timeout`.
  `unit_comp_pushforward_comparison_comp_succIso_comp_thickeningKernelMap` therefore does
  the reassociation at the level of morphisms, where it is two applications of
  `CategoryTheory.Category.assoc`, and is stated in exactly the association that lemma consumes, so
  a consumer needs one `congrArg` and no unfolding.

Nothing here carries a `@[stacks]` attribute: this is one step of the proof of [Stacks, Tag 0C2K].

## Main results

* `Stacks.Divisors.comparison_comp_pullbackPowerSystem_succIso` — the comparison of
  [Stacks, Tag 01CD] undoes the first factor of the pulled-back successor comparison.
* `Stacks.Divisors.unit_comp_pushforward_comparison_comp_succIso` — **the unit of `i^* ⊣ i_*`
  carries the multiplication of ideal sheaves on `X` to the multiplication of their restrictions
  to `E`**, and its restatement composed with the kernel inclusion,
  `unit_comp_pushforward_comparison_comp_succIso_comp_thickeningKernelMap`.
* `Stacks.Divisors.surjective_unit_app_negativeTwist` — **the unit is surjective on the sections
  over an affine open**, which is what makes the gluing of the `X`-side half possible.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open RingedSpaceModuleAdjunction (modulePullbackPushforwardAdjunction modulePushforward)
open Stacks.PullbackSheafTensor (pullbackPowerSystem sheafTensorComparisonIso)
open Stacks.RingedSpace (pullbackFunctor)

universe u

attribute [local instance] Stacks.PullbackSheafTensor.monoidalModules

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] (d : ℕ)

/-- The successor comparison of the system of negative twists is the canonical multiplication
of ideal sheaves, followed by the transport along `Dᵈ · D = Dᵈ⁺¹`.

This is `Stacks.Divisors.negativeTwistPowerSystem_succIso` read on the underlying morphism. It
carries its own name because the identity is used twice and each definitional unfolding of it
inside a larger term is paid for again. -/
public theorem negativeTwistPowerSystem_succIso_hom :
    ((negativeTwistPowerSystem D).succIso d).hom =
      idealTensorMul (D ^ d) D ≫
        eqToHom (congrArg negativeTwist (pow_succ D d).symm) := rfl

/-- **The comparison of [Stacks, Tag 01CD] undoes the first factor of the pulled-back system's
successor comparison.** The successor comparison of a pulled-back power system is the inverse of
that comparison followed by `i^*` of the old successor comparison, so composing with the
comparison leaves `i^*` of the multiplication of ideal sheaves. -/
public theorem comparison_comp_pullbackPowerSystem_succIso :
    (sheafTensorComparisonIso D.subschemeι.toLRSHom.toShHom
          ((negativeTwistPowerSystem D).obj d) (negativeTwistPowerSystem D).gen).hom ≫
        ((pullbackPowerSystem D.subschemeι.toLRSHom.toShHom
          (negativeTwistPowerSystem D)).succIso d).hom =
      (pullbackFunctor D.subschemeι.toLRSHom.toShHom).map
        ((negativeTwistPowerSystem D).succIso d).hom := by
  rw [Stacks.PullbackSheafTensor.pullbackPowerSystem_succIso]
  simp only [Iso.trans_hom, Iso.symm_hom]
  exact Iso.hom_inv_id_assoc _ _

/-- **The unit of `i^* ⊣ i_*` carries the multiplication of ideal sheaves on `X` to the
multiplication of their restrictions to `E`.**

Multiplying two ideal sheaves on `X` and then restricting to `E` is restricting both factors,
comparing with [Stacks, Tag 01CD] and multiplying on `E`. This is naturality of the unit at the
multiplication `Stacks.Divisors.idealTensorMul`, read through
`comparison_comp_pullbackPowerSystem_succIso`; it holds for an arbitrary morphism of ringed
spaces and uses nothing about the closed immersion. -/
public theorem unit_comp_pushforward_comparison_comp_succIso :
    (modulePullbackPushforwardAdjunction D.subschemeι.toLRSHom.toShHom).unit.app
          (MonoidalCategoryStruct.tensorObj ((negativeTwistPowerSystem D).obj d)
            (negativeTwistPowerSystem D).gen) ≫
        (modulePushforward D.subschemeι.toLRSHom.toShHom).map
          ((sheafTensorComparisonIso D.subschemeι.toLRSHom.toShHom
                ((negativeTwistPowerSystem D).obj d) (negativeTwistPowerSystem D).gen).hom ≫
            ((pullbackPowerSystem D.subschemeι.toLRSHom.toShHom
              (negativeTwistPowerSystem D)).succIso d).hom) =
      ((negativeTwistPowerSystem D).succIso d).hom ≫
        (modulePullbackPushforwardAdjunction D.subschemeι.toLRSHom.toShHom).unit.app
          ((negativeTwistPowerSystem D).obj (d + 1)) :=
  (congrArg (fun φ => (modulePullbackPushforwardAdjunction
          D.subschemeι.toLRSHom.toShHom).unit.app
        (MonoidalCategoryStruct.tensorObj ((negativeTwistPowerSystem D).obj d)
          (negativeTwistPowerSystem D).gen) ≫
      (modulePushforward D.subschemeι.toLRSHom.toShHom).map φ)
    (comparison_comp_pullbackPowerSystem_succIso D d)).trans
  ((modulePullbackPushforwardAdjunction
    D.subschemeι.toLRSHom.toShHom).unit.naturality _).symm

/-- **The same square, composed with the kernel inclusion of [Stacks, Tag 0C4T]**, and
reassociated to the association that
`Stacks.Divisors.app_idealTensorMul_comp_unit_comp_thickeningKernelMap_tmul_mul` is stated at.

A consumer evaluating this on a local pure tensor needs one `congrArg` and no definitional
unfolding; see the implementation notes on why the reassociation must happen here, before the
crossing to sections, and not after it. -/
public theorem unit_comp_pushforward_comparison_comp_succIso_comp_thickeningKernelMap :
    ((modulePullbackPushforwardAdjunction D.subschemeι.toLRSHom.toShHom).unit.app
            (MonoidalCategoryStruct.tensorObj ((negativeTwistPowerSystem D).obj d)
              (negativeTwistPowerSystem D).gen) ≫
          (modulePushforward D.subschemeι.toLRSHom.toShHom).map
            ((sheafTensorComparisonIso D.subschemeι.toLRSHom.toShHom
                  ((negativeTwistPowerSystem D).obj d) (negativeTwistPowerSystem D).gen).hom ≫
              ((pullbackPowerSystem D.subschemeι.toLRSHom.toShHom
                (negativeTwistPowerSystem D)).succIso d).hom)) ≫
        thickeningKernelMap D d =
      idealTensorMul (D ^ d) D ≫ eqToHom (congrArg negativeTwist (pow_succ D d).symm) ≫
        ((modulePullbackPushforwardAdjunction D.subschemeι.toLRSHom.toShHom).unit.app
          (negativeTwist (D ^ (d + 1))) ≫ thickeningKernelMap D d) :=
  (congrArg (fun φ => φ ≫ thickeningKernelMap D d)
      ((unit_comp_pushforward_comparison_comp_succIso D d).trans
        (congrArg (fun ψ => ψ ≫ (modulePullbackPushforwardAdjunction
            D.subschemeι.toLRSHom.toShHom).unit.app (negativeTwist (D ^ (d + 1))))
          (negativeTwistPowerSystem_succIso_hom D d)))).trans
    ((Category.assoc _ _ _).trans (Category.assoc _ _ _))

omit [IsEffectiveCartierDivisor D] in
/-- **The unit of `i^* ⊣ i_*` at a twisted ideal sheaf is surjective on the sections over an
affine open.**

The unit is an epimorphism of sheaves of modules at every module along a closed immersion
(`Stacks.ClosedImmersion.epi_unit_app`), and an epimorphism of quasi-coherent modules is a
surjection on the sections over an affine open
(`Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen`). Both ends are quasi-coherent:
the source by `Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf` and the
target by `Stacks.Divisors.isQuasicoherent_pushforward_pullback_negativeTwist`, neither needing a
hypothesis on either ideal sheaf. Each has to be supplied as an explicit application: instance
search does not unfold the `𝟭 X.Modules` of the unit's source nor the functor composition of its
target to reach the index these instances are stated at.

This is what makes the `X`-side half of one-step multiplicativity local: on global sections the
unit is not surjective — that would need `H¹(X, ℐ_{Dᵈ⁺²})` to vanish — but every identity it is
used to prove is an identity of sheaf sections, hence checkable on an affine cover. -/
public theorem surjective_unit_app_negativeTwist (E : X.IdealSheafData) (U : X.affineOpens) :
    Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction D.subschemeι).unit.app
        (negativeTwist E)).app U.1) := by
  have hsrc : SheafOfModules.IsQuasicoherent ((𝟭 X.Modules).obj (negativeTwist E)) :=
    Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf E.subschemeι
  have htgt : SheafOfModules.IsQuasicoherent
      ((Scheme.Modules.pullback D.subschemeι ⋙
        Scheme.Modules.pushforward D.subschemeι).obj (negativeTwist E)) :=
    isQuasicoherent_pushforward_pullback_negativeTwist D E
  have := Stacks.ClosedImmersion.epi_unit_app D.subschemeι (negativeTwist E)
  exact Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen _ U

end Stacks.Divisors

end
