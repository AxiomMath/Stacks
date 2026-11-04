module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# The base algebra structure on a homogeneous localization

Let `A` be a graded algebra over a commutative ring `R`, with grading `𝒜 : ι → Submodule R A`,
and let `x` be a submonoid of `A`. Mathlib makes the homogeneous localization
`HomogeneousLocalization 𝒜 x` an algebra over the degree-zero part `𝒜 0`, via
`HomogeneousLocalization.fromZeroRingHom`, and gives it a bare `R`-action, but no `Module R` or
`Algebra R` structure. This file supplies them, so that a homogeneous localization can be base
changed along a map of base rings.

## Main definitions

* `HomogeneousLocalization.instAlgebra` is the `R`-algebra structure on
  `HomogeneousLocalization 𝒜 x`, and hence also its `R`-module structure.

## Main results

* `HomogeneousLocalization.algebraMap_eq_fromZeroRingHom_comp`: the structure map is the
  composite `R → 𝒜 0 → HomogeneousLocalization 𝒜 x`, so the `R`-algebra structure is the one
  induced by the `𝒜 0`-algebra structure; nothing new is being chosen.
* `HomogeneousLocalization.val_algebraMap`: the structure map is compatible with the embedding
  into the ordinary localization; `HomogeneousLocalization.isScalarTower_localization` is the
  same statement as a tower.

## Implementation notes

The structure map is the composite `R → 𝒜 0 → HomogeneousLocalization 𝒜 x`, written out as such
rather than obtained from a module structure, so that `algebraMap` has exactly the definitional
behaviour of that composite.

The scalar action, on the other hand, is taken to be *definitionally* Mathlib's existing
`HomogeneousLocalization.instSMul` — the action on numerators, available for any `α` acting on
`A` whose action preserves the grading — and not the action `r • z = algebraMap r * z` that
`RingHom.toAlgebra` would manufacture. This matters: those two are not definitionally equal, so
an `Algebra R (HomogeneousLocalization 𝒜 x)` built by `RingHom.toAlgebra` puts a second,
non-definitionally-equal `SMul R (HomogeneousLocalization 𝒜 x)` in the instance graph alongside
Mathlib's, and then Mathlib's `HomogeneousLocalization.val_smul` and
`HomogeneousLocalization.mk_smul` no longer apply to the action that instance search finds.
`HomogeneousLocalization.instAlgebra` supplies `SMul` explicitly and discharges `smul_def'` as a
theorem instead. It sets the parent field `toSMul` to `HomogeneousLocalization.instSMul x`
itself, not to a structure `⟨fun r z ↦ r • z⟩` wrapping it: the wrapper is equal to
`instSMul x` only at default transparency, so `rw [Algebra.smul_def]`, which matches instances
reducibly, would not find the `•` that elaboration produces.

The grading is taken to be a family of `R`-submodules rather than an arbitrary `SetLike` family,
because that is exactly the hypothesis under which the degree-zero part is an `R`-algebra
(`SetLike.GradeZero.instAlgebra`) and under which the grading is stable under the `R`-action, so
that Mathlib's `HomogeneousLocalization.instSMul` applies.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

namespace HomogeneousLocalization

universe u v w

variable {ι : Type u} {R : Type v} {A : Type w} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommMonoid ι] [DecidableEq ι] {𝒜 : ι → Submodule R A} [GradedRing 𝒜] (x : Submonoid A)

variable {x} in
/-- A degree-zero element is the fraction with that numerator and denominator `1`. -/
@[simp]
public theorem val_fromZeroRingHom (f : 𝒜 0) :
    (fromZeroRingHom 𝒜 x f).val = Localization.mk (f : A) 1 := rfl

/-- The `R`-algebra structure on a homogeneous localization of a graded `R`-algebra: the
structure map is the composite `R → 𝒜 0 → HomogeneousLocalization 𝒜 x`, while the scalar action
is Mathlib's `HomogeneousLocalization.instSMul` — the action on numerators — definitionally. -/
public instance instAlgebra : Algebra R (HomogeneousLocalization 𝒜 x) where
  toSMul := instSMul x
  algebraMap := (fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0))
  commutes' _ _ := mul_comm _ _
  smul_def' r z := val_injective x <| by
    have h : (((fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0))) r).val =
        algebraMap R (Localization x) r := by
      rw [RingHom.comp_apply, val_fromZeroRingHom, SetLike.GradeZero.coe_algebraMap,
        Localization.mk_one_eq_algebraMap, ← IsScalarTower.algebraMap_apply R A (Localization x)]
    rw [val_mul, h, ← Algebra.smul_def]
    exact val_smul x r z

/-- **The `R`-algebra structure is the one induced from the degree-zero part.** The structure map
is the composite of the structure map `R → 𝒜 0` of the graded algebra with the canonical map
`𝒜 0 → HomogeneousLocalization 𝒜 x`, `g ↦ g / 1`. -/
public theorem algebraMap_eq_fromZeroRingHom_comp :
    algebraMap R (HomogeneousLocalization 𝒜 x) =
      (fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0)) := rfl

/-- The structure map of a homogeneous localization is compatible with the embedding into the
ordinary localization. -/
@[simp]
public theorem val_algebraMap (r : R) :
    (algebraMap R (HomogeneousLocalization 𝒜 x) r).val = algebraMap R (Localization x) r := by
  rw [algebraMap_eq_fromZeroRingHom_comp, RingHom.comp_apply, val_fromZeroRingHom,
    SetLike.GradeZero.coe_algebraMap, Localization.mk_one_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply R A (Localization x)]

/-- The tower `R → HomogeneousLocalization 𝒜 x → Localization x`.

Deliberately **not** an instance: `Stacks.ProjStandardOpenBaseChange.instModuleTwistAway` gives a
submodule of `Localization x` over `HomogeneousLocalization 𝒜 x` its `R`-module structure by
`Module.compHom`, and making this a global instance puts `Submodule.smul` — the restriction of
the `R`-action on `Localization x`, which needs exactly this tower — on the same submodule by a
second path. The two actions agree but not definitionally, and the ambient `R`-action wins
instance search. Supply it with `letI` where it is wanted, or delete that `Module.compHom`
instance in favour of the canonical one and promote this. -/
public theorem isScalarTower_localization :
    IsScalarTower R (HomogeneousLocalization 𝒜 x) (Localization x) where
  smul_assoc r z w := by
    change (r • z).val * w = r • (z.val * w)
    rw [val_smul, smul_mul_assoc]

end HomogeneousLocalization

end
