module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.DegreeOneFree
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.SectionsAlgebra

/-!
# The coefficient extension of the chart comparison on a degree-one chart

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of graded rings and `f ∈ 𝒜 1` homogeneous of degree one.
`Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroMap` is the algebraic form of
`Γ(D₊(f), θ n)`, the map

`𝒜(n)₍f₎ ⟶ ℬ(n)₍ψ f₎`,  `m / f ^ k ↦ ψ m / (ψ f) ^ k`,

semilinear over the chart ring homomorphism `HomogeneousLocalization.Away.map ψ f`. The criterion
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_of_isIso_extension` does not consume
that map but an **extension of scalars** of it, a `ℬ₍ψ f₎`-linear map out of
`ℬ₍ψ f₎ ⊗_{𝒜₍f₎} 𝒜(n)₍f₎`, and asks for that to be invertible. This file proves it is, for `f` of
degree one.

The reason is that both sides are free of rank one — `𝒜(n)₍f₎` on `f ^ n` and `ℬ(n)₍ψ f₎` on
`(ψ f) ^ n`, by
`Stacks.AlgebraicGeometry.TwistChartDegreeOne.twistDegreeZeroBasis` — and the map carries the one
generator to the other. An extension of scalars of a rank-one free module is free of rank one on
the base-changed generator, so any `ℬ₍ψ f₎`-linear map taking that generator to a generator is an
isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.TwistChartDegreeOne.bijective_of_basis_unit`: **the abstract step.**
  A `Q`-linear map `Q ⊗_P M ⟶ N` carrying `1 ⊗ₜ b` to `c`, for `b` a one-element `P`-basis of `M`
  and `c` a one-element `Q`-basis of `N`, is bijective. Nothing graded, and no compatibility of
  the algebra structure with anything, is needed: a basis is carried to a basis.
* `Stacks.AlgebraicGeometry.TwistChartDegreeOne.twistDegreeZeroMap_twistGen`: **the comparison
  carries the generator to the generator**, which is
  `Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroMap_degreeZeroFraction` read at the
  fraction that the generator is.
* `Stacks.AlgebraicGeometry.TwistChartDegreeOne.isIso_of_tmul_eq_twistDegreeZeroMap`: **the
  coefficient extension is invertible.** Any morphism of
  `ModuleCat (HomogeneousLocalization.Away ℬ (ψ f))` out of the extension of scalars of
  `𝒜(n)₍f₎` whose value on `1 ⊗ₜ z` is `twistDegreeZeroMap z` is an isomorphism.

## What this does not prove

**No project tag attribute is attached here.** This is one input to the chart-local statement of
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/AwayChart.lean`. Of the steps that file records,
the transpose identification is discharged in
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartTranspose.lean`, the quasi-coherence in
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartQcoh.lean`, and the identification of the
chart sections of the twisting sheaf with `𝒜(n)₍f₎` — and hence of the global sections of that
transpose with the map below — in
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartGamma.lean`, which assembles the three and
proves the twist transport for the polynomial grading — weaker than Tag 01N2's twist assertion,
which is not proved.

The degree-one hypothesis is **not** removable: see the discussion in
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/DegreeOneFree.lean`, where a homogeneous `f` of
degree two with `𝒜(1)₍f₎` not free is exhibited. Consequently the hypothesis of
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison_of_forall_restrict`, which
quantifies over every homogeneous `f` of positive degree, cannot be discharged by the argument
below; what is used instead is
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_of_isIso_pullback_awayι`, whose cover is
indexed by the degree-one elements alone.

## Implementation notes

The statement is phrased with the extension of scalars as `CategoryTheory.Functor.obj` of
`ModuleCat.extendScalars`, and with the value on pure tensors as a hypothesis rather than the
extension being constructed, exactly as
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_of_isIso_extension` consumes it.

`ModuleCat.extendScalars` builds its tensor product over the `Module` structure coming from
`ModuleCat.restrictScalars`, while `Module.Basis.baseChange` builds its basis over an `Algebra`
structure. The two agree definitionally but not syntactically, so the abstract step is stated for
an arbitrary `Algebra P Q` — which makes it `Module.Basis.baseChange`'s own setting — and the
`Algebra` instance coming from the ring homomorphism is introduced only inside the proof of the
graded statement, where the two spellings are reconciled by unification rather than by a rewrite.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open CategoryTheory HomogeneousLocalization AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistChain Stacks.AlgebraicGeometry.TwistChartLocality
open scoped ChangeOfRings TensorProduct

namespace Stacks.AlgebraicGeometry.TwistChartDegreeOne

/-! ### The abstract step -/

section Abstract

universe u₁ u₂ u₃ u₄

variable {P : Type u₁} {Q : Type u₂} {M : Type u₃} {N : Type u₄}
  [CommRing P] [CommRing Q] [Algebra P Q]
  [AddCommGroup M] [Module P M] [AddCommGroup N] [Module Q N]

/-- **A map out of an extension of scalars carrying a one-element basis to a one-element basis is
bijective.** The base change of a `P`-basis of `M` is a `Q`-basis of `Q ⊗_P M`
(`Module.Basis.baseChange`), consisting of the pure tensors `1 ⊗ₜ b i`; a `Q`-linear map agreeing
on that basis with the isomorphism the two bases determine is that isomorphism. -/
public theorem bijective_of_basis_unit (bM : Module.Basis Unit P M)
    (bN : Module.Basis Unit Q N) (e : TensorProduct P Q M →ₗ[Q] N)
    (he : e ((1 : Q) ⊗ₜ[P] bM ()) = bN ()) :
    Function.Bijective e := by
  have hb : ((bM.baseChange Q).equiv bN (Equiv.refl Unit)).toLinearMap = e := by
    refine (bM.baseChange Q).ext fun i => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply,
      Module.Basis.baseChange_apply]
    cases i
    exact he.symm
  rw [← hb]
  exact ((bM.baseChange Q).equiv bN (Equiv.refl Unit)).bijective

end Abstract

/-! ### The comparison on the generators -/

section Graded

universe u v v'

variable {A B : Type u} {R : Type v} {R' : Type v'}
  [CommRing A] [CommRing B] [CommRing R] [CommRing R'] [Algebra R A] [Algebra R' B]
  (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R' B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {f : A}

/-- **The chart comparison carries the generator to the generator.** The generator of the `t`-th
twist on the chart of `f` is the fraction `f ^ a / f ^ b` with `a - b = t`, and
`Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroMap` applies `ψ` to the numerator and
to the denominator, giving `(ψ f) ^ a / (ψ f) ^ b`, which is the generator at `ψ f`. -/
public theorem twistDegreeZeroMap_twistGen (ψ : 𝒜 →+*ᵍ ℬ) (hf : f ∈ 𝒜 1) (t : ℤ) :
    twistDegreeZeroMap 𝒜 ℬ ψ f t (twistGen 𝒜 hf t) =
      twistGen ℬ (mem_of_mem 𝒜 ℬ ψ hf) t := by
  rw [twistGen, twistGen, twistDegreeZeroMap_degreeZeroFraction]
  exact Subtype.ext (congrArg
    (fun x => LocalizedModule.mk x (⟨(ψ f) ^ denExp t, ⟨denExp t, rfl⟩⟩ :
      Submonoid.powers (ψ f))) (map_pow ψ f (numExp t)))

/-- **The coefficient extension of the chart comparison is invertible**, for `f` homogeneous of
degree one.

Both chart modules are free of rank one, on the generators `f ^ t` and `(ψ f) ^ t`
(`Stacks.AlgebraicGeometry.TwistChartDegreeOne.twistDegreeZeroBasis`), and the comparison carries
the one to the other, so a `ℬ₍ψ f₎`-linear map out of `ℬ₍ψ f₎ ⊗_{𝒜₍f₎} 𝒜(t)₍f₎` extending it
carries a basis to a basis.

This is the input that
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_of_isIso_extension` asks for, in the
shape it asks for it: the extension is a hypothesis, specified by its values on the pure tensors,
rather than constructed. -/
public theorem isIso_of_tmul_eq_twistDegreeZeroMap (ψ : 𝒜 →+*ᵍ ℬ) (hf : f ∈ 𝒜 1) (t : ℤ)
    (e : (ModuleCat.extendScalars (Away.map ψ f)).obj
          (ModuleCat.of (Away 𝒜 f)
            (GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 t) f)) ⟶
        ModuleCat.of (Away ℬ (ψ f))
          (GradedModuleDegreeZeroLocalization ℬ (twistGrading (S := B) ℬ t) (ψ f)))
    (he : ∀ z : GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 t) f,
      e ((1 : Away ℬ (ψ f)) ⊗ₜ[Away 𝒜 f, Away.map ψ f] z) =
        twistDegreeZeroMap 𝒜 ℬ ψ f t z) :
    IsIso e := by
  let _ : Algebra (Away 𝒜 f) (Away ℬ (ψ f)) := (Away.map ψ f).toAlgebra
  refine (ConcreteCategory.isIso_iff_bijective e).mpr ?_
  refine bijective_of_basis_unit (twistDegreeZeroBasis 𝒜 hf t)
    (twistDegreeZeroBasis ℬ (mem_of_mem 𝒜 ℬ ψ hf) t) (ModuleCat.Hom.hom e) ?_
  rw [twistDegreeZeroBasis_apply, twistDegreeZeroBasis_apply]
  exact (he _).trans (twistDegreeZeroMap_twistGen 𝒜 ℬ ψ hf t)

end Graded

end Stacks.AlgebraicGeometry.TwistChartDegreeOne

end
