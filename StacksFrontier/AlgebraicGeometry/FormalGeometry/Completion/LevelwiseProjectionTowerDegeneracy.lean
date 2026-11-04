module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.CohomologyAdicCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent

/-!
# The adic quotient tower degenerates at its first index

Let `X` be a scheme, `𝓘 ⊂ 𝒪_X` a quasi-coherent sheaf of ideals and `ℱ` an `𝒪_X`-module. The
tower `Stacks.Algebraization.adicQuotientSystem 𝓘 ℱ` of quotients of `ℱ` by the powers of `𝓘`
is indexed so that its term at `n` is `ℱ/𝓘ⁿℱ`; at `n = 0` the exponent is `0`, the subsheaf
`𝓘⁰ℱ` is all of `ℱ`, and the term is therefore **zero**. This file records that, and the one
consequence of it that matters.

## Why this is worth a file

A levelwise comparison of that tower with the ideal-power tower of the base ring — the shape

`RΓ(X, ℱ/𝓘ⁿℱ) ≅ RΓ(X, ℱ) ⊗^𝐋_A A/Iⁿ⁺¹`, as an isomorphism of `ℕᵒᵖ`-towers in `D(A)`,

which is the geometric half of the projection formula [Stacks, Tag 0944] and the shape a
reduction of [Stacks, Tag 0A0M] to a single input would naturally take — **cannot hold**. The
two towers are not indexed compatibly: `NoetherianAdicCompletion.idealPowerQuotientSystem I`
has `A/Iⁿ⁺¹` at index `n`, so its term at `n = 0` is `A/I`, whereas the term of
`adicQuotientSystem 𝓘 ℱ` at `n = 0` is zero. Such an isomorphism therefore forces
`RΓ(X, ℱ) ⊗^𝐋_A A/I` to vanish, which it does not: for `X = Spec A` and `ℱ = 𝒪_X` it is
`A/I`, nonzero for every proper `I`.

`Stacks.Algebraization.isZero_derivedTensor_idealPowerQuotient_zero_of_iso_adicQuotientTower`
is that implication. It is stated so that it applies verbatim to the hypothesis of
`Stacks.Algebraization.exists_shortExact_adicCompletion_cohomology_of_isDerivedLimit` of
`DerivedCompletionRinged/FiniteTypeIdealPending099E.lean`, whose input `hproj` is exactly this
shape: that theorem is sound, but its hypothesis is unsatisfiable whenever
`RΓ(X, ℱ) ⊗^𝐋_A A/I ≠ 0`, so it does not reduce [Stacks, Tag 0A0M] to anything.

The off-by-one is not the only obstruction, and aligning the indices does not repair the shape.
With the exponents matched, `RΓ(X, ℱ/𝓘ⁿℱ) ≅ RΓ(X, ℱ) ⊗^𝐋_A A/Iⁿ` still fails: for `A = ℤ`,
`I = (p)`, `X = Spec 𝔽ₚ` and `ℱ = 𝒪_X` the ideal sheaf `𝓘 = I𝒪_X` is zero, so the left hand
side is `𝔽ₚ` in degree `0`, while the right hand side is `𝔽ₚ ⊗^𝐋_ℤ ℤ/pⁿ`, which also has
`Tor₁(𝔽ₚ, ℤ/pⁿ) = 𝔽ₚ` in degree `-1`. What is true of those two towers is only that they are
*pro*-isomorphic — the `Tor` terms die in the limit, not at any finite level — and that is the
content of [Stacks, Tag 0A0K] part (1) together with the projection formula for the Koszul
complexes, neither of which this library has at an ideal with more than one generator. So the
right form of the missing input is a map of towers with eventual inverses in the sense of
`NoetherianAdicCompletion.HasEventualInverses`, not a natural isomorphism.

## Main results

* `Stacks.Algebraization.isZero_adicQuotientSystem_zero`: `ℱ/𝓘⁰ℱ = 0`.
* `Stacks.Algebraization.isZero_derivedGlobalSections_adicQuotientSystem_zero`: so the tower of
  derived global sections of the adic quotients vanishes at index `0` too.
* `Stacks.Algebraization.isZero_derivedTensor_idealPowerQuotient_zero_of_iso_adicQuotientTower`:
  a levelwise isomorphism of that tower with `n ↦ RΓ(X, ℱ) ⊗^𝐋_A A/Iⁿ⁺¹` forces
  `RΓ(X, ℱ) ⊗^𝐋_A A/I` to be zero.

## Implementation notes

`𝓘⁰ℱ = ℱ` is read off the definition of `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`
as the least subsheaf containing `𝓘(U)ⁿ · ℱ(U)` on every affine open `U`: at `n = 0` that lower
bound is all of `ℱ(U)`, and membership in a subsheaf is affine-local
(`Stacks.Algebraization.mem_submodule_of_affine`), so the subsheaf is the top one. Quotienting
by the top subsheaf gives zero because its inclusion is an isomorphism
(`AlgebraicGeometry.sheafTopIso`).

No tag is claimed here. These are statements about the indexing of a tower, not about any part
of a source result.

## References

* [Stacks Project, Tag 0A0M](https://stacks.math.columbia.edu/tag/0A0M)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

attribute [local instance 10000] Stacks.Algebraization.modulesHasDerivedCategory

universe u

namespace Stacks.Algebraization

/-- **The adic quotient tower is zero at index `0`.** The term of
`Stacks.Algebraization.adicQuotientSystem 𝓘 ℱ` at `n` is `ℱ/𝓘ⁿℱ`, and `𝓘⁰ℱ` is all of `ℱ`. -/
public theorem isZero_adicQuotientSystem_zero {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) :
    IsZero ((adicQuotientSystem I F).obj ⟨0⟩) := by
  have hmem : ∀ (U : (TopologicalSpace.Opens X)ᵒᵖ) (s : F.val.obj U),
      s ∈ (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I 0
        F).toSubmodule.obj U := by
    intro U s
    refine mem_submodule_of_affine _ U.unop s fun V i ↦ ?_
    have h := Stacks.AlgebraicGeometry.IdealPower.le_idealPowerMultiple_obj I 0 F V
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at h
    exact h Submodule.mem_top
  have htop : Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I 0 F = ⊤ :=
    le_antisymm le_top (fun U s _ ↦ hmem U s)
  have hiso : IsIso (C := X.Modules)
      (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I 0 F).ι := by
    rw [htop]
    exact (AlgebraicGeometry.sheafTopIso F).isIso_hom
  have hepi : Epi (C := X.Modules)
      (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I 0 F).ι :=
    @IsIso.epi_of_iso _ _ _ _ _ hiso
  exact IsZero.of_iso (isZero_zero _) (@cokernel.ofEpi _ _ _ _ _ _ _ _ hepi)

/-- **The tower of derived global sections of the adic quotients is zero at index `0`.** It is
`Stacks.Algebraization.isZero_adicQuotientSystem_zero` carried along two additive functors. -/
public theorem isZero_derivedGlobalSections_adicQuotientSystem_zero
    (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (F : X.Modules) :
    IsZero (((adicQuotientSystem (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f) F ⋙
        DerivedCategory.singleFunctor X.Modules 0) ⋙ derivedGlobalSectionsOver f).obj ⟨0⟩) :=
  Functor.map_isZero (derivedGlobalSectionsOver f)
    (Functor.map_isZero (DerivedCategory.singleFunctor X.Modules 0)
      (isZero_adicQuotientSystem_zero
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f) F))

/-- **A levelwise projection formula for the adic quotient tower forces
`RΓ(X, ℱ) ⊗^𝐋_A A/I` to vanish.** Let `A` be a commutative ring, `I ⊆ A` an ideal,
`f : X ⟶ Spec A` a scheme over `A` and `ℱ` an `𝒪_X`-module, and write `𝓘 = I · 𝒪_X`. Suppose the
tower `n ↦ RΓ(X, ℱ/𝓘ⁿℱ)` is isomorphic, as an `ℕᵒᵖ`-tower in `D(A)`, to the tower
`n ↦ RΓ(X, ℱ) ⊗^𝐋_A A/Iⁿ⁺¹`. Then `RΓ(X, ℱ) ⊗^𝐋_A A/I` is zero.

The two towers are indexed by different exponents — `𝓘ⁿ` on the left, `Iⁿ⁺¹` on the right — so
at `n = 0` the hypothesis identifies `RΓ(X, ℱ/ℱ) = 0` with `RΓ(X, ℱ) ⊗^𝐋_A A/I`. The
conclusion fails already for `X = Spec A` and `ℱ = 𝒪_X`, where it reads `A/I = 0`; so a
hypothesis of this shape is not available for any data with `RΓ(X, ℱ) ⊗^𝐋_A A/I ≠ 0`, and a
theorem carrying it proves nothing about such data. See the module documentation for why
matching the exponents does not repair this, and for the pro-isomorphism that does hold. -/
public theorem isZero_derivedTensor_idealPowerQuotient_zero_of_iso_adicQuotientTower
    (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (F : X.Modules)
    (hproj : ((adicQuotientSystem (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f) F ⋙
          DerivedCategory.singleFunctor X.Modules 0) ⋙ derivedGlobalSectionsOver f) ≅
        NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
            ((derivedGlobalSectionsOver f).obj
              ((DerivedCategory.singleFunctor X.Modules 0).obj F))) :
    IsZero (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F))).obj
      ((NoetherianAdicCompletion.idealPowerQuotientSystem I).obj ⟨0⟩)) :=
  (isZero_derivedGlobalSections_adicQuotientSystem_zero A I f F).of_iso
    (hproj.app ⟨0⟩).symm

end Stacks.Algebraization

end
