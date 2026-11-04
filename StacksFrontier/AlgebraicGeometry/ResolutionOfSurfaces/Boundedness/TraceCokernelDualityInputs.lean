module

public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TraceCokernelDualitySequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TraceCokernelTriangleData

/-!
# Tag 0B4S with its geometric inputs discharged, leaving two statements about `Hom_{D(A)}`

This is [Stacks, Tag 0B4S] with everything supplied except two identifications of morphism
groups in `D(A)`. Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two with a
normalized dualizing complex `ω_A^•`, and write `C_f = RΓ(X, 𝒪_X)[2]` for a modification
`f : X ⟶ Spec(A)` with `X` normal. Then reduction to rational singularities is possible for `A`
as soon as a nonzero `d ∈ A` satisfies, for every such `f`,

* `hvan`: every morphism `C_f[-1] ⟶ ω_A^•` vanishes, and
* `himage`: for every `u : A[-2] ⟶ C_f` which is an isomorphism on `H^{-2}` and every
  `q : A[-2] ⟶ ω_A^•`, the morphism `d · q` factors through `u`.

## The two hypotheses

Both hypotheses are the tag's own data read through duality. Their common core is the chain

`Hom_{D(A)}(RΓ(X, 𝒪_X)[n], ω_A^•) = H^{-n}(RHom_A(RΓ(X, 𝒪_X), ω_A^•)) = H^{-n}(RΓ(X, ω_X^•))`
`= H^{n-2}(X, ω_X)`,

which at `n = 1` is `H¹(X, ω_X)` and at `n = 2` is `Γ(X, ω_X)`. The first equality is
`StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso`, whose component is
`Dualizing.extIntoOmegaAtLinearEquiv`. The second is the duality transport
`RHom_A(RΓ(X, ω_X^•), ω_A^•) ≅ RΓ(X, 𝒪_X)`
(`Stacks.Duality.nonempty_iso_dualizingDerivedHom_derivedGlobalSections_relativeDualizing`) read
backwards through biduality ([Stacks, Tag 0A7C], `Dualizing.dualizingDerivedHom_biduality_isIso`),
and the third is the normalization `ω_X^• ≅ ω_X[2]`
(`AlgebraicGeometry.VanishingSituation.exists_isDualizingModule_properRightAdjoint_isoShiftTwo`)
together with the commutation of `RΓ(X, -)` with the shift.

Through that chain, `hvan` is Grauert-Riemenschneider: `H¹(X, ω_X) = 0`, [Stacks, Tag 0AXD]
(`AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_normalizedDualizingModule`). For
`himage`, composition with `u` is moreover identified with the trace `Γ(X, ω_X) ⟶ ω_A` of
[Stacks, Tag 0AWG], so that `himage` says that `d · ω_A` lies in the image of the trace, which is
the tag's hypothesis.

The other conditions of
`Stacks.ResolutionOfSurfaces.isReductionToRationalSingularitiesPossible_of_triangle_data` — the
concentration of `C` in the degrees `-2` and `-1`, the morphism `u` from `A[-2]` which is an
isomorphism on `H^{-2}` together with the identification of `H^{-1}(C)` with `H¹(X, 𝒪_X)`, and
the finite length of `H^{-1}(C)` — are supplied by
`AlgebraicGeometry.exists_triangle_data_standardDerivedGlobalSectionsUnitShift`, with `C` the
object `AlgebraicGeometry.standardDerivedGlobalSectionsUnitShift`.

`himage` quantifies over every `u` which is an isomorphism on `H^{-2}` rather than naming one,
because `exists_triangle_data_standardDerivedGlobalSectionsUnitShift` produces `u` existentially:
`H^{-2}(C_f) ≅ A` is itself only produced as a `Nonempty`. The intended `u`, the unit
`A ⟶ Rf_*𝒪_X` shifted, is such a morphism.

## References

* [Stacks Project, Tag 0B4S](https://stacks.math.columbia.edu/tag/0B4S)
* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 0AWG](https://stacks.math.columbia.edu/tag/0AWG)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ResolutionOfSurfaces

section Inputs

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 0B4S] with its geometric inputs discharged.** Let `(A, 𝔪, κ)` be a local
normal Nagata domain of dimension two with a normalized dualizing complex `ω_A^•` and let
`d ∈ A` be nonzero. Write `C_f = RΓ(X, 𝒪_X)[2]`
(`AlgebraicGeometry.standardDerivedGlobalSectionsUnitShift`) for a modification
`f : X ⟶ Spec(A)` with `X` normal. If for every such `f` every morphism `C_f[-1] ⟶ ω_A^•`
vanishes, and `d · Hom(A[-2], ω_A^•)` factors through every `u : A[-2] ⟶ C_f` which is an
isomorphism on `H^{-2}`, then reduction to rational singularities is possible for `A`.

The first hypothesis is Grauert-Riemenschneider ([Stacks, Tag 0AXD]) and the second is the tag's
hypothesis on `d`, each read through duality over the affine base. Everything else the duality
step `smul_eq_zero_of_triangle_of_forall_hom_eq_zero` asks for is supplied by
`AlgebraicGeometry.exists_triangle_data_standardDerivedGlobalSectionsUnitShift`. -/
theorem isReductionToRationalSingularitiesPossible_of_hom_vanishing_of_factorisation
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A]
    (hdim : ringKrullDim A = 2) (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u} ωA) (d : A) (hd : d ≠ 0)
    (hvan : ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      ∀ g : (standardDerivedGlobalSectionsUnitShift f)⟦(-1 : ℤ)⟧ ⟶ ωA, g = 0)
    (himage : ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      ∀ u : (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj (ModuleCat.of A A) ⟶
          standardDerivedGlobalSectionsUnitShift f,
        IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).map u) →
        ∀ q : (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj (ModuleCat.of A A) ⟶ ωA,
          ∃ r : standardDerivedGlobalSectionsUnitShift f ⟶ ωA, u ≫ r = q ≫ (d • 𝟙 ωA)) :
    IsReductionToRationalSingularitiesPossible A := by
  have : IsNoetherianRing A := ‹IsNagataRing A›.1
  refine isReductionToRationalSingularitiesPossible_of_triangle_data A hdim ωA hωA d hd
    fun X _ f hf => ?_
  obtain ⟨hge, hle, u, hu, hfl, he⟩ :=
    exists_triangle_data_standardDerivedGlobalSectionsUnitShift f hdim hf
  exact ⟨standardDerivedGlobalSectionsUnitShift f, hge, hle, u, hu, hfl, he, hvan X f hf,
    himage X f hf u hu⟩

end Inputs

end Stacks.ResolutionOfSurfaces

end
