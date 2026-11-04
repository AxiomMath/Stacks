module

public import Mathlib.Algebra.Category.ModuleCat.Images
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumCompletedSections
public import StacksFrontier.CategoryTheory.Abelian.InverseSystem
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyLimit
public import StacksFrontier.RingTheory.LocalCohomology.MittagLefflerSystems

/-!
# Completed local cohomology of a finite module as the limit of the local cohomologies of its
adic quotients

Let `(A, 𝔪)` be a Noetherian local ring, let `I ⊆ A` be an ideal and let `M` be a finite
`A`-module. The comparison map
`Hⁱ(RΓ_𝔪(M)^∧) ⟶ lim Hⁱ_𝔪(M/IⁿM)`
out of the cohomology of a derived limit of the tower `n ↦ RΓ_𝔪(M/IⁿM)` is an isomorphism in
every degree, where `RΓ_𝔪(M)^∧` is the derived `I`-adic completion of `RΓ_𝔪(M)`.

The comparison map sits in the Milnor short exact sequence whose left-hand term is the first
derived inverse limit `R¹lim H^{i-1}_𝔪(M/IⁿM)`. Since every `M/IⁿM` is a finite module, that
inverse system is Mittag-Leffler, so its first derived limit vanishes: the Mittag-Leffler
condition makes the difference map `(xₙ) ↦ (xₙ - xₙ₊₁)` on the product of the terms an
epimorphism, hence its cokernel — the left-hand term of the sequence — is zero and the
comparison map is both a monomorphism and an epimorphism.

## Main definitions

* `Stacks.LocalCohomology.completedLocalCohomologyIsoLimit` — the isomorphism
  `Hⁱ(RΓ_𝔪(M)^∧) ≅ lim Hⁱ_𝔪(M/IⁿM)` for an abstract derived limit `RΓ_𝔪(M)^∧` of the tower.
* `Stacks.LocalCohomology.completedLocalCohomologyDerivedCompletionIsoLimit` — the same
  isomorphism with `RΓ_𝔪(M)^∧` taken to be the derived `I`-adic completion itself.

## Main results

* `Stacks.LocalCohomology.isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology` — the
  inverse system `n ↦ Hⁱ_𝔪(M/IⁿM)` is Mittag-Leffler.
* `Stacks.LocalCohomology.isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology_smul` —
  the same for the submodule `IᵏM`, so that `n ↦ Hⁱ_𝔪(IᵏM/Iⁿ⁺ᵏM)` is Mittag-Leffler too.
* `Stacks.LocalCohomology.isIso_completedLocalCohomologyToLimit_of_isMittagLeffler` — the
  comparison map out of the cohomology of a derived limit of `n ↦ RΓ_{V(J)}(M/IⁿM)` is an
  isomorphism as soon as the system one degree below is Mittag-Leffler, for an arbitrary support
  ideal `J` over an arbitrary commutative ring.
* `Stacks.LocalCohomology.isIso_completedLocalCohomologyToLimit` — the comparison map out of the
  cohomology of a derived limit of `n ↦ RΓ_𝔪(M/IⁿM)` is an isomorphism.
* `Stacks.LocalCohomology.isIso_completedLocalCohomologyToLimit_derivedCompletion` — the same
  conclusion for the derived `I`-adic completion `RΓ_𝔪(M)^∧` itself.

## Implementation notes

The statements about an arbitrary derived limit of the tower are unconditional. The statements
about `RΓ_𝔪(M)^∧` itself feed `Dualizing.isDerivedLimit_completedLocalCohomology` — Tag 0EEW
part (1), identifying the derived `I`-adic completion of `RΓ_𝔪(M)` with a derived limit of the
tower, recorded in
`StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyLimit` — into the
comparison above, so no extra hypothesis on the completion is needed.

The module universe equals the ring universe, which is the universe the tower of Tag 0EEW lives
in. The vanishing of the first derived inverse limit of a Mittag-Leffler system is taken from
the abelian-group formulation of Tag 07KW and transported to `ModuleCat A` along the forgetful
functor, which preserves the countable products involved.

## References

* [Stacks Project, Tag 0DXJ](https://stacks.math.columbia.edu/tag/0DXJ)
* [Stacks Project, Tag 0DX1](https://stacks.math.columbia.edu/tag/0DX1)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

open Stacks.Algebraization

section Comparison

variable (A : Type u) [CommRing A]

/-- Limits of shape `Discrete ℕ`, that is countable products, are exact in `ModuleCat A`. -/
noncomputable local instance moduleCatHasExactLimitsNat :
    HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} A) :=
  moduleCat_hasExactLimitsOfShape_discrete A ℕ

/-- **The local cohomology of the adic quotients of a finite module is Mittag-Leffler.** For a
finite module `M` over a Noetherian local ring, the inverse system `n ↦ Hⁱ_𝔪(M/IⁿM)` satisfies
the Mittag-Leffler condition, since each `M/IⁿM` is again a finite module.

This is part (2) of [Stacks, Tag 0EFY] at the support `T = {𝔪}` of a Noetherian local ring. In
that case it holds in every degree and draws nothing from Situation [Stacks, Tag 0EFU]: local
cohomology at `𝔪` of a finite module over a Noetherian local ring is Artinian, and a descending
chain of submodules of an Artinian module stabilizes, which is the Mittag-Leffler condition. A
general specialization-stable `T ⊆ V(I)` lies beyond that argument, the modules `Hⁱ_T(M/IⁿM)`
being in general neither finite nor Artinian; the source obtains part (2) there from the
pro-zero assertion of [Stacks, Tag 0EFX] instead. -/
@[stacks 0EFY "part (2) at T = {𝔪} over a Noetherian local ring, in every degree"]
theorem isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology
    [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A)
    [Module.Finite A M] (i : ℤ) :
    IsMittagLefflerCategorical
      (Dualizing.adicQuotientLocalCohomologySystem A I (IsLocalRing.maximalIdeal A)
          (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) :=
  isMittagLeffler_localCohomology A (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M)
    (fun _ ↦ Module.Finite.quotient A _) i

/-- **Part (3) of [Stacks, Tag 0EFY] at the support `T = {𝔪}`.** For a finite module `M` over a
Noetherian local ring, an ideal `I` and a `k : ℕ`, the inverse system `n ↦ Hⁱ_𝔪(IᵏM/Iⁿ⁺ᵏM)` of
the local cohomologies of the adic quotients of the submodule `IᵏM` satisfies the
Mittag-Leffler condition, in every degree.

The source indexes that system by `n ≥ k` and writes its terms `Hⁱ_𝔪(IᵏM/IⁿM)`; the index here
runs over all of `ℕ` instead, which replaces `IⁿM` by `Iⁿ(IᵏM) = Iⁿ⁺ᵏM` and so gives the same
family of modules and the same transition maps, read along the cofinal shift `n ↦ n + k`.

`IᵏM` is a submodule of a finite module over a Noetherian ring, hence itself finite, so this is
`isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology` applied to it. -/
@[stacks 0EFY "part (3) at T = {𝔪} over a Noetherian local ring, for the submodule IᵏM"]
theorem isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology_smul
    [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A)
    [Module.Finite A M] (k : ℕ) (i : ℤ) :
    IsMittagLefflerCategorical
      (Dualizing.adicQuotientLocalCohomologySystem A I (IsLocalRing.maximalIdeal A)
          (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
          (ModuleCat.of A ↥(I ^ k • (⊤ : Submodule A M))) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) :=
  isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology A I
    (ModuleCat.of A ↥(I ^ k • (⊤ : Submodule A M))) i

/-- **Stacks Project, Tag 0DXJ, with the Mittag-Leffler condition as a hypothesis.** For ideals
`I` and `J` of a commutative ring `A` and a module `M`, the comparison map from the degree-`i`
cohomology of a derived limit of the tower `n ↦ RΓ_{V(J)}(M/IⁿM)` to the inverse limit of the
local cohomology modules `Hⁱ_{V(J)}(M/IⁿM)` is an isomorphism as soon as the inverse system
`n ↦ H^{i-1}_{V(J)}(M/IⁿM)` one degree below satisfies the Mittag-Leffler condition: that
condition makes the `R¹lim` term of the Milnor short exact sequence vanish, leaving the
comparison both a monomorphism and an epimorphism.

Neither the Noetherian hypothesis on `A`, nor the finiteness of `M`, nor the locality of `A`
enters; they are what `isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology` consumes
in order to discharge `hML` for `J = 𝔪`. Because `hML` is a hypothesis here, Tag 0DXJ is not
registered on this theorem; it is registered on
`isIso_completedLocalCohomologyToLimit_derivedCompletion` and
`completedLocalCohomologyDerivedCompletionIsoLimit` below, where nothing is assumed. -/
theorem isIso_completedLocalCohomologyToLimit_of_isMittagLeffler
    (I J : Ideal A) (hJ : J.FG) (M : ModuleCat.{u} A) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDerivedLimit (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M) K) (i : ℤ)
    (hML : IsMittagLefflerCategorical
      (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i - 1))) :
    IsIso (Dualizing.completedLocalCohomologyToLimit A I J hJ M K hK i) := by
  obtain ⟨incl, _, hshort⟩ :=
    Dualizing.completedLocalCohomologyToLimit_shortExact A I J hJ M K hK i
  let G : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
    Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i - 1)
  have hepi : Epi (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj (op n)) n -
      Pi.π (fun n : ℕ ↦ G.obj (op n)) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op) :=
    epi_milnorDifference_of_isMittagLefflerCategorical G hML
  have := hshort.exact.mono_g (((Preadditive.epi_iff_isZero_cokernel _).1 hepi).eq_of_src incl 0)
  have := hshort.epi_g
  exact isIso_of_mono_of_epi _

/-- **Stacks Project, Tag 0DXJ.** Let `(A, 𝔪)` be a Noetherian local ring, let `I ⊆ A` be an
ideal and let `M` be a finite `A`-module. For every `i`, the comparison map from the degree-`i`
cohomology of a derived limit of the tower `n ↦ RΓ_𝔪(M/IⁿM)` to the inverse limit of the local
cohomology modules `Hⁱ_𝔪(M/IⁿM)` is an isomorphism: the `R¹lim` term of the Milnor short exact
sequence vanishes because the system `n ↦ H^{i-1}_𝔪(M/IⁿM)` is Mittag-Leffler. -/
@[stacks 0DXJ "for a derived limit of the tower of local cohomologies of the adic quotients"]
theorem isIso_completedLocalCohomologyToLimit
    [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A)
    [Module.Finite A M] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDerivedLimit (Dualizing.adicQuotientLocalCohomologySystem A I
      (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M) K)
    (i : ℤ) :
    IsIso (Dualizing.completedLocalCohomologyToLimit A I (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M K hK i) :=
  isIso_completedLocalCohomologyToLimit_of_isMittagLeffler A I (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M K hK i
    (isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology A I M (i - 1))

/-- **The identification of Stacks 0DXJ.** The degree-`i` cohomology of a derived limit of the
tower `n ↦ RΓ_𝔪(M/IⁿM)` is isomorphic to the inverse limit of the modules `Hⁱ_𝔪(M/IⁿM)`. -/
def completedLocalCohomologyIsoLimit [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDerivedLimit (Dualizing.adicQuotientLocalCohomologySystem A I
      (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M) K)
    (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K ≅
      limit (Dualizing.adicQuotientLocalCohomologySystem A I (IsLocalRing.maximalIdeal A)
          (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) :=
  letI := isIso_completedLocalCohomologyToLimit A I M K hK i
  asIso (Dualizing.completedLocalCohomologyToLimit A I (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M K hK i)

/-- **Stacks Project, Tag 0DXJ, for the derived `I`-adic completion.** Let `(A, 𝔪)` be a
Noetherian local ring, let `I ⊆ A` be an ideal and let `M` be a finite `A`-module. For every
`i` the comparison map `Hⁱ(RΓ_𝔪(M)^∧) ⟶ lim Hⁱ_𝔪(M/IⁿM)` is an isomorphism.

Tag 0EEW part (1), `Dualizing.isDerivedLimit_completedLocalCohomology`, identifies the derived
`I`-adic completion of `RΓ_𝔪(M)` with a derived limit of the tower `n ↦ RΓ_𝔪(M/IⁿM)`; feeding
that identification into `isIso_completedLocalCohomologyToLimit` transports the conclusion from
an abstract derived limit to the completion itself. -/
@[stacks 0DXJ]
theorem isIso_completedLocalCohomologyToLimit_derivedCompletion
    [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A)
    [Module.Finite A M] (i : ℤ) :
    IsIso (Dualizing.completedLocalCohomologyToLimit A I (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M
      (Dualizing.completedLocalCohomology A I (IsLocalRing.maximalIdeal A)
        I.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M)
      (Dualizing.isDerivedLimit_completedLocalCohomology A I (IsLocalRing.maximalIdeal A)
        I.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M) i) :=
  isIso_completedLocalCohomologyToLimit A I M _ _ i

/-- **Stacks Project, Tag 0DXJ.** For a finite module `M` over a Noetherian local ring
`(A, 𝔪)` and an ideal `I ⊆ A`, the degree-`i` cohomology of the derived `I`-adic completion
`RΓ_𝔪(M)^∧` is isomorphic to the inverse limit of the local cohomology modules
`Hⁱ_𝔪(M/IⁿM)`, for every `i`. This is the equality `Hⁱ(RΓ_𝔪(M)^∧) = lim Hⁱ_𝔪(M/IⁿM)` of the
tag, realized by the comparison map
`Dualizing.completedLocalCohomologyToLimit`. -/
@[stacks 0DXJ]
def completedLocalCohomologyDerivedCompletionIsoLimit [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M] (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (Dualizing.completedLocalCohomology A I (IsLocalRing.maximalIdeal A)
          I.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M) ≅
      limit (Dualizing.adicQuotientLocalCohomologySystem A I (IsLocalRing.maximalIdeal A)
          (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) :=
  letI := isIso_completedLocalCohomologyToLimit_derivedCompletion A I M i
  asIso (Dualizing.completedLocalCohomologyToLimit A I (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M _
    (Dualizing.isDerivedLimit_completedLocalCohomology A I (IsLocalRing.maximalIdeal A)
      I.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M) i)

end Comparison

end Stacks.LocalCohomology

end
