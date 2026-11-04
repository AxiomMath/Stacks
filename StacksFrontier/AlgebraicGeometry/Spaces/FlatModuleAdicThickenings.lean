module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPoint
public import StacksFrontier.RingTheory.Flat.AdicFiltration

/-!
# Flatness over the base from flatness along the adic thickenings

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, let `F`
be an `𝒪_X`-module and let `x̄` be a geometric point of `X` with image `ȳ = f ∘ x̄`.  Write
`R = 𝒪_{Y, ȳ}` and `T = 𝒪_{X, x̄}` for the étale local rings of Stacks 04KF and `M = F_{x̄}` for
the geometric stalk of Stacks 05VQ, a `T`-module whose scalars are restricted along the
canonical homomorphism `R → T` of Stacks 04NG.  Let `J ⊆ R` be an ideal whose image in `T` is a
proper ideal — the condition that `x̄` lies over the closed set `V(J)`.

If `M/JⁿM` is flat over `R/Jⁿ` for every `n ≥ 1`, then `F` is flat over `Y` at `x̄` in the sense
of Stacks 05VU, so `x̄` lies in the relative flat locus. This is the local step of Stacks 08VP,
deduced from the algebra result Stacks 0523, `Module.Flat.of_flat_quotient_pow`.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_of_flat_quotient_pow`: **the local step of
  Stacks 08VP.**  For a Noetherian situation at `x̄` with finite geometric stalk, flatness of
  `M/JⁿM` over `R/Jⁿ` for every `n ≥ 1` gives flatness of `F` over `Y` at `x̄`.
* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_of_flat_quotient_pow_of_ne_top`:
  the same with the hypothesis on `J` read in `R`, where `J ⊆ 𝔪_R` is the condition that `x̄`
  lies over `V(J)`.  The two forms agree because the homomorphism of étale local rings is local,
  `AlgebraicGeometry.Space.isLocalHom_etaleLocalRingMap`.

## Implementation notes

Flatness over `Y` at a geometric point is `AlgebraicGeometry.Space.IsFlatOverAtGeometricPoint`,
clause (2) of Stacks 05VU, the chart-free form of the chartwise predicate
`AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV; for a quasi-coherent module the two agree at
every geometric point by
`AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtGeometricPoint`.

The ring-theoretic hypotheses are instance arguments:

* `IsNoetherianRing R` and `IsNoetherianRing T` follow from the étale-local Noetherianity of `X`
  and of `Y` by `AlgebraicGeometry.Space.isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian`;
  for `Y = Spec A` with `A` Noetherian and `f` locally of finite presentation this is what
  Stacks 08VP assumes.
* `Module.Finite T M` is the finiteness of the geometric stalk of a coherent module of
  Stacks 07UA, `AlgebraicGeometry.Space.IsCoherent`; it follows from quasi-coherence and finite
  type on the small étale site by `AlgebraicGeometry.Space.module_finite_geometricModuleStalk`.

Stacks 08VP itself, the containment of the inverse image of `V(I)` in the flat locus over
`Spec A`, is `AlgebraicGeometry.Space.preimage_zeroLocus_subset_flatLocus_of_isFlatOver_adicFibre`.
Reading its hypothesis, flatness of the pullback `Fₙ` of `F` to `Xₙ = Spec(A/Iⁿ) ×_{Spec A} X`
over `Spec(A/Iⁿ)`, as the hypothesis here, with `(R, J) = (𝒪_{Y, ȳ}, I·𝒪_{Y, ȳ})`, needs the
étale local ring of `Spec A` at a geometric point to be weakly étale over `A` (Stacks 04KF and
Stacks 0950), and the base-change isomorphism `(i^* F)_{z̄} ≅ 𝒪_{Xₙ, z̄} ⊗_{𝒪_{X, x̄}} F_{x̄}` of
geometric stalks (`AlgebraicGeometry.Space.geometricModuleStalkPullbackIso`, Stacks 05VQ).

The module universe is independent of the universe of the site, as it is for
`AlgebraicGeometry.Space.IsFlatOverAtGeometricPoint` and for the geometric stalk.

## References

* [Stacks Project, Tag 08VP](https://stacks.math.columbia.edu/tag/08VP)
* [Stacks Project, Tag 0523](https://stacks.math.columbia.edu/tag/0523)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u m

/-- **Stacks 0523 for a local ring of scalars.**  Let `R → T` be a homomorphism of Noetherian
rings with `T` local, let `M` be a finite `T`-module with compatible `R`-action and let `J ⊆ R`
be an ideal whose image in `T` lies in the maximal ideal.  If `M/JⁿM` is flat over `R/Jⁿ` for
every `n ≥ 1`, then `M` is flat over `R`. -/
@[ega "0 10.2.1" "d ⇒ a"]
private theorem flat_of_flat_quotient_pow_of_isLocalRing
    {R T M : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [IsNoetherianRing R] [IsNoetherianRing T] [IsLocalRing T]
    [AddCommGroup M] [Module R M] [Module T M] [IsScalarTower R T M] [Module.Finite T M]
    (J : Ideal R) (hJ : J.map (algebraMap R T) ≤ maximalIdeal T)
    (hflat : ∀ n : ℕ, 1 ≤ n → Module.Flat (R ⧸ J ^ n) (M ⧸ (J ^ n • (⊤ : Submodule R M)))) :
    Module.Flat R M := by
  have : IsLocalization.AtPrime T (maximalIdeal T) :=
    IsLocalization.self fun _ hx => IsLocalRing.notMem_maximalIdeal.mp hx
  have : IsLocalizedModule.AtPrime (maximalIdeal T) (LinearMap.id : M →ₗ[T] M) := by
    change IsLocalizedModule (maximalIdeal T).primeCompl (LinearMap.id : M →ₗ[T] M)
    exact isLocalizedModule_id (maximalIdeal T).primeCompl M T
  exact Module.Flat.of_flat_quotient_pow J M (fun n => hflat (n + 1) (by omega))
    (maximalIdeal T) hJ M LinearMap.id

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The local step of Stacks 08VP.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over
`S`, let `F` be an `𝒪_X`-module and let `x̄` be a geometric point of `X` whose étale local ring
`T = 𝒪_{X, x̄}` and whose image's étale local ring `R = 𝒪_{Y, ȳ}` are Noetherian, with geometric
stalk `M = F_{x̄}` finite over `T`.  Let `J ⊆ R` be an ideal whose image in `T` is a proper
ideal, which is the condition that `x̄` lies over `V(J)`.  If `M/JⁿM` is flat over `R/Jⁿ` for
every `n ≥ 1`, then `F` is flat over `Y` at `x̄`.

The scalars of `M` over `R` are restricted along the canonical homomorphism of étale local
rings `AlgebraicGeometry.Space.etaleLocalRingMap` of Stacks 04NG, as they are in the conclusion
`AlgebraicGeometry.Space.IsFlatOverAtGeometricPoint`.

The statement does not include the openness of the flat locus (Stacks 05WV), the identification
of the hypothesis with flatness of the pullbacks `F_n` to the thickenings `X_n` (Stacks 05VQ), or
the passage from the base ring `A` and its ideal `I` to the étale local ring of the base. -/
@[stacks 08VP "the local step at a geometric point lying over V(J)"]
theorem isFlatOverAtGeometricPoint_of_flat_quotient_pow
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, m} B S hS X.1 X.2) (xbar : GeometricPoint B S hS X.1)
    [IsNoetherianRing (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))]
    [IsNoetherianRing (etaleLocalRing B S hS X.1 xbar)]
    [Module.Finite (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F)]
    (J : Ideal (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar)))
    (hJ : J.map (etaleLocalRingMap X.2 f.hom xbar) ≠ ⊤)
    (hflat : ∀ n : ℕ, 1 ≤ n →
      letI : Module (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
          (geometricModuleStalk B S hS X xbar F) :=
        Module.compHom _ (etaleLocalRingMap X.2 f.hom xbar)
      Module.Flat (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar) ⧸ J ^ n)
        (geometricModuleStalk B S hS X xbar F ⧸
          (J ^ n • (⊤ : Submodule (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
            (geometricModuleStalk B S hS X xbar F))))) :
    IsFlatOverAtGeometricPoint B S hS f F xbar := by
  have : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  let : Algebra (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      (etaleLocalRing B S hS X.1 xbar) := (etaleLocalRingMap X.2 f.hom xbar).toAlgebra
  let : Module (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      (geometricModuleStalk B S hS X xbar F) :=
    Module.compHom _ (etaleLocalRingMap X.2 f.hom xbar)
  have : IsScalarTower (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F) :=
    IsScalarTower.of_compHom _ _ _
  exact flat_of_flat_quotient_pow_of_isLocalRing J (IsLocalRing.le_maximalIdeal hJ) hflat

/-- **The local step of Stacks 08VP, with the condition on `J` read in the base.**  The same
statement as `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_of_flat_quotient_pow`, with the
hypothesis that `x̄` lies over `V(J)` written as properness of `J` itself: since
`R = 𝒪_{Y, ȳ}` is local, a proper ideal of `R` is one contained in `𝔪_R`, and its image in
`T = 𝒪_{X, x̄}` is again proper because the canonical homomorphism of étale local rings is a
local homomorphism. -/
theorem isFlatOverAtGeometricPoint_of_flat_quotient_pow_of_ne_top
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, m} B S hS X.1 X.2) (xbar : GeometricPoint B S hS X.1)
    [IsNoetherianRing (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))]
    [IsNoetherianRing (etaleLocalRing B S hS X.1 xbar)]
    [Module.Finite (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F)]
    (J : Ideal (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))) (hJ : J ≠ ⊤)
    (hflat : ∀ n : ℕ, 1 ≤ n →
      letI : Module (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
          (geometricModuleStalk B S hS X xbar F) :=
        Module.compHom _ (etaleLocalRingMap X.2 f.hom xbar)
      Module.Flat (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar) ⧸ J ^ n)
        (geometricModuleStalk B S hS X xbar F ⧸
          (J ^ n • (⊤ : Submodule (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
            (geometricModuleStalk B S hS X xbar F))))) :
    IsFlatOverAtGeometricPoint B S hS f F xbar := by
  have : IsLocalRing (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar)) :=
    isLocalRing_etaleLocalRing B S hS Y.1 Y.2 (geometricPointMap f.hom xbar)
  have : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  have : IsLocalHom (etaleLocalRingMap X.2 f.hom xbar) :=
    isLocalHom_etaleLocalRingMap B S hS X.2 Y.2 f.hom xbar
  refine isFlatOverAtGeometricPoint_of_flat_quotient_pow B S hS f F xbar J ?_ hflat
  exact ne_top_of_le_ne_top
    (IsLocalRing.maximalIdeal.isMaximal (etaleLocalRing B S hS X.1 xbar)).ne_top
    ((Ideal.map_mono (IsLocalRing.le_maximalIdeal hJ)).trans
      (IsLocalRing.map_maximalIdeal_le (etaleLocalRingMap X.2 f.hom xbar)))

end AlgebraicGeometry.Space

end
