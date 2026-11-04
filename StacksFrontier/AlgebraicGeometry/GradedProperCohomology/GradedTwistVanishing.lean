module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.CoproductTwistVanishing
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.RelativeSpecData

/-!
# Uniform vanishing for the twists of a graded module, with the base change discharged

Let `X` be a scheme, `𝓑` a sheaf of graded `𝒪_X`-algebras with commutative homogeneous
multiplication, concentrated in nonnegative degrees and quasi-coherent, and `M` a graded
`𝓑`-module of finite type whose pieces are quasi-coherent and whose negative pieces vanish. Write
`π : X' = Spec_X(⨁ₙ 𝓑ₙ) ⟶ X` for the relative spectrum. If `X'` carries a proper morphism to the
spectrum of a Noetherian ring, is locally Noetherian, and `π^* ℒ` is ample on it for an
invertible `𝒪_X`-module `ℒ`, then one integer `d₀` makes

`Hᵖ(X, Mₙ ⊗ ℒ ^⊗ d) = 0` for every `p > 0`, every `d ≥ d₀` and every `n`.

This is **part (2) of [Stacks, Tag 0897] with the base change of the source's own proof
discharged.** `StacksFrontier/AlgebraicGeometry/GradedProperCohomology/Basic.lean` states that part
with `X'`, `f'`, `F'` and the cohomology comparison `hcmp` as named hypotheses; here only the
geometric ones are left, and the three that were sheaf-theoretic — the module `F'` on `X'`, its
coherence, and the comparison of the cohomology upstairs with the cohomology of the pieces
downstairs — are proved.

## Main results

* `Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_gradedModule` — the
  theorem displayed above.

## How the two halves meet

`StacksFrontier/AlgebraicGeometry/GradedProperCohomology/RelativeSpecData.lean` produces, from the
graded data alone, the relative spectrum `X'`, its affine structure morphism `π`, the coherent
`𝒪_{X'}`-module `F'` and the identification `ε : ∐ₙ Mₙ ≅ π_* F'`.
`StacksFrontier/AlgebraicGeometry/GradedProperCohomology/CoproductTwistVanishing.lean` turns exactly
that quadruple — together with a proper `f' : X' ⟶ Spec R` over a Noetherian `R` and ampleness of
`π^* ℒ` **upstairs** — into the uniform vanishing. Nothing is added here beyond composing them.

Why ampleness is asked for upstairs rather than on `X` is the subject of the module documentation
of `CoproductTwistVanishing.lean`: the source of [Stacks, Tag 0897] assumes `ℒ` ample on `X` and
derives ampleness of `π^* ℒ` from it by [Stacks, Tag 0892] part (2), `π` being affine, so the
hypothesis here is the derived one; and for the non-surjective `π` that [Stacks, Tag 0D2M]
applies this to — the relative spectrum of an associated graded algebra, which factors through
the closed subscheme the ideal cuts out — the derived hypothesis is strictly weaker and is the
one available.

## What remains conditional, and why it is not a gap in this file

Two hypotheses below are geometric and are the source's own, read through the base change:

* `f' : X' ⟶ Spec R` proper with `R` Noetherian. In [Stacks, Tag 0897] this is the second
  projection of `X' = Spec(B) ×_{Spec A} X`, proper by [Stacks, Tag 01W4]; it is a hypothesis
  here because `X'` is built as a relative spectrum over `X` rather than as that fibre product,
  and the identification of the two is a statement about `𝓑` — namely that it is the pullback
  `f^* B̃` — which a general graded algebra sheaf does not satisfy.
* local Noetherianness of `X'`, which
  `Stacks.GradedProperCohomology.isLocallyNoetherian_relativeSpecOver` reduces to local
  Noetherianness of `X` together with `𝓑`'s ungraded realization being an `𝒪_X`-algebra of finite
  type.

Ampleness of `π^* ℒ` is likewise a hypothesis, and deliberately so: see above.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.FiniteTypeDominating
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.GradedProperCohomology

/-- **[Stacks, Tag 0897] part (2), with the base change of the source's proof discharged.** Let
`X` be a scheme, `𝓑` a sheaf of graded `𝒪_X`-algebras with commutative homogeneous
multiplication whose ungraded realization is quasi-coherent, and `M` a graded `𝓑`-module of
finite type with quasi-coherent pieces, vanishing in negative degrees. Let
`π : X' = Spec_X(⨁ₙ 𝓑ₙ) ⟶ X` be the relative spectrum, assumed locally Noetherian and carrying a
proper morphism `f'` to the spectrum of a Noetherian ring. If `ℒ` is an invertible `𝒪_X`-module
whose pullback `π^* ℒ` is ample on `X'`, then there is a `d₀` with

`Hᵖ(X, Mₙ ⊗ ℒ ^⊗ d) = 0` for every `p > 0`, every `d ≥ d₀` and every `n`,

one bound serving all three.

The module `F'` on `X'` and the identification `ε : ∐ₙ Mₙ ≅ π_* F'` are
`Stacks.GradedProperCohomology.gradedBaseChangeModule` and `gradedCoprodPushforwardIso`, its
coherence is `isCoherent_gradedBaseChangeModule`, and the cohomological content is
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_coprodIso`. -/
public theorem exists_isZero_Hgroup_tensorPowTwist_of_gradedModule {X : Scheme.{u}}
    (𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (𝓑.piece i).val.obj W)
      (b : (𝓑.piece j).val.obj W), HEq ((𝓑.mul i j).app W a b) ((𝓑.mul j i).app W b a))
    [𝓑.IsCommutative] [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X 𝓑 hc)]
    [IsLocallyNoetherian (relativeSpecOver (gradedAlgebraSheaf X 𝓑 hc)).left]
    (M : _root_.SheafOfModules.GradedModule.{u, u, u} 𝓑)
    (hB : ((_root_.SheafOfModules.restrictScalars 𝓑.ungradedStructureMap).obj
      (_root_.SheafOfModules.unit 𝓑.ungradedSheaf)).IsQuasicoherent)
    (hcop : (∐ fun n : ℕ => M.piece (n : ℤ)).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n)) (hft : M.IsFiniteType)
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (f' : (relativeSpecOver (gradedAlgebraSheaf X 𝓑 hc)).left ⟶ Spec (CommRingCat.of R))
    [IsProper f'] (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple (relativeSpecOver (gradedAlgebraSheaf X 𝓑 hc)).left
      (pullbackModule (relativeSpecOver (gradedAlgebraSheaf X 𝓑 hc)).hom L)) :
    ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p → ∀ n : ℕ,
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (tensorModules X (M.piece (n : ℤ)) (tensorPowModule X L (d : ℤ)))) :=
  have : (gradedBaseChangeModule 𝓑 hc M hB hcop hneg).IsCoherent :=
    isCoherent_gradedBaseChangeModule 𝓑 hc M hB hcop hneg hft
  exists_isZero_Hgroup_tensorPowTwist_of_coprodIso
    (relativeSpecOver (gradedAlgebraSheaf X 𝓑 hc)).hom f' L hL
    (gradedBaseChangeModule 𝓑 hc M hB hcop hneg)
    (fun n : ℕ => M.piece (n : ℤ)) (gradedCoprodPushforwardIso 𝓑 hc M hB hcop hneg)

end Stacks.GradedProperCohomology

end
