module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.FiniteLength
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.RingTheory.Length.FlatLocalHom

/-!
# The length of a pullback of modules along a flat morphism of algebraic spaces

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over a scheme `S`, let `x̄` be a
geometric point of `X` and let `G` be an `𝒪_Y`-module. The length of the pullback `f^*G` at `x̄`
is the length of `G` at `f ∘ x̄` times the length of the fibre ring of the homomorphism of étale
local rings:

`length_{𝒪_{X, x̄}}((f^*G)_{x̄}) =
  length_{𝒪_{Y, f ∘ x̄}}(G_{f ∘ x̄}) · length_{𝒪_{X, x̄}}(𝒪_{X, x̄} / 𝔪_{f ∘ x̄} 𝒪_{X, x̄})`.

This is **Algebra, Lemma 10.52.13 (Stacks 02M1)** read on an algebraic space. The two inputs are
the base-change formula for the geometric stalk of a pullback, Stacks 05VQ in the form
`AlgebraicGeometry.Space.geometricModuleStalkPullbackIso`, and flatness and locality of the
homomorphism of étale local rings of Stacks 04NG,
`AlgebraicGeometry.Space.flat_etaleLocalRingMap` and
`AlgebraicGeometry.Space.isLocalHom_etaleLocalRingMap`.

The identity holds in `ℕ∞` with no finiteness hypothesis, and no quasi-coherence or coherence
of `G` is required.

## Main results

* `AlgebraicGeometry.Space.geometricLength_mul_length_quotient_extendedMaximalIdeal`: the
  identity above.

## Implementation notes

**Where this is used, and what it does not give.** The identity is the algebraic step of the
source's proof of Stacks 0EPB, part (2), which compares the coefficient of an integral closed
subspace `T ⊆ X` in `[f^*F]_{k+r}` with its coefficient in `f^*[F]_k`. It supplies the
comparison on the module side only. Turning it into that cycle identity needs in addition the
identification of the multiplicity `m_{T, f^{-1}(W)}` of Stacks 0EE9 with the second factor
`length_{𝒪_{X, x̄}}(𝒪_{X, x̄} / 𝔪_{f ∘ x̄} 𝒪_{X, x̄})`, which is not available here; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackClosedSubspaceMultiplicity`.

**The local-ring instances.** `AlgebraicGeometry.Space.etaleLocalRing` is not a local ring by
instance resolution — being one is `AlgebraicGeometry.Space.isLocalRing_etaleLocalRing`, which
needs the space to be algebraic — so the maximal ideal appearing in the statement is formed
under a `letI`, in the style of
`AlgebraicGeometry.Space.map_maximalIdeal_chartLocalRingToEtaleLocalRing`.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Multiplicativity of the length at a geometric point along a flat morphism, Stacks 02M1.**
For a flat morphism `f : X ⟶ Y` of algebraic spaces, a geometric point `x̄` of `X` and an
`𝒪_Y`-module `G`,

`length(G at f ∘ x̄) · length_{𝒪_{X, x̄}}(𝒪_{X, x̄} / 𝔪_{f ∘ x̄} 𝒪_{X, x̄}) =
  length(f^*G at x̄)`,

an identity in `ℕ∞` with no finiteness hypothesis.

The stalk of `f^*G` at `x̄` is the base change of the stalk of `G` at `f ∘ x̄` along the
homomorphism `𝒪_{Y, f ∘ x̄} ⟶ 𝒪_{X, x̄}` of étale local rings, by Stacks 05VQ; that
homomorphism is local and, `f` being flat, flat; so this is Algebra, Lemma 10.52.13. -/
theorem geometricLength_mul_length_quotient_extendedMaximalIdeal (f : X ⟶ Y)
    (hf : IsFlat B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    letI : IsLocalRing ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x)) :=
      isLocalRing_etaleLocalRing B S hS Y.1 Y.2 (geometricPointMap f.hom x)
    geometricLength B S hS Y (geometricPointMap f.hom x) G *
        Module.length ↥(etaleLocalRing B S hS X.1 x)
          (↥(etaleLocalRing B S hS X.1 x) ⧸
            Ideal.map (etaleLocalRingMap X.2 f.hom x)
              (maximalIdeal ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x)))) =
      geometricLength B S hS X x ((modulePullback B S hS f).obj G) := by
  have : IsLocalRing ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x)) :=
    isLocalRing_etaleLocalRing B S hS Y.1 Y.2 (geometricPointMap f.hom x)
  have : IsLocalRing ↥(etaleLocalRing B S hS X.1 x) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 x
  let : Algebra ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x))
      ↥(etaleLocalRing B S hS X.1 x) := (etaleLocalRingMap X.2 f.hom x).toAlgebra
  have : Module.Flat ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x))
      ↥(etaleLocalRing B S hS X.1 x) := flat_etaleLocalRingMap B S hS X.2 Y.2 f.hom hf x
  have : IsLocalHom (algebraMap ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x))
      ↥(etaleLocalRing B S hS X.1 x)) := isLocalHom_etaleLocalRingMap B S hS X.2 Y.2 f.hom x
  rw [geometricLength, geometricLength,
    ModuleCat.length_eq_of_iso (geometricModuleStalkPullbackIso B S hS f x G)]
  exact length_baseChange_eq_length_mul_length_quotient _ _ _

end AlgebraicGeometry.Space

end
