module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistSourceTheta
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.DegreeSection

/-!
# Clause (2) of Tag 02NC in the source's direction

Clause (2) of [Stacks, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC) is the square

```
𝒜_n(V) ⊗ ℒ^{⊗ n}(V) ---- multiplication ----> ℬ_n(V)
        |                                        |
        | ψ ⊗ π^*                                | ψ
        v                                        v
Γ(π^{-1}V, 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}) <---- θ_n ---- Γ(π'^{-1}V, 𝒪_{P'}(n))
```

in which `θ_n` runs **from** the sections of the twist of `P' = Proj ℬ` **to** the sections of the
twist of `P = Proj 𝒜`, matching the direction `θ_n : g^*𝒪_{P'}(n) ⟶ 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` of
clause (1).

The squares proved in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjInvertibleTwistSections.lean` run the other way:
their `θ_n` is the comparison attached to `ψ_ℓ : 𝒜 →+*ᵍ ℬ`, carrying a section of `𝒪_P(n)` to one
of `𝒪_{P'}(n)`. **This file states the square in the source's direction**, for a twisting module
with a global generator, by the same device as
`StacksFrontier/AlgebraicGeometry/Constructions/ProjInvertibleTwistSourceTheta.lean`: for a generator
the comparison is an isomorphism of graded rings, and [Stacks, Tag 01MY]'s homogeneous-sections
clause `Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection`, which holds for every
homomorphism of graded rings, applied to the inverse comparison gives exactly this square.

## Main results

* `Stacks.GradedRing.InvertibleTwist.twistMap_degreeSection_twistHomInv`: **clause (2) of Tag
  02NC in the source's direction**, at the section `ℓ ^ n` of `ℒ^{⊗ n}` and with `V` the whole
  base. The comparison `θ_n` carries the global section of `𝒪_{P'}(n)` attached to the product
  `a ⊗ ℓ ^ n` in the twisted algebra — which is the image of `a ⊗ ℓ ^ n` under the top row — to
  the global section of `𝒪_P(n)` attached to `a`.

## Scope, and what is not covered

* **The base is `Spec R` and `V` is the whole of it.** The source asserts the square for every
  open `V` of an arbitrary base scheme `S`; `𝒜_n(V)` for a proper open `V` is not an object of
  this absolute setting at all.
* **A global generator is used**, because the inverse comparison homomorphism is what carries the
  square in this direction and it exists only then. The other direction is available with no
  generator, for every `ℓ ∈ 𝓛 1`, as
  `Stacks.GradedRing.InvertibleTwist.twistMap_degreeSection_pieceMap`.
* **The target object `𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`** appears as `𝒪_P(n)`: the generator trivializes
  `ℒ^{⊗ n}`, so the tensor factor is the structure sheaf, and it is not carried as an object. The
  section of `ℒ^{⊗ n}` is correspondingly `ℓ ^ n`.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum Graded HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistSections
open scoped TensorProduct

universe u

namespace Stacks.GradedRing

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {R A B T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
  [Algebra R A] [Algebra R B] [Algebra R T]

namespace InvertibleTwist

variable {𝒜 : ℕ → Submodule R A} [_root_.GradedAlgebra 𝒜] {𝓛 : ℕ → Submodule R T}
  {ℬ : ℕ → Submodule R B} [_root_.GradedAlgebra ℬ] (tw : InvertibleTwist 𝒜 𝓛 ℬ)
  (h𝓛 : IsTensorPowerFamily 𝓛) {ℓ : T} {hℓ : ℓ ∈ 𝓛 1}
  (hgen : Function.Bijective (LinearMap.toSpanSingleton R (𝓛 1) ⟨ℓ, hℓ⟩))

include tw h𝓛 hgen

/-- **Clause (2) of Stacks Tag 02NC in the source's direction, for a twisting module with a global
generator.** For a homogeneous `a ∈ 𝒜 n`, the comparison `θ_n : g^*𝒪_{P'}(n) ⟶ 𝒪_P(n)` attached
to the inverse comparison homomorphism carries the global section of `𝒪_{Proj ℬ}(n)` attached to
the product `a ⊗ ℓ ^ n` in the twisted algebra — the image of `a ⊗ ℓ ^ n` under the top row of
the source's square — to the global section of `𝒪_{Proj 𝒜}(n)` attached to `a`. Both sections are
read through the unit of the pullback--pushforward adjunction.

This is the source's square with `V` the whole base and the section of `ℒ^{⊗ n}` taken to be
`ℓ ^ n`, which the generator trivializes `ℒ^{⊗ n}` by. For the same square with `θ_n` running in
the direction this library's comparison on twists runs, and with no generator, see
`Stacks.GradedRing.InvertibleTwist.twistMap_degreeSection_pieceMap`. -/
theorem twistMap_degreeSection_twistHomInv (n : ℕ) (a : 𝒜 n) :
    ((projMapData ℬ 𝒜 (tw.twistHomInv h𝓛 hgen)).twistMap (n : ℤ)).val.app (.op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction
            (projMapData ℬ 𝒜 (tw.twistHomInv h𝓛 hgen)).hom).unit.app
          (twistingSheaf ℬ (n : ℤ))).val.app (.op ⊤)
          (degreeSection ℬ n (tw.pieceMap h𝓛 hℓ n a)))
      = ((Scheme.Modules.pullbackPushforwardAdjunction
            (mapDomain ℬ 𝒜 (tw.twistHomInv h𝓛 hgen)).ι).unit.app
          (twistingSheaf 𝒜 (n : ℤ))).val.app (.op ⊤) (degreeSection 𝒜 n a) := by
  have hpiece : tw.pieceMap h𝓛 hℓ n a = tw.pieceEquiv h𝓛 hgen n a :=
    (tw.pieceMap_apply h𝓛 hℓ n a).trans (tw.pieceEquiv_apply h𝓛 hgen n a).symm
  have hinv : tw.twistHomInv h𝓛 hgen ((tw.pieceMap h𝓛 hℓ n a : B)) = (a : A) := by
    rw [hpiece, tw.twistHomInv_coe h𝓛 hgen n, LinearEquiv.symm_apply_apply]
  refine (Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection ℬ 𝒜
      (tw.twistHomInv h𝓛 hgen) n (tw.pieceMap h𝓛 hℓ n a)).trans ?_
  exact congrArg
    (fun x : 𝒜 n => ((Scheme.Modules.pullbackPushforwardAdjunction
          (mapDomain ℬ 𝒜 (tw.twistHomInv h𝓛 hgen)).ι).unit.app
        (twistingSheaf 𝒜 (n : ℤ))).val.app (.op ⊤) (degreeSection 𝒜 n x)) (Subtype.ext hinv)

end InvertibleTwist

end Stacks.GradedRing

end
