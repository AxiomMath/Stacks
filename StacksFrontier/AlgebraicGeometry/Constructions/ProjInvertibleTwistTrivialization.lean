module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwist
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModuleBundle
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso

/-!
# The trivialization of `π^*ℒ^{⊗ n}` by a global generator

Clause (1) of [Stacks, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC) asks for comparisons
`θ_n : g^*𝒪_{P'}(n) ⟶ 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` whose target carries the pullback of the `n`-th power
of the twisting module as an object. Turning a comparison with target `𝒪_P(n)` into one of that
shape needs an isomorphism

`π^*ℒ^{⊗ n} ≅ 𝒪`

over the scheme the comparison lives on. This file builds that isomorphism, for a twisting module
with a global generator `ℓ`, and for the pullback along an *arbitrary* morphism to the base — so
in particular along `π`, and along `π` restricted to any open. Since `ℓ ^ n` is a basis of `𝓛 n`
(`Stacks.GradedRing.IsTensorPowerFamily.bijective_toSpanSingleton_pow`), the trivialization is
already an isomorphism of `R`-modules, and `tilde` carries it to one of sheaves.

## Main definitions

* `Stacks.GradedRing.IsTensorPowerFamily.powEquiv`: the generator's `n`-th power as a basis,
  `R ≃ₗ[R] 𝓛 n`.
* `Stacks.GradedRing.IsTensorPowerFamily.tildeIsoUnit`: **`ℒ^{⊗ n} ≅ 𝒪_{Spec R}`**, the
  trivialization of the `n`-th power of the twisting module as a quasi-coherent sheaf on the base.
* `Stacks.GradedRing.IsTensorPowerFamily.pullbackTildeIsoUnit`: **`π^*ℒ^{⊗ n} ≅ 𝒪_W`**, its
  pullback along an arbitrary morphism `W ⟶ Spec R`.

## Implementation notes

The powers are indexed by `ℕ`, which is the index set of the family `𝓛`. The tag's `θ_n` runs over
`n : ℤ`; the negative powers of a trivial invertible sheaf are trivial as well
(`Stacks.TensorPowers.intTensorPowIsoUnit`).

A global generator is used throughout. Without one `ℓ ^ n` generates `𝓛 n` only at the points of
`U(ψ_ℓ)` (`Stacks.GradedRing.InvertibleTwist.exists_dual_notMem`), and the trivialization has to be
assembled over the charts instead.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Stacks.GradedRing.IsTensorPowerFamily

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
  {𝓛 : ℕ → Submodule R T} (h𝓛 : IsTensorPowerFamily 𝓛) {ℓ : T} {hℓ : ℓ ∈ 𝓛 1}
  (hgen : Function.Bijective (LinearMap.toSpanSingleton R (𝓛 1) ⟨ℓ, hℓ⟩))

include h𝓛 hgen

/-- **The `n`-th power of a generator is a basis of the `n`-th power of the twisting module**,
read as a linear isomorphism `R ≃ₗ[R] 𝓛 n`. -/
def powEquiv (n : ℕ) : R ≃ₗ[R] (𝓛 n) :=
  LinearEquiv.ofBijective _ (h𝓛.bijective_toSpanSingleton_pow hℓ hgen n)

/-- The isomorphism `powEquiv` sends a scalar `c` to `c • ℓ ^ n`. -/
theorem powEquiv_apply (n : ℕ) (c : R) : (h𝓛.powEquiv hgen n c : T) = c • ℓ ^ n := rfl

/-- **The trivialization of `ℒ^{⊗ n}` on the base by the `n`-th power of a global generator.**
The `n`-th power of the twisting module is free of rank one on `ℓ ^ n`, so the quasi-coherent
sheaf it determines on `Spec R` is the structure sheaf. -/
def tildeIsoUnit (n : ℕ) :
    AlgebraicGeometry.tildeOfModule R (𝓛 n) ≅
      SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf :=
  (AlgebraicGeometry.tilde.functor (CommRingCat.of R)).mapIso
      (LinearEquiv.toModuleIso (h𝓛.powEquiv hgen n)).symm ≪≫
    AlgebraicGeometry.tildeSelf

/-- **The trivialization of `π^*ℒ^{⊗ n}` by the `n`-th power of a global generator.** For any
scheme `W` over `Spec R` the pullback of the `n`-th power of the twisting module is the structure
sheaf of `W`. -/
def pullbackTildeIsoUnit {W : Scheme.{u}} (f : W ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (AlgebraicGeometry.tildeOfModule R (𝓛 n)) ≅
      SheafOfModules.unit W.ringCatSheaf :=
  (Scheme.Modules.pullback f).mapIso (h𝓛.tildeIsoUnit hgen n) ≪≫
    Stacks.PullbackAlgebra.pullbackUnitIso f.toLRSHom.toShHom

end Stacks.GradedRing.IsTensorPowerFamily

end
