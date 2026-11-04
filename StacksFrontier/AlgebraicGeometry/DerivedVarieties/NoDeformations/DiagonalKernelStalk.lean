module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernel
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.DerivedStalkHomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningQuasicoherent

/-!
# The derived stalk of the diagonal kernel at a point of the diagonal

Let `π : F ⟶ T` be a separated morphism, so that its diagonal `Δ : F ⟶ F ×_T F` is a closed
immersion, and let `y` be a point of `F`. This file computes the derived stalk of the diagonal
kernel `𝒪_Δ = RΔ_*𝒪_F` of [Stacks, Tag 0FYV] at the point `Δ(y)`: it is the cyclic module
`𝒪_{F ×_T F, Δ y} / ker Δ^♯_y` placed in degree zero.

This is the computation Case II of [Stacks, Tag 0G0R] runs: the hypothesis of 0G0R identifies the
derived restriction of the Fourier-Mukai kernel with `𝒪_Δ`, and what the Koszul machinery of
[Stacks, Tag 0G0N] must be handed is a degree-zero identification of a derived stalk. The ideal
`ker Δ^♯_y` is the one that [Stacks, Tag 0FDP] presents by a regular sequence, through
`AlgebraicGeometry.exists_isRegular_span_ker_stalkMap_diagonal_of_smooth`.

## Main results

* `AlgebraicGeometry.restrictScalarsIsoQuotientKer`: for a surjective homomorphism of commutative
  rings `ψ : B →+* A`, the ring `A` with scalars restricted along `ψ` is `B ⧸ ker ψ`.
* `AlgebraicGeometry.derivedStalkDiagonalKernelIsoSingle`: the derived stalk of the diagonal
  kernel at `Δ(y)`.

## Implementation notes

The three steps are: `Stacks.Thickenings.derivedPushforwardSingleIso`, which replaces
`RΔ_*(𝒪_F[0])` by `(Δ_*𝒪_F)[0]` — legitimate because `Δ` is a closed embedding;
`AlgebraicGeometry.derivedStalkSingleIso`, which computes the derived stalk of a module placed in
degree zero as its stalk placed in degree zero; and
`Stacks.Chow.stalkPushforwardStructureSheafLinearEquiv`, which identifies the stalk of `Δ_*𝒪_F` at
`Δ(y)` with the local ring `𝒪_{F,y}`, as a module over `𝒪_{F ×_T F, Δ y}` by restriction of
scalars along the stalk map. That stalk map is surjective, `Δ` being a closed immersion, so the
module is the quotient by its kernel.

The `Module` instance on `𝒪_{F,y}` over `𝒪_{F ×_T F, Δ y}` is the one
`Stacks.Chow.stalkPushforwardStructureSheafLinearEquiv` names in its own statement,
`Module.compHom` of the stalk map, which is also the instance
`ModuleCat.restrictScalars` puts on its value; the two agree by construction, so
the composite needs no transport.

## References

* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 0G0N](https://stacks.math.columbia.edu/tag/0G0N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **The target of a surjection, with scalars restricted, is the quotient by the kernel.** -/
def restrictScalarsIsoQuotientKer {B A : Type u} [CommRing B] [CommRing A] (ψ : B →+* A)
    (hψ : Function.Surjective ψ) :
    (ModuleCat.restrictScalars.{u, u, u} ψ).obj (ModuleCat.of A A) ≅
      ModuleCat.of B (B ⧸ RingHom.ker ψ) :=
  letI inst : Module B A := Module.compHom A ψ
  @LinearEquiv.toModuleIso B _ A (B ⧸ RingHom.ker ψ) _ _ inst _
    { toFun := fun a => (RingHom.quotientKerEquivOfSurjective hψ).symm a
      invFun := fun x => RingHom.quotientKerEquivOfSurjective hψ x
      left_inv := (RingHom.quotientKerEquivOfSurjective hψ).right_inv
      right_inv := (RingHom.quotientKerEquivOfSurjective hψ).left_inv
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => by
        have hmk : ∀ c : B, (RingHom.quotientKerEquivOfSurjective hψ).symm (ψ c) =
            Ideal.Quotient.mk (RingHom.ker ψ) c := by
          intro c
          rw [RingEquiv.symm_apply_eq]
          simp [RingHom.quotientKerEquivOfSurjective]
        obtain ⟨b, rfl⟩ := hψ a
        change (RingHom.quotientKerEquivOfSurjective hψ).symm (ψ r * ψ b) =
          Ideal.Quotient.mk (RingHom.ker ψ) r *
            (RingHom.quotientKerEquivOfSurjective hψ).symm (ψ b)
        rw [← map_mul ψ, hmk, hmk]
        exact map_mul (Ideal.Quotient.mk (RingHom.ker ψ)) r b }

variable {T F : Scheme.{u}} (π : F ⟶ T) [IsSeparated π]

/-- **The derived stalk of the diagonal kernel at a point of the diagonal.** For `π : F ⟶ T`
separated and `y` a point of `F`, the derived stalk of `𝒪_Δ = RΔ_*𝒪_F` at `Δ(y)` is the local
ring of `F ×_T F` there modulo the kernel of the stalk map of `Δ`, placed in degree zero. -/
def derivedStalkDiagonalKernelIsoSingle (y : F) :
    (derivedStalkFunctor ((Limits.pullback.diagonal π) y)).obj (diagonalKernel π) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u}
          ((Limits.pullback π π).presheaf.stalk ((Limits.pullback.diagonal π) y))) 0).obj
        (ModuleCat.of ((Limits.pullback π π).presheaf.stalk ((Limits.pullback.diagonal π) y))
          ((Limits.pullback π π).presheaf.stalk ((Limits.pullback.diagonal π) y) ⧸
            RingHom.ker ((Limits.pullback.diagonal π).stalkMap y).hom)) :=
  (derivedStalkFunctor ((Limits.pullback.diagonal π) y)).mapIso
      (Stacks.Thickenings.derivedPushforwardSingleIso
        (Limits.pullback.diagonal π).toLRSHom.toShHom
        (Limits.pullback.diagonal π).isClosedEmbedding (Stacks.Ample.unitModule F)) ≪≫
    derivedStalkSingleIso ((Limits.pullback.diagonal π) y) _ ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u}
        ((Limits.pullback π π).presheaf.stalk ((Limits.pullback.diagonal π) y))) 0).mapIso
      (LinearEquiv.toModuleIso
          (Stacks.Chow.stalkPushforwardStructureSheafLinearEquiv (Limits.pullback.diagonal π) y
            (Limits.pullback.diagonal π).isClosedEmbedding.isInducing) ≪≫
        restrictScalarsIsoQuotientKer ((Limits.pullback.diagonal π).stalkMap y).hom
          (SurjectiveOnStalks.stalkMap_surjective (Limits.pullback.diagonal π) y))

end AlgebraicGeometry

end
