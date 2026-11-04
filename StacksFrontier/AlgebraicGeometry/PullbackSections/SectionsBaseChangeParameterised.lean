module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs

/-!
# Degree-zero flat base change, parameterised over its scalar structures

`Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange` exhibits
`Γ(X', (g')^* F)` as `Γ(S', 𝒪_{S'}) ⊗_{Γ(S, 𝒪_S)} Γ(X, F)` for a flat base change of a
quasi-compact quasi-separated scheme over an affine base, with the algebra and module structures
on the tensor factors fixed as `Stacks.AlgebraicGeometry.SectionsBaseChange.baseAlgebra` and
`Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule`.

## Main results

* `Stacks.AlgebraicGeometry.SectionsBaseChange.isBaseChange_sections_baseChange`: **the theorem
  parameterised over its scalar structures.** The same statement with the algebra and module
  structures on the tensor factors taken as hypotheses, pinned down by their `algebraMap` and
  `smul` equations, and with the target read through an additive bijection.

## Implementation notes

The algebra and module structures on the tensor factors are hypotheses and the target is read
through an additive bijection, so that the statement can be instantiated at scalar structures that
are only propositionally `Stacks.AlgebraicGeometry.SectionsBaseChange.baseAlgebra` and
`Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule`, and at the sections of the pullback along
another factorisation of the same morphism, without rewriting an instance: identifying the
structures by `rw` leaves the instances of the tensor product out of reach of typeclass inference.
Every instance binder is named so that a caller can pass the instance it built positionally.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.FlatSectionsDescent
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.SectionsBaseChange

variable {S T X Y : Scheme.{u}}

/-- **Degree-zero flat base change, parameterised over its scalar structures.** Let `H` exhibit
`Y` as the pullback of `iX : X ⟶ S` along a flat morphism `q : T ⟶ S` of affine schemes, with `X`
quasi-compact and quasi-separated, and let `F` be a quasi-coherent `𝒪_X`-module. Give `Γ(T, ⊤)`
and `Γ(F, ⊤)` any `Γ(S, ⊤)`-algebra and `Γ(S, ⊤)`-module structures that act through `q.appLE`
and `iX.appLE`, and let `ψ` be an additive bijection from `Γ(p^*F, ⊤)` to a `Γ(T, ⊤)`-module `N`,
semilinear along `k.appLE ⊤ ⊤`. Then a `Γ(S, ⊤)`-linear map `ρ : Γ(F, ⊤) → N` which is `ψ` after
pulling sections back along `p` exhibits `N` as the base change of `Γ(F, ⊤)` to `Γ(T, ⊤)`.

This is `Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange` with
the scalar structures as parameters, pinned down by their `algebraMap` and `smul` equations,
instead of `Stacks.AlgebraicGeometry.SectionsBaseChange.baseAlgebra` and `baseModule`. -/
theorem isBaseChange_sections_baseChange
    {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T} (H : IsPullback p k iX q)
    [instAffS : IsAffine S] [instAffT : IsAffine T] [instFlat : Flat q]
    [instCpt : CompactSpace X] [instQS : QuasiSeparatedSpace X]
    (F : X.Modules) [instF : F.IsQuasicoherent]
    [instA : Algebra Γ(S, ⊤) Γ(T, ⊤)]
    (halg : ∀ r, algebraMap Γ(S, ⊤) Γ(T, ⊤) r =
      (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom r)
    [instM : Module Γ(S, ⊤) Γ(F, ⊤)]
    (hsmul : ∀ (r : Γ(S, ⊤)) (x : Γ(F, ⊤)),
      r • x = (iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom r • x)
    {N : Type u} [AddCommGroup N] [instNS : Module Γ(S, ⊤) N] [instNT : Module Γ(T, ⊤) N]
    [instTw : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) N]
    (ψ : Γ((Scheme.Modules.pullback p).obj F, ⊤) →+ N) (hψ : Function.Bijective ψ)
    (hψsmul : ∀ (b : Γ(T, ⊤)) (z : Γ((Scheme.Modules.pullback p).obj F, ⊤)),
      ψ ((k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom b • z) = b • ψ z)
    (ρ : Γ(F, ⊤) →ₗ[Γ(S, ⊤)] N)
    (hρ : ∀ a, ρ a = ψ (pullbackSectionsHom p F ⊤ ⊤ (le_preimage_top p ⊤) a)) :
    IsBaseChange Γ(T, ⊤) ρ := by
  obtain rfl : instA = baseAlgebra q := Algebra.algebra_ext _ _ halg
  obtain rfl : instM = baseModule iX F ⊤ := Module.ext' _ _ hsmul
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := baseAlgebra q
  let : Module Γ(S, ⊤) Γ(F, ⊤) := baseModule iX F ⊤
  let : Module Γ(S, ⊤) Γ((Scheme.Modules.pullback p).obj F, ⊤) :=
    baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) ⊤
  let : Module Γ(T, ⊤) Γ((Scheme.Modules.pullback p).obj F, ⊤) :=
    baseModule k ((Scheme.Modules.pullback p).obj F) ⊤
  have : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ((Scheme.Modules.pullback p).obj F, ⊤) :=
    baseTower H ((Scheme.Modules.pullback p).obj F) ⊤
  obtain ⟨e, he⟩ := exists_linearEquiv_sections_baseChange H F
  refine Stacks.FlatSectionsDescent.isBaseChange_of_bijective_liftBaseChange ρ ?_
  refine Stacks.FlatSectionsDescent.bijective_liftBaseChange_of_tmul ρ
    (ψ.comp e.toAddEquiv.toAddMonoidHom) (hψ.comp e.bijective) (fun b a => ?_)
  show ψ (e (b ⊗ₜ[Γ(S, ⊤)] a)) = b • ρ a
  rw [he b a, hρ a]
  exact hψsmul b _

end Stacks.AlgebraicGeometry.SectionsBaseChange

end
