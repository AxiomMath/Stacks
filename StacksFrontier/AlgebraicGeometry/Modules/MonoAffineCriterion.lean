module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness

/-!
# Monomorphy of a morphism of quasi-coherent modules is detected on global sections

On an affine scheme a morphism of quasi-coherent modules is invertible as soon as it is
invertible on global sections; that is
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ`. This file proves the
companion statement for monomorphy: a morphism of quasi-coherent modules on `Spec R` which is a
monomorphism on global sections is a monomorphism.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChange.mono_of_mono_comp_square`: in any category, two
  invertible edges and a monomorphic third edge of a commuting square make the fourth edge
  monomorphic.
* `Stacks.AlgebraicGeometry.AffineBaseChange.mono_of_mono_moduleSpecΓ`: **on an affine scheme a
  morphism of quasi-coherent modules which is a monomorphism on global sections is a
  monomorphism.**

## Implementation notes

The proof is the naturality square of
`AlgebraicGeometry.Scheme.Modules.fromTildeΓNatTrans` used in
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ`, with "three invertible
edges make the fourth invertible" weakened to "two invertible edges and a monomorphic third make
the fourth monomorphic". Two of the four edges are the components of that natural transformation
at the source and the target, invertible because those modules are quasi-coherent
(`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ`); the third is the image of the
morphism on global sections under `AlgebraicGeometry.tilde.functor`, and the one new input is
that this functor carries monomorphisms to monomorphisms. That follows from its exactness,
`AlgebraicGeometry.tilde.preservesFiniteLimits`, through
`CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`: a functor preserving limits
of shape `WalkingCospan` preserves monomorphisms. Full faithfulness of `tilde` — [Stacks, Tag
01I7] — would not do instead: a fully faithful functor *reflects* monomorphisms and need not
preserve them.

The two invertibility hypotheses of `mono_of_mono_comp_square` are explicit rather than
instance-implicit, for the same reason as in
`Stacks.AlgebraicGeometry.FlatBaseChange.isIso_of_isIso_comp_square`: at the use site in
`(Spec R).Modules` instance search compares the objects of the square at `instances`
transparency and the two spellings of the source of
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ` do not agree there, so they have to be supplied by
hand.

## References

* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChange

/-- **Two invertible edges and a monomorphic third make the fourth monomorphic.** If
`γ ≫ β = α ≫ ψ` with `α` and `β` invertible and `γ` a monomorphism, then `ψ` is a monomorphism,
being the composite `inv α ≫ γ ≫ β` of three monomorphisms. -/
theorem mono_of_mono_comp_square {D : Type*} [Category D] {P Q M N : D} {ψ : M ⟶ N}
    (α : P ⟶ M) (β : Q ⟶ N) (γ : P ⟶ Q) (hα : IsIso α) (hβ : IsIso β) (hγ : Mono γ)
    (w : γ ≫ β = α ≫ ψ) : Mono ψ := by
  have := hα
  have := hβ
  have := hγ
  rw [← IsIso.inv_hom_id_assoc α ψ, ← w]
  infer_instance

/-- **On an affine scheme a morphism of quasi-coherent modules which is a monomorphism on global
sections is a monomorphism.** -/
theorem mono_of_mono_moduleSpecΓ {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (h : Mono (moduleSpecΓFunctor.map φ)) : Mono φ := by
  have := h
  exact mono_of_mono_comp_square (Scheme.Modules.fromTildeΓ M) (Scheme.Modules.fromTildeΓ N)
    ((moduleSpecΓFunctor (R := R) ⋙ tilde.functor R).map φ)
    ((isQuasicoherent_iff_isIso_fromTildeΓ M).mp ‹_›)
    ((isQuasicoherent_iff_isIso_fromTildeΓ N).mp ‹_›)
    (Functor.map_mono (tilde.functor R) (moduleSpecΓFunctor.map φ))
    (Scheme.Modules.fromTildeΓNatTrans.naturality φ)

end Stacks.AlgebraicGeometry.AffineBaseChange

end
