module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartSourceGenerator

/-!
# Morphisms out of the pullback of an associated sheaf are determined on its canonical sections

`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartSourceGenerator` and
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ZeroSectionGenerator` read the two chart
identifications of [Stacks, Tag 0B3V] clause 3 on the *canonical global sections* of `M^~` pulled
back along `W ≅ Spec Γ(X, W)` — the unit of `f^* ⊣ f_*` applied to
`AlgebraicGeometry.tilde.toOpen M ⊤ m`. **This file is the extensionality principle that makes
those two formulas add up to an equation of morphisms**: two morphisms out of `f^*(M^~)` that
agree on all of them are equal.

Without it the generator formulas prove nothing about the clause. The reducers already in the
library do not apply:
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullbackSection` asks for agreement on the
pullback of *every* section of `M^~` over *every* open of `Spec Γ(X, W)`, of which the canonical
global sections are a vanishing fraction, and
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top` asks for agreement on every global
section of the pullback, which is not of the canonical form on the nose either.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_unit_toOpen`: **the reduction.**

## Implementation notes

Two adjunctions, one after the other, and no sheaf theory: the transpose of a morphism
`f^*(M^~) ⟶ N` under `f^* ⊣ f_*` is a morphism `M^~ ⟶ f_*N`, whose transpose under
`AlgebraicGeometry.tilde.adjunction` is an `R`-linear map out of `M`, and that map is precisely
`m ↦ (the canonical section at m)`. So the hypothesis *is* the equality of the twice-transposed
maps, applied to each `m`, and the proof is `LinearMap.ext` behind the two injectivities. The
opens are not transported: `f ⁻¹ᵁ ⊤` and `⊤` are the same open by definition, so the statement is
written at `⊤` and no `eqToHom` appears.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- **Morphisms out of the pullback of an associated sheaf are determined on its canonical global
sections.** Let `f : X ⟶ Spec R` and let `A` be an `R`-module. Two morphisms
`f^*(A^~) ⟶ N` that agree on the global section named by `a` — the unit of `f^* ⊣ f_*` applied to
`AlgebraicGeometry.tilde.toOpen A ⊤ a` — for every `a : A` are equal.

This is the form in which the chart computation of [Stacks, Tag 0B3V] clause 3 consumes its two
generator formulas, `Stacks.ProjectiveBundleConormal.restrictKernelIsoTilde_inv_unit_toOpen` and
`Stacks.ProjectiveBundleConormal.conormalZeroSectionTildeIso_hom_unit_toOpen`: both halves of the
chart identification land on `(ker p)^~` pulled back along `W ≅ Spec Γ(X, W)`, and this says that
naming the clause's map on the canonical sections of that sheaf names the map. -/
theorem hom_ext_of_unit_toOpen {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    {A : ModuleCat.{u} R} {N : X.Modules}
    {φ ψ : (Scheme.Modules.pullback f).obj (tilde A) ⟶ N}
    (h : ∀ a : A,
      φ.val.app (op (⊤ : X.Opens))
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (tilde A)).val.app (op ⊤)
            (tilde.toOpen A ⊤ a)) =
        ψ.val.app (op (⊤ : X.Opens))
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (tilde A)).val.app (op ⊤)
            (tilde.toOpen A ⊤ a))) :
    φ = ψ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv (tilde A) N).injective
  apply ((tilde.adjunction (R := R)).homEquiv A _).injective
  apply ModuleCat.hom_ext
  exact LinearMap.ext h

end Stacks.AlgebraicGeometry.ModuleLimits

end
