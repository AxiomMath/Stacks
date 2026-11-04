module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperKunneth.CompositeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperKunneth.BoundedBelowInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointProjectionFormulaBoundedBelow.Main
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.BoundedBelowTorsionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperBaseChangeUnboundedBoundedBelow
import StacksCore.Tactic.StacksAttribute

/-!
# Künneth for a proper factor over a separably closed field (Stacks 0F14 (1))

Let `k` be a separably closed field, `X` a proper scheme over `k` and `Y` a quasi-compact and
quasi-separated scheme over `k`, with structure morphisms `f : X ⟶ Spec k` and `g : Y ⟶ Spec k`
and projections `pr₁ : X ×_k Y ⟶ X`, `pr₂ : X ×_k Y ⟶ Y`. For `E ∈ D⁺(X_étale)` with torsion
cohomology sheaves and `K ∈ D⁺(Y_étale)`, [Stacks, Tag 0F14] (1) asserts

`RΓ(X ×_k Y, pr₁⁻¹E ⊗^L_ℤ pr₂⁻¹K) = RΓ(X, E) ⊗^L_ℤ RΓ(Y, K)`.

Over `Spec k`, `k` separably closed, global sections identify sheaves on `(Spec k)_étale` with
abelian groups (`Stacks.EtaleCohomology.etalePointDerivedEquivalence`), and the derived direct
images `Rf_*`, `Rg_*` and `R(pr₂ ≫ g)_*` to `Spec k` are `RΓ(X, -)`, `RΓ(Y, -)` and
`RΓ(X ×_k Y, -)`. The statement is the invertibility of the Künneth map
`Rf_*E ⊗^L Rg_*K ⟶ R(pr₂ ≫ g)_*(pr₁⁻¹E ⊗^L pr₂⁻¹K)` of
`Stacks.EtaleCohomology.etaleKunnethCompositeMap` on `D((Spec k)_étale, ℤ)`.

## The proof

The source's. The Künneth map is the composite of
* the projection map for `g` at `(K, Rf_*E)`, invertible by the projection formula to a
  separably closed point for bounded below objects over `ℤ` (the point case of
  [Stacks, Tag 0F0E],
  `Stacks.EtaleCohomology.isIso_etalePushforwardProjectionMap_of_isGE_of_isSepClosed`),
  `Rf_*E` being bounded below;
* the base change map `g⁻¹Rf_*E ⟶ Rpr₂_*pr₁⁻¹E`, invertible by proper base change
  ([Stacks, Tag 0DDE],
  `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isGE_of_isProper`);
* the projection map for the proper `pr₂` at `(pr₁⁻¹E, K)`, invertible by [Stacks, Tag 0F0F],
  `pr₁⁻¹E` being bounded below with torsion cohomology sheaves;
* the Leray isomorphism `R(pr₂ ≫ g)_* = Rg_* ∘ Rpr₂_*`.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleKunnethCompositeMap_of_isGE_of_isProper`:
  **[Stacks, Tag 0F14] (1)**.

## References

* [Stacks Project, Tag 0F14](https://stacks.math.columbia.edu/tag/0F14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- **[Stacks, Tag 0F14] (1).** Let `k` be a separably closed field, `f : X ⟶ Spec k` proper and
`g : Y ⟶ Spec k` with `Y` quasi-compact and quasi-separated. Let `E ∈ D⁺(X_étale)` have torsion
cohomology sheaves and `K ∈ D⁺(Y_étale)`. Then the Künneth map
`RΓ(X, E) ⊗^L_ℤ RΓ(Y, K) = Rf_*E ⊗^L_ℤ Rg_*K ⟶ R(pr₂ ≫ g)_*(pr₁⁻¹E ⊗^L_ℤ pr₂⁻¹K)
= RΓ(X ×_k Y, pr₁⁻¹E ⊗^L_ℤ pr₂⁻¹K)` in `D((Spec k)_étale, ℤ) = D(ℤ)` is an isomorphism. -/
@[stacks 0F14 "(1); on D((Spec k)_et, ℤ), which global sections identify with D(ℤ) for k
separably closed, so that the direct images to Spec k are the derived global sections"]
theorem isIso_etaleKunnethCompositeMap_of_isGE_of_isProper (k : Type u) [Field k]
    [IsSepClosed k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (g : Y ⟶ Spec (.of k)) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (E : DerivedCategory (EtaleModules.{u, 0} ℤ X)) (a : ℤ) (hE : E.IsGE a)
    (hT : ∀ n, IsTorsionEtaleModule.{u, 0} ℤ X ((DerivedCategory.homologyFunctor _ n).obj E))
    (K : DerivedCategory (EtaleModules.{u, 0} ℤ Y)) (b : ℤ) (hK : K.IsGE b) :
    IsIso (etaleKunnethCompositeMap.{u, 0} ℤ f g (pullback.fst f g) (pullback.snd f g)
      pullback.condition E K) := by
  have : QuasiCompact g := (quasiCompact_iff_compactSpace g).2 inferInstance
  exact isIso_etaleKunnethCompositeMap _ _ _ _ _ _ E K
    (isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isGE_of_isProper ℤ f
      (IsPullback.of_hasPullback f g) E a hE hT)
    (isIso_etalePushforwardProjectionMap_of_isGE_of_isSepClosed k g K b hK _ a
      (isGE_etaleModuleDerivedDirectImageUnbounded_obj ℤ f E a hE))
    (isIso_etalePushforwardProjectionMap_of_isProper_of_isGE (pullback.snd f g) _ a
      (isGE_etaleModuleDerivedInverseImage_obj ℤ _ E a hE)
      (isTorsionEtaleModule_homology_etaleModuleDerivedInverseImage_obj ℤ _ E hT) K b hK)

end Stacks.EtaleCohomology

end
