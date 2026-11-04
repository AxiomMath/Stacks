module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.FiniteSubmoduleExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafExact

/-!
# The sheaf `ℱ_N` attached to a discrete `π₁(X)`-module

Let `X` be a connected scheme with a geometric point `x` and `Λ` a finite ring. The sheaf
`ℱ_ρ` of `AlgebraicGeometry.representationSheaf` is attached to a *finite* `Λ`-module with a
continuous `π₁(X, x)`-action. This file extends it to every continuous discrete
`Λ`-`π₁(X, x)`-module `N`, as the filtered colimit

`ℱ_N = colim_{P ⊆ N} ℱ_P`

over the finite `π₁(X, x)`-stable submodules `P` of `N`
(`Stacks.ContinuousCohomology.finiteSubmoduleExtension`). The extension is exact and restricts
to `ℱ` on finite modules; it is built without any choice. In the proof of [Stacks, Tag 03VM] it
is what lets the right derived functors of invariants, which live on all discrete modules, be
compared with étale cohomology.

## Main definitions

* `AlgebraicGeometry.discreteRepresentationSheaf` — the functor `N ↦ ℱ_N`.
* `AlgebraicGeometry.discreteRepresentationSheafιIso` — `ℱ_N = ℱ_ρ` for `N` finite.

## Main results

* `AlgebraicGeometry.preservesFiniteLimits_discreteRepresentationSheaf` and
  `AlgebraicGeometry.preservesFiniteColimits_discreteRepresentationSheaf` — `N ↦ ℱ_N` is exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ]

/-- Étale module sheaves have colimits of the size of their sections, being a Grothendieck abelian
category. Stated on its own: instance search does not find it within its budget. -/
instance (priority := 3000) hasColimitsOfSize_etaleModules (Y : Scheme.{u}) :
    HasColimitsOfSize.{u + 1, u + 1} (Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ Y) :=
  IsGrothendieckAbelian.hasColimits (C := Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ Y)

/-- Filtered colimits of étale module sheaves are exact, the category being Grothendieck
abelian. -/
instance (priority := 3000) ab5OfSize_etaleModules (Y : Scheme.{u}) :
    AB5OfSize.{u + 1, u + 1} (Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ Y) :=
  IsGrothendieckAbelian.ab5OfSize (C := Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ Y)

/-- `ρ ↦ ℱ_ρ` is additive, being exact. -/
instance additive_representationSheaf : (representationSheaf.{u, 0} B X x Λ).Additive :=
  have := preservesFiniteLimits_representationSheaf.{u, 0} B X x Λ
  Functor.additive_of_preserves_binary_products _

/-- **The sheaf `ℱ_N` of a continuous discrete `Λ`-`π₁(X, x)`-module `N`**: the filtered colimit
of the sheaves `ℱ_P` of its finite `π₁(X, x)`-stable submodules `P`. -/
abbrev discreteRepresentationSheaf :
    Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x) ⥤
      Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ X.1 :=
  finiteSubmoduleExtension (representationSheaf.{u, 0} B X x Λ)

/-- **`ℱ_N = ℱ_ρ` for a finite `N`.** -/
def discreteRepresentationSheafιIso :
    finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x) ⋙
        discreteRepresentationSheaf B X x Λ ≅ representationSheaf.{u, 0} B X x Λ :=
  finiteSubmoduleExtensionιIso (representationSheaf.{u, 0} B X x Λ)

/-- `N ↦ ℱ_N` is additive. -/
instance additive_discreteRepresentationSheaf : (discreteRepresentationSheaf B X x Λ).Additive :=
  finiteSubmoduleExtension_additive (representationSheaf.{u, 0} B X x Λ)

/-- **`N ↦ ℱ_N` preserves finite limits.** -/
theorem preservesFiniteLimits_discreteRepresentationSheaf :
    PreservesFiniteLimits (discreteRepresentationSheaf B X x Λ) :=
  have : IsArtinianRing Λ := IsArtinianRing.of_finite Λ Λ
  have := preservesFiniteLimits_representationSheaf.{u, 0} B X x Λ
  have := preservesFiniteColimits_representationSheaf.{u, 0} B X x Λ
  preservesFiniteLimits_finiteSubmoduleExtension (representationSheaf.{u, 0} B X x Λ)

/-- **`N ↦ ℱ_N` preserves finite colimits.** -/
theorem preservesFiniteColimits_discreteRepresentationSheaf :
    PreservesFiniteColimits (discreteRepresentationSheaf B X x Λ) :=
  have : IsArtinianRing Λ := IsArtinianRing.of_finite Λ Λ
  have := preservesFiniteLimits_representationSheaf.{u, 0} B X x Λ
  have := preservesFiniteColimits_representationSheaf.{u, 0} B X x Λ
  preservesFiniteColimits_finiteSubmoduleExtension (representationSheaf.{u, 0} B X x Λ)

end AlgebraicGeometry

end
