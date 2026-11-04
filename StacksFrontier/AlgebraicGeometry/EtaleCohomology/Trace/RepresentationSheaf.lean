module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Modules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite

/-!
# The sheaf `ℱ_ρ` attached to a continuous representation of `π₁`

Let `X` be a connected scheme with a geometric point `x`, let `Λ` be a finite ring, and let
`ρ : π₁(X, x) → Aut_Λ(M)` be a continuous action on a finite `Λ`-module `M`. The Trace Formula
chapter writes `ℱ_ρ` for the locally constant sheaf of `Λ`-modules on `X_étale` attached to `ρ`
(Section 03VJ). This file constructs it, as a functor of `ρ`, with values in the sheaves of
`Λ`-modules on Mathlib's small étale site, which is where compactly supported cohomology
(Tag 0GJZ) is defined.

## Main definitions

* `AlgebraicGeometry.representationSheaf` — the functor `ρ ↦ ℱ_ρ`.
* `AlgebraicGeometry.geometricRepresentationSheaf` — the functor `ρ ↦ ℱ_ρ|_{X_K}`, the
  restriction of `ℱ_ρ` to the base change `X_K = X ×_k K` along the projection `X_K ⟶ X`. For
  `K = k^{sep}` this is the sheaf whose compactly supported cohomology Tag 03VK computes.

## Implementation notes

`ℱ_ρ` is the image of `ρ` under the inverse of Tag 0DV5 (3),
`AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalence`. That equivalence lives on
the size-bounded small étale site `AlgebraicGeometry.SmallEtale.topology B X` of a big étale
site `B` containing `X`, with module universe `u + 1`. Two canonical comparisons carry it to
`Stacks.EtaleCohomology.EtaleModules`. The universe lift `ModuleCat.uliftFunctor` raises the
coefficients to `max (u + 1) r`. Then `AlgebraicGeometry.SmallEtale.sheafEquiv`, the
dense-subsite equivalence between the two models of the small étale site, moves the sheaf to
Mathlib's site. Both comparisons are equivalences or fully faithful, so no information about
`ρ` is lost.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type r) [Ring Λ] [Finite Λ]

/-- **The sheaf `ℱ_ρ` of a continuous representation of `π₁`.** It sends a finite `Λ`-module
`M` with a continuous action `ρ` of `π₁(X, x)` to the finite type locally constant sheaf of
`Λ`-modules on `X_étale` that corresponds to it under Tag 0DV5 (3). The sheaf is read on
Mathlib's small étale site, with coefficients in `ModuleCat.{max (u + 1) r} Λ`. -/
public def representationSheaf :
    FiniteTypeContinuousModule.{r, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x) ⥤
      Stacks.EtaleCohomology.EtaleModules.{u, r} Λ X.1 :=
  (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse ⋙
    ObjectProperty.ι _ ⋙
    sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.uliftFunctor.{r, u + 1} Λ) ⋙
    (@SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{max (u + 1) r} Λ) _
      (Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize.{u, u, r, max (u + 1) r} Λ)).functor

variable {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (K : Type u) [Field K] [Algebra k K]

/-- **The restriction of `ℱ_ρ` to the base change `X_K = X ×_k K`.** It is the inverse image of
`AlgebraicGeometry.representationSheaf` along the projection `X_K ⟶ X`, for sheaves of
`Λ`-modules on Mathlib's small étale sites. The source writes `ℱ_ρ` for this sheaf on
`X_{k̄}` as well. -/
public def geometricRepresentationSheaf :
    FiniteTypeContinuousModule.{r, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x) ⥤
      Stacks.EtaleCohomology.EtaleModules.{u, r} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) :=
  representationSheaf B X x Λ ⋙
    Stacks.EtaleCohomology.etaleModuleInverseImage.{u, r} Λ
      (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))

end AlgebraicGeometry

end
