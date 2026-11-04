module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCohomologyBridge

/-!
# Stacks 08F6 with its carried hypothesis moved to the abelian-sheaf level

`AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower` — **Stacks 08F6**, that an object
`E` of `D_QCoh(𝒪_X)` on an algebraic space is a derived limit of the tower `n ↦ τ_{≥ -n} E` of
its canonical truncations from below — carries as an explicit hypothesis `h03DW` the vanishing

`R^p Γ(U, M) = 0` for `p > 0`, `M` a quasi-coherent `𝒪_X`-module and `U` an affine étale chart,

where `R^p Γ(U, -)` is the `p`-th right derived functor of `CategoryTheory.SheafOfModules.
evaluation` at `U`.  That is a statement about *module-valued* cohomology, whereas Stacks 03DW,
the result the source cites for it, and every Čech-theoretic criterion in this tree that could
discharge it, are statements about *abelian sheaf* cohomology, namely `CategoryTheory.Sheaf.H'`.

This file performs that one change of level, on the small étale site of an algebraic space.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isIso_of_isDerivedLimit_truncGETower_of_isZero_H'`:
  **Stacks 08F6 with `h03DW` replaced by the abelian-sheaf vanishing.**

## Implementation notes

The change of level is
`AlgebraicGeometry.Space.SmallEtale.chartwise_isZero_rightDerived_moduleEvaluation_of_isZero_H'`,
and the module universe is pinned to the universe `u` of the structure rings, which is where the
comparison lives: `AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower` leaves it free,
so this is the `m = u` instance of it and nothing more.

`HasExt` for the abelian sheaves on the site is carried as an instance hypothesis rather than
discharged, because it is needed to *state* the hypothesis `hab` and the binder has to precede
it.  It is not a restriction: `AlgebraicGeometry.Space.hasExt_sheaf_smallEtale` proves it,
and a caller introduces it with one type ascription at the projection spelling of the topology.

What this does **not** reach is the `h03DWab` of the two clauses of Stacks 0D3E in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedLimits.lean`.  Those phrase the same
mathematical vanishing through `Stacks.Cohomology.SiteInverseLimits.sectionsFunctor`, which is
`CategoryTheory.SheafOfModules.evaluation` *composed with* the forgetful functor
`ModuleCat ⥤ AddCommGrpCat`, and the right derived functors of a composite are not the composite
of the right derived functors without knowing that the second factor is exact and preserves
injectives.  That comparison is a separate piece of work and is not done here.

## References

* [Stacks Project, Tag 08F6](https://stacks.math.columbia.edu/tag/08F6)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.Cohomology.AcyclicCover.evaluation_additive

universe u

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 08F6 with its carried hypothesis moved to the abelian-sheaf level.**

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `E` be an object of
`D_QCoh(𝒪_X)`.  If the cohomology of the underlying abelian sheaf of every quasi-coherent
`𝒪_X`-module vanishes in every positive degree over every affine étale chart, then the canonical
map from `E` to a derived limit of the tower `n ↦ τ_{≥ -n} E` of canonical truncations from
below is an isomorphism.

This is `AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower` at module universe `u`,
with its hypothesis `h03DW` supplied by
`AlgebraicGeometry.Space.SmallEtale.chartwise_isZero_rightDerived_moduleEvaluation_of_isZero_H'`.
The covering hypothesis `hcover` — that the affine étale charts cover the small étale site — is
still carried, as it is there. -/
theorem isIso_of_isDerivedLimit_truncGETower_of_isZero_H'
    [HasExt.{u + 1} (Sheaf (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u})]
    (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) q).obj E).IsQuasicoherentOnSite)
    (hcover : (smallEtaleRingedSite B S hS F hF).J.HasEnoughObjects
      (IsAffineChart B S hS F))
    (hab : ∀ U : SmallEtale B S hS F, IsAffineChart B S hS F U →
      ∀ M : Modules.{u, u} B S hS F hF, M.IsQuasicoherentOnSite → ∀ p : ℕ, 0 < p →
        IsZero (Sheaf.H'.{u + 1} ((SheafOfModules.toSheaf.{u}
          (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj M) p U))
    [HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (Modules.{u, u} B S hS F hF) E).obj ⟨n⟩]
    (L : DerivedCategory (Modules.{u, u} B S hS F hF))
    (c : E ⟶ L)
    (pr : L ⟶ ∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (Modules.{u, u} B S hS F hF) E).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (Modules.{u, u} B S hS F hF) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hL : Triangle.mk pr (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
        (Modules.{u, u} B S hS F hF) E).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
          (Modules.{u, u} B S hS F hF) E).obj ⟨n⟩) (n + 1) ≫
          (Stacks.DerivedLimit.truncGETower
            (Modules.{u, u} B S hS F hF) E).map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (Modules.{u, u} B S hS F hF)))
    (hc : ∀ n : ℕ, c ≫ pr ≫ Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (Modules.{u, u} B S hS F hF) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c := by
  have := enoughInjectives_modules B S hS F hF
  exact isIso_of_isDerivedLimit_truncGETower B S hS F hF E hE hcover
    (chartwise_isZero_rightDerived_moduleEvaluation_of_isZero_H' B S hS F hF hab)
    L c pr δ hL hc

end AlgebraicGeometry.Space.SmallEtale

end
