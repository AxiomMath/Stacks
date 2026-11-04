module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreFreeStalk
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreConditionSpecialCases
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalEquivalence
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.CompletionFiniteFreeStalks
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.ClosedImmersionStalkVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# Finite locally free adic systems have finite free stalks

Let `X` be a scheme with an ideal sheaf `ℐ`. An object `(ℱ_n)` of `Coh(X, ℐ)` is finite locally
free when each `ℱ_n` is the direct image of a finite locally free module on the closed subscheme
`Y_n` cut out by `ℐ^{n+1}` (`Stacks.Algebraization.IsFiniteLocallyFreeAdic`). This file proves
that the stalk of each `ℱ_n` at each point `y` of `X` is then a finite free module over
`𝒪_{X,y} / ℐ_y^{n+1}`. At a point of the support of `ℐ` this is the stalk of the finite locally
free module on `Y_n`, read over `𝒪_{Y_n,y} = 𝒪_{X,y} / ℐ_y^{n+1}`. Away from the support both
sides vanish.

In the standing situation of [Stacks, Tag 0EHC] this is the step that lets the essential
surjectivity half of [Stacks, Tag 0EKZ] be applied to the finite locally free objects of
`Coh(U, I𝒪_U)` themselves. That half is stated for the stalkwise form
`Stacks.Algebraization.HasFiniteFreeStalks`.

## Main results

* `Stacks.Algebraization.exists_linearEquiv_pi_stalk_of_pushforward_iso` — the stalk of a direct
  image from `Y_n` of a finite locally free module is finite free over `𝒪_{X,y} / ℐ_y^{n+1}`.
* `Stacks.Algebraization.hasFiniteFreeStalks_of_isFiniteLocallyFreeAdic` — a finite locally free
  object of `Coh(U, I𝒪_U)` has finite free stalks over the infinitesimal neighbourhoods.
* `Stacks.Algebraization.support_idealOnOpen_subset` — the support of `I𝒪_U` lies over `V(I)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-- **The stalk of a direct image of a finite locally free module from `Y_t` is finite free over
`𝒪_{X,y} / ℐ_y^t`.** Let `ℰ` be an `𝒪_X`-module isomorphic to the direct image of a finite
locally free module `𝒩` on the closed subscheme cut out by `ℐ^t`, with `t ≥ 1`. At a point `y`
of the support of `ℐ`, the stalk `ℰ_y` is the stalk of `𝒩` at the point over `y`. That stalk is
free of finite rank over `𝒪_{Y_t, y}`, which is `𝒪_{X,y} / ℐ_y^t`. Away from the support both
`ℰ_y` and `𝒪_{X,y} / ℐ_y^t` vanish. -/
theorem exists_linearEquiv_pi_stalk_of_pushforward_iso (J : X.IdealSheafData) {t : ℕ}
    (ht : t ≠ 0) (E : X.Modules) (N : (J ^ t).subscheme.Modules)
    (hN : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree N)
    (e : (Scheme.Modules.pushforward (J ^ t).subschemeι).obj N ≅ E) (y : X) :
    ∃ r : ℕ, Nonempty ((modulesStalkFunctor X y).obj E ≃ₗ[X.presheaf.stalk y]
      (Fin r → (X.presheaf.stalk y ⧸ IdealSheafData.stalk J y ^ t))) := by
  classical
  by_cases hy : y ∈ J.support
  · have hind : Topology.IsInducing (ConcreteCategory.hom ((J ^ t).subschemeι).base) :=
      (IsClosedImmersion.isClosedEmbedding ((J ^ t).subschemeι)).isInducing
    let z : (J ^ t).subscheme := idealPowSubschemePoint J ht y hy
    let _ : Module (X.presheaf.stalk y) (N.presheaf.stalk z) :=
      Module.compHom _ (((J ^ t).subschemeι).stalkMap z).hom
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N :=
      (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators N).mp hN
    obtain ⟨hfree, hfin⟩ := Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree N z
    obtain ⟨r, ⟨b⟩⟩ := @Stacks.FreeStalkQuotient.exists_linearEquiv_pi
      ((J ^ t).subscheme.presheaf.stalk z) _ (N.presheaf.stalk z) _ inferInstance hfree hfin
    let eRing : (X.presheaf.stalk y ⧸ IdealSheafData.stalk J y ^ t) ≃+*
        ((J ^ t).subscheme.presheaf.stalk z) :=
      (Ideal.quotEquivOfEq (IdealSheafData.stalk_pow J t y).symm).trans
        (IdealSheafData.subschemeStalkQuotEquiv (J ^ t) z)
    have heR : ∀ a : X.presheaf.stalk y,
        eRing (Ideal.Quotient.mk (IdealSheafData.stalk J y ^ t) a) =
          ((J ^ t).subschemeι).stalkMap z a := fun a =>
      IdealSheafData.subschemeStalkQuotEquiv_mk (J ^ t) z a
    let f₀ : ((Scheme.Modules.pushforward ((J ^ t).subschemeι)).obj N).presheaf.stalk y
        ≃ₗ[X.presheaf.stalk y] N.presheaf.stalk z :=
      stalkPushforwardModuleLinearEquiv ((J ^ t).subschemeι) N z hind
    let f₁ : (modulesStalkFunctor X y).obj E ≃ₗ[X.presheaf.stalk y] N.presheaf.stalk z :=
      ((modulesStalkFunctor X y).mapIso e).toLinearEquiv.symm.trans f₀
    let f₂ : N.presheaf.stalk z ≃+
        (Fin r → (X.presheaf.stalk y ⧸ IdealSheafData.stalk J y ^ t)) :=
      b.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => eRing.symm.toAddEquiv)
    refine ⟨r, ⟨{ (f₁.toAddEquiv.trans f₂) with map_smul' := ?_ }⟩⟩
    intro c m
    funext i
    show eRing.symm (b (f₁ (c • m)) i) = c • eRing.symm (b (f₁ m) i)
    rw [f₁.map_smul]
    show eRing.symm (b ((((J ^ t).subschemeι).stalkMap z c) • f₁ m) i) = _
    rw [b.map_smul, Pi.smul_apply, smul_eq_mul, map_mul, ← heR, RingEquiv.symm_apply_apply,
      Algebra.smul_def]
    rfl
  · have htop : IdealSheafData.stalk J y ^ t = ⊤ := by
      rw [(Stacks.Divisors.stalk_eq_top_iff_notMem_support J y).mpr hy, Ideal.top_pow]
    have : Subsingleton (X.presheaf.stalk y ⧸ IdealSheafData.stalk J y ^ t) :=
      Ideal.Quotient.subsingleton_iff.mpr htop
    have hrange : y ∉ Set.range (ConcreteCategory.hom ((J ^ t).subschemeι).base) := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow J t ht]
      exact hy
    have : Subsingleton ((modulesStalkFunctor X y).obj
        ((Scheme.Modules.pushforward (J ^ t).subschemeι).obj N)) :=
      subsingleton_stalk_pushforward_of_notMemRange' ((J ^ t).subschemeι) N y hrange
    have : Subsingleton ((modulesStalkFunctor X y).obj E) :=
      ((modulesStalkFunctor X y).mapIso e).toLinearEquiv.symm.toEquiv.subsingleton
    exact ⟨0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩

/-- **A finite locally free object of `Coh(U, I𝒪_U)` has finite free stalks.** In the standing
situation of [Stacks, Tag 0EHC], let `(ℱ_n)` be a coherent `I𝒪_U`-adic system on `U` each of
whose terms is the direct image of a finite locally free module on the closed subscheme cut out
by `(I𝒪_U)^{n+1}`. Then the stalk of `ℱ_n` at every point `y` of `U` is finite free over
`𝒪_{U,y} / (I𝒪_U)_y^{n+1}`. -/
theorem hasFiniteFreeStalks_of_isFiniteLocallyFreeAdic (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hF : IsFiniteLocallyFreeAdic (idealOnOpen S) F) : HasFiniteFreeStalks S F := by
  intro m y
  obtain ⟨N, hN, ⟨e⟩⟩ := hF m
  exact exists_linearEquiv_pi_stalk_of_pushforward_iso (idealOnOpen S) (Nat.succ_ne_zero m)
    _ N hN e y

/-- **The support of `I𝒪_U` lies over `V(I)`.** In the standing situation of
[Stacks, Tag 0EHC], a point of `U` where the ideal sheaf `I𝒪_U` does not generate the unit ideal
maps into the closed subscheme `Y = V(I)` of `X`. So an open neighbourhood of `U ∩ Y` in `U`
contains the support of `I𝒪_U`. -/
theorem support_idealOnOpen_subset (S : AlgebraizationSituation.{u}) :
    ((idealOnOpen S).support : Set S.U.toScheme) ⊆ S.U.ι.base ⁻¹' Set.range S.Yι.base := by
  rw [idealOnOpen_eq_ker_comap, Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_preimage, Scheme.Hom.support_ker]
  rw [(IsClosedImmersion.isClosedEmbedding S.Yι).isClosed_range.closure_eq]

end Stacks.Algebraization

end
