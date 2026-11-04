module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardCoherentProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound

/-!
# A uniform bound on the derived direct image of bounded complexes

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `N` a natural number such that
`R^p f_* 𝓕 = 0` for every quasi-coherent `𝒪_X`-module `𝓕` and every `p ≥ N` — by Stacks 073G
such an `N` exists for a quasi-compact and quasi-separated `f` with quasi-compact target, and
works for every base change of `f`.  Then for every bounded object `L` of `D(𝒪_X)` with
quasi-coherent cohomology sheaves vanishing above `c`, the derived direct image `Rf_*L` has no
cohomology in degrees `≥ c + N`.

The proof is an induction along the truncation triangles `τ^{<c}L → L → H^c(L)[-c]` of the
canonical t-structure, using that `H^m(Rf_*(𝓕[-c])) = R^{m-c}f_*𝓕`.

This is the bound which, in the proof of Stacks 08IS, controls the part of `E ⊗_A σ^{≥k}R`
in low degrees after the derived direct image.

## Main results

* `AlgebraicGeometry.Space.isZero_homology_derivedModulePushforward_of_isLE`: the bound.

## References

* [Stacks Project, Tag 073G](https://stacks.math.columbia.edu/tag/073G)
* [Stacks Project, Tag 08IS](https://stacks.math.columbia.edu/tag/08IS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

attribute [local instance] isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The derived direct image of a bounded complex with quasi-coherent cohomology has bounded
amplitude above.**  If `R^p f_* 𝓕 = 0` for all quasi-coherent `𝓕` and `p ≥ N`, and `L` is bounded
with quasi-coherent cohomology vanishing above `c`, then `H^i(Rf_*L) = 0` for `i ≥ c + N`. -/
theorem isZero_homology_derivedModulePushforward_of_isLE (f : X ⟶ Y) (N : ℕ)
    (hN : ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite → ∀ p : ℕ, N ≤ p →
      have := hasInjectiveResolutions_modules B S hS X.1 X.2
      IsZero (((modulePushforward B S hS f).rightDerived p).obj F))
    (a : ℤ) : ∀ (n : ℕ) (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)), L.IsGE a →
      L.IsLE (a + n) →
      (∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj L).IsQuasicoherentOnSite) →
      ∀ i : ℤ, a + n + N ≤ i →
        IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
          ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj L)) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  -- the case of one module placed in degree `c`
  have hsingle : ∀ (M : Modules.{u, u} B S hS X.1 X.2), M.IsQuasicoherentOnSite → ∀ (c i : ℤ),
      c + N ≤ i → IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
        ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
          ((DerivedCategory.singleFunctor _ c).obj M))) := by
    intro M hM c i hi
    obtain ⟨p, hp⟩ : ∃ p : ℕ, i - c = p := ⟨(i - c).toNat, by omega⟩
    exact (hN M hM p (by omega)).of_iso
      (homologyDerivedModulePushforwardSingleIso B S hS f M c i p hp)
  -- an object concentrated in degree `c`
  have hconc : ∀ (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (c : ℤ), K.IsGE c →
      K.IsLE c → ((DerivedCategory.homologyFunctor _ c).obj K).IsQuasicoherentOnSite →
      ∀ i : ℤ, c + N ≤ i →
        IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
          ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj K)) := by
    intro K c hGE hLE hqc i hi
    obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K c
    have hM : M.IsQuasicoherentOnSite :=
      SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((DerivedCategory.homologyFunctor _ c).mapIso e ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso _ c).app M) hqc
    exact (hsingle M hM c i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso
        ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).mapIso e))
  intro n
  induction n with
  | zero =>
    intro L hGE hLE hqc i hi
    exact hconc L a hGE (by simpa using hLE) (hqc a) i (by simpa using hi)
  | succ n ih =>
    intro L hGE hLE hqc i hi
    have hcast : a + ((n + 1 : ℕ) : ℤ) = a + (n : ℤ) + 1 := by push_cast; ring
    rw [hcast] at hLE hi
    set c := a + (n : ℤ) + 1 with hc
    have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished c L
    have hT' :=
      (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).map_distinguished _ hT
    have hex :=
      (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map_distinguished_exact
        _ hT'
    have := hGE
    have := hLE
    -- the truncation below `c`
    have h₁ : IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
        ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
          ((DerivedCategory.TStructure.t.truncLT c).obj L))) := by
      refine ih _ inferInstance
        (DerivedCategory.TStructure.t.isLE_truncLT_obj L c (a + (n : ℤ)) (by omega))
        (fun q => ?_) i (by omega)
      by_cases hq : q < c
      · have : IsIso ((DerivedCategory.homologyFunctor _ q).map
            ((DerivedCategory.TStructure.t.truncLTι c).app L)) :=
          DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _ hT q c inferInstance hq
        exact SheafOfModules.IsQuasicoherentOnSite.of_iso
          (asIso ((DerivedCategory.homologyFunctor _ q).map
            ((DerivedCategory.TStructure.t.truncLTι c).app L))).symm (hqc q)
      · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
          (DerivedCategory.isZero_of_isLE _ (c - 1) q (by omega))
    -- the truncation above `c`
    have h₃ : IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
        ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
          ((DerivedCategory.TStructure.t.truncGE c).obj L))) := by
      have hπ : IsIso ((DerivedCategory.homologyFunctor _ c).map
          ((DerivedCategory.TStructure.t.truncGEπ c).app L)) :=
        DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ _ hT c (c - 1) inferInstance (by omega)
      refine hconc _ c inferInstance inferInstance ?_ i (by omega)
      exact SheafOfModules.IsQuasicoherentOnSite.of_iso
        (asIso ((DerivedCategory.homologyFunctor _ c).map
          ((DerivedCategory.TStructure.t.truncGEπ c).app L))) (hqc c)
    exact hex.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

end AlgebraicGeometry.Space

end
