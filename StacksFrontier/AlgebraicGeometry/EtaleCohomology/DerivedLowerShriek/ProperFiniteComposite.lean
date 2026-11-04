module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.QuasiFiniteHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.HigherDirectImageExtendScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstantCohomology

/-!
# `Rf_!` of a constant sheaf along a proper family followed by a finite morphism

Let `q̄ : Ȳ ⟶ T` be proper and `t : T ⟶ V` finite and of finite presentation, in a big étale site
`B`, and let `Λ` be a Noetherian ring and `M` a finite `Λ`-module annihilated by an integer
`m > 0`. If `R^q q̄_* 𝐙/ℓ` is constructible for every prime `ℓ` and every `q` (Stacks 0GKV for
`q̄`), then every cohomology sheaf of `R(t ∘ q̄)_! M`, computed through the identity
compactification of the proper morphism `t ∘ q̄`, is constructible.

This is the last step of the proof of Stacks 0GKX: `R(Ȳ → V)_! M = R(T → V)_! R(Ȳ → T)_! M`
(Stacks 0F7J, here the Leray isomorphism `R(t ∘ q̄)_* = Rt_* ∘ Rq̄_*` of
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageComp`, as both compactifications are
identities), the cohomology sheaves of `Rq̄_* M` are constructible by Stacks 0GKW
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_rightDerived_constantSheaf_of_zmod`), and
`Rt_*` keeps constructible cohomology (Stacks 0GK3 for a finite morphism,
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_of_isFinite`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) {Ybar T V : B.Scheme} (qbar : Ybar ⟶ T) (t : T ⟶ V)
  [IsProper (B.inclusion.map qbar)] [IsFinite (B.inclusion.map t)]
  [LocallyOfFinitePresentation (B.inclusion.map t)] (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]

/-- Being zero or isomorphic to a fixed object `X` is invariant under isomorphism. -/
private theorem isZero_or_nonempty_iso_of_iso {C : Type*} [Category C] [Preadditive C]
    {X F G : C} (e : G ≅ F) (h : IsZero F ∨ Nonempty (F ≅ X)) :
    IsZero G ∨ Nonempty (G ≅ X) :=
  h.elim (fun h => Or.inl (h.of_iso e)) (fun ⟨e'⟩ => Or.inr ⟨e ≪≫ e'⟩)

/-- **`R(t ∘ q̄)_! K` is constructible for `K` with constant cohomology**, for `q̄` proper with
`R^q q̄_* 𝐙/ℓ` constructible and `t` finite of finite presentation, through the identity
compactification of the proper morphism `t ∘ q̄`: every cohomology sheaf of `K` is zero or the
constant sheaf on a finite module `M` killed by `m > 0`. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_ofProper_comp_isFinite_of_hasConstantCohomology
    (hℓ : ∀ ℓ : ℕ, ℓ.Prime → ∀ q : ℕ, IsBigSiteConstructibleEtaleModule B T (ZMod ℓ)
      (rightDerivedConstantUnit (B.inclusion.map qbar) q (ZMod ℓ)))
    (m : ℕ) (hm : 0 < m) (M : ModuleCat.{u + 1} Λ) (hM : Module.Finite Λ M)
    (hmM : ∀ x : M, m • x = 0) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Ybar.obj))
    (hK : HasConstantCohomologyPlus Λ M K) (n : ℤ) :
    IsBigSiteConstructibleEtaleModule B V Λ ((DerivedCategory.Plus.homologyFunctor _ n).obj
      ((derivedLowerShriek.{u, 0} (B.inclusion.map qbar ≫ B.inclusion.map t)
        (CompactificationOf.ofProper _) Λ).obj K)) := by
  let cM := (constantSheaf Ybar.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let L := (etaleModuleDerivedExtensionByZero.{u, 0} Λ (𝟙 Ybar.obj)).obj K
  -- the cohomology of `L = (𝟙)_! K` is that of `K`
  have hL : ∀ q : ℤ, IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj L) ∨
      Nonempty ((DerivedCategory.Plus.homologyFunctor _ q).obj L ≅ cM) := by
    intro q
    obtain ⟨e⟩ := nonempty_homology_etaleModuleDerivedExtensionByZero_iso B (𝟙 Ybar.obj)
      (CompactificationOf.ofProper (𝟙 Ybar.obj)) Λ K q
    let e' := e ≪≫ (etaleModuleExtensionByZeroIdIso Λ Ybar.obj).app _
    exact isZero_or_nonempty_iso_of_iso e' (hK q)
  -- the cohomology sheaves of `Rq̄_* L` are constructible, by Stacks 0GKW
  have : IsSeparated (B.inclusion.map qbar) := IsProper.toIsSeparated
  have : UniversallyClosed (B.inclusion.map qbar) := IsProper.toUniversallyClosed
  have : QuasiCompact (B.inclusion.map qbar) := instQuasiCompactOfUniversallyClosed _
  have : QuasiSeparated (B.inclusion.map qbar) :=
    IsSeparated.instQuasiSeparated (B.inclusion.map qbar)
  have hQT := isWeakSerreClass_isBigSiteConstructibleEtaleModule B T Λ
  let P : ObjectProperty (EtaleModules.{u, 0} Λ Ybar.obj) := fun F =>
    IsZero F ∨ Nonempty (F ≅ cM)
  have hP : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h => isZero_or_nonempty_iso_of_iso e.symm h⟩
  have h₁ : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B T Λ
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (B.inclusion.map qbar)).obj L)) := fun q =>
    (Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj
      (etaleModuleDirectImage.{u, 0} Λ (B.inclusion.map qbar)) P
      (IsBigSiteConstructibleEtaleModule B T Λ) (fun F hF p => hF.elim
        (fun h => isConstructibleEtaleModule_of_isZero B Λ T
          (((etaleModuleDirectImage.{u, 0} Λ (B.inclusion.map qbar)).rightDerived p).map_isZero h))
        (fun ⟨e⟩ => IsBigSiteConstructibleEtaleModule.of_iso B Λ
          (((etaleModuleDirectImage.{u, 0} Λ (B.inclusion.map qbar)).rightDerived p).mapIso e).symm
          (isConstructibleEtaleModule_rightDerived_constantSheaf_of_zmod B (B.inclusion.map qbar) Λ
            hℓ m hm M hM hmM p)))
      L hL).2 q
  -- Leray: `R(t ∘ q̄)_* L = Rt_*(Rq̄_* L)`, and `Rt_*` keeps constructible cohomology
  exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
    ((DerivedCategory.Plus.homologyFunctor _ n).mapIso
      ((etaleModuleDerivedDirectImageComp.{u, 0} Λ (B.inclusion.map qbar) (B.inclusion.map t)
        (B.inclusion.map qbar ≫ B.inclusion.map t) rfl).app L).symm)
    (isConstructibleEtaleModule_homology_derivedDirectImage_of_isFinite B Λ t _ h₁ n)

/-- **`R(t ∘ q̄)_! M` is constructible**, for `q̄` proper with `R^q q̄_* 𝐙/ℓ` constructible and `t`
finite of finite presentation, through the identity compactification of the proper morphism
`t ∘ q̄`. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_ofProper_comp_isFinite
    (hℓ : ∀ ℓ : ℕ, ℓ.Prime → ∀ q : ℕ, IsBigSiteConstructibleEtaleModule B T (ZMod ℓ)
      (rightDerivedConstantUnit (B.inclusion.map qbar) q (ZMod ℓ)))
    (m : ℕ) (hm : 0 < m) (M : ModuleCat.{u + 1} Λ) (hM : Module.Finite Λ M)
    (hmM : ∀ x : M, m • x = 0) (n : ℤ) :
    IsBigSiteConstructibleEtaleModule B V Λ ((DerivedCategory.Plus.homologyFunctor _ n).obj
      ((derivedLowerShriek.{u, 0} (B.inclusion.map qbar ≫ B.inclusion.map t)
        (CompactificationOf.ofProper _) Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf Ybar.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) :=
  isConstructibleEtaleModule_homology_derivedLowerShriek_ofProper_comp_isFinite_of_hasConstantCohomology
    B qbar t Λ hℓ m hm M hM hmM _ (hasConstantCohomologyPlus_singleFunctor Λ M) n

end Stacks.EtaleCohomology

end
