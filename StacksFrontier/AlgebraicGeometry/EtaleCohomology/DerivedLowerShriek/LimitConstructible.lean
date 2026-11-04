module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.NagataConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitCategory
public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.RingTheory.Nagata.Examples
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover

/-!
# `Rf_!` of a constructible sheaf over an affine base, through Noetherian approximation

Let `Y = Spec R` be an affine scheme, `f : X ⟶ Y` separated of finite presentation, `Λ` a
torsion Noetherian ring and `F` a constructible sheaf of `Λ`-modules on `X`. Then every
cohomology sheaf of `Rf_! F` is constructible. Write `R` as the union of its finitely generated
subrings `ℤ[s]`, so that `Y = lim Spec ℤ[s]` with Noetherian Nagata stages; `f` descends to
`f₀ : X₀ ⟶ Spec ℤ[s₀]` (Stacks 01ZM), `X = lim X₀ ×_{Spec ℤ[s₀]} Spec ℤ[s]`, and `F` is the
inverse image of a constructible sheaf at some stage (Stacks 09YU). Base change (Stacks 0F7L)
then identifies `Rf_! F` with the inverse image of `Rf_{s!} F_s`, which is constructible by
Stacks 0GL0 over a Nagata base
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_isNagataScheme`),
and inverse image preserves constructibility (Stacks 095G). This is the passage to a Noetherian
base in the proof of Stacks 0GKZ.

Stacks 09YU (essential surjectivity for the limit of the categories of constructible sheaves)
enters as the hypothesis `h09YU`, and Stacks 0GKV as `h0GKV`, until they land.

## Main results

* `AlgebraicGeometry.BigEtaleSite.contains_terminal`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_isAffine_of_limit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Opposite

universe u

namespace AlgebraicGeometry

/-- A big étale site contains the terminal scheme: it is the spectrum of `ℤ`, of size `ℵ₀`, and
the cutoff of a big étale site is uncountable. -/
theorem BigEtaleSite.contains_terminal (B : BigEtaleSite.{u}) : B.Contains (⊤_ AlgebraicGeometry.Scheme.{u}) := by
  have htop : (⊤_ AlgebraicGeometry.Scheme.{u}).size = Cardinal.aleph0 := by
    let e : (⊤_ AlgebraicGeometry.Scheme.{u}) ≅ Spec (.of (ULift.{u} ℤ)) :=
      terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal
    calc
      (⊤_ AlgebraicGeometry.Scheme.{u}).size = (Spec (.of (ULift.{u} ℤ))).size := Scheme.size_congr e
      _ = max Cardinal.aleph0 (Cardinal.mk (ULift.{u} ℤ)) := Scheme.size_Spec _
      _ = Cardinal.aleph0 := by simp
  change (⊤_ AlgebraicGeometry.Scheme.{u}).size < B.cutoff
  rw [htop]
  exact B.aleph0_lt_cutoff

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-! ### Reindexing the stages above a finite subset -/

section Reindex

variable (R : Type u) (s₀ : Finset R)

/-- The finite subsets of `R` containing `s₀`. -/
abbrev FinsetAbove := {t : Finset R // s₀ ⊆ t}

instance : Nonempty (FinsetAbove R s₀) := ⟨⟨s₀, le_rfl⟩⟩

instance [DecidableEq R] : IsDirected (FinsetAbove R s₀) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.1 ∪ b.1, a.2.trans Finset.subset_union_left⟩,
    Finset.subset_union_left, Finset.subset_union_right⟩⟩

/-- The finite subsets containing `s₀`, as objects over `s₀` in `(Finset R)ᵒᵖ`. -/
def finsetAboveToOver : (FinsetAbove R s₀)ᵒᵖ ⥤ Over (op s₀) where
  obj t := Over.mk (homOfLE t.unop.2).op
  map {t t'} g := Over.homMk (homOfLE (leOfHom g.unop)).op (Subsingleton.elim _ _)
  map_id _ := by ext; exact Subsingleton.elim _ _
  map_comp _ _ := by ext; exact Subsingleton.elim _ _

instance : (finsetAboveToOver R s₀).Full where
  map_surjective {t t'} g :=
    ⟨(homOfLE (leOfHom g.left.unop)).op, by ext; exact Subsingleton.elim _ _⟩

instance : (finsetAboveToOver R s₀).Faithful where
  map_injective {_ _} _ _ _ := Subsingleton.elim _ _

instance : (finsetAboveToOver R s₀).EssSurj where
  mem_essImage d := ⟨op ⟨d.left.unop, leOfHom d.hom.unop⟩,
    ⟨Over.isoMk (Iso.refl _) (Subsingleton.elim _ _)⟩⟩

instance : (finsetAboveToOver R s₀).IsEquivalence where

instance : (finsetAboveToOver R s₀).Initial := inferInstance

end Reindex


/-! ### Constructibility of `Rf_!` from a stage of an inverse system -/

section Stage

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

variable (B : BigEtaleSite.{u})

/-- **`Rf_! F` is constructible when `f` and `F` come from a stage with a Noetherian Nagata
base.** Let `X = lim X_p` be a directed inverse limit in `B` with limit cone `cX`, let
`φ_p : X_p ⟶ Y_p` be separated of finite type over Noetherian Nagata schemes `Y_p`, and let
`f : X ⟶ Y` be such that `X` is the base change of `φ_p` along `g_p : Y ⟶ Y_p` for every `p`.
Assume (Stacks 09YU, essential surjectivity) that every constructible sheaf on `X` is the inverse
image of a constructible sheaf at some stage. Then for every constructible `F` on `X` over a
torsion Noetherian ring, every cohomology sheaf of `Rf_! F` is constructible: at a stage `p` with
`F = (X ⟶ X_p)⁻¹ F_p`, base change (Stacks 0F7L) gives `H^k(Rf_! F) = g_p⁻¹ H^k(Rφ_{p!} F_p)`,
constructible by Stacks 0GL0 over a Nagata base and Stacks 095G. `h0GKV` is Stacks 0GKV. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_stage
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    {I : Type u} [Preorder I] (DX DY : Iᵒᵖ ⥤ B.Scheme) (φ : DX ⟶ DY)
    (cX : Cone (DX ⋙ B.inclusion)) (hX : B.Contains cX.pt)
    (hN : ∀ p : I, IsNoetherian (DY.obj (op p)).obj)
    (hNag : ∀ p : I, IsNagataScheme (DY.obj (op p)).obj)
    (hφ : ∀ p : I, IsSeparated (B.inclusion.map (φ.app (op p))) ∧
      LocallyOfFiniteType (B.inclusion.map (φ.app (op p))) ∧
      QuasiCompact (B.inclusion.map (φ.app (op p))))
    (Y : B.Scheme) (f : cX.pt ⟶ Y.obj) (g : ∀ p : I, Y ⟶ DY.obj (op p))
    (hsq : ∀ p : I, IsPullback (cX.π.app (op p)) f (B.inclusion.map (φ.app (op p)))
      (B.inclusion.map (g p)))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [CompactSpace Y.obj]
    [QuasiSeparatedSpace Y.obj] (j : CompactificationOf (Over.mk f))
    (h09YU : SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) DX cX hX
      (fun Z => IsConstructibleModuleSheaf B Z Λ))
    (F : EtaleModules.{u, 0} Λ cX.pt) (hF : IsBigSiteConstructibleEtaleModule B (B.obj cX.pt hX) Λ F)
    (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  obtain ⟨p, Fp, hFp, ⟨e⟩⟩ := h09YU ((etaleModulesToSmallEtale B (B.obj cX.pt hX) Λ).obj F) hF
  let Xp := DX.obj (op p)
  let Yp := DY.obj (op p)
  have := hN p
  have := (hφ p).1
  have := (hφ p).2.1
  have := (hφ p).2.2
  let fp : Xp.obj ⟶ Yp.obj := B.inclusion.map (φ.app (op p))
  let E := SmallEtale.sheafEquiv B Xp.obj Xp.property (ModuleCat.{u + 1} Λ)
  let Gp : EtaleModules.{u, 0} Λ Xp.obj := E.functor.obj Fp
  have hGp : IsBigSiteConstructibleEtaleModule B Xp Λ Gp :=
    isConstructibleModuleSheaf_congr B Λ Xp (E.unitIso.app Fp) hFp
  -- the inverse image of `G_p` to `X` is `F`
  let legB : B.obj cX.pt hX ⟶ Xp := ObjectProperty.homMk (cX.π.app (op p))
  let e₁ : (etaleModulesToSmallEtale B (B.obj cX.pt hX) Λ).obj
        ((etaleModuleInverseImage.{u, 0} Λ (cX.π.app (op p))).obj Gp) ≅
      (etaleModulesToSmallEtale B (B.obj cX.pt hX) Λ).obj F :=
    etaleModulesToSmallEtalePullbackIso B Λ legB Gp ≪≫
      (smallEtaleSheafPullback B (ModuleCat.{u + 1} Λ) legB).mapIso (E.unitIso.app Fp).symm ≪≫ e
  let eF : (etaleModuleInverseImage.{u, 0} Λ (cX.π.app (op p))).obj Gp ≅ F :=
    (SmallEtale.sheafEquiv B cX.pt hX (ModuleCat.{u + 1} Λ)).inverse.preimageIso e₁
  -- Stacks 0GL0 over the Nagata scheme `Y_p`
  have : IsLocallyNoetherian Yp.obj := IsNoetherian.toIsLocallyNoetherian
  obtain ⟨jp⟩ : Nonempty (CompactificationOf (Over.mk fp)) := IsCofiltered.nonempty
  have hc := isConstructibleEtaleModule_homology_derivedLowerShriek_of_isNagataScheme B Yp
    (hNag p) Xp fp jp Λ m hm hΛ h0GKV Gp hGp k
  have hc' := isConstructibleEtaleModule_inverseImage B Λ (g p) hc
  -- base change along `g_p` (Stacks 0F7L)
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ Xp.obj) 0).obj Gp
  have hKt : isTorsionPlus.{u, 0} Λ Xp.obj K := fun _ =>
    isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _
  have := isIso_derivedLowerShriekBaseChange_app Λ (hsq p) jp K hKt
  let eBC := asIso ((derivedLowerShriekBaseChange.{u, 0} Λ (hsq p) jp).app K)
  obtain ⟨e₂⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ
    (B.inclusion.map (g p)) ((derivedLowerShriek.{u, 0} fp jp Λ).obj K) k
  obtain ⟨e₃⟩ := nonempty_inverseImage_singleFunctor_iso (Λ := Λ) (cX.π.app (op p)) Gp
  refine isConstructibleEtaleModule_homology_derivedLowerShriek_of_eq B rfl
    (jp.baseChange (hsq p)) j Λ _ (fun _ => isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _)
    k ?_
  exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
    (e₂.symm ≪≫ (DerivedCategory.Plus.homologyFunctor _ k).mapIso
      (eBC ≪≫ (derivedLowerShriek.{u, 0} f (jp.baseChange (hsq p)) Λ).mapIso
        (e₃ ≪≫ (DerivedCategory.Plus.singleFunctor _ 0).mapIso eF))) hc'

end Stage

end Stacks.EtaleCohomology

end
