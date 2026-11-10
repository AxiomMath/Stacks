module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.RelativeCurveGeneric
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.FiniteComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.UnibranchConstantModuleFiltration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.ModuleTraceDegreeSmallEtale
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.CompactificationShriek
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SectionCycle
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Composite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Rf_!` of a locally constant sheaf on a geometrically unibranch family of curves

Let `f : U ⟶ Y` be separated and of finite presentation with fibres of dimension at most `1`,
`Y` Noetherian, `U` irreducible and geometrically unibranch, and `F` a finite type, locally
constant sheaf of `Λ`-modules on `U` annihilated by `ℓ^n`, over a torsion Noetherian ring `Λ`.
Then every cohomology sheaf of `Rf_! F` is constructible (Stacks 0GKY).

## Main results

* `Stacks.EtaleCohomology.prop_of_retract_of_isWeakSerreClass`: a weak Serre class is closed
  under retracts.
* `Stacks.EtaleCohomology.nonempty_compactificationOf_comp`: `g ≫ f` has a compactification
  when `f` has one and `g` is separated and quasi-finite (Zariski's main theorem).
* `Stacks.EtaleCohomology.topologicalKrullDim_fiber_comp_le_of_locallyQuasiFinite`.
* `Stacks.EtaleCohomology.prop_homology_derivedLowerShriek_singleFunctor_of_shortExact`.
* `isConstructible_homology_derivedLowerShriek_of_isFiniteTypeLocallyConstant_of_unibranch`.

## Implementation notes

Stacks 0GJ0 gives a finite étale `g : T ⟶ U` of degree prime to `ℓ` such that `g⁻¹ F` is an
iterated extension of constant sheaves on finite modules, for which `R(f ∘ g)_!` is handled by
Stacks 0GKX; Stacks 0F7J (case of a finite étale `g`) identifies `R(f ∘ g)_! g⁻¹ F` with
`Rf_! g_* g⁻¹ F`, and the trace of Stacks 03SH makes `F` a direct summand of `g_* g⁻¹ F`.

Stacks 0GJ0 asks for `U` irreducible and geometrically unibranch, which is the hypothesis made
here. Stacks 0GKV enters as the hypothesis `h0GKV`; the case of Stacks 0F7J for a finite morphism
is `Stacks.EtaleCohomology.derivedLowerShriekCompDirectImageIsoOfIsFinite`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open ZeroObject

universe u

namespace Stacks.EtaleCohomology

/-- **A weak Serre class is closed under retracts**: a retract `X` of `Y` is the kernel of the
idempotent `𝟙 - r ∘ i` of `Y`. -/
theorem prop_of_retract_of_isWeakSerreClass {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] {X Y : C} (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r = 𝟙 X) (hY : P Y) : P X := by
  have w : i ≫ (𝟙 Y - r ≫ i) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, h, Category.id_comp, sub_self]
  refine P.prop_of_isLimit_kernelFork (k := KernelFork.ofι i w) ?_ hY hY
  refine KernelFork.IsLimit.ofι _ _ (fun g _ => g ≫ r) (fun g hg => ?_) (fun g hg m hm => ?_)
  · have hg' := hg
    rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at hg'
    rw [Category.assoc]
    exact hg'.symm
  · rw [← hm, Category.assoc, h, Category.comp_id]

/-- **A compactification of `g ≫ f` for `g` quasi-finite.** If `f : U ⟶ Y` is quasi-compact with a
compactification `j` over a quasi-compact quasi-separated `Y`, and `g : T ⟶ U` is separated,
quasi-finite, quasi-compact and locally of finite presentation, then `g ≫ f` has a
compactification: Zariski's main theorem (Stacks 0F2N) factors `T ⟶ U ⟶ X̄` through an open
immersion into a scheme finite over `X̄`. -/
@[sga "4 XVII 3.2.2" "(iii), special case"]
theorem nonempty_compactificationOf_comp {T U Y : Scheme.{u}} (g : T ⟶ U) [IsSeparated g]
    [LocallyQuasiFinite g] [QuasiCompact g] [LocallyOfFinitePresentation g] (f : U ⟶ Y)
    [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (j : CompactificationOf (Over.mk f)) : Nonempty (CompactificationOf (Over.mk (g ≫ f))) := by
  have : IsProper j.toBase := j.property.2
  have : UniversallyClosed j.toBase := IsProper.toUniversallyClosed
  have : QuasiCompact j.toBase := instQuasiCompactOfUniversallyClosed j.toBase
  have : IsSeparated j.toBase := IsProper.toIsSeparated
  have : QuasiSeparated j.toBase := IsSeparated.instQuasiSeparated j.toBase
  have : CompactSpace j.space := QuasiCompact.compactSpace_of_compactSpace j.toBase
  have : QuasiSeparatedSpace j.space := quasiSeparatedSpace_of_quasiSeparated j.toBase
  have : IsOpenImmersion j.immersion := j.property.1
  have : LocallyOfFiniteType g := inferInstance
  obtain ⟨T', j', π, hj', -, hπ, -, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_finitePresentation_factorization
      (g ≫ j.immersion)
  have : IsOpenImmersion j' := hj'
  have : IsFinite π := hπ
  have : IsProper π := inferInstance
  have : IsProper (π ≫ j.toBase) := inferInstance
  exact ⟨CompactificationOf.ofFactor (X₀ := Over.mk (g ≫ f)) j' (π ≫ j.toBase) (g ≫ f) (by
    rw [← Category.assoc, ← hfac, Category.assoc, CompactificationOf.immersion_toBase])⟩

/-- **Composing with a quasi-finite morphism does not raise the dimension of the fibres.** -/
theorem topologicalKrullDim_fiber_comp_le_of_locallyQuasiFinite {T U Y : Scheme.{u}}
    (g : T ⟶ U) [LocallyOfFiniteType g] [LocallyQuasiFinite g] (f : U ⟶ Y)
    [LocallyOfFiniteType f] {d : ℕ} (hdim : ∀ s, topologicalKrullDim (f.fiber s) ≤ d) (s : Y) :
    topologicalKrullDim ((g ≫ f).fiber s) ≤ d := by
  change (g ≫ f).fiberDimension s ≤ d
  refine (Scheme.Hom.fiberDimension_le_iff _ _ _).mpr fun x _ => ?_
  refine (topologicalKrullDimAt_fiber_comp_le_add g f x).trans ?_
  calc _ ≤ ((0 : ℕ) : WithBot ℕ∞) + f.fiberDimension (f (g x)) :=
        add_le_add (Stacks.Chow.relativeDimensionLE_zero_of_locallyQuasiFinite g x)
          (Scheme.Hom.topologicalKrullDimAt_fiber_le_fiberDimension f (x := g x) rfl)
    _ ≤ d := by rw [Nat.cast_zero, zero_add]; exact hdim _

section Triangle

open Stacks.DerivedFunctor

attribute [local instance] HasDerivedCategory.standard Functor.commShiftRightDerivedFunctorPlus
  Functor.isTriangulated_rightDerivedFunctorPlus

/-- **`Rf_!` along a short exact sequence of sheaves.** A weak Serre class containing every
cohomology sheaf of `Rf_! X₁` and `Rf_! X₃` contains those of `Rf_! X₂`, for a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of sheaves placed in degree `0`. -/
theorem prop_homology_derivedLowerShriek_singleFunctor_of_shortExact {X Y : Scheme.{u}}
    (f : X ⟶ Y) (j : CompactificationOf (Over.mk f)) (Λ : Type) [Ring Λ]
    (P : ObjectProperty (EtaleModules.{u, 0} Λ Y)) [P.IsWeakSerreClass]
    (S : ShortComplex (EtaleModules.{u, 0} Λ X)) (hS : S.ShortExact)
    (h₁ : ∀ q : ℤ, P ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj S.X₁))))
    (h₃ : ∀ q : ℤ, P ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj S.X₃))))
    (n : ℤ) :
    P ((DerivedCategory.Plus.homologyFunctor _ n).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj S.X₂))) :=
  prop_homology_obj₂_of_distTriang_plus P _
    ((derivedLowerShriek.{u, 0} f j Λ).map_distinguished _
      (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hS)) h₁ h₃ n

end Triangle

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **`Rg_*` of a sheaf placed in degree `0`, for `g` integral.** Direct image along an integral
morphism is exact (Stacks 095U), so `Rg_*(G[0]) ≅ (g_* G)[0]`. -/
theorem nonempty_derivedDirectImage_singleFunctor_iso_of_isIntegralHom {T U : Scheme.{u}}
    (g : T ⟶ U) [IsIntegralHom g] (Λ : Type) [Ring Λ] (G : EtaleModules.{u, 0} Λ T) :
    Nonempty ((etaleModuleDerivedDirectImage.{u, 0} Λ g).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} Λ g).obj G)) := by
  let e₁ : DerivedCategory.Plus.ι.obj
        ((etaleModuleDirectImage.{u, 0} Λ g).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≅
      DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} Λ g).obj G)) :=
    ((etaleModuleDirectImage.{u, 0} Λ g).mapDerivedCategorySingleFunctor 0).app G
  exact ⟨((etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus).app
      _ ≪≫ DerivedCategory.Plus.ι.preimageIso e₁⟩

/-- A sheaf of `Λ`-modules on `X_étale` is killed by the integer `c`, as a morphism `c • 𝟙`,
exactly when every section is. -/
private theorem nsmul_id_eq_zero_iff_forall_nsmul_eq_zero_aux {X : Scheme.{u}} {Λ : Type}
    [Ring Λ] (G : EtaleModules.{u, 0} Λ X) (c : ℕ) :
    c • 𝟙 G = 0 ↔ ∀ (V : X.Etale) (y : G.obj.obj (Opposite.op V)), c • y = 0 := by
  have h : ∀ V : (X.Etale)ᵒᵖ, ((sheafToPresheaf _ _).map (c • 𝟙 G)).app V = c • 𝟙 _ := by
    intro V
    simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id, NatTrans.app_nsmul,
      NatTrans.id_app]
  constructor
  · intro h0 V y
    have h' := congrArg (fun φ => φ y) (h (Opposite.op V))
    simp only at h'
    refine h'.symm.trans ?_
    rw [h0]
    simp
  · intro hann
    apply Sheaf.hom_ext
    ext V y
    have h' := congrArg (fun φ => φ y) (h V)
    simp only at h'
    change ((sheafToPresheaf _ _).map (c • 𝟙 G)).app V y = 0
    rw [h']
    exact hann (Opposite.unop V) y

/-- **Stacks 0GKY over a geometrically unibranch source, from Stacks 0GKV.** Let `Y` be a
Noetherian scheme of `B`, `f : U ⟶ Y` separated and of finite presentation with fibres of
dimension at most `1` (for instance an open of `𝔸¹_Y`), with `U` irreducible and geometrically
unibranch, `j` a compactification of `f`, `Λ` a Noetherian ring with `m = 0` in `Λ` for some
`m > 0`, and `F` a finite type, locally constant sheaf of `Λ`-modules on `U` annihilated by `ℓ^n`
for a prime `ℓ`. Then every cohomology sheaf of `Rf_! F` is constructible.

`h0GKV` is Stacks 0GKV. -/
theorem isConstructible_homology_derivedLowerShriek_of_isFiniteTypeLocallyConstant_of_unibranch
    (B : BigEtaleSite.{u}) (Y : B.Scheme) [IsNoetherian Y.obj] {U : Scheme.{u}}
    [IrreducibleSpace U] (hU : IsGeometricallyUnibranch U) (f : U ⟶ Y.obj) [IsSeparated f]
    (hf : FinitePresentation f) (hdim : ∀ s, topologicalKrullDim (f.fiber s) ≤ 1)
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
    (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0) {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 1 ≤ n)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (F : EtaleModules.{u, 0} Λ U)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.smallEtaleTopology F)
    (hann : ∀ (V : U.Etale) (y : F.obj.obj (Opposite.op V)), (ℓ ^ n) • y = 0) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  obtain ⟨T, g, d, hfin, het, hrank, hd, hPr⟩ :=
    exists_finiteEtale_primeToEll_prop_inverseImage hℓ hn hU F hF hann
  have : IsFinite g := hfin
  have : Etale g := het
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d := hrank
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  have : LocallyOfFiniteType f := inferInstance
  have : IsLocallyNoetherian Y.obj := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace Y.obj := inferInstance
  have : IsProper g := inferInstance
  have : IsSeparated g := IsProper.toIsSeparated
  have : UniversallyClosed g := IsProper.toUniversallyClosed
  have : QuasiCompact g := instQuasiCompactOfUniversallyClosed g
  have : QuasiSeparated g := IsSeparated.instQuasiSeparated g
  have : LocallyQuasiFinite g := inferInstance
  have : LocallyOfFinitePresentation g := inferInstance
  have : LocallyOfFiniteType g := IsProper.toLocallyOfFiniteType
  obtain ⟨j'⟩ := nonempty_compactificationOf_comp g f j
  have hQ := isWeakSerreClass_isBigSiteConstructibleEtaleModule B Y Λ
  have : QuasiSeparated f := hf.2.2
  have hgf : FinitePresentation (g ≫ f) :=
    ⟨inferInstance, inferInstance, MorphismProperty.comp_mem @QuasiSeparated _ _ ‹_› ‹_›⟩
  have : IsSeparated (g ≫ f) := inferInstance
  have hdimgf := topologicalKrullDim_fiber_comp_le_of_locallyQuasiFinite g f (d := 1) hdim
  -- the property `R(g ≫ f)_! G` constructible, closed under the operations of Stacks 0GJ0
  let Pr : ObjectProperty (EtaleModules.{u, 0} Λ T) := fun G => ∀ q : ℤ,
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((derivedLowerShriek.{u, 0} (g ≫ f) j' Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))
  have hPrI : Pr.IsClosedUnderIsomorphisms :=
    ⟨fun e h q => IsBigSiteConstructibleEtaleModule.of_iso B Λ
      ((DerivedCategory.Plus.homologyFunctor _ q).mapIso ((derivedLowerShriek.{u, 0} _ j' Λ).mapIso
        ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e))) (h q)⟩
  have hPr0 : Pr 0 := fun q => isConstructibleEtaleModule_of_isZero B Λ Y
    (Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _ (isZero_zero _))))
  have hPrE : ∀ Sc : ShortComplex (EtaleModules.{u, 0} Λ T), Sc.ShortExact → Pr Sc.X₁ →
      Pr Sc.X₃ → Pr Sc.X₂ := fun Sc hSc h₁ h₃ q =>
    prop_homology_derivedLowerShriek_singleFunctor_of_shortExact (g ≫ f) j' Λ _ Sc hSc h₁ h₃ q
  have hPrM : ∀ M : ModuleCat.{u + 1} Λ, Module.Finite Λ M →
      Pr ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := fun M hM q =>
    isConstructibleEtaleModule_homology_derivedLowerShriek_of_fiberDimension_le_one B Y (g ≫ f) hgf
      hdimgf j' Λ m hm hΛ M hM h0GKV _ ⟨Iso.refl _⟩ q
  have hgF := hPr Pr hPrI hPr0 hPrE hPrM
  -- Stacks 0F7J for `g`, then the trace retraction of Stacks 03SH
  have hnF : (ℓ ^ n) • 𝟙 F = 0 :=
    (nsmul_id_eq_zero_iff_forall_nsmul_eq_zero_aux F _).2 hann
  have hdn : d.Coprime (ℓ ^ n) := Nat.Coprime.pow_right n
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hd))
  obtain ⟨r, hr⟩ := exists_etaleModule_unit_comp_eq_id_of_coprime Λ g d F hdn hnF
  -- Stacks 0F7J for the finite `g`: `R(g ≫ f)_! G ≅ Rf_!(Rg_* G) ≅ Rf_!(g_* G)`
  let G := (etaleModuleInverseImage.{u, 0} Λ g).obj F
  have hG : isTorsionPlus.{u, 0} Λ T ((DerivedCategory.Plus.singleFunctor _ 0).obj G) :=
    fun _ => isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _
  obtain ⟨e₀⟩ := nonempty_derivedDirectImage_singleFunctor_iso_of_isIntegralHom g Λ G
  let e := ((derivedLowerShriek.{u, 0} f j Λ).mapIso e₀).symm ≪≫
    ((derivedLowerShriekCompDirectImageIsoOfIsFinite Λ g f j j').app
      ⟨(DerivedCategory.Plus.singleFunctor _ 0).obj G, hG⟩).symm
  let Φ := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ U) 0 ⋙
    derivedLowerShriek.{u, 0} f j Λ ⋙ DerivedCategory.Plus.homologyFunctor _ k
  refine prop_of_retract_of_isWeakSerreClass _
    (Φ.map ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app F)) (Φ.map r)
    (by rw [← Φ.map_comp, hr, Φ.map_id]; rfl) ?_
  exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
    ((DerivedCategory.Plus.homologyFunctor _ k).mapIso e).symm (hgF k)

/-- A sheaf of `Λ`-modules on `X_étale` is killed by the integer `c`, as a morphism `c • 𝟙`,
exactly when every section is. -/
theorem nsmul_id_eq_zero_iff_forall_nsmul_eq_zero {X : Scheme.{u}} {Λ : Type} [Ring Λ]
    (G : EtaleModules.{u, 0} Λ X) (c : ℕ) :
    c • 𝟙 G = 0 ↔ ∀ (V : X.Etale) (y : G.obj.obj (Opposite.op V)), c • y = 0 :=
  nsmul_id_eq_zero_iff_forall_nsmul_eq_zero_aux G c

/-- **Stacks 0GKY over a geometrically unibranch source, any torsion coefficient ring, from
Stacks 0GKV.** As
`isConstructible_homology_derivedLowerShriek_of_isFiniteTypeLocallyConstant_of_unibranch`,
without the hypothesis that `F` is killed by a power of a prime: `F` is killed by `m`, and for a
prime `ℓ ∣ m` the short exact sequence `0 → F[ℓ] → F → F/F[ℓ] → 0` has finite type locally
constant terms (Stacks 093U) killed by `ℓ` and by `m / ℓ`. `h0GKV` is Stacks 0GKV. -/
theorem isConstructible_homology_derivedLowerShriek_of_isFiniteTypeLocallyConstant_of_geomUnibranch
    (B : BigEtaleSite.{u}) (Y : B.Scheme) [IsNoetherian Y.obj] {U : Scheme.{u}}
    [IrreducibleSpace U] (hU : IsGeometricallyUnibranch U) (f : U ⟶ Y.obj) [IsSeparated f]
    (hf : FinitePresentation f) (hdim : ∀ s, topologicalKrullDim (f.fiber s) ≤ 1)
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
    (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (F : EtaleModules.{u, 0} Λ U)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.smallEtaleTopology F) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  suffices h : ∀ c : ℕ, 0 < c → ∀ G : EtaleModules.{u, 0} Λ U,
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.smallEtaleTopology G → c • 𝟙 G = 0 →
      ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B Y Λ
        ((DerivedCategory.Plus.homologyFunctor _ q).obj
          ((derivedLowerShriek.{u, 0} f j Λ).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) by
    refine h m hm F hF ((nsmul_id_eq_zero_iff_forall_nsmul_eq_zero F m).2 fun V y => ?_) k
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro hc G hG hcG q
  by_cases h1 : c = 1
  · subst h1
    have hz : IsZero G := by
      rw [IsZero.iff_id_eq_zero]
      simpa using hcG
    exact isConstructibleEtaleModule_of_isZero B Λ Y
      (Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _ hz)))
  have hℓ : c.minFac.Prime := Nat.minFac_prime h1
  set ℓ := c.minFac
  obtain ⟨c', hc'⟩ : ℓ ∣ c := Nat.minFac_dvd c
  have hc'pos : 0 < c' := Nat.pos_of_ne_zero (by rintro rfl; simp at hc'; omega)
  have hc'lt : c' < c := by
    rw [hc']
    exact lt_mul_left hc'pos hℓ.one_lt
  let ι := kernel.ι (ℓ • 𝟙 G)
  let π := cokernel.π ι
  have hK : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      U.smallEtaleTopology Λ (kernel (ℓ • 𝟙 G)) :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_kernel _ Λ (ℓ • 𝟙 G) hG hG
  have hQ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      U.smallEtaleTopology Λ (cokernel ι) :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_cokernel _ Λ ι hK hG
  -- the kernel is killed by `ℓ`
  have hKℓ : ℓ • 𝟙 (kernel (ℓ • 𝟙 G)) = 0 := by
    rw [← cancel_mono ι, Preadditive.nsmul_comp, Category.id_comp, zero_comp]
    have h := kernel.condition (ℓ • 𝟙 G)
    rwa [Preadditive.comp_nsmul, Category.comp_id] at h
  -- the cokernel is killed by `c'`
  have hQc : c' • 𝟙 (cokernel ι) = 0 := by
    have w : (c' • 𝟙 G) ≫ (ℓ • 𝟙 G) = 0 := by
      rw [Preadditive.nsmul_comp, Category.id_comp, ← mul_nsmul', mul_comm, ← hc', hcG]
    rw [← cancel_epi π, Preadditive.comp_nsmul, Category.comp_id, comp_zero]
    have : c' • π = (c' • 𝟙 G) ≫ π := by rw [Preadditive.nsmul_comp, Category.id_comp]
    rw [this, ← kernel.lift_ι (ℓ • 𝟙 G) (c' • 𝟙 G) w, Category.assoc, cokernel.condition,
      comp_zero]
  have := isWeakSerreClass_isBigSiteConstructibleEtaleModule B Y Λ
  let S : ShortComplex (EtaleModules.{u, 0} Λ U) := ShortComplex.mk ι π (cokernel.condition ι)
  have hS : S.ShortExact := { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel ι) }
  refine prop_homology_derivedLowerShriek_singleFunctor_of_shortExact f j Λ _ S hS
    (fun q' => ?_) (fun q' => ih c' hc'lt hc'pos _ hQ hQc q') q
  exact isConstructible_homology_derivedLowerShriek_of_isFiniteTypeLocallyConstant_of_unibranch
    B Y hU f hf hdim j Λ m hm hΛ hℓ le_rfl h0GKV _ hK
    (by simpa using (nsmul_id_eq_zero_iff_forall_nsmul_eq_zero _ ℓ).1 hKℓ) q'

end Stacks.EtaleCohomology

end
