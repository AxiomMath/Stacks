module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalCohomologyLimitLocal
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalization
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapShrink
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian
public import StacksFrontier.RingTheory.LocalCohomology.ProZeroOfEssentiallyConstant

/-!
# The per-prime half of Stacks 0EFX

Let `S` be a bootstrap situation ([Stacks, Tag 0EFU]) with ring `A`, ideal `I`, module `M` and
locus `T`, and let `𝔮 ∈ T`. The first paragraph of the proof of [Stacks, Tag 0EFX] shows that for
every `m` there is `m'(m, 𝔮) ≥ m` such that for `k ≥ m'(m, 𝔮)` the maps
`H^i_𝔮(Iᵏ M_𝔮) → H^i_𝔮(Iᵐ M_𝔮)` vanish for `i ≤ s`, and in degree `s + 1` their image is
independent of `k` and injects into `H^{s+1}_𝔮(M_𝔮)`.

This file proves that paragraph, in the spelling the globalization lemmas
`Stacks.LocalCohomology.exists_map_idealPowerTower_eq_zero_of_local` and
`Stacks.LocalCohomology.exists_eventually_injective_image_idealPowerTower_of_local` consume:
the functor `N ↦ H^i_{𝔮A_𝔮}(N_𝔮)` is `ModuleCat.localizedModuleFunctor` followed by
`Stacks.LocalCohomology.localCohomologyModuleFunctor`, applied to the tower `{IⁿM}`.

The source localizes the situation at `𝔮` and shrinks its locus to the closed point
([Stacks, Tag 0EFV]), where [Stacks, Tag 0EFR] makes `{H^i_𝔪(M_𝔮/IⁿM_𝔮)}` essentially constant for
`i ≤ s`; the pro-zero statements then follow from the `Stacks.LocalCohomology` lemma
`exists_localCohomology_idealPowerTower_eq_zero_of_isEssentiallyConstantWith` and its
degree-`(s+1)` companion, and the stability of images from the Artinianness of the local
cohomology of a finite module at the closed point. What remains is to carry these
statements from the localized situation's own tower `{(I A_𝔮)ⁿ M_𝔮}` and its model of local
cohomology with support in the closed point to the spelling above; the comparisons are natural
isomorphisms of towers, and the three kinds of statement (vanishing, equality of images,
injectivity of images into a fixed term) are invariant under such isomorphisms.

The cone form of [Stacks, Tag 0EFR] for an `I`-adically complete local situation is taken as the
explicit hypothesis `hcomplete`, in the shape of
`Stacks.Algebraization.nonempty_isLimit_cone_of_eq_closedPoint_of_complete`.

## Main results

* `Stacks.Algebraization.exists_perPrime_map_idealPowerTower_eq_zero`: for `𝔮 ∈ T` and `i ≤ s`
  the system `{H^i_{𝔮A_𝔮}((IⁿM)_𝔮)}` is pro-zero.
* `Stacks.Algebraization.exists_perPrime_degree_succ`: for `𝔮 ∈ T`, the degree-`s` vanishing and
  the degree-`(s + 1)` stability and injectivity of images of [Stacks, Tag 0EFX].

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFR](https://stacks.math.columbia.edu/tag/0EFR)
* [Stacks Project, Tag 0EFV](https://stacks.math.columbia.edu/tag/0EFV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.LocalCohomology

/-! ### Statements about towers of modules, invariant under isomorphism -/

section Transport

variable {R : Type u} [Ring R] {F G : ℕᵒᵖ ⥤ ModuleCat.{u} R} (e : F ≅ G)

include e in
/-- A transition map of a tower of modules vanishes exactly when the corresponding transition
map of an isomorphic tower does. -/
theorem map_eq_zero_iff_of_iso {m k : ℕᵒᵖ} (f : m ⟶ k) : F.map f = 0 ↔ G.map f = 0 := by
  constructor <;> intro h
  · rw [← NatIso.naturality_1 e f, h, zero_comp, comp_zero]
  · rw [← NatIso.naturality_2 e f, h, zero_comp, comp_zero]

include e in
/-- Equality of the images of two transition maps into a common term is invariant under an
isomorphism of towers. -/
theorem range_map_eq_iff_of_iso {m k k' : ℕᵒᵖ} (f : k ⟶ m) (f' : k' ⟶ m) :
    LinearMap.range (F.map f).hom = LinearMap.range (F.map f').hom ↔
      LinearMap.range (G.map f).hom = LinearMap.range (G.map f').hom := by
  have hrange : ∀ {k : ℕᵒᵖ} (g : k ⟶ m), LinearMap.range (G.map g).hom =
      (LinearMap.range (F.map g).hom).map (e.hom.app m).hom := by
    intro k g
    have : G.map g = e.inv.app k ≫ F.map g ≫ e.hom.app m := (NatIso.naturality_1 e g).symm
    rw [this, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.2 (ConcreteCategory.bijective_of_isIso (e.inv.app k)).2,
      Submodule.map_top, LinearMap.range_comp]
  rw [hrange f, hrange f']
  exact (Submodule.map_injective_of_injective
    (ConcreteCategory.bijective_of_isIso (e.hom.app m)).1).eq_iff.symm

include e in
/-- The condition "every element of the image of `t` that dies under `w` is zero" is invariant
under an isomorphism of towers. -/
theorem forall_map_eq_zero_of_mem_ker_iff_of_iso {n m k : ℕᵒᵖ} (t : k ⟶ m) (w : m ⟶ n) :
    (∀ x : F.obj k, (F.map t).hom x ∈ LinearMap.ker (F.map w).hom → (F.map t).hom x = 0) ↔
      (∀ x : G.obj k, (G.map t).hom x ∈ LinearMap.ker (G.map w).hom →
        (G.map t).hom x = 0) := by
  have key : ∀ {F G : ℕᵒᵖ ⥤ ModuleCat.{u} R} (e : F ≅ G),
      (∀ x : F.obj k, (F.map t).hom x ∈ LinearMap.ker (F.map w).hom → (F.map t).hom x = 0) →
      (∀ x : G.obj k, (G.map t).hom x ∈ LinearMap.ker (G.map w).hom →
        (G.map t).hom x = 0) := by
    intro F G e h x hx
    have ht : (G.map t).hom x = (e.hom.app m).hom ((F.map t).hom ((e.inv.app k).hom x)) := by
      rw [← NatIso.naturality_1 e t]
      rfl
    have hw : ∀ y, (G.map w).hom ((e.hom.app m).hom y) = (e.hom.app n).hom ((F.map w).hom y) :=
      fun y => (ConcreteCategory.congr_hom (e.hom.naturality w) y).symm
    rw [LinearMap.mem_ker, ht, hw] at hx
    have hx' : (F.map w).hom ((F.map t).hom ((e.inv.app k).hom x)) = 0 :=
      (ConcreteCategory.bijective_of_isIso (e.hom.app n)).1 (hx.trans (map_zero _).symm)
    rw [ht, h _ hx', map_zero]
  exact ⟨key e, key e.symm⟩

end Transport

/-! ### Localizing the tower `{IⁿM}` -/

section LocalizedTower

variable {A : Type u} [CommRing A] (P : Submonoid A) (I : Ideal A)
  (M : Type u) [AddCommGroup M] [Module A M]

/-- `IⁿM` localizes to `(I A_P)ⁿ M_P`. -/
theorem localized'_idealPow_smul_top (n : ℕ) :
    (I ^ n • (⊤ : Submodule A M)).localized' (Localization P) P
        (LocalizedModule.mkLinearMap P M) =
      (I.map (algebraMap A (Localization P))) ^ n • (⊤ : Submodule (Localization P)
        (LocalizedModule P M)) := by
  rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top, Ideal.map_pow]

/-- The localization map `IⁿM ⟶ (I A_P)ⁿ M_P`. -/
def idealPowLocalizedMap (n : ℕ) :
    ↥(I ^ n • (⊤ : Submodule A M)) →ₗ[A]
      ↥((I.map (algebraMap A (Localization P))) ^ n •
        (⊤ : Submodule (Localization P) (LocalizedModule P M))) :=
  ((LinearEquiv.ofEq _ _ (localized'_idealPow_smul_top P I M n)).restrictScalars A).toLinearMap ∘ₗ
    (I ^ n • (⊤ : Submodule A M)).toLocalized' (Localization P) P
      (LocalizedModule.mkLinearMap P M)

/-- `IⁿM → (I A_P)ⁿ M_P` is a localization of `IⁿM` at `P`. -/
instance (n : ℕ) : IsLocalizedModule P (idealPowLocalizedMap P I M n) := by
  unfold idealPowLocalizedMap
  infer_instance

/-- The image of `x ∈ IⁿM` under `idealPowLocalizedMap`, as an element of `M_P`, is `x / 1`. -/
@[simp]
theorem idealPowLocalizedMap_apply_coe (n : ℕ) (x : ↥(I ^ n • (⊤ : Submodule A M))) :
    ((idealPowLocalizedMap P I M n x : LocalizedModule P M)) =
      LocalizedModule.mkLinearMap P M x :=
  rfl

/-- **The localized tower.** Localizing the tower `{IⁿM}` at `P` gives the tower
`{(I A_P)ⁿ M_P}` of the localized ring and module, as towers of `A_P`-modules. -/
def idealPowerTowerLocalizedIso :
    idealPowerTower.{u, u} I (ModuleCat.of A M) ⋙ ModuleCat.localizedModuleFunctor P ≅
      idealPowerTower.{u, u} (I.map (algebraMap A (Localization P)))
        (ModuleCat.of (Localization P) (LocalizedModule P M)) :=
  NatIso.ofComponents
    (fun n =>
      letI := ModuleCat.localizedModule_isLocalizedModule
        (ModuleCat.of A ↥(I ^ n.unop • (⊤ : Submodule A M))) P
      ((IsLocalizedModule.linearEquiv P
        ((ModuleCat.of A ↥(I ^ n.unop • (⊤ : Submodule A M))).localizedModuleMkLinearMap P)
        (idealPowLocalizedMap P I M n.unop)).extendScalarsOfIsLocalization P
          (Localization P)).toModuleIso)
    (fun {n m} h => by
      have := ModuleCat.localizedModule_isLocalizedModule
        (ModuleCat.of A ↥(I ^ n.unop • (⊤ : Submodule A M))) P
      have := ModuleCat.localizedModule_isLocalizedModule
        (ModuleCat.of A ↥(I ^ m.unop • (⊤ : Submodule A M))) P
      let Ln := (ModuleCat.of A ↥(I ^ n.unop • (⊤ : Submodule A M))).localizedModule P
      let mkn := (ModuleCat.of A ↥(I ^ n.unop • (⊤ : Submodule A M))).localizedModuleMkLinearMap P
      let mkm := (ModuleCat.of A ↥(I ^ m.unop • (⊤ : Submodule A M))).localizedModuleMkLinearMap P
      let ιm := ((I.map (algebraMap A (Localization P))) ^ m.unop •
        (⊤ : Submodule (Localization P) (LocalizedModule P M))).subtype
      let ιn := ((I.map (algebraMap A (Localization P))) ^ n.unop •
        (⊤ : Submodule (Localization P) (LocalizedModule P M))).subtype
      let incl : ↥(I ^ n.unop • (⊤ : Submodule A M)) →ₗ[A] ↥(I ^ m.unop • (⊤ : Submodule A M)) :=
        Submodule.inclusion (Submodule.pow_smul_top_le I M (leOfHom h.unop))
      let eN := IsLocalizedModule.linearEquiv P mkn (idealPowLocalizedMap P I M n.unop)
      let eM := IsLocalizedModule.linearEquiv P mkm (idealPowLocalizedMap P I M m.unop)
      let lhs : Ln →ₗ[Localization P] LocalizedModule P M :=
        ιm ∘ₗ (eM.extendScalarsOfIsLocalization P (Localization P)).toLinearMap ∘ₗ
          IsLocalizedModule.mapExtendScalars P mkn mkm (Localization P) incl
      let rhs : Ln →ₗ[Localization P] LocalizedModule P M :=
        ιn ∘ₗ (eN.extendScalarsOfIsLocalization P (Localization P)).toLinearMap
      have key : lhs = rhs := by
        apply LinearMap.restrictScalars_injective A
        refine IsLocalizedModule.linearMap_ext P mkn (LocalizedModule.mkLinearMap P M) ?_
        refine LinearMap.ext fun y => ?_
        change ιm (eM (IsLocalizedModule.map P mkn mkm incl (mkn y))) = ιn (eN (mkn y))
        rw [IsLocalizedModule.map_apply, IsLocalizedModule.linearEquiv_apply,
          IsLocalizedModule.linearEquiv_apply]
        rfl
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => Subtype.ext ?_
      exact LinearMap.congr_fun key x)

/-- The inclusion `IᵏM ⊆ M` factors through the transition map to the zeroth term of the tower. -/
theorem idealPowerInclusion_eq_map_comp {A : Type u} [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) (k : ℕ) :
    idealPowerInclusion.{u, u} I M k =
      (idealPowerTower.{u, u} I M).map (homOfLE (Nat.zero_le k)).op ≫
        idealPowerInclusion.{u, u} I M 0 :=
  rfl

end LocalizedTower

/-! ### The two models of local cohomology at the closed point -/

/-- Over a Noetherian local ring, local cohomology with support in `V(𝔪)` computed by derived
sections with support agrees with `Stacks.LocalCohomology.localCohomologyModuleFunctor`, the
coreflection model, by [Stacks, Tag 0955]
(`Stacks.LocalCohomology.isIso_compareSectionsWithSupportLocalCohomology`). -/
def localCohomologyWithSupportInMaximalIdealIso (B : Type u) [CommRing B] [IsNoetherianRing B]
    [IsLocalRing B] (i : ℤ) :
    localCohomologyWithSupportInModuleFunctor.{u, u} B
        (PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal B : Set B)) i ≅
      localCohomologyModuleFunctor.{u, u} B i :=
  have := isIso_compareSectionsWithSupportLocalCohomology.{u, u} B (IsLocalRing.maximalIdeal B)
    (IsNoetherian.noetherian _)
  Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0)
    (Functor.isoWhiskerRight
      (asIso (compareSectionsWithSupportLocalCohomology.{u, u} B (IsLocalRing.maximalIdeal B)
        (IsNoetherian.noetherian _)))
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i))

end Stacks.LocalCohomology


namespace Stacks.Algebraization

open Stacks.LocalCohomology

namespace BootstrapSituation

/-- The ring of the localization of a bootstrap situation at a prime is local. -/
instance isLocalRing_localize_primeCompl (S : BootstrapSituation.{u, u, w})
    (q : PrimeSpectrum S.A) : IsLocalRing (S.localize q.asIdeal.primeCompl).A :=
  inferInstanceAs (IsLocalRing (Localization.AtPrime q.asIdeal))

/-- The closed point of the localization at `𝔮` lies over `𝔮`. -/
theorem comap_closedPoint_localize (S : BootstrapSituation.{u, u, w}) (q : PrimeSpectrum S.A) :
    PrimeSpectrum.comap (algebraMap S.A (Localization.AtPrime q.asIdeal))
      (IsLocalRing.closedPoint (Localization.AtPrime q.asIdeal)) = q :=
  PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := q.asIdeal))

/-- **The situation localized at a prime of `T` and shrunk to the closed point** ([Stacks,
Tag 0EFV], parts (F) and (E)). -/
def atPrime (S : BootstrapSituation.{u, u, w}) (q : PrimeSpectrum S.A) (hq : q ∈ S.T) :
    BootstrapSituation.{u, u, w} :=
  (S.localize q.asIdeal.primeCompl).shrink
    {IsLocalRing.closedPoint (S.localize q.asIdeal.primeCompl).A}
    (by
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      change PrimeSpectrum.comap (algebraMap S.A (Localization.AtPrime q.asIdeal))
        (IsLocalRing.closedPoint (Localization.AtPrime q.asIdeal)) ∈ S.T
      rw [comap_closedPoint_localize]
      exact hq)
    (fun x y hxy hx => by
      rw [Set.mem_singleton_iff] at hx ⊢
      subst hx
      exact ((IsLocalRing.specializes_closedPoint y).antisymm hxy).eq)

/-- The ring of the situation localized at a prime of `T` and shrunk to the closed point is
local. -/
instance isLocalRing_atPrime (S : BootstrapSituation.{u, u, w}) (q : PrimeSpectrum S.A)
    (hq : q ∈ S.T) : IsLocalRing (S.atPrime q hq).A :=
  isLocalRing_localize_primeCompl S q

/-- The locus of the situation localized at a prime of `T` and shrunk to the closed point is the
closed point. -/
theorem atPrime_T (S : BootstrapSituation.{u, u, w}) (q : PrimeSpectrum S.A) (hq : q ∈ S.T) :
    (S.atPrime q hq).T = {IsLocalRing.closedPoint (S.atPrime q hq).A} :=
  rfl

end BootstrapSituation

section PerPrime

variable (S : BootstrapSituation.{u, u, w}) (q : PrimeSpectrum S.A)

/-- The tower `n ↦ H^i_{𝔮A_𝔮}((IⁿM)_𝔮)` in the spelling of
`Stacks.LocalCohomology.exists_map_idealPowerTower_eq_zero_of_local`, compared with the tower of
local cohomology with support in the closed point of the localized tower `{(I A_𝔮)ⁿ M_𝔮}`. -/
def perPrimeTowerIso (i : ℤ) :
    idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
        (ModuleCat.localizedModuleFunctor q.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization.AtPrime q.asIdeal) i) ≅
      idealPowerTower.{u, u} (S.I.map (algebraMap S.A (Localization.AtPrime q.asIdeal)))
          (ModuleCat.of (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl S.M)) ⋙
        localCohomologyWithSupportInModuleFunctor.{u, u} (Localization.AtPrime q.asIdeal)
          {IsLocalRing.closedPoint (Localization.AtPrime q.asIdeal)} i :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (idealPowerTowerLocalizedIso q.asIdeal.primeCompl S.I S.M) _ ≪≫
    Functor.isoWhiskerLeft _
      ((localCohomologyWithSupportInMaximalIdealIso (Localization.AtPrime q.asIdeal) i).symm ≪≫
        eqToIso (by rw [zeroLocus_maximalIdeal]))

/-- The hypothesis of [Stacks, Tag 0EFR] in cone form for `I`-adically complete local
situations, in the shape of
`Stacks.Algebraization.nonempty_isLimit_cone_of_eq_closedPoint_of_complete`. -/
abbrev CompleteLocalConeHypothesis : Prop :=
  ∀ (S' : BootstrapSituation.{u, u, u}) [IsLocalRing S'.A] [IsAdicComplete S'.I S'.A],
    S'.T = {IsLocalRing.closedPoint S'.A} → ∀ i : ℤ, i ≤ S'.s →
      Nonempty (IsLimit (Bootstrap.cone.{u, u} S' i))

variable {S q} in
/-- At a prime of `T`, the systems `{H^i_{𝔪}(M_𝔮/IⁿM_𝔮)}` of the localized and shrunk situation
are essentially constant for `i ≤ s` ([Stacks, Tag 0EFR]). -/
theorem exists_isEssentiallyConstantWith_atPrime (hcomplete : CompleteLocalConeHypothesis.{u})
    (hq : q ∈ S.T) (i : ℤ) (hi : i ≤ S.s) :
    ∃ (j : ℕᵒᵖ) (σ : (Bootstrap.tower.{u, u} (S.atPrime q hq) i).obj j ⟶
        (Bootstrap.cone.{u, u} (S.atPrime q hq) i).pt),
      EssentiallyConstantPro.IsEssentiallyConstantWith
        (Bootstrap.tower.{u, u} (S.atPrime q hq) i) (Bootstrap.cone.{u, u} (S.atPrime q hq) i)
        j σ :=
  Bootstrap.isEssentiallyConstantWith_of_eq_closedPoint_of_isLimit (S.atPrime q hq) i
    (S.atPrime_T q hq)
    (nonempty_isLimit_cone_of_eq_closedPoint_of_complete hcomplete (S.atPrime q hq)
      (S.atPrime_T q hq) i hi).some

variable {S q} in
/-- **The per-prime pro-zero assertion of [Stacks, Tag 0EFX].** At a prime `𝔮 ∈ T`, for `i ≤ s`
the system `{H^i_{𝔮A_𝔮}((IⁿM)_𝔮)}` is pro-zero. -/
theorem exists_perPrime_map_idealPowerTower_eq_zero (hcomplete : CompleteLocalConeHypothesis.{u})
    (hq : q ∈ S.T) (i : ℤ) (hi : i ≤ S.s) (m : ℕ) :
    ∃ k : ℕ, ∃ h : m ≤ k,
      (ModuleCat.localizedModuleFunctor q.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization.AtPrime q.asIdeal) i).map
        ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M)).map (homOfLE h).op) = 0 := by
  obtain ⟨j₁, σ₁, h₁⟩ := exists_isEssentiallyConstantWith_atPrime hcomplete hq (i - 1) (by omega)
  obtain ⟨j, σ, h⟩ := exists_isEssentiallyConstantWith_atPrime hcomplete hq i hi
  obtain ⟨k, hmk, hk⟩ :=
    exists_localCohomology_idealPowerTower_eq_zero_of_isEssentiallyConstantWith.{u, u}
      (S.atPrime q hq).T (S.atPrime q hq).I
      (ModuleCat.of (S.atPrime q hq).A (S.atPrime q hq).M) i h₁ h m
  exact ⟨k, hmk, (map_eq_zero_iff_of_iso (perPrimeTowerIso S q i) (homOfLE hmk).op).2 hk⟩

variable {S q} in
/-- **The per-prime degree-`(s + 1)` assertions of [Stacks, Tag 0EFX].** At a prime `𝔮 ∈ T` and
for every `m` there is `c ≥ m` such that for `k ≥ c` the map
`H^s_{𝔮A_𝔮}((IᵏM)_𝔮) → H^s_{𝔮A_𝔮}((IᵐM)_𝔮)` vanishes, the image of
`H^{s+1}_{𝔮A_𝔮}((IᵏM)_𝔮) → H^{s+1}_{𝔮A_𝔮}((IᵐM)_𝔮)` does not depend on `k`, and that image
injects into `H^{s+1}_{𝔮A_𝔮}(M_𝔮)`. -/
theorem exists_perPrime_degree_succ (hcomplete : CompleteLocalConeHypothesis.{u})
    (hq : q ∈ S.T) (m : ℕ) :
    ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      (ModuleCat.localizedModuleFunctor q.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization.AtPrime q.asIdeal) S.s).map
        ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M)).map
          (homOfLE (hmc.trans hck)).op) = 0 ∧
      LinearMap.range ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
          ModuleCat.localizedModuleFunctor q.asIdeal.primeCompl ⋙
            localCohomologyModuleFunctor (Localization.AtPrime q.asIdeal) (S.s + 1)).map
              (homOfLE (hmc.trans hck)).op).hom =
        LinearMap.range ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
          ModuleCat.localizedModuleFunctor q.asIdeal.primeCompl ⋙
            localCohomologyModuleFunctor (Localization.AtPrime q.asIdeal) (S.s + 1)).map
              (homOfLE hmc).op).hom ∧
      (∀ x : (idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
          ModuleCat.localizedModuleFunctor q.asIdeal.primeCompl ⋙
            localCohomologyModuleFunctor (Localization.AtPrime q.asIdeal) (S.s + 1)).obj (op k),
        ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
          ModuleCat.localizedModuleFunctor q.asIdeal.primeCompl ⋙
            localCohomologyModuleFunctor (Localization.AtPrime q.asIdeal) (S.s + 1)).map
              (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
            ModuleCat.localizedModuleFunctor q.asIdeal.primeCompl ⋙
              localCohomologyModuleFunctor (Localization.AtPrime q.asIdeal) (S.s + 1)).map
                (homOfLE (Nat.zero_le m)).op).hom →
        ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
          ModuleCat.localizedModuleFunctor q.asIdeal.primeCompl ⋙
            localCohomologyModuleFunctor (Localization.AtPrime q.asIdeal) (S.s + 1)).map
              (homOfLE (hmc.trans hck)).op).hom x = 0) := by
  let B := Localization.AtPrime q.asIdeal
  let MB : ModuleCat.{u} B := ModuleCat.of B (LocalizedModule q.asIdeal.primeCompl S.M)
  let IB : Ideal B := S.I.map (algebraMap S.A B)
  let G : ℕᵒᵖ ⥤ ModuleCat.{u} B := idealPowerTower.{u, u} IB MB ⋙
    localCohomologyWithSupportInModuleFunctor.{u, u} B {IsLocalRing.closedPoint B} (S.s + 1)
  let F : ℕᵒᵖ ⥤ ModuleCat.{u} B := idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
    ModuleCat.localizedModuleFunctor q.asIdeal.primeCompl ⋙
      localCohomologyModuleFunctor B (S.s + 1)
  let e : F ≅ G := perPrimeTowerIso S q (S.s + 1)
  -- vanishing in degree `s`
  obtain ⟨c₁, hmc₁, hc₁⟩ := exists_perPrime_map_idealPowerTower_eq_zero hcomplete hq S.s le_rfl m
  -- stability of the images in degree `s + 1`, from Artinianness at the closed point
  have : Module.Finite B MB :=
    Module.Finite.of_isLocalizedModule q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl S.M)
  have : IsNoetherian B MB := isNoetherian_of_isNoetherianRing_of_finite B MB
  have : Module.Finite B ((idealPowerTower.{u, u} IB MB).obj (op m)) :=
    Module.IsNoetherian.finite B ↥(IB ^ m • (⊤ : Submodule B MB))
  have hart : IsArtinian B (G.obj (op m)) :=
    isArtinian_localCohomologyWithSupportIn_closedPoint B _ (S.s + 1)
  have hcomp : ∀ {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c),
      (homOfLE (h₁.trans h₂)).op = (homOfLE h₂).op ≫ (homOfLE h₁).op :=
    fun _ _ => Subsingleton.elim _ _
  let R : ℕ → Submodule B (G.obj (op m)) := fun k =>
    if h : m ≤ k then LinearMap.range (G.map (homOfLE h).op).hom else ⊤
  have hR : ∀ k (h : m ≤ k), R k = LinearMap.range (G.map (homOfLE h).op).hom :=
    fun k h => dite_eq_left h
  have hRanti : ∀ k k', m ≤ k → k ≤ k' → R k' ≤ R k := by
    intro k k' hk hkk'
    rw [hR k hk, hR k' (hk.trans hkk')]
    rw [hcomp hk hkk', G.map_comp, ModuleCat.hom_comp, LinearMap.range_comp]
    exact LinearMap.map_le_range
  let f : ℕ →o (Submodule B (G.obj (op m)))ᵒᵈ :=
    ⟨fun j => OrderDual.toDual (R (m + j)),
      fun j j' hjj' => hRanti (m + j) (m + j') (Nat.le_add_right m j) (by omega)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes f
  -- injectivity of the stable image into the zeroth term
  obtain ⟨j₀, σ₀, h₀⟩ := exists_isEssentiallyConstantWith_atPrime hcomplete hq (S.s + 1 - 1)
    (by omega)
  obtain ⟨c₃, hmc₃, hc₃⟩ :=
    exists_forall_eq_zero_of_inclusion_eq_zero_of_isEssentiallyConstantWith.{u, u}
      (S.atPrime q hq).T (S.atPrime q hq).I
      (ModuleCat.of (S.atPrime q hq).A (S.atPrime q hq).M) (S.s + 1) h₀ m
  refine ⟨max c₁ (max (m + n) c₃), le_max_of_le_left hmc₁, fun k hck => ⟨?_, ?_, ?_⟩⟩
  · rw [hcomp hmc₁ ((le_max_left _ _).trans hck), Functor.map_comp, Functor.map_comp, hc₁,
      comp_zero]
  · have hG : ∀ k' (hk' : m + n ≤ k'), R k' = R (m + n) := by
      intro k' hk'
      have h1 := hn (k' - m) (by omega)
      change OrderDual.toDual (R (m + n)) = OrderDual.toDual (R (m + (k' - m))) at h1
      rw [OrderDual.toDual_inj, show m + (k' - m) = k' by omega] at h1
      exact h1.symm
    have hGk := (hG k ((le_max_of_le_right (le_max_left _ _)).trans hck)).trans
      (hG (max c₁ (max (m + n) c₃)) (le_max_of_le_right (le_max_left _ _))).symm
    rw [hR _ ((le_max_of_le_left hmc₁).trans hck), hR _ (le_max_of_le_left hmc₁)] at hGk
    exact (range_map_eq_iff_of_iso e _ _).2 hGk
  · refine (forall_map_eq_zero_of_mem_ker_iff_of_iso e _ _).2 fun x hx => ?_
    have hck₃ : c₃ ≤ k := (le_max_of_le_right (le_max_right _ _)).trans hck
    have h0 : (G.map (homOfLE (Nat.zero_le k)).op).hom x = 0 := by
      rw [hcomp (Nat.zero_le m) ((le_max_of_le_left hmc₁).trans hck), G.map_comp,
        ModuleCat.hom_comp, LinearMap.comp_apply]
      exact hx
    have hincl : ((localCohomologyWithSupportInModuleFunctor.{u, u} B
        {IsLocalRing.closedPoint B} (S.s + 1)).map (idealPowerInclusion.{u, u} IB MB k)).hom x =
          0 := by
      rw [idealPowerInclusion_eq_map_comp, Functor.map_comp, ModuleCat.hom_comp,
        LinearMap.comp_apply]
      change ((localCohomologyWithSupportInModuleFunctor.{u, u} B {IsLocalRing.closedPoint B}
        (S.s + 1)).map (idealPowerInclusion.{u, u} IB MB 0)).hom
          ((G.map (homOfLE (Nat.zero_le k)).op).hom x) = 0
      rw [h0, map_zero]
    exact hc₃ k hck₃ x hincl

end PerPrime

end Stacks.Algebraization

end
