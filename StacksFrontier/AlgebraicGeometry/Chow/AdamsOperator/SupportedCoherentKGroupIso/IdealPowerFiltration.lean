module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.RingTheory.Support
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroup
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerComplex
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SheafSubmodule
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroup
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.CoherentReflexive
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.Topology.Sheaves.Modules.Support

/-!
# Dévissage: `K'_0(Z) ≅ K_0(Coh_Z(X))`

Let `X` be a locally Noetherian scheme and `Z ⊂ X` a closed subscheme with ideal sheaf `ℐ`.
The exact inclusion functor `Coh(𝒪_Z) ⥤ Coh_Z(X)`, direct image along `i : Z ⟶ X`, induces an
isomorphism `K'_0(Z) = K_0(Coh(𝒪_Z)) → K_0(Coh_Z(X))`.

## Main results

* `AlgebraicGeometry.coherentToSupportedCoherentKZeroHom_bijective`: **[Stacks, Tag 0FDT]**, the
  homomorphism `AlgebraicGeometry.coherentToSupportedCoherentKZeroHom` is bijective.
* `AlgebraicGeometry.coherentToSupportedCoherentKZeroEquiv`: the resulting isomorphism of groups.

## Implementation notes

The proof is the source's. For `ℱ` coherent and supported on `Z`, the filtration
`ℱ ⊃ ℐℱ ⊃ ℐ²ℱ ⊃ ⋯` is locally finite: over an affine open, which is Noetherian, some power of
`ℐ` kills `ℱ` by [Stacks, Tag 01Y9]. Hence `⊕_{p ≥ 0} ℐᵖℱ`, `⊕_{p ≥ 1} ℐᵖℱ` and
`gr ℱ = ⊕_{p ≥ 0} ℐᵖℱ/ℐᵖ⁺¹ℱ` are coherent, and the two short exact sequences relating them give
`[ℱ] = [gr ℱ]`. The module `gr ℱ` is annihilated by `ℐ`, so it is a direct image from `Z` by
[Stacks, Tag 087T]; this gives surjectivity. The inverse sends `ℱ` to the class of the coherent
`𝒪_Z`-module whose direct image is `gr ℱ`. That it is additive is the source's double filtration
argument: for `0 → ℱ → 𝒢 → ℋ → 0` the filtration of `𝒢` by `ℐ^q𝒢` induces on `ℱ` the
filtration by `ℱ ∩ ℐ^q𝒢`, and the class of the graded module of a locally finite filtration with
quotients annihilated by `ℐ` does not depend on the filtration, by comparing both with the
grid `ℐᵖℱ ∩ ℐ^q𝒢`.

## References

* [Stacks Project, Tag 0FDT](https://stacks.math.columbia.edu/tag/0FDT)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.SupportedCoherentDevissage

open Scheme.Modules TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.IdealPower (idealPowerMultiple idealPowerMultiple_le_iff)
open Stacks.AlgebraicGeometry.CoherenceCriteria (coherent_tfae)
open Stacks.AlgebraicGeometry.Tag087TCoherentImage (CoherentAnnihilatedModules AnnihilatedByKer)
open scoped AlgebraicGeometry

section

-- `X.Modules` and its morphisms are definitions over `SheafOfModules`; the lemmas below are
-- stated on either side, and instance search has to see through both.
attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom

local instance {X : Scheme.{u}} (M : X.Modules) [M.IsCoherent] : M.IsQuasicoherent :=
  isQuasicoherent_of_isCoherent M

local instance {X : Scheme.{u}} (M : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    M.obj.IsCoherent :=
  CoherentAbelian.isCoherent_of_stacksIsCoherent M.property

lemma support_subset_range_of_annihilated
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsCoherent]
    (hM : ∀ U : X.affineOpens, ∀ a : Γ(X, U), a ∈ i.ker.ideal U →
      ∀ m : Γ(M, U), a • m = 0) :
    SheafOfModules.supp M ⊆ Set.range i.base := by
  have hs : SheafOfModules.supp M ⊆ (i.ker.support : Set X) := by
    intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    let Uaff : X.affineOpens := ⟨U, hU⟩
    let p := Uaff.2.primeIdealOf ⟨x, hxU⟩
    have hpM : p ∈ Module.support Γ(X, U) Γ(M, U) := by
      apply (AlgebraicGeometry.Scheme.Modules.mem_support_sections_iff_mem_supp M Uaff x hxU).2
      exact hx
    have hIann : i.ker.ideal Uaff ≤ Module.annihilator Γ(X, U) Γ(M, U) := by
      intro a ha
      rw [Module.mem_annihilator]
      intro m
      exact hM Uaff a ha m
    have hpZero : p ∈ PrimeSpectrum.zeroLocus (i.ker.ideal Uaff : Set Γ(X, U)) :=
      hIann.trans (Module.annihilator_le_of_mem_support hpM)
    let p' : Spec (CommRingCat.of Γ(X, U)) := p
    have hpoint : Uaff.2.fromSpec p' = x :=
      Uaff.2.fromSpec_primeIdealOf ⟨x, hxU⟩
    have hbasic (f : Γ(X, U)) :
        p' ∈ PrimeSpectrum.basicOpen f ↔ x ∈ X.basicOpen f := by
      rw [← Uaff.2.fromSpec_preimage_basicOpen]
      show Uaff.2.fromSpec p' ∈ X.basicOpen f ↔ x ∈ X.basicOpen f
      rw [hpoint]
    have hxZero : x ∈ X.zeroLocus (U := U) (i.ker.ideal Uaff) := by
      apply (Scheme.mem_zeroLocus_iff X (i.ker.ideal Uaff : Set Γ(X, U)) x).2
      intro f hf hxBasic
      have hpBasic : p' ∈ PrimeSpectrum.basicOpen f := hbasic f |>.2 hxBasic
      change i.ker.ideal Uaff ≤ p.asIdeal at hpZero
      exact ((PrimeSpectrum.mem_basicOpen f p).mp hpBasic) (hpZero hf)
    exact (i.ker.mem_support_iff_of_mem (U := Uaff) hxU).mpr hxZero
  have hrange : (i.ker.support : Set X) = Set.range i.base := by
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
  simpa [hrange] using hs

noncomputable def annihilatedToSupported
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] :
    CoherentAnnihilatedModules i ⥤
      SupportedCoherentModules i where
  obj M := by
    letI : M.obj.IsCoherent := M.property.1
    have hs' : SheafOfModules.supp M.obj ⊆ Set.range i.base :=
      support_subset_range_of_annihilated i M.obj M.property.2
    have hs :
        (⟨M.obj.val, M.obj.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp ⊆
          Set.range i.base := by
      change (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules M.obj).supp ⊆ _
      rw [SheafOfModules.supp_eq_moduleSheaf_supp M.obj]
      exact hs'
    exact ⟨⟨M.obj, CoherentAbelian.stacksIsCoherent_of_isCoherent M.property.1⟩, hs⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk f.hom)
  map_id := by intros; ext; rfl
  map_comp := by intros; ext; rfl

private theorem preservesFiniteLimitsRestrictFunctor {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : PreservesFiniteLimits (restrictFunctor f) := by
  have : PreservesLimitsOfSize.{0, 0} (toPresheaf Y) := preservesLimitsOfSize_shrink _
  have : PreservesFiniteLimits (toPresheaf Y) := inferInstance
  have : PreservesFiniteLimits ((Functor.whiskeringLeft _ _ Ab.{u}).obj f.opensFunctor.op) :=
    inferInstance
  have e : restrictFunctor f ⋙ toPresheaf X ≅
      toPresheaf Y ⋙ (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op := Iso.refl _
  have : PreservesFiniteLimits (restrictFunctor f ⋙ toPresheaf X) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (toPresheaf X)

attribute [local instance] preservesFiniteLimitsRestrictFunctor

/-- On an open subscheme, the cokernel of a map into a module that vanishes there vanishes. -/
lemma isZero_restrict_cokernel {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B)
    (U : X.Opens) (h : IsZero ((restrictFunctor U.ι).obj B)) :
    IsZero ((restrictFunctor U.ι).obj (cokernel f)) := by
  have : Epi ((restrictFunctor U.ι).map (cokernel.π f)) := Functor.map_epi _ _
  exact IsZero.of_epi ((restrictFunctor U.ι).map (cokernel.π f)) h

/-- On an open subscheme, a submodule of a module that vanishes there vanishes. -/
lemma isZero_restrict_of_mono {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B)
    (hf : Mono f) (U : X.Opens) (h : IsZero ((restrictFunctor U.ι).obj B)) :
    IsZero ((restrictFunctor U.ι).obj A) := by
  have : Mono ((restrictFunctor U.ι).map f) := Functor.map_mono _ _
  exact IsZero.of_mono ((restrictFunctor U.ι).map f) h

private theorem idealPowerMultiple_isQuasicoherent {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (idealPowerMultiple I n F).toSheafOfModules.IsQuasicoherent :=
  Stacks.AlgebraicGeometry.IdealPowerComparison.isQuasicoherent_idealPowerMultiple I n F

/-- A module all of whose sections vanish is zero. -/
private theorem isZero_of_forall_section_eq_zero {X : Scheme.{u}} (P : X.Modules)
    (h : ∀ (U : X.Opensᵒᵖ) (s : P.val.presheaf.obj U), s = 0) : IsZero P := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext s
  exact h U s

/-- The inclusion of a subsheaf of modules is a monomorphism of `𝒪_X`-modules. -/
lemma mono_submodule_ι {X : Scheme.{u}} {M : X.Modules} (N : M.Submodule) :
    Mono (C := X.Modules) N.ι := by
  constructor
  intro T a b h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext t
  have heq := congrArg (fun q : T ⟶ M => q.val.app U t) h
  exact Subtype.ext heq

attribute [local instance] mono_submodule_ι

theorem idealPowerMultiple_isCoherent {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsCoherent] (n : ℕ) :
    (idealPowerMultiple I n F).toSheafOfModules.IsCoherent := by
  have := idealPowerMultiple_isQuasicoherent I F n
  let N := idealPowerMultiple I n F
  exact Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono N.ι

private theorem finiteType_of_iso {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ≅ N) [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let τ : N.LocalGeneratorsData := {
    I := σ.I
    X := σ.X
    coversTop := σ.coversTop
    generators := fun i =>
      (σ.generators i).equivOfIso (asIso (e.hom.over (σ.X i))) }
  have hτ : τ.IsFiniteType := by
    constructor
    intro i
    have : (σ.generators i).IsFiniteType := hσ.isFiniteType i
    have : IsIso (e.hom.over (σ.X i)) := by
      dsimp [SheafOfModules.Hom.over]
      infer_instance
    show ((σ.generators i).ofEpi (e.hom.over (σ.X i))).IsFiniteType
    infer_instance
  exact SheafOfModules.IsFiniteType.mk.{u, u, u} ⟨τ, hτ⟩

private theorem coherent_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] [IsLocallyNoetherian Y]
    (M : Y.Modules) [M.IsCoherent] : (M.restrict f).IsCoherent := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : M.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have : ((Scheme.Modules.pullback f).obj M).IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType f.toLRSHom.toShHom M
  apply ((coherent_tfae X (M.restrict f)).out 1 2 rfl rfl).mpr
  exact ⟨inferInstance,
    finiteType_of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm⟩

private theorem supp_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) :
    SheafOfModules.supp (M.restrict f) = f ⁻¹' SheafOfModules.supp M := by
  ext x
  let e := ((Scheme.Modules.restrictStalkNatIso f x).app M).addCommGroupIsoToAddEquiv
  show (∃ a, a ≠ (0 : ↑((M.restrict f).presheaf.stalk x))) ↔
    ∃ b, b ≠ (0 : ↑(M.presheaf.stalk (f x)))
  exact (exists_congr fun a => (map_ne_zero_iff e e.injective).symm).trans
    (e.surjective.exists (p := (· ≠ 0))).symm

private theorem exists_idealPower_restrict_eq_bot {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (M : X.Modules) [M.IsCoherent]
    (hM : SheafOfModules.supp M ⊆ (I.support : Set X)) (U : X.affineOpens) :
    ∃ n : ℕ, idealPowerMultiple (I.comap U.1.ι) n
      (M.restrict U.1.ι) = ⊥ := by
  have : IsAffine U.1.toScheme := U.2
  have : IsLocallyNoetherian U.1.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian U.1.ι
  have : IsNoetherian U.1.toScheme := ⟨⟩
  have : (M.restrict U.1.ι).IsCoherent := coherent_restrict U.1.ι M
  apply (Stacks.IdealPowerSupport.exists_idealPowerMultiple_eq_bot_iff_supp_subset
    (M.restrict U.1.ι) (I.comap U.1.ι)).mpr
  rw [supp_restrict, Scheme.IdealSheafData.support_comap]
  exact Set.preimage_mono hM

theorem supp_subset_of_mono {X : Scheme.{u}}
    {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    SheafOfModules.supp M ⊆ SheafOfModules.supp N := by
  intro x hx
  obtain ⟨a, ha⟩ := hx
  let g := (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).map f
  have hg : Function.Injective g := by
    apply TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
    intro U
    exact (AddCommGrpCat.mono_iff_injective _).mp
      ((NatTrans.mono_iff_mono_app ((Scheme.Modules.toPresheaf X).map f)).mp
        (Functor.map_mono (Scheme.Modules.toPresheaf X) f) (op U))
  exact ⟨g a, fun h => ha (hg (h.trans g.hom.map_zero.symm))⟩

private noncomputable def bottomSheafSubmodule {X : Scheme.{u}} (F : X.Modules) :
    F.Submodule := by
  let N : F.val.Submodule := ⊥
  refine { toSubmodule := N, isSheaf := ?_ }
  intro V s hs
  let S := N.toSubfunctor.sieveOfSection s
  have hF : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (F.val.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ _ _ (SheafOfModules.isSheaf F))
  refine (hF S hs).isSeparatedFor.ext ?_
  intro W f hf
  have hmem : F.val.presheaf.map f.op s ∈ N.toSubfunctor.obj (op W) := by
    change (F.val.presheaf.map f.op).hom s ∈ N.toSubfunctor.obj (op W) at hf
    simpa [S, N, Subfunctor.sieveOfSection] using hf
  have hzero : F.val.presheaf.map f.op s = 0 := by
    change F.val.presheaf.map f.op s ∈ (⊥ : F.val.Submodule).obj (op W) at hmem
    exact (Submodule.mem_bot (X.ringCatSheaf.obj.obj (op W))).mp hmem
  change (F.val.presheaf.map f.op).hom s = (F.val.presheaf.map f.op).hom 0
  rw [hzero, map_zero]

theorem bottom_toSubmodule {X : Scheme.{u}} (F : X.Modules) :
    (⊥ : F.Submodule).toSubmodule = (⊥ : F.val.Submodule) := by
  let N := bottomSheafSubmodule F
  have hN : N = (⊥ : F.Submodule) := by
    apply le_antisymm
    · apply SheafOfModules.Submodule.le_iff.mpr
      intro V
      show ∀ x, x ∈ N.toSubmodule.obj V →
        x ∈ (⊥ : F.Submodule).toSubmodule.obj V
      intro x hx
      have hx' : x ∈ (⊥ : F.val.Submodule).obj V := by
        dsimp [N, bottomSheafSubmodule] at hx
        exact hx
      have hx0 := (Submodule.mem_bot (X.ringCatSheaf.obj.obj V)).mp hx'
      subst x
      exact ((⊥ : F.Submodule).toSubmodule.obj V).zero_mem
    · exact bot_le
  simpa [N, bottomSheafSubmodule] using
    (congrArg SheafOfModules.Submodule.toSubmodule hN).symm

theorem top_toSubmodule {X : Scheme.{u}} (M : X.Modules) :
    (⊤ : M.Submodule).toSubmodule = (⊤ : M.val.Submodule) := by
  show sInf ((fun N : M.Submodule => N.toSubmodule) '' (∅ : Set M.Submodule)) = _
  rw [Set.image_empty, sInf_empty]

theorem idealPowerMultiple_antitone {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) :
    Antitone (fun n => idealPowerMultiple I n M) := by
  intro n m hnm
  apply (idealPowerMultiple_le_iff I m M _).mpr
  intro U
  exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right hnm)).trans
    ((idealPowerMultiple_le_iff I n M _).mp le_rfl U)

noncomputable def idealPowerMultipleFunctor {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) : X.Modules ⥤ X.Modules where
  obj M := (idealPowerMultiple I n M).toSheafOfModules
  map f := sheafSubmoduleMap f _ _ (idealPowerMultiple_le_comap I n f _ le_rfl)
  map_id := by intro M; ext U s; rfl
  map_comp := by intro M N P f g; ext U s; rfl

lemma idealPowerMultipleFunctor_map_comp_ι {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) {M N : X.Modules} (f : M ⟶ N) :
    (idealPowerMultipleFunctor I n).map f ≫ (idealPowerMultiple I n N).ι =
      (idealPowerMultiple I n M).ι ≫ f :=
  sheafSubmoduleMap_comp_ι f _ _ (idealPowerMultiple_le_comap I n f _ le_rfl)

noncomputable def idealPowerSupported
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (F : SupportedCoherentModules i) (n : ℕ) :
    SupportedCoherentModules i := by
  let M := idealPowerMultiple i.ker n F.obj.obj
  have hcoh : M.toSheafOfModules.IsCoherent :=
    idealPowerMultiple_isCoherent i.ker F.obj.obj n
  refine ⟨⟨M.toSheafOfModules, CoherentAbelian.stacksIsCoherent_of_isCoherent hcoh⟩, ?_⟩
  have hM : Mono (C := X.Modules) M.ι := by
    exact mono_submodule_ι _
  have hs := (supp_subset_of_mono M.ι)
  have hF : SheafOfModules.supp F.obj.obj ⊆ Set.range i.base := by
    rw [← SheafOfModules.supp_eq_moduleSheaf_supp F.obj.obj]
    exact F.property
  change (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
    M.toSheafOfModules).supp ⊆ _
  rw [SheafOfModules.supp_eq_moduleSheaf_supp]
  exact hs.trans hF

private noncomputable def idealPowerSupportedStep
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (F : SupportedCoherentModules i) (n : ℕ) :
    idealPowerSupported i F (n + 1) ⟶ idealPowerSupported i F n :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (show (idealPowerMultiple i.ker (n + 1) F.obj.obj).toSheafOfModules ⟶
      (idealPowerMultiple i.ker n F.obj.obj).toSheafOfModules from
    ⟨PresheafOfModules.Submodule.homOfLE
      ((idealPowerMultiple_antitone i.ker F.obj.obj (Nat.le_succ n)))⟩))

theorem isZero_submodule_of_eq_bot {X : Scheme.{u}} {M : X.Modules}
    (N : M.Submodule) (hN : N = ⊥) : IsZero N.toSheafOfModules := by
  subst N
  refine isZero_of_forall_section_eq_zero _ fun U s => ?_
  apply Subtype.ext
  show s.val = 0
  have hEq := congrArg (fun P : M.val.Submodule => P.obj U) (bottom_toSubmodule M)
  have hs : s.val ∈ (⊥ : M.val.Submodule).obj U := hEq ▸ s.property
  exact hs

noncomputable def submoduleTopIso {X : Scheme.{u}} (M : X.Modules) :
    (⊤ : M.Submodule).toSheafOfModules ≅ M := by
  let f : (⊤ : M.Submodule).toSheafOfModules ⟶ M := (⊤ : M.Submodule).ι
  have hf : IsIso f := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    have hm : Mono (Scheme.Modules.Hom.app (X := X) f U) := (AddCommGrpCat.mono_iff_injective _).mpr
      (show Function.Injective (fun s : (⊤ : M.Submodule).obj (op U) => s.val) from
        Subtype.val_injective)
    have he : Epi (Scheme.Modules.Hom.app (X := X) f U) := (AddCommGrpCat.epi_iff_surjective _).mpr
      (fun s => ⟨⟨s, by
        change s ∈ (⊤ : M.Submodule).toSubmodule.obj (op U)
        rw [top_toSubmodule]
        trivial⟩, rfl⟩)
    exact isIso_of_mono_of_epi (Scheme.Modules.Hom.app (X := X) f U)
  exact asIso f

noncomputable def idealPowerSupportedZeroIso
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (F : SupportedCoherentModules i) :
    idealPowerSupported i F 0 ≅ F :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules
      (idealPowerMultiple_zero i.ker F.obj.obj)) ≪≫ submoduleTopIso F.obj.obj))

private noncomputable def coproductIsoFiniteOfIsZero {C : Type*}
    [Category.{v} C] [HasZeroMorphisms C] (F : ℕ → C) (N : ℕ)
    [HasCoproduct F] [HasCoproduct (fun n : Fin N => F n)]
    (hF : ∀ n, N ≤ n → IsZero (F n)) :
    (∐ F) ≅ ∐ (fun n : Fin N => F n) := by
  classical
  refine ⟨Sigma.desc (fun n => if h : n < N then Sigma.ι (fun j : Fin N => F j) ⟨n, h⟩ else 0),
    Sigma.desc (fun n : Fin N => Sigma.ι F n), ?_, ?_⟩
  · apply Sigma.hom_ext
    intro n
    by_cases h : n < N
    · simp [h]
    · exact (hF n (Nat.le_of_not_gt h)).eq_of_src _ _
  · apply Sigma.hom_ext
    intro n
    simp [n.isLt]

private noncomputable def coproductIsoHeadTail {C : Type*} [Category.{v} C]
    (F : ℕ → C) [HasCoproduct F] [HasCoproduct (fun n => F (n + 1))]
    [HasBinaryCoproduct (F 0) (∐ fun n => F (n + 1))] :
    (∐ F) ≅ F 0 ⨿ (∐ fun n => F (n + 1)) := by
  refine ⟨Sigma.desc (fun n => match n with
    | 0 => coprod.inl
    | n + 1 => Sigma.ι (fun j => F (j + 1)) n ≫ coprod.inr),
    coprod.desc (Sigma.ι F 0) (Sigma.desc fun n => Sigma.ι F (n + 1)), ?_, ?_⟩
  · apply Sigma.hom_ext
    rintro (_ | n)
    · simp only [Sigma.ι_desc_assoc, coprod.inl_desc, Category.comp_id]
    · simp only [Sigma.ι_desc_assoc, Category.assoc, coprod.inr_desc, Sigma.ι_desc,
        Category.comp_id]
  · apply coprod.hom_ext
    · simp only [coprod.inl_desc_assoc, Sigma.ι_desc, Category.comp_id]
    · apply Sigma.hom_ext
      intro n
      simp only [coprod.inr_desc_assoc, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.comp_id]

private theorem coherent_finiteCoproduct {X : Scheme.{u}}
    {J : Type*} [Finite J] (F : J → X.Modules)
    [HasCoproduct F] (hF : ∀ j, (F j).IsCoherent) :
    (∐ F).IsCoherent := by
  let P : ObjectProperty X.Modules := fun M => M.IsCoherent
  have : P.IsWeakSerreClass :=
    _root_.SheafOfModules.coherentModules_isWeakSerreClass (R := X.ringCatSheaf)
  have : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  exact P.prop_of_iso
    ((biproduct.isoProduct F).symm ≪≫ biproduct.isoCoproduct F) (P.prop_product hF)

theorem coherent_natCoproduct_of_eventually_isZero_restrict
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : ℕ → X.Modules)
    (hF : ∀ n, (F n).IsCoherent)
    (hlocal : ∀ U : X.affineOpens, ∃ N : ℕ, ∀ n, N ≤ n →
      IsZero ((F n).restrict U.1.ι)) : (∐ F).IsCoherent := by
  apply ((coherent_tfae X (∐ F)).out 1 4 rfl rfl).mpr
  intro U hU
  obtain ⟨N, hN⟩ := hlocal ⟨U, hU⟩
  let G : Fin N → X.Modules := fun n => F n
  have : (∐ G).IsCoherent := coherent_finiteCoproduct G (fun n => hF n)
  obtain ⟨M, hM, ⟨e⟩⟩ :=
    (((coherent_tfae X (∐ G)).out 1 4 rfl rfl).mp inferInstance) U hU
  let R := Scheme.Modules.restrictFunctor U.ι
  let e' : (∐ F).restrict U.ι ≅ (∐ G).restrict U.ι :=
    PreservesCoproduct.iso R F ≪≫
      coproductIsoFiniteOfIsZero (fun n => R.obj (F n)) N hN ≪≫
        (PreservesCoproduct.iso R G).symm
  exact ⟨M, hM, ⟨e' ≪≫ e⟩⟩

private lemma kZero_mk_coprod {C : Type*} [Category.{v} C] [Abelian C]
    (A B : C) : KZero.mk C (A ⨿ B) = KZero.mk C A + KZero.mk C B := by
  rw [← KZero.mk_eq_of_iso (biprod.isoCoprod A B)]
  exact KZero.mk_of_shortExact _ (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact

private lemma kZero_mk_natCoproduct {C : Type*} [Category.{v} C] [Abelian C]
    (F : ℕ → C) [HasCoproduct F] [HasCoproduct (fun n => F (n + 1))] :
    KZero.mk C (∐ F) = KZero.mk C (F 0) + KZero.mk C (∐ fun n => F (n + 1)) := by
  rw [KZero.mk_eq_of_iso (coproductIsoHeadTail F), kZero_mk_coprod]

private lemma kZero_mk_eq_of_shortExact_natCoproduct
    {C : Type*} [Category.{v} C] [Abelian C] (F : ℕ → C)
    [HasCoproduct F] [HasCoproduct (fun n => F (n + 1))]
    (G : C) (f : (∐ fun n => F (n + 1)) ⟶ ∐ F) (g : (∐ F) ⟶ G)
    (w : f ≫ g = 0) (h : (ShortComplex.mk f g w).ShortExact) :
    KZero.mk C (F 0) = KZero.mk C G := by
  have heq := KZero.mk_of_shortExact (ShortComplex.mk f g w) h
  change KZero.mk C (∐ F) = KZero.mk C (∐ fun n => F (n + 1)) + KZero.mk C G at heq
  rw [kZero_mk_natCoproduct] at heq
  exact add_right_cancel (heq.trans (add_comm _ _))

lemma restrict_comp_apply {X : Scheme.{u}} (M : X.Modules)
    {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) (s : Γ(M, W)) :
    M.presheaf.map (homOfLE hUV).op (M.presheaf.map (homOfLE hVW).op s) =
      M.presheaf.map (homOfLE (hUV.trans hVW)).op s := by
  exact (congrArg (fun f : Γ(M, W) ⟶ Γ(M, U) => f s)
    (M.presheaf.map_comp (homOfLE hVW).op (homOfLE hUV).op)).symm

/-- A section of `ℐⁿℳ` over `V`, for `ℳ` quasi-coherent, restricts near every point of `V` to an
affine open on which it lies in `ℐ(U)ⁿ • Γ(ℳ, U)`. -/
lemma exists_affine_restrict_mem_idealPow {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] {V : X.Opens}
    (s : Γ(M, V)) (hs : s ∈ (idealPowerMultiple I n M).toSubmodule.obj (op V)) (x : X)
    (hx : x ∈ V) :
    ∃ (U : X.affineOpens) (hUV : U.1 ≤ V), x ∈ U.1 ∧
      M.presheaf.map (homOfLE hUV).op s ∈ I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  refine ⟨⟨U, hU⟩, hUV, hxU, ?_⟩
  have h1 := (idealPowerMultiple I n M).toSubmodule.map (homOfLE hUV).op hs
  rw [Stacks.AlgebraicGeometry.IdealPowerComparison.obj_idealPowerMultiple I n M ⟨U, hU⟩] at h1
  exact h1

private lemma idealPowerMultiple_section_eq_zero {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] (O : X.Opens)
    (hO : ∀ U : X.affineOpens, U.1 ≤ O →
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) = ⊥)
    (V : X.Opens) (hVO : V ≤ O) (s : Γ(M, V))
    (hs : s ∈ (idealPowerMultiple I n M).toSubmodule.obj (op V)) :
    s = 0 := by
  apply M.isSheaf.section_ext
  intro x hx
  obtain ⟨U, hUV, hxU, hsU⟩ := exists_affine_restrict_mem_idealPow I n M s hs x hx
  refine ⟨U.1, hUV, hxU, ?_⟩
  have hz := (hO U (hUV.trans hVO)).le hsU
  rw [map_zero]
  exact (Submodule.mem_bot _).mp hz

private lemma idealPower_sections_eq_bot_image {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    (h : idealPowerMultiple (I.comap f) n (M.restrict f) = ⊥)
    (W : Y.affineOpens) :
    let T : X.affineOpens := ⟨f ''ᵁ W.1, W.2.image_of_isOpenImmersion f⟩
    I.ideal T ^ n • (⊤ : Submodule Γ(X, T) Γ(M, T)) = ⊥ := by
  let T : X.affineOpens := ⟨f ''ᵁ W.1, W.2.image_of_isOpenImmersion f⟩
  have hJ : (I.ideal T).map (f.appIso W.1).hom.hom = (I.comap f).ideal W := by
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    exact Ideal.map_comap_of_equiv (f.appIso W.1).commRingCatIsoToRingEquiv
  have hgen := (idealPowerMultiple_le_iff (I.comap f) n
    (M.restrict f) ⊥).mp (le_of_eq h) W
  rw [bottom_toSubmodule] at hgen
  apply le_antisymm ?_ bot_le
  refine Submodule.smul_le.mpr ?_
  intro r hr m hm
  have hr' : (f.appIso W.1).hom r ∈ (I.comap f).ideal W ^ n := by
    rw [← hJ, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hr
  have hz := hgen (Submodule.smul_mem_smul hr'
    (show ((M.restrictAppIso f W.1).inv m) ∈
      (⊤ : Submodule Γ(Y, W) Γ(M.restrict f, W)) from trivial))
  change (f.appIso W.1).inv ((f.appIso W.1).hom r) • m = 0 at hz
  simpa using hz

private lemma idealPower_sections_eq_bot_of_restrict {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    (h : idealPowerMultiple (I.comap f) n (M.restrict f) = ⊥)
    (U : X.affineOpens) (hU : U.1 ≤ f.opensRange) :
    I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) = ⊥ := by
  let W : Y.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage_of_isOpenImmersion f hU⟩
  have himage : f ''ᵁ W.1 = U.1 := by
    simp [W, Scheme.Hom.image_preimage_eq_opensRange_inf, inf_of_le_right hU]
  have heq : (⟨f ''ᵁ W.1, W.2.image_of_isOpenImmersion f⟩ : X.affineOpens) = U :=
    Subtype.ext himage
  have hz := idealPower_sections_eq_bot_image f I n M h W
  change I.ideal (⟨f ''ᵁ W.1, W.2.image_of_isOpenImmersion f⟩ : X.affineOpens) ^ n •
    (⊤ : Submodule Γ(X, (⟨f ''ᵁ W.1, W.2.image_of_isOpenImmersion f⟩ : X.affineOpens))
      Γ(M, (⟨f ''ᵁ W.1, W.2.image_of_isOpenImmersion f⟩ : X.affineOpens))) = ⊥ at hz
  exact (congrArg (fun V : X.affineOpens => I.ideal V ^ n •
    (⊤ : Submodule Γ(X, V) Γ(M, V)) = ⊥) heq).mp hz

private lemma idealPowerMultiple_isZero_restrict {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    [M.IsQuasicoherent]
    (h : idealPowerMultiple (I.comap f) n (M.restrict f) = ⊥) :
    IsZero (Scheme.Modules.restrict (Y := X)
      (idealPowerMultiple I n M).toSheafOfModules f) := by
  refine isZero_of_forall_section_eq_zero _ fun V s => ?_
  apply Subtype.ext
  show s.val = 0
  exact idealPowerMultiple_section_eq_zero I n M f.opensRange
    (idealPower_sections_eq_bot_of_restrict f I n M h) (f ''ᵁ V.unop)
    (f.image_le_opensRange _) s.val s.property

lemma idealPowerMultiple_eventually_isZero_restrict {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (M : X.Modules) [M.IsCoherent]
    (hM : SheafOfModules.supp M ⊆ (I.support : Set X)) (U : X.affineOpens) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      IsZero (Scheme.Modules.restrict (Y := X)
        (idealPowerMultiple I n M).toSheafOfModules U.1.ι) := by
  obtain ⟨N, hN⟩ := exists_idealPower_restrict_eq_bot I M hM U
  refine ⟨N, fun n hn => idealPowerMultiple_isZero_restrict U.1.ι I n M ?_⟩
  exact le_bot_iff.mp ((idealPowerMultiple_antitone (I.comap U.1.ι)
    (M.restrict U.1.ι) hn).trans_eq hN)

lemma coherent_idealPowerMultiple_coproduct {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (M : X.Modules) [M.IsCoherent]
    (hM : SheafOfModules.supp M ⊆ (I.support : Set X)) :
    (∐ fun n : ℕ => (idealPowerMultiple I n M).toSheafOfModules).IsCoherent :=
  coherent_natCoproduct_of_eventually_isZero_restrict _
    (idealPowerMultiple_isCoherent I M) (idealPowerMultiple_eventually_isZero_restrict I M hM)


lemma isZero_coproduct {C : Type*} [Category.{v} C] [HasZeroMorphisms C]
    {ι : Type*} (F : ι → C) [HasCoproduct F] (h : ∀ j, IsZero (F j)) :
    IsZero (∐ F) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Limits.Sigma.hom_ext
  intro j
  exact (h j).eq_of_src _ _

lemma supp_natCoproduct_subset {X : Scheme.{u}}
    (F : ℕ → X.Modules) (Z : Set X)
    (h : ∀ j, SheafOfModules.supp (F j) ⊆ Z) :
    SheafOfModules.supp (∐ F) ⊆ Z := by
  intro x hx
  by_contra hn
  let G := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits X.ringCatSheaf x
  have : PreservesColimitsOfSize.{0, 0} G := preservesColimitsOfSize_shrink G
  have hzero (j : ℕ) : IsZero (G.obj (F j)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    refine ⟨fun a b => ?_⟩
    have hz (a : G.obj (F j)) : a = 0 := by
      by_contra ha
      exact hn (h j ⟨a, ha⟩)
    exact (hz a).trans (hz b).symm
  have hz : IsZero (G.obj (∐ F)) :=
    (isZero_coproduct (fun j => G.obj (F j)) hzero).of_iso (PreservesCoproduct.iso G F)
  have hs := ModuleCat.isZero_iff_subsingleton.mp hz
  exact hx.choose_spec (hs.elim _ _)

private lemma fullSubcategory_hasCoproduct {C : Type*} [Category.{v} C]
    (P : ObjectProperty C) {ι : Type*} (F : ι → P.FullSubcategory)
    [HasCoproduct (fun j => (F j).obj)] (h : P (∐ fun j => (F j).obj)) :
    HasCoproduct F := by
  let c : Cofan F := Cofan.mk ⟨_, h⟩
    (fun j => ObjectProperty.homMk (Limits.Sigma.ι (fun j => (F j).obj) j))
  refine ⟨⟨c, Cofan.IsColimit.mk _
    (fun s => ObjectProperty.homMk (Limits.Sigma.desc (fun j => (s.inj j).hom))) ?_ ?_⟩⟩
  · intro s j
    apply ObjectProperty.hom_ext
    exact Limits.Sigma.ι_desc _ _
  · intro s m hm
    apply ObjectProperty.hom_ext
    apply Limits.Sigma.hom_ext
    intro j
    exact (congrArg (fun f => f.hom) (hm j)).trans
      (Limits.Sigma.ι_desc (fun j => (s.inj j).hom) j).symm

end

end AlgebraicGeometry.SupportedCoherentDevissage

end
