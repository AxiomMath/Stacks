module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Constructible
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.SupportedSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.SupportedSections
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherence of the sections supported in a closed subset

Let `Z` be a closed subset of a scheme whose open complement is retrocompact, and let `F` be a
quasi-coherent module. The subsheaf of `F` of sections all of whose germs outside `Z` vanish is
again quasi-coherent.

On an affine open the supported sections admit a purely algebraic description: they are the
sections annihilated by a power of any finitely generated ideal cutting out the closed subset
there.

## Main results

* `AlgebraicGeometry.supportedSectionsSubmodule_isQuasicoherent`: the supported-sections
  submodule sheaf of a quasi-coherent module is quasi-coherent.
* `AlgebraicGeometry.mem_supportedSectionsSubmodule_iff_exists_pow_le_annihilator` is the
  **torsion description of the supported sections** over an affine open: a section of a
  quasi-coherent module is supported on the closed subset exactly when some power of a
  finitely generated ideal cutting that subset out annihilates it.

## Implementation notes

The submodule sheaf is `AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule`, the
construction of [Stacks, Tag 084L]. It is identified with the kernel of the unit
`F ⟶ j_* (F|_{Zᶜ})` of the restriction-pushforward adjunction along the inclusion `j` of the
complement: a section over `U` has all its germs outside `Z` zero exactly when its restriction
to `U ∩ Zᶜ` is zero, which is what that unit computes. Quasi-coherence then comes from the two
closure properties of quasi-coherent modules the kernel is built out of — pushforward along a
quasi-compact quasi-separated morphism, which is [Stacks, Tag 01LC], and kernels. Retrocompactness
of `Zᶜ` is exactly quasi-compactness of `j`, by `IsRetrocompact_iff_isSpectralMap_subtypeVal`;
quasi-separatedness is automatic for the inclusion of an open.

The torsion description is the two implications of the tag read through the annihilator ideal
of the section, `LinearMap.ker (LinearMap.toSpanSingleton _ _ s)`. For the direction that
needs quasi-coherence, every `g` in the ideal has its basic open disjoint from the closed
subset, so the section restricts to zero there; the sections over a basic open of an affine
open are the localization away from `g`
(`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`), so a power
of `g` annihilates the section, the ideal lies in the radical of the annihilator, and
`Ideal.exists_pow_le_of_le_radical_of_fg` converts that into a single power of the ideal — this
is where finite generation is used. The other direction needs no quasi-coherence: at a point
outside the closed subset some `g` of the ideal is invertible, and then so is the restriction
of `g ^ n`, which kills the restricted section.

## References

* [Stacks Project, Tag 07ZP](https://stacks.math.columbia.edu/tag/07ZP)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

private noncomputable def complementOpen {X : Scheme.{u}} (Z : Set X)
    (hZ : IsClosed Z) : X.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The subsheaf of sections supported on a closed subset with retrocompact complement is
quasicoherent. -/
@[stacks 07ZP "supported_sections_is_quasicoherent"]
public theorem supportedSectionsSubmodule_isQuasicoherent {X : Scheme.{u}} (Z : Set X)
    (hZ : IsClosed Z) (hZc : IsRetrocompact Zᶜ) (F : X.Modules) [F.IsQuasicoherent] :
    (AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule Z
      F).toSheafOfModules.IsQuasicoherent := by
  classical
  let V : X.Opens := complementOpen Z hZ
  let j : V.toScheme ⟶ X := V.ι
  let N := AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule Z F
  let N' : X.Modules := N.toSheafOfModules
  let ι' : N' ⟶ F := N.ι
  let g : F ⟶ ((Scheme.Modules.pushforward j).obj
      ((Scheme.Modules.restrictFunctor j).obj F)) :=
    (Scheme.Modules.restrictAdjunction j).unit.app F
  have : QuasiCompact j := quasiCompact_iff_isSpectralMap.mpr (by
    change IsSpectralMap (Subtype.val : V → X)
    exact (IsRetrocompact_iff_isSpectralMap_subtypeVal).mp hZc)
  have : ((Scheme.Modules.pushforward j).obj
      ((Scheme.Modules.restrictFunctor j).obj F)).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent j ((Scheme.Modules.restrictFunctor j).obj F)
  have hzero : ι' ≫ g = 0 := by
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext s
    exact (supported_iff_restrict_eq_zero Z hZ F U s.1).mp s.2
  let k : N' ⟶ kernel g := kernel.lift g ι' hzero
  have hk : IsIso k := by
    refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U =>
      (ConcreteCategory.isIso_iff_bijective _).mpr ?_
    have hc : Scheme.Modules.Hom.app k U ≫ (kernel.ι g).app U =
        Scheme.Modules.Hom.app ι' U :=
      congrArg (fun q : N' ⟶ F => Scheme.Modules.Hom.app q U) (kernel.lift_ι g ι' hzero)
    have hcomp (x : Γ(N', U)) := congrArg (fun q => q x) hc
    refine ⟨fun s t hst => Subtype.ext <|
      (hcomp s).symm.trans ((congrArg ((kernel.ι g).app U) hst).trans (hcomp t)), fun t => ?_⟩
    let s : Γ(F, U) := (kernel.ι g).app U t
    have hs : s ∈ N.toSubmodule.obj (op U) := by
      apply (supported_iff_restrict_eq_zero Z hZ F U s).2
      have hz := congrArg
        (fun q : kernel g ⟶ (Scheme.Modules.pushforward j).obj
          ((Scheme.Modules.restrictFunctor j).obj F) => Scheme.Modules.Hom.app q U)
        (kernel.condition g)
      change (kernel.ι g).app U ≫ Scheme.Modules.Hom.app g U = 0 at hz
      have hzt := congrArg (fun q => (ConcreteCategory.hom q) t) hz
      simp only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero,
        AddMonoidHom.zero_apply] at hzt
      exact hzt
    have hm : Mono ((Scheme.Modules.toPresheaf X).map (kernel.ι g)) := inferInstance
    exact ⟨⟨s, hs⟩, (AddCommGrpCat.mono_iff_injective _).mp
      ((NatTrans.mono_iff_mono_app _).mp hm (op U)) (hcomp ⟨s, hs⟩)⟩
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (asIso k).symm
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel g)

/-! ### The torsion description of the supported sections on an affine open -/

section Torsion

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

/-- A section killed by a power of `g` restricts to zero on the basic open of `g`, where that
power of `g` is invertible. No quasi-coherence is needed. -/
private lemma res_basicOpen_eq_zero_of_pow_smul_eq_zero {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) (g : Γ(X, U)) (s : Γ(F, U)) {n : ℕ} (hs : (g ^ n) • s = 0) :
    F.presheaf.map (homOfLE (X.basicOpen_le g)).op s = 0 := by
  have hunit : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n)) := by
    rw [map_pow]
    exact (X.toRingedSpace.isUnit_res_basicOpen g).pow n
  have key := F.map_smul (homOfLE (X.basicOpen_le g)) (g ^ n) s
  rw [hs, map_zero] at key
  exact hunit.smul_eq_zero.mp key.symm

/-- The basic open of a member of an ideal cutting out `Z` on `U` misses `Z`. -/
private lemma basicOpen_subset_diff_of_mem {X : Scheme.{u}} {Z : Set X} {U : X.Opens}
    {I : Ideal Γ(X, U)}
    (hI : Z ∩ (U : Set X) = X.zeroLocus (U := U) (I : Set Γ(X, U)) ∩ (U : Set X))
    {g : Γ(X, U)} (hg : g ∈ I) : (X.basicOpen g : Set X) ⊆ (U : Set X) \ Z := by
  intro x hx
  refine ⟨X.basicOpen_le g hx, fun hxZ => ?_⟩
  have hmem : x ∈ X.zeroLocus (U := U) (I : Set Γ(X, U)) :=
    ((Set.ext_iff.mp hI x).mp ⟨hxZ, X.basicOpen_le g hx⟩).1
  exact (X.mem_zeroLocus_iff _ x).mp hmem g hg hx

/-- **Stacks 07ZP, the torsion description of the supported sections.** Let `Z` be a subset of
a scheme `X`, let `U` be an affine open and let `I ⊆ 𝒪_X(U)` be a finitely generated ideal
whose zero locus meets `U` in `Z`. A section of a quasi-coherent `𝒪_X`-module over `U` has all
its germs outside `Z` equal to zero exactly when some power of `I` annihilates it.

Such an `I` exists for every closed `Z` with retrocompact complement, by
`AlgebraicGeometry.exists_fg_ideal_zeroLocus_eq_inter`; so the two together are the tag's
description of the sections of the supported-section subsheaf over an affine open. -/
@[stacks 07ZP "the supported sections over an affine open are the ideal-power torsion"]
theorem mem_supportedSectionsSubmodule_iff_exists_pow_le_annihilator {X : Scheme.{u}}
    (Z : Set X) (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    {I : Ideal Γ(X, U)} (hIfg : I.FG)
    (hI : Z ∩ (U : Set X) = X.zeroLocus (U := U) (I : Set Γ(X, U)) ∩ (U : Set X))
    (s : Γ(F, U)) :
    s ∈ (supportedSectionsSubmodule Z F).toSubmodule.obj (op U) ↔
      ∃ n : ℕ, ∀ a ∈ I ^ n, a • s = 0 := by
  rw [mem_supportedSectionsSubmodule_iff]
  constructor
  · intro hs
    set J : Ideal Γ(X, U) := LinearMap.ker (LinearMap.toSpanSingleton Γ(X, U) Γ(F, U) s) with hJ
    have hmemJ : ∀ a : Γ(X, U), a ∈ J ↔ a • s = 0 := fun a => by
      rw [hJ, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    have hrad : I ≤ J.radical := by
      intro g hg
      have hres : F.presheaf.map (homOfLE (X.basicOpen_le g)).op s = 0 := by
        rw [section_map_eq_zero_iff_germs F U (X.basicOpen g) (X.basicOpen_le g) s]
        intro x hx
        exact hs x (X.basicOpen_le g hx) (basicOpen_subset_diff_of_mem hI hg hx).2
      let _ := moduleOfLE F (X.basicOpen_le g)
      have hloc : IsLocalizedModule.Away g (restrictₗ F (X.basicOpen_le g)) :=
        isLocalizedModule_restrictₗ F hU g rfl (X.basicOpen_le g)
      obtain ⟨⟨_, k, rfl⟩, ht⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g)
        (restrictₗ F (X.basicOpen_le g))).mp hres
      exact ⟨k, (hmemJ _).mpr ht⟩
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hIfg
    exact ⟨n, fun a ha => (hmemJ a).mp (hn ha)⟩
  · rintro ⟨n, hn⟩ x hx hxZ
    have hxnot : x ∉ X.zeroLocus (U := U) (I : Set Γ(X, U)) := fun hmem =>
      hxZ ((Set.ext_iff.mp hI x).mpr ⟨hmem, hx⟩).1
    obtain ⟨g, hg, hxg⟩ : ∃ g ∈ (I : Set Γ(X, U)), x ∈ X.basicOpen g := by
      by_contra hcon
      exact hxnot ((X.mem_zeroLocus_iff _ x).mpr fun f hf hxf => hcon ⟨f, hf, hxf⟩)
    calc TopCat.Presheaf.germ F.presheaf U x hx s
        = TopCat.Presheaf.germ F.presheaf (X.basicOpen g) x hxg
            (F.presheaf.map (homOfLE (X.basicOpen_le g)).op s) :=
          (TopCat.Presheaf.germ_res_apply F.presheaf
            (homOfLE (X.basicOpen_le g)) x hxg s).symm
      _ = 0 := by
        rw [res_basicOpen_eq_zero_of_pow_smul_eq_zero F U g s (hn _ (Ideal.pow_mem_pow hg n)),
          map_zero]

end Torsion

end AlgebraicGeometry

end

