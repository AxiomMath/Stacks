module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.SupportedSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.SupportedSections
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Quasi-coherence of the sections supported on a closed subset

Let `Z` be a closed subset of a scheme whose open complement `V` is retrocompact, and let `F` be
a quasi-coherent module. The submodule of sections of `F` supported on `Z` is quasi-coherent.

A local section of `F` is supported on `Z` exactly when it restricts to zero on `V`, so the
supported-sections submodule is the kernel of the unit `F ⟶ j_* j^* F` of the restriction
adjunction along the open immersion `j : V ⟶ X`. Retrocompactness of `V` says that `j` is
quasi-compact, hence the pushforward is quasi-coherent, and a kernel of a morphism of
quasi-coherent modules is quasi-coherent.

## Main results

* `Stacks.AlgebraicGeometry.EmbeddedPoints.isRetrocompact_of_isLocallyNoetherian`: on a locally
  Noetherian scheme every subset is retrocompact.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.supportedSectionsSubmodule_isQuasicoherent`: the
  sections supported on a closed subset with retrocompact complement form a quasi-coherent
  submodule.

## Implementation notes

The identification of the supported sections with the kernel is checked section by section: the
comparison map is a morphism of sheaves of modules whose component over every open is bijective,
which is enough because a morphism of sheaves of modules is an isomorphism as soon as all its
components are.

## References

* [Stacks Project, Tag 07ZP](https://stacks.math.columbia.edu/tag/07ZP)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.EmbeddedPoints

variable {X : Scheme.{u}}

/-- On a locally Noetherian scheme every subset is retrocompact: a compact open subscheme is
Noetherian, and in a Noetherian space every subset is compact. -/
@[ega "IV 1.8.1" "special case"]
lemma isRetrocompact_of_isLocallyNoetherian [IsLocallyNoetherian X] (S : Set X) :
    IsRetrocompact S := by
  intro U hUc hUo
  let V : X.Opens := ⟨U, hUo⟩
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hUc
  have : IsNoetherian V.toScheme := ⟨⟩
  have hc : IsCompact {x : V | x.1 ∈ S} :=
    @NoetherianSpace.isCompact V _ (inferInstanceAs (NoetherianSpace V.toScheme)) _
  have heq : Subtype.val '' {x : V | x.1 ∈ S} = S ∩ U := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨hxS, hxU⟩
      exact ⟨⟨x, hxU⟩, hxS, rfl⟩
  exact heq ▸ hc.image continuous_subtype_val

/-- Alias of `AlgebraicGeometry.section_map_eq_zero_iff_germs`. -/
alias map_eq_zero_iff_forall_germ_eq_zero := _root_.AlgebraicGeometry.section_map_eq_zero_iff_germs

/-- The open complement of a closed subset of a scheme. -/
def complementOpens (Z : Set X) (hZ : IsClosed Z) : X.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩

/-- A section of a module on a scheme is supported on a closed subset exactly when the unit of
the restriction adjunction along the inclusion of the open complement kills it, that is, exactly
when it restricts to zero on the complement. -/
lemma mem_supportedSectionsSubmodule_iff_unit_eq_zero (Z : Set X) (hZ : IsClosed Z)
    (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) :
    s ∈ (Scheme.Modules.supportedSectionsSubmodule Z F).toSubmodule.obj (op U) ↔
      ((Scheme.Modules.restrictAdjunction (complementOpens Z hZ).ι).unit.app F).app U s = 0 := by
  let V : X.Opens := complementOpens Z hZ
  let j : V.toScheme ⟶ X := V.ι
  rw [Scheme.Modules.mem_supportedSectionsSubmodule_iff,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  let W : X.Opens := j ''ᵁ (j ⁻¹ᵁ U)
  have hW : W ≤ U := j.image_preimage_le U
  change (∀ (x : X) (hx : x ∈ U), x ∉ Z →
      TopCat.Presheaf.germ F.presheaf U x hx s = 0) ↔
    F.presheaf.map (homOfLE hW).op s = 0
  rw [map_eq_zero_iff_forall_germ_eq_zero F U W hW s]
  have hWmem (x : X) : x ∈ W ↔ x ∈ U ∧ x ∉ Z := by
    change x ∈ Set.image j.base {y : V.toScheme | j.base y ∈ U} ↔ _
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by simpa [j] using hy, y.2⟩
    · rintro ⟨hxU, hxZ⟩
      exact ⟨⟨x, hxZ⟩, hxU, rfl⟩
  exact ⟨fun hs x hxW ↦ hs x ((hWmem x).1 hxW).1 ((hWmem x).1 hxW).2,
    fun hs x hxU hxZ ↦ hs x ((hWmem x).2 ⟨hxU, hxZ⟩)⟩

/-- **Stacks Project, Tag 07ZP.** The submodule of sections supported on a closed subset with
retrocompact open complement is quasi-coherent. -/
theorem supportedSectionsSubmodule_isQuasicoherent (Z : Set X) (hZ : IsClosed Z)
    (hZc : IsRetrocompact Zᶜ) (F : X.Modules) (hF : F.IsQuasicoherent) :
    (Scheme.Modules.supportedSectionsSubmodule Z F).toSheafOfModules.IsQuasicoherent := by
  classical
  let V : X.Opens := complementOpens Z hZ
  let j : V.toScheme ⟶ X := V.ι
  let N := Scheme.Modules.supportedSectionsSubmodule Z F
  let P : X.Modules := N.toSheafOfModules
  let ι : P ⟶ F := N.ι
  let g : F ⟶ ((Scheme.Modules.pushforward j).obj ((Scheme.Modules.restrictFunctor j).obj F)) :=
    (Scheme.Modules.restrictAdjunction j).unit.app F
  have : QuasiCompact j := quasiCompact_iff_isSpectralMap.mpr (by
    change IsSpectralMap (Subtype.val : V → X)
    exact IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hZc)
  have hpush : ((Scheme.Modules.pushforward j).obj
      ((Scheme.Modules.restrictFunctor j).obj F)).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent j _
  have hzero : ι ≫ g = 0 := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    exact (mem_supportedSectionsSubmodule_iff_unit_eq_zero Z hZ F U s.1).mp s.2
  let k : P ⟶ kernel g := kernel.lift g ι hzero
  have hk : IsIso k := by
    refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U ↦ ?_
    refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
    have hc : Scheme.Modules.Hom.app k U ≫ (kernel.ι g).app U = Scheme.Modules.Hom.app ι U :=
      congrArg (fun q : P ⟶ F ↦ Scheme.Modules.Hom.app q U) (kernel.lift_ι g ι hzero)
    have hcomp (x : Γ(P, U)) := congrArg (fun q ↦ q x) hc
    refine ⟨fun s t hst ↦
      Subtype.ext (((hcomp s).symm.trans (congrArg ((kernel.ι g).app U) hst)).trans (hcomp t)),
      fun t ↦ ?_⟩
    let s : Γ(F, U) := (kernel.ι g).app U t
    have hs : s ∈ N.toSubmodule.obj (op U) := by
      refine (mem_supportedSectionsSubmodule_iff_unit_eq_zero Z hZ F U s).2 ?_
      have hz := congrArg
        (fun q : kernel g ⟶ (Scheme.Modules.pushforward j).obj
          ((Scheme.Modules.restrictFunctor j).obj F) ↦ Scheme.Modules.Hom.app q U)
        (kernel.condition g)
      change (kernel.ι g).app U ≫ Scheme.Modules.Hom.app g U = 0 at hz
      have hz2 := ConcreteCategory.congr_hom hz t
      rw [ConcreteCategory.comp_apply] at hz2
      exact hz2.trans rfl
    have hm : Mono ((Scheme.Modules.toPresheaf X).map (kernel.ι g)) := inferInstance
    exact ⟨⟨s, hs⟩, (AddCommGrpCat.mono_iff_injective _).mp
      ((NatTrans.mono_iff_mono_app _).mp hm (op U)) (hcomp ⟨s, hs⟩)⟩
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (asIso k).symm
    (@Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel _ _ _ g hF hpush)

end Stacks.AlgebraicGeometry.EmbeddedPoints

end
