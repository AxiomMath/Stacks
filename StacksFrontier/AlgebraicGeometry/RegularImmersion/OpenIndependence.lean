module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.QuasiRegular
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Basic
public import StacksFrontier.RingTheory.Koszul.FlatQuotient
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Abelian
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Sets
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.RingedSpaceComorphism
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-regularity of an immersion does not depend on the chosen open

An immersion `i : Z ⟶ X` factors as a closed immersion into the open subscheme `i.coborderRange`
of `X`, and
`Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion` is quasi-regularity of the
defining ideal of that *canonical* closed factor.  Any other open in which the immersion is closed
gives the same answer, so quasi-regularity of a base-changed immersion may be tested on the
preimage of `i.coborderRange`.

## Main results

* `Stacks.AlgebraicGeometry.isQuasiRegularImmersion_iff_of_open`: for any open `U` of `X` with a
  closed immersion `j : Z ⟶ U` such that `j ≫ U.ι = i`, the immersion `i` is quasi-regular if and
  only if the defining ideal of `j` is a quasi-regular ideal sheaf on `U`.
* `Stacks.AlgebraicGeometry.baseChangeLiftCoborder`: for a base change `i'` of `i` along
  `p : X' ⟶ X`, the closed immersion `Z' ⟶ p ⁻¹ᵁ i.coborderRange` factoring `i'`.
* `Stacks.AlgebraicGeometry.isQuasiRegularImmersion_baseChange_iff`: quasi-regularity of `i'`
  read on `p ⁻¹ᵁ i.coborderRange`.

## References

* [Stacks Project, Lemma 31.21.2 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
* [Stacks Project, Lemma 31.20.2 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
* [Stacks Project, Lemma 31.22.1 (Tag 063R)](https://stacks.math.columbia.edu/tag/063R)
* [Stacks Project, Lemma 26.4.5 (Tag 01QO)](https://stacks.math.columbia.edu/tag/01QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RingedSpace

namespace Stacks.AlgebraicGeometry

universe u

section Factorization

/-- An open subscheme in which an immersion is closed is contained in `i.coborderRange`. -/
private alias open_le_coborderRange :=
  Stacks.AlgebraicGeometry.RegularIdealSheaf.le_coborderRange_of_isClosedImmersion

/-- The closed factor through an arbitrary open in which the immersion is closed, followed by
the inclusion of that open into `i.coborderRange`, is the canonical closed factor. -/
private lemma closedFactor_eq_liftCoborder {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.Opens) (j : Z ⟶ U.toScheme) [IsClosedImmersion j]
    (hij : j ≫ U.ι = i) :
    j ≫ Scheme.Hom.resLE (𝟙 X) i.coborderRange U
      (open_le_coborderRange i U j hij) = i.liftCoborder := by
  apply (cancel_mono i.coborderRange.ι).1
  calc
    (j ≫ Scheme.Hom.resLE (𝟙 X) i.coborderRange U
      (open_le_coborderRange i U j hij)) ≫ i.coborderRange.ι = j ≫ U.ι := by simp
    _ = i := hij
    _ = i.liftCoborder ≫ i.coborderRange.ι := i.liftCoborder_ι.symm

end Factorization

section Support

/-- Membership in the support of a sheaf of modules on a scheme is nontriviality of the stalk
of the underlying presheaf of abelian groups. -/
private lemma moduleSheaf_supp_iff_nontrivial_stalk {X : Scheme.{u}}
    (M : X.Modules) (x : X) :
    x ∈ (⟨M.val, M.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp ↔
      Nontrivial ((TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((Scheme.Modules.toPresheaf X).obj M)) x) := by
  let F : RingedSpace.ModuleSheaf.{u} X.toRingedSpace := ⟨M.val, M.isSheaf⟩
  change (∃ a : F.abPresheaf.stalk x, a ≠ 0) ↔ _
  rw [(nontrivial_iff_exists_ne (0 : F.abPresheaf.stalk x)).symm]
  rfl

/-- Isomorphic sheaves of modules have the same support. -/
private lemma moduleSheaf_supp_iso {X : Scheme.{u}} (M N : X.Modules) (e : M ≅ N) :
    (⟨M.val, M.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp =
      (⟨N.val, N.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp := by
  ext x
  rw [moduleSheaf_supp_iff_nontrivial_stalk, moduleSheaf_supp_iff_nontrivial_stalk]
  exact Equiv.nontrivial_congr ((TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso
    ((Scheme.Modules.toPresheaf X).mapIso e)).addCommGroupIsoToAddEquiv.toEquiv

/-- The pushforward of a sheaf of modules along a closed immersion is supported on the image. -/
private lemma scheme_pushforward_support_subset_range {Z X : Scheme.{u}}
    (j : Z ⟶ X) [IsClosedImmersion j] (M : Z.Modules) :
    (⟨((Scheme.Modules.pushforward j).obj M).val,
      ((Scheme.Modules.pushforward j).obj M).isSheaf⟩ :
        RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp ⊆ Set.range j.base := by
  intro x hx
  rw [moduleSheaf_supp_iff_nontrivial_stalk] at hx
  by_contra hnot
  let 𝒜 : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z) :=
    ⟨(Scheme.Modules.toPresheaf Z).obj M, Scheme.Modules.isSheaf M⟩
  have hzero := closedInclusion_pushforward_stalk_isZero_of_not_mem_range
    (TopCat.of Z) (TopCat.of X) j.base j.isClosedEmbedding 𝒜 x hnot
  have hzero' : IsZero ((show TopCat.Presheaf Ab.{u} (TopCat.of X) from
      ((Scheme.Modules.pushforward j).obj M).val.presheaf).stalk x) := by
    change IsZero
      (TopCat.Presheaf.stalk
        ((closedInclusionPushforward (TopCat.of Z) (TopCat.of X) j.base).obj 𝒜).1 x)
    exact hzero
  exact (not_nontrivial_iff_subsingleton.mpr
    (AddCommGrpCat.subsingleton_of_isZero hzero')) hx

/-- The structure sheaf of a closed subscheme is supported on the image. -/
private lemma scheme_pushforward_support_superset_range {Z X : Scheme.{u}}
    (j : Z ⟶ X) [IsClosedImmersion j] :
    Set.range j.base ⊆
      (⟨((Scheme.Modules.pushforward j).obj
          (SheafOfModules.unit (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace))).val,
        ((Scheme.Modules.pushforward j).obj
          (SheafOfModules.unit
            (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace))).isSheaf⟩ :
          RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp := by
  intro x hx
  obtain ⟨z, rfl⟩ := hx
  rw [moduleSheaf_supp_iff_nontrivial_stalk]
  let M : Z.Modules := SheafOfModules.unit (structureSheafRing Z.toRingedSpace)
  let 𝒜 : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z) :=
    ⟨(Scheme.Modules.toPresheaf Z).obj M, Scheme.Modules.isSheaf M⟩
  let e := preservesColimitIso
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
    ((OpenNhds.inclusion z).op ⋙ Z.toRingedSpace.presheaf)
  have hnRing : Nontrivial (↑(Z.toRingedSpace.presheaf.stalk z)) := inferInstance
  have hn : Nontrivial (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) 𝒜.obj z) :=
    (Equiv.nontrivial_congr e.addCommGroupIsoToAddEquiv.toEquiv).mp hnRing
  have : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} j.base 𝒜.obj z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      (C := AddCommGrpCat.{u}) j.isClosedEmbedding.isInducing 𝒜.obj z
  have hn' : Nontrivial
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((closedInclusionPushforward (TopCat.of Z)
          (TopCat.of X) j.base).obj 𝒜).obj (j.base z)) :=
    (Equiv.nontrivial_congr
      (asIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        j.base 𝒜.obj z)).addCommGroupIsoToAddEquiv.toEquiv).mpr hn
  change Nontrivial
    (TopCat.Presheaf.stalk
      (C := AddCommGrpCat.{u}) ((Scheme.Modules.toPresheaf X).obj
        ((Scheme.Modules.pushforward j).obj
          (SheafOfModules.unit (structureSheafRing Z.toRingedSpace)))) (j.base z))
  exact hn'

end Support

section Kernel

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- The embedded kernel of a morphism of sheaves of modules is a kernel in the categorical
sense. -/
private def kernelSubmodule_isLimit {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    IsLimit (Fork.ofι (kernelSubmodule f).ι
      (show (kernelSubmodule f).ι ≫ f = (kernelSubmodule f).ι ≫ 0 from by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.Hom.ext
        ext U s
        change (f.val.app U) (((kernelSubmodule f).ι.val.app U) s) = 0
        exact s.property)) := by
  let K := kernelSubmodule f
  have hcond : K.ι ≫ f = K.ι ≫ 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.Hom.ext
    ext U s
    change (f.val.app U) ((K.ι.val.app U) s) = 0
    exact s.property
  refine Fork.IsLimit.mk (Fork.ofι K.ι hcond) (fun s ↦ ?_) ?_ ?_
  · let φ : s.pt.val.presheaf ⟶ K.toSubmodule.toPresheafOfModules.presheaf :=
      { app := fun U ↦ AddCommGrpCat.ofHom {
          toFun := fun x ↦ ⟨s.ι.val.app U x, by
            have hzero := congrArg (fun g => g.val.app U x) s.condition
            change (f.val.app U) ((s.ι.val.app U) x) = 0 at hzero
            exact hzero⟩
          map_zero' := by apply Subtype.ext; exact (s.ι.val.app U).hom.map_zero
          map_add' := by intro x y; apply Subtype.ext; exact (s.ι.val.app U).hom.map_add x y }
        naturality := by
          intro U V g
          ext x
          apply Subtype.ext
          exact congrArg (fun q => q x) (s.ι.val.naturality g) }
    exact ⟨PresheafOfModules.homMk φ (by
      intro U r x
      apply Subtype.ext
      exact (s.ι.val.app U).hom.map_smul r x)⟩
  · intro s
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.Hom.ext
    ext U x
    rfl
  · intro s m hm
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.Hom.ext
    ext U x
    apply Subtype.ext
    exact congrArg (fun q => q.val.app U x) hm

/-- An epimorphism of sheaves of modules presents its target as the quotient by its embedded
kernel. -/
private def kernelQuotientIso_of_epi {M N : SheafOfModules.{u} R} (f : M ⟶ N) [Epi f] :
    cokernel (kernelSubmodule f).ι ≅ N :=
  (IsColimit.coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel _ (kernelSubmodule_isLimit f))
    (cokernelIsCokernel (kernelSubmodule f).ι)).symm

/-- An embedded submodule sheaf is the kernel of the projection onto its quotient. -/
private lemma kernelSubmodule_cokernel_π_eq {M : SheafOfModules.{u} R} (K : M.Submodule) :
    kernelSubmodule (CategoryTheory.Limits.cokernel.π K.ι) = K := by
  let q : M ⟶ cokernel K.ι := CategoryTheory.Limits.cokernel.π K.ι
  have hK : IsLimit (Fork.ofι K.ι (show K.ι ≫ q = K.ι ≫ 0 from by simp [q])) :=
    Abelian.monoIsKernelOfCokernel
      (Cofork.ofπ q (by simp [q])) (CategoryTheory.Limits.cokernelIsCokernel K.ι)
  let hker := kernelSubmodule_isLimit q
  let e := IsLimit.conePointUniqueUpToIso hK hker
  have hcomp : e.hom ≫ (kernelSubmodule q).ι = K.ι :=
    IsLimit.conePointUniqueUpToIso_hom_comp hK hker WalkingParallelPair.zero
  have hcompInv : e.inv ≫ K.ι = (kernelSubmodule q).ι :=
    IsLimit.conePointUniqueUpToIso_hom_comp hker hK WalkingParallelPair.zero
  apply SheafOfModules.Submodule.ext
  apply PresheafOfModules.Submodule.ext
  intro V
  apply Submodule.ext
  intro s
  constructor
  · intro hs
    let t := e.inv.val.app V ⟨s, hs⟩
    have ht : t.val = s := congrArg (fun g => g.val.app V ⟨s, hs⟩) hcompInv
    simpa [ht] using t.property
  · intro hs
    let t := e.hom.val.app V ⟨s, hs⟩
    have ht : t.val = s := congrArg (fun g => g.val.app V ⟨s, hs⟩) hcomp
    simpa [ht] using t.property

end Kernel

section StructureSheafEpi

/-- The structure-sheaf map of a closed immersion of schemes is an epimorphism of sheaves of
modules. -/
private alias structureSheafEpi_of_isClosedImmersion :=
  Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion

end StructureSheafEpi

section SupportRange

/-- The support of the quotient by the defining ideal of a closed immersion is its image. -/
lemma definingIdealQuotient_support_eq_range {Z X : Scheme.{u}}
    (j : Z ⟶ X) [IsClosedImmersion j] :
    idealQuotientSupport X.toRingedSpace (definingIdealOfHom j) = Set.range j.base := by
  have hepi : Epi (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom j.toLRSHom.toShHom)) := structureSheafEpi_of_isClosedImmersion j
  let e := kernelQuotientIso_of_epi
    (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom j.toLRSHom.toShHom))
  let Q : X.Modules := idealQuotient X.toRingedSpace (definingIdealOfHom j)
  let P : X.Modules := (Scheme.Modules.pushforward j).obj
    (SheafOfModules.unit (structureSheafRing Z.toRingedSpace))
  exact (moduleSheaf_supp_iso Q P e).trans
    (Set.Subset.antisymm (scheme_pushforward_support_subset_range j _)
      (scheme_pushforward_support_superset_range j))

end SupportRange

section Restriction

/-- The restriction of an ideal subsheaf along an open immersion: a section over `V` belongs to
it exactly when its transport to the image open belongs to the given ideal. -/
abbrev idealRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (J : (structureSheafModule Y.toRingedSpace).Submodule) :
    (structureSheafModule X.toRingedSpace).Submodule :=
  kernelSubmodule ((Scheme.Modules.restrictUnitIso f).inv ≫
    (Scheme.Modules.restrictFunctor f).map (cokernel.π J.ι))

/-- A section over `V` lies in the restricted ideal exactly when its transport to the image
open lies in the original ideal. -/
lemma mem_idealRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (J : (structureSheafModule Y.toRingedSpace).Submodule) (V : X.Opens) (s : Γ(X, V)) :
    s ∈ (idealRestriction f J).obj (op V) ↔
      (f.appIso V).inv s ∈ J.obj (op (f ''ᵁ V)) := by
  change (cokernel.π J.ι).val.app (op (f ''ᵁ V)) ((f.appIso V).inv s) = 0 ↔ _
  change (f.appIso V).inv s ∈ (kernelSubmodule (cokernel.π J.ι)).obj (op (f ''ᵁ V)) ↔ _
  rw [kernelSubmodule_cokernel_π_eq]

/-- The extension of an ideal subsheaf along a morphism: a section over `V` belongs to it
exactly when its pullback belongs to the given ideal. -/
abbrev idealExtension {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : (structureSheafModule X.toRingedSpace).Submodule) :
    (structureSheafModule Y.toRingedSpace).Submodule :=
  kernelSubmodule (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
    (Scheme.Modules.pushforward f).map (cokernel.π J.ι))

/-- A section over `V` lies in the extended ideal exactly when its pullback lies in the
original ideal. -/
lemma mem_idealExtension {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : (structureSheafModule X.toRingedSpace).Submodule) (V : Y.Opens) (s : Γ(Y, V)) :
    s ∈ (idealExtension f J).obj (op V) ↔ f.app V s ∈ J.obj (op (f ⁻¹ᵁ V)) := by
  change (cokernel.π J.ι).val.app (op (f ⁻¹ᵁ V)) (f.app V s) = 0 ↔ _
  change f.app V s ∈ (kernelSubmodule (cokernel.π J.ι)).obj (op (f ⁻¹ᵁ V)) ↔ _
  rw [kernelSubmodule_cokernel_π_eq]

private lemma mem_map_eq_iff {X : Scheme.{u}}
    (J : (structureSheafModule X.toRingedSpace).Submodule)
    {V W : X.Opens} (h : V = W) (s : Γ(X, W)) :
    X.presheaf.map (eqToHom h).op s ∈ J.obj (op V) ↔ s ∈ J.obj (op W) := by
  subst W
  simp

private lemma mem_idealExtension_image {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (J : (structureSheafModule X.toRingedSpace).Submodule) (V : X.Opens) (s : Γ(Y, f ''ᵁ V)) :
    s ∈ (idealExtension f J).obj (op (f ''ᵁ V)) ↔ (f.appIso V).hom s ∈ J.obj (op V) := by
  rw [mem_idealExtension, Scheme.Hom.appIso_hom, CommRingCat.comp_apply, mem_map_eq_iff]

/-- Transporting a section over `U` to the image of its preimage is the restriction map. -/
private lemma appIso_inv_app_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) (s : Γ(Y, U)) :
    (f.appIso (f ⁻¹ᵁ U)).inv (f.app U s) =
      Y.presheaf.map (homOfLE (Set.image_preimage_subset f U.1)).op s :=
  congrArg (fun k => (ConcreteCategory.hom k) s) (f.app_appIso_inv U)

/-- Transporting a section along `f.appIso V` and back is the identity. -/
private lemma appIso_hom_inv_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (V : X.Opens) (s : Γ(X, V)) : (f.appIso V).hom ((f.appIso V).inv s) = s :=
  (f.appIso V).commRingCatIsoToRingEquiv.apply_symm_apply s

private lemma idealRestriction_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {J K : (structureSheafModule Y.toRingedSpace).Submodule} (h : J ≤ K) :
    idealRestriction f J ≤ idealRestriction f K := by
  exact fun V s hs => (mem_idealRestriction f K V.unop s).2
    (h _ ((mem_idealRestriction f J V.unop s).1 hs))

private lemma idealRestriction_idealExtension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (J : (structureSheafModule X.toRingedSpace).Submodule) :
    idealRestriction f (idealExtension f J) = J := by
  apply SheafOfModules.Submodule.ext
  apply PresheafOfModules.Submodule.ext
  rintro ⟨V⟩
  apply Submodule.ext
  intro s
  refine (mem_idealRestriction f (idealExtension f J) V s).trans
    ((mem_idealExtension_image f J V ((f.appIso V).inv s)).trans ?_)
  rw [appIso_hom_inv_apply f V s]
  exact Iff.rfl

private lemma le_idealExtension_idealRestriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (J : (structureSheafModule Y.toRingedSpace).Submodule) :
    J ≤ idealExtension f (idealRestriction f J) := by
  intro V s hs
  apply (mem_idealExtension f (idealRestriction f J) V.unop s).2
  apply (mem_idealRestriction f J (f ⁻¹ᵁ V.unop) (f.app V.unop s)).2
  rw [appIso_inv_app_eq f V.unop s]
  exact J.toSubmodule.map _ hs

private lemma idealRestriction_generatedIdealOn {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (U : Y.Opens) {r : ℕ} (s : Fin r → Γ(Y, U)) :
    idealRestriction f (generatedIdealOn Y.toRingedSpace U s) =
      generatedIdealOn X.toRingedSpace (f ⁻¹ᵁ U) (fun i ↦ f.app U (s i)) := by
  apply le_antisymm
  · have h := generatedIdealOn_le Y.toRingedSpace U s
      (idealExtension f (generatedIdealOn X.toRingedSpace
        (f ⁻¹ᵁ U) (fun i ↦ f.app U (s i)))) (fun i ↦
          (mem_idealExtension _ _ _ _).2 (mem_generatedIdealOn _ _ _ i))
    simpa only [idealRestriction_idealExtension] using idealRestriction_mono f h
  · apply generatedIdealOn_le
    intro i
    exact (mem_idealExtension _ _ _ _).1
      (le_idealExtension_idealRestriction f _ _ (mem_generatedIdealOn _ _ s i))

private lemma idealRestriction_generatedIdealOn_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Opens) {r : ℕ} (s : Fin r → Γ(X, U)) :
    idealRestriction f (generatedIdealOn Y.toRingedSpace
      (f ''ᵁ U) (fun i ↦ (f.appIso U).inv (s i))) =
      generatedIdealOn X.toRingedSpace U s := by
  apply le_antisymm
  · have h := generatedIdealOn_le Y.toRingedSpace
      (f ''ᵁ U) (fun i ↦ (f.appIso U).inv (s i))
      (idealExtension f (generatedIdealOn X.toRingedSpace U s)) (by
        intro i
        rw [mem_idealExtension_image]
        simpa using mem_generatedIdealOn X.toRingedSpace U s i)
    simpa only [idealRestriction_idealExtension] using idealRestriction_mono f h
  · apply generatedIdealOn_le
    intro i
    rw [mem_idealRestriction]
    exact mem_generatedIdealOn _ _ _ i

private lemma mem_idealRestriction_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (J : (structureSheafModule Y.toRingedSpace).Submodule)
    (U : Y.Opens) (hU : U ≤ f.opensRange) (s : Γ(Y, U)) :
    f.app U s ∈ (idealRestriction f J).obj (op (f ⁻¹ᵁ U)) ↔ s ∈ J.obj (op U) := by
  rw [mem_idealRestriction]
  rw [appIso_inv_app_eq f U s]
  have he : f ''ᵁ (f ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hU]
  exact mem_map_eq_iff J he s

/-- A generating family for an ideal subsheaf transports to the restricted ideal along an open
immersion. -/
lemma isGeneratedByOn_restriction {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (J : (structureSheafModule Y.toRingedSpace).Submodule) (U : Y.Opens) {r : ℕ}
    (s : Fin r → Γ(Y, U)) (h : IsGeneratedByOn Y.toRingedSpace J U s) :
    IsGeneratedByOn X.toRingedSpace (idealRestriction f J)
      (f ⁻¹ᵁ U) (fun i ↦ f.app U (s i)) := by
  intro V hV
  rw [← idealRestriction_generatedIdealOn]
  apply Submodule.ext
  intro a
  rw (transparency := .default) [mem_idealRestriction, mem_idealRestriction,
    h (f ''ᵁ V) ((f.image_mono hV).trans (Set.image_preimage_subset f U.1))]

/-- A family generates an ideal subsheaf over the image of an open immersion exactly when it
generates the restricted ideal. -/
lemma isGeneratedByOn_image_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (J : (structureSheafModule Y.toRingedSpace).Submodule) (U : X.Opens) {r : ℕ}
    (s : Fin r → Γ(X, U)) :
    IsGeneratedByOn Y.toRingedSpace J (f ''ᵁ U) (fun i ↦ (f.appIso U).inv (s i)) ↔
      IsGeneratedByOn X.toRingedSpace (idealRestriction f J) U s := by
  constructor
  · intro h V hV
    rw [← idealRestriction_generatedIdealOn_image f U s]
    apply Submodule.ext
    intro a
    rw (transparency := .default) [mem_idealRestriction, mem_idealRestriction,
      h _ (f.image_mono hV)]
  · intro h V hV
    have hVr : V ≤ f.opensRange :=
      hV.trans (show f ''ᵁ U ≤ f.opensRange from Set.image_subset_range _ _)
    have hp : f ⁻¹ᵁ V ≤ U := by simpa using (Opens.map f.base).monotone hV
    apply Submodule.ext
    intro a
    rw (transparency := .default) [← mem_idealRestriction_preimage f J V hVr a,
      ← mem_idealRestriction_preimage f
        (generatedIdealOn Y.toRingedSpace (f ''ᵁ U)
          (fun i ↦ (f.appIso U).inv (s i))) V hVr a,
      idealRestriction_generatedIdealOn_image f U s, h _ hp]

/-- The defining ideal of `j ≫ f` restricts along the open immersion `f` to the defining ideal
of `j`. -/
lemma definingIdealOfHom_comp_open {Z X Y : Scheme.{u}} (j : Z ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion f] :
    idealRestriction f (definingIdealOfHom (j ≫ f)) = definingIdealOfHom j := by
  apply SheafOfModules.Submodule.ext
  apply PresheafOfModules.Submodule.ext
  rintro ⟨V⟩
  apply Submodule.ext
  intro s
  rw (transparency := .default) [mem_idealRestriction f (definingIdealOfHom (j ≫ f)) V s]
  change (j ≫ f).app (f ''ᵁ V) ((f.appIso V).inv s) = 0 ↔ j.app V s = 0
  have he : j ⁻¹ᵁ V = (j ≫ f) ⁻¹ᵁ (f ''ᵁ V) := by simp
  have hmorph : (f.appIso V).hom ≫ j.app V =
      (j ≫ f).appLE (f ''ᵁ V) (j ⁻¹ᵁ V) he.le := by
    rw [Scheme.Hom.appIso_hom', j.app_eq_appLE]
    exact Scheme.Hom.appLE_comp_appLE j f _ _ _ _ _
  have hm := congrArg (fun k => (ConcreteCategory.hom k) ((f.appIso V).inv s)) hmorph
  rw [CommRingCat.comp_apply] at hm
  rw [appIso_hom_inv_apply f V s] at hm
  have hi : Function.Injective (Z.presheaf.map (eqToHom he).op) :=
    (asIso (Z.presheaf.map (eqToHom he).op)).commRingCatIsoToRingEquiv.injective
  rw [← show Z.presheaf.map (eqToHom he).op
    ((j ≫ f).app (f ''ᵁ V) ((f.appIso V).inv s)) = j.app V s from hm.symm]
  exact (map_eq_zero_iff _ hi).symm

private lemma mem_extension_restriction_of_le {X : Scheme.{u}}
    (J : (structureSheafModule X.toRingedSpace).Submodule)
    {U V : X.Opens} (hVU : V ≤ U) (s : Γ(X, U)) :
    s ∈ (idealExtension V.ι (idealRestriction V.ι J)).obj (op U) ↔
      X.presheaf.map (homOfLE hVU).op s ∈ J.obj (op V) := by
  rw [mem_idealExtension, mem_idealRestriction]
  rw [appIso_inv_app_eq V.ι U s]
  have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = V := by
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_left.mpr hVU]
  have hm : X.presheaf.map (eqToHom he).op (X.presheaf.map (homOfLE hVU).op s) =
      X.presheaf.map (homOfLE (Set.image_preimage_subset V.ι U.1)).op s := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rw [← hm, mem_map_eq_iff J he]

/-- A generating family for an ideal subsheaf over an open restricts to one over a smaller
open. -/
lemma isGeneratedByOn_mono {X : Scheme.{u}}
    (J : (structureSheafModule X.toRingedSpace).Submodule)
    {U V : X.Opens} (hVU : V ≤ U) {r : ℕ} (s : Fin r → Γ(X, U))
    (h : IsGeneratedByOn X.toRingedSpace J U s) :
    IsGeneratedByOn X.toRingedSpace J V
      (fun i ↦ X.presheaf.map (homOfLE hVU).op (s i)) := by
  let K := generatedIdealOn X.toRingedSpace V (fun i ↦ X.presheaf.map (homOfLE hVU).op (s i))
  have hsmall : K ≤ generatedIdealOn X.toRingedSpace U s :=
    generatedIdealOn_le _ _ _ _ (fun i ↦
      (generatedIdealOn X.toRingedSpace U s).toSubmodule.map _
        (mem_generatedIdealOn _ _ s i))
  have hlarge : generatedIdealOn X.toRingedSpace U s ≤
      idealExtension V.ι (idealRestriction V.ι K) :=
    generatedIdealOn_le _ _ _ _ (fun i ↦
      (mem_extension_restriction_of_le K hVU (s i)).2 (mem_generatedIdealOn _ _ _ i))
  intro W hWV
  rw [h W (hWV.trans hVU)]
  apply le_antisymm
  · intro a ha
    exact (mem_idealRestriction_preimage V.ι K W (by simpa using hWV) a).1
      ((mem_idealExtension _ _ _ _).1 (hlarge (op W) ha))
  · exact hsmall (op W)

end Restriction

section QuasiRegular

/-- Quasi-regularity of a finite sequence is inherited by its image under a flat ring map. -/
private lemma isQuasiRegular_ofFn_map_of_flat {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) {r : ℕ} (s : Fin r → R)
    (h : RingTheory.Sequence.IsQuasiRegular R (List.ofFn s)) :
    RingTheory.Sequence.IsQuasiRegular S (List.ofFn fun i ↦ φ (s i)) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    Koszul.isQuasiRegular_map_of_flat φ hφ h

/-- Let `j : Z ⟶ X` be a closed immersion, `f : X ⟶ Y` an open immersion and suppose `j ≫ f` is
again a closed immersion. Then the defining ideal of `j ≫ f` on `Y` is quasi-regular if and only if
the defining ideal of `j` on `X` is. -/
@[ega "IV 16.9.2" "independence of U"]
private lemma isQuasiRegularIdealSheaf_comp_open_iff {Z X Y : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (f : X ⟶ Y) [IsOpenImmersion f] [IsClosedImmersion (j ≫ f)] :
    IsQuasiRegularIdealSheaf Y.toRingedSpace (definingIdealOfHom (j ≫ f)) ↔
      IsQuasiRegularIdealSheaf X.toRingedSpace (definingIdealOfHom j) := by
  rw [isQuasiRegularIdealSheaf_iff_exists_affine_generators,
    isQuasiRegularIdealSheaf_iff_exists_affine_generators]
  constructor
  · intro h x hx
    rw [definingIdealQuotient_support_eq_range] at hx
    obtain ⟨z, rfl⟩ := hx
    have hz : f (j z) ∈ idealQuotientSupport Y.toRingedSpace
        (definingIdealOfHom (j ≫ f)) := by
      rw [definingIdealQuotient_support_eq_range]
      exact ⟨z, rfl⟩
    obtain ⟨U, hxU, r, s, hgen, hs⟩ := h (f (j z)) hz
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (show j z ∈ f ⁻¹ᵁ U.1 from hxU)
    refine ⟨⟨V, hV⟩, hxV, r, (fun i ↦ f.appLE U.1 V hVU (s i)), ?_, ?_⟩
    · have hg := isGeneratedByOn_mono _ hVU _
        (isGeneratedByOn_restriction f _ U.1 s hgen)
      rwa [definingIdealOfHom_comp_open] at hg
    · exact isQuasiRegular_ofFn_map_of_flat (f.appLE U.1 V hVU).hom
        (f.flat_appLE U.2 hV hVU) s hs
  · intro h y hy
    rw [definingIdealQuotient_support_eq_range] at hy
    obtain ⟨z, rfl⟩ := hy
    have hz : j z ∈ idealQuotientSupport X.toRingedSpace (definingIdealOfHom j) := by
      rw [definingIdealQuotient_support_eq_range]
      exact ⟨z, rfl⟩
    obtain ⟨U, hxU, r, s, hgen, hs⟩ := h (j z) hz
    refine ⟨⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩,
      ⟨j z, hxU, rfl⟩, r, (fun i ↦ (f.appIso U.1).inv (s i)), ?_, ?_⟩
    · apply (isGeneratedByOn_image_iff f _ U.1 s).2
      rwa [definingIdealOfHom_comp_open]
    · exact isQuasiRegular_ofFn_map_of_flat (f.appIso U.1).inv.hom
        (RingHom.Flat.of_bijective
          (f.appIso U.1).commRingCatIsoToRingEquiv.symm.bijective) s hs

end QuasiRegular

section ArbitraryOpen

/-- An immersion `i : Z ⟶ X` is quasi-regular if and only if, for one — equivalently any — open
subscheme `U` of `X` through which `i` factors as a closed immersion `j : Z ⟶ U`, the defining
ideal of `j` is a quasi-regular ideal sheaf on `U`. -/
@[stacks 063J "part (4): independence of the chosen open"]
theorem isQuasiRegularImmersion_iff_of_open {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (j : Z ⟶ U.toScheme) [IsClosedImmersion j] (hij : j ≫ U.ι = i) :
    IsQuasiRegularImmersion i ↔
      IsQuasiRegularIdealSheaf U.toScheme.toLocallyRingedSpace.toRingedSpace
        (definingIdealOfHom j) := by
  let f : U.toScheme ⟶ i.coborderRange.toScheme :=
    Scheme.Hom.resLE (𝟙 X) i.coborderRange U (open_le_coborderRange i U j hij)
  have hfι : f ≫ i.coborderRange.ι = U.ι := by simp [f]
  have : IsOpenImmersion f := by
    have : IsOpenImmersion (f ≫ i.coborderRange.ι) := hfι ▸ inferInstance
    exact IsOpenImmersion.of_comp f i.coborderRange.ι
  have hf : j ≫ f = i.liftCoborder := closedFactor_eq_liftCoborder i U j hij
  have : IsClosedImmersion (j ≫ f) := hf ▸ inferInstance
  change IsQuasiRegularIdealSheaf _ (definingIdealOfHom i.liftCoborder) ↔ _
  rw [← hf]
  exact isQuasiRegularIdealSheaf_comp_open_iff j f

end ArbitraryOpen

section BaseChange

variable {Z X X' Z' : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] {p : X' ⟶ X} {i' : Z' ⟶ X'}
  {q : Z' ⟶ Z} (H : IsPullback i' q p i)

/-- If `i' : Z' ⟶ X'` is the base change of an immersion `i : Z ⟶ X` along `p : X' ⟶ X`, this
is the closed immersion of `Z'` into the open subscheme `p ⁻¹ᵁ i.coborderRange` of `X'` through
which `i'` factors. -/
def baseChangeLiftCoborder : Z' ⟶ (p ⁻¹ᵁ i.coborderRange).toScheme :=
  (isPullback_morphismRestrict p i.coborderRange).flip.lift i' (q ≫ i.liftCoborder)
    (by rw [Category.assoc, i.liftCoborder_ι, H.w])

/-- `baseChangeLiftCoborder H` followed by the inclusion of `p ⁻¹ᵁ i.coborderRange` is `i'`. -/
@[simp]
lemma baseChangeLiftCoborder_ι :
    baseChangeLiftCoborder H ≫ (p ⁻¹ᵁ i.coborderRange).ι = i' :=
  (isPullback_morphismRestrict p i.coborderRange).flip.lift_fst _ _ _

/-- The closed factor of a base-changed immersion is the base change of the closed factor. -/
lemma isPullback_baseChangeLiftCoborder :
    IsPullback (baseChangeLiftCoborder H) q (p ∣_ i.coborderRange) i.liftCoborder := by
  have H' : IsPullback i' q p (i.liftCoborder ≫ i.coborderRange.ι) := by
    rwa [i.liftCoborder_ι]
  exact IsPullback.of_right' H' (isPullback_morphismRestrict p i.coborderRange).flip

/-- `baseChangeLiftCoborder H` is a closed immersion. -/
instance isClosedImmersion_baseChangeLiftCoborder :
    IsClosedImmersion (baseChangeLiftCoborder H) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeLiftCoborder H).flip inferInstance

/-- The base change `i'` of an immersion `i` along `p` is quasi-regular exactly when the defining
ideal of `baseChangeLiftCoborder H` on `p ⁻¹ᵁ i.coborderRange` is quasi-regular. -/
theorem isQuasiRegularImmersion_baseChange_iff [IsImmersion i'] :
    IsQuasiRegularImmersion i' ↔
      IsQuasiRegularIdealSheaf
        (p ⁻¹ᵁ i.coborderRange).toScheme.toLocallyRingedSpace.toRingedSpace
        (definingIdealOfHom (baseChangeLiftCoborder H)) :=
  isQuasiRegularImmersion_iff_of_open i' (p ⁻¹ᵁ i.coborderRange)
    (baseChangeLiftCoborder H) (baseChangeLiftCoborder_ι H)

end BaseChange

end Stacks.AlgebraicGeometry

end
