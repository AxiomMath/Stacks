module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.LocalizationData

/-!
# Global sections as an extension from a punctured affine scheme

Let `I` be a finitely generated ideal of a commutative ring `R` and let `U = Spec R \ V(I)`.
A quasi-coherent module `F` on `U` is the restriction of the sheaf associated to its own
`R`-module of global sections `N = Γ(U, F)`, by an isomorphism under which the restriction map
`N ⟶ Γ(U, F)` of the low-degree exact sequence of Stacks 0DWR is the identity, and `N` has no
local cohomology with support in `V(I)` in degrees zero and one.

## Main results

* `Stacks.LocalCohomology.iso_restrict_tilde_globalSectionsModule` — a quasi-coherent module on
  `U` is the restriction of the sheaf associated to its module of global sections.
* `Stacks.LocalCohomology.isZero_localCohomology_zero_globalSectionsModule` and
  `Stacks.LocalCohomology.isZero_localCohomology_one_globalSectionsModule` — that module of
  global sections has vanishing local cohomology with support in `V(I)` in degrees zero and one.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology

/-- The inverse of `AlgebraicGeometry.Scheme.Modules.restrictAppIso` acts as the identity on
sections. -/
private theorem restrictAppIso_inv_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : X.Opens) (x : Γ(M, f ''ᵁ U)) :
    (Scheme.Modules.restrictAppIso f M U).inv x = x := rfl

variable (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)

/-- A quasi-coherent module `F` on `U = Spec R \ V(I)` is the restriction of the sheaf associated
to its module of global sections `N`, by an isomorphism under which the restriction map
`N ⟶ Γ(U, F)` of the localization triangle is the identity. -/
private theorem exists_globalSections_iso_restrictionToComplement_id
    (F : (complementZeroLocus R I : Scheme).Modules) [F.IsQuasicoherent]
    (D : LocalizationTriangleData.{u, u} R I hI) :
    ∃ e : F ≅ complementTilde R I (complementGlobalSections R I F),
      restrictionToComplement D (complementGlobalSections R I F) F e = LinearMap.id := by
  let U := complementZeroLocus R I
  let N := complementGlobalSections R I F
  let F' : SheafOfModules.{u} (complementZeroLocus R I : Scheme).ringCatSheaf := F
  have : QuasiCompact U.ι :=
    quasiCompact_iff_isSpectralMap.mpr
      (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp
        (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg hI))
  let G := (Scheme.Modules.pushforward U.ι).obj F'
  have hGiso : IsIso G.fromTildeΓ :=
    (AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ G).mp inferInstance
  let eT : (tilde.functor (CommRingCat.of R)).obj N ≅ G := @asIso _ _ _ _ G.fromTildeΓ hGiso
  let c := (Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app F'
  let e : F ≅ complementTilde R I N :=
    c.symm ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso eT.symm
  refine ⟨e, ?_⟩
  ext n
  rw [restrictionToComplement_apply (D := D) (M := N) (F := F) (e := e)]
  let s : (complementTilde R I N).val.obj (op ⊤) :=
    ⟨fun x ↦ LocalizedModule.mk n (1 : x.1.asIdeal.primeCompl),
      fun x ↦ ⟨_, x.2, 𝟙 _, n, 1,
        fun y ↦ ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩⟩
  change (e.inv.val.app (op ⊤)) s = n
  let GN := (AlgebraicGeometry.modulesSpecToSheaf
    (R := CommRingCat.of R)).obj G |>.presheaf.obj (op ⊤)
  let nG : GN := by
    change F'.val.obj (op ⊤)
    exact n
  have heval : (e.inv.val.app (op ⊤)) s =
      (c.hom.val.app (op ⊤))
        ((((Scheme.Modules.restrictFunctor U.ι).map G.fromTildeΓ).val.app (op ⊤)) s) := by
    change (ConcreteCategory.hom
        ((((Scheme.Modules.restrictFunctor U.ι).map G.fromTildeΓ).val.app (op ⊤)) ≫
          c.hom.val.app (op ⊤))) _ = _
    rfl
  have hnImage : (tilde.toOpen GN (U.ι ''ᵁ ⊤)) nG =
      s := by
    apply Subtype.ext
    funext x
    rfl
  have hinner :
      (((Scheme.Modules.restrictFunctor U.ι).map G.fromTildeΓ).val.app (op ⊤)) s =
        (Scheme.Modules.restrictAppIso U.ι G
          (⊤ : (complementZeroLocus R I : Scheme).Opens)).inv
          ((G.fromTildeΓ.val.app
            (op (U.ι ''ᵁ ⊤)))
            ((tilde.toOpen GN (U.ι ''ᵁ ⊤)) nG)) := by
    dsimp only [Scheme.Modules.restrictFunctor]
    change (G.fromTildeΓ.val.app (op (U.ι ''ᵁ ⊤))) s =
      (Scheme.Modules.restrictAppIso U.ι G
        (⊤ : (complementZeroLocus R I : Scheme).Opens)).inv
        ((G.fromTildeΓ.val.app (op (U.ι ''ᵁ ⊤)))
          ((tilde.toOpen GN (U.ι ''ᵁ ⊤)) nG))
    rw [hnImage]
    exact (restrictAppIso_inv_apply U.ι G (⊤ : (complementZeroLocus R I : Scheme).Opens)
      ((G.fromTildeΓ.val.app (op (U.ι ''ᵁ ⊤))) ((tilde.toOpen GN (U.ι ''ᵁ ⊤)) nG))).symm
  have hcalc := congrArg (fun f ↦ f nG)
    (Scheme.Modules.toOpen_fromTildeΓ_app G (complementZeroLocus R I))
  have hcinv : (c.inv.val.app (op ⊤)) n =
      (Scheme.Modules.restrictAppIso U.ι G
        (⊤ : (complementZeroLocus R I : Scheme).Opens)).inv
        (G.val.presheaf.map (homOfLE le_top).op nG) := by
    dsimp only [c, G, Scheme.Modules.restrictFunctorAdjCounitIso,
      Scheme.Modules.restrictAppIso, Scheme.Modules.restrictFunctor,
      Scheme.Modules.pushforward]
    rfl
  have hci : (c.hom.val.app (op ⊤)) ((c.inv.val.app (op ⊤)) n) = n := by
    have h := congrArg (fun f ↦ (f.val.app (op ⊤)) n) c.inv_hom_id
    change ((c.inv.val.app (op ⊤)) ≫ (c.hom.val.app (op ⊤))) n = n at h
    simpa only [ModuleCat.comp_apply] using h
  have hc : (c.hom.val.app (op ⊤))
      ((Scheme.Modules.restrictAppIso U.ι G
        (⊤ : (complementZeroLocus R I : Scheme).Opens)).inv
        (G.val.presheaf.map (homOfLE le_top).op nG)) = n := by
    rwa [← hcinv]
  have hcalcImage :
      (G.fromTildeΓ.val.app (op (U.ι ''ᵁ ⊤)))
        ((tilde.toOpen GN (U.ι ''ᵁ ⊤)) nG) =
        G.val.presheaf.map (homOfLE le_top).op nG := by
    rw [U.ι_image_top]
    change (ConcreteCategory.hom
        ((modulesSpecToSheaf.map G.fromTildeΓ).hom.app
          (op (complementZeroLocus R I))))
        ((ConcreteCategory.hom (tilde.toOpen GN
          (complementZeroLocus R I))) nG) =
      (ConcreteCategory.hom
        ((modulesSpecToSheaf.obj G).obj.map (homOfLE le_top).op)) nG
    exact hcalc
  rw [heval, hinner, hcalcImage]
  exact hc

include hI in
/-- A quasi-coherent module on the complement of `V(I)` is the restriction of the associated sheaf
of its global-sections `R`-module. -/
@[stacks 0DWR "global_sections_choice"]
theorem iso_restrict_tilde_globalSectionsModule
    (F : (complementZeroLocus R I : Scheme).Modules) [F.IsQuasicoherent] :
    Nonempty
      (F ≅ ((tilde.functor (CommRingCat.of R)).obj
        (complementGlobalSections R I F)).restrict
        (complementZeroLocus R I).ι) := by
  obtain ⟨D⟩ := nonempty_localizationTriangleData.{u, u} R I hI
  exact ⟨(exists_globalSections_iso_restrictionToComplement_id R I hI F D).choose⟩

/-- The degree-zero local cohomology of the global-sections module vanishes. -/
@[stacks 0DWR "global_sections_choice"]
theorem isZero_localCohomology_zero_globalSectionsModule
    (F : (complementZeroLocus R I : Scheme).Modules) [F.IsQuasicoherent] :
    IsZero (localCohomologyModule R I hI (complementGlobalSections R I F) 0) := by
  let N := complementGlobalSections R I F
  obtain ⟨D, hD⟩ := lowDegreeExactSequence.{u, u} R I hI
  obtain ⟨e, he⟩ := exists_globalSections_iso_restrictionToComplement_id R I hI F D
  have hseq := hD N F e
  let f := localCohomologyZeroToModule R I hI N
  have hrange : f.hom.range = ⊥ := by
    have hex := LinearMap.exact_iff.mp hseq.2.1
    rw [he] at hex
    simpa [f] using hex.symm
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ hseq.1 ?_⟩
  have hf : ∀ z, f.hom z = 0 := fun z ↦ by
    simpa [hrange] using LinearMap.mem_range_self f.hom z
  rw [hf, hf]

/-- The degree-one local cohomology of the global-sections module vanishes. -/
@[stacks 0DWR "global_sections_choice"]
theorem isZero_localCohomology_one_globalSectionsModule
    (F : (complementZeroLocus R I : Scheme).Modules) [F.IsQuasicoherent] :
    IsZero (localCohomologyModule R I hI (complementGlobalSections R I F) 1) := by
  let N := complementGlobalSections R I F
  obtain ⟨D, hD⟩ := lowDegreeExactSequence.{u, u} R I hI
  obtain ⟨e, he⟩ := exists_globalSections_iso_restrictionToComplement_id R I hI F D
  have hseq := hD N F e
  let g := localizationBoundary D N F e
  have hker : g.ker = ⊤ := by
    have hex := LinearMap.exact_iff.mp hseq.2.2.1
    rw [he] at hex
    exact hex.trans LinearMap.range_id
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hseq.2.2.2 x
  obtain ⟨b, rfl⟩ := hseq.2.2.2 y
  have hg : ∀ z, g z = 0 := fun z ↦ LinearMap.mem_ker.mp (by simp [hker])
  change g a = g b
  rw [hg, hg]

end Stacks.LocalCohomology

end
