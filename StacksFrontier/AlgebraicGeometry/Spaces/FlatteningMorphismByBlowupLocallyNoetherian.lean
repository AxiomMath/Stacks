module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningMorphismByBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremFiniteFactorization

/-!
# Flattening a morphism by blowing up, over a locally Noetherian base

Let `f : X ⟶ A` be a morphism of algebraic spaces of finite type and quasi-separated, with `A`
quasi-compact, quasi-separated and locally Noetherian, and let `U ⊆ A` be a quasi-compact open
subspace over which `f` is flat and locally of finite presentation. Then there is a
`U`-admissible blowup `A' ⟶ A` such that the strict transform of `X` is flat and of finite
presentation over `A'`: this is Stacks 087E over a locally Noetherian base.

## Main results

* `Space.exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransform_of_noetherian`:
  Stacks 087E over a quasi-compact, quasi-separated, locally Noetherian base.

## Implementation notes

The proof of Stacks 087E in
`StacksFrontier.AlgebraicGeometry.Spaces.FlatteningMorphismByBlowup` uses two results for an
arbitrary quasi-compact quasi-separated base: Stacks 0873 (an algebraic space separated and of
finite type over the base is a closed subspace of one of finite presentation) and Stacks 07VR (a
finite morphism is a limit of finite morphisms of finite presentation), the latter only to make
the finite morphism of Zariski's main theorem (Stacks 082K) one of finite presentation (Stacks
0874), on the way to Stacks 087B. Over a locally Noetherian base both are immediate, a morphism
of finite type and quasi-separated being of finite presentation (Stacks 06G4). This file
repeats the proofs of the steps of the chain, Stacks 0874, 087B, 087C and 087E, over a locally
Noetherian base, each with the same argument as the general step it repeats.

## References

* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 087C](https://stacks.math.columbia.edu/tag/087C)
* [Stacks Project, Tag 087B](https://stacks.math.columbia.edu/tag/087B)
* [Stacks Project, Tag 0874](https://stacks.math.columbia.edu/tag/0874)
* [Stacks Project, Tag 06G4](https://stacks.math.columbia.edu/tag/06G4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- **Stacks 0874 over a locally Noetherian base.** Let `f : X ⟶ Y` be a quasi-finite separated
morphism of algebraic spaces over `S` which is locally of finite presentation, with `Y`
quasi-compact, quasi-separated and locally Noetherian. Then `f = π ∘ j` with `j : X ⟶ T` a
quasi-compact open immersion and `π : T ⟶ Y` finite and of finite presentation.

Zariski's main theorem (Stacks 082K) gives the factorization with `π` finite; a finite morphism
is of finite type and separated, hence of finite presentation over the locally Noetherian `Y`
(Stacks 06G4). -/
theorem exists_isOpenImmersion_isFinitePresentation_of_isQuasiFinite_of_noetherian
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hN : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqf : IsQuasiFinite B S hS f) (hsep : IsSeparated B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (_hfp : IsLocallyOfFinitePresentation B S hS f) :
    ∃ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (j : X ⟶ T) (π : T ⟶ Y),
      IsAlgebraicSpace B S hS T ∧ IsOpenImmersion B S hS j ∧ IsQuasiCompact B S hS j ∧
        IsFinite B S hS π ∧ IsFinitePresentation B S hS π ∧ j ≫ π = f := by
  obtain ⟨T, j, π, hT, hj, hjqc, hπ, hfac⟩ :=
    exists_isOpenImmersion_isFinite_comp_eq_of_isQuasiFinite f hX hY hqf hsep hYqc hYqs
  refine ⟨T, j, π, hT, hj, hjqc, hπ, ?_, hfac⟩
  have hp := ((isFinite_iff_isAffineHom_and_isProper B S hS hT hY π).1 hπ).2
  exact isFinitePresentation_of_isFiniteType B S hS hT hY π hN hp.2.1
    (isQuasiSeparated_of_isSeparated B S hS hp.1)

/-- A closed subspace is of finite presentation exactly when its defining ideal is of finite
type. -/
private theorem isFinitePresentation_ι_iff_definingIdealSheaf
    {V : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS V.1) :
    IsFinitePresentation B S hS Z.1.ι ↔
      SheafOfModules.IsFiniteTypeOnSite (definingIdealSheaf B S hS V Z).toSheafOfModules :=
  isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf B S hS
    (ObjectProperty.homMk Z.1.ι : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ V) Z.2.2

/-- **The construction of Stacks 087B on the affine charts, over a locally Noetherian base.**
Let `X` be a quasi-compact, quasi-separated and locally Noetherian algebraic space, `φ : W ⟶ X`
a quasi-compact separated étale morphism, `U ⊆ X` a quasi-compact open subspace and `𝓘 ⊆ 𝒪_W`
a finite type quasi-coherent sheaf of ideals with `V(𝓘) ∩ φ⁻¹(U) = ∅`. Then there are finite
type quasi-coherent sheaves of ideals `𝓙 ⊆ 𝒪_X` with `V(𝓙) ∩ U = ∅` and `𝓘' ⊆ 𝒪_W` such that
over every affine étale chart `V` of `W` the sections of `𝓙` over `V ⟶ W ⟶ X` are the product
of the sections of `𝓘` and of `𝓘'` over `V`.

The proof is that of
`AlgebraicGeometry.Space.exists_isFiniteTypeQuasicoherentIdeal_chartSectionsIdeal_eq_mul`, whose
only use of Stacks 07VR is the factorization of `φ` through a finite morphism of finite
presentation (Stacks 0874); over a locally Noetherian base that factorization is
`Space.exists_isOpenImmersion_isFinitePresentation_of_isQuasiFinite_of_noetherian`. -/
theorem exists_isFiniteTypeQuasicoherentIdeal_chartSectionsIdeal_eq_mul_of_noetherian
    {X W : AlgebraicSpaces B S hS} (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (φ : W ⟶ X) (hφqc : IsQuasiCompact B S hS φ.hom) (hφsep : IsSeparated B S hS φ.hom)
    (hφet : IsEtale B S hS φ.hom)
    (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule)
    (hI : IsFiniteTypeQuasicoherentIdeal B S hS W I)
    (hIU : Disjoint (idealZeroLocus B S hS W I)
      (subspacePointSet B S hS W.1 (U.preimage φ.hom))) :
    ∃ J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule,
      IsFiniteTypeQuasicoherentIdeal B S hS X J ∧
        Disjoint (idealZeroLocus B S hS X J) (subspacePointSet B S hS X.1 U) ∧
        ∃ I' : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule,
          IsFiniteTypeQuasicoherentIdeal B S hS W I' ∧
            ∀ V : SmallEtale B S hS W.1,
              IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V) →
                chartSectionsIdeal B S hS W (etaleIdealRestrict B S hS φ hφet J) V =
                  chartSectionsIdeal B S hS W I V * chartSectionsIdeal B S hS W I' V := by
  classical
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  have hWqc : IsQuasiCompactSpace B S hS W.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS X.2 hXqc hφqc
  -- Stacks 0874: `φ = π ∘ j`, `j` a quasi-compact open immersion, `π` finite of finite
  -- presentation.
  obtain ⟨Y, j, π, hY, hj, hjqc, hπ, hπfp, hfac⟩ :=
    exists_isOpenImmersion_isFinitePresentation_of_isQuasiFinite_of_noetherian
        (hN := hN) φ.hom W.2 X.2
      ⟨isLocallyQuasiFinite_of_isEtale' B S hS hφet, hφqc⟩ hφsep hXqc hXqs
      (isLocallyOfFinitePresentation_of_isEtale B S hS hφet)
  have hYqc : IsQuasiCompactSpace B S hS Y :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS X.2 hXqc hπfp.2.1
  have hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hY hXqs hπfp.2.2
  -- The closed subspace `V(𝓘) ⊆ W`, of finite presentation by Stacks 084Q.
  obtain ⟨ZI, hZI⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS W I hI.1
  have hZIfp : IsFinitePresentation B S hS ZI.1.ι :=
    (isFinitePresentation_ι_iff_definingIdealSheaf ZI).2 (hZI ▸ hI.2)
  -- The open subspace `j(W) ⊆ Y`, isomorphic to `W`.
  set Vj : Subfunctor Y := openSubspaceOfPoints B S hS Y (Set.range (pointsMap B S hS W.1 j))
    with hVjdef
  have hVj : IsOpenSubspace B S hS Vj := isOpenSubspace_openSubspaceOfPoints B S hS hY _
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS j hj)
  have hVjr : Subfunctor.range j = Vj :=
    range_eq_openSubspaceOfPoints_of_isOpenImmersion_of_isAlgebraicSpace B S hS W.2 hj
  let jV : W.1 ⟶ Vj.toFunctor := Subfunctor.lift j (by rw [hVjr])
  have hjmono : Mono j := mono_of_isOpenImmersion B S hS j hj
  have hjV : IsIso jV := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro a
    rw [isIso_iff_bijective]
    refine ⟨fun x y hxy => ?_, fun w => ?_⟩
    · have hinj := (NatTrans.mono_iff_mono_app j).1 hjmono a
      rw [mono_iff_injective] at hinj
      exact hinj (congrArg Subtype.val hxy)
    · have hw : w.1 ∈ (Subfunctor.range j).obj a := by rw [hVjr]; exact w.2
      obtain ⟨x, hx⟩ := hw
      exact ⟨x, Subtype.ext hx⟩
  have hjVι : jV ≫ Vj.ι = j := Subfunctor.lift_ι _ _
  have hVjqc : IsQuasiCompactSpace B S hS Vj.toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (asIso jV) hWqc
  -- `V(𝓘)` transported to `j(W)`.
  set Z' : Subfunctor Vj.toFunctor := ZI.1.preimage (inv jV) with hZ'def
  have hZ'c : IsClosedSubspace B S hS Z' :=
    isClosedSubspace_preimage B S hS (inv jV) ZI.1 W.2 hVj.1 ZI.2
  have hZ'fp : IsFinitePresentation B S hS Z'.ι :=
    isFinitePresentation_of_isPullback B S hS hZ'c.1 ZI.2.1 hVj.1 W.2
      (Subfunctor.isPullback_preimage (inv jV) ZI.1) hZIfp
  -- The inverse image `π⁻¹(U)`, a quasi-compact open subspace of `Y`.
  set UY : Subfunctor Y := U.preimage π with hUYdef
  have hUY : IsOpenSubspace B S hS UY := isOpenSubspace_preimage B S hS π U X.2 hY hU
  have hUYqc : IsQuasiCompactSpace B S hS UY.toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (Subfunctor.isPullback_preimage π U).isoPullback.symm
      (hπfp.2.1 U.toFunctor hU.1 hUqc U.ι)
  -- `V(𝓘)` avoids `π⁻¹(U) ∩ j(W)`.
  have hWU : Disjoint (subspacePointSet B S hS Vj.toFunctor (UY.preimage Vj.ι))
      (subspacePointSet B S hS Vj.toFunctor Z') := by
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    change y ∈ Set.range (pointsMap B S hS _ (UY.preimage Vj.ι).ι) at hy₁
    change y ∈ Set.range (pointsMap B S hS _ Z'.ι) at hy₂
    rw [range_pointsMap_preimage_ι, Set.mem_preimage, hUYdef, range_pointsMap_preimage_ι,
      Set.mem_preimage] at hy₁
    rw [hZ'def, range_pointsMap_preimage_ι, Set.mem_preimage] at hy₂
    set w := pointsMap B S hS _ (inv jV) y
    have hyw : pointsMap B S hS _ jV w = y := by
      rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id]
      rfl
    refine Set.disjoint_left.1 hIU ?_
      (show w ∈ subspacePointSet B S hS W.1 (U.preimage φ.hom) from ?_)
    · rwa [hZI.symm, ← range_pointsMap_ι_eq_idealZeroLocus]
    · show w ∈ Set.range (pointsMap B S hS _ (U.preimage φ.hom).ι)
      rwa [range_pointsMap_preimage_ι, Set.mem_preimage, ← hfac, pointsMap_comp_apply, ← hjVι,
        pointsMap_comp_apply, hyw]
  -- Stacks 0853 in the form of finitely presented closed subspaces: `Z ⊆ Y`.
  obtain ⟨Z, hZc, hZfp, hZdisj, hZW⟩ := exists_closedSubspace_extension_disjoint hZ
    (X := ⟨Y, hY⟩) hYqc hYqs UY Vj hUY hVj hUYqc hVjqc Z' hZ'c hZ'fp hWU
  -- `τ : Z ⟶ X`, finite and of finite presentation, with image avoiding `U`.
  let Zsp : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZc.1⟩
  let τ : Zsp ⟶ X := ObjectProperty.homMk (Z.ι ≫ π)
  have hτ : IsFinite B S hS τ.hom :=
    isFinite_comp B S hS (isFinite_of_isClosedImmersion B S hS Z.ι hZc.2) hπ
  have hτfp : IsFinitePresentation B S hS τ.hom :=
    isFinitePresentation_comp B S hS hZc.1 hY X.2 Z.ι π hZfp hπfp
  have hτU : Disjoint (Set.range (pointsMap B S hS Zsp.1 τ.hom))
      (subspacePointSet B S hS X.1 U) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, rfl⟩ hzU
    refine Set.disjoint_left.1 hZdisj ?_ (⟨z, rfl⟩ : pointsMap B S hS _ Z.ι z ∈ Set.range _)
    show _ ∈ Set.range (pointsMap B S hS _ (U.preimage π).ι)
    rwa [range_pointsMap_preimage_ι, Set.mem_preimage, ← pointsMap_comp_apply]
  -- `𝓙 = Fit_0(τ_* 𝒪_Z)`.
  refine ⟨fittingIdeal B S hS X.1 X.2 (finiteDirectImageUnit τ hτ) 0,
    isFiniteTypeQuasicoherentIdeal_fittingIdeal X _
      (isQuasicoherentOnSite_smallBaseChangeModulePushforward B S hS τ hτ _
        (SheafOfModules.isQuasicoherentOnSite_unit _))
      (fun A hA => moduleFinitePresentation_sections_finiteDirectImageUnit τ hτ hτfp A hA) 0,
    disjoint_idealZeroLocus_fittingIdeal_zero τ hτ U hU hτU, ?_⟩
  -- The graph of `j` over `π` splits `W ×_X Z`.
  set T := graphPoints j π φ.hom hfac Z with hTdef
  have hP : IsAlgebraicSpace B S hS (pullback φ.hom τ.hom) := isAlgebraicSpace_pullback_hom φ τ
  have hT : IsClopen T :=
    (isClopen_range_pointsMap_graph B S hS W.2 hY X.2 j π (isEtale_of_isOpenImmersion B S hS hj)
      (by rw [hfac]; exact hφet) (isSeparated_of_isFinite B S hS π hY X.2 hπ)).preimage
      (continuous_pointsMap B S hS _)
  have sq := isPullback_graphPiece W.2 hY X.2 j π φ.hom hfac Z hj hφet
  -- The piece over the graph is `V(𝓘)`.
  have he₁ : IsClosedImmersion B S hS (fibrePieceHom φ τ T hT.isOpen).hom :=
    (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback sq hZc.2
  have hZpre : Z.preimage j = ZI.1 := by
    rw [← hjVι, Subfunctor.preimage_comp, hZW, hZ'def, ← Subfunctor.preimage_comp,
      IsIso.hom_inv_id, Subfunctor.preimage_id]
  have hjet : IsEtale B S hS j := isEtale_of_isOpenImmersion B S hS hj
  let jsp : W ⟶ (⟨Y, hY⟩ : AlgebraicSpaces B S hS) := ObjectProperty.homMk j
  have hsqA := isPullback_homMk B S hS hZc.1 W.2 hY
    (isOpenSubspace_openSubspaceOfPoints B S hS hP T hT.isOpen).1 sq
  have hker : kernelIdealSheaf B S hS (fibrePieceHom φ τ T hT.isOpen) = I := by
    rw [← hZI]
    have h₁ : kernelIdealSheaf B S hS (fibrePieceHom φ τ T hT.isOpen) =
        etaleRestrictionDefiningIdealSheaf B S hS jsp hjet ⟨Z, hZc⟩ := by
      refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun V => ?_)
      obtain ⟨V⟩ := V
      exact kernelIdealSheaf_baseChange_obj B S hS _ _ _ _ hsqA hjet V
    rw [h₁, etaleRestrictionDefiningIdealSheaf_eq]
    congr 1
    exact Subtype.ext hZpre
  -- The complementary piece is finite and of finite presentation over `W`.
  have hG₂c : IsClosedSubspace B S hS (openSubspaceOfPoints B S hS _ Tᶜ) :=
    isClosedSubspace_openSubspaceOfPoints B S hS hP Tᶜ hT.isClosed.isOpen_compl
      hT.isOpen.isClosed_compl
  have hG₂o := isOpenSubspace_openSubspaceOfPoints B S hS hP Tᶜ hT.isClosed.isOpen_compl
  have hfst : IsFinite B S hS (pullback.fst φ.hom τ.hom) :=
    isFinite_of_isPullback B S hS (IsPullback.of_hasPullback φ.hom τ.hom).flip hτ
  have hfstfp : IsFinitePresentation B S hS (pullback.fst φ.hom τ.hom) :=
    isFinitePresentation_of_isPullback B S hS hP Zsp.2 W.2 X.2
      (IsPullback.of_hasPullback φ.hom τ.hom).flip hτfp
  have he₂ : IsFinite B S hS (fibrePieceHom φ τ Tᶜ hT.isClosed.isOpen_compl).hom :=
    isFinite_comp B S hS (isFinite_of_isClosedImmersion B S hS _ hG₂c.2) hfst
  have he₂fp : IsFinitePresentation B S hS (fibrePieceHom φ τ Tᶜ hT.isClosed.isOpen_compl).hom :=
    isFinitePresentation_comp B S hS hG₂c.1 hP W.2 _ _
      ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS hG₂o.2,
        isQuasiCompact_of_isClosedImmersion' B S hS hG₂c.2,
        isQuasiSeparated_of_mono B S hS _ inferInstance⟩ hfstfp
  -- The computation of the inverse-image ideal on the affine charts of `W`.
  refine ⟨_, isFiniteTypeQuasicoherentIdeal_fittingIdeal W _
    (isQuasicoherentOnSite_smallBaseChangeModulePushforward B S hS _ he₂ _
      (SheafOfModules.isQuasicoherentOnSite_unit _))
    (fun A hA => moduleFinitePresentation_sections_finiteDirectImageUnit _ he₂ he₂fp A hA) 0,
    fun V hV => ?_⟩
  have h := chartSectionsIdeal_etaleIdealRestrict_fittingIdeal_eq_mul φ hφet τ hτ T hT he₁ he₂ V hV
  rwa [hker] at h

/-- **Stacks 087B for closed subspaces, over a locally Noetherian base.** Let `X` be a
quasi-compact, quasi-separated and locally Noetherian algebraic space, `φ : W ⟶ X` a
quasi-compact separated étale morphism, `U ⊆ X` a quasi-compact open subspace and `Z_W ⊆ W` a
closed subspace of finite presentation disjoint from `φ⁻¹(U)`. Then there are a closed subspace
`Z_X ⊆ X` of finite presentation disjoint from `U` and a closed subspace `Z' ⊆ W` of finite
presentation with `φ⁻¹(Z_X) = Z_W + Z'`.

The proof is that of
`AlgebraicGeometry.Space.exists_isFinitePresentation_preimageClosedSubspace_eq_sumClosedSubspaces`,
with the construction on the affine charts taken over the locally Noetherian base. -/
theorem exists_isFinitePresentation_preimageClosedSubspace_eq_sum_of_noetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) {X W : AlgebraicSpaces B S hS} (φ : W ⟶ X)
    (U : OpenSubspaces B S hS X.1) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hφqc : IsQuasiCompact B S hS φ.hom) (hφsep : IsSeparated B S hS φ.hom)
    (hφet : IsEtale B S hS φ.hom) (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (ZW : ClosedSubspaces B S hS W.1) (hZWfp : IsFinitePresentation B S hS ZW.1.ι)
    (hZWU : Disjoint (subspacePointSet B S hS W.1 (U.1.preimage φ.hom))
      (subspacePointSet B S hS W.1 ZW.1)) :
    ∃ ZX : ClosedSubspaces B S hS X.1, IsFinitePresentation B S hS ZX.1.ι ∧
      Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 ZX.1) ∧
      ∃ Z' : ClosedSubspaces B S hS W.1, IsFinitePresentation B S hS Z'.1.ι ∧
        preimageClosedSubspace φ ZX = sumClosedSubspaces B S hS W ZW Z' := by
  have hI : IsFiniteTypeQuasicoherentIdeal B S hS W (definingIdealSheaf B S hS W ZW) :=
    ⟨isQuasicoherentOnSite_definingIdealSheaf B S hS W ZW,
      (isFinitePresentation_ι_iff_definingIdealSheaf ZW).1 hZWfp⟩
  have hIU : Disjoint (idealZeroLocus B S hS W (definingIdealSheaf B S hS W ZW))
      (subspacePointSet B S hS W.1 (U.1.preimage φ.hom)) := by
    rw [← range_pointsMap_ι_eq_idealZeroLocus]
    exact hZWU.symm
  obtain ⟨J, hJ, hJU, I', hI', hchart⟩ :=
    exists_isFiniteTypeQuasicoherentIdeal_chartSectionsIdeal_eq_mul_of_noetherian
        (hN := hN) hXqc hXqs φ hφqc
      hφsep hφet U.1 U.2 hUqc _ hI hIU
  obtain ⟨ZX, hZX⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X J hJ.1
  obtain ⟨Z', hZ'⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS W I' hI'.1
  refine ⟨ZX, (isFinitePresentation_ι_iff_definingIdealSheaf ZX).2 (hZX ▸ hJ.2), ?_, Z',
    (isFinitePresentation_ι_iff_definingIdealSheaf Z').2 (hZ' ▸ hI'.2), ?_⟩
  · rw [show subspacePointSet B S hS X.1 ZX.1 = idealZeroLocus B S hS X J from
      (range_pointsMap_ι_eq_idealZeroLocus B S hS X ZX).trans (by rw [hZX])]
    exact hJU.symm
  · refine definingIdealSheaf_injective B S hS W ?_
    refine structureSubmodule_ext_of_forall_isAffine_hom B S hS W
      ⟨CostructuredArrow.mk (atlasHom B S hS W), atlasHom_etale B S hS W⟩
      ((presheafSurjective_iff_isSurjective_yoneda B S hS W.1 W.2 _ _).1
        (atlasHom_surjective B S hS W)) _ _ fun A hA m => ?_
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
    have h₁ : definingIdealAt B S hS W (preimageClosedSubspace φ ZX) (op A) =
        chartSectionsIdeal B S hS W (etaleIdealRestrict B S hS φ hφet J) A := by
      refine (definingIdealAt_preimage_eq_definingIdealAt_postcomp B S hS φ hφet ZX A).trans ?_
      rw [← definingIdealSheaf_obj, hZX]
      rfl
    show definingIdealAt B S hS W (preimageClosedSubspace φ ZX) (op A) =
      definingIdealAt B S hS W (sumClosedSubspaces B S hS W ZW Z') (op A)
    rw [definingIdealAt_sumClosedSubspaces_of_isAffine B S hS W ZW Z' A m, h₁, hchart A hA, ← hZ']
    rfl

/-- **Stacks 087C for a representable source, over a locally Noetherian base.** Let `A` be a
quasi-compact, quasi-separated and locally Noetherian algebraic space, `U ⊆ A` a quasi-compact
open subspace, `f : X ⟶ A` locally of finite presentation with `X` a quasi-compact representable
algebraic space and `F` a quasi-coherent `𝒪_X`-module of finite type whose restriction over `U`
is of finite presentation and flat over `U`. Given the case of an affine base (`hscheme`), there
is a `U`-admissible blowup of `A` flattening `F`.

The proof is that of `AlgebraicGeometry.Space.exists_isFlatteningBlowup_of_isRepresentableSpace`,
with Stacks 087B taken over the locally Noetherian base. -/
theorem exists_isFlatteningBlowup_of_isRepresentableSpace_of_noetherian
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {A : AlgebraicSpaces B S hS} (hAqc : IsQuasiCompactSpace B S hS A.1)
    (hN : HasEtaleLocalProperty B S hS A.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1) (U : OpenSubspaces B S hS A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hscheme : ∀ (A X : AlgebraicSpaces B S hS),
      IsAffineSpace B S hS A.1 → IsRepresentableSpace B S hS X →
      ∀ (f : X ⟶ A), IsQuasiCompactSpace B S hS X.1 →
        IsLocallyOfFinitePresentation B S hS f.hom →
      ∀ (F : Modules.{u, u} B S hS X.1 X.2), F.IsQuasicoherentOnSite → F.IsFiniteTypeOnSite →
      ∀ (U : OpenSubspaces B S hS A.1), IsQuasiCompactSpace B S hS U.1.toFunctor →
        ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite →
        IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
          ((modulePullback B S hS (restrictOverι f U)).obj F) →
      ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
        IsFlatteningBlowup f F U Z b)
    {X : AlgebraicSpaces B S hS} (hXrep : IsRepresentableSpace B S hS X) (f : X ⟶ A)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFqc : F.IsQuasicoherentOnSite)
    (hFft : F.IsFiniteTypeOnSite)
    (hFUfp : ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite)
    (hFUflat : IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
      ((modulePullback B S hS (restrictOverι f U)).obj F)) :
    ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
      IsFlatteningBlowup f F U Z b := by
  obtain ⟨W₀, φ₀, hW₀, hφs, hφe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS A.1 A.2).1 hAqc
  let W : AlgebraicSpaces B S hS := ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩
  let φ : W ⟶ A := ObjectProperty.homMk φ₀
  have hWqc : IsQuasiCompactSpace B S hS W.1 := isQuasiCompactSpace_yoneda_of_isAffine B S hS W₀ hW₀
  have hφsurj : IsSurjective B S hS φ.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS A.1 A.2 W₀ φ₀).1 hφs
  have hφsep : IsSeparated B S hS φ.hom :=
    have := hW₀
    isSeparated_of_isEtale_of_scheme_isSeparated B S hS A.1 A.2 W₀ inferInstance φ₀ hφe
  have hφqc : IsQuasiCompact B S hS φ.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ A.2 hAqs hWqc φ.hom
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    flatteningHypotheses_baseChange f φ U hZ hAqs hWqc hφe hXqc hf F hFqc hFft hUqc hFUfp hFUflat
  obtain ⟨ZW, W₁, c, hZWfp, hUZW, hc, hG₁fp, hG₁flat⟩ := hscheme W _ ⟨W₀, hW₀, ⟨Iso.refl _⟩⟩
    (isRepresentableSpace_fiberProduct f φ hXrep ⟨W₀, ⟨Iso.refl _⟩⟩) (baseChangeHom f φ) h1 h2
    _ h3 h4 (U.pullback φ) h5 h6 h7
  obtain ⟨Z, hZfp, hUZ, Z', hZ'fp, hsum⟩ :=
    exists_isFinitePresentation_preimageClosedSubspace_eq_sum_of_noetherian (hN := hN) hZ φ U hAqc
      hAqs hφqc hφsep hφe hUqc ZW hZWfp hUZW
  obtain ⟨W₂, c₂, hY, hNfp, hNflat⟩ :=
    exists_isBlowupAlong_sum_isFinitePresentation_isFlatOver (baseChangeHom f φ) _ Z' hZ'fp hc
      hG₁fp hG₁flat
  obtain ⟨A', b, hb⟩ := exists_isBlowupAlong Z
  have hφflat : IsFlat B S hS φ.hom := isFlat_of_isEtale B S hS hφe
  have h85S := isBlowupAlong_pullbackFst_of_isFlat hφflat hb
  rw [hsum] at h85S
  obtain ⟨ε, hε⟩ := hY.exists_iso h85S
  have hsq : IsPullback (c₂ ≫ c) (ε.hom ≫ pullback.snd φ b) φ b :=
    (IsPullback.of_hasPullback φ b).of_iso ε.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [← hε]) (by simp) (by simp) (by simp)
  have hE : (sumClosedSubspaces B S hS W ZW Z').1.preimage (c₂ ≫ c).hom =
      (Z.1.preimage b.hom).preimage (ε.hom ≫ pullback.snd φ b).hom := by
    have h1 : (sumClosedSubspaces B S hS W ZW Z').1 = Z.1.preimage φ.hom := by
      rw [← hsum]; rfl
    rw [h1, ← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp]
    exact congrArg (fun k => Z.1.preimage k) (congrArg InducedCategory.Hom.hom hsq.w)
  rw [hE] at hNfp hNflat
  exact ⟨Z, A', b, isFlatteningBlowup_of_baseChange hφe hφsurj hsq hZfp hUZ hb hNfp hNflat⟩

/-- **Stacks 087C from the case of an affine base, over a locally Noetherian base.** Let `A`
be a quasi-compact, quasi-separated and locally Noetherian algebraic space, `U ⊆ A` a
quasi-compact open subspace, `f : X ⟶ A` locally of finite presentation with `X` quasi-compact
and `F` a quasi-coherent `𝒪_X`-module of finite type whose restriction over `U` is of finite
presentation and flat over `U`. Given the case of an affine base (`hscheme`), there is a
`U`-admissible blowup of `A` flattening `F`. The proof is that of
`AlgebraicGeometry.Space.exists_isFlatteningBlowup_of_schemeCase`. -/
theorem exists_isFlatteningBlowup_of_schemeCase_of_noetherian (hZ : B.Contains (⊤_ Scheme.{u}))
    {A : AlgebraicSpaces B S hS} (hAqc : IsQuasiCompactSpace B S hS A.1)
    (hN : HasEtaleLocalProperty B S hS A.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1) (U : OpenSubspaces B S hS A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hscheme : ∀ (A X : AlgebraicSpaces B S hS),
      IsAffineSpace B S hS A.1 → IsRepresentableSpace B S hS X →
      ∀ (f : X ⟶ A), IsQuasiCompactSpace B S hS X.1 →
        IsLocallyOfFinitePresentation B S hS f.hom →
      ∀ (F : Modules.{u, u} B S hS X.1 X.2), F.IsQuasicoherentOnSite → F.IsFiniteTypeOnSite →
      ∀ (U : OpenSubspaces B S hS A.1), IsQuasiCompactSpace B S hS U.1.toFunctor →
        ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite →
        IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
          ((modulePullback B S hS (restrictOverι f U)).obj F) →
      ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
        IsFlatteningBlowup f F U Z b)
    {X : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFqc : F.IsQuasicoherentOnSite)
    (hFft : F.IsFiniteTypeOnSite)
    (hFUfp : ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite)
    (hFUflat : IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
      ((modulePullback B S hS (restrictOverι f U)).obj F)) :
    ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
      IsFlatteningBlowup f F U Z b :=
  exists_isFlatteningBlowup_of_isRepresentableSpace_source U
    (fun _ f' G hrep hqc hlfp hGqc hGft hGfp hGflat =>
      exists_isFlatteningBlowup_of_isRepresentableSpace_of_noetherian
          (hN := hN) hZ hAqc hAqs U hUqc hscheme
        hrep f' hqc hlfp G hGqc hGft hGfp hGflat)
    f hXqc hf F hFqc hFft hFUfp hFUflat

/-- **Stacks 087C, flattening by blowing up, over a locally Noetherian base.** Let `A` be a
quasi-compact, quasi-separated and locally Noetherian algebraic space, let `f : X ⟶ A` be locally
of finite presentation with `X` quasi-compact, let `F` be a quasi-coherent `𝒪_X`-module of
finite type and let `U ⊆ A` be a quasi-compact open subspace such that `F_U` is of finite
presentation and flat over `U`. Then there is a blowup `b : A' ⟶ A` in a finitely presented
closed subspace `Z` disjoint from `U` such that the strict transform of `F` is of finite
presentation and flat over `A'`. The proof is that of
`AlgebraicGeometry.Space.exists_isFlatteningBlowup`, the affine case being Stacks 0815. -/
theorem exists_isFlatteningBlowup_of_noetherian (hZ : B.Contains (⊤_ Scheme.{u}))
    {A : AlgebraicSpaces B S hS} (hAqc : IsQuasiCompactSpace B S hS A.1)
    (hN : HasEtaleLocalProperty B S hS A.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1) (U : OpenSubspaces B S hS A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    {X : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFqc : F.IsQuasicoherentOnSite)
    (hFft : F.IsFiniteTypeOnSite)
    (hFUfp : ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite)
    (hFUflat : IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
      ((modulePullback B S hS (restrictOverι f U)).obj F)) :
    ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
      IsFlatteningBlowup f F U Z b :=
  exists_isFlatteningBlowup_of_schemeCase_of_noetherian (hN := hN) hZ hAqc hAqs U hUqc
    (fun _ _ hA _ f' hqc hlfp G hGqc hGft U' hU'qc hGfp hGflat =>
      exists_isFlatteningBlowup_of_isAffineSpace hA f' hqc hlfp G hGqc hGft U' hU'qc hGfp hGflat)
    f hXqc hf F hFqc hFft hFUfp hFUflat

/-- **Stacks 087E for a closed subspace of a space of finite presentation over the base, over
a locally Noetherian base.** Let `A` be a quasi-compact, quasi-separated and locally Noetherian
algebraic space, `U ⊆ A` a quasi-compact open subspace, `g : Y ⟶ A` of finite presentation and
`W ⊆ Y` a closed subspace such that `W_U ⟶ U` is flat and locally of finite presentation. Then
there is a `U`-admissible blowup `b : A' ⟶ A`, with centre `Z`, such that the strict transform
of `W` is flat and locally of finite presentation over `A'`. The proof is that of
`Space.exists_isBlowupAlong_isFlat_strictTransformSpaceToBlowUp_of_closedSubspace`.
-/
theorem exists_isBlowupAlong_isFlat_strictTransform_of_closedSubspace_of_noetherian
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {A Y : AlgebraicSpaces B S hS} (g : Y ⟶ A) (hg : IsFinitePresentation B S hS g.hom)
    (hN : HasEtaleLocalProperty B S hS A.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hAqc : IsQuasiCompactSpace B S hS A.1) (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1)
    (U : OpenSubspaces B S hS A.1) (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (W : ClosedSubspaces B S hS Y.1)
    (hWflat : IsFlat B S hS
      ((preimageClosedSubspace (restrictOverι g U) W).1.ι ≫ (restrictOverHom g U).hom))
    (hWlfp : IsLocallyOfFinitePresentation B S hS
      ((preimageClosedSubspace (restrictOverι g U) W).1.ι ≫ (restrictOverHom g U).hom)) :
    ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1),
      IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
          IsBlowupAlong B S hS Z b ∧
            IsFlat B S hS (strictTransformSpaceToBlowUp B S hS
              (subspaceInclusion B S hS Y W ≫ g) b (Z.1.preimage b.hom)).hom ∧
              IsLocallyOfFinitePresentation B S hS (strictTransformSpaceToBlowUp B S hS
                (subspaceInclusion B S hS Y W ≫ g) b (Z.1.preimage b.hom)).hom := by
  have hYqc : IsQuasiCompactSpace B S hS Y.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS A.2 hAqc hg.2.1
  -- the module `F = i_*𝒪_W` on `Y`
  have hFqc : (pushforwardStructureSheaf B S hS Y W).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_pushforwardStructureSheaf B S hS Y W
  have hFft : (pushforwardStructureSheaf B S hS Y W).IsFiniteTypeOnSite :=
    @isFiniteTypeOnSite_of_epi B S hS Y.1 Y.2 _ _ (structureProjection B S hS Y W)
      (epi_structureProjection B S hS Y W) (isFiniteTypeOnSite_unit_structureRingSheaf B S hS Y)
  -- its restriction over `U` is `i_*𝒪_{W_U}`, of finite presentation and flat over `U`
  obtain ⟨eU⟩ := nonempty_modulePullback_restrictOverι_pushforwardStructureSheaf_iso g U W
  set WU := preimageClosedSubspace (restrictOverι g U) W with hWU
  have hsnd : IsLocallyOfFinitePresentation B S hS (restrictOverHom g U).hom :=
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS g U.toSpaceι) hg.1
  have hincl : IsLocallyOfFinitePresentation B S hS WU.1.ι :=
    isLocallyOfFinitePresentation_of_comp B S hS WU.2.1 (restrictOver g U).2 U.2.1 _ _ hWlfp
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hsnd)
  have hker := (isFinitePresentation_ι_iff_definingIdealSheaf WU).1
    ((isFinitePresentation_iff_isLocallyOfFinitePresentation B S hS
      (subspaceInclusion B S hS (restrictOver g U) WU) WU.2.2).2 hincl)
  have hFUfp : ((modulePullback B S hS (restrictOverι g U)).obj
      (pushforwardStructureSheaf B S hS Y W)).IsFinitePresentationOnSite :=
    SheafOfModules.IsFinitePresentationOnSite.of_iso eU.symm
      (isFinitePresentationOnSite_pushforwardStructureSheaf B S hS _ WU hker)
  have hFUflat : IsFlatOver B S hS (restrictOver g U).2 (restrictOverHom g U).hom
      ((modulePullback B S hS (restrictOverι g U)).obj
        (pushforwardStructureSheaf B S hS Y W)) :=
    IsFlatOver.of_iso B S hS _ eU.symm
      (isFlatOver_pushforwardStructureSheaf_of_isFlat B S hS WU (restrictOverHom g U) hWflat)
  -- flattening by blowing up, Stacks 087C
  obtain ⟨Z, A', b, hZfp, hUZ, hb, hFfp, hFflat⟩ :=
    exists_isFlatteningBlowup_of_noetherian (hN := hN) hZ hAqc hAqs U hUqc g hYqc hg.1
      (pushforwardStructureSheaf B S hS Y W) hFqc hFft hFUfp hFUflat
  -- the strict transform of `i_*𝒪_W` is `k_*𝒪_{W'}`, by Stacks 0866
  obtain ⟨-, e, -⟩ := exists_modulePushforward_strictTransformSheaf_iso_unconditional B S hS
    (subspaceInclusion B S hS Y W) g b Z
    (SheafOfModules.unit (structureRingSheaf B S hS ⟨W.1.toFunctor, W.2.1⟩))
    (SheafOfModules.isQuasicoherentOnSite_unit _) hb
    (isAffineHom_of_isClosedImmersion B S hS _ W.2.2)
  obtain ⟨e₀⟩ := nonempty_strictTransformSheaf_unit_iso (subspaceInclusion B S hS Y W ≫ g) b hb
  set i' := strictTransformPullbackMap B S hS (subspaceInclusion B S hS Y W) g b with hi'
  set W' := strictTransform B S hS (subspaceInclusion B S hS Y W ≫ g) b (Z.1.preimage b.hom)
    with hW'
  have hk : IsClosedImmersion B S hS
      (subspaceInclusion B S hS (strictTransformPullback B S hS
        (subspaceInclusion B S hS Y W ≫ g) b) W' ≫ i').hom :=
    isClosedImmersion_comp B S hS _ _ W'.2.2
      (isClosedImmersion_of_isPullback B S hS
        (isPullback_strictTransformPullbackMap B S hS (subspaceInclusion B S hS Y W) g b) W.2.2)
  let eM : structureSheafPushforward B S hS
        (subspaceInclusion B S hS (strictTransformPullback B S hS
          (subspaceInclusion B S hS Y W ≫ g) b) W' ≫ i') ≅
      strictTransformSheaf B S hS g b (Z.1.preimage b.hom)
        (pushforwardStructureSheaf B S hS Y W) :=
    ((modulePushforwardCompIso B S hS _ i').app _).symm ≪≫
      (modulePushforward B S hS i').mapIso e₀.symm ≪≫ e
  have hkfp := isFinitePresentation_of_isFinitePresentationOnSite_structureSheafPushforward B S hS
    _ hk (SheafOfModules.IsFinitePresentationOnSite.of_iso eM.symm hFfp)
  have hkflat := isFlat_comp_of_isFlatOver_structureSheafPushforward B S hS _ hk
    (strictTransformPullbackToBlowUp B S hS g b) (IsFlatOver.of_iso B S hS _ eM.symm hFflat)
  have hp : IsLocallyOfFinitePresentation B S hS (strictTransformPullbackToBlowUp B S hS g b).hom :=
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS g b) hg.1
  have hkeq : (subspaceInclusion B S hS (strictTransformPullback B S hS
        (subspaceInclusion B S hS Y W ≫ g) b) W' ≫ i') ≫
          strictTransformPullbackToBlowUp B S hS g b =
      strictTransformSpaceToBlowUp B S hS (subspaceInclusion B S hS Y W ≫ g) b
        (Z.1.preimage b.hom) := by
    rw [Category.assoc, hi', strictTransformPullbackMap_toBlowUp]
  refine ⟨A', b, Z, hZfp, hUZ, hb, ?_, ?_⟩
  · rwa [← hkeq]
  · rw [← hkeq]
    exact isLocallyOfFinitePresentation_comp B S hS W'.2.1 (strictTransformPullback B S hS g b).2
      A'.2 _ _ hkfp.1 hp

/-- **Stacks 087E, flattening a morphism by blowing up, over a locally Noetherian base.** Let
`f : X ⟶ A` be a morphism of algebraic spaces over `S` and `U ⊆ A` an open subspace. Assume that
`A` is quasi-compact, quasi-separated and locally Noetherian, that `U` is quasi-compact, that `f`
is of finite type and quasi-separated, and that `f⁻¹(U) ⟶ U` is flat and locally of finite
presentation. Then there is a `U`-admissible blowup `b : A' ⟶ A`, with centre `Z`, such that the
strict transform of `X` is flat and of finite presentation over `A'`.

The proof is that of
`Space.exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp`.
There, Stacks 0873 embeds an affine étale chart `V` of `X`, separated and of finite type over
`A`, into an algebraic space separated and of finite presentation over `A`; over a locally
Noetherian `A` the chart itself is of finite presentation over `A` (Stacks 06G4), so the
embedding is the identity of `V`. -/
theorem exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransform_of_noetherian
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {A X : AlgebraicSpaces B S hS} (f : X ⟶ A) (U : OpenSubspaces B S hS A.1)
    (hN : HasEtaleLocalProperty B S hS A.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hAqc : IsQuasiCompactSpace B S hS A.1) (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hft : IsFiniteType B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    (hflat : IsFlat B S hS (pullback.snd f.hom U.1.ι))
    (hlfp : IsLocallyOfFinitePresentation B S hS (pullback.snd f.hom U.1.ι)) :
    ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1),
      IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
          IsBlowupAlong B S hS Z b ∧
            IsFlat B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom ∧
              IsFinitePresentation B S hS
                (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom := by
  -- an affine scheme `V` with a surjective étale `a : V ⟶ X`
  have hXqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS A.2 hAqc hft.2
  obtain ⟨V₀, a, hV₀, has, hae⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hXqc
  have hVqc : IsQuasiCompactSpace B S hS (yoneda.obj V₀) :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS V₀ hV₀
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V₀) := isAlgebraicSpace_yoneda B S hS V₀
  -- `V ⟶ A` is separated and of finite type
  have hsep : IsSeparated B S hS (a ≫ f.hom) := by
    have := hV₀
    exact isSeparated_of_scheme_isSeparated B S hS inferInstance _
  have hvft : IsFiniteType B S hS (a ≫ f.hom) :=
    ⟨isLocallyOfFiniteType_comp B S hS hV X.2 A.2 a f.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
          (isLocallyOfFinitePresentation_of_isEtale B S hS hae)) hft.1,
      isQuasiCompact_of_isQuasiCompactSpace B S hS hZ A.2 hAqs hVqc _⟩
  -- Stacks 0873: a closed immersion `i : V ⟶ Y` with `Y ⟶ A` separated of finite presentation
  obtain ⟨Y₀, g₀, i, hY₀, -, hgfp, hi, hig⟩ : ∃ (Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (g₀ : Y₀ ⟶ A.1) (i : yoneda.obj V₀ ⟶ Y₀), IsAlgebraicSpace B S hS Y₀ ∧
        IsSeparated B S hS g₀ ∧ IsFinitePresentation B S hS g₀ ∧ IsClosedImmersion B S hS i ∧
          i ≫ g₀ = a ≫ f.hom :=
    ⟨yoneda.obj V₀, a ≫ f.hom, 𝟙 _, hV, hsep,
      isFinitePresentation_of_isFiniteType B S hS hV A.2 _ hN hvft
        (isQuasiSeparated_of_isSeparated B S hS hsep),
      isClosedImmersion_of_isIso B S hS _, Category.id_comp _⟩
  let Y : AlgebraicSpaces B S hS := ⟨Y₀, hY₀⟩
  let g : Y ⟶ A := ObjectProperty.homMk g₀
  -- the image `W ⊆ Y` of `i`, isomorphic to `V`
  let W : ClosedSubspaces B S hS Y₀ :=
    ⟨Subfunctor.range i, isClosedSubspace_range_of_isClosedImmersion B S hS i hV hi⟩
  have : Mono i := mono_of_isClosedImmersion B S hS i hi
  let e : yoneda.obj V₀ ≅ W.1.toFunctor := asIso (Subfunctor.toRange i)
  have he : e.inv ≫ i = W.1.ι := by
    rw [Iso.inv_comp_eq]
    exact (Subfunctor.toRange_ι i).symm
  let u : (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X :=
    ObjectProperty.homMk (e.inv ≫ a)
  have hue : IsEtale B S hS u.hom := isEtale_comp B S hS (isEtale_of_isIso B S hS e.inv) hae
  have hus : IsSurjective B S hS u.hom :=
    isSurjective_comp B S hS (isSurjective_of_isIso B S hS e.inv)
      ((presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 V₀ a).1 has)
  have hcomm : u ≫ f = subspaceInclusion B S hS Y W ≫ g := by
    refine ObjectProperty.hom_ext _ ?_
    show (e.inv ≫ a) ≫ f.hom = W.1.ι ≫ g₀
    rw [Category.assoc, ← hig, ← Category.assoc, he]
  -- `W_U ⟶ U` is flat and locally of finite presentation: it is étale over `X_U ⟶ U`
  have hWU := (preimageClosedSubspace (restrictOverι g U) W).2.1
  have hsqg := AlgebraicSpaces.isPullback_hom B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS g U.toSpaceι)
  have hfst : (W.1.preimage (restrictOverι g U).hom).ι ≫ (restrictOverι g U).hom =
      W.1.fromPreimage (restrictOverι g U).hom ≫ W.1.ι :=
    (Subfunctor.fromPreimage_ι W.1 (restrictOverι g U).hom).symm
  have hu : u.hom ≫ f.hom = W.1.ι ≫ g.hom := congrArg (fun k => k.hom) hcomm
  have hXU : IsAlgebraicSpace B S hS (pullback f.hom U.1.ι) :=
    isAlgebraicSpace_pullback B S hS f.hom U.1.ι X.2 U.2.1 A.2
  let t : (W.1.preimage (restrictOverι g U).hom).toFunctor ⟶ pullback f.hom U.1.ι :=
    pullback.lift (W.1.fromPreimage (restrictOverι g U).hom ≫ u.hom)
      ((W.1.preimage (restrictOverι g U).hom).ι ≫ (restrictOverHom g U).hom) (by
        rw [Category.assoc, hu, ← Category.assoc, ← hfst, Category.assoc, hsqg.w,
          Category.assoc]
        rfl)
  have ht_snd : t ≫ pullback.snd f.hom U.1.ι =
      (W.1.preimage (restrictOverι g U).hom).ι ≫ (restrictOverHom g U).hom :=
    pullback.lift_snd _ _ _
  have hsqt : IsPullback t (W.1.fromPreimage (restrictOverι g U).hom)
      (pullback.fst f.hom U.1.ι) u.hom := by
    have houter : IsPullback (t ≫ pullback.snd f.hom U.1.ι)
        (W.1.fromPreimage (restrictOverι g U).hom) U.1.ι (u.hom ≫ f.hom) := by
      rw [ht_snd, hu]
      exact (Subfunctor.isPullback_preimage (restrictOverι g U).hom W.1).flip.paste_horiz
        hsqg.flip
    exact IsPullback.of_right houter (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback f.hom U.1.ι).flip
  have ht : IsEtale B S hS t :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS hsqt hWU hXU W.2.1 X.2 hue
  have hWflat : IsFlat B S hS
      ((W.1.preimage (restrictOverι g U).hom).ι ≫ (restrictOverHom g U).hom) := by
    rw [← ht_snd]
    exact isFlat_comp B S hS hWU hXU U.2.1 _ _ (isFlat_of_isEtale B S hS ht) hflat
  have hWlfp : IsLocallyOfFinitePresentation B S hS
      ((W.1.preimage (restrictOverι g U).hom).ι ≫ (restrictOverHom g U).hom) := by
    rw [← ht_snd]
    exact isLocallyOfFinitePresentation_comp B S hS hWU hXU U.2.1 _ _
      (isLocallyOfFinitePresentation_of_isEtale B S hS ht) hlfp
  -- the case of the closed subspace `W ⊆ Y`
  obtain ⟨A', b, Z, hZfp, hUZ, hb, hW'flat, hW'lfp⟩ :=
    exists_isBlowupAlong_isFlat_strictTransform_of_closedSubspace_of_noetherian (hN := hN) hZ
      g hgfp hAqc hAqs U hUqc W hWflat hWlfp
  rw [← hcomm] at hW'flat hW'lfp
  -- Stacks 0863, part (2): the strict transform of `X` is flat and locally of finite presentation
  obtain ⟨hXflat, hXlfp⟩ :=
    isFlat_and_isLocallyOfFinitePresentation_strictTransformSpaceToBlowUp_of_comp hb f u hue hus
      hW'flat hW'lfp
  -- the strict transform is closed in `X ×_A A'`, which is quasi-compact and quasi-separated
  -- over `A'`
  have hcl := strictTransformSubfunctor_isClosedSubspace B S hS f b (Z.1.preimage b.hom)
  have hsqb := AlgebraicSpaces.isPullback_hom B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
  refine ⟨A', b, Z, hZfp, hUZ, hb, hXflat, hXlfp, ?_, ?_⟩
  · exact isQuasiCompact_comp B S hS (strictTransformPullback B S hS f b).2 A'.2 _ _
      (isQuasiCompact_of_isClosedImmersion' B S hS hcl.2)
      (isQuasiCompact_of_isPullback B S hS hsqb hft.2)
  · exact isQuasiSeparated_comp B S hS hcl.1 (strictTransformPullback B S hS f b).2 _ _
      (isQuasiSeparated_of_isClosedImmersion B S hS hcl.2)
      (isQuasiSeparated_of_isPullback B S hS hsqb hqs)

end AlgebraicGeometry.Space

end
