module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.Constructibility
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage

/-!
# The reduction of [Stacks, Tag 0GL0] to the affine line, over bases on which `n` is invertible

Fix an integer `n`. Granted the proper base change theorem, if the sheaf form of [Stacks, Tag
0GL0] holds for the affine line `𝔸¹_S ⟶ S` over every affine scheme `S` on which `n` is
invertible, then `Rf_!` preserves constructibility for every morphism `f : X ⟶ Y` of the theorem
whose target `Y` is a scheme on which `n` is invertible. Invertibility of `n` passes to every
scheme over `Y` (`Stacks.Kummer.isUnit_natCast_of_hom`), so it holds on every base met in the
reduction to the affine line.

## Main results

* `isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_affineLine_of_isUnit`:
  over a base on which `n` is invertible, `Rf_!` preserves `D⁺_{tors, c}`, given the affine line.
* `isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_affineLine_of_isUnit`: over a
  torsion ring and a base on which `n` is invertible, `Rf_!` preserves `D_c`, given the affine
  line.

## References

* [Stacks Project, Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.CompactificationOf

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **[Stacks, Tag 0GL0] for affine space**, granted the proper base change theorem `h095T`
(Tag 095T): if the sheaf form of the theorem holds for the affine line over every affine scheme on
which `n` is invertible, it holds for affine `(d + 1)`-space `𝔸^{d + 1}_Y ⟶ Y` over every affine
`Y` on which `n` is invertible. -/
theorem lowerShriekConstructibleOnSheaves_affineSpace_of_isUnit
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    {n : ℕ} (hA1 : ∀ (Y : Scheme.{u}) [IsAffine Y], IsUnit ((n : ℕ) : Γ(Y, ⊤)) →
      LowerShriekConstructibleOnSheaves Λ (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y))
    (d : ℕ) (Y : Scheme.{u}) [IsAffine Y] (hnY : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    LowerShriekConstructibleOnSheaves Λ (AffineSpace (ULift.{u} (Fin (d + 1))) Y ↘ Y) := by
  induction d generalizing Y with
  | zero => exact hA1 Y hnY
  | succ d ih =>
    let A := AffineSpace (ULift.{u} (Fin 1)) Y
    let g : A ⟶ Y := A ↘ Y
    let f : AffineSpace (ULift.{u} (Fin (d + 1 + 1))) Y ⟶ A :=
      (Stacks.Chow.affineSpaceSuccIso Y (d + 1)).hom ≫
        (AffineSpace (ULift.{u} (Fin (d + 1))) A ↘ A)
    have hf : LowerShriekConstructibleOnSheaves Λ f :=
      lowerShriekConstructibleOnSheaves_iso_comp Λ (Stacks.Chow.affineSpaceSuccIso Y (d + 1))
        (ih A (Stacks.Kummer.isUnit_natCast_of_hom g hnY))
    obtain ⟨jg, -⟩ := exists_quasiCompact_compactificationOf_of_isQuasiAffine g
    obtain ⟨_, _⟩ : IsSeparated ((f ≫ jg.immersion) ≫ jg.toBase) ∧
        LocallyOfFiniteType ((f ≫ jg.immersion) ≫ jg.toBase) := by
      rw [Category.assoc, jg.immersion_toBase]; exact ⟨inferInstance, inferInstance⟩
    have := IsSeparated.of_comp (f ≫ jg.immersion) jg.toBase
    have := locallyOfFiniteType_of_comp (f ≫ jg.immersion) jg.toBase
    obtain ⟨J, -⟩ := exists_quasiCompact_compactificationOf_of_isQuasiAffine (f ≫ jg.immersion)
    have hfg := lowerShriekConstructibleOnSheaves_comp Λ h095T jg J hf (hA1 Y hnY)
    refine lowerShriekConstructibleOnSheaves_congr Λ ?_ hfg
    simpa [f, g, Category.assoc] using Stacks.Chow.affineSpaceSuccIso_hom_over Y (d + 1)

/-- **The affine case of [Stacks, Tag 0GL0]**, granted the proper base change theorem `h095T`
(Tag 095T): if the sheaf form of the theorem holds for the affine line over every affine scheme on
which `n` is invertible, it holds for every morphism locally of finite presentation `f : X ⟶ Y`
of affine schemes with `n` invertible on `Y`. -/
theorem lowerShriekConstructibleOnSheaves_of_isAffine_of_isUnit
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    {n : ℕ} (hA1 : ∀ (Y : Scheme.{u}) [IsAffine Y], IsUnit ((n : ℕ) : Γ(Y, ⊤)) →
      LowerShriekConstructibleOnSheaves Λ (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y))
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (hnY : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    LowerShriekConstructibleOnSheaves Λ f := by
  obtain ⟨d, i, hi, hif⟩ := exists_isClosedImmersion_affineSpace_succ f
  let p := AffineSpace (ULift.{u} (Fin (d + 1))) Y ↘ Y
  have : LocallyOfFinitePresentation (i ≫ p) := by rw [hif]; infer_instance
  have : LocallyOfFinitePresentation i := locallyOfFinitePresentation_of_comp i p
  obtain ⟨J, -⟩ := exists_quasiCompact_compactificationOf_of_isQuasiAffine p
  have h := lowerShriekConstructibleOnSheaves_closedImmersion_comp Λ h095T i
    (AlgebraicGeometry.isCompact_compl_range_of_isClosedImmersion i) J
    (lowerShriekConstructibleOnSheaves_affineSpace_of_isUnit Λ h095T hA1 d Y hnY)
  exact lowerShriekConstructibleOnSheaves_congr Λ hif h

/-- **[Stacks, Tag 0GL0] for `D⁺_{tors, c}`, granted the proper base change theorem and the case
of the affine line.** Let `f : X ⟶ Y` be a morphism locally of finite presentation and
quasi-compact, with `X` quasi-compact and quasi-separated and `Y` quasi-separated, let `j` be a
compactification of `f`, let `Λ` be a Noetherian ring and let `n` be invertible on `Y`. If, for
every affine scheme `S` on which `n` is invertible, every compactification of `𝔸¹_S ⟶ S` and every
constructible torsion sheaf `ℱ` on `𝔸¹_S`, `R(𝔸¹_S ⟶ S)_!(ℱ[0])` has constructible cohomology
(Tag 0GKZ, `hA1`), then `Rf_!` carries `D⁺_{tors, c}(X_étale, Λ)` into `D⁺_{tors, c}(Y_étale, Λ)`.
The hypothesis `h095T` is the proper base change theorem (Tag 095T). -/
theorem isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_affineLine_of_isUnit
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    {n : ℕ} (hA1 : ∀ (S : Scheme.{u}) [IsAffine S], IsUnit ((n : ℕ) : Γ(S, ⊤)) →
      LowerShriekConstructibleOnSheaves Λ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]
    (j : CompactificationOf (Over.mk f)) (K : DerivedCategory (EtaleModules.{u, r} Λ X))
    (hK : IsTorsionConstructibleEtaleComplexPlus Λ K) (hnY : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    IsTorsionConstructibleEtaleComplexPlus Λ
      ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj K) := by
  suffices h : LowerShriekConstructibleOnSheaves Λ f from
    isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_sheaves Λ j (h j) K hK
  refine lowerShriekConstructibleOnSheaves_of_isAffineOpen_target Λ h095T f fun V hV ↦ ?_
  have : IsAffine V := hV
  have : CompactSpace (f ⁻¹ᵁ V) := isCompact_iff_compactSpace.1 (f.isCompact_preimage hV.isCompact)
  have : QuasiSeparatedSpace (f ⁻¹ᵁ V) := quasiSeparatedSpace_of_quasiSeparated (f ⁻¹ᵁ V).ι
  refine lowerShriekConstructibleOnSheaves_of_isAffineOpen Λ h095T
    (j.baseChange (isPullback_morphismRestrict f V).flip) fun W hW ↦ ?_
  have : IsAffine W := hW
  exact lowerShriekConstructibleOnSheaves_of_isAffine_of_isUnit Λ h095T hA1 (W.ι ≫ f ∣_ V)
    (Stacks.Kummer.isUnit_natCast_of_hom V.ι hnY)

/-- **[Stacks, Tag 0GL0] for `D_c` over a torsion ring, granted the proper base change theorem,
Tag 095U and the case of the affine line.** Let `f : X ⟶ Y` be locally of finite presentation and
quasi-compact, with `X` and `Y` quasi-compact and quasi-separated, let `j` be a compactification
of `f`, let `Λ` be a Noetherian torsion ring and let `n` be invertible on `Y`. If the affine line
hypothesis `hA1` (Tag 0GKZ) holds over every affine scheme on which `n` is invertible, then `Rf_!`
carries `D_c(X_étale, Λ)` into `D_c(Y_étale, Λ)`. The hypotheses `h095T` and `h095U` are the
proper base change theorem (Tag 095T) and the cohomological dimension bound of Tag 095U. -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_affineLine_of_isUnit
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F))
    {n : ℕ} (hA1 : ∀ (S : Scheme.{u}) [IsAffine S], IsUnit ((n : ℕ) : Γ(S, ⊤)) →
      LowerShriekConstructibleOnSheaves Λ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
    (hΛ : IsAddTorsion Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    [QuasiCompact f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (j : CompactificationOf (Over.mk f))
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (hK : IsConstructibleEtaleComplex Λ K)
    (hnY : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj K) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_fiber_le j.toBase
  intro i
  let K' := (DerivedCategory.TStructure.t.truncGE (i - 2 * d)).obj K
  have hK' : IsTorsionConstructibleEtaleComplexPlus Λ K' :=
    ⟨⟨i - 2 * d, fun n hn ↦ DerivedCategory.isZero_of_isGE K' (i - 2 * d) n hn⟩, fun n ↦
      ⟨isTorsionEtaleModule_of_isAddTorsion Λ hΛ _,
        DerivedCategoryB.derivedCategoryB_truncGE_obj _
          (isWeakSerre_isConstructibleEtaleModule Λ X) _ K hK n⟩⟩
  have := isIso_homologyMap_derivedLowerShriekUnbounded_map_truncGEπ_of_isAddTorsion Λ j h095U hΛ
    d hd K i i le_rfl
  exact (IsConstructibleEtaleModule Λ).prop_of_iso
    (asIso ((DerivedCategory.homologyFunctor _ i).map
      ((derivedLowerShriekUnbounded.{u, r} f j Λ).map
        ((DerivedCategory.TStructure.t.truncGEπ (i - 2 * d)).app K)))).symm
    ((isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_affineLine_of_isUnit Λ
      h095T hA1 f j K' hK' hnY).2 i).2

end Stacks.EtaleCohomology

end
