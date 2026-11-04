module

public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyRegular
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.DiagonalBoxGenerator

/-!
# The diagonal trick, with the resolution property of a regular scheme proved

`StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.DiagonalBoxGenerator` proves [Stacks, Tag
0FZ5]: for a field `k` and a quasi-compact separated smooth scheme `X` over `k`, there are finite
locally free `𝒪_X`-modules `ℰ` and `𝒢` with `𝒪_Δ ∈ ⟨ℰ ⊠ 𝒢⟩` in `D(𝒪_{X × X})`. Its first step
is that `X`, being regular, has the resolution property, [Stacks, Tag 0F8A], which that module
reaches through one hypothesis on ideal coverings
(`AlgebraicGeometry.ExistsSectionImageIdeal`).

This module runs the same argument with [Stacks, Tag 0F8A] taken from
`AlgebraicGeometry.IsRegular.hasResolutionProperty`, which carries no
hypothesis, so that ideal-covering hypothesis is dropped too. The other four hypotheses of the
argument (`AlgebraicGeometry.HomVanishingAcrossCohomologyGap`,
`AlgebraicGeometry.FiniteDimensionalOfSmoothOverField`,
`AlgebraicGeometry.BrutalTruncationOfAcyclicResolution` and
`AlgebraicGeometry.ExternalTensorSumRetract`) are as there.

## Main results

* `AlgebraicGeometry.exists_externalTensor_triangEnvelope_diagonal_of_regular` — the diagonal
  trick, with the resolution property of `X` proved.

## References

* [Stacks Project, Tag 0FZ5](https://stacks.math.columbia.edu/tag/0FZ5)
* [Stacks Project, Tag 0F8A](https://stacks.math.columbia.edu/tag/0F8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **The diagonal trick, [Stacks, Tag 0FZ5], with [Stacks, Tag 0F8A] proved.** Let `k` be a
field and let `X` be a quasi-compact separated smooth scheme over `k`. There are finite locally
free `𝒪_X`-modules `ℰ` and `𝒢` such that `𝒪_Δ ∈ ⟨ℰ ⊠ 𝒢⟩` in `D(𝒪_{X × X})`, where `⟨−⟩` is the
smallest strictly full saturated triangulated subcategory containing the object. This is
`AlgebraicGeometry.exists_externalTensor_triangEnvelope_diagonal` without its ideal-covering
hypothesis: the resolution property of the regular scheme `X` is
`AlgebraicGeometry.IsRegular.hasResolutionProperty`. -/
public theorem exists_externalTensor_triangEnvelope_diagonal_of_regular
    (hvan : HomVanishingAcrossCohomologyGap.{u})
    (hdim : FiniteDimensionalOfSmoothOverField.{u})
    (htrunc : BrutalTruncationOfAcyclicResolution.{u})
    (hsum : ExternalTensorSumRetract.{u})
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [CompactSpace X] [IsSeparated f] [Smooth f] :
    ∃ E G : X.Modules,
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E ∧
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) G ∧
      (ObjectProperty.singleton ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
          (externalTensorProduct f f E G))).triangEnvelope
        ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
          ((Scheme.Modules.pushforward (pullback.diagonal f)).obj
            (SheafOfModules.unit X.ringCatSheaf))) := by
  -- `X` is regular, hence has the resolution property.
  have hsepT : IsSeparated (terminal.from X) := by
    have h : terminal.from X = f ≫ terminal.from (Spec (.of k)) := terminal.hom_ext _ _
    rw [h]; infer_instance
  have hres : HasResolutionProperty X :=
    AlgebraicGeometry.IsRegular.hasResolutionProperty X
      (isRegular_of_smooth_over_field f)
  -- The resolution of the diagonal by external tensor products.
  obtain ⟨C, E, G, hE, hG, h0, hterm, hac⟩ := exists_diagonalResolution k f
  -- `X × X` is smooth over `k`, hence regular, Noetherian and finite dimensional.
  have hWreg : IsRegular (pullback f f) :=
    isRegular_of_smooth_over_field (pullback.fst f f ≫ f)
  have : IsLocallyNoetherian (pullback f f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f ≫ f)
  have : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  have hWnoeth : IsNoetherian (pullback f f) := ⟨⟩
  obtain ⟨d, hd⟩ := hdim k (pullback f f) (pullback.fst f f ≫ f)
  -- A single external tensor product dominating all the terms.
  obtain ⟨A', B', hA', hB', hret⟩ :=
    hsum k X f (max d 1) E G hE hG
  refine ⟨A', B', hA', hB', ?_⟩
  -- Coherence of the terms of the resolution.
  have hCcoh : ∀ j : ℕ, (C.X j).IsCoherent := by
    intro j
    cases j with
    | zero =>
      exact AlgebraicGeometry.isCoherent_of_moduleIso (h0.symm) (isCoherent_diagonalUnit (R := k) f)
    | succ j =>
      exact AlgebraicGeometry.isCoherent_of_moduleIso (hterm j).symm
        (isCoherent_externalTensorProduct (R := k) f (E j) (G j) (hE j) (hG j))
  -- The brutal truncation.
  obtain ⟨L, hLge, hLle, hLterm, ⟨hL0⟩, hLgap, hLcoh⟩ :=
    htrunc (pullback f f) C hac hCcoh (max d 1) (by omega)
  have hdN : (d : ℤ) ≤ ((max d 1 : ℕ) : ℤ) := by exact_mod_cast le_max_left d 1
  have hKle : DerivedCategory.TStructure.t.IsLE (DerivedCategory.Q.obj L) 0 := inferInstance
  have hKge : DerivedCategory.TStructure.t.IsGE (DerivedCategory.Q.obj L)
      (-((max d 1 : ℕ) : ℤ)) := inferInstance
  have hKbdd : DerivedCategory.TStructure.t.bounded (DerivedCategory.Q.obj L) :=
    ⟨⟨-((max d 1 : ℕ) : ℤ), hKge⟩, ⟨0, hKle⟩⟩
  -- The gap, placed so that the splitting degree is `0`.
  have hgap : ∀ i : ℤ, -(d : ℤ) < i → i < -(d : ℤ) + (d : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor (pullback f f).Modules i).obj
        (DerivedCategory.Q.obj L)) := fun i h1 h2 => hLgap i (by omega) (by omega)
  obtain ⟨e⟩ := exists_iso_biprod_truncLE_truncGE (pullback f f) hWreg d hd
    (hvan (pullback f f) d) (DerivedCategory.Q.obj L) hKbdd hLcoh (-(d : ℤ)) hgap
  rw [show -(d : ℤ) + (d : ℤ) = 0 from by omega] at e
  -- `τ^{≥0}` of the truncation is concentrated in degree `0`.
  have hBle : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncGE 0).obj (DerivedCategory.Q.obj L)) 0 := by
    refine (DerivedCategory.isLE_iff _ 0).2 fun i hi => ?_
    have := DerivedCategory.isIso_homologyMap_truncGEπ_app (C := (pullback f f).Modules)
      0 i (le_of_lt hi) (DerivedCategory.Q.obj L)
    exact (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj L) 0 i hi).of_iso
      (asIso ((DerivedCategory.homologyFunctor (pullback f f).Modules i).map
        ((DerivedCategory.TStructure.t.truncGEπ 0).app (DerivedCategory.Q.obj L)))).symm
  -- and it is `𝒪_Δ` placed in degree `0`.
  have hLT : IsIso ((DerivedCategory.TStructure.t.truncLTι 1).app (DerivedCategory.Q.obj L)) :=
    (DerivedCategory.TStructure.t.isLE_iff_isIso_truncLTι_app 0 1 (by omega)
      (DerivedCategory.Q.obj L)).1 hKle
  have eB : (DerivedCategory.TStructure.t.truncGE 0).obj (DerivedCategory.Q.obj L) ≅
      (DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
        ((Scheme.Modules.pushforward (pullback.diagonal f)).obj
          (SheafOfModules.unit X.ringCatSheaf)) :=
    ((DerivedCategory.TStructure.t.truncGE 0).mapIso
        (asIso ((DerivedCategory.TStructure.t.truncLTι 1).app
          (DerivedCategory.Q.obj L)))).symm ≪≫
      (DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor
        (C := (pullback f f).Modules) 0).app (DerivedCategory.Q.obj L) ≪≫
      (DerivedCategory.singleFunctor (pullback f f).Modules 0).mapIso (hL0 ≪≫ h0)
  -- `𝒪_Δ[0]` is a retract of the truncation.
  have hretract : Retract
      ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
        ((Scheme.Modules.pushforward (pullback.diagonal f)).obj
          (SheafOfModules.unit X.ringCatSheaf)))
      (DerivedCategory.Q.obj L) :=
    { i := eB.inv ≫ biprod.inr ≫ e.inv
      r := e.hom ≫ biprod.snd ≫ eB.hom
      retract := by simp }
  -- The terms of the truncation are summands of a single external tensor product.
  have hterms : ∀ i ∈ Set.Icc (-((max d 1 : ℕ) : ℤ)) (0 : ℤ),
      (ObjectProperty.singleton
        (externalTensorProduct f f A' B')).binaryProductsClosure.retractClosure (L.X i) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := Set.mem_Icc.1 hi
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = -(j : ℤ) := ⟨(-i).toNat, by omega⟩
    have hjN : j ≤ max d 1 := by omega
    obtain ⟨eL⟩ := hLterm j hjN
    obtain ⟨r⟩ := hret j hjN
    refine ⟨externalTensorProduct f f A' B',
      ObjectProperty.le_limitsClosure _ _ _ ((ObjectProperty.singleton_iff _ _).2 rfl), ⟨?_⟩⟩
    refine { i := (eL ≪≫ hterm j).hom ≫ r.i, r := r.r ≫ (eL ≪≫ hterm j).inv, retract := ?_ }
    rw [Category.assoc, ← Category.assoc r.i, r.retract, Category.id_comp, Iso.hom_inv_id]
  -- [Stacks, Tag 0FX7] part (3).
  have hfx7 :=
    (DerivedCategory.prop_retractClosure_extensionProductIter_of_prop_homology_and_of_prop_X
      (ObjectProperty.singleton (externalTensorProduct f f A' B'))
      (a := -((max d 1 : ℕ) : ℤ)) (b := 0) (by omega)).2 L hterms
  -- [Stacks, Tag 0FX4]: the subcategory is stable under retracts and strictly full.
  obtain ⟨hiso, -, hstable, -⟩ :=
    ObjectProperty.retractClosure_extensionProductIter_isClosedUnderBinaryProducts_and_add
      (((⨆ i ∈ Set.Icc (-((max d 1 : ℕ) : ℤ)) (0 : ℤ),
        (ObjectProperty.singleton (externalTensorProduct f f A' B')).map
          (DerivedCategory.singleFunctor (pullback f f).Modules i))).binaryProductsClosure)
      ((0 : ℤ) - -((max d 1 : ℕ) : ℤ)).toNat 0
  have hmem := hstable.of_retract hretract hfx7
  -- The inclusion into `⟨ℰ ⊠ 𝒢⟩`, by [Stacks, Tag 0FX9].
  refine ObjectProperty.triangEnvelopeIter_le_triangEnvelope _
    ((0 : ℤ) - -((max d 1 : ℕ) : ℤ)).toNat _ ?_
  rw [ObjectProperty.triangEnvelopeIter_eq_iSup_retractClosure_extensionProductIter,
    ObjectProperty.prop_iSup_iff]
  refine ⟨max d 1, ?_⟩
  refine ObjectProperty.monotone_retractClosure
    (ObjectProperty.monotone_extensionProductIter
      (ObjectProperty.limitsClosure_monotone _ ?_) _) _ hmem
  refine iSup₂_le fun i hi => ?_
  obtain ⟨hi1, hi2⟩ := Set.mem_Icc.1 hi
  refine le_trans ?_ (le_iSup₂_of_le i (Set.mem_Icc.2 ⟨hi1, by omega⟩) le_rfl)
  rintro Z ⟨M, hM, ⟨eZ⟩⟩
  obtain rfl : externalTensorProduct f f A' B' = M := (ObjectProperty.singleton_iff _ _).1 hM
  exact ⟨_, (ObjectProperty.singleton_iff _ _).2 rfl,
    ⟨(shiftFunctor (DerivedCategory (pullback f f).Modules) i).mapIso eZ.symm ≪≫
      ((DerivedCategory.singleFunctors (pullback f f).Modules).shiftIso i 0 i (by omega)).app
        (externalTensorProduct f f A' B')⟩⟩

end AlgebraicGeometry

end
