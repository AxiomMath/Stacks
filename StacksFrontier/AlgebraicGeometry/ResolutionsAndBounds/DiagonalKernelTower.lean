module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.SchemeModules
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernel
public import StacksFrontier.AlgebraicGeometry.ProperMapping
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.BrutalTruncationResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.DiagonalResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExtVanishingRegular
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FibreBandSplitting
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyNoetherianRegular
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SmoothBandSplitting
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# The diagonal kernel in a bounded tower of external tensor products

Let `k` be a field and `X` a quasi-compact separated scheme smooth over `k`. Then there are an
integer `N ≥ 0` and finite locally free `𝒪_X`-modules `ℰ₀, …, ℰ_N`, `𝒢₀, …, 𝒢_N` such that the
diagonal kernel `𝒪_Δ = RΔ_*𝒪_X` of `D(𝒪_{X ×_k X})` is a direct summand of an `N`-fold
extension of finite direct sums of the objects `(ℰⱼ ⊠ 𝒢ⱼ)[i]`, `j ≤ N`, `0 ≤ i ≤ N`:

`𝒪_Δ ∈ smd(add({ℰⱼ ⊠ 𝒢ⱼ}[-N, 0])^{⋆ (N + 1)})`.

This is the content of the proof of [Stacks, Tag 0FZ5] (and of the first paragraph of
[Stacks, Section 0G07]) with the window of shifts and the number of extensions kept: the
resolution `⋯ → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀ → 𝒪_Δ → 0` of [Stacks, Tag 0FZ2], brutally truncated after
`N ≥ dim(X × X)` steps, has `𝒪_Δ` as a direct summand by [Stacks, Tag 0FZ4] (with
[Stacks, Tag 0FZ3] part (2)), and lies in the displayed subcategory by [Stacks, Tag 0FX7]. The
membership of `𝒪_Δ` in `⟨ℰ ⊠ 𝒢⟩` that [Stacks, Tag 0FZ5] records forgets the window, which is
what the uniform bounds of [Stacks, Tag 0FZ7] and [Stacks, Tag 0FZ8] need.

## Main definitions

* `AlgebraicGeometry.diagonalBoxes`: the objects `(ℰⱼ ⊠ 𝒢ⱼ)[0]`, `j ≤ N`, of `D(𝒪_{X ×_S X})`.

## Main results

* `AlgebraicGeometry.exists_diagonalKernel_retractClosure_extensionProductIter`.

## References

* [Stacks Project, Tag 0FZ5](https://stacks.math.columbia.edu/tag/0FZ5)
* [Stacks Project, Section 0G07](https://stacks.math.columbia.edu/tag/0G07)
* [Stacks Project, Tag 0FZ2](https://stacks.math.columbia.edu/tag/0FZ2)
* [Stacks Project, Tag 0FZ4](https://stacks.math.columbia.edu/tag/0FZ4)
* [Stacks Project, Tag 0FX7](https://stacks.math.columbia.edu/tag/0FX7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The external tensor products `ℰⱼ ⊠ 𝒢ⱼ`, `j ≤ N`, placed in degree zero, as a property of
objects of `D(𝒪_{X ×_S X})` (up to isomorphism). -/
def diagonalBoxes (N : ℕ) (E G : ℕ → X.Modules) :
    ObjectProperty (DerivedCategory (pullback f f).Modules) :=
  fun Z => ∃ j ≤ N, Nonempty (Z ≅
    (DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
      (externalTensorProduct f f (E j) (G j)))

/-- **The diagonal kernel is the structure sheaf of the diagonal placed in degree zero**: the
diagonal of a separated morphism is a closed immersion, hence affine, so `RΔ_*𝒪_X = (Δ_*𝒪_X)[0]`
([Stacks, Tag 01XC]). -/
def diagonalKernelIsoSingle [IsSeparated f] :
    diagonalKernel f ≅ (DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
      ((Scheme.Modules.pushforward (pullback.diagonal f)).obj
        (SheafOfModules.unit X.ringCatSheaf)) :=
  (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.derivedPushforwardSingleIso
    (pullback.diagonal f) 0 (SheafOfModules.unit X.ringCatSheaf)
    (show (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent from inferInstance)).symm

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The diagonal kernel lies in a bounded tower of external tensor products.** For `X`
quasi-compact, separated and smooth over a field there are `N` and finite locally free
`ℰⱼ`, `𝒢ⱼ` with `𝒪_Δ ∈ smd(add({(ℰⱼ ⊠ 𝒢ⱼ)[0]}_{j ≤ N}[-N, 0])^{⋆ (N + 1)})` in
`D(𝒪_{X ×_k X})`. -/
theorem exists_diagonalKernel_retractClosure_extensionProductIter
    [CompactSpace X] [IsSeparated f] [Smooth f] :
    ∃ (N : ℕ) (E G : ℕ → X.Modules),
      (∀ i, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (E i)) ∧
      (∀ i, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (G i)) ∧
      ((⨆ i ∈ Set.Icc (-(N : ℤ)) 0, (diagonalBoxes f N E G).isoClosure.shift i
        ).binaryProductsClosure.extensionProductIter N).retractClosure (diagonalKernel f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := ⟨⟩
  have : IsSeparated (terminal.from X) := by
    rw [show terminal.from X = f ≫ terminal.from (Spec (.of k)) from terminal.hom_ext _ _]
    infer_instance
  have : HasResolutionProperty X :=
    hasResolutionProperty_of_isRegular_of_isNoetherian X (isRegular_of_smooth_over_field f)
  obtain ⟨C, E, G, hE, hG, h0, hterm, hac⟩ := exists_diagonalResolution k f
  have : IsLocallyNoetherian (pullback f f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f ≫ f)
  have : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  have : IsNoetherian (pullback f f) := ⟨⟩
  have hbox : ∀ (N j : ℕ), j ≤ N →
      diagonalBoxes f N E G ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
        (externalTensorProduct f f (E j) (G j))) := fun N j hj => ⟨j, hj, ⟨Iso.refl _⟩⟩
  rcases isEmpty_or_nonempty (pullback f f : Scheme.{u}) with hW | hW
  · -- Every object over the empty product is zero, and a zero object is a retract of anything.
    refine ⟨0, E, G, hE, hG, ?_⟩
    have hz : IsZero (diagonalKernel f) := isZero_of_isEmpty _
    refine ⟨(DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
      (externalTensorProduct f f (E 0) (G 0)), ?_,
      ⟨{ i := 0, r := 0, retract := hz.eq_of_src _ _ }⟩⟩
    rw [extensionProductIter_zero]
    refine le_limitsClosure _ _ _ ((prop_iSup_iff _ _).2 ⟨0, (prop_iSup_iff _ _).2
      ⟨by simp, ?_⟩⟩)
    exact ⟨_, hbox 0 0 le_rfl, ⟨(shiftFunctorZero _ ℤ).app _⟩⟩
  obtain ⟨d, hd⟩ :=
    exists_topologicalKrullDim_eq_natCast_of_locallyOfFiniteType k (pullback.fst f f ≫ f) hW
  set N := max d 1 with hN
  refine ⟨N, E, G, hE, hG, ?_⟩
  -- Coherence of the terms of the resolution.
  have hCcoh : ∀ j : ℕ, (C.X j).IsCoherent := by
    rintro (_ | j)
    · exact isCoherent_of_moduleIso h0.symm (isCoherent_diagonalUnit (R := k) f)
    · exact isCoherent_of_moduleIso (hterm j).symm
        (isCoherent_externalTensorProduct (R := k) f (E j) (G j) (hE j) (hG j))
  -- The brutal truncation `L` of the resolution, in degrees `[-N, 0]`
  -- (`AlgebraicGeometry.brutalTruncationOfAcyclicResolution`, the brutal truncation step of
  -- [Stacks, Tag 0FZ5]).
  obtain ⟨L, hLge, hLle, hLX, ⟨hL0⟩, hLgap, hLcoh⟩ :=
    brutalTruncationOfAcyclicResolution (pullback f f) C hac hCcoh N (by omega)
  have hdN : (d : ℤ) ≤ (N : ℤ) := by exact_mod_cast le_max_left d 1
  have hKle : DerivedCategory.TStructure.t.IsLE (DerivedCategory.Q.obj L) 0 := inferInstance
  -- The splitting at the gap in the cohomology of `L`, placed in degree `0`.
  obtain ⟨e⟩ := exists_iso_biprod_truncLE_truncGE (pullback f f)
    (isRegular_of_smooth_over_field (pullback.fst f f ≫ f)) d hd
    (forall_separatedCohomologyHomVanishing (pullback f f) d) (DerivedCategory.Q.obj L)
    ⟨⟨-(N : ℤ), inferInstance⟩, ⟨0, hKle⟩⟩ hLcoh (-(d : ℤ))
    fun i h₁ h₂ => hLgap i (by omega) (by omega)
  rw [show -(d : ℤ) + (d : ℤ) = 0 by omega] at e
  -- `τ^{≥0}` of `L` is `𝒪_Δ` placed in degree `0`.
  have hLT : IsIso ((DerivedCategory.TStructure.t.truncLTι 1).app (DerivedCategory.Q.obj L)) :=
    (DerivedCategory.TStructure.t.isLE_iff_isIso_truncLTι_app 0 1 (by omega)
      (DerivedCategory.Q.obj L)).1 hKle
  have eB : (DerivedCategory.TStructure.t.truncGE 0).obj (DerivedCategory.Q.obj L) ≅
      diagonalKernel f :=
    ((DerivedCategory.TStructure.t.truncGE 0).mapIso
        (asIso ((DerivedCategory.TStructure.t.truncLTι 1).app
          (DerivedCategory.Q.obj L)))).symm ≪≫
      (DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor
        (C := (pullback f f).Modules) 0).app (DerivedCategory.Q.obj L) ≪≫
      (DerivedCategory.singleFunctor (pullback f f).Modules 0).mapIso (hL0 ≪≫ h0) ≪≫
      (diagonalKernelIsoSingle f).symm
  -- `𝒪_Δ` is a retract of `L`.
  have hretract : Retract (diagonalKernel f) (DerivedCategory.Q.obj L) :=
    { i := eB.inv ≫ biprod.inr ≫ e.inv
      r := e.hom ≫ biprod.snd ≫ eB.hom
      retract := by simp }
  -- [Stacks, Tag 0FX7] part (3): `L` lies in the tower of its terms.
  let P : ObjectProperty (pullback f f).Modules := fun M =>
    ∃ j ≤ N, Nonempty (M ≅ externalTensorProduct f f (E j) (G j))
  have hterms : ∀ i ∈ Set.Icc (-(N : ℤ)) (0 : ℤ),
      P.binaryProductsClosure.retractClosure (L.X i) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := Set.mem_Icc.1 hi
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = -(j : ℤ) := ⟨(-i).toNat, by omega⟩
    obtain ⟨eX⟩ := hLX j (by omega)
    exact le_retractClosure _ _ (le_limitsClosure _ _ _ ⟨j, by omega, ⟨eX ≪≫ hterm j⟩⟩)
  have hfx7 :=
    (DerivedCategory.prop_retractClosure_extensionProductIter_of_prop_homology_and_of_prop_X P
      (a := -(N : ℤ)) (b := 0) (by omega)).2 L hterms
  rw [show ((0 : ℤ) - -(N : ℤ)).toNat = N by omega] at hfx7
  obtain ⟨-, -, hstable, -⟩ :=
    ObjectProperty.retractClosure_extensionProductIter_isClosedUnderBinaryProducts_and_add
      ((⨆ i ∈ Set.Icc (-(N : ℤ)) (0 : ℤ),
        P.map (DerivedCategory.singleFunctor (pullback f f).Modules i))).binaryProductsClosure
      N 0
  have hmem := hstable.of_retract hretract hfx7
  -- From the degree-`i` placements to the shifts of the degree-zero placements.
  refine monotone_retractClosure (monotone_extensionProductIter
    (limitsClosure_monotone _ ?_) _) _ hmem
  refine iSup₂_le fun i hi => ?_
  refine le_trans ?_ (le_iSup₂_of_le i hi le_rfl)
  rintro Z ⟨M, ⟨j, hj, ⟨eM⟩⟩, ⟨eZ⟩⟩
  exact ⟨_, hbox N j hj,
    ⟨(shiftFunctor (DerivedCategory (pullback f f).Modules) i).mapIso eZ.symm ≪≫
      ((DerivedCategory.singleFunctors (pullback f f).Modules).shiftIso i 0 i (by omega)).app M ≪≫
      (DerivedCategory.singleFunctor (pullback f f).Modules 0).mapIso eM⟩⟩

end AlgebraicGeometry

end
