module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealEtaleClopenSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleIdealSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSum
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Descending a finite type ideal along a quasi-compact separated étale morphism

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, let
`φ : W ⟶ X` be a quasi-compact separated étale morphism, let `U ⊆ X` be a quasi-compact open
subspace and let `𝓘 ⊆ 𝒪_W` be a finite type quasi-coherent sheaf of ideals with
`V(𝓘) ∩ φ⁻¹(U) = ∅`.  Stacks 087B asserts that there is a finite type quasi-coherent sheaf of
ideals `𝓙 ⊆ 𝒪_X` with `V(𝓙) ∩ U = ∅` and `φ⁻¹(𝓙) 𝒪_W = 𝓘 𝓘'` for some finite type
quasi-coherent sheaf of ideals `𝓘' ⊆ 𝒪_W`.

## Main results

* `fittingIdeal_zero_eq_top_of_subsingleton`: the zeroth Fitting ideal of the zero module is
  the unit ideal.
* `AlgebraicGeometry.Space.disjoint_idealZeroLocus_fittingIdeal_zero`: the zeroth Fitting
  ideal of the direct image of the structure sheaf along a finite morphism is the unit ideal
  away from the image of the morphism.
* `AlgebraicGeometry.Space.isPullback_graphPiece`: for `φ = π ∘ j` with `j` an open immersion,
  the piece of `W ×_X Z` over the graph of `j` is `W ×_Y Z`.
* `AlgebraicGeometry.Space.exists_isFiniteTypeQuasicoherentIdeal_chartSectionsIdeal_eq_mul`: the
  construction of Stacks 087B, with its conclusion read on the affine charts of `W`.
* `Space.exists_isFiniteTypeQuasicoherentIdeal_pullbackIdealSubsheaf_eq_idealSmul`:
  **Stacks 087B**, granted Stacks 07VR.
* `Space.exists_isFinitePresentation_preimageClosedSubspace_eq_sumClosedSubspaces`:
  Stacks 087B for finitely presented closed subspaces, granted Stacks 07VR.

## Implementation notes

The proof is the source's.  Zariski's main theorem with a finitely presented compactification
(Stacks 0874) factors `φ` as a quasi-compact open immersion `j : W ⟶ Y` followed by a finite
morphism of finite presentation `π : Y ⟶ X`.  The closed subspace `V(𝓘) ⊆ W ≅ j(W)` and the
empty closed subspace on `π⁻¹(U)` extend to a finitely presented closed subspace `Z ⊆ Y` with
`Z ∩ j(W) = V(𝓘)` and `Z ∩ π⁻¹(U) = ∅`; the source does this with Stacks 0853, and the library's
form of that step works directly with finitely presented closed subspaces
(`AlgebraicGeometry.Space.exists_closedSubspace_extension_disjoint`).  Then `τ : Z ⟶ X` is finite
and of finite presentation, `𝓙 = Fit_0(τ_* 𝒪_Z)`, and the graph of `j` over `π` splits
`W ×_X Z` into the piece `W ×_Y Z = V(𝓘)` and a complementary piece `Z'` finite and of finite
presentation over `W`; `𝓘' = Fit_0((Z' ⟶ W)_* 𝒪)`, and the identity
`φ⁻¹(𝓙) 𝒪_W = 𝓘 𝓘'` is
`AlgebraicGeometry.Space.pullbackIdealSubsheaf_fittingIdeal_eq_idealSmul`.

The inverse-image ideal `φ⁻¹(𝓙) 𝒪_W` is
`AlgebraicGeometry.Space.pullbackIdealSubsheaf`, which is defined for representable morphisms;
a separated étale morphism is representable by Stacks 0418, and the statement names that
proof.

## References

* [Stacks Project, Tag 087B](https://stacks.math.columbia.edu/tag/087B)
* [Stacks Project, Tag 0874](https://stacks.math.columbia.edu/tag/0874)
* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 0610](https://stacks.math.columbia.edu/tag/0610)
* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

/-- The zeroth Fitting ideal of the zero module is the unit ideal. -/
theorem fittingIdeal_zero_eq_top_of_subsingleton {C : Type u} [CommRing C] {M : Type u}
    [AddCommGroup M] [Module C M] [Module.Finite C M] [Subsingleton M] :
    fittingIdeal (R := C) (M := M) 0 = ⊤ := by
  simpa using (fittingIdeal_basic_properties.{u, u, u, u} (R := C) (M := M)).1 0
    ⟨Fin.elim0, Subsingleton.elim _ _⟩

/-- The lift of a monomorphism through a subfunctor equal to its range is an isomorphism. -/
private theorem CategoryTheory.Subfunctor.isIso_lift_of_range_eq {C : Type*} [Category C]
    {F F' : C ⥤ Type u} {j : F' ⟶ F} [Mono j] {V : Subfunctor F}
    (h : Subfunctor.range j = V) : IsIso (Subfunctor.lift j h.le) := by
  subst h
  exact inferInstanceAs (IsIso (Subfunctor.toRange j))

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The zeroth Fitting ideal of a finite direct image is the unit ideal away from the image.**
For a finite morphism `τ : Z ⟶ X` and an open subspace `U ⊆ X` whose points avoid the image of
`τ`, the zero locus of `Fit_0(τ_* 𝒪_Z)` avoids `U`: over an affine étale chart of `U` the fibre
product with `Z` is empty, so the sections of `τ_* 𝒪_Z` there vanish and their zeroth Fitting
ideal is the unit ideal. -/
theorem disjoint_idealZeroLocus_fittingIdeal_zero {X Z : AlgebraicSpaces B S hS} (τ : Z ⟶ X)
    (hτ : IsFinite B S hS τ.hom) (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (h : Disjoint (Set.range (pointsMap B S hS Z.1 τ.hom)) (subspacePointSet B S hS X.1 U)) :
    Disjoint (idealZeroLocus B S hS X (fittingIdeal B S hS X.1 X.2 (finiteDirectImageUnit τ hτ) 0))
      (subspacePointSet B S hS X.1 U) := by
  rw [Set.disjoint_right]
  rintro x ⟨u, rfl⟩ hx
  obtain ⟨Wc, b, hWaff, hbet, w, hw⟩ :=
    exists_affine_etale_chart_at_point B S hS U.toFunctor hU.1 u
  let V : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk (b ≫ U.ι),
    (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition.comp_mem _ _ hbet
      (presheaf_etale_of_isOpenImmersion B S hS hU.2)⟩
  have hVaff : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V) :=
    hWaff
  set hτr := relativelyRepresentable_hom_of_isFinite B S hS τ hτ
  -- The chart of `Z` over `V` is empty.
  have hempty : IsEmpty ((BigFppfOver.toScheme B S hS).obj (hτr.pullback V.1.hom)) := by
    refine ⟨fun a => ?_⟩
    obtain ⟨p, -⟩ := surjective_pointsToScheme B S hS _ a
    have hz : pointsMap B S hS Z.1 τ.hom
        (pointsMap B S hS _ (hτr.fst V.1.hom) p) ∈ subspacePointSet B S hS X.1 U := by
      rw [← pointsMap_comp_apply, hτr.w, pointsMap_comp_apply]
      show pointsMap B S hS _ (b ≫ U.ι) _ ∈ _
      rw [pointsMap_comp_apply]
      exact ⟨_, rfl⟩
    exact Set.disjoint_left.1 h ⟨_, rfl⟩ hz
  have hJ : (fittingIdeal B S hS X.1 X.2 (finiteDirectImageUnit τ hτ) 0).obj (op V) = ⊤ := by
    rw [fittingIdeal_obj_eq_fittingIdealOnChart _
      (isCartesianOnAffineCharts_finiteDirectImageUnit τ hτ)
      (fun A hA => moduleFinite_sections_finiteDirectImageUnit τ hτ A hA) 0 hVaff]
    have := moduleFinite_sections_finiteDirectImageUnit τ hτ V hVaff
    have : Subsingleton ((finiteDirectImageUnit τ hτ).val.obj (op V)) :=
      (inferInstance : Subsingleton
        Γ((BigFppfOver.toScheme B S hS).obj (hτr.pullback V.1.hom), ⊤))
    show _root_.fittingIdeal (R := chartRing B S hS X.1 X.2 V)
      (M := (finiteDirectImageUnit τ hτ).val.obj (op V)) ((0 : ℕ) : ℤ) = ⊤
    rw [Nat.cast_zero]
    exact fittingIdeal_zero_eq_top_of_subsingleton
  refine (mem_idealZeroLocus_iff B S hS X _ _).1 hx V hJ ⟨w, ?_⟩
  show pointsMap B S hS _ (b ≫ U.ι) w = _
  rw [pointsMap_comp_apply, hw]

/-! ### The piece of `W ×_X Z` cut out by the graph -/

section GraphPiece

variable {W Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
  (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
  (j : W ⟶ Y) (π : Y ⟶ X) (φ : W ⟶ X) (hfac : j ≫ π = φ) (Z : Subfunctor Y)

/-- The canonical morphism `W ×_X Z ⟶ W ×_X Y` induced by the inclusion `Z ⊆ Y`, for
`φ = π ∘ j`. -/
noncomputable def fibreToGraphTarget :
    pullback φ (Z.ι ≫ π) ⟶ pullback (j ≫ π) π :=
  pullback.map φ (Z.ι ≫ π) (j ≫ π) π (𝟙 W) Z.ι (𝟙 X) (by simp [hfac]) (by simp)

/-- The set of points of `W ×_X Z` lying over the graph of `j` over `π`. -/
abbrev graphPoints : Set (points B S hS (pullback φ (Z.ι ≫ π))) :=
  pointsMap B S hS _ (fibreToGraphTarget j π φ hfac Z) ⁻¹'
    Set.range (pointsMap B S hS W (graph B S hS j π))

include hW hY hX in
/-- **The piece of `W ×_X Z` over the graph of `j` is `W ×_Y Z`.**  For `φ = π ∘ j` with `j` an
open immersion, the open subspace of `W ×_X Z` cut out by the points over the graph of `j` over
`π` is the base change of `Z ⊆ Y` along `j`. -/
theorem isPullback_graphPiece (hj : IsOpenImmersion B S hS j) (hφ : IsEtale B S hS φ) :
    IsPullback ((openSubspaceOfPoints B S hS _ (graphPoints j π φ hfac Z)).ι ≫
        pullback.snd φ (Z.ι ≫ π))
      ((openSubspaceOfPoints B S hS _ (graphPoints j π φ hfac Z)).ι ≫
        pullback.fst φ (Z.ι ≫ π)) Z.ι j := by
  set m := fibreToGraphTarget j π φ hfac Z
  set Γ := graph B S hS j π
  set G := openSubspaceOfPoints B S hS _ (graphPoints j π φ hfac Z)
  have hm₁ : m ≫ pullback.fst (j ≫ π) π = pullback.fst φ (Z.ι ≫ π) := by
    simp [m, fibreToGraphTarget]
  have hm₂ : m ≫ pullback.snd (j ≫ π) π = pullback.snd φ (Z.ι ≫ π) ≫ Z.ι := by
    simp [m, fibreToGraphTarget]
  -- `W ×_X Z` is the base change of `Z ⊆ Y` along `W ×_X Y ⟶ Y`.
  have sqA : IsPullback (pullback.snd (j ≫ π) π) (pullback.fst (j ≫ π) π) π φ := by
    rw [← hfac]
    exact (IsPullback.of_hasPullback (j ≫ π) π).flip
  have sqC : IsPullback (pullback.snd φ (Z.ι ≫ π)) m Z.ι (pullback.snd (j ≫ π) π) := by
    refine IsPullback.of_bot ?_ hm₂.symm sqA
    rw [hm₁]
    exact (IsPullback.of_hasPullback φ (Z.ι ≫ π)).flip
  -- The piece over the graph is the inverse image of the range of the graph.
  have hrange : Subfunctor.range Γ =
      openSubspaceOfPoints B S hS _ (Set.range (pointsMap B S hS W Γ)) :=
    range_eq_openSubspaceOfPoints_of_isOpenImmersion_of_isAlgebraicSpace B S hS hW
      (isOpenImmersion_graph B S hS hW hY hX j π (isEtale_of_isOpenImmersion B S hS hj)
        (by rwa [hfac]))
  have hG : G = (Subfunctor.range Γ).preimage m := by
    rw [hrange, preimage_openSubspaceOfPoints]
  have : Mono Γ := mono_graph B S hS j π
  have sqE : IsPullback (inv (Subfunctor.toRange Γ)) (Subfunctor.range Γ).ι Γ (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsIso.inv_comp_eq, Subfunctor.toRange_ι]⟩
  have sqD' := (isPullback_lift_of_eq_preimage m hG).paste_horiz sqE
  rw [Category.comp_id] at sqD'
  have hg : (Subfunctor.lift (G.ι ≫ m) (by
        rw [hG, Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff]) ≫
        inv (Subfunctor.toRange Γ)) = G.ι ≫ pullback.fst φ (Z.ι ≫ π) := by
    rw [← Category.comp_id (Subfunctor.lift _ _ ≫ _), ← graph_comp_fst B S hS j π,
      ← Category.assoc, sqD'.w, Category.assoc, hm₁]
  have sq := sqD'.flip.paste_horiz sqC
  rwa [graph_comp_snd, hg] at sq

end GraphPiece

/-! ### Stacks 087B -/

/-- A closed subspace is of finite presentation exactly when its ideal is of finite type. -/
private theorem isFinitePresentation_iff_isFiniteTypeOnSite_definingIdealSheaf
    {V : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS V.1) :
    IsFinitePresentation B S hS Z.1.ι ↔
      SheafOfModules.IsFiniteTypeOnSite (definingIdealSheaf B S hS V Z).toSheafOfModules :=
  isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf B S hS
    (ObjectProperty.homMk Z.1.ι : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ V) Z.2.2

/-- A finite type quasi-coherent ideal is the ideal of a closed subspace of finite presentation. -/
private theorem exists_isFinitePresentation_definingIdealSheaf_eq {W : AlgebraicSpaces B S hS}
    (I : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule)
    (hI : IsFiniteTypeQuasicoherentIdeal B S hS W I) :
    ∃ Z : ClosedSubspaces B S hS W.1,
      IsFinitePresentation B S hS Z.1.ι ∧ definingIdealSheaf B S hS W Z = I := by
  obtain ⟨Z, hZ⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS W I hI.1
  exact ⟨Z, (isFinitePresentation_iff_isFiniteTypeOnSite_definingIdealSheaf Z).2
    (hZ ▸ hI.2), hZ⟩

/-- **Extending a closed subspace across a quasi-compact open immersion.**  For an open
immersion `j : W ⟶ Y` of quasi-compact algebraic spaces with `Y` quasi-separated, a quasi-compact
open subspace `U ⊆ Y` and a closed subspace `Z_W ⊆ W` of finite presentation disjoint from
`j⁻¹(U)`, there is a closed subspace `Z ⊆ Y` of finite presentation disjoint from `U` with
`j⁻¹(Z) = Z_W`. -/
private theorem exists_closedSubspace_preimage_eq_of_isOpenImmersion
    (hZ : B.Contains (⊤_ Scheme.{u})) {W : AlgebraicSpaces B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y) (hWqc : IsQuasiCompactSpace B S hS W.1)
    (j : W.1 ⟶ Y) (hj : IsOpenImmersion B S hS j) (U : Subfunctor Y)
    (hU : IsOpenSubspace B S hS U) (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (ZW : ClosedSubspaces B S hS W.1) (hZWfp : IsFinitePresentation B S hS ZW.1.ι)
    (hZWU : Disjoint (subspacePointSet B S hS W.1 ZW.1)
      (subspacePointSet B S hS W.1 (U.preimage j))) :
    ∃ Z : Subfunctor Y, IsClosedSubspace B S hS Z ∧ IsFinitePresentation B S hS Z.ι ∧
      Disjoint (subspacePointSet B S hS Y U) (subspacePointSet B S hS Y Z) ∧
        Z.preimage j = ZW.1 := by
  set Vj : Subfunctor Y := openSubspaceOfPoints B S hS Y (Set.range (pointsMap B S hS W.1 j))
  have hVj : IsOpenSubspace B S hS Vj := isOpenSubspace_openSubspaceOfPoints B S hS hY _
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS j hj)
  have hVjr : Subfunctor.range j = Vj :=
    range_eq_openSubspaceOfPoints_of_isOpenImmersion_of_isAlgebraicSpace B S hS W.2 hj
  let jV : W.1 ⟶ Vj.toFunctor := Subfunctor.lift j hVjr.le
  have : Mono j := mono_of_isOpenImmersion B S hS j hj
  have hjV : IsIso jV := Subfunctor.isIso_lift_of_range_eq hVjr
  have hjVι : jV ≫ Vj.ι = j := Subfunctor.lift_ι _ _
  have hVjqc : IsQuasiCompactSpace B S hS Vj.toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (asIso jV) hWqc
  set Z' : Subfunctor Vj.toFunctor := ZW.1.preimage (inv jV) with hZ'def
  have hZ'c : IsClosedSubspace B S hS Z' :=
    isClosedSubspace_preimage B S hS (inv jV) ZW.1 W.2 hVj.1 ZW.2
  have hZ'fp : IsFinitePresentation B S hS Z'.ι :=
    isFinitePresentation_of_isPullback B S hS hZ'c.1 ZW.2.1 hVj.1 W.2
      (Subfunctor.isPullback_preimage (inv jV) ZW.1) hZWfp
  have hWU : Disjoint (subspacePointSet B S hS Vj.toFunctor (U.preimage Vj.ι))
      (subspacePointSet B S hS Vj.toFunctor Z') := by
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    change y ∈ Set.range (pointsMap B S hS _ (U.preimage Vj.ι).ι) at hy₁
    change y ∈ Set.range (pointsMap B S hS _ Z'.ι) at hy₂
    rw [range_pointsMap_preimage_ι, Set.mem_preimage] at hy₁
    rw [hZ'def, range_pointsMap_preimage_ι, Set.mem_preimage] at hy₂
    set w := pointsMap B S hS _ (inv jV) y
    have hyw : pointsMap B S hS _ jV w = y := by
      rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id]
      rfl
    refine Set.disjoint_left.1 hZWU hy₂ ?_
    show w ∈ Set.range (pointsMap B S hS _ (U.preimage j).ι)
    rwa [range_pointsMap_preimage_ι, Set.mem_preimage, ← hjVι, pointsMap_comp_apply, hyw]
  obtain ⟨Z, hZc, hZfp, hZdisj, hZW⟩ := exists_closedSubspace_extension_disjoint hZ
    (X := ⟨Y, hY⟩) hYqc hYqs U Vj hU hVj hUqc hVjqc Z' hZ'c hZ'fp hWU
  refine ⟨Z, hZc, hZfp, hZdisj, ?_⟩
  rw [← hjVι, Subfunctor.preimage_comp, hZW, hZ'def, ← Subfunctor.preimage_comp,
    IsIso.hom_inv_id, Subfunctor.preimage_id]

/-- **A clopen piece of a finite fibre product is finite.**  For `τ : Z ⟶ X` finite and of finite
presentation and `T` a clopen set of points of `W ×_X Z`, the projection to `W` of the open
subspace cut out by `T` is finite and of finite presentation. -/
private theorem isFinite_fibrePieceHom_of_isClosed {X W Z : AlgebraicSpaces B S hS} (φ : W ⟶ X)
    (τ : Z ⟶ X) (hτ : IsFinite B S hS τ.hom) (hτfp : IsFinitePresentation B S hS τ.hom)
    (T : Set (points B S hS (pullback φ.hom τ.hom))) (hTo : IsOpen T) (hTc : IsClosed T) :
    IsFinite B S hS (fibrePieceHom φ τ T hTo).hom ∧
      IsFinitePresentation B S hS (fibrePieceHom φ τ T hTo).hom := by
  have hP := isAlgebraicSpace_pullback_hom φ τ
  have hc := isClosedSubspace_openSubspaceOfPoints B S hS hP T hTo hTc
  have hpb := (IsPullback.of_hasPullback φ.hom τ.hom).flip
  exact ⟨isFinite_comp B S hS (isFinite_of_isClosedImmersion B S hS _ hc.2)
      (isFinite_of_isPullback B S hS hpb hτ),
    isFinitePresentation_comp B S hS hc.1 hP W.2 _ _
      ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS
        (isOpenSubspace_openSubspaceOfPoints B S hS hP T hTo).2,
        isQuasiCompact_of_isClosedImmersion' B S hS hc.2,
        isQuasiSeparated_of_mono B S hS _ inferInstance⟩
      (isFinitePresentation_of_isPullback B S hS hP Z.2 W.2 X.2 hpb hτfp)⟩

/-- **The Fitting ideal of a finite direct image, restricted along `φ = π ∘ j`.**  For
`φ = π ∘ j` étale with `j` an open immersion and `π` finite, and a closed subspace `Z ⊆ Y` with
`Z ∩ W = Z_W` and `τ : Z ⟶ X` finite and of finite presentation, there is a finite type
quasi-coherent sheaf of ideals `𝓘' ⊆ 𝒪_W` such that over every affine étale chart `V` of `W` the
sections of `Fit_0(τ_* 𝒪_Z)` over `V ⟶ W ⟶ X` are the product of the sections of the ideal of
`Z_W` and of `𝓘'` over `V`. -/
private theorem exists_isFiniteTypeQuasicoherentIdeal_chartSectionsIdeal_fittingIdeal_eq_mul
    {X W : AlgebraicSpaces B S hS} (φ : W ⟶ X) (hφet : IsEtale B S hS φ.hom)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (j : W.1 ⟶ Y)
    (hj : IsOpenImmersion B S hS j) (π : Y ⟶ X.1) (hπ : IsFinite B S hS π)
    (hfac : j ≫ π = φ.hom) (Z : Subfunctor Y) (hZc : IsClosedSubspace B S hS Z)
    (ZW : ClosedSubspaces B S hS W.1) (hZW : Z.preimage j = ZW.1)
    (hτ : IsFinite B S hS (Z.ι ≫ π)) (hτfp : IsFinitePresentation B S hS (Z.ι ≫ π)) :
    ∃ I' : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule,
      IsFiniteTypeQuasicoherentIdeal B S hS W I' ∧
        ∀ V : SmallEtale B S hS W.1,
          IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V) →
            chartSectionsIdeal B S hS W (etaleIdealRestrict B S hS φ hφet
              (fittingIdeal B S hS X.1 X.2 (finiteDirectImageUnit
                (ObjectProperty.homMk (Z.ι ≫ π) :
                  (⟨Z.toFunctor, hZc.1⟩ : AlgebraicSpaces B S hS) ⟶ X) hτ) 0)) V =
              chartSectionsIdeal B S hS W (definingIdealSheaf B S hS W ZW) V *
                chartSectionsIdeal B S hS W I' V := by
  let Zsp : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZc.1⟩
  let τ : Zsp ⟶ X := ObjectProperty.homMk (Z.ι ≫ π)
  -- The graph of `j` over `π` splits `W ×_X Z`.
  set T := graphPoints j π φ.hom hfac Z
  have hP : IsAlgebraicSpace B S hS (pullback φ.hom τ.hom) := isAlgebraicSpace_pullback_hom φ τ
  have hjet : IsEtale B S hS j := isEtale_of_isOpenImmersion B S hS hj
  have hT : IsClopen T :=
    (isClopen_range_pointsMap_graph B S hS W.2 hY X.2 j π hjet (by rwa [hfac])
      (isSeparated_of_isFinite B S hS π hY X.2 hπ)).preimage (continuous_pointsMap B S hS _)
  have sq := isPullback_graphPiece W.2 hY X.2 j π φ.hom hfac Z hj hφet
  -- The piece over the graph is `Z_W`.
  have he₁ : IsClosedImmersion B S hS (fibrePieceHom φ τ T hT.isOpen).hom :=
    (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback sq hZc.2
  let jsp : W ⟶ (⟨Y, hY⟩ : AlgebraicSpaces B S hS) := ObjectProperty.homMk j
  have hsqA := isPullback_homMk B S hS hZc.1 W.2 hY
    (isOpenSubspace_openSubspaceOfPoints B S hS hP T hT.isOpen).1 sq
  have hker : kernelIdealSheaf B S hS (fibrePieceHom φ τ T hT.isOpen) =
      definingIdealSheaf B S hS W ZW := by
    have h₁ : kernelIdealSheaf B S hS (fibrePieceHom φ τ T hT.isOpen) =
        etaleRestrictionDefiningIdealSheaf B S hS jsp hjet ⟨Z, hZc⟩ := by
      refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun V => ?_)
      obtain ⟨V⟩ := V
      exact kernelIdealSheaf_baseChange_obj B S hS _ _ _ _ hsqA hjet V
    rw [h₁, etaleRestrictionDefiningIdealSheaf_eq]
    congr 1
    exact Subtype.ext hZW
  obtain ⟨he₂, he₂fp⟩ := isFinite_fibrePieceHom_of_isClosed φ τ hτ hτfp Tᶜ
    hT.isClosed.isOpen_compl hT.isOpen.isClosed_compl
  refine ⟨_, isFiniteTypeQuasicoherentIdeal_fittingIdeal W _
    (isQuasicoherentOnSite_smallBaseChangeModulePushforward B S hS _ he₂ _
      (SheafOfModules.isQuasicoherentOnSite_unit _))
    (fun A hA => moduleFinitePresentation_sections_finiteDirectImageUnit _ he₂ he₂fp A hA) 0,
    fun V hV => ?_⟩
  rw [← hker]
  exact chartSectionsIdeal_etaleIdealRestrict_fittingIdeal_eq_mul φ hφet τ hτ T hT he₁ he₂ V hV

/-- **The construction of Stacks 087B, on the affine charts.**  In the situation of Stacks 087B
there are finite type quasi-coherent sheaves of ideals `𝓙 ⊆ 𝒪_X` with `V(𝓙) ∩ U = ∅` and
`𝓘' ⊆ 𝒪_W` such that over every affine étale chart `V` of `W` the sections of `𝓙` over
`V ⟶ W ⟶ X` are the product of the sections of `𝓘` and of `𝓘'` over `V`.

This is the form of the conclusion of Stacks 087B which the proof establishes; Stacks 087B itself,
`AlgebraicGeometry.Space.exists_isFiniteTypeQuasicoherentIdeal_pullbackIdealSubsheaf_eq_idealSmul`,
and its form for closed subspaces,
`AlgebraicGeometry.Space.exists_isFinitePresentation_preimageClosedSubspace_eq_sumClosedSubspaces`,
are read off from it. -/
theorem exists_isFiniteTypeQuasicoherentIdeal_chartSectionsIdeal_eq_mul
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ s : IntegralFiniteSystem B S hS g,
        letI := s.indexPreorder
        ∀ (i j : s.indexType) (h : i ≤ j),
          IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op))
    {X W : AlgebraicSpaces B S hS} (hXqc : IsQuasiCompactSpace B S hS X.1)
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
    exists_isOpenImmersion_isFinitePresentation_of_isQuasiFinite h07VR φ.hom W.2 X.2
      ⟨isLocallyQuasiFinite_of_isEtale' B S hS hφet, hφqc⟩ hφsep hXqc hXqs
      (isLocallyOfFinitePresentation_of_isEtale B S hS hφet)
  have hYqc : IsQuasiCompactSpace B S hS Y :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS X.2 hXqc hπfp.2.1
  have hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hY hXqs hπfp.2.2
  -- The closed subspace `V(𝓘) ⊆ W`, of finite presentation by Stacks 084Q.
  obtain ⟨ZI, hZIfp, hZI⟩ := exists_isFinitePresentation_definingIdealSheaf_eq I hI
  have hUY : IsOpenSubspace B S hS (U.preimage π) := isOpenSubspace_preimage B S hS π U X.2 hY hU
  have hUYqc : IsQuasiCompactSpace B S hS (U.preimage π).toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (Subfunctor.isPullback_preimage π U).isoPullback.symm
      (hπfp.2.1 U.toFunctor hU.1 hUqc U.ι)
  rw [← hZI, ← range_pointsMap_ι_eq_idealZeroLocus, ← hfac, Subfunctor.preimage_comp] at hIU
  -- Stacks 0853 in the form of finitely presented closed subspaces: `Z ⊆ Y`.
  obtain ⟨Z, hZc, hZfp, hZdisj, hZW⟩ := exists_closedSubspace_preimage_eq_of_isOpenImmersion hZ
    hY hYqc hYqs hWqc j hj _ hUY hUYqc ZI hZIfp hIU
  -- `τ : Z ⟶ X`, finite and of finite presentation, with image avoiding `U`.
  let τ : (⟨Z.toFunctor, hZc.1⟩ : AlgebraicSpaces B S hS) ⟶ X := ObjectProperty.homMk (Z.ι ≫ π)
  have hτ : IsFinite B S hS τ.hom :=
    isFinite_comp B S hS (isFinite_of_isClosedImmersion B S hS Z.ι hZc.2) hπ
  have hτfp : IsFinitePresentation B S hS τ.hom :=
    isFinitePresentation_comp B S hS hZc.1 hY X.2 Z.ι π hZfp hπfp
  have hτU : Disjoint (Set.range (pointsMap B S hS Z.toFunctor τ.hom))
      (subspacePointSet B S hS X.1 U) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, rfl⟩ hzU
    refine Set.disjoint_left.1 hZdisj ?_ (⟨z, rfl⟩ : pointsMap B S hS _ Z.ι z ∈ Set.range _)
    show _ ∈ Set.range (pointsMap B S hS _ (U.preimage π).ι)
    rwa [range_pointsMap_preimage_ι, Set.mem_preimage, ← pointsMap_comp_apply]
  obtain ⟨I', hI', hchart⟩ :=
    exists_isFiniteTypeQuasicoherentIdeal_chartSectionsIdeal_fittingIdeal_eq_mul φ hφet hY j hj π
      hπ hfac Z hZc ZI hZW hτ hτfp
  -- `𝓙 = Fit_0(τ_* 𝒪_Z)`.
  refine ⟨fittingIdeal B S hS X.1 X.2 (finiteDirectImageUnit τ hτ) 0,
    isFiniteTypeQuasicoherentIdeal_fittingIdeal X _
      (isQuasicoherentOnSite_smallBaseChangeModulePushforward B S hS τ hτ _
        (SheafOfModules.isQuasicoherentOnSite_unit _))
      (fun A hA => moduleFinitePresentation_sections_finiteDirectImageUnit τ hτ hτfp A hA) 0,
    disjoint_idealZeroLocus_fittingIdeal_zero τ hτ U hU hτU, I', hI', fun V hV => hZI ▸ hchart V hV⟩


/- The hypothesis `h07VR` below is the statement of Stacks 07VR, which enters through Stacks 0874.
It is a theorem of this library, `exists_integralFiniteSystem_of_isFinite`; supplying it gives
Stacks 087B with no hypotheses beyond the source's, namely
`exists_isFiniteTypeQuasicoherentIdeal_disjoint_pullbackIdealSubsheaf_eq_idealSmul` in
`FiniteTypeIdealEtaleFittingDescentUnconditional.lean`. -/
/-- **Stacks 087B, granted Stacks 07VR.**  Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`, let `φ : W ⟶ X` be a quasi-compact separated étale
morphism, let `U ⊆ X` be a quasi-compact open subspace and let `𝓘 ⊆ 𝒪_W` be a finite type
quasi-coherent sheaf of ideals with `V(𝓘) ∩ φ⁻¹(U) = ∅`.  Then there is a finite type
quasi-coherent sheaf of ideals `𝓙 ⊆ 𝒪_X` such that

1. `V(𝓙) ∩ U = ∅`, and
2. `φ⁻¹(𝓙) 𝒪_W = 𝓘 𝓘'` for some finite type quasi-coherent sheaf of ideals `𝓘' ⊆ 𝒪_W`.

The hypothesis `h07VR` is the statement of Stacks 07VR, through
which Stacks 0874 factors `φ`; see
`AlgebraicGeometry.Space.exists_isOpenImmersion_isFinitePresentation_of_isQuasiFinite`. -/
theorem exists_isFiniteTypeQuasicoherentIdeal_pullbackIdealSubsheaf_eq_idealSmul
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ s : IntegralFiniteSystem B S hS g,
        letI := s.indexPreorder
        ∀ (i j : s.indexType) (h : i ≤ j),
          IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op))
    {X W : AlgebraicSpaces B S hS} (hXqc : IsQuasiCompactSpace B S hS X.1)
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
            pullbackIdealSubsheaf B S hS φ
                (relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS φ.hom W.2 X.2
                  (isLocallyQuasiFinite_of_isEtale' B S hS hφet) hφsep) J =
              Stacks.Sites.idealSmul (O := structureSheaf B S hS W.1 W.2) I I' := by
  obtain ⟨J, hJ, hJU, I', hI', hchart⟩ :=
    exists_isFiniteTypeQuasicoherentIdeal_chartSectionsIdeal_eq_mul h07VR hXqc hXqs φ hφqc
      hφsep hφet U hU hUqc I hI hIU
  exact ⟨J, hJ, hJU, I', hI',
    (pullbackIdealSubsheaf_eq_etaleIdealRestrict B S hS φ hφet _ J).trans
      (eq_idealSmul_of_forall_isAffine _ _ _ hchart)⟩

/- This is the form of Stacks 087B in which the proof of Stacks 087C consumes it, stated for
finitely presented closed subspaces rather than for finite type quasi-coherent ideals.  It carries
the hypothesis `h07VR` exactly as
`exists_isFiniteTypeQuasicoherentIdeal_pullbackIdealSubsheaf_eq_idealSmul` above does. -/
/-- **Stacks 087B for finitely presented closed subspaces, granted Stacks 07VR.**  Let `X`
be a quasi-compact and quasi-separated algebraic space over `S`, let `φ : W ⟶ X` be a
quasi-compact separated étale morphism, let `U ⊆ X` be a quasi-compact open subspace and let
`Z_W ⊆ W` be a closed subspace of finite presentation disjoint from `φ⁻¹(U)`.  Then there are a
closed subspace `Z_X ⊆ X` of finite presentation disjoint from `U` and a closed subspace
`Z' ⊆ W` of finite presentation with `φ⁻¹(Z_X) = Z_W + Z'`.

Closed subspaces of finite presentation are the closed subspaces cut out by the finite type
quasi-coherent sheaves of ideals (Stacks 03MB and 084Q), inverse images of closed subspaces are
cut out by the inverse-image ideals, and sums are cut out by products (Stacks 083U), so this is
Stacks 087B read through those dictionaries. -/
theorem exists_isFinitePresentation_preimageClosedSubspace_eq_sumClosedSubspaces
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ s : IntegralFiniteSystem B S hS g,
        letI := s.indexPreorder
        ∀ (i j : s.indexType) (h : i ≤ j),
          IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op))
    (hZ : B.Contains (⊤_ Scheme.{u})) {X W : AlgebraicSpaces B S hS} (φ : W ⟶ X)
    (U : OpenSubspaces B S hS X.1) (hXqc : IsQuasiCompactSpace B S hS X.1)
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
      (isFinitePresentation_iff_isFiniteTypeOnSite_definingIdealSheaf ZW).1 hZWfp⟩
  have hIU : Disjoint (idealZeroLocus B S hS W (definingIdealSheaf B S hS W ZW))
      (subspacePointSet B S hS W.1 (U.1.preimage φ.hom)) := by
    rw [← range_pointsMap_ι_eq_idealZeroLocus]
    exact hZWU.symm
  obtain ⟨J, hJ, hJU, I', hI', hchart⟩ :=
    exists_isFiniteTypeQuasicoherentIdeal_chartSectionsIdeal_eq_mul h07VR hXqc hXqs φ hφqc
      hφsep hφet U.1 U.2 hUqc _ hI hIU
  obtain ⟨ZX, hZXfp, hZX⟩ := exists_isFinitePresentation_definingIdealSheaf_eq J hJ
  obtain ⟨Z', hZ'fp, hZ'⟩ := exists_isFinitePresentation_definingIdealSheaf_eq I' hI'
  refine ⟨ZX, hZXfp, ?_, Z', hZ'fp, ?_⟩
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

end AlgebraicGeometry.Space

end
