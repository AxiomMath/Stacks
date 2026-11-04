module

public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyIdealCoveringSubstantial
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyLimit

/-!
# The resolution property in a limit of quasi-compact quasi-separated schemes

[Stacks, Tag 0F8B] states that for `X = lim X i` a limit of a cofiltered diagram of
quasi-compact, quasi-separated schemes with affine transition morphisms, `X` has the resolution
property if and only if some `X i` does.  The direction from a stage to the limit is
`AlgebraicGeometry.hasResolutionProperty_of_isLimit`.  This file proves the direction from the
limit to a stage and the equivalence.

`AlgebraicGeometry.exists_hasResolutionProperty_of_isLimit` of
`StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyLimitStageNoetherian.lean` is the same
statement with Noetherian stages; it is kept because it is what
`AlgebraicGeometry.exists_isAffineHom_isNoetherian_hasResolutionProperty` consumes, and its
proof is the one adapted here.

## Main results

* `AlgebraicGeometry.exists_hasResolutionProperty_of_isLimit_of_quasiSeparated`: if the limit
  has the resolution property, so does some stage.
* `AlgebraicGeometry.hasResolutionProperty_iff_exists_of_isLimit`: [Stacks, Tag 0F8B].
* `AlgebraicGeometry.hasResolutionProperty_stage_of_quasiSeparated`: the same for a diagram
  indexed by the opposite of a directed preorder, which is the shape [Stacks, Tag 01ZA]
  produces.

## The argument

It is the source's, and it is the proof of the Noetherian case with Noetherianness removed from
the two places it was used.  Fix a stage `i₀` and a finite affine open covering of it; by
[Stacks, Tag 01PH] (2) ⟹ (4) the complement of each member is the vanishing locus of a sheaf of
ideals `J j` of finite type.  The resolution property of the limit resolves the pullback of
`J j` there, and `AlgebraicGeometry.exists_stage_isFiniteLocallyFree_hom_idealSheafData_of_isLimit`
descends the resolution to a stage `l j`.  On the limit the vanishing locus of the image of the
descended morphism is the complement of the pullback of the member of the covering
(`AlgebraicGeometry.coe_preimage_support_idealSheafDataOfHom_of_epi_factor`).

The two uses of Noetherianness in the Noetherian case are replaced as follows.

* [Stacks, Tag 01Z4] (2) asks the two compared opens to be quasi-compact.  There that came from
  every open of a Noetherian space being quasi-compact.  Here each is quasi-compact for its own
  reason: `D.map (e j) ⁻¹ᵁ V j` is the preimage of an affine open under an affine morphism, hence
  affine; and the complement of the vanishing locus of the image of `θ j` is quasi-compact by
  [Stacks, Tag 01PH] (4) ⟹ (2), `AlgebraicGeometry.isCompact_of_isFiniteType_idealSheafData`,
  the image being of finite type (`AlgebraicGeometry.isFiniteType_idealSheafDataOfHom`) because
  `E j` is finite locally free.
* The final appeal to [Stacks, Tag 0F89] is to
  `AlgebraicGeometry.hasResolutionProperty_of_coe_support_idealSheafDataOfHom`, the substantial
  direction of that tag at the source's generality, in place of its Noetherian form.

## References

* [Stacks Project, Tag 0F8B](https://stacks.math.columbia.edu/tag/0F8B)
* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

namespace AlgebraicGeometry

section

variable {K : Type u} [Category.{u} K] [IsCofiltered K] (D : K ⥤ Scheme.{u})
  [∀ {i j : K} (g : i ⟶ j), IsAffineHom (D.map g)] (c : Cone D)
  [∀ i : K, CompactSpace (D.obj i)] [∀ i : K, QuasiSeparatedSpace (D.obj i)]

include c in
/-- Let `c` be a limit cone over a cofiltered diagram `D` of quasi-compact, quasi-separated
schemes with affine transition morphisms.  If the limit `c.pt` has the resolution property then
so does some stage `D.obj i`. -/
theorem exists_hasResolutionProperty_of_isLimit_of_quasiSeparated (hc : IsLimit c)
    [HasResolutionProperty c.pt] :
    ∃ i, HasResolutionProperty (D.obj i) := by
  classical
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := K)
  -- a finite affine open covering of the stage `i₀`
  have hbasis : ∀ x : (D.obj i₀), ∃ W : (D.obj i₀).Opens, IsAffineOpen W ∧ x ∈ W := by
    intro x
    obtain ⟨-, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      (D.obj i₀).isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ ((⊤ : (D.obj i₀).Opens) : Set (D.obj i₀)) from trivial)
        (⊤ : (D.obj i₀).Opens).isOpen
    exact ⟨W, hW, hxW⟩
  choose W hWaff hWmem using hbasis
  obtain ⟨fs, hfs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : (D.obj i₀) => (W x : Set (D.obj i₀))) (fun x => (W x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hWmem x⟩)
  set ξ : Fin fs.card → (D.obj i₀) := fun j => (fs.equivFin.symm j).1 with hξ
  set V : Fin fs.card → (D.obj i₀).Opens := fun j => W (ξ j) with hV
  have hVaff : ∀ j, IsAffineOpen (V j) := fun j => hWaff (ξ j)
  have hVcov : ⨆ j, V j = ⊤ := by
    refine le_antisymm (iSup_le fun _ => le_top) fun x _ => ?_
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ fs, x ∈ (W y : Set (D.obj i₀)) := by
      simpa only [Set.mem_iUnion, Finset.mem_coe, exists_prop] using hfs (Set.mem_univ x)
    exact Opens.mem_iSup.mpr ⟨fs.equivFin ⟨y, hy⟩, by simpa [hV, hξ] using hxy⟩
  -- Tag 01PH (2) ⟹ (4): the complements are cut out by finite type sheaves of ideals
  choose J hJft hJsupp using fun j : Fin fs.card =>
    exists_isFiniteType_idealSheafData_support_eq_compl (V j) (hVaff j).isCompact
  have hJpow : ∀ j, (idealPow (J j) 1).IsFiniteType := fun j =>
    Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_idealPow (J j) 1 (hJft j)
  -- the descent step of Tag 0F8B
  choose l e E hE θ ε hεepi hεeq using fun j : Fin fs.card =>
    exists_stage_isFiniteLocallyFree_hom_idealSheafData_of_isLimit D c hc i₀ (J j) (hJpow j)
  have hEqc : ∀ j, (E j).IsQuasicoherent := fun j =>
    have _ := hE j
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree
      (R := (D.obj (l j)).ringCatSheaf) (E j)
  have hEft : ∀ j, (E j).IsFiniteType := fun j =>
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation
      (E j) (SheafOfModules.IsFiniteLocallyFree.isFinitePresentation (E j) (hE j))).2
  -- the vanishing locus of the descended morphism, read on the limit
  have hsupp0 : ∀ j, (c.π.app (l j)).base ⁻¹'
        ((@idealSheafDataOfHom _ (E j) (hEqc j) (θ j)).support : Set (D.obj (l j)))
      = (c.π.app i₀).base ⁻¹' (((J j).support : Set (D.obj i₀))) := fun j =>
    have _ := hEqc j
    have _ : Epi (ε j) := hεepi j
    coe_preimage_support_idealSheafDataOfHom_of_epi_factor (c.π.app (l j)) (c.π.app i₀)
      (E j) (θ j) (J j) (ε j) (hεeq j)
  have hcone : ∀ j, c.π.app (l j) ⁻¹ᵁ (D.map (e j) ⁻¹ᵁ V j) = c.π.app i₀ ⁻¹ᵁ V j := fun j => by
    rw [← Scheme.Hom.comp_preimage, c.w (e j)]
  have hleft : ∀ j, c.π.app (l j) ⁻¹ᵁ
        ((@idealSheafDataOfHom _ (E j) (hEqc j) (θ j)).support.compl : (D.obj (l j)).Opens)
      = c.π.app i₀ ⁻¹ᵁ V j := fun j => by
    refine TopologicalSpace.Opens.ext ?_
    simp only [TopologicalSpace.Opens.map_coe, TopologicalSpace.Closeds.coe_compl,
      Set.preimage_compl, hsupp0 j, hJsupp j, compl_compl]
  -- quasi-compactness of the two opens being compared, without a Noetherian hypothesis
  have hcV : ∀ j, IsCompact (((D.map (e j) ⁻¹ᵁ V j) : Set (D.obj (l j)))) := fun j =>
    ((hVaff j).preimage (D.map (e j))).isCompact
  have hcI : ∀ j, IsCompact ((((@idealSheafDataOfHom _ (E j) (hEqc j) (θ j)).support.compl :
      (D.obj (l j)).Opens) : Set (D.obj (l j)))) := by
    intro j
    have _ := hEqc j
    have _ := hEft j
    refine isCompact_of_isFiniteType_idealSheafData _ _
      (isFiniteType_idealSheafDataOfHom (E j) (θ j)) ?_
    simp only [TopologicalSpace.Closeds.coe_compl, compl_compl]
  -- Tag 01Z4 (2): the two quasi-compact opens agree at a stage
  choose k t ht using fun j : Fin fs.card =>
    exists_map_preimage_eq_map_preimage D c hc (hcI j) (hcV j) ((hleft j).trans (hcone j).symm)
  -- one stage below all of them
  obtain ⟨kk, hkk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  have r : ∀ j, kk ⟶ k j := fun j =>
    (hkk (Finset.mem_image_of_mem _ (Finset.mem_univ j))).some
  -- Tag 01Z4: the covering becomes a covering at a stage
  have hcovlim : c.π.app kk ⁻¹ᵁ (⨆ j, D.map (r j ≫ t j ≫ e j) ⁻¹ᵁ V j) = ⊤ := by
    rw [Scheme.Hom.preimage_iSup]
    have hj : ∀ j, c.π.app kk ⁻¹ᵁ (D.map (r j ≫ t j ≫ e j) ⁻¹ᵁ V j) = c.π.app i₀ ⁻¹ᵁ V j :=
      fun j => by rw [← Scheme.Hom.comp_preimage, c.w (r j ≫ t j ≫ e j)]
    rw [iSup_congr hj, ← Scheme.Hom.preimage_iSup, hVcov]
    simp
  obtain ⟨kk', s, hs⟩ :=
    exists_map_eq_top D c hc (⨆ j, D.map (r j ≫ t j ≫ e j) ⁻¹ᵁ V j) hcovlim
  refine ⟨kk', ?_⟩
  have hpre : ∀ j, D.map (s ≫ r j ≫ t j) ⁻¹ᵁ
        ((@idealSheafDataOfHom _ (E j) (hEqc j) (θ j)).support.compl : (D.obj (l j)).Opens)
      = D.map (s ≫ r j ≫ t j ≫ e j) ⁻¹ᵁ V j := fun j => by
    simp only [D.map_comp, Scheme.Hom.comp_preimage]
    rw [ht j]
  refine hasResolutionProperty_of_coe_support_idealSheafDataOfHom
    (fun j => D.map (s ≫ r j ≫ t j ≫ e j) ⁻¹ᵁ V j)
    (fun j => (Scheme.Modules.pullback (D.map (s ≫ r j ≫ t j))).obj (E j))
    (fun j => SheafOfModules.IsFiniteLocallyFree.pullback_scheme
      (D.map (s ≫ r j ≫ t j)) (E j) (hE j))
    (fun j => (Scheme.Modules.pullback (D.map (s ≫ r j ≫ t j))).map (θ j) ≫
      (Scheme.Modules.pullbackUnitIso (D.map (s ≫ r j ≫ t j))).hom)
    (fun j => have _ := hEqc j; inferInstance)
    (fun j => (hVaff j).preimage (D.map (s ≫ r j ≫ t j ≫ e j))) ?_ ?_
  · rw [← hs, Scheme.Hom.preimage_iSup]
    refine iSup_congr fun j => ?_
    simp only [D.map_comp, Scheme.Hom.comp_preimage]
  · intro j
    have _ := hEqc j
    have hkey := coe_support_idealSheafDataOfHom_pullback_of_appLE
      (D.map (s ≫ r j ≫ t j)) (E j) (θ j) _
      (structureAppₗ_pullbackSectionHom (D.map (s ≫ r j ≫ t j)) (E j) (θ j))
    refine hkey.trans ?_
    have hcompl := congrArg (fun O : (D.obj kk').Opens => ((O : Set (D.obj kk')))ᶜ) (hpre j)
    simpa [TopologicalSpace.Closeds.coe_compl, Set.preimage_compl, Set.preimage_comp]
      using hcompl

include c in
/-- **[Stacks, Tag 0F8B].**  Let `c` be a limit cone over a cofiltered diagram `D` of
quasi-compact, quasi-separated schemes with affine transition morphisms.  The limit `c.pt` has
the resolution property if and only if some stage `D.obj i` has it. -/
@[stacks 0F8B]
theorem hasResolutionProperty_iff_exists_of_isLimit (hc : IsLimit c) :
    HasResolutionProperty c.pt ↔ ∃ i, HasResolutionProperty (D.obj i) :=
  ⟨fun _ => exists_hasResolutionProperty_of_isLimit_of_quasiSeparated D c hc,
    fun ⟨i, _⟩ => hasResolutionProperty_of_isLimit D c hc i⟩

end

/-- The direction from the limit to a stage of [Stacks, Tag 0F8B], for a diagram indexed by the
opposite of a directed preorder, which is the shape [Stacks, Tag 01ZA] produces.  This is
`AlgebraicGeometry.exists_hasResolutionProperty_of_isLimit_of_quasiSeparated` with the
quasi-compactness and quasi-separatedness of the stages, and the affineness of the transition
morphisms, taken as explicit hypotheses. -/
theorem hasResolutionProperty_stage_of_quasiSeparated {A : Type u} [Preorder A] [Nonempty A]
    [IsDirected A (· ≤ ·)] (D : Aᵒᵈ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (haff : ∀ {i j : Aᵒᵈ} (g : i ⟶ j), IsAffineHom (D.map g))
    (hcs : ∀ i, CompactSpace (D.obj i)) (hqs : ∀ i, QuasiSeparatedSpace (D.obj i))
    (hRP : HasResolutionProperty c.pt) :
    ∃ i, HasResolutionProperty (D.obj i) :=
  have _ : IsCofiltered Aᵒᵈ := inferInstance
  have _ : ∀ {i j : Aᵒᵈ} (g : i ⟶ j), IsAffineHom (D.map g) := fun g => haff g
  have _ : HasResolutionProperty c.pt := hRP
  exists_hasResolutionProperty_of_isLimit_of_quasiSeparated D c hc

end AlgebraicGeometry

end
