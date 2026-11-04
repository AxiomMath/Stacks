module

public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyLimitStage
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.ImageIdealPullback
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealCoveringResolutionNoetherianImage

/-!
# The resolution property descends to a Noetherian stage of a limit of schemes

[Stacks, Tag 0F8B] states that for `X = lim X i` a limit of a cofiltered diagram of
quasi-compact, quasi-separated schemes with affine transition morphisms, `X` has the resolution
property if and only if some `X i` does; that is
`AlgebraicGeometry.hasResolutionProperty_iff_exists_of_isLimit`.  This file proves the direction
from the limit to a stage when every stage is Noetherian, the shape in which
`AlgebraicGeometry.Scheme.exists_isLimit_affine_locallyOfFiniteType` of [Stacks, Tag 01ZA]
presents a scheme.

The proof is the source's.  Fix a stage `i₀` and a finite affine open covering of it; by
[Stacks, Tag 01PH] (2) ⟹ (4) the complement of each member is the vanishing locus of a sheaf of
ideals `J j` of finite type.  The resolution property of the limit resolves the pullback of
`J j` there, and `AlgebraicGeometry.exists_stage_isFiniteLocallyFree_hom_idealSheafData_of_isLimit`
descends the resolution to a stage `l j`: a finite locally free module `E j` with a morphism
`θ j : E j ⟶ 𝒪` whose pullback to the limit factors as an epimorphism onto the pullback of
`J j` followed by the pullback of the inclusion of `J j`.

What remains is to see that the vanishing locus of the image of `θ j` *is*, at a stage, the
complement of the pullback of the member of the covering.  On the limit the two agree:
`AlgebraicGeometry.coe_support_idealSheafDataOfHom_of_epi` removes the epimorphism and
`AlgebraicGeometry.coe_support_idealSheafDataOfHom_pullback` commutes the vanishing locus with
both pullbacks.  Every open of a Noetherian scheme is quasi-compact, so [Stacks, Tag 01Z4] (2)
(`AlgebraicGeometry.exists_map_preimage_eq_map_preimage`) makes the two opens agree at a stage
over `l j`, and [Stacks, Tag 01Z4] (`AlgebraicGeometry.exists_map_eq_top`) makes the pulled-back
covering a covering at a further stage.  There the hypotheses of the Noetherian case of
[Stacks, Tag 0F89] are met in the form
`AlgebraicGeometry.hasResolutionProperty_of_isNoetherian_of_coe_support_idealSheafDataOfHom`.

## Main results

* `AlgebraicGeometry.idealSheafDataOfHom_idealPow_one`: the image of the inclusion of a sheaf of
  ideals into the structure sheaf is that sheaf of ideals.
* `AlgebraicGeometry.coe_preimage_support_idealSheafDataOfHom_of_epi_factor`: the vanishing locus
  of a descended resolution, read on the limit.
* `AlgebraicGeometry.exists_hasResolutionProperty_of_isLimit`: the direction from the limit to a
  stage of [Stacks, Tag 0F8B], at Noetherian stages.
* `AlgebraicGeometry.hasResolutionProperty_stage`: the same for a diagram indexed by the opposite
  of a directed preorder, which is the shape [Stacks, Tag 01ZA] produces and the shape in which
  `AlgebraicGeometry.exists_isAffineHom_isNoetherian_hasResolutionProperty` consumes it.

## Implementation notes

The same statement at quasi-compact quasi-separated stages is
`AlgebraicGeometry.exists_hasResolutionProperty_of_isLimit_of_quasiSeparated` in
`StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyLimitStageQcqs.lean`.

Two auxiliary statements are deliberately phrased with the morphism to the structure sheaf as a
*variable* constrained by an equation rather than as the composite
`f^*φ ≫ pullbackUnitIso f`; the reason is the transparency obstruction recorded in
`StacksFrontier/AlgebraicGeometry/Properties/ExtendFiniteType/ImageIdealPullback.lean`.

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

variable {X : Scheme.{u}}

/-- A quasi-coherent sheaf of ideals is the image of a morphism to the structure sheaf as soon as
the values of that morphism over each affine open are exactly its sections there. -/
theorem idealSheafDataOfHom_eq_of_range (I : X.IdealSheafData) {A : X.Modules}
    [A.IsQuasicoherent] (φ : A ⟶ structureModule X)
    (h : ∀ (V : X.affineOpens) (y : Γ(X, V.1)),
      (∃ z : Γ(A, V.1), structureAppₗ φ V.1 z = y) ↔ y ∈ (I.ideal V : Ideal Γ(X, V.1))) :
    idealSheafDataOfHom A φ = I :=
  Scheme.IdealSheafData.ext (funext fun V => by ext y; exact h V y)

/-- The image of the inclusion of a sheaf of ideals into the structure sheaf is that sheaf of
ideals. -/
theorem idealSheafDataOfHom_idealPow_one (I : X.IdealSheafData) :
    idealSheafDataOfHom (idealPow I 1)
        (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I 1
          (structureModule X)).ι = I :=
  idealSheafDataOfHom_eq_of_range I _ fun V y => by
    constructor
    · rintro ⟨z, rfl⟩
      have hz := (obj_idealPow_affineOpen I 1 V).le z.2
      rwa [pow_one] at hz
    · exact fun hy => ⟨⟨y, (obj_idealPow_affineOpen I 1 V).ge (by rwa [pow_one])⟩, rfl⟩

/-- **The vanishing locus of a descended resolution, read on the limit.**  Suppose that over a
scheme `Z` the pullback of a morphism `θ : E ⟶ 𝒪_Y` out of a quasi-coherent module factors, as
an epimorphism followed by the pullback of the inclusion of a sheaf of ideals `I` on `Y'`.  Then
the preimage in `Z` of the vanishing locus of the image of `θ` is the preimage of the vanishing
locus of `I`. -/
theorem coe_preimage_support_idealSheafDataOfHom_of_epi_factor {Z Y Y' : Scheme.{u}}
    (f : Z ⟶ Y) (g : Z ⟶ Y') (E : Y.Modules) [E.IsQuasicoherent]
    (θ : E ⟶ structureModule Y) (I : Y'.IdealSheafData)
    (ε : (Scheme.Modules.pullback f).obj E ⟶
      (Scheme.Modules.pullback g).obj (idealPow I 1)) [Epi ε]
    (heq : (Scheme.Modules.pullback f).map θ ≫ (Scheme.Modules.pullbackUnitIso f).hom =
      ε ≫ (Scheme.Modules.pullback g).map
        (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I 1 (structureModule Y')).ι ≫
          (Scheme.Modules.pullbackUnitIso g).hom) :
    f.base ⁻¹' ((idealSheafDataOfHom E θ).support : Set Y)
      = g.base ⁻¹' ((I.support : Set Y')) :=
  have h1 := coe_support_idealSheafDataOfHom_pullback_of_appLE f E θ _
    (structureAppₗ_pullbackSectionHom f E θ)
  have h2 := coe_support_idealSheafDataOfHom_pullback_of_appLE g (idealPow I 1)
    (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I 1 (structureModule Y')).ι _
    (structureAppₗ_pullbackSectionHom g (idealPow I 1)
      (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I 1 (structureModule Y')).ι)
  h1.symm.trans (((coe_support_idealSheafDataOfHom_of_epi ε _ _ heq).trans h2).trans
    (congrArg (fun J : Y'.IdealSheafData => g.base ⁻¹' (J.support : Set Y'))
      (idealSheafDataOfHom_idealPow_one I)))

/-- The complement of the vanishing locus of a descended resolution, read on the limit: if the
vanishing locus of `I` is the complement of `V`, then the preimage in `Z` of the complement of the
vanishing locus of the image of `θ` is the preimage of `V`. -/
theorem preimage_compl_support_idealSheafDataOfHom_of_epi_factor {Z Y Y' : Scheme.{u}}
    (f : Z ⟶ Y) (g : Z ⟶ Y') (E : Y.Modules) [E.IsQuasicoherent]
    (θ : E ⟶ structureModule Y) (I : Y'.IdealSheafData) (V : Y'.Opens)
    (hI : (I.support : Set Y') = (V : Set Y')ᶜ)
    (ε : (Scheme.Modules.pullback f).obj E ⟶
      (Scheme.Modules.pullback g).obj (idealPow I 1)) [Epi ε]
    (heq : (Scheme.Modules.pullback f).map θ ≫ (Scheme.Modules.pullbackUnitIso f).hom =
      ε ≫ (Scheme.Modules.pullback g).map
        (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I 1 (structureModule Y')).ι ≫
          (Scheme.Modules.pullbackUnitIso g).hom) :
    f ⁻¹ᵁ ((idealSheafDataOfHom E θ).support.compl : Y.Opens) = g ⁻¹ᵁ V := by
  refine TopologicalSpace.Opens.ext ?_
  simp only [TopologicalSpace.Opens.map_coe, TopologicalSpace.Closeds.coe_compl,
    Set.preimage_compl, coe_preimage_support_idealSheafDataOfHom_of_epi_factor f g E θ I ε heq,
    hI, compl_compl]

/-- If the preimage under `f` of the complement of the vanishing locus of the image of `θ` is `W`,
then the vanishing locus of the image of the pullback of `θ` is the complement of `W`. -/
theorem coe_support_idealSheafDataOfHom_pullback_eq_compl {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    (E : Y.Modules) [E.IsQuasicoherent] (θ : E ⟶ structureModule Y) (W : Z.Opens)
    (h : f ⁻¹ᵁ ((idealSheafDataOfHom E θ).support.compl : Y.Opens) = W) :
    ((idealSheafDataOfHom ((Scheme.Modules.pullback f).obj E)
      ((Scheme.Modules.pullback f).map θ ≫ (Scheme.Modules.pullbackUnitIso f).hom)).support :
        Set Z) = (W : Set Z)ᶜ :=
  (coe_support_idealSheafDataOfHom_pullback_of_appLE f E θ _
    (structureAppₗ_pullbackSectionHom f E θ)).trans <| by
    simpa [TopologicalSpace.Closeds.coe_compl, Set.preimage_compl, Set.preimage_comp]
      using congrArg (fun O : Z.Opens => (O : Set Z)ᶜ) h

/-- A quasi-compact scheme has a finite covering by affine opens. -/
theorem exists_fin_isAffineOpen_iSup_eq_top (X : Scheme.{u}) [CompactSpace X] :
    ∃ (n : ℕ) (V : Fin n → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ := by
  have hbasis : ∀ x : X, ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W := by
    intro x
    obtain ⟨-, ⟨W, hW, rfl⟩, hxW, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((⊤ : X.Opens) : Set X) from trivial) (⊤ : X.Opens).isOpen
    exact ⟨W, hW, hxW⟩
  choose W hWaff hWmem using hbasis
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hWmem x⟩)
  refine ⟨t.card, fun j => W (t.equivFin.symm j).1, fun j => hWaff _,
    le_antisymm (iSup_le fun _ => le_top) fun x _ => ?_⟩
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, x ∈ (W y : Set X) := by
    simpa only [Set.mem_iUnion, Finset.mem_coe, exists_prop] using ht (Set.mem_univ x)
  exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

/-- The preimage in the cone point of a preimage along a transition morphism `t : k ⟶ i` is the
preimage along the projection to `i`. -/
private theorem preimage_cone_app_map_preimage {K : Type*} [Category K] {D : K ⥤ Scheme.{u}}
    (c : Cone D) {i k : K} (t : k ⟶ i) (V : (D.obj i).Opens) :
    c.π.app k ⁻¹ᵁ D.map t ⁻¹ᵁ V = c.π.app i ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, c.w t]

section

variable {K : Type u} [Category.{u} K] [IsCofiltered K] (D : K ⥤ Scheme.{u})
  [∀ {i j : K} (g : i ⟶ j), IsAffineHom (D.map g)] (c : Cone D)

include c in
/-- A finite open covering of a stage of a limit of quasi-compact schemes with affine transition
morphisms, pulled back along morphisms `t j : k ⟶ i` from one further stage, becomes a covering at
a stage below `k`. -/
theorem exists_map_iSup_preimage_eq_top (hc : IsLimit c) [∀ i, CompactSpace (D.obj i)]
    {i k : K} {n : ℕ} (V : Fin n → (D.obj i).Opens) (hV : ⨆ j, V j = ⊤) (t : Fin n → (k ⟶ i)) :
    ∃ (k' : K) (s : k' ⟶ k), ⨆ j, D.map (s ≫ t j) ⁻¹ᵁ V j = ⊤ := by
  have hlim : c.π.app k ⁻¹ᵁ (⨆ j, D.map (t j) ⁻¹ᵁ V j) = ⊤ := by
    rw [Scheme.Hom.preimage_iSup]
    rw [iSup_congr fun j => preimage_cone_app_map_preimage c (t j) (V j),
      ← Scheme.Hom.preimage_iSup, hV]
    simp
  obtain ⟨k', s, hs⟩ := exists_map_eq_top D c hc _ hlim
  refine ⟨k', s, ?_⟩
  rw [← hs, Scheme.Hom.preimage_iSup]
  exact iSup_congr fun j => by simp only [D.map_comp, Scheme.Hom.comp_preimage]

include c in
/-- **The direction from the limit to a stage of [Stacks, Tag 0F8B], at Noetherian stages.**
Let `c` be a limit cone over a cofiltered diagram `D` of Noetherian schemes with affine
transition morphisms.  If the limit `c.pt` has the resolution property then so does some stage
`D.obj i`. -/
theorem exists_hasResolutionProperty_of_isLimit (hc : IsLimit c)
    (hN : ∀ i, IsNoetherian (D.obj i)) [HasResolutionProperty c.pt] :
    ∃ i, HasResolutionProperty (D.obj i) := by
  classical
  have hcs : ∀ i, CompactSpace (D.obj i) := fun i => (hN i).toCompactSpace
  have hqs : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i =>
    have _ : IsLocallyNoetherian (D.obj i) := (hN i).toIsLocallyNoetherian
    IsLocallyNoetherian.quasiSeparatedSpace
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := K)
  obtain ⟨n, V, hVaff, hVcov⟩ := exists_fin_isAffineOpen_iSup_eq_top (D.obj i₀)
  -- Tag 01PH (2) ⟹ (4): the complements are cut out by finite type sheaves of ideals
  choose J hJft hJsupp using fun j : Fin n =>
    exists_isFiniteType_idealSheafData_support_eq_compl (V j) (hVaff j).isCompact
  have hJpow : ∀ j, (idealPow (J j) 1).IsFiniteType := fun j =>
    Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_idealPow (J j) 1 (hJft j)
  -- the descent step of Tag 0F8B
  choose l e E hE θ ε hεepi hεeq using fun j : Fin n =>
    exists_stage_isFiniteLocallyFree_hom_idealSheafData_of_isLimit D c hc i₀ (J j) (hJpow j)
  have hEqc : ∀ j, (E j).IsQuasicoherent := fun j =>
    have _ := hE j
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree
      (R := (D.obj (l j)).ringCatSheaf) (E j)
  have hleft : ∀ j, c.π.app (l j) ⁻¹ᵁ
        ((@idealSheafDataOfHom _ (E j) (hEqc j) (θ j)).support.compl : (D.obj (l j)).Opens)
      = c.π.app i₀ ⁻¹ᵁ V j := fun j =>
    have _ := hEqc j
    have _ : Epi (ε j) := hεepi j
    preimage_compl_support_idealSheafDataOfHom_of_epi_factor (c.π.app (l j)) (c.π.app i₀)
      (E j) (θ j) (J j) (V j) (hJsupp j) (ε j) (hεeq j)
  -- Tag 01Z4 (2): the two quasi-compact opens agree at a stage
  have hcompact : ∀ (i : K) (O : (D.obj i).Opens), IsCompact ((O : Set (D.obj i))) :=
    fun _ _ => NoetherianSpace.isCompact _
  choose k q hq using fun j : Fin n =>
    exists_map_preimage_eq_map_preimage D c hc (hcompact (l j) _) (hcompact (l j) _)
      ((hleft j).trans (preimage_cone_app_map_preimage c (e j) (V j)).symm)
  obtain ⟨kk, hkk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  have r : ∀ j, kk ⟶ k j := fun j =>
    (hkk (Finset.mem_image_of_mem _ (Finset.mem_univ j))).some
  -- Tag 01Z4: the covering becomes a covering at a stage
  obtain ⟨kk', s, hs⟩ := exists_map_iSup_preimage_eq_top D c hc V hVcov fun j => r j ≫ q j ≫ e j
  refine ⟨kk', hasResolutionProperty_of_isNoetherian_of_coe_support_idealSheafDataOfHom
    (fun j => D.map (s ≫ r j ≫ q j ≫ e j) ⁻¹ᵁ V j)
    (fun j => (Scheme.Modules.pullback (D.map (s ≫ r j ≫ q j))).obj (E j))
    (fun j => SheafOfModules.IsFiniteLocallyFree.pullback_scheme
      (D.map (s ≫ r j ≫ q j)) (E j) (hE j))
    (fun j => (Scheme.Modules.pullback (D.map (s ≫ r j ≫ q j))).map (θ j) ≫
      (Scheme.Modules.pullbackUnitIso (D.map (s ≫ r j ≫ q j))).hom)
    (fun j => have _ := hEqc j; inferInstance)
    (fun j => (hVaff j).preimage (D.map (s ≫ r j ≫ q j ≫ e j))) hs fun j => ?_⟩
  have _ := hEqc j
  refine coe_support_idealSheafDataOfHom_pullback_eq_compl _ (E j) (θ j) _ ?_
  simp only [D.map_comp, Scheme.Hom.comp_preimage]
  rw [hq j]

end

/-- **The direction from the limit to a stage of [Stacks, Tag 0F8B], at Noetherian stages**, in
the shape the reduction of
[Stacks, Tag 0F8C] to the Noetherian case produces. -/
theorem hasResolutionProperty_stage {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵈ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (haff : ∀ {i j : Iᵒᵈ} (g : i ⟶ j), IsAffineHom (D.map g))
    (hN : ∀ i, IsNoetherian (D.obj i)) (hRP : HasResolutionProperty c.pt) :
    ∃ i, HasResolutionProperty (D.obj i) :=
  exists_hasResolutionProperty_of_isLimit D c hc hN

end AlgebraicGeometry

end
