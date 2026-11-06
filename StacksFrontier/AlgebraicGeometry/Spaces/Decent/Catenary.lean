module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Catenary
public import StacksFrontier.AlgebraicGeometry.Spaces.Catenary
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Noetherian.CatenaryOpenCovering

/-!
# Catenarity of a decent algebraic space over a catenary base

An algebraic space which is decent and locally of finite type over a locally Noetherian,
universally catenary base is catenary. This is **Stacks 0ED6**.

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `isCatenary_of_dimensionFunction`: a decent algebraic space locally of finite type over a locally
  Noetherian, universally catenary base carrying a dimension function is catenary.
* `isCatenary_of_isDecentSpace`: a decent algebraic space locally of finite type over a locally
  Noetherian, universally catenary base is catenary (**Stacks 0ED6**).

## References

* [Stacks Project, Tag 02I2](https://stacks.math.columbia.edu/tag/02I2)
* [Stacks Project, Tag 02IA](https://stacks.math.columbia.edu/tag/02IA)
* [Stacks Project, Tag 02IC](https://stacks.math.columbia.edu/tag/02IC)
* [Stacks Project, Tag 02IY](https://stacks.math.columbia.edu/tag/02IY)
* [Stacks Project, Tag 0462](https://stacks.math.columbia.edu/tag/0462)
* [Stacks Project, Tag 03KF](https://stacks.math.columbia.edu/tag/03KF)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 0ED4](https://stacks.math.columbia.edu/tag/0ED4)
* [Stacks Project, Tag 0ED5](https://stacks.math.columbia.edu/tag/0ED5)
* [Stacks Project, Tag 0ED6](https://stacks.math.columbia.edu/tag/0ED6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- A sober space carrying a dimension function is catenary. -/
private theorem isCatenarySpace_of_dimensionFunction {α : Type*} [TopologicalSpace α]
    (hsob : StacksSober α) (d : TopologicalSpace.DimensionFunction α) :
    IrreducibleClosedsCodim.IsCatenarySpace α :=
  (isCatenarySpace_and_topCodim_eq_of_isDimensionFunction α hsob (d : α → ℤ)
    { strict_spec := fun {_ _} hxy hne ↦ d.strictAnti_specializes hxy hne
      immediate := fun {_ _} himm ↦ d.step_immediate himm }).1

/-- An open subset of a sober space which carries a dimension function is catenary. -/
private theorem isCatenarySpace_subtype_of_dimensionFunction {α : Type*} [TopologicalSpace α]
    (hsob : StacksSober α) {W : Set α} (hW : IsOpen W)
    (d : TopologicalSpace.DimensionFunction W) :
    IrreducibleClosedsCodim.IsCatenarySpace W := by
  obtain ⟨_, _⟩ := stacksSober_iff_t0_and_quasiSober.mp hsob
  have : QuasiSober W := hW.isOpenEmbedding_subtypeVal.quasiSober
  exact isCatenarySpace_of_dimensionFunction
    (stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩) d

/-- A space each of whose points has a catenary open neighbourhood is catenary (Stacks 02I2). -/
private theorem isCatenarySpace_of_forall_exists_mem_isOpen {α : Type*} [TopologicalSpace α]
    (h : ∀ x : α, ∃ W : Set α, IsOpen W ∧ x ∈ W ∧
      IrreducibleClosedsCodim.IsCatenarySpace W) :
    IrreducibleClosedsCodim.IsCatenarySpace α :=
  (CatenaryTopologicalSpace.isCatenary_iff_hasOpenCoveringByCatenarySpaces α).mpr
    ⟨α, fun x ↦ (h x).choose, fun x ↦ (h x).choose_spec.1,
      Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.mpr ⟨y, (h y).choose_spec.2.1⟩,
      fun x ↦ (h x).choose_spec.2.2⟩

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_DecentCatenary
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A morphism to an object of the site all of whose points lie over an open subobject factors
through that subobject. -/
private theorem exists_comp_eq_of_range_subset
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    {T V : BigFppfOver B S hS} (ιV : V ⟶ T)
    (hιV : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ιV))
    (p : Z ⟶ yoneda.obj T)
    (hsub : Set.range (pointsMap B S hS Z p) ⊆
      Set.range (pointsMap B S hS (yoneda.obj V) (yoneda.map ιV))) :
    ∃ q : Z ⟶ yoneda.obj V, q ≫ yoneda.map ιV = p := by
  have _hst := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
  have _hbc := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  have hopenV : IsOpenImmersion B S hS (yoneda.map ιV) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ιV).2 hιV
  have sq : IsPullback (pullback.fst p (yoneda.map ιV)) (pullback.snd p (yoneda.map ιV)) p
      (yoneda.map ιV) := IsPullback.of_hasPullback _ _
  have hPalg : IsAlgebraicSpace B S hS (pullback p (yoneda.map ιV)) :=
    isAlgebraicSpace_pullback B S hS p (yoneda.map ιV) hZ (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_yoneda B S hS T)
  have hfstopen : IsOpenImmersion B S hS (pullback.fst p (yoneda.map ιV)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip hopenV
  have hfstsurj : Function.Surjective
      (pointsMap B S hS (pullback p (yoneda.map ιV)) (pullback.fst p (yoneda.map ιV))) := by
    have hpre := preimage_image_pointsMap_of_isPullback B S hS sq.flip (Set.univ)
    rw [Set.image_univ, Set.preimage_univ, Set.image_univ] at hpre
    intro z
    have hz : z ∈ pointsMap B S hS Z p ⁻¹'
        Set.range (pointsMap B S hS (yoneda.obj V) (yoneda.map ιV)) :=
      hsub ⟨z, rfl⟩
    rwa [hpre] at hz
  have hiso : IsIso (pullback.fst p (yoneda.map ιV)) :=
    isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS _ hfstopen
      ((surjective_iff_pointsMap_surjective B S hS hPalg hZ _ hfstopen.rep).mpr hfstsurj)
  refine ⟨inv (pullback.fst p (yoneda.map ιV)) ≫ pullback.snd p (yoneda.map ιV), ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

/-- The points of an object of the site lying over an open subobject of its target are exactly
those whose scheme point lies in the corresponding open set. -/
private theorem range_pointsMap_yoneda_map_openObjHom {T : BigFppfOver B S hS}
    (O : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    Set.range (pointsMap B S hS
        (yoneda.obj (Stacks.SeparationLocal.openObj B S hS T O.ι))
        (yoneda.map (Stacks.SeparationLocal.openObjHom B S hS T O.ι))) =
      pointsToScheme B S hS T ⁻¹' (O : Set ((BigFppfOver.toScheme B S hS).obj T)) := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    rw [Set.mem_preimage, pointsToScheme_pointsMap, ← Scheme.Opens.range_ι (U := O)]
    exact Set.mem_range_self _
  · intro hy
    rw [Set.mem_preimage, ← Scheme.Opens.range_ι (U := O)] at hy
    obtain ⟨w, hw⟩ := hy
    let a : points B S hS (yoneda.obj (Stacks.SeparationLocal.openObj B S hS T O.ι)) :=
      (schemePointsHomeomorph B S hS (Stacks.SeparationLocal.openObj B S hS T O.ι)).symm w
    have haw : pointsToScheme B S hS
        (Stacks.SeparationLocal.openObj B S hS T O.ι) a = w :=
      (schemePointsHomeomorph B S hS
        (Stacks.SeparationLocal.openObj B S hS T O.ι)).apply_symm_apply w
    refine ⟨a, (schemePointsHomeomorph B S hS T).injective ?_⟩
    rwa [schemePointsHomeomorph_apply, schemePointsHomeomorph_apply,
      pointsToScheme_pointsMap, haw]

/-- A decent algebraic space over `S` which is locally of finite type over an object of the
site whose scheme is locally Noetherian, universally catenary and carries a dimension function
is catenary. -/
theorem isCatenary_of_dimensionFunction {T : BigFppfOver B S hS}
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
    (hcat : Scheme.IsUniversallyCatenary ((BigFppfOver.toScheme B S hS).obj T))
    (δ : TopologicalSpace.DimensionFunction ((BigFppfOver.toScheme B S hS).obj T))
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (f : X ⟶ yoneda.obj T) (hf : IsLocallyOfFiniteType B S hS f) :
    IsCatenary B S hS X hX := by
  obtain ⟨d, -⟩ := inducedDimensionValue_isDimensionFunction B S hS hcat δ hX
    (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec) f hf
  exact isCatenarySpace_of_dimensionFunction (stacksSober_points_of_isDecentSpace B S hS hX hdec) d

/-- **Stacks 0ED6.** A decent algebraic space over `S` which is locally of finite type over an
object of the site whose scheme is locally Noetherian and universally catenary is catenary. -/
@[stacks 0ED6]
theorem isCatenary_of_isDecentSpace {T : BigFppfOver B S hS}
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
    (hcat : Scheme.IsUniversallyCatenary ((BigFppfOver.toScheme B S hS).obj T))
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (f : X ⟶ yoneda.obj T) (hf : IsLocallyOfFiniteType B S hS f) :
    IsCatenary B S hS X hX := by
  refine isCatenarySpace_of_forall_exists_mem_isOpen fun x ↦ ?_
  obtain ⟨U₀, hU₀open, hU₀mem, ⟨δ₀⟩⟩ :=
    (AlgebraicGeometry.isCatenarySpace_iff_locally_dimensionFunction
        ((BigFppfOver.toScheme B S hS).obj T)).mp (hcat.isCatenarySpace (𝟙 _))
      (pointsToScheme B S hS T (pointsMap B S hS X f x))
  let O : ((BigFppfOver.toScheme B S hS).obj T).Opens := ⟨U₀, hU₀open⟩
  let V : BigFppfOver B S hS := Stacks.SeparationLocal.openObj B S hS T O.ι
  let ιV : V ⟶ T := Stacks.SeparationLocal.openObjHom B S hS T O.ι
  have hιVopen : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ιV) :=
    (inferInstance : AlgebraicGeometry.IsOpenImmersion O.ι)
  have _hVnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    (inferInstance : IsLocallyNoetherian O.toScheme)
  have _hVlft : AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map ιV) :=
    (inferInstance : AlgebraicGeometry.LocallyOfFiniteType O.ι)
  have hcatV : Scheme.IsUniversallyCatenary ((BigFppfOver.toScheme B S hS).obj V) :=
    Scheme.isUniversallyCatenary_of_locallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map ιV) hcat
  have δV : TopologicalSpace.DimensionFunction ((BigFppfOver.toScheme B S hS).obj V) := δ₀
  set W : Set (points B S hS X) :=
    (fun y ↦ pointsToScheme B S hS T (pointsMap B S hS X f y)) ⁻¹' U₀
  have hWopen : IsOpen W :=
    IsOpen.preimage
      ((schemePointsHomeomorph B S hS T).continuous.comp (continuous_pointsMap B S hS f))
      hU₀open
  refine ⟨W, hWopen, hU₀mem, ?_⟩
  let G : Subfunctor X := openSubspaceOfPoints B S hS X W
  have hGopen : IsOpenSubspace B S hS G :=
    isOpenSubspace_openSubspaceOfPoints B S hS hX W hWopen
  have hGrange : Set.range (pointsMap B S hS G.toFunctor G.ι) = W :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS W
  have hGlft : IsLocallyOfFiniteType B S hS (G.ι ≫ f) :=
    isLocallyOfFiniteType_comp B S hS hGopen.1 hX (isAlgebraicSpace_yoneda B S hS T) G.ι f
      (isLocallyOfFiniteType_of_isEtale B S hS hX (isEtale_ι_of_isOpenSubspace hGopen)) hf
  have hsub : Set.range (pointsMap B S hS G.toFunctor (G.ι ≫ f)) ⊆
      Set.range (pointsMap B S hS (yoneda.obj V) (yoneda.map ιV)) := by
    rw [range_pointsMap_yoneda_map_openObjHom B S hS O]
    rintro - ⟨a, rfl⟩
    have ha : pointsMap B S hS G.toFunctor G.ι a ∈ W := hGrange ▸ Set.mem_range_self a
    rw [Set.mem_preimage, pointsMap_comp_apply]
    exact ha
  obtain ⟨g, hg⟩ :=
    exists_comp_eq_of_range_subset B S hS hGopen.1 ιV hιVopen (G.ι ≫ f) hsub
  obtain ⟨d, -⟩ := inducedDimensionValue_isDimensionFunction B S hS hcatV δV hGopen.1
    (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS
      (isDecentSpace_of_relativelyRepresentable B S hS hGopen.1 G.ι hGopen.2.rep hdec)) g
    (isLocallyOfFiniteType_of_comp B S hS hGopen.1 (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_yoneda B S hS T) g (yoneda.map ιV) (hg ▸ hGlft))
  refine isCatenarySpace_subtype_of_dimensionFunction
    (stacksSober_points_of_isDecentSpace B S hS hX hdec) hWopen
    (d.comp (Homeomorph.isOpenEmbedding
      ((isEmbedding_pointsMap_of_isImmersion B S hS hX G.ι
        (isImmersion_of_isOpenImmersion B S hS hGopen.2)).toHomeomorph.trans
          (Homeomorph.setCongr hGrange)).symm))

end AlgebraicGeometry.Space

end
