module

public import StacksFrontier.AlgebraicGeometry.Limits.AffineSiteNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGeometricallyReducedConnected
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGeometricallyReducedOpen
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricComponentsNoetherianOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique

/-!
# Geometrically reduced and connected fibres form an open set

Let `f : X ⟶ U` be a proper, flat morphism of finite presentation from an algebraic space to a
scheme `U` of the big fppf site of `Spec(ℤ)`. The set of points of `U` at which the fibre of `f`
is geometrically reduced (Stacks 0E08) and the geometric fibre is connected — has exactly one
connected component (Stacks 0E1B) — is open.

For a Noetherian base this is
`AlgebraicGeometry.Space.isOpen_setOf_isGeometricallyReducedFibreAt_and_eq_one`. An affine base
`T` is the limit of the spectra of the finite-type `ℤ`-subalgebras of `Γ(T, 𝒪)`
(`AlgebraicGeometry.isLimit_affineSiteStageCone`, Stacks 01ZA), and a proper, flat morphism of
finite presentation to `T` is the base change of one to such a Noetherian stage
(`AlgebraicGeometry.properFlatFamilyDescendsAlongAffineLimit`, the descent of objects in
Stacks 0D1I); both the geometric reducedness of the fibres (Stacks 0E09) and the number of
geometric connected components (Stacks 0E1B) are compatible with base change, so the set is the
inverse image of the corresponding open set of the stage. A general base is covered by affine
étale charts, which are open on points.

## Main results

* `AlgebraicGeometry.Space.isOpen_setOf_isGeometricallyReducedFibreAt_and_eq_one_of_isAffine`:
  the statement for an affine base.
* `AlgebraicGeometry.Space.isOpen_setOf_isGeometricallyReducedFibreAt_and_eq_one_of_scheme`: the
  statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {X : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}

/-- The locus of points with geometrically reduced fibre and connected geometric fibre of a base
change `X ×_Y Y' ⟶ Y'` is the inverse image of that of `f : X ⟶ Y` (Stacks 0E09 and 0E1B). -/
private theorem setOf_geometricallyReduced_and_eq_one_pullback {S : Scheme.{u}}
    {hS : B.Contains S} {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') :
    {y | IsGeometricallyReducedFibreAt B S hS (pullback.snd f g)
        (isAlgebraicSpace_pullback B S hS f g hX hY' hY) hY' y ∧
      numberGeometricConnectedComponents B S hS (pullback.snd f g) y = 1} =
      pointsMap B S hS Y' g ⁻¹'
        {y | IsGeometricallyReducedFibreAt B S hS f hX hY y ∧
          numberGeometricConnectedComponents B S hS f y = 1} := by
  ext y
  have h1 := congrArg (fun s => y ∈ s)
    (geometricallyReducedFibreLocus_pullback B S hS f g hX hY hY')
  have h2 := congrFun (numberGeometricConnectedComponents_baseChange B S hS hX hY hY' f g) y
  simp only [eq_iff_iff] at h1
  simp only [Set.mem_setOf_eq, Set.mem_preimage, IsGeometricallyReducedFibreAt, h1, h2,
    Function.comp_apply]

/-- The locus is unchanged by precomposing the morphism with an isomorphism of the source. -/
private theorem setOf_geometricallyReduced_and_eq_one_iso_comp {S : Scheme.{u}}
    {hS : B.Contains S} {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X' ≅ X) (f : X ⟶ Y)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) :
    {y | IsGeometricallyReducedFibreAt B S hS (e.hom ≫ f) hX' hY y ∧
      numberGeometricConnectedComponents B S hS (e.hom ≫ f) y = 1} =
      {y | IsGeometricallyReducedFibreAt B S hS f hX hY y ∧
        numberGeometricConnectedComponents B S hS f y = 1} := by
  ext y
  simp only [Set.mem_setOf_eq, IsGeometricallyReducedFibreAt,
    geometricallyReducedFibreLocus_iso_comp B S hS e f hX' hX hY,
    numberGeometricConnectedComponents_iso_comp e f]

/-- **Geometrically reduced and connected fibres form an open set over an affine base.** -/
theorem isOpen_setOf_isGeometricallyReducedFibreAt_and_eq_one_of_isAffine
    (T : BigFppfOver B integerBase hZ) [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj T)]
    (f : X ⟶ yoneda.obj T) (hX : IsAlgebraicSpace B integerBase hZ X)
    (hf : IsProper B integerBase hZ f) (hfl : IsFlat B integerBase hZ f)
    (hfp : IsFinitePresentation B integerBase hZ f) :
    IsOpen {y | IsGeometricallyReducedFibreAt B integerBase hZ f hX
        (isAlgebraicSpace_yoneda B integerBase hZ T) y ∧
      numberGeometricConnectedComponents B integerBase hZ f y = 1} := by
  obtain ⟨i, Zi, hZi, fi, g, hfpi, hfli, hpri, hpb⟩ :=
    properFlatFamilyDescendsAlongAffineLimit B integerBase hZ _ (affineSiteStageDiagram B hZ T)
      (affineSiteStageCone B hZ T) (isLimit_affineSiteStageCone B hZ T) X hX f hfp hfl hf
  have : AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj
      ((BigAffineFppf.inclusion B integerBase hZ).obj ((affineSiteStageDiagram B hZ T).obj i))) :=
    isNoetherian_affineSiteStageDiagram_obj B hZ T i
  have hopen := isOpen_setOf_isGeometricallyReducedFibreAt_and_eq_one B integerBase hZ _ fi hZi
    hpri hfli hfpi
  have hT := isAlgebraicSpace_yoneda B integerBase hZ T
  have hTi := isAlgebraicSpace_yoneda B integerBase hZ
    ((BigAffineFppf.inclusion B integerBase hZ).obj ((affineSiteStageDiagram B hZ T).obj i))
  have heq := setOf_geometricallyReduced_and_eq_one_pullback B fi
    (yoneda.map ((BigAffineFppf.inclusion B integerBase hZ).map
      ((affineSiteStageCone B hZ T).π.app i))) hZi hTi hT
  have h1 := setOf_geometricallyReduced_and_eq_one_iso_comp B hpb.isoPullback
    (pullback.snd fi (yoneda.map ((BigAffineFppf.inclusion B integerBase hZ).map
      ((affineSiteStageCone B hZ T).π.app i)))) hX
    (isAlgebraicSpace_pullback B integerBase hZ fi _ hZi hT hTi) hT
  rw [hpb.isoPullback_hom_snd, heq] at h1
  have h2 := hopen.preimage (continuous_pointsMap B integerBase hZ
    (yoneda.map ((BigAffineFppf.inclusion B integerBase hZ).map
      ((affineSiteStageCone B hZ T).π.app i))))
  rw [← h1] at h2
  exact h2

/-- **Geometrically reduced and connected fibres form an open set.** Let `f : X ⟶ U` be a
proper, flat morphism of finite presentation from an algebraic space to a scheme `U` of the big
fppf site of `Spec(ℤ)`. The set of points of `U` at which the fibre of `f` is geometrically
reduced and the geometric fibre has exactly one connected component is open. -/
theorem isOpen_setOf_isGeometricallyReducedFibreAt_and_eq_one_of_scheme
    (U : BigFppfOver B integerBase hZ)
    (f : X ⟶ yoneda.obj U) (hX : IsAlgebraicSpace B integerBase hZ X)
    (hf : IsProper B integerBase hZ f) (hfl : IsFlat B integerBase hZ f)
    (hfp : IsFinitePresentation B integerBase hZ f) :
    IsOpen {y | IsGeometricallyReducedFibreAt B integerBase hZ f hX
        (isAlgebraicSpace_yoneda B integerBase hZ U) y ∧
      numberGeometricConnectedComponents B integerBase hZ f y = 1} := by
  have hU := isAlgebraicSpace_yoneda B integerBase hZ U
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨W, t, hWaff, ht, w, hw⟩ := exists_affine_etale_chart_at_point B integerBase hZ _ hU y
  have hW := isAlgebraicSpace_yoneda B integerBase hZ W
  have hP := isAlgebraicSpace_pullback B integerBase hZ f t hX hW hU
  have hflfp := isFlat_and_isFinitePresentation_pullback_snd hX hU f hfl hfp t
  have hpr : IsProper B integerBase hZ (pullback.snd f t) :=
    (isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B integerBase hZ) ⟶ ⟨_, hU⟩)
        (ObjectProperty.homMk t : (⟨_, hW⟩ : AlgebraicSpaces B integerBase hZ) ⟶ ⟨_, hU⟩)) hf
  have hopen := isOpen_setOf_isGeometricallyReducedFibreAt_and_eq_one_of_isAffine B hZ W
    (pullback.snd f t) hP hpr hflfp.1 hflfp.2
  rw [setOf_geometricallyReduced_and_eq_one_pullback B f t hX hU hW] at hopen
  refine ⟨pointsMap B integerBase hZ _ t '' (pointsMap B integerBase hZ _ t ⁻¹'
    {y | IsGeometricallyReducedFibreAt B integerBase hZ f hX hU y ∧
      numberGeometricConnectedComponents B integerBase hZ f y = 1}), ?_, ?_, ?_⟩
  · exact Set.image_preimage_subset _ _
  · exact isOpenMap_pointsMap_of_etale B integerBase hZ hU W t ht _ hopen
  · exact ⟨w, by rw [Set.mem_preimage, hw]; exact hy, hw⟩

end AlgebraicGeometry.Space
