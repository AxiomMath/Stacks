module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreCartesianOfProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFiniteAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedPointInfiniteFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.NormalIntegralElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreFieldPushout

/-!
# The chart of Stacks 0EQ4 at the generic point of a prime divisor

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

include hintY in
/-- **The fibre of a proper dominant morphism over the generic point of a prime divisor of the
target is finite**, for integral good spaces of the same δ-dimension: by Stacks 0AD1 the morphism
is quasi-finite at every point above a point whose local ring has dimension at most one, the
transcendence degree at the generic point being zero. -/
theorem finite_fibre_primeDivisor_genericPoint {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hproper : IsProper D.site D.base D.base_mem p)
    (hgen : pointsMap D.site D.base D.base_mem X p
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      genericPoint D.site D.base D.base_mem hY.1 hintY)
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ =
      deltaDimensionClosed D sY hY Set.univ isClosed_univ)
    (W : PrimeDivisor D.site D.base D.base_mem Y) :
    {x : points D.site D.base D.base_mem X | pointsMap D.site D.base D.base_mem X p x =
      W.genericPoint D.site D.base D.base_mem Y}.Finite := by
  have hYLN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY
  refine (finite_fibre_iff_forall_isQuasiFiniteAt D.site D.base D.base_mem hX.1 hY.1 p
    hproper.2.1.1 hproper.2.2 hintX.2.1 hintY.2.1 _).2 ?_
  refine isQuasiFiniteAt_of_localRingDimension_le_one D.site D.base D.base_mem hX.1 hY.1 p
    hproper.2.1.1 hYLN _ ?_ (Or.inl fun x hx => ?_)
  · rw [W.localRingDimension_genericPoint D.site D.base D.base_mem hY.1 hintY.2.1]
  · rw [eq_genericPoint_of_localRingDimension_eq_zero D hintX hX.1 hx]
    exact hasTranscendenceDegreeAt_genericPoint_eq_zero D sX sY hX hY hintX hintY p hpB hgen hdim

/-! ### The generic fibres of the chart -/

section Fibre

variable {p : X ⟶ Y} (d : ChartDiagram D.site D.base D.base_mem X Y p)

/-- The canonical field point `Spec κ(w) ⟶ V` at a point `w` of the scheme of the chart `V`. -/
abbrev fibreChartFieldPoint (w : chartScheme d.V) :
    FieldValuedPoint D.site D.base D.base_mem
      (yoneda.obj ((SmallEtale.toOver D.site D.base D.base_mem Y).obj d.V)) :=
  canonicalSiteFieldPoint D.site D.base D.base_mem _ w

/-- The generic fibre of the chart `U ⟶ V` over a point `w` of `V`: `G = U ×_V Spec κ(w)`. -/
abbrev chartGenericFibre (w : chartScheme d.V) : BigFppfOver D.site D.base D.base_mem :=
  Limits.pullback d.g (fibreChartFieldPoint D d w).siteHom

include hintY in
/-- **The two cartesian squares of the generic fibre of the chart.** Let `w` be a point of the
chart `V` of `Y` over the generic point of `Y`. Then the fibre `G = U ×_V Spec κ(w)` of the chart
`U ⟶ V` sits in a cartesian square over `Spec κ(w) ⟶ Spec R(Y)`, with `Spec R(X)` in the fourth
corner. -/
theorem exists_isPullback_chartFibre (hpB : p ≫ sY = sX)
    (hproper : IsProper D.site D.base D.base_mem p)
    (hgen : pointsMap D.site D.base D.base_mem X p
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      genericPoint D.site D.base D.base_mem hY.1 hintY)
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ =
      deltaDimensionClosed D sY hY Set.univ isClosed_univ)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) p d.V.1.hom) (w : chartScheme d.V)
    (hw : chartSchemeToPoints D.site D.base D.base_mem Y d.V w =
      pointsMap D.site D.base D.base_mem X p (genericPoint D.site D.base D.base_mem hX.1 hintX)) :
    ∃ (g0 : (residueFieldRepresentative D.site D.base D.base_mem X hintX.2.1
          (genericPoint D.site D.base D.base_mem hX.1 hintX)).1.siteObject
          D.site D.base D.base_mem X ⟶
        (residueFieldRepresentative D.site D.base D.base_mem Y hintY.2.1
          (pointsMap D.site D.base D.base_mem X p
            (genericPoint D.site D.base D.base_mem hX.1 hintX))).1.siteObject
          D.site D.base D.base_mem Y)
      (f : (fibreChartFieldPoint D d w).siteObject D.site D.base D.base_mem _ ⟶
        (residueFieldRepresentative D.site D.base D.base_mem Y hintY.2.1
          (pointsMap D.site D.base D.base_mem X p
            (genericPoint D.site D.base D.base_mem hX.1 hintX))).1.siteObject
          D.site D.base D.base_mem Y)
      (r : chartGenericFibre D d w ⟶
        (residueFieldRepresentative D.site D.base D.base_mem X hintX.2.1
          (genericPoint D.site D.base D.base_mem hX.1 hintX)).1.siteObject
          D.site D.base D.base_mem X),
      yoneda.map g0 ≫ residueFieldMorphism D.site D.base D.base_mem Y hintY.2.1
          (pointsMap D.site D.base D.base_mem X p
            (genericPoint D.site D.base D.base_mem hX.1 hintX)) =
        residueFieldMorphism D.site D.base D.base_mem X hintX.2.1
          (genericPoint D.site D.base D.base_mem hX.1 hintX) ≫ p ∧
      yoneda.map (fibreChartFieldPoint D d w).siteHom ≫ d.V.1.hom =
        yoneda.map f ≫ residueFieldMorphism D.site D.base D.base_mem Y hintY.2.1
          (pointsMap D.site D.base D.base_mem X p
            (genericPoint D.site D.base D.base_mem hX.1 hintX)) ∧
      yoneda.map r ≫ residueFieldMorphism D.site D.base D.base_mem X hintX.2.1
          (genericPoint D.site D.base D.base_mem hX.1 hintX) =
        yoneda.map (Limits.pullback.fst d.g (fibreChartFieldPoint D d w).siteHom) ≫ d.U.1.hom ∧
      IsPullback (yoneda.map r)
        (yoneda.map (Limits.pullback.snd d.g (fibreChartFieldPoint D d w).siteHom))
        (yoneda.map g0) (yoneda.map f) := by
  obtain ⟨g0, hα⟩ := exists_isPullback_residueFieldMorphism_genericPoint_of_isProper D sX hX sY
    hY hintX hintY hpB hproper hgen hdim
  have hgf : IsPullback (yoneda.map (Limits.pullback.fst d.g (fibreChartFieldPoint D d w).siteHom))
      (yoneda.map (Limits.pullback.snd d.g (fibreChartFieldPoint D d w).siteHom)) (yoneda.map d.g)
      (yoneda.map (fibreChartFieldPoint D d w).siteHom) :=
    (IsPullback.of_hasPullback d.g (fibreChartFieldPoint D d w).siteHom).map yoneda
  -- the factorization of `Spec κ(w) ⟶ V ⟶ Y` through `Spec κ(p ξ_X)`
  have : Mono (yonedaEquiv.symm (residueFieldRepresentative D.site D.base D.base_mem Y hintY.2.1
      (pointsMap D.site D.base D.base_mem X p
        (genericPoint D.site D.base D.base_mem hX.1 hintX))).1.value) :=
    (residueFieldRepresentative D.site D.base D.base_mem Y hintY.2.1 _).2.2
  obtain ⟨f, hf, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono D.site D.base
    D.base_mem Y hY.1 (residueFieldRepresentative D.site D.base D.base_mem Y hintY.2.1
      (pointsMap D.site D.base D.base_mem X p
        (genericPoint D.site D.base D.base_mem hX.1 hintX))).1
    (chartSchemeFieldValuedPoint D.site D.base D.base_mem Y d.V w)
    ((residueFieldRepresentative D.site D.base D.base_mem Y hintY.2.1 _).2.1.trans hw.symm)
  have hcomm : yoneda.map (fibreChartFieldPoint D d w).siteHom ≫ d.V.1.hom =
      yoneda.map f ≫ residueFieldMorphism D.site D.base D.base_mem Y hintY.2.1
        (pointsMap D.site D.base D.base_mem X p
          (genericPoint D.site D.base D.base_mem hX.1 hintX)) := by
    rw [← fieldMorphism_map_yoneda]
    show _ = yoneda.map f ≫ yonedaEquiv.symm _
    rw [yonedaEquiv_symm_naturality_left, hf]
    rfl
  obtain ⟨a, ha1, -, ha⟩ := exists_isPullback_baseChange_of_isPullback hα hd hgf hcomm
  refine ⟨g0, f, yoneda.preimage a, hα.w.symm, hcomm, ?_, ?_⟩
  · rw [Functor.map_preimage, ha1]
  · rw [Functor.map_preimage]
    exact ha

end Fibre

end AlgebraicGeometry.Space

end
