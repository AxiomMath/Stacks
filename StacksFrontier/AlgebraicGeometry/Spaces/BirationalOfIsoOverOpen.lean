module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericPointsFiniteComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus
public import StacksFrontier.Topology.Irreducible.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationBirationalIntegral

/-!
# A morphism of algebraic spaces which is an isomorphism over an open is birational

Let `f : X ⟶ Y` be a morphism of decent algebraic spaces over a scheme `S` with finitely many
irreducible components, and let `V ⊆ Y` be an open subspace such that `f⁻¹(V) ⟶ V` is an
isomorphism, `f⁻¹(V)` contains every generic point of `|X|` and `V` contains every generic
point of `|Y|`. Then `f` is birational.

## Main results

* `AlgebraicGeometry.Space.isBirational_of_isIso_fromPreimage`: the criterion above.

## Implementation notes

On generic points the map is the composite of the open embedding `|f⁻¹(V)| ⟶ |X|` (inverted),
the homeomorphism `|f⁻¹(V)| ≅ |V|` and the open embedding `|V| ⟶ |Y|`, each of which preserves
and reflects generic points. On local rings, a chart `c` of `V` at the image of a generic point
gives the chart `c ≫ V.ι` of `Y` and the chart `c ≫ φ⁻¹ ≫ f⁻¹(V).ι` of `X`, and these are
compatible along `f` through the identity of the chart scheme, so the local-ring map is an
isomorphism.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The image of a point of `f⁻¹(V)` in `|Y|` factors through `|f⁻¹(V)| ⟶ |V| ⟶ |Y|`. -/
theorem pointsMap_preimage_ι_apply {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (V : Subfunctor Y) (p : points B S hS (V.preimage f).toFunctor) :
    pointsMap B S hS X f (pointsMap B S hS (V.preimage f).toFunctor (V.preimage f).ι p) =
      pointsMap B S hS V.toFunctor V.ι
        (pointsMap B S hS (V.preimage f).toFunctor (V.fromPreimage f) p) := by
  rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]

/-- The image in `|Y|` of a point of `|f⁻¹(V)|` can be computed through the homeomorphism
`|f⁻¹(V)| ≅ |V|` induced by the isomorphism `f⁻¹(V) ⟶ V`. -/
private theorem pointsMap_comp_ι_apply_homeomorph {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (V : Subfunctor Y) [IsIso (V.fromPreimage f)]
    (p : points B S hS (V.preimage f).toFunctor) :
    pointsMap B S hS X f (pointsMap B S hS (V.preimage f).toFunctor (V.preimage f).ι p) =
      pointsMap B S hS V.toFunctor V.ι
        (pointsHomeomorphOfIso B S hS (asIso (V.fromPreimage f)) p) :=
  pointsMap_preimage_ι_apply f V p

/-- An open subspace of a decent algebraic space with finitely many irreducible components has
finitely many irreducible components. -/
theorem finite_irreducibleComponents_points_of_isOpenSubspace
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hdecY : IsDecentSpace B S hS Y) (hfiniteY : (irreducibleComponents (points B S hS Y)).Finite)
    {V : Subfunctor Y} (hV : IsOpenSubspace B S hS V) :
    (irreducibleComponents (points B S hS V.toFunctor)).Finite := by
  have hiV := isOpenEmbedding_pointsMap_ι B S hS hV
  have hsoberV := stacksSober_points_of_isDecentSpace B S hS hV.1
    (isDecentSpace_of_isOpenSubspace B S hS hY hdecY hV)
  have : QuasiSober (points B S hS V.toFunctor) := (stacksSober_iff_t0_and_quasiSober.mp hsoberV).2
  have : T0Space (points B S hS V.toFunctor) := (stacksSober_iff_t0_and_quasiSober.mp hsoberV).1
  have : T0Space (points B S hS Y) :=
    (stacksSober_iff_t0_and_quasiSober.mp (stacksSober_points_of_isDecentSpace B S hS hY hdecY)).1
  have : Finite (genericPoints (points B S hS V.toFunctor)) :=
    (((genericPoints.finite hfiniteY).preimage hiV.injective.injOn).subset
      fun w hw => hiV.mem_genericPoints hw).to_subtype
  exact Set.finite_coe_iff.mp
    (Finite.of_equiv _ (genericPoints.equiv (α := points B S hS V.toFunctor)))

/-- If `f⁻¹(V) ⟶ V` is an isomorphism and `f⁻¹(V)`, `V` contain the generic points of `|X|`,
`|Y|`, then `f` maps the generic points of `|X|` bijectively onto those of `|Y|`. -/
theorem bijOn_genericPoints_of_isIso_fromPreimage {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V) [IsIso (V.fromPreimage f)]
    (hgenX : genericPoints (points B S hS X) ⊆
      Set.range (pointsMap B S hS (V.preimage f).toFunctor (V.preimage f).ι))
    (hgenY : genericPoints (points B S hS Y) ⊆
      Set.range (pointsMap B S hS V.toFunctor V.ι)) :
    Set.BijOn (pointsMap B S hS X f) (genericPoints (points B S hS X))
      (genericPoints (points B S hS Y)) := by
  set P := V.preimage f
  set φ := V.fromPreimage f
  have hiP := isOpenEmbedding_pointsMap_ι B S hS (isOpenSubspace_preimage B S hS f V hY hX hV)
  let e := pointsHomeomorphOfIso B S hS (asIso φ)
  have hj : Topology.IsOpenEmbedding (pointsMap B S hS V.toFunctor V.ι ∘ e) :=
    (isOpenEmbedding_pointsMap_ι B S hS hV).comp e.isOpenEmbedding
  have hsq := pointsMap_comp_ι_apply_homeomorph f V
  have hgen : ∀ p, pointsMap B S hS P.toFunctor P.ι p ∈ genericPoints (points B S hS X) ↔
      pointsMap B S hS X f (pointsMap B S hS P.toFunctor P.ι p) ∈
        genericPoints (points B S hS Y) := by
    intro p
    rw [hsq, hiP.mem_genericPoints_iff]
    exact (hj.mem_genericPoints_iff (x := p)).symm
  refine ⟨fun x hx => ?_, fun x hx x' hx' hxx' => ?_, fun y hy => ?_⟩
  · obtain ⟨p, rfl⟩ := hgenX hx
    exact (hgen p).1 hx
  · obtain ⟨p, rfl⟩ := hgenX hx
    obtain ⟨p', rfl⟩ := hgenX hx'
    rw [hsq, hsq] at hxx'
    rw [hj.injective hxx']
  · obtain ⟨v, rfl⟩ := hgenY hy
    refine ⟨pointsMap B S hS P.toFunctor P.ι (e.symm v), (hgen _).2 ?_, ?_⟩ <;>
      rw [hsq, e.apply_symm_apply]
    exact hy

/-- **A morphism which is an isomorphism over an open subspace containing the generic points is
birational.** -/
theorem isBirational_of_isIso_fromPreimage {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y)
    (hfiniteX : (irreducibleComponents (points B S hS X)).Finite)
    (hfiniteY : (irreducibleComponents (points B S hS Y)).Finite) (f : X ⟶ Y)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V) [IsIso (V.fromPreimage f)]
    (hgenX : genericPoints (points B S hS X) ⊆
      Set.range (pointsMap B S hS (V.preimage f).toFunctor (V.preimage f).ι))
    (hgenY : genericPoints (points B S hS Y) ⊆
      Set.range (pointsMap B S hS V.toFunctor V.ι)) :
    IsBirational B S hS hX hY hdecX hdecY hfiniteX hfiniteY f := by
  have hbij := bijOn_genericPoints_of_isIso_fromPreimage hX hY f V hV hgenX hgenY
  set P := V.preimage f
  set φ := V.fromPreimage f
  have hP : IsOpenSubspace B S hS P := isOpenSubspace_preimage B S hS f V hY hX hV
  have hiP := isOpenEmbedding_pointsMap_ι B S hS hP
  let e := pointsHomeomorphOfIso B S hS (asIso φ)
  have hsq := pointsMap_comp_ι_apply_homeomorph f V
  refine ⟨hbij, fun x hx => ?_⟩
  obtain ⟨p, rfl⟩ := hgenX hx
  have hvgen : e p ∈ genericPoints (points B S hS V.toFunctor) :=
    (Homeomorph.mem_genericPoints_iff e p).2 (hiP.mem_genericPoints_of_image hx)
  let cV := schematicGenericChart B S hS hV.1
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hV.1
      (isDecentSpace_of_isOpenSubspace B S hS hY hdecY hV))
    (finite_irreducibleComponents_points_of_isOpenSubspace hY hdecY hfiniteY hV) (e p) hvgen
  let d : GenericChart B S hS (pointsMap B S hS X f (pointsMap B S hS P.toFunctor P.ι p)) :=
    ⟨cV.U, cV.immersion ≫ V.ι, MorphismProperty.comp_mem _ _ _ cV.isOpen hV.2, cV.point, by
      rw [pointsMap_comp_apply, cV.mapsTo, hsq]⟩
  let c : GenericChart B S hS (pointsMap B S hS P.toFunctor P.ι p) :=
    ⟨cV.U, cV.immersion ≫ inv φ ≫ P.ι, MorphismProperty.comp_mem _ _ _ cV.isOpen
      (MorphismProperty.comp_mem _ _ _ (isOpenImmersion_of_isIso B S hS (inv φ)) hP.2),
      cV.point, by
      rw [pointsMap_comp_apply, pointsMap_comp_apply, cV.mapsTo]
      exact congrArg _ (e.symm_apply_apply p)⟩
  have hk : c.immersion ≫ f = yoneda.map (𝟙 cV.U) ≫ d.immersion := by
    change (cV.immersion ≫ inv φ ≫ P.ι) ≫ f = yoneda.map (𝟙 cV.U) ≫ cV.immersion ≫ V.ι
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, Category.assoc,
      ← Subfunctor.fromPreimage_ι]
    exact congrArg (cV.immersion ≫ ·) (IsIso.inv_hom_id_assoc φ V.ι)
  have hkp : (BigFppfOver.toScheme B S hS).map (𝟙 cV.U) (schemePoint B S hS c.U c.point) =
      schemePoint B S hS d.U d.point := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  have he := (exists_genericLocalRingMap B S hS hX hY
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecX)
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecY)
    hfiniteX hfiniteY f _ hx (hbij.mapsTo hx)).choose_spec c d (𝟙 cV.U) hk hkp
  rw [show genericLocalRingMap B S hS hX hY _ _ hfiniteX hfiniteY f _ hx (hbij.mapsTo hx) = _
    from he]
  infer_instance

end AlgebraicGeometry.Space

end
