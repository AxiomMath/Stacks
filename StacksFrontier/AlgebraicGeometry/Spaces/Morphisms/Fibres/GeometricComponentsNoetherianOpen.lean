module

public import StacksFrontier.AlgebraicGeometry.Properties.DiscreteValuation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricComponentsDVR
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricComponentsLowerSemicontinuous
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReducedOpenLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.Topology.Specialization.Constructible

/-!
# Geometrically reduced and connected fibres form an open set over a Noetherian base

Let `f : X ⟶ U` be a proper, flat morphism of finite presentation from an algebraic space to a
Noetherian scheme `U` of the big fppf site. The set of points of `U` at which the fibre of `f` is
geometrically reduced (Stacks 0E08) and the geometric fibre is connected — has exactly one
connected component (Stacks 0E1B) — is open.

The set is constructible: it is cut out by the open locus of geometrically reduced fibres
(Stacks 0E0C) and by the two open sets `{n ≥ 1}` and `{n ≥ 2}` of the lower semicontinuous
function `n` counting the geometric connected components (Stacks 0E1D). It is stable under
generalization: a specialization `η ⤳ y` of points of the Noetherian scheme `U` is realised by
a discrete valuation ring (Stacks 054F), and over a discrete valuation ring connectedness of the
geometric fibre spreads from the closed point to the generic point when the closed fibre is
geometrically reduced (`AlgebraicGeometry.Space.numberGeometricConnectedComponents_eq_one_of_dvr`).
A constructible set stable under generalization in a Noetherian scheme is open (Stacks 0542).

## Main results

* `AlgebraicGeometry.Space.isOpen_setOf_isGeometricallyReducedFibreAt_and_eq_one`: the
  statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The image of the point of the spectrum of a field `κ` under `Spec κ ⟶ Spec R` is the kernel of
the ring map `R ⟶ κ`. -/
private theorem asIdeal_spec_map_closedPoint {R κ : Type u} [CommRing R] [Field κ] (φ : R →+* κ)
    (x : Spec (.of κ)) :
    ((Spec.map (CommRingCat.ofHom φ)) x : PrimeSpectrum R).asIdeal = RingHom.ker φ := by
  rw [Spec.map_apply]
  change Ideal.comap φ x.asIdeal = _
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  rw [Ideal.eq_bot_of_prime x.asIdeal]
  rfl

/-- A ring whose fraction field has the cardinality of a residue field of a scheme of the site has
its spectrum in the site. -/
private theorem contains_spec_of_residueField_genericPoint {R : Type u} [CommRing R] [IsDomain R]
    {T : Scheme.{u}} (hT : B.Contains T) (t : T)
    (e : (Spec (.of R)).residueField (_root_.genericPoint (Spec (.of R))) ≃+* T.residueField t) :
    B.Contains (Spec (.of R)) := by
  have hκ : B.Contains (Spec (T.residueField t)) :=
    (Scheme.size_le_of_mono_quasiCompact (T.fromSpecResidueField t)).trans_lt hT
  refine BigFppfSite.contains_spec_of_mk_lt_cutoff B (lt_of_le_of_lt ?_
    (BigFppfSite.mk_lt_cutoff_of_contains_spec B hκ))
  let x := _root_.genericPoint (Spec (.of R))
  have hx : x.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal (genericPoint_eq_bot_of_affine (.of R))
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  have hinj : Function.Injective (algebraMap R x.asIdeal.ResidueField) := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField, hx]
  exact Cardinal.mk_le_of_injective <| e.injective.comp
    ((Scheme.Spec.residueFieldIso (.of R) x).commRingCatIsoToRingEquiv.symm.injective.comp hinj)

/-- **Geometrically reduced and connected fibres form an open set over a Noetherian base.** Let
`f : X ⟶ U` be a proper, flat morphism of finite presentation from an algebraic space to a
Noetherian scheme `U` of the big fppf site. The set of points of `U` at which the fibre of `f` is
geometrically reduced and the geometric fibre has exactly one connected component is open. -/
theorem isOpen_setOf_isGeometricallyReducedFibreAt_and_eq_one (U : BigFppfOver B S hS)
    [AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (f : X ⟶ yoneda.obj U) (hX : IsAlgebraicSpace B S hS X)
    (hf : IsProper B S hS f) (hfl : IsFlat B S hS f) (hfp : IsFinitePresentation B S hS f) :
    IsOpen {y | IsGeometricallyReducedFibreAt B S hS f hX (isAlgebraicSpace_yoneda B S hS U) y ∧
      numberGeometricConnectedComponents B S hS f y = 1} := by
  have hY := isAlgebraicSpace_yoneda B S hS U
  set 𝒰 := (BigFppfOver.toScheme B S hS).obj U
  set n := numberGeometricConnectedComponents B S hS f
  set E := geometricallyReducedFibreLocus B S hS f hX hY
  set G := {y | IsGeometricallyReducedFibreAt B S hS f hX hY y ∧ n y = 1}
  have hE : IsOpen E := isOpen_geometricallyReducedFibreLocus B S hS f hX hY hfl hf hfp
  have hlsc := lowerSemicontinuous_numberGeometricConnectedComponents B S hS hX hY f hf hfl hfp
  have hO : ∀ c : ℕ∞, IsOpen (n ⁻¹' Set.Ioi c) := lowerSemicontinuous_iff_isOpen_preimage.mp hlsc
  have hGeq : G = E ∩ n ⁻¹' Set.Ioi 0 ∩ (n ⁻¹' Set.Ioi 1)ᶜ := by
    ext y
    simp only [G, E, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi,
      Set.mem_compl_iff, not_lt]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, h2 ▸ zero_lt_one⟩, h2.le⟩,
      fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, le_antisymm h3 (Order.one_le_iff_pos.mpr h2)⟩⟩
  suffices hG' : IsOpen ((schemePointsHomeomorph B S hS U).symm ⁻¹' G) by
    have := hG'.preimage (schemePointsHomeomorph B S hS U).continuous
    rwa [← Set.preimage_comp, Homeomorph.symm_comp_self, Set.preimage_id] at this
  have hcons : ∀ s : Set 𝒰, IsOpen s → Topology.IsConstructible s := fun s hs =>
    IsRetrocompact.isConstructible hs fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _
  refine isOpen_of_stableUnderGeneralization_of_isConstructible 𝒰 _ ?_ ?_
  · rw [hGeq, Set.preimage_inter, Set.preimage_inter, Set.preimage_compl]
    exact ((hcons _ (hE.preimage (schemePointsHomeomorph B S hS U).symm.continuous)).inter
      (hcons _ ((hO 0).preimage (schemePointsHomeomorph B S hS U).symm.continuous))).inter
      (hcons _ ((hO 1).preimage (schemePointsHomeomorph B S hS U).symm.continuous)).compl
  · rintro y' η' hspec ⟨hyE, hy1⟩
    obtain rfl | hne := eq_or_ne y' η'
    · exact ⟨hyE, hy1⟩
    refine ⟨(hE.preimage (schemePointsHomeomorph B S hS U).symm.continuous
      ).stableUnderGeneralization hspec hyE, ?_⟩
    obtain ⟨R, _, _, _, φ, hη, hcl, eR, -⟩ :=
      exists_dvr_morphism_of_specializes_with_residueField_equiv 𝒰 hspec hne (𝒰.residueField η')
    have hV : B.Contains (Spec (.of R)) :=
      contains_spec_of_residueField_genericPoint B U.left.property η' eR
    let gR : B.obj hV ⟶ B.obj hS := ObjectProperty.homMk φ ≫ U.hom
    let v : (yoneda.obj U).obj (op (Over.mk gR)) := Over.homMk (ObjectProperty.homMk φ) rfl
    have hP : B.Contains (Spec (.of (maximalIdeal R).ResidueField)) :=
      BigFppfSite.contains_spec_residueField_atPrime B hV (maximalIdeal R)
    let gP : B.obj hP ⟶ B.obj hV := ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap R (maximalIdeal R).ResidueField)))
    let K := AlgebraicClosure (⊥ : Ideal R).ResidueField
    have hK : B.Contains (Spec (.of K)) := BigFppfSite.contains_spec_algebraicClosure B
      (BigFppfSite.contains_spec_residueField_atPrime B hV ⊥)
    have hinjK : Function.Injective (algebraMap R K) := by
      rw [IsScalarTower.algebraMap_eq R (⊥ : Ideal R).ResidueField K, RingHom.coe_comp]
      refine (algebraMap (⊥ : Ideal R).ResidueField K).injective.comp ?_
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField]
    have : Module.IsTorsionFree R K := ⟨fun r hr x y hxy =>
      mul_left_cancel₀ ((map_ne_zero_iff _ hinjK).mpr hr.ne_zero) <| by
        simpa only [Algebra.smul_def] using hxy⟩
    let gK : B.obj hK ⟶ B.obj hV :=
      ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    have hps : FieldValuedPoint.class B S hS (yoneda.obj U)
        { carrier := (maximalIdeal R).ResidueField, contained := hP, toBase := (gP ≫ gR).hom,
          value := (yoneda.obj U).map (Over.homMk gP rfl).op v } =
          (schemePointsHomeomorph B S hS U).symm y' := by
      apply (schemePointsHomeomorph B S hS U).injective
      rw [Homeomorph.apply_symm_apply, ← hcl, schemePointsHomeomorph_apply, pointsToScheme_class]
      change φ ((Spec.map (CommRingCat.ofHom (algebraMap R (maximalIdeal R).ResidueField)))
        (closedPoint (maximalIdeal R).ResidueField)) = _
      congr 1
      exact PrimeSpectrum.ext <|
        (asIdeal_spec_map_closedPoint (algebraMap R (maximalIdeal R).ResidueField) _).trans
          (Ideal.ker_algebraMap_residueField (maximalIdeal R))
    have hpK : FieldValuedPoint.class B S hS (yoneda.obj U)
        { carrier := K, contained := hK, toBase := (gK ≫ gR).hom,
          value := (yoneda.obj U).map (Over.homMk gK rfl).op v } =
          (schemePointsHomeomorph B S hS U).symm η' := by
      apply (schemePointsHomeomorph B S hS U).injective
      rw [Homeomorph.apply_symm_apply, ← hη, schemePointsHomeomorph_apply, pointsToScheme_class]
      change φ ((Spec.map (CommRingCat.ofHom (algebraMap R K))) (closedPoint K)) = _
      congr 1
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext <| (asIdeal_spec_map_closedPoint (algebraMap R K) _).trans
        ((RingHom.injective_iff_ker_eq_bot _).mp hinjK)
    have key := numberGeometricConnectedComponents_eq_one_of_dvr B S hS f hX hY hf hfl hfp hV gR
      v hP gP rfl K hK gK rfl (hps ▸ hyE) (hps ▸ hy1)
    rwa [hpK] at key

end AlgebraicGeometry.Space
