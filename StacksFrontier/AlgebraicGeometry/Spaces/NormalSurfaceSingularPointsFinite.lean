module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.DedekindBase
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionIntegralMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteRegularAlteration
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# A normal two-dimensional space with a regular proper cover has finitely many singular points

Let `N` be an integral normal algebraic space over a scheme `S`, quasi-compact with locally
Noetherian étale charts and of dimension at most two, and let `g : X ⟶ N` be a proper dominant
morphism from an integral regular algebraic space. Then `N` has only finitely many points at which
it is not regular.

This is the finiteness of the singular locus in the implication (1) `⇒` (4) of
[Stacks, Tag 0BHY], along a corrected route. The source argues that the alteration is finite over
an open `V` containing the points of codimension at most one, flat there by [Stacks, Tag 00R4],
so that `V` is regular by [Stacks, Tag 07NG]. Flatness over all of such a `V` is not available:
`𝔸² ⟶ 𝔸²/{±1}` is a finite morphism from a regular scheme onto a normal surface which is not flat
at the vertex, and the vertex may lie in `V`. Instead:

1. regularity descends along a flat local homomorphism, so `N` is regular at the image of every
   point at which `g` is flat (`AlgebraicGeometry.Space.isRegularAt_of_isFlatAt`);
2. the flat locus of `g` is open ([Stacks, Tag 0399] for spaces) and `g` is closed, so the image
   `Z` of the non-flat locus is closed, and it contains every singular point because `g` is
   surjective;
3. `g` is flat at every point lying over a point of codimension at most one: there the local
   ring of `N` is a normal Noetherian local domain of dimension at most one, a Dedekind domain,
   and the local rings of `X` are torsion free over it because every generic point of a chart of
   `X` lies over a generic point of a chart of `N`
   (`AlgebraicGeometry.Space.isFlatAt_of_localRingDimension_le_one`);
4. a closed set of points of local dimension at least two in a quasi-compact space of dimension at
   most two with locally Noetherian charts is finite
   (`AlgebraicGeometry.Space.finite_of_isClosed_of_one_lt_localRingDimension`).

## Main results

* `AlgebraicGeometry.flat_stalkMap_of_ringKrullDim_le_one_of_genericPoints`: the scheme form of
  step 3.
* `AlgebraicGeometry.Space.isRegularAt_of_isFlatAt`: step 1.
* `AlgebraicGeometry.Space.isFlatAt_of_localRingDimension_le_one`: step 3.
* `AlgebraicGeometry.Space.finite_of_isClosed_of_one_lt_localRingDimension`: step 4.
* `AlgebraicGeometry.Space.finite_setOf_not_isRegularAt_of_isProper`: the finiteness of the
  singular locus.

## References

* [Stacks Project, Tag 0BHY](https://stacks.math.columbia.edu/tag/0BHY)
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 07NG](https://stacks.math.columbia.edu/tag/07NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Flatness over a local ring of dimension at most one.** Let `f : W ⟶ U` be a morphism from a
reduced scheme to a locally Noetherian normal scheme carrying every generic point of `W` to a
generic point of `U`. At a point `w` whose image has a local ring of dimension at most one, the
map of local rings is flat: the local ring of `U` is a Dedekind domain, and the local ring of `W`
is torsion free over it, because a nonzero element of it survives at some generic point through
`w`, where the base acts through its fraction field. -/
theorem flat_stalkMap_of_ringKrullDim_le_one_of_genericPoints {W U : Scheme.{u}} (f : W ⟶ U)
    [IsReduced W] [IsLocallyNoetherian U] [IsNormal U] (w : W)
    (hdim : ringKrullDim (U.presheaf.stalk (f w)) ≤ 1)
    (hgen : ∀ η ∈ genericPoints W, f η ∈ genericPoints U) :
    (f.stalkMap w).hom.Flat := by
  let R := U.presheaf.stalk (f w)
  let Sw := W.presheaf.stalk w
  let : Algebra R Sw := (f.stalkMap w).hom.toAlgebra
  have : IsIntegrallyClosed R := IsNormal.stalk_normal (f w)
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
  have : Ring.DimensionLEOne R := ⟨fun hne hp => hp.isMaximal_of_ne_bot hne⟩
  have : IsDedekindDomain R :=
    { (inferInstance : IsDomain R), (inferInstance : IsNoetherianRing R),
      (inferInstance : Ring.DimensionLEOne R), (inferInstance : IsIntegrallyClosed R) with }
  have : Module.IsTorsionFree R Sw := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    by_cases hm : m = 0
    · exact Or.inr hm
    refine Or.inl ?_
    obtain ⟨η, hη, hspec, hσ⟩ := exists_genericPoint_stalkSpecializes_ne_zero w hm
    by_contra hr
    have hrm' : (f.stalkMap w) r * m = 0 := by
      simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hrm
    have h0 : (f.stalkMap η) (U.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) r) *
        (W.presheaf.stalkSpecializes hspec) m = 0 := by
      rw [Scheme.Hom.stalkSpecializes_stalkMap_apply f η w hspec r, ← map_mul, hrm', map_zero]
    have hfield : IsField (U.presheaf.stalk (f η)) :=
      isField_stalk_of_closure_mem_irreducibleComponents U (f η) (hgen η hη)
    have hinj : Function.Injective
        (U.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)) := by
      let : Algebra (U.presheaf.stalk (f w)) (U.presheaf.stalk (f η)) :=
        (U.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toAlgebra
      have := Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes
        (f.base.hom.map_specializes hspec)
      exact IsLocalization.injective (U.presheaf.stalk (f η))
        (Ideal.primeCompl_le_nonZeroDivisors ((IsLocalRing.maximalIdeal
          (U.presheaf.stalk (f η))).under (U.presheaf.stalk (f w))))
    obtain ⟨c, hc⟩ := hfield.mul_inv_cancel
      (show U.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) r ≠ 0 from
        fun h => hr (hinj (h.trans (map_zero _).symm)))
    exact hσ (((isUnit_iff_exists_inv.mpr ⟨c, hc⟩).map
      (f.stalkMap η).hom).mul_right_eq_zero.mp h0)
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- On a scheme of dimension at most two, a point whose local ring has dimension at least two is
closed: nothing specializes to it properly. -/
theorem isClosed_singleton_of_two_le_ringKrullDim_stalk (Y : Scheme.{u})
    (hdim : topologicalKrullDim Y ≤ 2) (y : Y)
    (hy : 2 ≤ ringKrullDim (Y.presheaf.stalk y)) : IsClosed ({y} : Set Y) := by
  have hbound (z : Y) : Order.coheight z ≤ 2 := by
    have h := Order.coheight_le_krullDim z
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))] at h
    exact WithBot.coe_le_coe.mp (h.trans hdim)
  have hy2 : Order.coheight y = 2 := by
    rw [ringKrullDim_stalk_eq_coheight] at hy
    exact le_antisymm (hbound y) (WithBot.coe_le_coe.mp hy)
  refine isClosed_of_closure_subset fun z hz => ?_
  have hzy : z ≤ y := specializes_iff_mem_closure.mpr hz
  refine Set.mem_singleton_iff.mpr ?_
  by_contra hne
  have hlt := Order.coheight_strictAnti (show z < y from ⟨hzy, fun hyz =>
      hne ((hyz : Specializes z y).antisymm (hzy : Specializes y z)).eq⟩)
    (lt_of_le_of_lt (hbound y) (by decide : (2 : ℕ∞) < ⊤))
  rw [hy2] at hlt
  exact (not_lt_of_ge (hbound z)) hlt

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Regularity descends along a morphism flat at a point.** If `f : X ⟶ Y` is flat at a point
`x` at which `X` is regular, and `Y` is locally Noetherian, then `Y` is regular at the image of
`x`: the homomorphism of étale local rings at a geometric point over `x` is flat and local. -/
theorem isRegularAt_of_isFlatAt {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hN : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (x : points B S hS X) (hfx : IsFlatAt B S hS f x) (hx : IsRegularAt B S hS X x) :
    IsRegularAt B S hS Y (pointsMap B S hS X f x) := by
  obtain ⟨xbar, hxbar, hreg⟩ := ((isRegularAt_tfae B S hS X hX x).out 1 3).mp hx
  have hfx' : IsFlatAt B S hS f xbar.image := by
    rw [show xbar.image = x from hxbar]
    exact hfx
  have : IsLocalRing (etaleLocalRing B S hS Y (geometricPointMap f xbar)) :=
    isLocalRing_etaleLocalRing B S hS Y hY (geometricPointMap f xbar)
  have : IsNoetherianRing (etaleLocalRing B S hS Y (geometricPointMap f xbar)) :=
    isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS Y hY hN
      (geometricPointMap f xbar)
  let : Algebra (etaleLocalRing B S hS Y (geometricPointMap f xbar))
      (etaleLocalRing B S hS X xbar) := (etaleLocalRingMap hX f xbar).toAlgebra
  have : IsLocalHom (algebraMap (etaleLocalRing B S hS Y (geometricPointMap f xbar))
      (etaleLocalRing B S hS X xbar)) := isLocalHom_etaleLocalRingMap B S hS hX hY f xbar
  have : Module.Flat (etaleLocalRing B S hS Y (geometricPointMap f xbar))
      (etaleLocalRing B S hS X xbar) :=
    (isFlatAt_iff_etaleLocalRingMap_flat hX hY f xbar).mp hfx'
  have : IsRegularLocalRing (etaleLocalRing B S hS X xbar) := hreg
  have key : ∃ ybar : GeometricPoint B S hS Y, ybar.LiesOver (pointsMap B S hS X f x) ∧
      IsRegularLocalRing (etaleLocalRing B S hS Y ybar) := by
    refine ⟨geometricPointMap f xbar, ?_,
      IsRegularLocalRing.of_flat_of_isLocalHom (etaleLocalRing B S hS X xbar)⟩
    show pointsMap B S hS X f xbar.image = pointsMap B S hS X f x
    rw [hxbar]
  exact ((isRegularAt_tfae B S hS Y hY (pointsMap B S hS X f x)).out 3 1).mp key

/-- **Flatness over the points of codimension at most one.** Let `g : X ⟶ N` be a dominant
morphism of integral algebraic spaces with `X` regular and `N` normal with locally Noetherian
étale charts. Then `g` is flat at every point of `X` whose image has a local ring of dimension at
most one.

On a commuting square of étale charts `U ⟶ V` over `g` the generic points of `U` lie over
codimension-zero points of `X`, which `g` carries to codimension-zero points of `N`, that is to
generic points of `V`; so `AlgebraicGeometry.flat_stalkMap_of_ringKrullDim_le_one_of_genericPoints`
applies to `U ⟶ V`. -/
theorem isFlatAt_of_localRingDimension_le_one {X N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hN : IsAlgebraicSpace B S hS N)
    (hXint : IsIntegralSpace B S hS X) (hNint : IsIntegralSpace B S hS N)
    (hXreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T))
    (hNnorm : IsNormal B S hS N)
    (hNnoeth : HasEtaleLocalProperty B S hS N (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (g : X ⟶ N) (hdom : IsDominant B S hS g) (x : points B S hS X)
    (hx : localRingDimension B S hS (pointsMap B S hS X g x) ≤ 1) :
    IsFlatAt B S hS g x := by
  let Tsch := BigFppfOver.toScheme B S hS
  obtain ⟨V, b, hbs, hbe⟩ := hN.exists_atlas
  obtain ⟨U, a, α, hcomm, has, hae⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hN g V b hbs hbe
  obtain ⟨y, rfl⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U a).mp has x
  induction y using Quot.ind with
  | _ p =>
  rw [← isFlatAt_chart_iff B S hS g U V a b α hae hbe hcomm p (IsLocalRing.closedPoint p.carrier),
    isFlatAt_yoneda_iff B S hS U V α p]
  have hUreg : IsRegular (Tsch.obj U) :=
    (exists_atlas_iff_forall_etale B S hS X _ hX).mp hXreg U a hae
  have : IsLocallyNoetherian (Tsch.obj V) :=
    (exists_atlas_iff_forall_etale B S hS N _ hN).mp hNnoeth V b hbe
  have : _root_.AlgebraicGeometry.IsNormal (Tsch.obj V) :=
    (exists_atlas_iff_forall_etale B S hS N _ hN).mp hNnorm V b hbe
  have : _root_.AlgebraicGeometry.IsNormal (Tsch.obj U) :=
    (exists_atlas_iff_forall_etale B S hS X _ hX).mp (isNormal_of_isRegular B S hS X hXreg) U a hae
  have : _root_.AlgebraicGeometry.IsReduced (Tsch.obj U) := inferInstance
  have hchart : ∀ q : FieldValuedPoint B S hS (yoneda.obj U),
      ChartPoint B S hS V b (Tsch.map α (schemePoint B S hS U q))
        (pointsMap B S hS X g (pointsMap B S hS (yoneda.obj U) a
          (q.class B S hS (yoneda.obj U)))) := by
    intro q
    refine ⟨FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map α) q,
      schemePoint_map_yoneda B S hS α q, ?_⟩
    rw [← Function.comp_apply (f := pointsMap B S hS X g), ← pointsMap_comp, hcomm,
      pointsMap_comp]
    rfl
  refine flat_stalkMap_of_ringKrullDim_le_one_of_genericPoints (Tsch.map α)
    (schemePoint B S hS U p) ?_ ?_
  · rw [← localRingDimension_eq_of_chartPoint B S hS hN V b hbe _ _ (hchart p)]
    exact_mod_cast hx
  · intro η hη
    let q := schemePointRepresentative B S hS U η
    have hq : schemePoint B S hS U q = η := schemePointRepresentative_point B S hS U η
    have h0 : localRingDimension B S hS
        (pointsMap B S hS (yoneda.obj U) a (q.class B S hS (yoneda.obj U))) = 0 := by
      have h := localRingDimension_eq_of_chartPoint B S hS hX U a hae η _ ⟨q, hq, rfl⟩
      rw [(ringKrullDim_stalk_eq_zero_iff_mem_genericPoints (Tsch.obj U) η).mpr hη] at h
      exact_mod_cast h
    have h1 := localRingDimension_eq_zero_of_isDominant_of_isIntegralSpace B S hS hX hN hXint
      hNint g hdom _ h0
    have h2 := localRingDimension_eq_of_chartPoint B S hS hN V b hbe _ _ (hchart q)
    rw [h1, hq] at h2
    exact (ringKrullDim_stalk_eq_zero_iff_mem_genericPoints (Tsch.obj V) _).mp
      (by exact_mod_cast h2.symm)

/-- **Finiteness of a closed set of points of local dimension at least two.** In a quasi-compact
algebraic space of dimension at most two whose étale charts are locally Noetherian, a closed set
of points whose local rings have dimension at least two is finite.

Over an affine surjective étale chart `U`, a Noetherian scheme of dimension at most two, the
preimage of the set is closed and consists of points with local rings of dimension at least two,
which are closed points; a closed set of closed points of a Noetherian scheme is finite. -/
theorem finite_of_isClosed_of_one_lt_localRingDimension {N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hN : IsAlgebraicSpace B S hS N) (hNqc : IsQuasiCompactSpace B S hS N)
    (hNnoeth : HasEtaleLocalProperty B S hS N (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hdim : dimension B S hS N hN ≤ 2) (Z : Set (points B S hS N)) (hZ : IsClosed Z)
    (h2 : ∀ z ∈ Z, 1 < localRingDimension B S hS z) : Z.Finite := by
  let Tsch := BigFppfOver.toScheme B S hS
  obtain ⟨U, a, hUaff, haSurjP, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS N hN).mp hNqc
  have haeP := (isEtale_iff_presheaf_of_yoneda B S hS a).mp haet
  have : IsAffine (Tsch.obj U) := hUaff
  have : IsLocallyNoetherian (Tsch.obj U) :=
    (exists_atlas_iff_forall_etale B S hS N _ hN).mp hNnoeth U a haeP
  have : _root_.AlgebraicGeometry.IsNoetherian (Tsch.obj U) := {}
  let e := schemePointsHomeomorph B S hS U
  let π : Tsch.obj U → points B S hS N := fun u => pointsMap B S hS (yoneda.obj U) a (e.symm u)
  have hπc : Continuous π := (continuous_pointsMap B S hS a).comp e.symm.continuous
  have hπs : Function.Surjective π := by
    intro x
    obtain ⟨y, rfl⟩ := (surjective_iff_surjective_pointsMap B S hS N hN U a).mp haSurjP x
    exact ⟨e y, by simp [π]⟩
  have hchart (u : Tsch.obj U) : ChartPoint B S hS U a u (π u) := by
    have h := chartPoint_pointsToScheme B S hS U a (e.symm u)
    rwa [show pointsToScheme B S hS U (e.symm u) = u from e.apply_symm_apply u] at h
  have hdimU : topologicalKrullDim (Tsch.obj U) ≤ 2 := by
    have hsup : topologicalKrullDim (Tsch.obj U) = ⨆ u, topologicalKrullDimAt (Tsch.obj U) u := by
      simpa only [TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim] using
        TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim (Tsch.obj U)
    rw [hsup]
    refine iSup_le fun u => ?_
    let p := schemePointRepresentative B S hS U u
    rw [← schemePointRepresentative_point B S hS U u,
      ← dimensionAtPoint_eq_of_etale_chart B S hS N hN _ U a haeP p rfl]
    exact (le_iSup (fun x => dimensionAtPoint B S hS N hN x) _).trans hdim
  have hZ' : (π ⁻¹' Z).Finite := by
    refine finite_of_isClosed_of_forall_isClosed_singleton (hZ.preimage hπc) fun u hu => ?_
    refine isClosed_singleton_of_two_le_ringKrullDim_stalk _ hdimU u ?_
    rw [← localRingDimension_eq_of_chartPoint B S hS hN U a haeP u _ (hchart u)]
    have h22 : (2 : ℕ∞) ≤ localRingDimension B S hS (π u) := by
      simpa [one_add_one_eq_two] using Order.add_one_le_of_lt (h2 _ hu)
    exact (WithBot.coe_le_coe.mpr h22 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ _)
  rw [← Set.image_preimage_eq Z hπs]
  exact hZ'.image π

/-- **A normal space of dimension at most two with a regular proper cover has finitely many
singular points.** Let `N` be an integral normal algebraic space over `S`, quasi-compact, with
locally Noetherian étale charts and of dimension at most two, and let `g : X ⟶ N` be proper and
dominant with `X` integral and regular. Then the set of points of `N` at which `N` is not regular
is finite.

The image `Z` under `g` of the set of points where `g` is not flat is closed, as the flat locus
is open and `g` is closed; it contains every singular point, since `g` is surjective and
regularity descends along a morphism flat at a point; and it contains no point of codimension at
most one, at which `g` is flat. So `Z` is finite. -/
theorem finite_setOf_not_isRegularAt_of_isProper {X N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hN : IsAlgebraicSpace B S hS N)
    (hXint : IsIntegralSpace B S hS X) (hNint : IsIntegralSpace B S hS N)
    (hXreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T))
    (hNnorm : IsNormal B S hS N)
    (hNnoeth : HasEtaleLocalProperty B S hS N (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNqc : IsQuasiCompactSpace B S hS N) (hdim : dimension B S hS N hN ≤ 2)
    (g : X ⟶ N) (hgp : IsProper B S hS g) (hdom : IsDominant B S hS g) :
    {y : points B S hS N | ¬ IsRegularAt B S hS N y}.Finite := by
  have hlfp : IsLocallyOfFinitePresentation B S hS g := by
    intro U V a b h ha hb comm
    have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
      (exists_atlas_iff_forall_etale B S hS N _ hN).mp hNnoeth V b hb
    exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
      (hgp.2.1.1 U V a b h ha hb comm)
  let Z := pointsMap B S hS X g '' {x | ¬ IsFlatAt B S hS g x}
  have hZ : IsClosed Z :=
    isClosed_of_universallyClosed B S hS hN g hgp.2.2 _
      (isOpen_setOf_isFlatAt B S hS hX hN g hlfp).isClosed_compl
  have hsurj : IsSurjective B S hS g := isSurjective_of_isProper_of_isDominant B S hS hN g hgp hdom
  have hsub : {y : points B S hS N | ¬ IsRegularAt B S hS N y} ⊆ Z := by
    intro y hy
    obtain ⟨x, rfl⟩ := hsurj y
    refine ⟨x, fun hflat => hy (isRegularAt_of_isFlatAt B S hS hX hN g hNnoeth x hflat ?_), rfl⟩
    intro U a ha p _
    have hiff : IsRegular ((BigFppfOver.toScheme B S hS).obj U) ↔
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) ∧
          ∀ z : (BigFppfOver.toScheme B S hS).obj U,
            IsRegularLocalRing (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk z) :=
      (isRegular_tfae ((BigFppfOver.toScheme B S hS).obj U)).out 1 2 (by simp) (by simp)
    exact (hiff.mp ((exists_atlas_iff_forall_etale B S hS X _ hX).mp hXreg U a ha)).2 _
  refine Set.Finite.subset (finite_of_isClosed_of_one_lt_localRingDimension B S hS hN hNqc
    hNnoeth hdim Z hZ ?_) hsub
  rintro z ⟨x, hx, rfl⟩
  exact not_le.mp fun hle => hx (isFlatAt_of_localRingDimension_le_one B S hS hX hN hXint hNint
    hXreg hNnorm hNnoeth g hdom x hle)

end Space

end AlgebraicGeometry

end
