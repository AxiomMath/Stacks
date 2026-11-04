module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique

/-!
# Condition (o) for a locus which is open over an open substack of curves

Let `P` be a property of families of curves satisfying condition (o) of Section 0E0E, and let `Q`
be a property read off a locus `L(G)` of points of the base of every family `G`, a locus which
commutes with base change along morphisms of families. If `L(G)` is open whenever `G` has `P`,
then `P ∧ Q` satisfies condition (o): `Curves^{P, Q}` is an open substack of `Curves`.

This is the step by which the source makes `Curves^{CM, 1}` and `Curves^{Gorenstein, 1}` open
substacks (Tags 0E1F and 0E6M): the relative-dimension-one locus is only known to be open over a
family which is already Cohen–Macaulay, and it is enough to know that over the open substack cut
out by `P`.

## Main results

* `AlgebraicGeometry.IsOpenCurvesLocus.and_of_baseLocus`: condition (o) for `P ∧ Q`.

## Implementation notes

Given a family `G`, condition (o) for `P` supplies an open subspace `W` of the base `S` of `G`.
The candidate open of the base for `P ∧ Q` is `|W| ∩ L(G)`; that it describes `P ∧ Q` on every
family mapping to `G` is condition (o) for `P` together with the base-change compatibility of
`L`. For openness the open subspace `W` is represented by an open subscheme `V ⊂ S` of the site,
and `G` is restricted to `V` by a cartesian lift of `V ⟶ S` (the category of families of curves
is fibred in groupoids over the site). The restricted family `G_V` maps to `G` over the inclusion
of `V`, hence has `P`, hence `L(G_V)` is open; and `L(G_V)` is the inverse image of `L(G)`, so its
image in `S`, which is `|W| ∩ L(G)`, is open because an open immersion of schemes is open on
points.

## References

* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E1F](https://stacks.math.columbia.edu/tag/0E1F)
* [Stacks Project, Tag 0E6M](https://stacks.math.columbia.edu/tag/0E6M)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Condition (o) over an open substack.** Let `P` satisfy condition (o) of Stacks 0E0E, and let
`Q` be the condition that a locus `L` of points of the base be everything, where `L` commutes with
base change along morphisms of families of curves. If `L(G)` is open for every family `G` with
`P`, then `P ∧ Q` satisfies condition (o). -/
theorem IsOpenCurvesLocus.and_of_baseLocus {P Q : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P)
    (L : ∀ G : CurveFamily B hZ, Set (Space.points B integerBase hZ (schemeSpace G.base).obj))
    (hL : ∀ {F G : CurveFamily B hZ} (a : F ⟶ G),
      Space.pointsMap B integerBase hZ (schemeSpace F.base).obj (schemeSpaceMap a.baseMap).hom ⁻¹'
        L G = L F)
    (hQ : ∀ F : CurveFamily B hZ, Q F ↔ L F = Set.univ)
    (hopen : ∀ G : CurveFamily B hZ, P G → IsOpen (L G)) :
    IsOpenCurvesLocus B hZ (fun F => P F ∧ Q F) := by
  refine IsOpenCurvesLocus.of_points fun G => ?_
  obtain ⟨W, hW, hchar⟩ := hP G
  -- The open subspace `W` of the base is represented by an open subscheme `V` of the site.
  obtain ⟨V, j, hj, e, he⟩ : ∃ (V : BigFppfOver B integerBase hZ) (j : V ⟶ G.base),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
      ∃ e : yoneda.obj V ≅ W.toFunctor, e.hom ≫ W.ι = yoneda.map j := by
    have key : ∀ (U' : BigFppfOver B integerBase hZ) (W' : Subfunctor (yoneda.obj U')),
        Space.IsOpenSubspace B integerBase hZ W' →
        ∃ (V : BigFppfOver B integerBase hZ) (j : V ⟶ U'),
          IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
          ∃ e : yoneda.obj V ≅ W'.toFunctor, e.hom ≫ W'.ι = yoneda.map j := by
      intro U' W' hW'
      let h := hW'.2.rep.isPullback (𝟙 (yoneda.obj U'))
      let eMap := hW'.2.rep.fst (𝟙 (yoneda.obj U'))
      have : IsIso eMap := h.isIso_fst_of_isIso
      exact ⟨_, hW'.2.rep.snd (𝟙 (yoneda.obj U')), hW'.2.property_snd (𝟙 (yoneda.obj U')),
        asIso eMap, by simpa [eMap] using h.w⟩
    exact key G.base W hW
  -- The restriction of `G` to `V`, as a cartesian lift of `V ⟶ S`.
  have hfib : (curvesProjectionOver B hZ).IsFiberedInGroupoids := (curvesFiberedCategory B hZ).2
  obtain ⟨GV, φ, hφ⟩ := hfib.exists_lift j G rfl
  obtain ⟨i, hfac⟩ : ∃ i : GV.base ≅ V, φ.baseMap = i.hom ≫ j := by
    refine ⟨eqToIso (IsHomLift.domain_eq (curvesProjectionOver B hZ) j φ), ?_⟩
    have h := IsHomLift.fac' (curvesProjectionOver B hZ) j φ
    change φ.baseMap = eqToHom _ ≫ j ≫ eqToHom (rfl : G.base = G.base) at h
    simp only [eqToHom_refl, Category.comp_id] at h
    exact h
  have hfactor : (schemeSpaceMap φ.baseMap).hom = (yoneda.map i.hom ≫ e.hom) ≫ W.ι := by
    show yoneda.map φ.baseMap = _
    rw [hfac, Functor.map_comp, Category.assoc, he]
    rfl
  have hPV : P GV := (hchar GV φ).mpr ⟨yoneda.map i.hom ≫ e.hom, hfactor.symm⟩
  have hrange : Set.range (Space.pointsMap B integerBase hZ (schemeSpace GV.base).obj
        (schemeSpaceMap φ.baseMap).hom) =
      Set.range (Space.pointsMap B integerBase hZ W.toFunctor W.ι) := by
    rw [hfactor]
    exact Space.range_pointsMap_comp_isIso B integerBase hZ (yoneda.mapIso i ≪≫ e).hom W.ι
  have hetale : Etale ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) := by
    rw [hfac, Functor.map_comp]
    infer_instance
  refine ⟨Set.range (Space.pointsMap B integerBase hZ W.toFunctor W.ι) ∩ L G, ?_,
    fun F a => ?_⟩
  · have himage : Space.pointsMap B integerBase hZ (schemeSpace GV.base).obj
          (schemeSpaceMap φ.baseMap).hom '' L GV =
        Set.range (Space.pointsMap B integerBase hZ W.toFunctor W.ι) ∩ L G := by
      rw [← hL φ, Set.image_preimage_eq_inter_range, hrange, Set.inter_comm]
    rw [← himage]
    exact Space.isOpenMap_pointsMap_yonedaMap_of_etale B integerBase hZ φ.baseMap hetale _
      (hopen GV hPV)
  · rw [hchar F a, Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace G.base).property (schemeSpace F.base).property W hW, hQ F, ← hL a,
      Set.preimage_eq_univ_iff, Set.subset_inter_iff]

end AlgebraicGeometry

end
