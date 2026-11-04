module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.SmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.NormalizationEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The normalization of an algebraic space commutes with smooth base change

Let `S` be a scheme, let `φ : F ⟶ G` be a smooth morphism of algebraic spaces over `S`, let `D`
be normalization data for `G` and `D'` normalization data for `F`. Part (4) of Stacks 07U4 says
that the morphism `F^ν ⟶ G^ν` induced by `φ` exhibits `F^ν` as the fibre product
`F ×_G G^ν`. The étale case is
`AlgebraicGeometry.Space.NormalizationData.isPullback_hom_of_isEtale`; this file proves the
smooth one, which is the case the proof of Stacks 0GMJ uses, for the source and target maps of a
smooth groupoid.

The argument is the étale one, with the two inputs that used étaleness replaced:

* normality of `F ×_G G^ν` ascends from `G^ν` along the smooth projection, by
  `AlgebraicGeometry.Space.isNormal_of_isSmooth` (Stacks 033C on charts);
* the projection `F ×_G G^ν ⟶ F` carries points of codimension zero to points of codimension
  zero. For an étale `φ` this was the étale invariance of the dimension of the local ring; for a
  flat `φ` it is
  `AlgebraicGeometry.Space.NormalizationData.localRingDimension_pullback_snd_eq_zero`, which
  reads the scheme statement `AlgebraicGeometry.mem_genericPoints_pullbackSnd_of_flat` on a
  chart.

## Main results

* `AlgebraicGeometry.Space.isNormal_of_isSmooth`: an algebraic space smooth over a normal
  algebraic space is normal.
* `AlgebraicGeometry.Space.NormalizationData.localRingDimension_pullback_snd_eq_zero`: for a
  flat `φ : F ⟶ G`, the projection `G^ν ×_G F ⟶ F` carries points of codimension zero to points
  of codimension zero.
* `AlgebraicGeometry.Space.NormalizationData.isPullback_hom_of_isSmooth`: **Stacks 07U4, part
  (4)** for a smooth morphism of algebraic spaces, with given normalization data.
* `AlgebraicGeometry.Space.NormalizationData.exists_isPullback_hom_of_isSmooth`: the same, with
  the normalization of the source produced by Stacks 07U4.

## References

* [Stacks Project, Tag 033C](https://stacks.math.columbia.edu/tag/033C)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0GMD](https://stacks.math.columbia.edu/tag/0GMD)
* [Stacks Project, Tag 0GMJ](https://stacks.math.columbia.edu/tag/0GMJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The scheme statement `AlgebraicGeometry.mem_genericPoints_pullbackSnd_of_flat`, for an
arbitrary cartesian square rather than the chosen fibre product. -/
theorem mem_genericPoints_of_isPullback_of_flat {P X Y Z : Scheme.{u}} {fst : P ⟶ Z}
    {snd : P ⟶ X} {g : Z ⟶ Y} {φ : X ⟶ Y} (h : IsPullback fst snd g φ) [Flat φ]
    (hg : ∀ z : Z, z ∈ genericPoints Z → g z ∈ genericPoints Y)
    {w : P} (hw : w ∈ genericPoints P) : snd w ∈ genericPoints X := by
  have hiso : h.isoPullback.hom ≫ pullback.snd g φ = snd := h.isoPullback_hom_snd
  rw [← hiso, Scheme.Hom.comp_apply]
  exact mem_genericPoints_pullbackSnd_of_flat g φ hg
    (Scheme.Hom.mem_genericPoints_of_flat h.isoPullback.hom hw)

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Normality ascends along smooth morphisms of algebraic spaces.** An algebraic space smooth
over a normal algebraic space is normal.

A surjective étale chart `V ⟶ G` by a normal scheme lifts, by Stacks 02X1, to a surjective étale
chart `U ⟶ F` with a morphism `U ⟶ V` over `φ`; that morphism is smooth because `φ` is, so `U`
is normal by Stacks 033C. -/
@[sga "3 X 8.9" "more general"]
theorem isNormal_of_isSmooth {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (φ : F ⟶ G)
    (hφ : IsSmooth B S hS φ) (hGn : Space.IsNormal B S hS G) : Space.IsNormal B S hS F := by
  obtain ⟨V, q, hqS, hqE, hVn⟩ := hGn
  obtain ⟨U, p, α, hcomm, hpS, hpE⟩ :=
    exists_surjective_etale_presentation_lift B S hS hF hG φ V q hqS hqE
  have : Smooth ((BigFppfOver.toScheme B S hS).map α) := hφ U V p q α hpE hqE hcomm.symm
  have : _root_.AlgebraicGeometry.IsNormal ((BigFppfOver.toScheme B S hS).obj V) := hVn
  exact ⟨U, p, hpS, hpE, _root_.AlgebraicGeometry.isNormal_of_smooth
    ((BigFppfOver.toScheme B S hS).map α)⟩

namespace NormalizationData

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The base change of the normalization along a flat morphism preserves codimension zero.**
For a flat morphism `φ : F ⟶ G` of algebraic spaces and normalization data `D` of `G`, the
projection `G^ν ×_G F ⟶ F` carries points of codimension zero to points of codimension zero.

On a surjective étale chart `V ⟶ G` the normalization is the normalization scheme `V^ν` of the
chart, and a surjective étale chart `U ⟶ F` lying over `V` (Stacks 02X1) gives the surjective
étale chart `V^ν ×_V U` of `G^ν ×_G F`. A point of codimension zero lifts to a generic point of
that scheme, and the scheme statement of the étale-free half of Stacks 07TD,
`AlgebraicGeometry.mem_genericPoints_of_isPullback_of_flat`, carries it to a generic point of
`U`, the normalization morphism of `V` carrying generic points to generic points. -/
theorem localRingDimension_pullback_snd_eq_zero (D : NormalizationData B S hS G)
    (hG : IsAlgebraicSpace B S hS G) (hF : IsAlgebraicSpace B S hS F) (φ : F ⟶ G)
    (hφ : IsFlat B S hS φ) (z : points B S hS (pullback D.hom φ))
    (hz : localRingDimension B S hS z = 0) :
    localRingDimension B S hS (pointsMap B S hS _ (pullback.snd D.hom φ) z) = 0 := by
  let T := BigFppfOver.toScheme B S hS
  have hN : IsAlgebraicSpace B S hS (pullback D.hom φ) :=
    isAlgebraicSpace_pullback B S hS D.hom φ D.isAlgebraicSpace hF hG
  obtain ⟨V, q, hqS, hqE⟩ := hG.exists_atlas
  obtain ⟨U, p, α, hcomm, hpS, hpE⟩ :=
    exists_surjective_etale_presentation_lift B S hS hF hG φ V q hqS hqE
  have : Flat (T.map α) := hφ U V p q α hpE hqE hcomm.symm
  obtain ⟨hV, Vν, pν, g, e, hpν, hsq1⟩ := D.chart V q
    ((surjective_iff_surjective_pointsMap B S hS G hG V q).mp hqS)
    ((isEtale_iff_presheaf_of_yoneda B S hS q).mpr hqE)
  have := hasPullbacks_bigFppfOver B S hS
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have sqW := IsPullback.of_hasPullback pν α
  have hbig : IsPullback (yoneda.map (pullback.fst pν α) ≫ g) (yoneda.map (pullback.snd pν α))
      D.hom (p ≫ φ) := by
    rw [hcomm]
    exact (sqW.map yoneda).paste_horiz hsq1
  let k : yoneda.obj (pullback pν α) ⟶ pullback D.hom φ :=
    pullback.lift (yoneda.map (pullback.fst pν α) ≫ g) (yoneda.map (pullback.snd pν α) ≫ p)
      (by rw [hbig.w, Category.assoc])
  have hk : IsPullback k (yoneda.map (pullback.snd pν α)) (pullback.snd D.hom φ) p :=
    IsPullback.of_right (by rw [pullback.lift_fst]; exact hbig) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback D.hom φ)
  have hkE : IsEtale B S hS k :=
    isEtale_of_isPullback_yoneda B S hS hk.flip ((isEtale_iff_presheaf_of_yoneda B S hS p).mpr hpE)
  obtain ⟨u, hu⟩ := (surjective_iff_surjective_pointsMap B S hS F hF U p).mp hpS
    (pointsMap B S hS _ (pullback.snd D.hom φ) z)
  obtain ⟨w, hwz, hwu⟩ := exists_point_of_isPullback_presheaf B S hS hk z u hu.symm
  have hwgen : pointsToScheme B S hS _ w ∈ genericPoints (T.obj (pullback pν α)) :=
    (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hN z).mp hz _ k _ hkE
      (hwz ▸ chartPoint_pointsToScheme B S hS _ k w)
  have hpνgen : ∀ x : T.obj Vν, x ∈ genericPoints (T.obj Vν) →
      T.map pν x ∈ genericPoints (T.obj V) := by
    intro x hx
    rw [hpν, Scheme.Hom.comp_apply]
    exact Scheme.normalization_mem_genericPoints _ hV
      (Scheme.Hom.mem_genericPoints_of_flat e.hom hx)
  have hugen : T.map (pullback.snd pν α) (pointsToScheme B S hS _ w) ∈ genericPoints (T.obj U) :=
    mem_genericPoints_of_isPullback_of_flat (sqW.map T) hpνgen hwgen
  refine (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hF _).mpr
    ⟨U, p, _, (isEtale_iff_presheaf_of_yoneda B S hS p).mpr hpE, ?_, hugen⟩
  rw [← pointsToScheme_pointsMap B S hS (pullback.snd pν α) w, hwu, ← hu]
  exact chartPoint_pointsToScheme B S hS U p u

/-- **Stacks 07U4, part (4), for a smooth morphism of algebraic spaces: the normalization square
is cartesian.** Let `φ : F ⟶ G` be a smooth morphism of algebraic spaces over `S`, let `D` be
normalization data for `G` and `D'` normalization data for `F`. Then there is a morphism
`F^ν ⟶ G^ν` over `φ` exhibiting `F^ν` as the fibre product `F ×_G G^ν`.

The morphism `F^ν ⟶ G^ν` and its inverse comparison `F ×_G G^ν ⟶ F^ν` both come from the
universal property of the normalization, Stacks 0BB4 part (4): `F^ν` is normal, and so is
`F ×_G G^ν`, being smooth over the normal space `G^ν`; the relevant morphisms carry codimension
zero to codimension zero because flat morphisms do (Stacks 0GMC), because the normalization
morphisms do (Stacks 0BB4 part (3)), and because the projection `F ×_G G^ν ⟶ F` does
(`AlgebraicGeometry.Space.NormalizationData.localRingDimension_pullback_snd_eq_zero`). The two
composites are identities by the uniqueness half of the same universal property. -/
@[stacks 07U4 "part (4) for a smooth morphism of algebraic spaces, with given normalizations"]
theorem isPullback_hom_of_isSmooth (D : NormalizationData B S hS G)
    (D' : NormalizationData B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hF : IsAlgebraicSpace B S hS F) (φ : F ⟶ G) (hφ : IsSmooth B S hS φ) :
    ∃ m : D'.space ⟶ D.space, IsPullback m D'.hom D.hom φ := by
  have hN : IsAlgebraicSpace B S hS (pullback D.hom φ) :=
    isAlgebraicSpace_pullback B S hS D.hom φ D.isAlgebraicSpace hF hG
  have hp : IsSmooth B S hS (pullback.fst D.hom φ) :=
    isSmooth_of_isPullback (IsPullback.of_hasPullback D.hom φ) hN hF D.isAlgebraicSpace hG hφ
  have hφflat : IsFlat B S hS φ := isFlat_of_isSmooth B S hS φ hφ
  have hNn : Space.IsNormal B S hS (pullback D.hom φ) :=
    isNormal_of_isSmooth hN D.isAlgebraicSpace _ hp (D.isNormal hG)
  have hgenP : ∀ z : points B S hS (pullback D.hom φ), localRingDimension B S hS z = 0 →
      localRingDimension B S hS
        (pointsMap B S hS _ (pullback.fst D.hom φ ≫ D.hom) z) = 0 := by
    intro z hz
    rw [pointsMap_comp_apply]
    exact (D.bijOn_codimensionZeroPoints_hom hG).1
      (localRingDimension_eq_zero_of_isFlat B S hS hN D.isAlgebraicSpace _
        (isFlat_of_isSmooth B S hS _ hp) z hz)
  have hgenQ : ∀ z : points B S hS (pullback D.hom φ), localRingDimension B S hS z = 0 →
      localRingDimension B S hS (pointsMap B S hS _ (pullback.snd D.hom φ) z) = 0 :=
    D.localRingDimension_pullback_snd_eq_zero hG hF φ hφflat
  have hgenM : ∀ z : points B S hS D'.space, localRingDimension B S hS z = 0 →
      localRingDimension B S hS (pointsMap B S hS _ (D'.hom ≫ φ) z) = 0 := by
    intro z hz
    rw [pointsMap_comp_apply]
    exact localRingDimension_eq_zero_of_isFlat B S hS hF hG φ hφflat _
      ((D'.bijOn_codimensionZeroPoints_hom hF).1 hz)
  obtain ⟨m, hm, -⟩ := D.existsUnique_lift_hom hG D'.isAlgebraicSpace
    (D'.hasEtaleLocalProperty_isNormal hF) (D'.hom ≫ φ) hgenM
  refine ⟨m, ?_⟩
  set lift : D'.space ⟶ pullback D.hom φ := pullback.lift m D'.hom hm with hliftdef
  obtain ⟨u, hu, -⟩ := D'.existsUnique_lift_hom hF hN hNn (pullback.snd D.hom φ) hgenQ
  have hliftu : lift ≫ u = 𝟙 D'.space := by
    refine ExistsUnique.unique (D'.existsUnique_lift_hom hF D'.isAlgebraicSpace
      (D'.hasEtaleLocalProperty_isNormal hF) D'.hom
      (fun z hz => (D'.bijOn_codimensionZeroPoints_hom hF).1 hz)) ?_ (Category.id_comp _)
    rw [Category.assoc, hu, hliftdef, pullback.lift_snd]
  have hfst : u ≫ m = pullback.fst D.hom φ := by
    refine ExistsUnique.unique (D.existsUnique_lift_hom hG hN hNn
      (pullback.fst D.hom φ ≫ D.hom) hgenP) ?_ rfl
    rw [Category.assoc, hm, ← Category.assoc, hu, pullback.condition]
  have hulift : u ≫ lift = 𝟙 (pullback D.hom φ) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hliftdef, pullback.lift_fst, hfst, Category.id_comp]
    · rw [Category.assoc, hliftdef, pullback.lift_snd, hu, Category.id_comp]
  have : IsIso lift := ⟨u, hliftu, hulift⟩
  exact IsPullback.of_iso_pullback ⟨hm⟩ (asIso lift)
    (by rw [asIso_hom, hliftdef, pullback.lift_fst])
    (by rw [asIso_hom, hliftdef, pullback.lift_snd])

/-- **Stacks 07U4, part (4), for a smooth morphism, with the normalization of the source
produced.** Only normalization data for the target is given: the source satisfies the condition
of Stacks 0BB1 because the target does and the morphism is flat and locally of finite type
(Stacks 0GMD), so it has normalization data by Stacks 07U4, and
`AlgebraicGeometry.Space.NormalizationData.isPullback_hom_of_isSmooth` applies to it. -/
@[stacks 07U4 "part (4) for a smooth morphism of algebraic spaces"]
theorem exists_isPullback_hom_of_isSmooth (D : NormalizationData B S hS G)
    (hG : IsAlgebraicSpace B S hS G) (hF : IsAlgebraicSpace B S hS F) (φ : F ⟶ G)
    (hφ : IsSmooth B S hS φ) (hGfin : HasLocallyFiniteIrreducibleComponents B S hS G) :
    ∃ (D' : NormalizationData B S hS F) (m : D'.space ⟶ D.space),
      IsPullback m D'.hom D.hom φ := by
  obtain ⟨D'⟩ := nonempty_normalizationData B S hS hF
    (hasLocallyFiniteIrreducibleComponents_of_isFlat_of_isLocallyOfFiniteType B S hS hF hG φ
      (isFlat_of_isSmooth B S hS φ hφ)
      (isLocallyOfFiniteType_of_isSmooth B S hS hφ) hGfin)
  obtain ⟨m, hm⟩ := D.isPullback_hom_of_isSmooth D' hG hF φ hφ
  exact ⟨D', m, hm⟩

end NormalizationData

end Space

end AlgebraicGeometry

end
